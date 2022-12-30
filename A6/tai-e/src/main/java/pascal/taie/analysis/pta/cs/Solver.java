/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            csMethod.getMethod().getIR().getStmts()
                    .stream()
                    .filter(stmt -> (stmt instanceof New) ||
                            (stmt instanceof Copy) ||
                            (stmt instanceof StoreField storeField && storeField.isStatic()) ||
                            (stmt instanceof LoadField loadField && loadField.isStatic()) ||
                            (stmt instanceof Invoke invoke && invoke.isStatic()))
                    .forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            var obj = heapModel.getObj(stmt);
            var objContext = contextSelector.selectHeapContext(csMethod, obj);
            var csObj = csManager.getCSObj(objContext, obj);
            var var = stmt.getLValue();
            var csVar = csManager.getCSVar(context, var);
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            return null;
        }

        // assign stmt: x = y;
        @Override
        public Void visit(Copy stmt) {
            var cy = csManager.getCSVar(context, stmt.getRValue());
            var cx = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(cy, cx);
            return null;
        }

        // static field store: T.f = y;
        @Override
        public Void visit(StoreField stmt) {
            // none static field store will be processed in analyze()
            if (stmt.isStatic()) {
                var staticField = csManager.getStaticField(stmt.getFieldRef().resolve());
                var cy = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(cy, staticField);
            }
            return null;
        }

        // static field load: y = T.f;
        @Override
        public Void visit(LoadField stmt) {
            // none static field load will be processed in analyze()
            if (stmt.isStatic()) {
                var staticField = csManager.getStaticField(stmt.getFieldRef().resolve());
                var cy = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(staticField, cy);
            }
            return null;
        }


        // invoke: x.k(a1, ..., an);
        // static invoke: T.m(x1, ..., xn);
        @Override
        public Void visit(Invoke stmt) {
            assert stmt.isStatic();
            var method = resolveCallee(null, stmt);
            var csMethod = csManager.getCSMethod(context, method);
            var csCallSite = csManager.getCSCallSite(context, stmt);
            processCallHelper(csCallSite, csMethod);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            var pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var n = entry.pointer();
            var pts = entry.pointsToSet();
            var delta = propagate(n, pts);
            if (n instanceof CSVar csVar) {
                Var var = csVar.getVar();
                var c = csVar.getContext();
                delta.objects().forEach(csObj -> {
                    // store field
                    var.getStoreFields().forEach(storeStmt -> {
                        var cy = csManager.getCSVar(c, storeStmt.getRValue());
                        var field = storeStmt.getFieldRef().resolve();
                        var instanceField = csManager.getInstanceField(csObj, field);
                        addPFGEdge(cy, instanceField);
                    });
                    // load field
                    var.getLoadFields().forEach(loadStmt -> {
                        var cy = csManager.getCSVar(c, loadStmt.getLValue());
                        var field = loadStmt.getFieldRef().resolve();
                        var instanceField = csManager.getInstanceField(csObj, field);
                        addPFGEdge(instanceField, cy);
                    });
                    // array store
                    var.getStoreArrays().forEach(arrayStoreStmt -> {
                        var cy = csManager.getCSVar(c, arrayStoreStmt.getRValue());
                        var arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdge(cy, arrayIndex);
                    });
                    // array load
                    var.getLoadArrays().forEach(arrayLoadStmt -> {
                        var cy = csManager.getCSVar(c, arrayLoadStmt.getLValue());
                        var arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdge(arrayIndex, cy);
                    });
                    // process call
                    processCall(csVar, csObj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {

        // cal delta
        var delta = PointsToSetFactory.make();
        var ptn = pointer.getPointsToSet();
        pointsToSet.objects()
                .filter(ptr -> ptn.objects().noneMatch(ptr::equals))
                .forEach(delta::addObject);
        if (!delta.isEmpty()) {
            delta.forEach(ptn::addObject);
            pointerFlowGraph.getSuccsOf(pointer).forEach(s -> workList.addEntry(s, delta));
        }
        return delta;
    }

    private void processCall(CSVar recv, CSObj recvObj) {
        var invokes = recv.getVar().getInvokes();
        var c = recv.getContext();
        invokes.forEach(invoke -> {
            var method = resolveCallee(recvObj, invoke);
            var csCallSite = csManager.getCSCallSite(c, invoke);
            Context ct = contextSelector.selectContext(csCallSite, recvObj, method);
            var csMethod = csManager.getCSMethod(ct, method);
            var thisVar = method.getIR().getThis();
            var csThisVar = csManager.getCSVar(ct, thisVar);
            workList.addEntry(csThisVar, PointsToSetFactory.make(recvObj));
            processCallHelper(csCallSite, csMethod);
        });
    }

    private void processCallHelper(CSCallSite csCallSite, CSMethod csMethod) {
        var c = csCallSite.getContext();
        var ct = csMethod.getContext();
        Invoke invoke = csCallSite.getCallSite();
        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod))) {
            addReachable(csMethod);
            // pass arguments
            JMethod method = csMethod.getMethod(); // JMethod of CSMethod
            for (int i = 0; i < method.getParamCount(); i++) {
                var param = method.getIR().getParam(i);
                var arg = invoke.getInvokeExp().getArg(i);
                addPFGEdge(csManager.getCSVar(c, arg), csManager.getCSVar(ct, param));
            }
            // pass return values
            Var r = invoke.getLValue();
            if (r != null) {
                var rPtr = csManager.getCSVar(c, r);
                method.getIR().getReturnVars().forEach(retVar -> {
                    var retPtr = csManager.getCSVar(ct, retVar);
                    addPFGEdge(retPtr, rPtr);
                });
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
