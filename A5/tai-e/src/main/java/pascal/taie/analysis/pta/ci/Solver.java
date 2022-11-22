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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import javax.annotation.Nullable;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.addReachableMethod(method)) { // if RM changes, continue
            // new Stmt
            // assign Stmt
            // Static field Load and Store
            // Static invoke
            method.getIR().getStmts()
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
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        // new stmt: x = new T();
        @Override
        public Void visit(New stmt) {
            var obj = heapModel.getObj(stmt);
            var pointer = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(pointer, new PointsToSet(obj));
            return null;
        }

        // assign stmt: x = y;
        @Override
        public Void visit(Copy stmt) {
            var y = pointerFlowGraph.getVarPtr(stmt.getRValue());
            var x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(y, x);
            return null;
        }

        // static field store: T.f = y;
        @Override
        public Void visit(StoreField stmt) {
            // none static field store will be processed in analyze()
            if (stmt.isStatic()) {
                var staticFieldPtr = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                var y = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(y, staticFieldPtr);
            }
            return null;
        }

        // static field load: y = T.f;
        @Override
        public Void visit(LoadField stmt) {
            // none static field load will be processed in analyze()
            if (stmt.isStatic()) {
                var staticFieldPtr = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                var y = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(staticFieldPtr, y);
            }
            return null;
        }

        // invoke: x.k(a1, ..., an);
        // static invoke: T.m(x1, ..., xn);
        @Override
        public Void visit(Invoke stmt) {
            assert stmt.isStatic();
            var method = resolveCallee(null, stmt);
            processCallHelper(stmt, method);
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
     * Add call graph edge, add parameter edge and return edge
     *
     * @param invoke the call site
     * @param method the resolved method
     */
    private void processCallHelper(Invoke invoke, JMethod method) {
        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))) {
            addReachable(method);
            // pass arguments
            for (int i = 0; i < method.getParamCount(); i++) {
                var param = method.getIR().getParam(i);
                var arg = invoke.getInvokeExp().getArg(i);
                addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
            }
            // pass return values
            Var r = invoke.getLValue();
            if (r != null) {
                var rPtr = pointerFlowGraph.getVarPtr(r);
                method.getIR().getReturnVars().forEach(retVar -> {
                    var retPtr = pointerFlowGraph.getVarPtr(retVar);
                    addPFGEdge(retPtr, rPtr);
                });
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
            var ptn = n.getPointsToSet();
            var pts = entry.pointsToSet();
            // cal delta
            var delta = new PointsToSet();
            pts.objects()
                    .filter(pointer -> ptn.objects().noneMatch(pointer::equals))
                    .forEach(delta::addObject);
            propagate(n, delta);

            if (n instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                delta.objects().forEach(obj -> {
                    // store field
                    var.getStoreFields().forEach(storeStmt -> {
                        var y = pointerFlowGraph.getVarPtr(storeStmt.getRValue());
                        var field = storeStmt.getFieldRef().resolve();
                        var instanceField = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(y, instanceField);
                    });
                    // load field
                    var.getLoadFields().forEach(loadStmt -> {
                        var y = pointerFlowGraph.getVarPtr(loadStmt.getLValue());
                        var field = loadStmt.getFieldRef().resolve();
                        var instanceField = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(instanceField, y);
                    });
                    // array store
                    var.getStoreArrays().forEach(arrayStoreStmt -> {
                        var y = pointerFlowGraph.getVarPtr(arrayStoreStmt.getRValue());
                        var arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(y, arrayIndex);
                    });
                    // array load
                    var.getLoadArrays().forEach(arrayLoadStmt -> {
                        var y = pointerFlowGraph.getVarPtr(arrayLoadStmt.getLValue());
                        var arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, y);
                    });
                    // process call
                    processCall(var, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        if (!pointsToSet.isEmpty()) {
            var ptn = pointer.getPointsToSet();
            pointsToSet.forEach(ptn::addObject);
            pointerFlowGraph.getSuccsOf(pointer).forEach(s -> workList.addEntry(s, pointsToSet));
        }
        return pointsToSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        var invokes = var.getInvokes();
        invokes.forEach(invoke -> {
            var method = resolveCallee(recv, invoke);
            var thisVar = method.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(thisVar), new PointsToSet(recv));
            processCallHelper(invoke, method);
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(@Nullable Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
