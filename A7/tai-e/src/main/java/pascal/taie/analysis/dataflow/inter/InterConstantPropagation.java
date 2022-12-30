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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

import java.util.*;
/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";
    public static final Map<Obj, Set<Var>> aliasMap = new HashMap<>();
    public static final Map<Pair<?, ?>, Value> valMap = new HashMap<>();
    public static final Map<Pair<JClass, FieldRef>, Set<LoadField>> staticLoadFields = new HashMap<>();
    private final ConstantPropagation cp;
    public static PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here

        pta.getVars().forEach(var -> {
            pta.getPointsToSet(var).forEach(obj -> {
                Set<Var> s = aliasMap.getOrDefault(obj, new HashSet<>());
                s.add(var);
                aliasMap.put(obj, s);
            });
        });

        icfg.getNodes().forEach(stmt -> {
            if(stmt instanceof LoadField loadField && loadField.getFieldAccess() instanceof StaticFieldAccess access){
                var accessPair = new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef());
                var set = staticLoadFields.getOrDefault(accessPair, new HashSet<>());
                set.add(loadField);
                staticLoadFields.put(accessPair, set);
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact res = out.copy();
        Stmt source = edge.getSource();
        if (source instanceof DefinitionStmt<?, ?> definitionStmt) {
            // if this definition statement has a left-side var, then getDef() is not null
            if (definitionStmt.getDef().isPresent() && definitionStmt.getDef().get() instanceof Var var) {
                res.remove(var);
            }
        }
        return res;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // Passing arguments at call site to parameters of the callee
        CPFact res = newInitialFact();
        if (edge.getSource() instanceof Invoke invoke) {
            InvokeExp invokeExp = invoke.getInvokeExp();
            if (!(invokeExp instanceof InvokeDynamic) && invokeExp.getMethodRef().getSubsignature().equals(edge.getCallee().getSubsignature())) {
                List<Var> args = invokeExp.getArgs();
                List<Var> params = edge.getCallee().getIR().getParams();
                for (int i = 0; i < args.size(); i++) {
                    Var arg = args.get(i);
                    Var param = params.get(i);
                    if (canHoldInt(param)) {
                        res.update(param, callSiteOut.get(arg));
                    }
                }
            }
        }
        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact res = newInitialFact();
        if (edge.getCallSite() instanceof Invoke invoke) {
            Var var = invoke.getResult();
            if (var != null && canHoldInt(var)) {
                Value returnValue = edge.getReturnVars()
                        .stream()
                        .map(returnOut::get)
                        .reduce(Value.getUndef(), ConstantPropagation::meetValue);
                res.update(var, returnValue);
            }
        }
        return res;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType primitiveType) {
            return switch (primitiveType) {
                case BYTE, SHORT, INT, CHAR, BOOLEAN -> true;
                default -> false;
            };
        }
        return false;

    }
}

