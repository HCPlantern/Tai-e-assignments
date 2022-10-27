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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // Your task is to recognize dead code in ir and add it to deadCode

        // dead variable
        ir.getStmts().forEach(stmt -> {
            SetFact<Var> liveVarsFact = liveVars.getResult(stmt);
            if (stmt instanceof AssignStmt<?, ?> assignStmt) {
                if (assignStmt.getLValue() instanceof Var var && hasNoSideEffect(assignStmt.getRValue())) {
                    if (!liveVarsFact.contains(var)) {
                        deadCode.add(stmt);
                    }
                }
            }
        });
        // unreachable stmt
        LinkedList<Stmt> list = new LinkedList<>();
        list.add(cfg.getEntry());
        Set<Stmt> visited = new HashSet<>();
        while (!list.isEmpty()) {
            Stmt stmt = list.removeFirst();
            visited.add(stmt);
            cfg.getOutEdgesOf(stmt)
                    .stream()
                    .filter(edge -> !isUnreachableBranch(edge, constants))
                    .map(Edge::getTarget)
                    .forEach(target -> {
                        if (!visited.contains(target)) {
                            list.add(target);
                        }
                    });
        }
        ir.forEach(stmt -> {
            if (!visited.contains(stmt)) {
                deadCode.add(stmt);
            }
        });

        return deadCode;
    }

    private boolean isUnreachableBranch(Edge<Stmt> edge, DataflowResult<Stmt, CPFact> constants) {
        Stmt source = edge.getSource();
        if (source instanceof If ifStmt) {
            Value value = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getResult(ifStmt));
            if (value.isConstant()) {
                return switch (edge.getKind()) {
                    case IF_TRUE -> value.getConstant() != 1;
                    case IF_FALSE -> value.getConstant() != 0;
                    default -> false;
                };
            }
        } else if (source instanceof SwitchStmt switchStmt) {
            Value value = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getResult(switchStmt));
            if (value.isConstant()) {
                return switch (edge.getKind()) {
                    case SWITCH_CASE -> edge.getCaseValue() != value.getConstant();
                    // if any other case is reachable, then the default case is unreachable
                    case SWITCH_DEFAULT -> switchStmt.getCaseValues()
                            .stream()
                            .anyMatch(caseValue -> caseValue == value.getConstant());
                    default -> false;
                };
            }
        }
        return false;
}

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
