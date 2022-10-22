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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact res = new CPFact();
        // initialize all the params of this function as NAC
        cfg.getIR().getParams().stream()
                .filter(ConstantPropagation::canHoldInt)
                .forEach(p -> res.update(p, Value.getNAC()));
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        // absence in CPFact represents UNDEF.
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, factVal) -> {
            Value targetVal = target.get(var);
            target.update(var, meetValue(factVal, targetVal));
        });

    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return v1;
            } else {
                return Value.getNAC();
            }
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact res = in.copy();
        // Reference types (e.g. class types and array types) are not supported.
        // Other primitive types are not supported too.
        // In other cases (e.g. field storage stmt like o.f = x), transfer function do nothing.
        if (stmt instanceof AssignStmt<?, ?> assignStmt) {
            LValue lValue = assignStmt.getLValue();
            RValue rValue = assignStmt.getRValue();
            if (lValue instanceof Var var) {
                if (canHoldInt(var)) {
                    in.remove(var);
                    res.update(var, evaluate(rValue, in));
                }
            }
        }
        return out.copyFrom(res);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            return in.get(var);
        } else if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof BinaryExp binaryExp) {
            Value value1 = in.get(binaryExp.getOperand1());
            Value value2 = in.get(binaryExp.getOperand2());
            // value1 and value2 are both constant
            if (value1.isConstant() && value2.isConstant()) {
                int int1 = value1.getConstant();
                int int2 = value2.getConstant();
                if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                    return switch (arithmeticExp.getOperator()) {
                        case ADD -> Value.makeConstant(int1 + int2);
                        case SUB -> Value.makeConstant(int1 - int2);
                        case MUL -> Value.makeConstant(int1 * int2);
                        case DIV -> int2 == 0 ? Value.getNAC() : Value.makeConstant(int1 / int2);
                        case REM -> int2 == 0 ? Value.getNAC() : Value.makeConstant(int1 % int2);
                    };
                } else if (binaryExp instanceof ConditionExp conditionExp) {
                    return switch (conditionExp.getOperator()) {
                        case EQ -> Value.makeConstant(int1 == int2 ? 1 : 0);
                        case NE -> Value.makeConstant(int1 != int2 ? 1 : 0);
                        case LT -> Value.makeConstant(int1 < int2 ? 1 : 0);
                        case LE -> Value.makeConstant(int1 <= int2 ? 1 : 0);
                        case GT -> Value.makeConstant(int1 > int2 ? 1 : 0);
                        case GE -> Value.makeConstant(int1 >= int2 ? 1 : 0);
                    };
                } else if (binaryExp instanceof ShiftExp shiftExp) {
                    return switch (shiftExp.getOperator()) {
                        case SHL -> Value.makeConstant(int1 << int2);
                        case SHR -> Value.makeConstant(int1 >> int2);
                        case USHR -> Value.makeConstant(int1 >>> int2);
                    };
                } else if (binaryExp instanceof BitwiseExp bitwiseExp) {
                    return switch (bitwiseExp.getOperator()) {
                        case AND -> Value.makeConstant(int1 & int2);
                        case OR -> Value.makeConstant(int1 | int2);
                        case XOR -> Value.makeConstant(int1 ^ int2);
                    };
                }
                // value1 or value2 is NAC
            } else if (value1.isNAC() || value2.isNAC()) {
                return Value.getNAC();
                // else return UNDEF
            } else {
                return Value.getUndef();
            }
        }
        return Value.getUndef();
    }
}
