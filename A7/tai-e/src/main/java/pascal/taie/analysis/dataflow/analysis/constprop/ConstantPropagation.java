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
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

import java.util.Optional;

import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.pta;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.valMap;

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
    public static Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        } else if (v1.isUndef() || v2.isUndef()) {
            return v1.isUndef() ? v2 : v1;
        } else if (v1.isConstant() && v2.isConstant()) {
            return v1.getConstant() == v2.getConstant() ? v1 : Value.getNAC();
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact res = in.copy();
        Optional<LValue> lValue = stmt.getDef();
        // 左侧是 Var 且能 hold int
        if (lValue.isPresent() && lValue.get() instanceof Var var && canHoldInt(var)) {
            res.remove(var); // 这里是对 res 更改，不是 in （一开始写错了）
            // 对右侧进行检查
            if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
                RValue rValue = definitionStmt.getRValue();
                if (rValue instanceof IntLiteral || rValue instanceof Var || rValue instanceof BinaryExp) {
                    res.update(var, evaluate(rValue, in)); // 这里是传进去原始的 in
                    return out.copyFrom(res);
                }
            }
            res.update(var, Value.getNAC());
        }
        // 左侧不是Var, 恒等函数，即不处理
        return out.copyFrom(res);
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
                        case DIV -> int2 == 0 ? Value.getUndef() : Value.makeConstant(int1 / int2);
                        case REM -> int2 == 0 ? Value.getUndef() : Value.makeConstant(int1 % int2);
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
            } else if (value1.isNAC()) {
                // NAC / 0 or NAC % 0 returns UNDEF
                if (value2.isConstant() && value2.getConstant() == 0) {
                    if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                        return switch (arithmeticExp.getOperator()) {
                            case DIV, REM -> Value.getUndef();
                            default -> Value.getNAC();
                        };
                    }
                }
                return Value.getNAC();
            } else if (value2.isNAC()) {
                return Value.getNAC();
            } else {
                // else return UNDEF
                return Value.getUndef();
            }
        } else if (exp instanceof InstanceFieldAccess access) {
            var val = Value.getUndef();
            for (Obj obj : pta.getPointsToSet(access.getBase())) {
                val = meetValue(val, valMap.getOrDefault(new Pair<>(obj, access.getFieldRef()), Value.getUndef()));
            }
            return val;
        } else if (exp instanceof StaticFieldAccess access) {
            return valMap.getOrDefault(
                    new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef()),
                    Value.getUndef()
            );
        } else if (exp instanceof ArrayAccess access) {
            var index = evaluate(access.getIndex(), in);
            var val = Value.getUndef();
            if (index.isConstant()) {
                for (Obj obj : pta.getPointsToSet(access.getBase())) {
                    val = meetValue(val, valMap.getOrDefault(new Pair<>(obj, index), Value.getUndef()));
                    val = meetValue(val, valMap.getOrDefault(new Pair<>(obj, Value.getNAC()), Value.getUndef()));
                }
            } else if (index.isNAC()) {
                for (Obj obj : pta.getPointsToSet(access.getBase())) {
                    for (var entry : valMap.entrySet()) {
                        var accessPair = entry.getKey();
                        if (accessPair.first().equals(obj) && accessPair.second() instanceof Value) {
                            val = meetValue(val, entry.getValue());
                        }
                    }
                }
            }
            return val;
        }

        return Value.getNAC(); // should not reach here
    }
}
