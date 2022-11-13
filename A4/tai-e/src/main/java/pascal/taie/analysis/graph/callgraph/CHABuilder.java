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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod m = workList.poll();
            if (!callGraph.addReachableMethod(m)) {
                continue; // if call graph already contains m, skip it
            }
            callGraph.callSitesIn(m).forEach(cs -> resolve(cs)
                    .stream()
                    .filter(Objects::nonNull)
                    .forEach(callee -> {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, callee));
                        workList.offer(callee);
                    }));
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
        return switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> Collections.singleton(declaringClass.getDeclaredMethod(subsignature));
            case SPECIAL -> Collections.singleton(dispatch(declaringClass, subsignature));
            case INTERFACE, VIRTUAL -> {
                Set<JMethod> res = new HashSet<>();
                // for c or any of its subclasses, do dispatch
                res.add(dispatch(declaringClass, subsignature));
                Stream<JClass> class1 = hierarchy.getDirectImplementorsOf(declaringClass).stream();
                Stream<JClass> class2 = hierarchy.getDirectSubinterfacesOf(declaringClass).stream();
                Stream<JClass> class3 = hierarchy.getDirectSubclassesOf(declaringClass).stream();
                Stream.concat(class1, Stream.concat(class2, class3))
                        .map(c -> dispatch(c, subsignature))
                        .filter(Objects::nonNull)
                        .forEach(res::add);
                yield res;
            }
            default -> Collections.emptySet();
        };
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null) {
            return null;
        }
        return jclass.getDeclaredMethods()
                .stream()
                .filter(jMethod -> jMethod.getSubsignature().equals(subsignature))
                .filter(jMethod -> !jMethod.isAbstract()) // ignore abstract methods
                .findFirst()
                .orElse(dispatch(jclass.getSuperClass(), subsignature)); // else dispatch to super class
    }
}
