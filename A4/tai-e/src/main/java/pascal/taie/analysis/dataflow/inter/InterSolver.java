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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        Set<Node> entryNodes = new HashSet<>();
        icfg.entryMethods().map(icfg::getEntryOf).forEach(node -> {
            entryNodes.add(node);
            result.setInFact(node, analysis.newBoundaryFact(node));
            result.setOutFact(node, analysis.newBoundaryFact(node));
        });
        icfg.getNodes().forEach(node -> {
            if (!entryNodes.contains(node)) {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        });
    }

    private void doSolve() {
        Queue<Node> workList = new LinkedList<>(icfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact in = result.getInFact(node);
            Fact out = result.getOutFact(node);
            icfg.getInEdgesOf(node).forEach(inEdge -> {
                Fact outFact = result.getOutFact(inEdge.getSource());
                Fact transferredFact = analysis.transferEdge(inEdge, outFact);
                analysis.meetInto(transferredFact, in);
            });
            if (analysis.transferNode(node, in, out)) {
                icfg.getSuccsOf(node).forEach(workList::offer);
            }
        }
    }
}
