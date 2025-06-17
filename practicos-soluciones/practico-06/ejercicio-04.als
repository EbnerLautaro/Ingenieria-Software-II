//  Modele grafos dirigidos y algunas de sus operaciones en Alloy.
//  Utilice predicados para especificar que:
//      (a) el grafo es aciclico
//      (b) el grafo es no dirigido
//      (c) el grafo es fuertemente conexo
//      (d) el grafo es conexo
//      (e) el grafo contiene una componente fuertemente conexa
//      (f) el grafo contiene una componente conexa

sig Node {}
sig Graph {
    nodes: set Node,
    edges: nodes -> nodes
}{
    #nodes >= 1 // un grafo tiene al menos un Nodo
}

fact no_loose_nodes {
    all n: Node | some g: Graph | n in g.nodes 
}

fun univ_nodes: (Node -> Node) {
    (Node -> Node)
}

pred acyclic(g: Graph) {
    no ^(g.edges) & iden
    // not (all n: g.nodes |  n->n in ^(g.edges))
}
run acyclic for 1 but exactly 1 Graph, 4 Node


pred undirected(g: Graph) {
    all n1,n2: g.nodes | 
        (n1 -> n2 in g.edges) implies (n2 -> n1 in g.edges)
}
run undirected for 4 but exactly 1 Graph


pred strongly_connected(g: Graph) {
    all n1, n2: g.nodes | n1 -> n2 in ^(g.edges)
}
run strongly_connected for 1 but 1 Graph, 4 Node

pred weekly_connected(g: Graph) {
    all n1, n2: g.nodes | 
        (n1->n2 in ^(g.edges) || n2->n1 in ^(g.edges))
}
run weekly_connected for 1 but 1 Graph, 4 Node



