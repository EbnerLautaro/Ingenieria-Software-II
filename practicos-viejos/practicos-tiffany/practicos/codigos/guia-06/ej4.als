sig N {}

sig Grafo {
	nodos: set N,
	aristas: nodos -> nodos
}{
	#nodos >= 1
}

fact noLooseNodes{
	all n: N | some g: Grafo | n in g.nodos
}

fun idenNodos[]: (N -> N){
	iden & (N -> N)
}

fun univNodos[]: (N -> N){
	(N -> N)
}

pred aciclico[g: Grafo]{
	no (^(g.aristas) & ~(g.aristas))
}

pred aciclico2[g: Grafo]{
	no (^(g.aristas) & idenNodos)
}

pred noDirigido[g: Grafo]{
	g.aristas = ~(g.aristas)
}

pred strongConexo[g: Grafo]{
	^(g.aristas) + idenNodos = univNodos
}

pred conexo[g: Grafo]{
	^(g.aristas + ~(g.aristas)) = univNodos or #g.nodos = 1
}

pred componenteStrongConexo[g: Grafo]{
	some disj n1, n2: N |
		(n1 -> n2) in ^(g.aristas) and
		(n2 -> n1) in ^(g.aristas)
}

pred componenteConexo[g: Grafo]{
	some n1, n2: N |
		(n1 -> n2) in ^(g.aristas) or
		(n2 -> n1) in ^(~(g.aristas)) or
		#g.nodos = 1 or
		(no g.aristas and not no g.nodos)
}

assert equivalentesAciclico{
	all g: Grafo | aciclico[g] iff aciclico2[g]
}

assert strongConexoConexo{
	all g: Grafo | strongConexo[g] implies conexo[g]
}

pred componenteNotAll[g: Grafo]{
	componenteStrongConexo[g] and not strongConexo[g]
}

pred componenteNotAllConexo[g: Grafo]{
	componenteConexo[g] and not conexo[g]
}

pred componenteNotAllStrongConexo[g: Grafo]{
	componenteStrongConexo[g] and not strongConexo[g]
}

assert grafos{
	all g: Grafo | componenteConexo[g]
}

pred showConexo{
	all g: Grafo | all n: N | conexo[g] and n in g.nodos
}


run aciclico for 4 but exactly 1 Grafo
//check grafos for 5 but exactly 1 Grafo
run componenteNotAllStrongConexo for 4 but exactly 1 Grafo
