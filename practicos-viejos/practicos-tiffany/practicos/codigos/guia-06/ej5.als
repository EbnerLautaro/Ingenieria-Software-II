sig Elem {}

sig Rel {
	rel: Elem -> Elem
}

fun idenElem[]: (Elem -> Elem){
	(iden & (Elem -> Elem))
}

fun univElem[]: (Elem -> Elem){
	(Elem -> Elem)
}

pred reflexiva[r: Rel]{
	idenElem in r.rel
}

pred sim[r: Rel]{
	(r.rel in ~(r.rel))
}

pred asim[r:Rel]{
	no (r.rel & ~(r.rel))
}

pred antisim[r: Rel]{
	(r.rel & ~(r.rel)) in idenElem
}

pred transitiva[r: Rel]{
	(r.rel).(r.rel) in r.rel
}

pred totalidad[r: Rel]{
	(r.rel + ~(r.rel)) = univElem
}

pred preorden[r: Rel]{
	reflexiva[r] 
	transitiva[r]
}

pred poset[r: Rel]{
	preorden[r] 
	antisim[r]
}

pred total[r: Rel]{
	poset[r]
	totalidad[r]
}

pred estricto[r: Rel]{
	not reflexiva[r]
	asim[r]
	transitiva[r]
}

pred isPrimerElem[r: Rel, e: Elem]{
	all a: Elem | some b: Elem | 
	(a -> b in r.rel or b -> a in r.rel) => (e -> a in r.rel) 
}

pred isUltimoElem[r: Rel, e: Elem]{
	all a: Elem | some b: Elem | 
	(a -> b in r.rel or b -> a in r.rel) => (a -> e in r.rel) 
}

pred primerElem[r: Rel] {
    one e: Elem | isPrimerElem[r, e] and poset[r]
}

pred ultimoElem[r: Rel] {
    one e: Elem | isUltimoElem[r, e] and poset[r]
}

fun getPrimerElem[r: Rel]: lone Elem {
    { e: Elem | isPrimerElem[r, e] }
}

fun getUltimoElem[r: Rel]: lone Elem {
    { e: Elem | isUltimoElem[r, e] }
}

//Todo orden parcial es total
assert parcialEsTotal{
	all r: Rel | poset[r] implies total[r]
}

//Todo orden parcial tiene primer elemento
//Contraejemplo solo relaciones reflexivas
assert parcialTienePrimer{
	all r:Rel | (#r.rel > 0) and poset[r] => primerElem[r]
}

//Si r es un orden total con primer elemento x e ultimo elemento y entonces x != y
//El unico contrajemplo es cuando r tiene un solo elemento 
assert primerUltimoDistintos {
    	all r: Rel | let x = getPrimerElem[r] | let y = getUltimoElem[r] | 
	total[r] and x != none and y != none => x != y
}

//La union de dos ordenes estrictos es un orden estricto
assert unionEstrictos{
	all r, s: Rel | estricto[r] and estricto[s] => estricto[r+s]
}

//La composicion de dos ordenes estrictos es un orden estricto
assert composicionEstrictos {
    all r, s: Rel | 
        estricto[r] and estricto[s] => {
            let c = Rel | c.rel = (r.rel) . (s.rel) and estricto[c]
        }
}

check composicionEstrictos for 5 but exactly 2 Rel
run primerElem for 5 but exactly 1 Rel 
check parcialTienePrimer for 5 but exactly 1 Rel

