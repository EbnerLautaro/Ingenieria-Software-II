//  Modele relaciones binarias en Alloy. Utilizando predicados, especifique que una relacion es:
//      (a) un preorden,
//      (b) un orden parcial,
//      (c) un orden total,
//      (d) un orden estricto,
//      (e) que tiene primer elemento,
//      (f) que tiene ultimo elemento.

sig Object {}
sig R {
    rel: Object -> Object
}


pred reflexividad[r: R] {
    all x: Object | x -> x in r.rel
}

pred transitividad[r: R] {
    all x, y, z: Object | (x -> y in r.rel && y -> z in r.rel) implies x -> z in r.rel
}

pred antisimetria[r: R] {
    all x, y: Object | (x -> y in r.rel && y -> x in r.rel) implies x = y
}

pred irreflexividad[r: R] {
    no x: Object | x -> x in r.rel
}

pred totalidad[r: R] {
    all disj x, y: Object | (x -> y in r.rel || y -> x in r.rel)
}

pred preorden[r: R] {
    reflexividad[r] 
    transitividad[r]
}
run preorden for 4 but exactly 4 Object, 1 R

pred orden_parcial[r: R] {
    reflexividad[r]
    transitividad[r]
    antisimetria[r]
}
run orden_parcial for 4 but exactly 4 Object, 1 R

pred orden_total[r: R] {
    reflexividad[r]
    transitividad[r]
    antisimetria[r]
    totalidad[r]
}
run orden_total for 4 but 1 Object, 1 R


pred primer_elemento[r: R] {
    one x: Object | 
        all y: Object | 
            x!=y implies (x -> y in r.rel and not y -> x in r.rel)

}
run primer_elemento for exactly 4 Object, 1 R


pred ultimo_elemento[r: R] {
    one x: Object | 
        all y: Object | 
            x!=y implies (y -> x in r.rel and not x -> y in r.rel)
}
run ultimo_elemento for exactly 4 Object, 1 R

//  Escriba aserciones para las siguientes propiedades:
//      - todo orden parcial es total;
//      - todo orden parcial tiene primer elemento;
//      - todo orden total con primer elemento x y ´ultimo elemento y satisface x 6= y;
//      - la union de ordenes estrictos es un orden estricto;
//      - la composici´on de ´ordenes estrictos es un orden estricto.
//  Analice estas propiedades usando el Alloy Analyzer.

assert parcial_es_total {
    all r: R | 
        orden_parcial[r] implies orden_total[r]
}
check parcial_es_total for exactly 1 R, 4 Object

assert parcial_tiene_primer {
    all r: R | 
        #r.rel> 1 implies  orden_parcial[r] implies primer_elemento[r]
}
check parcial_tiene_primer for exactly 1 R, 3 Object

pred is_primer_elemento [r: R, e: Object] {
    all x: Object |
        x!=e implies e->x in ^(R.rel) and x->e not in ^(R.rel)
}
pred is_ultimo_elemento [r: R, e: Object] {
    all x: Object |
        x!=e implies x->e in ^(R.rel) and e->x not in ^(R.rel)
}
assert total_loco {
    all r: R, x,y: Object |
        orden_total[r] and is_primer_elemento[r, x] and is_ultimo_elemento[r, y]
        implies x!=y
}
check total_loco for exactly 4 Object, 1 R

pred orden_estricto[r: R] {
    irreflexividad[r] and transitividad[r] and antisimetria[r]
}

assert union_ordenes_estrictos {
    all r, s: R | 
        orden_estricto[r] and orden_estricto[s] implies orden_estricto[r+s]
}
check union_ordenes_estrictos for exactly 2 R, 4 Object

assert composicion_ordened_esctrictos {
    all disj r, s: R | 
        orden_estricto[r] and orden_estricto[s] implies {
            let t = R | t.rel = (r.rel).(s.rel) and orden_estricto[t]
        }
}

check composicion_ordened_esctrictos for exactly 2 R, 4 Object