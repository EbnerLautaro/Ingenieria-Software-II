// Se desea modelar en Alloy la manipulacion de catalogos de musica. 
// Estos catalogos contienen canciones, interpretes y el listado de canciones interpretadas. 
// Esta estructura podrıa modelarse de la siguiente manera:

sig Interprete {}

sig Cancion {}

sig Catalogo {
    canciones: set Cancion,
    interpretes: set Interprete,
    interpretaciones: canciones -> interpretes
}{
    // Se dice que un catalogo es consistente si todas las canciones del catalogo estan registradas por
    // algun interprete y todo interprete del catalogo tiene registrada alguna cancion. Complete los tres
    // puntitos de la definicion de Catalogo para que asegure consistencia.
    all c: interpretes | c in canciones.interpretaciones // interpretaciones[canciones]
    all i: canciones | i in interpretes.(~interpretaciones) // (~interpretaciones)[interpretes]
}

fun iden_interprete: (Interprete -> Interprete) {
    iden & (Interprete -> Interprete)
}

// (a) Un predicado que dado un catalogo y una cacnion con su interprete, devuelva un nuevo catalogo
// igual al primero pero con esa interpretacion agragada.
pred add[cat_i, cat_o: Catalogo, c: Cancion, i: Interprete] {
    cat_o.interpretaciones = cat_i.interpretaciones ++ (c -> i) 
}

// (b) Un predicado que dado un catalogo y una cancion con su interprete, devuelva un nuevo catalogo
// igual al primero pero eliminando esa interpretacion.
pred delete[cat_i, cat_o: Catalogo, c: Cancion, i: Interprete] {
    cat_o.interpretaciones = cat_i.interpretaciones - (c -> i)
}

// (c) Una funcion que, dado un catalogo, devuelva los pares de interpretes que interpretan la misma
// cancion.
fun get_interpretes[c: Catalogo]: (Interprete -> Interprete) {
    // todos los interpretes relacionados a travez de una cancion, menos la identidad de interpretes
    (c.interpretaciones) . (~(c.interpretaciones)) - iden_interprete
}




