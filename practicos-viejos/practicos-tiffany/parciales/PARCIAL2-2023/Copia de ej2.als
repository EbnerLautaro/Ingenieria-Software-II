sig VueloID, Ciudad, Horario, Alianza {}

sig Aerolinea {
    nrovuelos: set VueloID,
    rutadirecta: nrovuelos -> Ciudad -> Ciudad,
    partidas: nrovuelos -> Horario,
    arribos: nrovuelos -> Horario,
    socio: Alianza
}{
    // (a) y (b)
    all v: nrovuelos | 
        one rutadirecta[v] and 
        one partidas[v] and 
        one arribos[v]

    // (c)
    lone socio
}

// (d)
fact UnicidadVuelos {
    all a1, a2: Aerolinea | 
        (a1 != a2) => no (a1.nrovuelos & a2.nrovuelos)
}

// (e) auxiliar
fun AerolineaRutas[a: Aerolinea]: Ciudad -> Ciudad {
    {c1, c2: Ciudad | some v: a.nrovuelos | c1 -> c2 in a.rutadirecta[v]}
}

pred Ejemplo {
    // Asegura que haya al menos 2 ciudades
    #Ciudad > 2
    // Asegura que hay al menos 2 aerolíneas
    #Aerolinea > 1
    // Asegura que al menos una aerolínea tiene vuelos asociados
    all a: Aerolinea | #a.nrovuelos > 0
    // Asegura que hay al menos una ruta posible entre ciudades para alguna aerolínea
    some a: Aerolinea, d, o: Ciudad | d != o and RutaPosible2[a, o, d] and 
	not (some v: a.nrovuelos | o -> d in a.rutadirecta[v])
}


// (e)
pred RutaPosible[a: Aerolinea, o: Ciudad, d: Ciudad] {
    d in o.*(AerolineaRutas[a])
}

pred RutaPosible2[a: Aerolinea, o: Ciudad, d: Ciudad] {
    d in o.*(VueloID.(a.rutadirecta))
}

pred RutaPosible3[a: Aerolinea, o: Ciudad, d: Ciudad] {
	all v: VueloID | (o->d) in *(v.(a.rutadirecta))
}

assert ruta {
	all a: Aerolinea, o, d: Ciudad | RutaPosible[a, o, d] iff RutaPosible3[a, o ,d]
}

check ruta

run Ejemplo for 3 Ciudad, 3 Aerolinea, 5 VueloID, 4 Horario, 1 Alianza
