sig VueloID, Ciudad, Horario, Alianza {}

sig Aerolinea {
    vuelos: set VueloID,
    rutadirecta: vuelos -> Ciudad -> Ciudad,
    partidas: vuelos -> Horario,
    arribos: vuelos -> Horario,
    socio: Alianza
}{
    // (a) y (b)
    all v: vuelos | 
        one rutadirecta[v] and 
        one partidas[v] and 
        one arribos[v]

    // (c)
    lone socio
}

// (d)
fact UnicidadVuelos {
    all a1, a2: Aerolinea | 
        (a1 != a2) => no (a1.vuelos & a2.vuelos)
}

// (e) auxiliar
fun AerolineaRutas[a: Aerolinea]: Ciudad -> Ciudad {
    {c1, c2: Ciudad | some v: a.vuelos | c1 -> c2 in a.rutadirecta[v]}
}

pred Ejemplo {
    // Asegura que haya al menos 2 ciudades
    #Ciudad > 2
    // Asegura que hay al menos 2 aerolíneas
    #Aerolinea > 1
    // Asegura que al menos una aerolínea tiene vuelos asociados
    all a: Aerolinea | #a.vuelos > 0
    // Asegura que hay al menos una ruta posible entre ciudades para alguna aerolínea
    some a: Aerolinea, d, o: Ciudad | d != o and RutaPosible[a, o, d] and 
	not (some v: a.vuelos | o -> d in a.rutadirecta[v])
}

// (e)
pred RutaPosible[a: Aerolinea, o: Ciudad, d: Ciudad] {
    d in o.*(AerolineaRutas[a])
}

// (f)
fun RutasDirectas[al: Alianza, o: Ciudad, d: Ciudad, p: Horario]: set VueloID {
	{v: VueloID | some a: Aerolinea | a.socio = al and 
		(o->d) in a.rutadirecta[v] and (v->p) in a.partidas}
}

run Ejemplo for 3 Ciudad, 3 Aerolinea, 5 VueloID, 4 Horario, 1 Alianza
