// Se desea modelar en Alloy un sistema de administracion de aerolineas aereas. 
// Un esquema parcial se muestra en la Fig. 1. Cada aerolinea posee un conjunto 
// de vuelos, cada uno con su respectiva ciudad de origen y destino. Ademas cada
// vuelo tiene un horario de partida y otro de arribo. Es importante que el 
// numero de vuelo (VueloID) sea universalmente unico y este claramente definido. 
// Por lo tanto debera asegurar que:

sig VueloID, Ciudad, Horario {}

sig Aerolinea {
    nrovuelos: set VueloID,
    rutadirecta: nrovuelos -> one (Ciudad -> Ciudad),
    partidas: nrovuelos -> one Horario,
    arribos: nrovuelos -> one Horario
} {
    no (nrovuelos.rutadirecta) & iden
}

fact all_vuelos_asignados {
    all v: VueloID | some a: Aerolinea | v in a.nrovuelos
}



// Complete los tres puntitos de la definicion de Aerolinea, modifique la signatura, y/o agregue los hechos (facts) necesarios para asegurar que las condiciones anteriores se satisfagan.


// (i) para cada aerolinea, cada vuelo tiene una unica ruta directa asociada (i.e. una unica ciudad de origen y una unica ciudad de destino), un unico horario de partida, y un unico horario de llegada
// modificacion en la signature

// (ii) todos los numeros de vuelos de una aerolinea tienen asignado una ruta directa, y los horarios de partida y arribo


// (iii) los numeros de vuelo son globalmente unicos, es decir, dos aerolineas distintas no pueden tener el mismo numero de vuelo
fact unique_vuelo_id {
    all disj a1,a2: Aerolinea | no (a1.nrovuelos & a2.nrovuelos) 
}

//(iv) Defina, ademas, un predicado que, dada una aerolinea, una ciudad de origen, y una de destino, determine si es posible construir una ruta (no necesariamente directa) entre dichas ciudades.

pred vuelo [a: Aerolinea, c_partida, c_destino: Ciudad] {

    let conecciones = (a.nrovuelos).(a.rutadirecta)|
        c_partida -> c_destino in ^ conecciones
}

run vuelo for 3 but exactly 1 Aerolinea, exactly 2 VueloID, exactly 2 Ciudad
