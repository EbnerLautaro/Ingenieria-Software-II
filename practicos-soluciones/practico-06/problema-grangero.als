open util/ordering[State]

abstract sig Object {
    eats: set Object
}


one sig Farmer, Fox, Chicken, Grain extends Object {} 


fact eating {
    no Farmer.eats
    no Grain.eats
    Fox.eats = Chicken
    Chicken.eats = Grain

    // Otra opcion puede ser
    // eats = Fox -> Chicken + Chicken -> Grain 
}

sig State {
    west: set Object,
    east: set Object
}

fact init {
    let s0 = first[] |
        no s0.east and s0.west = Object
} 

pred cross_river [from_i, from_o, to_i, to_o: set Object] {

    (
        // solo cruza el Farmer, luego el resultado es que se comen los que se pueden comer
        from_o = from_i - Farmer && to_o = to_i - to_i.eats + Farmer
    ) or (
        // cruza el Farmer con otro
        some o: from_i - Farmer | 
            from_o = from_i - o - Farmer && to_o = to_i - to_i.eats + Farmer + o  
    )
}

fact traces {
    all s1: State, s2: next[s1] |
        (
            Farmer in s1.west implies cross_river[s1.west, s2.west, s1.east, s2.east]
        ) and (
            Farmer in s1.east implies cross_river[s1.east, s2.east, s1.west, s2.west]
        ) 
}

pred solve_puzle {
    last[].east = Object
}

run solve_puzle for 8 State