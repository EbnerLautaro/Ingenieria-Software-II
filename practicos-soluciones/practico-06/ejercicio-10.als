open util/ordering[State] 

sig Disk {
    smaller: set Disk
}

sig Tower {}
one sig T1, T2, T3 extends Tower {}

fact propiedades {
    // Transitividad
    all d1, d2, d3: Disk |
        d2 in d1.smaller and d3 in d2.smaller => d3 in d1.smaller

    // Antisimetría
    all d1, d2: Disk |
        d1 in d2.smaller and d2 in d1.smaller => d1 = d2

    // Totalidad
    all disj d1, d2: Disk |
        d1 in d2.smaller or d2 in d1.smaller

    // Reflexividad
    all d: Disk | d in d.smaller
}

sig State {
    loc: Disk -> one Tower
} 

fact init {
    let s = first[] |
        all d: Disk | (s.loc)[d] = T1
}



fact trace {
    all s0: State, s1: next[s0] | 
        one d:Disk, from, to: Tower | 
            d in (s0.loc).from 
            and d in (s1.loc).to 
        

}   

pred show {}
run show for 3 but exactly 3 Disk, exactly 10 State
