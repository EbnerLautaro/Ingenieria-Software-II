open util/ordering[State] 

// El dominio del problema ---------

abstract sig Object { eats: set Object }
 
one sig Farmer, Fox, Chicken, Grain
       extends Object { }

fact eating { eats = Fox -> Chicken + Chicken -> Grain }

// La dinámica --------------------
// Espacio de estado

sig State {
	near: set Object, 
	far: set Object 
	} 

// Estado inicial

fact initialState {
	let s0 = first[] | s0.near = Object && no s0.far 
}

// Transición

pred crossRiver [ from_i, from_o, to_i, to_o: set Object ] { 
	( from_o = from_i - Farmer && to_o = to_i - to_i.eats + Farmer) 
	||
	( some item: from_i - Farmer |
		from_o = from_i - Farmer - item &&
		to_o = to_i - to_i.eats + Farmer + item
		)
	} 

fact stateTransition {
	all s1: State, s2: next[s1] |
		( Farmer in s1.near => crossRiver [ s1.near, s2.near, s1.far, s2.far ] ) &&
		( Farmer in s1.far => crossRiver [ s1.far, s2.far, s1.near, s2.near ] )
}

// Estado Final

pred solvePuzzle[] {
	last[].far = Object 
}

// Ejecución

run solvePuzzle for 8 State 
