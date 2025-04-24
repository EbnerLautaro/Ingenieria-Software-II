//No funciona, hay que corregir
open util/ordering[State]

abstract sig Object { harms: set Object }
one sig Adult extends Object {}
one sig Kids extends Object {}
one sig Son1, Son2, Daughter1, Daughter2 extends Kids {}
one sig Mom, Dad, Cop extends Adult {}
one sig Criminal extends Object {}
one sig Balsa extends Object {
	driver: one Adult
}

/* Defines what can't be left alone */
fact { 
  harms = Criminal->Mom + Criminal->Dad + Criminal->Kids +
          Mom->Son1 + Mom->Son2 + 
          Dad->Daughter1 + Dad->Daughter2 
}

/* Stores the objects at near and far side of river. */
sig State {
  near, far: set Object
}

fact initialState {
     first.near = Object && no first.far
}

/*At most one item to move from 'from' to 'to'*/
pred crossRiver[from_i, from_o, to_i, to_o: set Object] {
    lone x: (from_i - Balsa.driver.harms) | {
      from_o = from_i - x - Balsa.driver - from_o.harms 
      to_o = to_i + x + Balsa.driver
    }
}

/* crossRiver transitions between states
fact {
  all s_i: State, s_o: s_i.next | some a: Adult {
    a in s_i.near => 
	crossRiver[s_i.near, s_o.near, s_i.far, s_o.far]
    else
	crossRiver[s_i.far, s_o.far, s_i.near, s_o.near]
  }
}*/

pred solvePuzzle[] {
	some s: State | s.far = Object
}


/* Run command to find a solution where all objects are on the far side */
run solvePuzzle
