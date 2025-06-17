
// Dominio

sig Element {}

sig Set {
    elements: set Element
   }

// Aserción obviamente válida

assert Closed {
    all s0, s1: Set | some s2: Set |
        s2.elements = s0.elements + s1.elements
   }

check Closed
