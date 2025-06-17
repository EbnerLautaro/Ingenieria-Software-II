
// Dominio

sig Element {}

sig Set {
    elements: set Element
   }

// Axioma de generación

fact SetGenerator {
    some s: Set | no s.elements
    all s1: Set, e: Element |
        some s2: Set | s2.elements = s1.elements + e
   }

// Aserción obviamente válida

assert Closed {
    all s0, s1: Set | some s2: Set |
        s2.elements = s0.elements + s1.elements
   }

check Closed


