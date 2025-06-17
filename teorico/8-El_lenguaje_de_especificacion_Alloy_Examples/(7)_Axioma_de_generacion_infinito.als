
// Dominio

abstract sig List {}

sig Element {}

one sig EmptyList extends List {}

sig NonEmptyList extends List {
    element: Element,
    rest: List
   }

// Axioma de generación generando infinitas listas

fact ListGenerator {
    all l1: List, e: Element |
        some l2: List | l2.rest = l1  and  l2.element = e
   }

// Aserción obviamente no válida que da verdadera

assert ObviouslyNotValid { all l1: List | all l2: List | l2.rest = l1 or l1 = l2 }

check ObviouslyNotValid

// Predicado auxiliar

pred show [] {}

// Genera sólo una instancia (la lista vacía)

run show

// No genera ninguna instancia

run show for 3 but exactly 1 Element
