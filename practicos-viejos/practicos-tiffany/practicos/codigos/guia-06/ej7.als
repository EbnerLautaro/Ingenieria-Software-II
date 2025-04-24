sig Interprete {}

sig Cancion {}

sig Catalogo {
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
}{
	interpretes = interpretaciones[canciones]
	canciones = (~interpretaciones)[interpretes]
}

pred add[ci, co: Catalogo, s: Cancion, i: Interprete] {
	co.interpretaciones = ci.interpretaciones + (s -> i)
}

pred delete[ci, co: Catalogo, s: Cancion, i: Interprete] {
	co.interpretaciones = ci.interpretaciones - (s -> i)
}

assert addDelete {
	all c: Catalogo| all s: Cancion | all i: Interprete |
	all co: Catalogo | add[c, co, s, i] => (delete[co, c, s, i] or (s -> i) in c.interpretaciones)
}

fun coInterprete[c: Catalogo]: (Interprete -> Interprete) {	
	~(c.interpretaciones).(c.interpretaciones) 
	- (iden & (Interprete -> Interprete))
}

check addDelete
run delete for 3 but 2 Catalogo
