sig Editorial, Titulo, Autor, Revista, DOI, Topico {}

abstract sig Cuartil {}

one sig Q1, Q2, Q3, Q4 extends Cuartil {}

sig Hemeroteca {
	catalogo: set DOI,
	revistas: Revista -> one (Editorial -> Cuartil),
	articulos: DOI -> one (Titulo -> Revista),
	autorias: DOI -> some Autor, 
	topicos: DOI -> some Topico
} {
	articulos.Revista.Titulo = catalogo
	autorias.Autor = catalogo
	topicos.Topico = catalogo
	Titulo.(DOI.articulos) = revistas.Cuartil.Editorial
}

pred inciso_IV[h: Hemeroteca, t: Topico, jobs: set Titulo] {
	jobs = {(h.topicos.t).(h.articulos).Revista}
}

fun inciso_V[h: Hemeroteca, Q: Cuartil]: set Autor {
	{h.articulos.(h.revistas.Q.Editorial).Titulo.(h.autorias)}
}

assert inciso_VI{
	all h: Hemeroteca, Q1: Q1, Q2: Q2 |
		no (inciso_V[h, Q1] & inciso_V[h, Q2])
}

pred inciso_IV_alt[h: Hemeroteca, t: Topico, jobs: set Titulo]{
	jobs = {t1: Titulo | some r: Revista, d: DOI |
		(d->t) in h.topicos and (d->t1->r) in h.articulos}
}

assert equal {
	all h: Hemeroteca, t: Topico, jobs: set Titulo |
		inciso_IV[h, t, jobs] iff inciso_IV_alt[h, t, jobs]
}

fun inciso_V_alt[h: Hemeroteca, Q: Cuartil]: set Autor {
	{a: Autor | some r: Revista, e: Editorial, d: DOI, t: Titulo |
		(r->e->Q) in h.revistas and (d->t->r) in h.articulos and (d->a) in h.autorias}
}

assert equal2 {
	all h: Hemeroteca, Q: Cuartil |
		inciso_V[h, Q] = inciso_V_alt[h, Q]
}

check equal2
