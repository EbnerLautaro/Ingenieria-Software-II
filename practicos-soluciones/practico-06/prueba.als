module tour/addressBook1
	sig Name, Addr {}
	sig Book {
	addr: Name -> lone Addr
}


pred show (b: Book) {
	#b.addr > 1
	#Name.(b.addr) > 1
}

pred add(b,bp: Book, n: Name, a: Addr) {
	bp.addr = b.addr + n->a
}

pred showAdd( b,bp: Book, n: Name, a: Addr) {
	add [b, bp, n, a]
	#Name.addr > 1
}

run showAdd for 3 but 2 Book
