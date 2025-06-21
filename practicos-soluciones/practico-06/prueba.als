sig Disk {
	gt: Disk
}


fact consistency {
	all d: Disk | not d in d.gt
	all d1, d2, d3: Disk |
		d1 in d2.gt and d2 in d3.gt implies d1 in d3.gt
}



pred show {}
run show for exactly 3 Disk