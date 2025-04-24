sig Addr, Data {}

sig Memory{
	addrs: set Addr,
	map: addrs -> one Data
 }

sig MainMemory extends Memory {}

sig Cache extends Memory{
	dirty: set addrs
 }

sig System {
	cache: Cache,
	main: MainMemory
 }

fact {
	all s:System | s.cache.addrs in s.main.addrs
 }

fact {
	all m:Memory | ~(m.map).(m.map) in iden
	all m:Memory | m.map.Data = m.addrs
 }

pred Write[s_i, s_o: System, a: Addr, d: Data]{
	a in s_i.cache.addrs =>
	s_o.cache.map = s_i.cache.map ++ (a->d)
	s_o.cache.dirty = s_i.cache.dirty ++ a
	s_o.main = s_i.main
}

pred Read[s_i, s_o: System, a: Addr, d: Data] {
    a in s_i.cache.addrs => {
        d = s_i.cache.map[a] 
        s_o.main = s_i.main
        s_o.cache = s_i.cache
    } a not in s_i.cache.addrs {
        Load[s_i, s_o, a] 
        d = s_o.cache.map[a]
    }
}

pred Load[s_i, s_o: System, a: Addr]{
	not a in s_i.cache.addrs =>
	let d = s_i.main.map[a] |
	s_o.cache.map = s_i.cache.map + (a -> d) 
}

pred Flush[s_i, s_o: System]{
	s_o.main.map = s_i.main.map ++ s_i.cache.map
	no s_o.cache.dirty
	s_o.cache.map = s_i.cache.map
}

pred Consistent{
	all s: System |
	all a: s.cache.addrs-s.cache.dirty |
	s.cache.map[a] = s.main.map[a]
 }

fact AllAddrsMapped{
    all a: Addr | some m: Memory | a in m.addrs
}

fact AllDataMapped{
    all d: Data | some m: Memory | some a: Addr | d in m.map[a]
}

assert ReadConsistency{
	all s_i, s_o: System | some a: Addr | some d: Data | 
	Read[s_i, s_o, a, d] => Consistent
}

assert WriteConsistency{
	all s_i, s_o: System | some a: Addr | some d: Data | 
	Write[s_i, s_o, a, d] => Consistent
}

assert FlushConsistency{
	all s_i, s_o: System | Flush[s_i, s_o] => Consistent
}

assert LoadConsistency{
	all s_i, s_o: System | some a: Addr | 
	Load[s_i, s_o, a] => Consistent
}


check ReadConsistency for 5 but exactly 1 System, 1 Memory, 1 Cache
