
// Memoria abstracta

sig Addr, Data { }

sig Memory{
    data: Addr -> lone Data
   }

pred write [ m_i, m_o: Memory, a: Addr, d: Data ] {
    m_o.data = m_i.data ++ a -> d
   }

pred read [ m: Memory, a: Addr, d_o: Data ] {
    let d = m.data[a] | some d implies d = d_o
}

// Sistema de Memoria Cache

sig Mem { 
    addrs: set Addr,
    map: addrs -> one Data 
   }

sig MainMemory extends Mem { }
sig Cache extends Mem {
    dirty: set addrs
   }

sig CacheSystem {
    cache: Cache,
    main: MainMemory
   }

pred writeMem [m_i,m_o: Mem, a: Addr, d: Data ] {
    m_o.map = m_i.map ++ (a -> d)
   }

pred writeSys [s_i,s_o: CacheSystem, a: Addr, d: Data ] {
    s_o.main = s_i.main
    writeMem [s_i.cache,s_o.cache,a,d]
    s_o.cache.dirty = s_i.cache.dirty + a
   }

// Función de abstracción

fun alpha [c: CacheSystem]: Memory {
    { m: Memory | m.data = c.main.map ++ c.cache.map }
   }

assert WriteOK {
    all c1, c2: CacheSystem, 
        a: Addr, d: Data, m1, m2: Memory |
           ( writeSys[c1,c2,a,d] and 
             m1 = alpha[c1] and m2 = alpha[c2] )
           =>
              write[m1,m2,a,d] 
   }

check WriteOK
