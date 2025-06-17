

// El dominio del problema ---------

sig Addr, Data { }

sig Memory{
    data: Addr -> lone Data
   }

pred write (m_i, m_o: Memory, a: Addr, d: Data) {
    m_o.data = m_i.data ++ a -> d
}

pred read (m: Memory, a: Addr, d_o: Data) {
    let d = m.data[a] | some d implies d = d_o
}

run write for 3 but 1 Addr, 1 Data