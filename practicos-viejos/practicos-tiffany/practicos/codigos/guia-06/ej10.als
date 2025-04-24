open util/ordering[State] as states
open util/ordering[Stake] as stakes
open util/ordering[Disc] as discs

sig Stake { }

sig Disc { }

sig State {
  on: Disc -> one Stake  
}

fun discsOnStake[st: State, stake: Stake]: set Disc {
  stake.~(st.on)
}
fun topDisc[st: State, stake: Stake]: lone Disc {
  { d: st.discsOnStake[stake] | st.discsOnStake[stake] in discs/nexts[d] + d }
}

pred Move [st: State, fromStake, toStake: Stake, s: State] {
   let d = st.topDisc[fromStake] | {
      st.discsOnStake[toStake] in discs/nexts[d]
      s.discsOnStake[fromStake] = st.discsOnStake[fromStake] - d
      s.discsOnStake[toStake] = st.discsOnStake[toStake] + d
      let otherStake = Stake - fromStake - toStake |
        s.discsOnStake[otherStake] = st.discsOnStake[otherStake]
   }
}


pred Game1 {
   Disc in states/first.discsOnStake[stakes/first]
   some finalState: State | Disc in finalState.discsOnStake[stakes/last]

   all preState: State - states/last |
       let postState = states/next[preState] |
          some fromStake: Stake | {
             some preState.discsOnStake[fromStake]
             some toStake: Stake | preState.Move[fromStake, toStake, postState]
          }
}


pred Game2  {
   Disc in states/first.discsOnStake[stakes/first]
   some finalState: State | Disc in finalState.discsOnStake[stakes/last]

   all preState: State - states/last |
       let postState = states/next[preState] |
          some fromStake: Stake |
             let d = preState.topDisc[fromStake] | {
               some preState.discsOnStake[fromStake]
               postState.discsOnStake[fromStake] = preState.discsOnStake[fromStake] - d
               some toStake: Stake | {
                 preState.discsOnStake[toStake] in discs/nexts[d]
                 postState.discsOnStake[toStake] = preState.discsOnStake[toStake] + d
                let otherStake = Stake - fromStake - toStake |
                    postState.discsOnStake[otherStake] = preState.discsOnStake[otherStake]
                }
             }
      }

run Game1 for 1 but 3 Stake, 5 Disc, 32 State expect 1
run Game2 for 1 but 3 Stake, 3 Disc, 8 State expect 1
