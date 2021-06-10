include "file1.dfy"

module Host {
  import opened Base
  import opened Environment

  datatype Message = Transfer(table:imap<int,int>)

  datatype Constants = Constants(id:HostId)
  datatype Variables = Variables(table:imap<int,int>)

  predicate Get(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>, key:int, value:int) {
    && key in state.table
    && state.table[key] == value
    && state' == state
    && a.rcv.None?
    && a.send == {}
  }

  predicate Put(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>, key:int, value:int) {
    && key in state.table
    && state'.table == state.table[key := value]
    && a.rcv.None?
    && a.send == {}
  }

  predicate SendShard(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>, m:Message) {
    && a.rcv.None?
    && a.send == {m}
    && m.table.Keys <= state.table.Keys
    && (forall key :: key in m.table ==> m.table[key] == state.table[key])
    && state'.table == MapRemove(state.table, m.table.Keys)
  }

  predicate ReceiveShard(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>) {
    && a.rcv.Some?
    && a.send == {}
    && var m := a.rcv.value;
    && state'.table == IMapUnionPreferLeft(state.table, m.table)
  }

  predicate Init(constants:Constants, state:Variables, id:HostId) {
    state.table == if id == 0 then ZeroMap() else EmptyMap()
  }

  datatype Step =
    | GetStep(key:int, value:int)
    | PutStep(key:int, value:int)
    | SendShardStep(m:Message)
    | ReceiveShardStep()

  predicate NextStep(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>, step:Step) {
    match step {
      case GetStep(key, value) => Get(constants, state, state', a, key, value)
      case PutStep(key, value) => Put(constants, state, state', a, key, value)
      case SendShardStep(m) => SendShard(constants, state, state', a, m)
      case ReceiveShardStep() => ReceiveShard(constants, state, state', a)
    }
  }
}

module ShardedHashTable refines DistributedSystem {
  import Host

  type M = Host.Message
  type HConstants = Host.Constants
  type HVariables = Host.Variables
  type HStep(!new,==) = Host.Step

  predicate HInit(constants:HConstants, state:HVariables, id:HostId) {
    Host.Init(constants, state, id)
  }

  predicate HNextStep(constants:HConstants, state:HVariables, state':HVariables, a:NetAction<M>, step:HStep) {
    Host.NextStep(constants, state, state', a, step)
  }
}
