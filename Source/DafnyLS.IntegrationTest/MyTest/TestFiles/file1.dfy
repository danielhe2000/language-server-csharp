module Base {
  function ZeroMap() : imap<int,int>
  {
    imap i | true :: 0
  }

  function EmptyMap() : imap<int,int>
  {
    imap i | false :: 0
  }

  function MapUnionPreferLeft<K(!new),V>(a:map<K,V>, b:map<K,V>) : map<K,V>
  {
    map key | key in a.Keys + b.Keys :: if key in a then a[key] else b[key]
  }

  function IMapUnionPreferLeft(a:imap<int,int>, b:imap<int,int>) : imap<int,int>
  {
    imap key | key in a || key in b :: if key in a then a[key] else b[key]
  }

  function  MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
    ensures forall k :: k in m && k != key ==> k in m'
    ensures forall k :: k in m' ==> k in m && k != key
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    var m':= map j | j in m && j != key :: m[j];
    assert m'.Keys == m.Keys - {key};
    m'
  }

  function MapRemove(table:imap<int,int>, removeKeys:iset<int>) : imap<int,int>
    requires removeKeys <= table.Keys
  {
    imap key | key in table && key !in removeKeys :: table[key]
  }

}

//////////////////////////////////////////////////////////////////////////////
// Application spec

module HashTable {
  import opened Base

  predicate  IsFull(m:imap<int, int>) {
    forall i :: i in m
  }
  function FullMapWitness() : (m:imap<int,int>)
    ensures IsFull(m)
  {
    //reveal_IsFull();
    imap key:int | true :: 0
  }
  type FullMap = m: imap<int, int> | IsFull(m)
    ghost witness FullMapWitness()

  datatype Constants = Constants()
  datatype Variables = Variables(table:FullMap)
  
  predicate Init(constants:Constants, state:Variables) {
    state.table == ZeroMap()
  }

  predicate Get(constants:Constants, state:Variables, state':Variables, key:int, value:int) {
    && state.table[key] == value
    && state' == state
  }

  predicate Put(constants:Constants, state:Variables, state':Variables, key:int, value:int) {
    && state'.table == state.table[key := value]
  }

  datatype Step = GetStep(key:int, value:int) | PutStep(key:int, value:int)

  predicate NextStep(constants:Constants, state:Variables, state':Variables, step:Step) {
    match step {
      case GetStep(key, value) => Get(constants, state, state', key, value)
      case PutStep(key, value) => Put(constants, state, state', key, value)
    }
  }

  predicate Next(constants:Constants, state:Variables, state':Variables) {
    exists step :: NextStep(constants, state, state', step)
  }
}

//////////////////////////////////////////////////////////////////////////////
// Environment spec

module Environment {
  function NumHosts() : nat
    ensures NumHosts() > 0

  newtype HostId = b: int | 0 <= b < NumHosts()
  function AllHosts() : set<HostId> {
    set h:HostId | true
  }
  datatype Option<V> = None | Some(value:V)
  datatype NetAction<M> = NetAction(rcv:Option<M>, send:set<M>)
}

module Network {
  import opened Environment

  datatype Constants = Constants()
  datatype Variables<M> = Variables(messageSet:set<M>)

  predicate Init(constants:Constants, state:Variables) {
    state.messageSet == {}
  }

  predicate Next(constants:Constants, state:Variables, state':Variables, a:NetAction) {
    && (a.rcv.Some? ==> a.rcv.value in state.messageSet)
    && state'.messageSet == state.messageSet + a.send - if a.rcv.Some? then {a.rcv.value} else {}
  }
}

abstract module DistributedSystem {
  import opened Environment
  import Network

  // parameters filled in by refining module
  type M(!new,==)
  type HConstants
  type HVariables
  type HStep(!new,==)
  predicate HInit(constants:HConstants, state:HVariables, id:HostId)
  predicate HNextStep(constants:HConstants, state:HVariables, state':HVariables, a:NetAction<M>, step:HStep)

  type HostMap<V> = m:map<HostId, V> | m.Keys == AllHosts()
    ghost witness var v:V :| true; map h:HostId | h in AllHosts() :: v
  type HostConstantsMap = HostMap<HConstants>
  type HostVariablesMap = HostMap<HVariables>
  datatype Constants
    = Constants(hosts:HostConstantsMap, network:Network.Constants)
  datatype Variables
    = Variables(hosts:HostVariablesMap, network:Network.Variables<M>)
  
  predicate Init(constants:Constants, state:Variables) {
    && (forall id :: HInit(constants.hosts[id], state.hosts[id], id))
    && Network.Init(constants.network, state.network)
  }

  predicate NextStep(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>, step:HStep) {
    && HNextStep(constants.hosts[id], state.hosts[id], state'.hosts[id], a, step)
    && (forall other :: other != id ==> state'.hosts[other] == state.hosts[other])
    && Network.Next(constants.network, state.network, state'.network, a)
  }

  predicate Next(constants:Constants, state:Variables, state':Variables) {
    exists id, a, step :: NextStep(constants, state, state', id, a, step)
  }
}