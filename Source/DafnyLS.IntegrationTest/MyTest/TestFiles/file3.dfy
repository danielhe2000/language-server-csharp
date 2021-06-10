include "file2.dfy"

abstract module RefinementTheorem {
  import HashTable
  import opened Environment
  import opened ShardedHashTable

  function Ik(constants:Constants) : HashTable.Constants
  function I(constants:Constants, state:Variables) : HashTable.Variables
  predicate Inv(constants:Constants, state:Variables)

  lemma RefinementInit(constants:Constants, state:Variables)
    requires Init(constants, state)
    ensures Inv(constants, state) // Inv base case
    ensures HashTable.Init(Ik(constants), I(constants, state))  // Refinement base case

  lemma RefinementNext(constants:Constants, state:Variables, state':Variables)
    requires Next(constants, state, state')
    requires Inv(constants, state)
    // ensures Inv(constants, state')  // Inv inductive step
    // ensures HashTable.Next(Ik(constants), I(constants, state), I(constants, state'))
    //     || I(constants, state) == I(constants, state') // Refinement inductive step
}

module RefinementProof refines RefinementTheorem {
  import opened Base

  function Ik(constants:Constants) : HashTable.Constants
  {
    HashTable.Constants()
  }

  datatype MapOwner = HostOwner(id:HostId) | MessageOwner(msg:Host.Message)
  type MapGathering = map<MapOwner,imap<int,int>>

  predicate MapsAreDisjoint(maps:MapGathering)
  {
    forall src1, src2 :: src1 in maps && src2 in maps && src1 != src2 ==> maps[src1].Keys !! maps[src2].Keys
  }

  // forall-exists puts Dafny in a bad mood
  predicate  MapsAreFull(maps:MapGathering)
  {
    forall key :: exists src :: src in maps && key in maps[src]
  }

  predicate MapsPartitionFullMap(maps:MapGathering)
  {
    && MapsAreDisjoint(maps)
    && MapsAreFull(maps)
  }

  function HostMaps(constants:Constants, state:Variables) : (hm:MapGathering)
  {
    var sourceSet := set i | true :: HostOwner(i);
    map src | src in sourceSet :: state.hosts[src.id].table
  }

  function TransferMaps(constants:Constants, state:Variables) : MapGathering
  {
    var sourceSet := set m | m in state.network.messageSet :: MessageOwner(m);
    map src | src in sourceSet :: src.msg.table
  }

  function LiveMaps(constants:Constants, state:Variables) : MapGathering
  {
    MapUnionPreferLeft(HostMaps(constants, state), TransferMaps(constants, state))
  }

  // Dafny'state :| should be deterministic (functional), but it ain't.
  function TheOwnerYouChoose(maps:MapGathering) : MapOwner
    requires maps != map[]
  {
    var source :| source in maps; source
  }

  function DisjointMapUnion(maps:MapGathering) : imap<int,int>
  {
    if maps == map[]
    then EmptyMap()
    else
      var source := TheOwnerYouChoose(maps);
      IMapUnionPreferLeft(DisjointMapUnion(MapRemoveOne(maps, source)), maps[source])
  }

  function ForceFilled(m:imap<int,int>) : HashTable.FullMap
  {
    if HashTable.IsFull(m) then m else ZeroMap()
  }

  function I(constants:Constants, state:Variables) : HashTable.Variables
  {
    HashTable.Variables(ForceFilled(DisjointMapUnion(LiveMaps(constants, state))))
  }

  predicate Inv(constants:Constants, state:Variables) {
    MapsPartitionFullMap(LiveMaps(constants, state))
  }

  lemma GatheringOfEmptyMaps(mg:MapGathering)
    requires forall src :: src in mg ==> mg[src] == EmptyMap()
    ensures DisjointMapUnion(mg) == EmptyMap()
  {
  }

  lemma EmptyMapsDontMatter(mg:MapGathering, vsrc:MapOwner)
    requires vsrc in mg.Keys
    requires forall src :: src in mg && src != vsrc ==> mg[src] == EmptyMap()
    ensures DisjointMapUnion(mg) == mg[vsrc]
  {
    if mg.Keys != {vsrc} {
      var csource := TheOwnerYouChoose(mg);
      if csource == vsrc {
        GatheringOfEmptyMaps(MapRemoveOne(mg, csource));
      } else {
        EmptyMapsDontMatter(MapRemoveOne(mg, csource), vsrc);
      }
    }
  }

  lemma RefinementInit(constants:Constants, state:Variables)
    //requires Init(constants, state) // inherited from abstract module
    ensures Inv(constants, state)
    ensures HashTable.Init(Ik(constants), I(constants, state))
  {
    assert LiveMaps(constants, state)[HostOwner(0)] == ZeroMap();  // TRIGGER
    EmptyMapsDontMatter(LiveMaps(constants, state), HostOwner(0));
    //reveal_MapsAreFull();
  }

  // Controlled revelation: access a little bit of MapsAreFull definition without getting trigger-crazy.
  function  UseMapsAreFull(maps:MapGathering, key:int) : (src:MapOwner)
    requires MapsAreFull(maps)
    ensures src in maps && key in maps[src]
  {
    //reveal_MapsAreFull();
    var src :| src in maps && key in maps[src];
    src
  }

  lemma PutKeepsMapsFull(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>, key:int, value:int)
    requires Inv(constants, state)
    requires NextStep(constants, state, state', id, a, Host.PutStep(key, value))
    ensures MapsAreFull(LiveMaps(constants, state'))
  {
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    forall key
      ensures exists src' :: src' in maps' && key in maps'[src']
    {
      var src := UseMapsAreFull(maps, key);
      assert src in maps' && key in maps'[src];
    }
    //reveal_MapsAreFull();
  }

  lemma SendShardKeepsMapsFull(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>, msg:Host.Message)
    requires Inv(constants, state)
    requires NextStep(constants, state, state', id, a, Host.SendShardStep(msg))
    ensures MapsAreFull(LiveMaps(constants, state'))
  {
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    forall key
      ensures exists src' :: src' in maps' && key in maps'[src']
    {
      var src := if key in msg.table then MessageOwner(msg) else UseMapsAreFull(maps, key);
      assert src in maps' && key in maps'[src];
    }
    //reveal_MapsAreFull();
  }

  lemma ReceiveShardKeepsMapsFull(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>)
    requires Inv(constants, state)
    requires NextStep(constants, state, state', id, a, Host.ReceiveShardStep())
    ensures MapsAreFull(LiveMaps(constants, state'))
  {
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    forall key
      ensures exists src' :: src' in maps' && key in maps'[src']
    {
      var oldSrc := UseMapsAreFull(maps, key);
      var src := if oldSrc == MessageOwner(a.rcv.value) then HostOwner(id) else oldSrc;
      assert src in maps' && key in maps'[src];
    }
    //reveal_MapsAreFull();
  }

  lemma DisjointMapsDontContainKey(maps:MapGathering, key:int)
    requires forall src :: src in maps ==> key !in maps[src]
    ensures key !in DisjointMapUnion(maps)
  {
  }

  lemma DisjointMapsMapKeyToValue(maps:MapGathering, src:MapOwner, key:int)
    requires MapsAreDisjoint(maps)
    requires src in maps
    requires key in maps[src]
    ensures key in DisjointMapUnion(maps)
    ensures DisjointMapUnion(maps)[key] == maps[src][key]
  {
    if maps.Keys != {src} {
      var rSrc := TheOwnerYouChoose(maps);
      if src == rSrc {
        DisjointMapsDontContainKey(MapRemoveOne(maps, rSrc), key);
        assert key !in DisjointMapUnion(MapRemoveOne(maps, rSrc));
      } else {
        DisjointMapsMapKeyToValue(MapRemoveOne(maps, rSrc), src, key);
      }
    }
  }

  lemma MapsPartitionImpliesIsFull(maps:MapGathering)
    requires MapsPartitionFullMap(maps)
    ensures HashTable.IsFull(DisjointMapUnion(maps))
  {
    //HashTable.reveal_IsFull();
    forall key ensures key in DisjointMapUnion(maps)
    {
      var src := UseMapsAreFull(maps, key);
      DisjointMapsMapKeyToValue(maps, src, key);
    }
  }

  lemma TimeoutTest(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>)
    requires Inv(constants, state)
    requires NextStep(constants, state, state', id, a, Host.ReceiveShardStep())
  {
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    assert true;
    assert true;
    assert true;
    {
      assert true;
      assert true;
      if(true){
        assert true;
        assert true;
        forall key ensures exists src' :: src' in maps' && key in maps'[src']
        {
          var oldSrc := UseMapsAreFull(maps, key);
          var src := if oldSrc == MessageOwner(a.rcv.value) then HostOwner(id) else oldSrc;
          assert src in maps' && key in maps'[src];
        }
        assert true;
      }
      assert true;
    }
    assert MapsAreFull(LiveMaps(constants, state'));
    assert true;
    assert false;
    //reveal_MapsAreFull();
  }

  lemma RefinementNext(constants:Constants, state:Variables, state':Variables)
    // requires Next(constants, state, state')
    // requires Inv(constants, state)
    // ensures Inv(constants, state')  // Inv inductive step
  {
    assert true;
    assert true;
    assert true;
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    var id, a, step :| ShardedHashTable.NextStep(constants, state, state', id, a, step);
    var hostconstants := constants.hosts[id];
    var hoststate := state.hosts[id];
    var hoststate' := state'.hosts[id];
    match step {
      case GetStep(key, value) => {
        assert state == state';
        DisjointMapsMapKeyToValue(maps, HostOwner(id), key);
        MapsPartitionImpliesIsFull(maps);
      }
      case PutStep(key, value) => {
        forall src1, src2 | src1 in maps' && src2 in maps' && src1 != src2
        ensures maps'[src1].Keys !! maps'[src2].Keys
        {
          var oldMap := state.hosts[id].table;
          if src1 == HostOwner(id) {
            assert maps[src1] == oldMap;  // TRIGGER disjointness hypothesis
            assert maps[src2] == maps'[src2];
          } else if src2 == HostOwner(id) {
            assert maps[src1] == maps'[src1];
            assert maps[src2] == oldMap;
          } else {
            assert maps[src1] == maps'[src1];
            assert maps[src2] == maps'[src2];
          }
        }
        PutKeepsMapsFull(constants, state, state', id, a, key, value);
        MapsPartitionImpliesIsFull(maps);
        MapsPartitionImpliesIsFull(maps');
        forall kk
          ensures I(constants, state').table[kk] == I(constants, state).table[key := value][kk]
        {
          if kk == key {
            DisjointMapsMapKeyToValue(maps', HostOwner(id), key);
          } else {
            var src := UseMapsAreFull(maps, kk);
            var src' := UseMapsAreFull(maps', kk);
            DisjointMapsMapKeyToValue(maps, src, kk);
            DisjointMapsMapKeyToValue(maps', src', kk);
            if src == HostOwner(id) {
              if src' != HostOwner(id) {
                assert maps[src'] == maps'[src'];
                assert false;
              }
            } else {
              if src' != src {
                assert maps[src'] == maps'[src'];
                assert false;
              }
            }
          }
        }
        assert HashTable.NextStep(Ik(constants), I(constants, state), I(constants, state'), HashTable.PutStep(key, value)); // trigger
      }
      case SendShardStep(msg) => {
        forall src1, src2 | src1 in maps' && src2 in maps' && src1 != src2
        ensures maps'[src1].Keys !! maps'[src2].Keys
        {
          if src1 == HostOwner(id) {
            assert maps'[src1].Keys <= maps[src1].Keys;
          } else if src1 == MessageOwner(msg) {
            assert maps'[src1].Keys <= maps[HostOwner(id)].Keys;
          } else {
            assert maps'[src1].Keys == maps[src1].Keys; // trigger
          }
          if src2 == HostOwner(id) {
            assert maps'[src2].Keys <= maps[src2].Keys;
          } else if src2 == MessageOwner(msg) {
            assert maps'[src2].Keys <= maps[HostOwner(id)].Keys;
          } else {
            assert maps'[src2].Keys == maps[src2].Keys; // trigger
          }
        }
        SendShardKeepsMapsFull(constants, state, state', id, a, msg);
        MapsPartitionImpliesIsFull(maps);
        MapsPartitionImpliesIsFull(maps');
        forall kk
          ensures I(constants, state').table[kk] == I(constants, state).table[kk]
        {
          var src := UseMapsAreFull(maps, kk);
          var src' := UseMapsAreFull(maps', kk);
          DisjointMapsMapKeyToValue(maps, src, kk);
          DisjointMapsMapKeyToValue(maps', src', kk);
          if src' == MessageOwner(msg) {
            if src != HostOwner(id) {
              assert kk in maps[HostOwner(id)];
              assert false;
            }
          } else {
            if src != src' {
              assert kk in maps[src'];
              assert false;
            }
          }
        }
      }
      case ReceiveShardStep() => {
        var msg := a.rcv.value;
        forall src1, src2 | src1 in maps' && src2 in maps' && src1 != src2
        ensures maps'[src1].Keys !! maps'[src2].Keys
        {
          if src1 == HostOwner(id) {
            assert maps[src1].Keys <= maps'[src1].Keys;
            assert maps[MessageOwner(msg)].Keys <= maps'[src1].Keys;
          } else {
            assert maps'[src1].Keys == maps[src1].Keys; // trigger
          }
          if src2 == HostOwner(id) {
            assert maps[src2].Keys <= maps'[src2].Keys;
            assert maps[MessageOwner(msg)].Keys <= maps'[src2].Keys;
          } else {
            assert maps'[src2].Keys == maps[src2].Keys; // trigger
          }
        }
        ReceiveShardKeepsMapsFull(constants, state, state', id, a);
        MapsPartitionImpliesIsFull(maps);
        MapsPartitionImpliesIsFull(maps');
        forall kk
          ensures I(constants, state').table[kk] == I(constants, state).table[kk]
        {
          var src := UseMapsAreFull(maps, kk);
          var src' := UseMapsAreFull(maps', kk);
          DisjointMapsMapKeyToValue(maps, src, kk);
          DisjointMapsMapKeyToValue(maps', src', kk);
          if src == MessageOwner(msg) {
            if src' != HostOwner(id) {
              assert kk in maps'[HostOwner(id)];
              assert false;
            }
            assert maps'[src'][kk] == IMapUnionPreferLeft(maps[src'], maps[src])[kk];
          } else {
            if src != src' {
              assert kk in maps'[src];
              assert false;
            }
          }
        }
      }
    }
  }
}