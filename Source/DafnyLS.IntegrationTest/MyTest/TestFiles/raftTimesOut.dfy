module MissingLibrary {

function Last<T>(s:seq<T>) : T  // TODO move to library
    requires 0<|s|
{
    s[|s|-1]
}

function {:opaque} EmptyImap<K(!new),V>() : (e:imap<K,V>)
    ensures e.Keys == iset{}
{
    var v :| true;
    imap k | k in {} :: v
}

function {:opaque} EmptyMap<K(!new),V>() : (e:map<K,V>)
    ensures e.Keys == {}
{
    var v :| true;
    map k | k in {} :: v
}

function {:opaque} MapRemove<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures m'.Keys == m.Keys - {k}
    ensures forall j :: j in m' ==> m'[j] == m[j]
{
    map j | j in m && j != k :: m[j]
}

function {:opaque} SingletonImap<K,V>(k:K, v:V) : (m:imap<K,V>)
    ensures m.Keys == iset {k}
    ensures m[k] == v
{
    imap j | j == k :: v
}

function {:opaque} MapUnionPreferB<U,T>(mapa: map<U,T>, mapb: map<U,T>) : (mapc:map<U,T>)
    ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapb.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapa.Keys && !(k in mapb.Keys) ==> mapc[k] == mapa[k]; // no-set-op translation is easier for Dafny
{
    map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapb then mapb[x] else mapa[x]
}

function {:opaque} ImapUnionPreferB<U,T>(mapa: imap<U,T>, mapb: imap<U,T>) : (mapc:imap<U,T>)
    ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapb.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapa.Keys && !(k in mapb.Keys) ==> mapc[k] == mapa[k]; // no-set-op translation is easier for Dafny
{
    imap x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapb then mapb[x] else mapa[x]
}

datatype Option<V> = None | Some(value:V)

function max(a:int, b:int) : int
{
    if a>b then a else b
}

function {:opaque} MemsetSeq<V>(v:V, len:nat) : (s:seq<V>)
    ensures |s| == len
    ensures forall i :: 0<=i<len ==> s[i] == v
{
    if len == 0 then [] else MemsetSeq(v, len-1) + [v]
}

} // module

/*
 * Translation of Diego Ongaro's TLA spec into dafny-tla.
 * This translation: Jon Howell, CC-BY 4.0
 *
 * Original:
 * Copyright 2014 Diego Ongaro.
 * This work is licensed under the Creative Commons Attribution-4.0
 * International License https://creativecommons.org/licenses/by/4.0/
 */
module raft {
import opened MissingLibrary

type ServerID(!new,==)
function ServerIDs() : set<ServerID>

type Value(!new,==)

datatype ServerState = Follower | Candidate | Leader

datatype LogEntry = LogEntry(term:int, value:Value)

type Log = seq<LogEntry>

datatype Message =
      RequestVoteRequest(
        term:int,
        lastLogTerm:int,
        lastLogIndex:int,
        source:ServerID,
        dest:ServerID)
    | RequestVoteResponse(
        term:int,
        voteGranted:bool,
        // logGhost (was: mlog) is used as a history variable for the proof.
        // It would not exist in a real implementation.
        logGhost:Log,
        source:ServerID,
        dest:ServerID)
    | AppendEntriesRequest(
        term:int,
        prevLogIndex:int,
        prevLogTerm:int,
        entries:seq<LogEntry>,
            // jonh notes that there seems to be an unstated constraint that
            // all the log entries in an AppendEntriesRequest share a common
            // term value. Are the equal to .term? Why not make entries a seq
            // of values?
        // logGhost (was: mlog) is used as a history variable for the proof.
        // It would not exist in a real implementation.
        logGhost:Log,
        commitIndex:int,
        source:ServerID,
        dest:ServerID)
    | AppendEntriesResponse(
        term:int,
        success:bool,
        matchIndex:int,
        source:ServerID,
        dest:ServerID)

predicate WFMessage(m:Message) {
    && m.source in ServerIDs()
    && m.dest in ServerIDs()
}

//////////////////////////////////////////////////////////////////////////////
// Global variables

type Messages = multiset<Message>

datatype ElectionRecord = ElectionRecord(
    term:int,
    leader:ServerID,
    log:Log,
    votes:set<ServerID>,
    voterLog:map<ServerID, Log>
    )

datatype GlobalVars = GlobalVars(
    // A bag of records representing requests and responses sent from one server
    // to another.
    // jonh using Dafny multiset because original comment wanted it:
    // TLAPS doesn't support the Bags module, so this is a function
    // mapping Message to Nat.
    messages:Messages,

    // A history variable used in the proof. This would not be present in an
    // implementation.
    // Keeps track of successful elections, including the initial logs of the
    // leader and voters' logs. Set of functions containing various things about
    // successful elections (see BecomeLeader).
    elections:set<ElectionRecord>,

    // A history variable used in the proof. This would not be present in an
    // implementation.
    // Keeps track of every log ever in the system (set of logs).
    allLogs:set<Log>
)
    

//////////////////////////////////////////////////////////////////////////////
// The following variables are all per server (functions with domain Server).

datatype ServerVars = ServerVars(
    // The server's term number.
    currentTerm:int,

    // The server's state (Follower, Candidate, or Leader).
    state:ServerState,

    // The candidate the server voted for in its current term, or
    // Nil if it hasn't voted for any.
    votedFor:Option<ServerID>
    )

datatype LogVars = LogVars(
    // A Sequence of log entries. The index into this sequence is the index of
    // the log entry.
    log:Log,

    // The index of the latest entry in the log the state machine may apply.
    commitIndex: int
    )

datatype CandidateVars = CandidateVars(
    // The set of servers from which the candidate has received a RequestVote
    // response in its currentTerm.
    votesResponded:set<ServerID>,

    // The set of servers from which the candidate has received a vote in its
    // currentTerm.
    votesGranted:set<ServerID>,

    // A history variable used in the proof. This would not be present in an
    // implementation.  Function from each server that voted for this candidate
    // in its currentTerm to that voter's log.
    voterLog:map<ServerID, Log>
    )

datatype LeaderVars = LeaderVars(
    // The next entry to send to each follower.
    nextIndex:map<ServerID, int>,

    // The latest entry that each follower has acknowledged is the same as the
    // leader's. This is used to calculate commitIndex on the leader.
    matchIndex:map<ServerID, int>
)

predicate WFLeaderVars(l:LeaderVars) {
    && l.nextIndex.Keys == ServerIDs()
    && l.matchIndex.Keys == ServerIDs()
}

datatype HostVars = HostVars(
    server:ServerVars,
    log:LogVars,
    candidate:CandidateVars,
    leader:LeaderVars)

datatype Variables = Variables(
    host:map<ServerID, HostVars>,
    global:GlobalVars
    )

//////////////////////////////////////////////////////////////////////////////

// Helpers

// The set of all quorums. This just calculates simple majorities, but the only
// important property is that every quorum overlaps with every other.
// jonh rewhacked as predicate for easier predicate logicking.
predicate IsQuorum(servers:set<ServerID>)
{
    |servers| * 2 > |ServerIDs()|
}

// The term of the last entry in a log, or 0 if the log is empty.
function LastTerm(xlog:Log) : int {
    if |xlog| == 0 then 0 else xlog[|xlog|-1].term
}

// Helper for Send and Reply. Given a message m and bag of messages, return a
// new bag of messages with one more m in it.
function WithMessage(m:Message, msgs:Messages) : Messages
{
    msgs + multiset{m}
}

// Helper for Discard and Reply. Given a message m and bag of messages, return
// a new bag of messages with one less m in it.
function WithoutMessage(m:Message, msgs:Messages) : Messages
{
    msgs - multiset{m}
}

// Add a message to the bag of messages.
predicate Send(messages:multiset<Message>, messages':multiset<Message>, m:Message) {
    messages' == WithMessage(m, messages)
}

// Remove a message from the bag of messages. Used when a server is done
// processing a message.
predicate Discard(messages:multiset<Message>, messages':multiset<Message>, m:Message) {
    messages' == WithoutMessage(m, messages)
}

// Combination of Send and Discard
predicate Reply(messages:multiset<Message>, messages':multiset<Message>, response:Message, request:Message) {
    messages' == WithoutMessage(request, WithMessage(response, messages))
}

function EmptyVoterLog() : map<ServerID, Log>
{
    EmptyMap()
}

function Min(a:int, b:int) : int
{
    if a < b then a else b
}

function Max(a:int, b:int) : int
{
    if a > b then a else b
}

predicate WFVars(v:Variables) {
    && v.host.Keys == ServerIDs()
    && (forall s :: s in v.host ==> WFLeaderVars(v.host[s].leader))
}

// Define initial values for all variables
predicate InitHistoryVars(v:Variables) {
    && v.global.elections == {}
    && v.global.allLogs == {}
    && WFVars(v)
    && (forall s :: s in ServerIDs()
        ==> v.host[s].candidate.voterLog == EmptyVoterLog())
}

predicate InitServerVars(server:ServerVars) {
    && server.currentTerm == 1
    && server.state == Follower
    && server.votedFor == None
}

predicate InitCandidateVars(c:CandidateVars) {
    && c.votesResponded == {}
    && c.votesGranted == {}
}

function {:opaque} MapAll(i:int) : (m:map<ServerID, int>)
    ensures m.Keys == ServerIDs()
    ensures forall s :: s in m ==> m[s] == i
{
    map s | s in ServerIDs() :: i
}

// The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
// leader does not send itself messages. It's still easier to include these
// in the functions.

predicate InitLeaderVars(l:LeaderVars) {
    && l.nextIndex == MapAll(1)
    && l.matchIndex == MapAll(0)
}

predicate InitLogVars(l:LogVars) {
    && l.log == []
    && l.commitIndex == 0
}

predicate InitHostVars(h:HostVars) {
    && InitServerVars(h.server)
    && InitLogVars(h.log)
    && InitCandidateVars(h.candidate)
    && InitLeaderVars(h.leader)
}

predicate InitGlobalVars(g:GlobalVars) {
    && g.messages == multiset{}
}

predicate Init(v:Variables) {
    && InitGlobalVars(v.global)
    && InitHistoryVars(v)
    && (forall s :: s in ServerIDs() ==> InitHostVars(v.host[s]))
}

//////////////////////////////////////////////////////////////////////////////
// Define state transitions

// Server i restarts from stable storage.
// It loses everything but its currentTerm, votedFor, and log.
predicate RestartHost(h:HostVars, h':HostVars)
{
    && h'.server.state == Follower
    && h'.candidate.votesResponded == {}
    && h'.candidate.votesGranted == {}
    && h'.candidate.voterLog == EmptyVoterLog()
    && h'.leader.nextIndex == MapAll(1)
    && h'.leader.matchIndex == MapAll(0)
    && h'.log.commitIndex == 0

    // UNCHANGED
    && h'.server.currentTerm == h.server.currentTerm
    && h'.server.votedFor == h.server.votedFor
    && h'.log.log == h.log.log
}

predicate UnchangedAllHosts(v:Variables, v':Variables)
    requires WFVars(v) && WFVars(v')
{
    //forall s :: s in ServerIDs() ==> v'.host[s] == v.host[s] // below is cleaner!
    v'.host == v.host
}

predicate UnchangedOtherHosts(v:Variables, v':Variables, s:ServerID)
    requires WFVars(v) && WFVars(v')
    requires s in ServerIDs()
{
    forall s2 :: s2 in ServerIDs() && s2 != s ==> v'.host[s2] == v.host[s2]
}

predicate Restart(v:Variables, v':Variables, s:ServerID)
    requires WFVars(v) && WFVars(v')
{
    && s in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && RestartHost(v'.host[s], v.host[s])
    && UnchangedOtherHosts(v', v, s)
    && v'.global == v.global
}

// Server i times out and starts a new election.
predicate TimeoutHost(h:HostVars, h':HostVars)
{
    && (h.server.state.Follower? || h.server.state.Candidate?)
    && h'.server.state.Candidate?
    && h'.server.currentTerm == h.server.currentTerm + 1
    && h'.server.votedFor == None
    && h'.candidate.votesResponded == {}
    && h'.candidate.votesGranted == {}
    && h'.candidate.voterLog == EmptyVoterLog()
    && h'.leader == h.leader
    && h'.log == h.log
}

predicate Timeout(v:Variables, v':Variables, s:ServerID)
    requires WFVars(v) && WFVars(v')
{
    && s in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && TimeoutHost(v.host[s], v'.host[s])
    // Most implementations would probably just set the local vote
    // atomically, but messaging localhost for it is weaker.
    && UnchangedOtherHosts(v', v, s)
    && v'.global == v.global
}

// Candidate i sends j a RequestVote request.
predicate RequestVote(v:Variables, v':Variables, i:ServerID, j:ServerID)
    requires WFVars(v) && WFVars(v')
{
    && i in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && j in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && var h := v.host[i];
    && h.server.state.Candidate?
    && !(j in h.candidate.votesResponded)
    && UnchangedAllHosts(v', v)
    && v'.global.elections == v.global.elections
    && Send(v.global.messages, v'.global.messages,
        RequestVoteRequest(
            h.server.currentTerm,
            LastTerm(h.log.log),
            |h.log.log|,
            i,
            j))
}

function PrevLogIndex(h:HostVars, j:ServerID) : int
    requires WFLeaderVars(h.leader)
    requires j in ServerIDs()
    requires h.server.state.Leader?
{
    h.leader.nextIndex[j] - 1
}

function PrevLogTerm(h:HostVars, j:ServerID) : int
    requires WFLeaderVars(h.leader)
    requires j in ServerIDs()
    requires h.server.state.Leader?
{
    if PrevLogIndex(h, j) > 0
        // jonh new constraint needed for Dafny's eager bounds checking
        && PrevLogIndex(h, j) < |h.log.log|
    then h.log.log[PrevLogIndex(h, j)].term
    else 0
}

// Send up to 1 entry, constrained by the end of the log.
function LastEntry(h:HostVars, j:ServerID) : int
    requires WFLeaderVars(h.leader)
    requires j in ServerIDs()
    requires h.server.state.Leader?
{
    Min(|h.log.log|, h.leader.nextIndex[j])
}

function Entries(h:HostVars, j:ServerID) : seq<LogEntry>
    requires WFLeaderVars(h.leader)
    requires j in ServerIDs()
    requires h.server.state.Leader?
    requires 0 <= h.leader.nextIndex[j] < |h.log.log|
{
    h.log.log[h.leader.nextIndex[j] .. LastEntry(h, j)]
}

// Leader i sends j an AppendEntries request containing up to 1 entry.
// While implementations may want to send more than 1 at a time, this spec uses
// just 1 because it minimizes atomic regions without loss of generality.
predicate AppendEntries(v:Variables, v':Variables, i:ServerID, j:ServerID)
    requires WFVars(v) && WFVars(v')
{
    && i in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && j in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && var h := v.host[i];
    && i != j
    && h.server.state.Leader?

    && UnchangedAllHosts(v', v)
    && v'.global.elections == v.global.elections
    && 0 <= h.leader.nextIndex[j] < |h.log.log| // NB absent from TLA source spec; is it an invariant? No, because |h.log.log| can be zero.
    && Send(v.global.messages, v'.global.messages,
        AppendEntriesRequest(
            h.server.currentTerm,
            PrevLogIndex(h, j),
            PrevLogTerm(h, j),
            Entries(h, j),
            h.log.log,
            Min(h.log.commitIndex, LastEntry(h, j)),
            i,
            j))
}

// Candidate i transitions to leader.
predicate BecomeLeaderHost(h:HostVars, h':HostVars)
{
    && h.server.state.Candidate?
    && IsQuorum(h.candidate.votesGranted)
    && h'.server.state.Leader?
    && h'.server.currentTerm == h.server.currentTerm
    && h'.server.votedFor == h.server.votedFor
    && h'.log == h.log
    && h'.candidate == h.candidate
    && h'.leader.nextIndex == MapAll(|h.log.log| + 1)  // XXX +1 for 1-based TLA seqs?
    && h'.leader.matchIndex == MapAll(0)
}

function MakeElectionRecord(h:HostVars, i:ServerID) : ElectionRecord
{
    ElectionRecord(
        h.server.currentTerm,
        i,
        h.log.log,
        h.candidate.votesGranted,
        h.candidate.voterLog)
}

predicate BecomeLeader(v:Variables, v':Variables, i:ServerID)
    requires WFVars(v) && WFVars(v')
{
    && i in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && BecomeLeaderHost(v.host[i], v'.host[i])
    && UnchangedOtherHosts(v', v, i)
    && v'.global.messages == v.global.messages
    && v'.global.elections == v.global.elections + {MakeElectionRecord(v.host[i], i)}
}


// Leader i receives a client request to add value to the log.
predicate ClientRequestHost(h:HostVars, h':HostVars, value:Value)
{
    && h.server.state.Leader?
    && var entry := LogEntry(h.server.currentTerm, value);
    && h'.log.log == h.log.log + [entry]
    && h'.log.commitIndex == h.log.commitIndex
    && h'.server == h.server
    && h'.candidate == h.candidate
    && h'.leader == h.leader
}

predicate ClientRequest(v:Variables, v':Variables, i:ServerID, value:Value)
    requires WFVars(v) && WFVars(v')
{
    && i in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && ClientRequestHost(v.host[i], v'.host[i], value)
    && UnchangedOtherHosts(v', v, i)
    && v'.global == v.global
    // NB bug in source TLA doesn't constrain elections
}

// Leader i advances its commitIndex.
// This is done as a separate step from handling AppendEntries responses,
// in part to minimize atomic regions, and in part so that leaders of
// single-server clusters are able to mark entries committed.

// The set of servers that agree up through index.
function {:opaque} Agree(h:HostVars, index:int) : (a:set<ServerID>)
    requires WFLeaderVars(h.leader)
    ensures forall k :: k in a ==> k in ServerIDs()
    ensures forall k :: k in a ==> h.leader.matchIndex[k] >= index
{
    set k | k in ServerIDs() && h.leader.matchIndex[k] >= index
}

predicate QuorumAtIndex(h:HostVars, index:int)
    requires WFLeaderVars(h.leader)
{
    IsQuorum(Agree(h, index))
}

// The [sic: maximum] indexes for which a quorum agrees
// jonh uses a seq instead of a set to simplify MaxAgreeIndex definition.
// This is still probably overkill, since there's surely a stability property.
// But I'm trying to stay close to the source TLA.
function {:opaque} AgreeIndexesDef(h:HostVars, limit:nat) : (ai:seq<int>)
    requires WFLeaderVars(h.leader)
    ensures forall index :: index in ai ==> 0 <= index < limit
    ensures forall index :: index in ai ==> QuorumAtIndex(h, index)
    decreases limit
{
    if limit == 0
    then []
    else AgreeIndexesDef(h, limit-1) + if QuorumAtIndex(h, limit-1) then [limit-1] else []
}

function AgreeIndexes(h:HostVars) : (ai:seq<int>)
    requires WFLeaderVars(h.leader)
{
    AgreeIndexesDef(h, |h.log.log|)
}

function {:opaque} SeqMax(q:seq<int>) : (m:int)
    requires 0<|q|
    ensures forall i :: 0<=i<|q| ==> m >= q[i]
    ensures m in q
{
    if |q| == 1
    then q[0]
    else Max(SeqMax(q[..|q|-1]), q[|q|-1])
}

function MaxAgreeIndex(h:HostVars) : (index:int)
    requires WFLeaderVars(h.leader)
    requires AgreeIndexes(h) != []
    ensures index in AgreeIndexes(h)
    ensures forall i2 :: i2 in AgreeIndexes(h) ==> i2 <= index
{
    SeqMax(AgreeIndexes(h))
}

function NewCommitIndex(h:HostVars) : int
    requires WFLeaderVars(h.leader)
{
    if |AgreeIndexes(h)| == 0
        then h.log.commitIndex
    else if h.log.log[MaxAgreeIndex(h)].term != h.server.currentTerm
        then h.log.commitIndex
    else
        MaxAgreeIndex(h)
}

predicate AdvanceCommitIndexHost(h:HostVars, h':HostVars)
    requires WFLeaderVars(h.leader)
{
    && h.server.state.Leader?
    && h'.log.commitIndex == NewCommitIndex(h)
    && h'.log.log == h.log.log
    && h'.server == h.server
    && h'.candidate == h.candidate
    && h'.leader == h.leader
    // NB bug in source TLA doesn't constrain elections
}

// NB TLA spec doesn't actually define "applying a log entry at a given index
// to its state machine", so State Machine Safety isn't even definable yet! Sigh.
predicate AdvanceCommitIndex(v:Variables, v':Variables, i:ServerID)
    requires WFVars(v) && WFVars(v')
{
    && i in ServerIDs() // NB TLA spec never actually establishes this type constraint
    && AdvanceCommitIndexHost(v.host[i], v'.host[i])
    && UnchangedOtherHosts(v', v, i)
    && v'.global == v.global
}

//////////////////////////////////////////////////////////////////////////////
// Message handlers
// i = recipient, j = sender, m = message

// Server i receives a RequestVote request from server j with
// m.mterm <= currentTerm[i].

predicate VoteLogOk(h:HostVars, m:Message)
    requires m.RequestVoteRequest?
{
    || m.lastLogTerm > LastTerm(h.log.log)
    || (
        && m.lastLogTerm == LastTerm(h.log.log)
        && m.lastLogIndex >= |h.log.log|
       )
}

predicate Grant(h:HostVars, j:ServerID, m:Message)
    requires j in ServerIDs()
    requires m.RequestVoteRequest?
{
    && m.term == h.server.currentTerm
    && VoteLogOk(h, m)
    && (|| h.server.votedFor.None?
        || h.server.votedFor == Some(j))
}

predicate HandleRequestVoteRequestHost(h:HostVars, h':HostVars, j:ServerID, m:Message)
    requires j in ServerIDs()
    requires m.RequestVoteRequest?
{
    && m.term <= h.server.currentTerm
    // jonh rewrote for readibility (imperative style)
    && h'.server.votedFor == (if Grant(h, j, m) then Some(j) else h.server.votedFor)
    && h'.server.state == h.server.state
    && h'.server.currentTerm == h.server.currentTerm
    && h'.candidate == h.candidate
    && h'.leader == h.leader
    && h'.log == h.log
}

function MakeRequestVoteResponse(h:HostVars, i:ServerID, j:ServerID, m:Message) : Message
    requires i in ServerIDs()
    requires j in ServerIDs()
    requires m.RequestVoteRequest?
{
    RequestVoteResponse(
        h.server.currentTerm,
        Grant(h, j, m),
        h.log.log,
        i,
        j)
}

predicate HandleRequestVoteRequest(v:Variables, v':Variables, m:Message)
    requires WFVars(v) && WFVars(v')
    requires WFMessage(m)
{
    var i := m.dest;
    var j := m.source;
    && m.RequestVoteRequest?
    && HandleRequestVoteRequestHost(v.host[i], v'.host[i], j, m)
    && UnchangedOtherHosts(v', v, i)
    && Reply(v.global.messages, v'.global.messages,
        MakeRequestVoteResponse(v.host[i], i, j, m), m)
    // NB TLA source didn't constrain elections
    && v'.global.elections == v.global.elections
}

// Server i receives a RequestVote response from server j with
// m.mterm = currentTerm[i].
predicate HandleRequestVoteResponseHost(h:HostVars, h':HostVars, j:ServerID, m:Message)
    requires m.RequestVoteResponse?
    requires j in ServerIDs()
{
    // This tallies votes even when the current state is not Candidate, but
    // they won't be looked at, so it doesn't matter.
    && m.term == h.server.currentTerm
    && h'.candidate.votesResponded == h.candidate.votesResponded + {j}
    // jonh rewrote TLA source into imperative style.
    && h'.candidate.votesGranted ==
        h.candidate.votesGranted + (if m.voteGranted then {j} else {})
    && h'.candidate.voterLog == if m.voteGranted
        then h.candidate.voterLog[j := m.logGhost]
        else h.candidate.voterLog
}

predicate HandleRequestVoteResponse(v:Variables, v':Variables, m:Message)
    requires WFVars(v) && WFVars(v')
    requires WFMessage(m)
    requires m.RequestVoteResponse?
{
    var i := m.dest;
    var j := m.source;
    && HandleRequestVoteResponseHost(v.host[i], v'.host[i], j, m)
    && UnchangedOtherHosts(v', v, i)
    && Discard(v.global.messages, v'.global.messages, m)
    // NB TLA source didn't constrain elections
    && v'.global.elections == v.global.elections + {MakeElectionRecord(v.host[i], i)}
}

predicate AppendLogOk(h:HostVars, m:Message)
    requires m.AppendEntriesRequest?
{
    || m.prevLogIndex == -1
    || (
        && m.prevLogIndex >= 0
        && m.prevLogIndex < |h.log.log|
        && m.prevLogTerm == h.log.log[m.prevLogIndex].term
       )
}

predicate AlreadyDoneWithRequest(h:HostVars, h':HostVars, m:Message, index:int, reply:Option<Message>)
    requires WFMessage(m) && m.AppendEntriesRequest?
{
    var i := m.dest;
    var j := m.source;
    // already done with request
    && (
        || m.entries == []
        || (
            && 0 <= index   // jonh added check that's probably inductive in TLA spec
            && index < |h.log.log|
            && h.log.log[index].term == m.entries[0].term
           )
       )
      // This could make our commitIndex decrease (for
      // example if we process an old, duplicated request),
      // but that doesn't really affect anything.
      // [jonh: doesn't it? Couldn't you re-execute a re-commited entry!?] 
    && h'.log.commitIndex == m.commitIndex
    && reply == Some(AppendEntriesResponse(
            h.server.currentTerm, true, m.prevLogIndex + |m.entries|, i, j))
    && h'.server == h.server
    && h'.log.log == h.log.log
    // NB TLA source spec erroneously sets commitIndex & unchanged logVars,
    // leading to a case that can't ever occur. (Spec wasn't live.)
}

predicate Conflict(h:HostVars, h':HostVars, m:Message, index:int, reply:Option<Message>)
    requires WFMessage(m) && m.AppendEntriesRequest?
{
    && m.entries != []
    && 0 <= index   // jonh adds check; probably inductive in TLA spec
    && index < |h.log.log|
    && h.log.log[index].term != m.entries[0].term
    && h'.log.log == h.log.log[..|h.log.log| - 1]
    && h'.server == h.server
    && h'.log.commitIndex == h.log.commitIndex
    && reply == None
}

predicate NoConflict(h:HostVars, h':HostVars, m:Message, index:int, reply:Option<Message>)
    requires WFMessage(m) && m.AppendEntriesRequest?
{
    // no conflict: append [jonh: exactly one] entry
    // jonh: ...yet we don't send a reply. How does leader discover that it shouldn't
    // re-send the same prefix over and over? It seems this isn't live!
    && m.entries != []
    && |h.log.log| == m.prevLogIndex
    && h'.log.log == h.log.log + m.entries[..1]
    && h'.server == h.server
    && h'.log.commitIndex == h.log.commitIndex
    && reply == None
}

predicate HandleAppendEntriesRequestHost(h:HostVars, h':HostVars, m:Message, reply:Option<Message>)
    requires WFMessage(m) && m.AppendEntriesRequest?
{
    var i := m.dest;
    var j := m.source;
    && m.term <= h.server.currentTerm
    && (
        || ( // reject request
            && (
                || m.term < h.server.currentTerm
                || (
                    && m.term == h.server.currentTerm
                    && h.server.state.Follower?
                    && !AppendLogOk(h, m)
                   )
               )
            && reply == Some(AppendEntriesResponse(h.server.currentTerm, false, 0, i, j))
            && h'.server == h.server
            && h'.candidate == h.candidate
            && h'.log == h.log
           )
        || ( // return to follower state
            && m.term == h.server.currentTerm
            && h.server.state.Candidate?
            && h'.server.state.Follower?
            && h'.server.currentTerm == h.server.currentTerm
            && h'.server.votedFor == h.server.votedFor
            && h'.log == h.log
            && reply == None
           )
        || ( // accept request
            && m.term == h.server.currentTerm
            && h.server.state.Follower?
            && AppendLogOk(h, m)
            && var index := m.prevLogIndex + 1;
            && (
                || AlreadyDoneWithRequest(h, h', m, index, reply)
                || Conflict(h, h', m, index, reply)
                || NoConflict(h, h', m, index, reply)
               )
           )
       )
    && h'.candidate == h.candidate
    && h'.leader == h.leader
}

predicate HandleAppendEntriesRequest(v:Variables, v':Variables, m:Message, reply:Option<Message>)
    requires WFVars(v) && WFVars(v')
    requires WFMessage(m) && m.AppendEntriesRequest?
{
    var i := m.dest;
    var j := m.source;
    && HandleAppendEntriesRequestHost(v.host[i], v'.host[i], m, reply)
    && (reply.Some? ==> Reply(v.global.messages, v'.global.messages, reply.value, m))
    && (reply.None? ==> Discard(v.global.messages, v'.global.messages, m))
    // NB TLA source didn't constrain elections
    && v'.global.elections == v.global.elections
}

// Server i receives an AppendEntries response from server j with
// m.mterm = currentTerm[i].
predicate HandleAppendEntriesResponseHost(h:HostVars, h':HostVars, m:Message)
    requires WFLeaderVars(h.leader)
    requires WFMessage(m) && m.AppendEntriesResponse?
{
    var i := m.dest;
    var j := m.source;
    && m.term == h.server.currentTerm
    && (
        || (
            && m.success
            && h'.leader.nextIndex == h.leader.nextIndex[j := m.matchIndex + 1]
            && h'.leader.matchIndex == h.leader.matchIndex[j := m.matchIndex]
           )
        || (
            && !m.success
            && h'.leader.nextIndex ==
                h.leader.nextIndex[j := Max(h.leader.nextIndex[j] -1, 0)]
            && h'.leader.matchIndex == h.leader.matchIndex
           )
       )
    && h'.server == h.server
    && h'.candidate == h.candidate
    && h'.log == h.log
}

predicate HandleAppendEntriesResponse(v:Variables, v':Variables, m:Message)
    requires WFVars(v) && WFVars(v')
    requires m.AppendEntriesResponse?
    requires WFMessage(m)
{
    var i := m.dest;
    && HandleAppendEntriesResponseHost(v.host[i], v'.host[i], m)
    && Discard(v.global.messages, v'.global.messages, m)
    && v'.global.elections == v.global.elections
}

predicate UpdateTermHost(h:HostVars, h':HostVars, m:Message)
{
    && m.term > h.server.currentTerm
    && h'.server.currentTerm == m.term
    && h'.server.state.Follower?
    && h'.server.votedFor == None
    && h'.candidate == h.candidate
    && h'.leader == h.leader
    && h'.log == h.log
}

// Any RPC with a newer term causes the recipient to advance its term first.
predicate UpdateTerm(v:Variables, v':Variables, m:Message)
    requires WFVars(v) && WFVars(v')
    requires WFMessage(m)
{
    var i := m.dest;
    && UpdateTermHost(v.host[i], v'.host[i], m)
    && UnchangedOtherHosts(v', v, i)
    && v'.global == v.global
}

// Responses with stale terms are ignored.
predicate DropStaleResponse(v:Variables, v':Variables, m:Message)
    requires WFVars(v) && WFVars(v')
    requires WFMessage(m)
{
    var h := v.host[m.dest];
    && m.term < h.server.currentTerm
    && UnchangedAllHosts(v', v)
    && Discard(v.global.messages, v'.global.messages, m)
    // NB TLA source didn't constrain elections
    && v'.global.elections == v.global.elections
}

// NB source TLA writes:
    // Any RPC with a newer term causes the recipient to advance
    // its term first. Responses with stale terms are ignored.
// ... in a nondeterministic disjunct. What happens if the recipient decides to
// try one of the other actions first? Spurious rejections?

predicate Receive(v:Variables, v':Variables, m:Message, reply:Option<Message>)
    requires WFVars(v) && WFVars(v')
{
    && WFMessage(m)
    && (
        || UpdateTerm(v, v', m)
        || (
            && m.RequestVoteRequest?
            && HandleRequestVoteRequest(v, v', m)
           )
        || (
            && m.RequestVoteResponse?
            && (
                || DropStaleResponse(v, v', m)
                || HandleRequestVoteResponse(v, v', m)
               )
           )
        || (
            && m.AppendEntriesRequest?
            && HandleAppendEntriesRequest(v, v', m, reply)
           )
        || (
            && m.AppendEntriesResponse?
            && (
                || DropStaleResponse(v, v', m)
                || HandleAppendEntriesResponse(v, v', m)
               )
           )
       )
}

// End of message handlers.

//////////////////////////////////////////////////////////////////////////////
// Network state transitions

// The network duplicates a message
predicate DuplicateMessage(v:Variables, v':Variables, m:Message)
    requires WFVars(v) && WFVars(v')
{
    && UnchangedAllHosts(v', v)
    // NB source TLA spec doesn't constrain elections
    && v'.global.elections == v.global.elections
    // NB alarmingly, TLA spec allows duplication of *any* message, not just
    // messages already in network!
    && m in v.global.messages
    && Send(v.global.messages, v'.global.messages, m)
}

// The network drops a message
predicate DropMessage(v:Variables, v':Variables, m:Message)
    requires WFVars(v) && WFVars(v')
{
    && UnchangedAllHosts(v', v)
    // NB source TLA spec doesn't constrain elections
    && v'.global.elections == v.global.elections
    && Discard(v.global.messages, v'.global.messages, m)
}

//////////////////////////////////////////////////////////////////////////////
// Defines how the variables may transition.

datatype Step =
      RestartStep(i:ServerID)
    | TimeoutStep(i:ServerID)
    | RequestVoteStep(i:ServerID, j:ServerID)
    | BecomeLeaderStep(i:ServerID)
    | ClientRequestStep(i:ServerID, v:Value)
    | AdvanceCommitIndexStep(i:ServerID)
    | AppendEntriesStep(i:ServerID, j:ServerID)
    | ReceiveStep(m:Message, reply:Option<Message>)
    | DuplicateMessageStep(m:Message)
    | DropMessageStep(m:Message)

predicate NextStep(v:Variables, v':Variables, step:Step)
    requires WFVars(v) && WFVars(v')
{
    match step {
        case RestartStep(i) => Restart(v, v', i)
        case TimeoutStep(i) => Timeout(v, v', i)
        case RequestVoteStep(i, j) => RequestVote(v, v', i, j)
        case BecomeLeaderStep(i) => BecomeLeader(v, v', i)
        case ClientRequestStep(i, value) => ClientRequest(v, v', i, value)
        case AdvanceCommitIndexStep(i) => AdvanceCommitIndex(v, v', i)
        case AppendEntriesStep(i, j) => AppendEntries(v, v', i, j)
        case ReceiveStep(m, reply) => Receive(v, v', m, reply)
        case DuplicateMessageStep(m) => DuplicateMessage(v, v', m)
        case DropMessageStep(m) => DropMessage(v, v', m)
    }
}

function {:opaque} EveryLogNow(v:Variables) : (el:set<Log>)
    requires WFVars(v)
    ensures forall s :: s in ServerIDs() ==> v.host[s].log.log in el
{
    set s | s in ServerIDs() :: v.host[s].log.log
}

predicate {:opaque} Next(v:Variables, v':Variables)
    requires WFVars(v) && WFVars(v')
{
    && (exists step :: NextStep(v, v', step))

    // History variable that tracks every log ever:
    && v'.global.allLogs == v.global.allLogs + EveryLogNow(v)
}

// The specification must start with the initial state and transition according
// to Next.
// Spec == Init /\ [][Next]_vars

} // module

module raftInvariants {
import opened MissingLibrary
import opened raft

predicate ElectionSafety(v:Variables)
{
    forall e1, e2 ::
        (&& e1 in v.global.elections
        && e2 in v.global.elections
        && e1.term == e2.term) ==>
        e1.leader == e2.leader
}

lemma ElectionSafetyInit(v:Variables)
    requires Init(v)
    ensures ElectionSafety(v)
{
}

function getStep(v:Variables, v':Variables) : (step:Step)
    requires WFVars(v) && WFVars(v')
    requires Next(v, v')
    ensures NextStep(v, v', step)
{
    reveal_Next();
    var step :| NextStep(v, v', step);
    step
}

lemma ElectionSafetyInduction(v:Variables, v':Variables)
    requires ElectionSafety(v)
    requires WFVars(v) && WFVars(v')
    requires Next(v, v')
    ensures ElectionSafety(v')
{
    var step := getStep(v, v');
    if step.BecomeLeaderStep? {
        assume false;
        assert ElectionSafety(v');
    } else {
        assert v'.global.elections == v.global.elections;
        assert ElectionSafety(v');
    }
}

}
