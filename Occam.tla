------------------------------- MODULE Occam --------------------------------
(***************************************************************************)
(* This is the TLA+ specification for Occam, a replicated atomic commit    *)
(* protocol based on 2PC&Paxos and enhanced by the Reduction Theory.       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANT
    DS,             \* The set of data servers
    Shards,         \* The set of shards
    Leaders,        \* The set of leaders
    numShards,      \* The number of shards
    Coordinator     \* The ID of the coordinator

(***************************************************************************)
(* We assume the following properties of the declared constants.           *)
(***************************************************************************)
ASSUME
    /\ Coordinator \in DS
    /\ Coordinator \in {Leaders[l] : l \in 1..numShards}    \* Only leaders can act as the coordinator
    /\ numShards = Len(Shards)
    /\ numShards = Len(Leaders)
    /\ DS = UNION {Shards[i] : i \in 1..numShards}          \* Union of all shards is the full set
    /\ \A s \in 1..numShards : Leaders[s] \in Shards[s]     \* Leaders are in corresponding shards

Messages ==
    (***********************************************************************)
    (* The set of all possible messages                                    *)
    (* To reduce the state space, messages are not stored in variables     *)
    (* of each node, instead each node checks the message buffer directly  *)
    (***********************************************************************)
    [type : {"phase2a"}, src : DS, desc : {"leaderPrepared", "leaderAborted", "committed", "aborted"}] \cup
    [type : {"phase2b"}, src : DS, dst : DS, desc : {"leaderDecision", "coordDecision"}] \cup
    [type : {"prepareAccepted"}, src : 1..numShards] \cup
    [type : {"prepared", "aborted", "ack"}, src : 1..numShards] \cup
    [type : {"commit", "abort"}]

-----------------------------------------------------------------------------
VARIABLES
    dsState,                    \* dsState[ds] is the state of data server ds
    coordState,                 \* The state of the coordinator
    coordPrepared,              \* The set of shards that are prepared
    coordDecisionReplicated,    \* The set of replicas to which the coordinator has replicated its decision
    msgs                        \* The message pool
    
vars == <<dsState, coordState, coordPrepared, coordDecisionReplicated, msgs>>

TypeOK ==
    /\ dsState \in [DS -> [Shard : 1..numShards,
                           Role : {"Coordinator", "Leader", "Follower"},
                           LeaderDecisionReplicated : SUBSET DS,
                           CoordDecisionReplicated : SUBSET DS,
                           State : {"working", "prepared", "committed", "aborted"}]]
    /\ coordState \in {"init", "commit", "abort"}
    /\ coordPrepared \subseteq {i : i \in 1..numShards}
    /\ coordDecisionReplicated \subseteq DS
    /\ msgs \subseteq Messages

Init ==
    /\ dsState = [ds \in DS |-> [Shard |-> CHOOSE s \in 1..numShards : ds \in Shards[s],
                  Role |-> CASE ds = Coordinator                       -> "Coordinator"
                           [] ds \in {Leaders[l] : l \in 1..numShards} -> "Leader"
                           [] OTHER                                    -> "Follower",
                  LeaderDecisionReplicated |-> {},
                  CoordDecisionReplicated |-> {},
                  State |-> "working"]]
    /\ coordState              = "init"
    /\ coordPrepared           = {}
    /\ coordDecisionReplicated = {}
    /\ msgs                    = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                THE ACTIONS                              *)
(***************************************************************************)
send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            COORDINATOR ACTIONS                          *)
(***************************************************************************)
CoordRcvLeaderPrepare(s) ==
    /\ coordState = "init"
    /\ [type |-> "prepared", src |-> s] \in msgs
    /\ coordPrepared' = coordPrepared \cup {s}
    /\ UNCHANGED <<dsState, coordState, coordDecisionReplicated, msgs>>

CoordRcvLeaderAbort(s) ==
    /\ coordState = "init"
    /\ [type |-> "aborted", src |-> s] \in msgs
    /\ coordState' = "abort"
    /\ dsState' = [dsState EXCEPT ![Coordinator].State = "aborted"]
    /\ send([type |-> "abort"])
    /\ UNCHANGED <<coordPrepared, coordDecisionReplicated>>

CoordCommit ==
    /\ coordState = "init"
    /\ \/ coordPrepared = {i : i \in 1..numShards} \ {dsState[Coordinator].Shard}
          \* All shards excluding the one coordinator resides in are prepared
       \/ \A s \in {i : i \in 1..numShards} \ {dsState[Coordinator].Shard} :
            [type |-> "prepareAccepted", src |-> s] \in msgs
          \* prepareAccepted message from shard s indicates that the leader and at least
          \* one follower of s has prepared. In 3-way replicated case, this indeed means
          \* that the prepare decision of the shard is fault-tolerant now.
          \* If all shards excluding the one coordinator resides are prepared, coordinator
          \* can proceed to commit the transaction.
    /\ coordState' = "commit"
    /\ dsState' = [dsState EXCEPT ![Coordinator].State = "committed"]
    /\ send([type |-> "commit"])
    /\ UNCHANGED <<coordPrepared, coordDecisionReplicated>>

CoordSendPhase2a ==
    /\ \/ coordState = "commit"
       \/ coordState = "abort"
    /\ send([type |-> "phase2a", src |-> Coordinator,
             desc |-> IF coordState = "commit" THEN "committed" ELSE "aborted"])
    /\ coordDecisionReplicated' = coordDecisionReplicated \cup {Coordinator}
    /\ UNCHANGED <<dsState, coordState, coordPrepared>>

CoordRcvPhase2b(ds) ==
    /\ ds \in Shards[dsState[Coordinator].Shard]   \* ds is in the same shard as the coordinator
    /\ [type |-> "phase2b", src |-> ds, dst |-> Coordinator, desc |-> "coordDecision"] \in msgs
    /\ coordDecisionReplicated' = coordDecisionReplicated \cup {ds}
    /\ UNCHANGED <<dsState, coordState, coordPrepared, msgs>>

CoordBroadcastDecision ==
    /\ \/ coordState = "commit"
       \/ coordState = "abort"
    /\ Cardinality(coordDecisionReplicated) \geq Cardinality(Shards[dsState[Coordinator].Shard]) \div 2 + 1
    /\ send([type |-> IF coordState = "commit" THEN "commit" ELSE "abort"])
    /\ UNCHANGED <<dsState, coordState, coordPrepared, coordDecisionReplicated>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                              LEADER ACTIONS                             *)
(***************************************************************************)
LeaderPrepare(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ dsState[ds].State = "working"
    /\ dsState' = [dsState EXCEPT ![ds].State = "prepared"]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderAbort(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ dsState[ds].State = "working"
    /\ dsState' = [dsState EXCEPT ![ds].State = "aborted"]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderSendPhase2aLeaderDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ dsState[ds].State = "prepared"
       \/ dsState[ds].State = "aborted"
    /\ send([type |-> "phase2a", src |-> ds,
             desc |-> IF dsState[ds].State = "prepared" THEN "leaderPrepared" ELSE "leaderAborted"])
    /\ dsState' = [dsState EXCEPT 
                   ![ds].LeaderDecisionReplicated = dsState[ds].LeaderDecisionReplicated \cup {ds}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

LeaderRcvPhase2bLeaderDecision(src, dst) ==
    /\ dsState[dst].Role = "Leader"
    /\ dsState[src].Shard = dsState[dst].Shard      \* Source and destination reside in the same shard
    /\ [type |-> "phase2b", src |-> src, dst |-> dst, desc |-> "leaderDecision"] \in msgs
    /\ dsState' = [dsState EXCEPT
                   ![dst].LeaderDecisionReplicated = dsState[dst].LeaderDecisionReplicated \cup {src}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderSendDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ dsState[ds].State = "prepared"
       \/ dsState[ds].State = "aborted"
    /\ Cardinality(dsState[ds].LeaderDecisionReplicated) \geq Cardinality(Shards[dsState[ds].Shard]) \div 2 + 1
    /\ send([type |-> IF dsState[ds].State = "prepared" THEN "prepared" ELSE "aborted",
             src |-> dsState[ds].Shard])
    /\ UNCHANGED <<dsState, coordState, coordPrepared, coordDecisionReplicated>>

LeaderSendPhase2aCoordDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ [type |-> "commit"] \in msgs
       \/ [type |-> "abort"] \in msgs   \* Decision from the coordinator
       \/ \A s \in {i : i \in 1..numShards} \ {dsState[Coordinator].Shard} :
            [type |-> "prepareAccepted", src |-> s] \in msgs
          \* prepareAccepted message from shard s indicates that the leader and at least
          \* one follower of s has prepared. In 3-way replicated case, this indeed means
          \* that the prepare decision of the shard is fault-tolerant now.
          \* If all shards excluding the one coordinator resides are prepared, coordinator
          \* can proceed to commit the transaction.
    /\ send([type |-> "phase2a",
             src |-> ds, desc |-> IF [type |-> "abort"] \in msgs THEN "aborted" ELSE "committed"])
    /\ dsState' = [dsState EXCEPT 
                   ![ds].State = IF [type |-> "abort"] \in msgs THEN "aborted" ELSE "committed",
                   ![ds].CoordDecisionReplicated = dsState[ds].CoordDecisionReplicated \cup {ds}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

LeaderRcvPhase2bCoordDecision(src, dst) ==
    /\ dsState[dst].Role = "Leader"
    /\ dsState[src].Shard = dsState[dst].Shard      \* Source and destination reside in the same shard
    /\ [type |-> "phase2b", src |-> src, dst |-> dst, desc |-> "coordDecision"] \in msgs
    /\ dsState' = [dsState EXCEPT
                   ![dst].CoordDecisionReplicated = dsState[dst].CoordDecisionReplicated \cup {src}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderAck(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ Cardinality(dsState[ds].CoordDecisionReplicated) \geq Cardinality(Shards[dsState[ds].Shard]) \div 2 + 1
    /\ send([type |-> "ack", src |-> dsState[ds].Shard])
    /\ UNCHANGED <<dsState, coordState, coordPrepared, coordDecisionReplicated>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                             FOLLOWER ACTIONS                            *)
(***************************************************************************)
FollowerSendPhase2bLeaderDecision(ds) ==
    /\ dsState[ds].Role = "Follower"
    /\ dsState[ds].State = "working"
    /\ \/ [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderPrepared"] \in msgs
       \/ [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderAborted"] \in msgs
    /\ dsState' = [dsState EXCEPT ![ds].State = 
                   IF [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderPrepared"] \in msgs
                   THEN "prepared" ELSE "aborted"]
    /\ msgs' = IF [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderAborted"] \in msgs
               THEN msgs \cup
                    {[type |-> "phase2b", src |-> ds, dst |-> Leaders[dsState[ds].Shard], desc |-> "leaderDecision"]}
               ELSE msgs \cup
                    {[type |-> "prepareAccepted", src |-> dsState[ds].Shard],  \* Occam's shortcut messages
                     [type |-> "phase2b", src |-> ds, dst |-> Leaders[dsState[ds].Shard], desc |-> "leaderDecision"]}
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

FollowerSendPhase2bCoordDecision(ds) ==
    /\ dsState[ds].Role = "Follower"
    /\ \/ dsState[ds].State = "working"
       \/ dsState[ds].State = "prepared"
    /\ \/ [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "committed"] \in msgs
       \/ [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "aborted"] \in msgs
    /\ dsState' = [dsState EXCEPT ![ds].State =
                   IF [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "committed"] \in msgs
                   THEN "committed" ELSE "aborted"]
    /\ send([type |-> "phase2b", src |-> ds, dst |-> Leaders[dsState[ds].Shard], desc |-> "coordDecision"])
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            NEXT STATE ACTION                            *)
(***************************************************************************)
Next ==
    \/ CoordCommit
    \/ CoordSendPhase2a
    \/ CoordBroadcastDecision
    \/ \E ds \in DS : \/ CoordRcvPhase2b(ds)
                      \/ LeaderPrepare(ds)
                      \/ LeaderAbort(ds)
                      \/ LeaderSendPhase2aLeaderDecision(ds)
                      \/ LeaderSendDecision(ds)
                      \/ LeaderSendPhase2aCoordDecision(ds)
                      \/ LeaderAck(ds)
                      \/ FollowerSendPhase2bLeaderDecision(ds)
                      \/ FollowerSendPhase2bCoordDecision(ds)
    \/ \E src, dst \in DS : \/ LeaderRcvPhase2bLeaderDecision(src, dst)
                            \/ LeaderRcvPhase2bCoordDecision(src, dst)
    \/ \E s \in {i : i \in 1..numShards} : \/ CoordRcvLeaderPrepare(s)
                                           \/ CoordRcvLeaderAbort(s)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                               CONSTRAINTS                               *)
(***************************************************************************)
AllCommit == \A ds \in DS : dsState[ds].State = "committed"

AllAbort == \A ds \in DS : dsState[ds].State = "aborted"
    
Liveness == <>(AllCommit \/ AllAbort)

Safety ==
    \A ds1, ds2 \in DS : ~ /\ dsState[ds1].State = "aborted"
                           /\ dsState[ds2].State = "committed"

Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec
            /\ WF_vars(CoordCommit)
            /\ WF_vars(CoordSendPhase2a)
            /\ WF_vars(CoordBroadcastDecision)
            /\ \A ds \in DS : /\ WF_vars(CoordRcvPhase2b(ds))
                              /\ WF_vars(LeaderPrepare(ds))
                              /\ WF_vars(LeaderSendPhase2aLeaderDecision(ds))
                              /\ WF_vars(LeaderSendDecision(ds))
                              /\ WF_vars(LeaderSendPhase2aCoordDecision(ds))
                              /\ WF_vars(LeaderAck(ds))
                              /\ WF_vars(FollowerSendPhase2bLeaderDecision(ds))
                              /\ WF_vars(FollowerSendPhase2bCoordDecision(ds))
            /\ \A src, dst \in DS : /\ WF_vars(LeaderRcvPhase2bLeaderDecision(src, dst))
                                    /\ WF_vars(LeaderRcvPhase2bCoordDecision(src, dst))
            /\ \A s \in {i : i \in 1..numShards} : /\ WF_vars(CoordRcvLeaderPrepare(s))
                                                   /\ WF_vars(CoordRcvLeaderAbort(s))
