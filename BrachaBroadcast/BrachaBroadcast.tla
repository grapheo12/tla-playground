---- MODULE BrachaBroadcast ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS NULL, NumNodes, HonestProposal
CONSTANTS Proposal, Echo, Vote
nodes == 1..NumNodes


INSTANCE AsyncNetwork

VARIABLES state, leader, sendTo, pc
vars == << state, leader, sendTo, pc >>



Init ==
    /\ state = [n \in nodes |-> [echo |-> TRUE, vote |-> TRUE]]
    /\ sendTo = [n \in nodes |-> 1]
    /\ leader = 1
    /\ pc = [n \in nodes |-> CASE n = leader -> "SendProposal"
                             [] n # leader -> "WaitForMessage"]

                            
NonAtomicBroadcast(self, msg, typ, pcName, jmp) ==
    /\ pc[self] = pcName
    /\ IF sendTo[self] \in nodes THEN
        /\ AsyncNetwork!EnqueueForSend([src |-> to, dest |-> from, body |-> msg, type |-> typ, sendonce |-> FALSE])
        /\ sendTo' = [sendTo EXCEPT ![self] = @ + 1]
        /\ UNCHANGED << state, leader, pc >>
       ELSE
        /\ sendTo' = [sendTo EXCEPT ![self] = 1]
        /\ pc' = [pc EXCEPT ![self] = jmp]
        /\ UNCHANGED  << state, leader >>

SendProposal(self) ==
    /\ self = leader
    /\ pc[self] = "SendProposal"
    /\ sendTo' = [sendTo EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "SendProposal_NonAtomicBroadcast"]

SendProposal_NonAtomicBroadcast(self) ==
    NonAtomicBroadcast(self, HonestProposal, Proposal, "SendProposal_NonAtomicBroadcast", "WaitForMessage")






    
    

====