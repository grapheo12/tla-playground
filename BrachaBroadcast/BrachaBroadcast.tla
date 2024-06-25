---- MODULE BrachaBroadcast ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS NULL, src, dest, type, body, sent_once
CONSTANTS Proposal, Echo, Vote
CONSTANTS HonestProposal, ByzProposal1, ByzProposal2

CONSTANTS NumNodes, NetTimeSteps


Nodes == 1..NumNodes
ProcSet == 0..NumNodes  \* 0 is network adversary

VARIABLE local_queues, global_queue, next_msg, next_msg_idx, time_steps, send_to
net_vars == << next_msg, next_msg_idx, time_steps >>
shared_vars == << local_queues, global_queue, send_to >>

protocol_vars == << >>
VARIABLE pc

vars == << pc >> + protocol_vars + shared_vars + net_vars

NetworkDeliverMessage(self) ==
    /\ pc[self] = "NetworkDeliverMessage"
    /\ Len(global_queue) > 0
    /\ next_msg_idx' = (CHOOSE _msg \in global_queue: TRUE)
    /\ global_queue' = [global_queue EXCEPT ![next_msg_idx'].sent_once = TRUE]
    /\ next_msg' = global_queue'[next_msg_idx']
    /\ local_queues' = [local_queues EXCEPT ![next_msg'.dest] = @ + << next_msg' >>]
    /\ time_steps' = time_steps + 1
    /\ IF time_steps' >= NetTimeSteps THEN pc[self] = "Done" ELSE UNCHANGED pc
    /\ UNCHANGED protocol_vars

EnqueueForSend(msg) ==
    /\ global_queue' = global_queue + << msg >>


BroadcastLoop(self, pcName, jmp, bod, typ) ==
    /\ pc[self] = pcName
    /\ IF send_to[self] > NumNodes
        THEN /\ send_to' = [send_to EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = jmp]
             /\ UNCHANGED global_queue
        ELSE /\ EnqueueForSend([src |-> self, dest |-> send_to[self], body |-> bod, type |-> typ, sent_once |-> FALSE])
             /\ send_to' = [send_to EXCEPT ![self] = @ + 1]
             /\ UNCHANGED pc
    /\ UNCHANGED net_vars
    /\ UNCHANGED local_queues
    /\ UNCHANGED protocol_vars


SendProposal(self) ==
    /\ pc[self] = "SendProposal"
    /\ BroadcastLoop(self, "BCL_SendProposal", "WaitMessage", HonestProposal, Proposal)


WaitMessage(self) ==
    /\ pc[self] = "WaitMessage"
    /\ Len(local_queues[self]) > 0
    /\ LET _msg == Head(local_queues[self])
       IN /\ IF _msg.type = Proposal
              THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
              ELSE /\ UNCHANGED pc
    /\ local_queues' = [local_queues EXCEPT ![self] = Tail(@)]
    /\ UNCHANGED net_vars
    /\ UNCHANGED << global_queue, send_to >>
    /\ UNCHANGED protocol_vars 


Terminating ==
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED pc
    /\ UNCHANGED net_vars
    /\ UNCHANGED shared_vars
    /\ UNCHANGED protocol_vars

Init ==
    /\ pc = [n \in ProcSet |-> CASE n = 0 -> "NetworkDeliverMessage"
                               [] n = 1 -> "SendProposal" 
                               [] n \in 2..NumNodes -> "WaitMessage"]
    /\ local_queues = [n \in Nodes |-> << >>]
    /\ global_queue = << >>
    /\ send_to = [n \in Nodes |-> 1]
    /\ next_msg = NULL
    /\ next_msg_idx = -1
    /\ time_steps = NetTimeSteps


Next ==
    \/ NetworkDeliverMessage(0)
    \/ SendProposal(1)
    \/ (\E n \in Nodes: WaitMessage(n))
    \/ Terminating

Spec ==
    Init /\ [][Next]_vars
    
    

====