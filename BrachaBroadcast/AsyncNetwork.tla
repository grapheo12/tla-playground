---- MODULE AsyncNetwork ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NULL, NumNodes, NetworkTimesteps
CONSTANTS src, dest, body, sendonce, type



(* --algorithm NetworkAdversary
variables
    nodes = 1..NumNodes;
    global_queue = << >>;
    local_queues = [n \in nodes |-> << >>];

define
MsgType(msg) ==
    DOMAIN msg = {src, dest, body, type, sendonce}

AsyncNetworkProperty ==
    <>(
        Len(global_queue) > 0 => (\A msg \in global_queue: msg.sendonce)
    )

EnqueueForSend(m) ==
    MsgType(m) => global_queue' = global_queue + << m >>

end define;
process network_adversary = "network_adversary"
variables
    next_msg = NULL;
    next_msg_idx = -1;
    i = 0;
begin
    SendMessage:
        while i < NetworkTimesteps do
            either
                await Len(global_queue) > 0;
                next_msg_idx := CHOOSE msg \in DOMAIN global_queue: TRUE;
                global_queue[next_msg_idx].sendonce := TRUE;
                next_msg := global_queue[next_msg_idx];
                local_queues[next_msg.dest] := local_queues[next_msg.dest] + << next_msg >>;
            or
                skip;
            end either;
            i := i + 1;
        end while; 
    

end process;



end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "db65b87f" /\ chksum(tla) = "e494f093")
VARIABLES nodes, global_queue, local_queues, pc

(* define statement *)
MsgType(msg) ==
    DOMAIN msg = {src, dest, body, type, sendonce}

AsyncNetworkProperty ==
    <>(
        Len(global_queue) > 0 => (\A msg \in global_queue: msg.sendonce)
    )

EnqueueForSend(m) ==
    MsgType(m) => global_queue' = global_queue + << m >>

VARIABLES next_msg, next_msg_idx, i

vars == << nodes, global_queue, local_queues, pc, next_msg, next_msg_idx, i
        >>

ProcSet == {"network_adversary"}

Init == (* Global variables *)
        /\ nodes = 1..NumNodes
        /\ global_queue = << >>
        /\ local_queues = [n \in nodes |-> << >>]
        (* Process network_adversary *)
        /\ next_msg = NULL
        /\ next_msg_idx = -1
        /\ i = 0
        /\ pc = [self \in ProcSet |-> "SendMessage"]

SendMessage == /\ pc["network_adversary"] = "SendMessage"
               /\ IF i < NetworkTimesteps
                     THEN /\ \/ /\ Len(global_queue) > 0
                                /\ next_msg_idx' = (CHOOSE msg \in DOMAIN global_queue: TRUE)
                                /\ global_queue' = [global_queue EXCEPT ![next_msg_idx'].sendonce = TRUE]
                                /\ next_msg' = global_queue'[next_msg_idx']
                                /\ local_queues' = [local_queues EXCEPT ![next_msg'.dest] = local_queues[next_msg'.dest] + << next_msg' >>]
                             \/ /\ TRUE
                                /\ UNCHANGED <<global_queue, local_queues, next_msg, next_msg_idx>>
                          /\ i' = i + 1
                          /\ pc' = [pc EXCEPT !["network_adversary"] = "SendMessage"]
                     ELSE /\ pc' = [pc EXCEPT !["network_adversary"] = "Done"]
                          /\ UNCHANGED << global_queue, local_queues, next_msg, 
                                          next_msg_idx, i >>
               /\ nodes' = nodes

network_adversary == SendMessage

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == network_adversary
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
