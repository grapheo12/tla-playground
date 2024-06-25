--------------------------- MODULE CircularBuffer ---------------------------
EXTENDS Integers, Sequences

CONSTANTS NULL, EMPTY, BufferSize, NumWrites, NumReads

Buffer == [s \in 1..BufferSize |-> EMPTY]

BufferValType == Int \union {NULL}

threads == {"reader", "writer"}

VARIABLES write_counter, read_counter, last_read, buffer, pc, read_so_far, written_so_far, diff
vars == << write_counter, read_counter, last_read, buffer, pc, read_so_far, written_so_far, diff >>

IncCounter(cnt) ==
    IF cnt = BufferSize THEN
        cnt' = 1
    ELSE
        cnt' = cnt + 1
        
Write(val) ==
    /\ buffer[write_counter] = EMPTY
    /\ buffer' = [buffer EXCEPT ![write_counter] = val]
    /\ diff' = diff + 1
    /\ IncCounter(write_counter)
    /\ UNCHANGED << read_counter, last_read >>
    
Read ==
    /\ diff > 0
    /\ last_read' = buffer[read_counter]
    /\ buffer' = [buffer EXCEPT ![read_counter] = EMPTY]
    /\ diff' = diff - 1
    /\ IncCounter(read_counter)
    /\ UNCHANGED << write_counter >>
    
    
ReadThread(self) ==
    /\ pc[self] = "ReadThread"
    /\ Read
    /\ read_so_far' = read_so_far + 1
    /\ IF read_so_far' < NumReads THEN
          UNCHANGED pc
       ELSE
          pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << written_so_far >>

WriteThread(self) ==
    /\ pc[self] = "WriteThread"
    /\ Write(written_so_far)
    /\ written_so_far' = written_so_far + 1
    /\ IF written_so_far' < NumWrites THEN
          UNCHANGED pc
       ELSE
          pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << read_so_far >>
          

        
Init ==
    /\ last_read = NULL
    /\ read_so_far = 0
    /\ diff = 0
    /\ written_so_far = 0
    /\ write_counter = 1
    /\ read_counter = 1
    /\ buffer = Buffer
    /\ pc = [self \in threads |-> CASE self = "reader" -> "ReadThread"
                               [] self = "writer" -> "WriteThread"]
                               
thread(self) ==
    \/ WriteThread(self)
    \/ ReadThread(self)
    
Terminating ==
    /\ pc["reader"] = "Done"
    /\ UNCHANGED vars


Next ==
    \/ (\E self \in threads: thread(self))
    \/ Terminating
    
    
Spec ==
    Init /\ [][Next]_vars /\ SF_vars(Next)
    
    
Safety ==
    /\ diff >= 0
    /\ last_read \in BufferValType
    
Liveness ==
    <>(
        /\ read_so_far = NumReads
        /\ (NumWrites - NumReads < BufferSize) => written_so_far = NumWrites
      )
    


=============================================================================
