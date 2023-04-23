------------------------------- MODULE queue -------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize \* initially this queue is unbounded
(*--algorithm message_queue
variables queue = <<>>,
         sem = 1,
         Readers = {"r1", "r2"},
         Writers = {"w1"},
         Res = [w \in Readers |-> ""],
         RFlags = [w \in Readers |-> FALSE];


define
  BoundedQueue == Len(queue) <= MaxQueueSize
end define;

procedure Enqueue(val="") begin
  En:
    await sem = 1 /\ Len(queue) < MaxQueueSize;
    sem := 0;
    
    queue := Append(queue, val);
    
    unlock: sem := 1;
    return;
end procedure;

procedure Dequeue() begin
  Dq:
    await sem = 1 /\ queue /= <<>>;
    sem := 0;
    
    if queue /= <<>> then
        unlock: sem := 1;
        RFlags[self] := FALSE;
        return;
    else
        unlock_succ: sem:= 1; \* if I got right sem and Ops under queue occure simultaniously.
        Res[self] := Head(queue);
        RFlags[self] := TRUE;
        queue := Tail(queue);
        return;
    end if;
end procedure;
    

process writer \in Writers
begin Write:
    while TRUE do
        call Enqueue("msg");
    end while;
end process;

process reader \in Readers
variables curr_msg = "", res = FALSE;
begin Read:
  while TRUE do
    call Dequeue();
    lab:
        curr_msg := Res[self];
        res := RFlags[self];
        if res = TRUE then
            assert(curr_msg = "msg")
        else
            assert(curr_msg = "")
        end if;
  end while;
end process;
end algorithm;*)


\* BEGIN TRANSLATION (chksum(pcal) = "65d38652" /\ chksum(tla) = "a573e686")
\* Label unlock of procedure Enqueue at line 25 col 13 changed to unlock_
VARIABLES queue, sem, Readers, Writers, Res, RFlags, pc, stack

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLES val, curr_msg, res

vars == << queue, sem, Readers, Writers, Res, RFlags, pc, stack, val, 
           curr_msg, res >>

ProcSet == (Writers) \cup (Readers)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ sem = 1
        /\ Readers = {"r1", "r2"}
        /\ Writers = {"w1"}
        /\ Res = [w \in Readers |-> ""]
        /\ RFlags = [w \in Readers |-> FALSE]
        (* Procedure Enqueue *)
        /\ val = [ self \in ProcSet |-> ""]
        (* Process reader *)
        /\ curr_msg = [self \in Readers |-> ""]
        /\ res = [self \in Readers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "Write"
                                        [] self \in Readers -> "Read"]

En(self) == /\ pc[self] = "En"
            /\ sem = 1 /\ Len(queue) < MaxQueueSize
            /\ sem' = 0
            /\ queue' = Append(queue, val[self])
            /\ pc' = [pc EXCEPT ![self] = "unlock_"]
            /\ UNCHANGED << Readers, Writers, Res, RFlags, stack, val, 
                            curr_msg, res >>

unlock_(self) == /\ pc[self] = "unlock_"
                 /\ sem' = 1
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << queue, Readers, Writers, Res, RFlags, 
                                 curr_msg, res >>

Enqueue(self) == En(self) \/ unlock_(self)

Dq(self) == /\ pc[self] = "Dq"
            /\ sem = 1 /\ queue /= <<>>
            /\ sem' = 0
            /\ IF queue /= <<>>
                  THEN /\ pc' = [pc EXCEPT ![self] = "unlock"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "unlock_succ"]
            /\ UNCHANGED << queue, Readers, Writers, Res, RFlags, stack, val, 
                            curr_msg, res >>

unlock(self) == /\ pc[self] = "unlock"
                /\ sem' = 1
                /\ RFlags' = [RFlags EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << queue, Readers, Writers, Res, val, curr_msg, 
                                res >>

unlock_succ(self) == /\ pc[self] = "unlock_succ"
                     /\ sem' = 1
                     /\ Res' = [Res EXCEPT ![self] = Head(queue)]
                     /\ RFlags' = [RFlags EXCEPT ![self] = TRUE]
                     /\ queue' = Tail(queue)
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << Readers, Writers, val, curr_msg, res >>

Dequeue(self) == Dq(self) \/ unlock(self) \/ unlock_succ(self)

Write(self) == /\ pc[self] = "Write"
               /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                           pc        |->  "Write",
                                                           val       |->  val[self] ] >>
                                                       \o stack[self]]
                  /\ val' = [val EXCEPT ![self] = "msg"]
               /\ pc' = [pc EXCEPT ![self] = "En"]
               /\ UNCHANGED << queue, sem, Readers, Writers, Res, RFlags, 
                               curr_msg, res >>

writer(self) == Write(self)

Read(self) == /\ pc[self] = "Read"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Dequeue",
                                                       pc        |->  "lab" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "Dq"]
              /\ UNCHANGED << queue, sem, Readers, Writers, Res, RFlags, val, 
                              curr_msg, res >>

lab(self) == /\ pc[self] = "lab"
             /\ curr_msg' = [curr_msg EXCEPT ![self] = Res[self]]
             /\ res' = [res EXCEPT ![self] = RFlags[self]]
             /\ IF res'[self] = TRUE
                   THEN /\ Assert((curr_msg'[self] = "msg"), 
                                  "Failure of assertion at line 64, column 13.")
                   ELSE /\ Assert((curr_msg'[self] = ""), 
                                  "Failure of assertion at line 66, column 13.")
             /\ pc' = [pc EXCEPT ![self] = "Read"]
             /\ UNCHANGED << queue, sem, Readers, Writers, Res, RFlags, stack, 
                             val >>

reader(self) == Read(self) \/ lab(self)

Next == (\E self \in ProcSet: Enqueue(self) \/ Dequeue(self))
           \/ (\E self \in Writers: writer(self))
           \/ (\E self \in Readers: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Apr 23 18:59:27 MSK 2023 by bg
\* Created Sat Apr 22 10:57:36 MSK 2023 by bg
