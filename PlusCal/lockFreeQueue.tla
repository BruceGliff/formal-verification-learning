------------------------------- MODULE lockFreeQueue -------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS Readers, Writers, MsgCount
(*--algorithm message_queue
variables queue = <<0>>,
         MsgRead = 0,
         Idx = 0,
         Res = [w \in Readers |-> ""],
         Msgs = MsgCount,
         CASResW = [w \in Writers |-> ""],
         CASResR = [w \in Readers |-> ""],
         RFlags = [w \in Readers |-> FALSE];


define
AllRead == MsgRead + Len(queue) + Msgs - 1 = MsgCount
QueueValid == Len(queue) <= MsgCount
end define;

macro CAS(success, ptr, old, new) begin
    if (ptr = old) then
        ptr := new;
        success := TRUE;
    else
        success := FALSE;
    end if;
end macro


macro EndQ(Val, Sz) begin
    Sz := Len(queue);
    Val := queue[Sz];
end macro


procedure Enqueue() begin
EnqBegin:
    EndEq := TRUE;
EnqLoopBegin:
    while EndEq do
        EnqLoop:
            EndQ(Val1, Sz1);
        EnqIf:
            EndQ(Val2, Sz2);
            if Val1 = Val2 then
                if Val1 = Idx then
                    EndQ(Val4, Sz4);
                    SuccEq:
                        \* Try to enqueue
                        CAS(Succ, Idx, Val4, Val1 + 1);
                        if Succ then
                            queue := Append(queue, Val1);
                            Msgs := Msgs - 1;
                            EndEq := FALSE;
                        end if;
                else
                    \* Try to swing tail.
                    EndQ(Val3, Sz3);
                    SwingTail:
                        CAS(Succ, Val1, Val3, Val1 + 1);
                end if;
            end if;
    end while;
end procedure;

procedure Dequeue() begin
DeqBegin:
    curr_msg := "ASD";

end procedure;
    

process writer \in Writers
variables EndEq, Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, Succ;
begin Write:
    while Msgs /= 0 do
        call Enqueue();
    end while;
end process;

process reader \in Readers
variables curr_msg = "", res = FALSE;
begin Read:
    curr_msg := "ASD"
end process;
end algorithm;*)


\* BEGIN TRANSLATION (chksum(pcal) = "1eccabab" /\ chksum(tla) = "19ed7672")
CONSTANT defaultInitValue
VARIABLES queue, MsgRead, Idx, Res, Msgs, CASResW, CASResR, RFlags, pc, stack

(* define statement *)
AllRead == MsgRead + Len(queue) + Msgs - 1 = MsgCount
QueueValid == Len(queue) <= MsgCount

VARIABLES EndEq, Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, Succ, curr_msg, 
          res

vars == << queue, MsgRead, Idx, Res, Msgs, CASResW, CASResR, RFlags, pc, 
           stack, EndEq, Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, Succ, 
           curr_msg, res >>

ProcSet == (Writers) \cup (Readers)

Init == (* Global variables *)
        /\ queue = <<0>>
        /\ MsgRead = 0
        /\ Idx = 0
        /\ Res = [w \in Readers |-> ""]
        /\ Msgs = MsgCount
        /\ CASResW = [w \in Writers |-> ""]
        /\ CASResR = [w \in Readers |-> ""]
        /\ RFlags = [w \in Readers |-> FALSE]
        (* Process writer *)
        /\ EndEq = [self \in Writers |-> defaultInitValue]
        /\ Sz1 = [self \in Writers |-> defaultInitValue]
        /\ Sz2 = [self \in Writers |-> defaultInitValue]
        /\ Sz3 = [self \in Writers |-> defaultInitValue]
        /\ Sz4 = [self \in Writers |-> defaultInitValue]
        /\ Val1 = [self \in Writers |-> defaultInitValue]
        /\ Val2 = [self \in Writers |-> defaultInitValue]
        /\ Val3 = [self \in Writers |-> defaultInitValue]
        /\ Val4 = [self \in Writers |-> defaultInitValue]
        /\ Succ = [self \in Writers |-> defaultInitValue]
        (* Process reader *)
        /\ curr_msg = [self \in Readers |-> ""]
        /\ res = [self \in Readers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "Write"
                                        [] self \in Readers -> "Read"]

EnqBegin(self) == /\ pc[self] = "EnqBegin"
                  /\ EndEq' = [EndEq EXCEPT ![self] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "EnqLoopBegin"]
                  /\ UNCHANGED << queue, MsgRead, Idx, Res, Msgs, CASResW, 
                                  CASResR, RFlags, stack, Sz1, Sz2, Sz3, Sz4, 
                                  Val1, Val2, Val3, Val4, Succ, curr_msg, res >>

EnqLoopBegin(self) == /\ pc[self] = "EnqLoopBegin"
                      /\ IF EndEq[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = "EnqLoop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                      /\ UNCHANGED << queue, MsgRead, Idx, Res, Msgs, CASResW, 
                                      CASResR, RFlags, stack, EndEq, Sz1, Sz2, 
                                      Sz3, Sz4, Val1, Val2, Val3, Val4, Succ, 
                                      curr_msg, res >>

EnqLoop(self) == /\ pc[self] = "EnqLoop"
                 /\ Sz1' = [Sz1 EXCEPT ![self] = Len(queue)]
                 /\ Val1' = [Val1 EXCEPT ![self] = queue[Sz1'[self]]]
                 /\ pc' = [pc EXCEPT ![self] = "EnqIf"]
                 /\ UNCHANGED << queue, MsgRead, Idx, Res, Msgs, CASResW, 
                                 CASResR, RFlags, stack, EndEq, Sz2, Sz3, Sz4, 
                                 Val2, Val3, Val4, Succ, curr_msg, res >>

EnqIf(self) == /\ pc[self] = "EnqIf"
               /\ Sz2' = [Sz2 EXCEPT ![self] = Len(queue)]
               /\ Val2' = [Val2 EXCEPT ![self] = queue[Sz2'[self]]]
               /\ IF Val1[self] = Val2'[self]
                     THEN /\ IF Val1[self] = Idx
                                THEN /\ Sz4' = [Sz4 EXCEPT ![self] = Len(queue)]
                                     /\ Val4' = [Val4 EXCEPT ![self] = queue[Sz4'[self]]]
                                     /\ pc' = [pc EXCEPT ![self] = "SuccEq"]
                                     /\ UNCHANGED << Sz3, Val3 >>
                                ELSE /\ Sz3' = [Sz3 EXCEPT ![self] = Len(queue)]
                                     /\ Val3' = [Val3 EXCEPT ![self] = queue[Sz3'[self]]]
                                     /\ pc' = [pc EXCEPT ![self] = "SwingTail"]
                                     /\ UNCHANGED << Sz4, Val4 >>
                     ELSE /\ pc' = [pc EXCEPT ![self] = "EnqLoopBegin"]
                          /\ UNCHANGED << Sz3, Sz4, Val3, Val4 >>
               /\ UNCHANGED << queue, MsgRead, Idx, Res, Msgs, CASResW, 
                               CASResR, RFlags, stack, EndEq, Sz1, Val1, Succ, 
                               curr_msg, res >>

SuccEq(self) == /\ pc[self] = "SuccEq"
                /\ IF (Idx = Val4[self])
                      THEN /\ Idx' = Val1[self] + 1
                           /\ Succ' = [Succ EXCEPT ![self] = TRUE]
                      ELSE /\ Succ' = [Succ EXCEPT ![self] = FALSE]
                           /\ Idx' = Idx
                /\ IF Succ'[self]
                      THEN /\ queue' = Append(queue, Val1[self])
                           /\ Msgs' = Msgs - 1
                           /\ EndEq' = [EndEq EXCEPT ![self] = FALSE]
                      ELSE /\ TRUE
                           /\ UNCHANGED << queue, Msgs, EndEq >>
                /\ pc' = [pc EXCEPT ![self] = "EnqLoopBegin"]
                /\ UNCHANGED << MsgRead, Res, CASResW, CASResR, RFlags, stack, 
                                Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, 
                                curr_msg, res >>

SwingTail(self) == /\ pc[self] = "SwingTail"
                   /\ IF (Val1[self] = Val3[self])
                         THEN /\ Val1' = [Val1 EXCEPT ![self] = Val1[self] + 1]
                              /\ Succ' = [Succ EXCEPT ![self] = TRUE]
                         ELSE /\ Succ' = [Succ EXCEPT ![self] = FALSE]
                              /\ Val1' = Val1
                   /\ pc' = [pc EXCEPT ![self] = "EnqLoopBegin"]
                   /\ UNCHANGED << queue, MsgRead, Idx, Res, Msgs, CASResW, 
                                   CASResR, RFlags, stack, EndEq, Sz1, Sz2, 
                                   Sz3, Sz4, Val2, Val3, Val4, curr_msg, res >>

Enqueue(self) == EnqBegin(self) \/ EnqLoopBegin(self) \/ EnqLoop(self)
                    \/ EnqIf(self) \/ SuccEq(self) \/ SwingTail(self)

DeqBegin(self) == /\ pc[self] = "DeqBegin"
                  /\ curr_msg' = [curr_msg EXCEPT ![self] = "ASD"]
                  /\ pc' = [pc EXCEPT ![self] = "Error"]
                  /\ UNCHANGED << queue, MsgRead, Idx, Res, Msgs, CASResW, 
                                  CASResR, RFlags, stack, EndEq, Sz1, Sz2, Sz3, 
                                  Sz4, Val1, Val2, Val3, Val4, Succ, res >>

Dequeue(self) == DeqBegin(self)

Write(self) == /\ pc[self] = "Write"
               /\ IF Msgs /= 0
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                                   pc        |->  "Write" ] >>
                                                               \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "EnqBegin"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ stack' = stack
               /\ UNCHANGED << queue, MsgRead, Idx, Res, Msgs, CASResW, 
                               CASResR, RFlags, EndEq, Sz1, Sz2, Sz3, Sz4, 
                               Val1, Val2, Val3, Val4, Succ, curr_msg, res >>

writer(self) == Write(self)

Read(self) == /\ pc[self] = "Read"
              /\ curr_msg' = [curr_msg EXCEPT ![self] = "ASD"]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << queue, MsgRead, Idx, Res, Msgs, CASResW, CASResR, 
                              RFlags, stack, EndEq, Sz1, Sz2, Sz3, Sz4, Val1, 
                              Val2, Val3, Val4, Succ, res >>

reader(self) == Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Enqueue(self) \/ Dequeue(self))
           \/ (\E self \in Writers: writer(self))
           \/ (\E self \in Readers: reader(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat May 06 14:11:11 MSK 2023 by bg
\* Created Sat Apr 22 10:57:36 MSK 2023 by bg
