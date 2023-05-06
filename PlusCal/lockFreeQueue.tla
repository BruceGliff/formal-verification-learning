------------------------------- MODULE lockFreeQueue -------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS Readers, Writers, MsgCount
(*--algorithm message_queue
variables queue = <<0>>,
         MsgRead = 0,
         Idx = 0,
         Msgs = MsgCount,
         RFlags = [w \in Readers |-> FALSE];


define
AllRead == MsgRead + Len(queue) + Msgs - 1 = MsgCount
QueueValid == Len(queue) <= MsgCount + 1 /\ Len(queue) >= 1
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
EnqLoopBegin:
    while TRUE do
        EnqLoop: EndQ(Val1, Sz1);
        EnqIf: EndQ(Val2, Sz2);
        if Val1 = Val2 then
            if Val1 = Idx then
                GetTail1: EndQ(Val4, Sz4);
                SuccEnq: CAS(Succ, Idx, Val4, Val1 + 1);
                if Succ then
                    if Msgs /= 0 then
                        return;
                    else
                        queue := Append(queue, Val1);
                        Msgs := Msgs - 1;
                        return;
                    end if;
                end if;
            else
                \* Try to swing tail.
                GetTail2: EndQ(Val3, Sz3);
                SwingTail: CAS(Succ, Val1, Val3, Val1 + 1);
            end if;
        end if;
    end while;
end procedure;

procedure Dequeue() begin
DeqLoopBegin:
    while TRUE do
        DeqLoop: H1 := Head(queue);
        DeqTail: EndQ(RVal1, RSz1);
        DeqHead1:
            if H1 = Head(queue) then
                if H1 = Val1 then
                    if H1 = 0 then \* queue is empty
                        QueueIsEmpty: RFlags[self] := FALSE;
                            return;
                    else
                        GetTail3: EndQ(RVal2, RSz2);
                        AdvanceTail: CAS(RSucc, RVal1, RVal2, Val1 + 1);
                    end if;
                else
                    DeqHead2: H2 := Head(queue);
                    RSuccEnq: CAS(RSucc, H1, H2, H1 + 1);
                    if Succ then
                        queue := Tail(queue);
                        MsgRead := MsgRead + 1;
                        RFlags[self] := TRUE;
                        return;
                    end if;
                end if;
            end if;
    end while;
end procedure;
    

process writer \in Writers
variables  Sz1 = 0, Sz2 = 0, Sz3 = 0, Sz4 = 0, Val1 = 0, Val2 = 0, Val3 = 0, Val4 = 0, Succ = TRUE;
begin Write:
    while Msgs /= 0 do
        call Enqueue();
    end while;
end process;

process reader \in Readers
variables H1 = 0, H2 = 0, RSz1 = 0, RSz2 = 0, RVal1 = 0, RVal2 = 0, RSucc = TRUE;
begin Read:
    while TRUE do
        call Dequeue();
    end while;
end process;
end algorithm;*)


\* BEGIN TRANSLATION (chksum(pcal) = "1132bdd6" /\ chksum(tla) = "44272464")
VARIABLES queue, MsgRead, Idx, Msgs, RFlags, pc, stack

(* define statement *)
AllRead == MsgRead + Len(queue) + Msgs - 1 = MsgCount
QueueValid == Len(queue) <= MsgCount + 1 /\ Len(queue) >= 1

VARIABLES Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, Succ, H1, H2, RSz1, 
          RSz2, RVal1, RVal2, RSucc

vars == << queue, MsgRead, Idx, Msgs, RFlags, pc, stack, Sz1, Sz2, Sz3, Sz4, 
           Val1, Val2, Val3, Val4, Succ, H1, H2, RSz1, RSz2, RVal1, RVal2, 
           RSucc >>

ProcSet == (Writers) \cup (Readers)

Init == (* Global variables *)
        /\ queue = <<0>>
        /\ MsgRead = 0
        /\ Idx = 0
        /\ Msgs = MsgCount
        /\ RFlags = [w \in Readers |-> FALSE]
        (* Process writer *)
        /\ Sz1 = [self \in Writers |-> 0]
        /\ Sz2 = [self \in Writers |-> 0]
        /\ Sz3 = [self \in Writers |-> 0]
        /\ Sz4 = [self \in Writers |-> 0]
        /\ Val1 = [self \in Writers |-> 0]
        /\ Val2 = [self \in Writers |-> 0]
        /\ Val3 = [self \in Writers |-> 0]
        /\ Val4 = [self \in Writers |-> 0]
        /\ Succ = [self \in Writers |-> TRUE]
        (* Process reader *)
        /\ H1 = [self \in Readers |-> 0]
        /\ H2 = [self \in Readers |-> 0]
        /\ RSz1 = [self \in Readers |-> 0]
        /\ RSz2 = [self \in Readers |-> 0]
        /\ RVal1 = [self \in Readers |-> 0]
        /\ RVal2 = [self \in Readers |-> 0]
        /\ RSucc = [self \in Readers |-> TRUE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "Write"
                                        [] self \in Readers -> "Read"]

EnqLoopBegin(self) == /\ pc[self] = "EnqLoopBegin"
                      /\ pc' = [pc EXCEPT ![self] = "EnqLoop"]
                      /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                      Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, 
                                      Val4, Succ, H1, H2, RSz1, RSz2, RVal1, 
                                      RVal2, RSucc >>

EnqLoop(self) == /\ pc[self] = "EnqLoop"
                 /\ Sz1' = [Sz1 EXCEPT ![self] = Len(queue)]
                 /\ Val1' = [Val1 EXCEPT ![self] = queue[Sz1'[self]]]
                 /\ pc' = [pc EXCEPT ![self] = "EnqIf"]
                 /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, Sz2, 
                                 Sz3, Sz4, Val2, Val3, Val4, Succ, H1, H2, 
                                 RSz1, RSz2, RVal1, RVal2, RSucc >>

EnqIf(self) == /\ pc[self] = "EnqIf"
               /\ Sz2' = [Sz2 EXCEPT ![self] = Len(queue)]
               /\ Val2' = [Val2 EXCEPT ![self] = queue[Sz2'[self]]]
               /\ IF Val1[self] = Val2'[self]
                     THEN /\ IF Val1[self] = Idx
                                THEN /\ pc' = [pc EXCEPT ![self] = "GetTail1"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "GetTail2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "EnqLoopBegin"]
               /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, Sz1, 
                               Sz3, Sz4, Val1, Val3, Val4, Succ, H1, H2, RSz1, 
                               RSz2, RVal1, RVal2, RSucc >>

GetTail1(self) == /\ pc[self] = "GetTail1"
                  /\ Sz4' = [Sz4 EXCEPT ![self] = Len(queue)]
                  /\ Val4' = [Val4 EXCEPT ![self] = queue[Sz4'[self]]]
                  /\ pc' = [pc EXCEPT ![self] = "SuccEnq"]
                  /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                  Sz1, Sz2, Sz3, Val1, Val2, Val3, Succ, H1, 
                                  H2, RSz1, RSz2, RVal1, RVal2, RSucc >>

SuccEnq(self) == /\ pc[self] = "SuccEnq"
                 /\ IF (Idx = Val4[self])
                       THEN /\ Idx' = Val1[self] + 1
                            /\ Succ' = [Succ EXCEPT ![self] = TRUE]
                       ELSE /\ Succ' = [Succ EXCEPT ![self] = FALSE]
                            /\ Idx' = Idx
                 /\ IF Succ'[self]
                       THEN /\ IF Msgs /= 0
                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                       /\ UNCHANGED << queue, Msgs >>
                                  ELSE /\ queue' = Append(queue, Val1[self])
                                       /\ Msgs' = Msgs - 1
                                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "EnqLoopBegin"]
                            /\ UNCHANGED << queue, Msgs, stack >>
                 /\ UNCHANGED << MsgRead, RFlags, Sz1, Sz2, Sz3, Sz4, Val1, 
                                 Val2, Val3, Val4, H1, H2, RSz1, RSz2, RVal1, 
                                 RVal2, RSucc >>

GetTail2(self) == /\ pc[self] = "GetTail2"
                  /\ Sz3' = [Sz3 EXCEPT ![self] = Len(queue)]
                  /\ Val3' = [Val3 EXCEPT ![self] = queue[Sz3'[self]]]
                  /\ pc' = [pc EXCEPT ![self] = "SwingTail"]
                  /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                  Sz1, Sz2, Sz4, Val1, Val2, Val4, Succ, H1, 
                                  H2, RSz1, RSz2, RVal1, RVal2, RSucc >>

SwingTail(self) == /\ pc[self] = "SwingTail"
                   /\ IF (Val1[self] = Val3[self])
                         THEN /\ Val1' = [Val1 EXCEPT ![self] = Val1[self] + 1]
                              /\ Succ' = [Succ EXCEPT ![self] = TRUE]
                         ELSE /\ Succ' = [Succ EXCEPT ![self] = FALSE]
                              /\ Val1' = Val1
                   /\ pc' = [pc EXCEPT ![self] = "EnqLoopBegin"]
                   /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                   Sz1, Sz2, Sz3, Sz4, Val2, Val3, Val4, H1, 
                                   H2, RSz1, RSz2, RVal1, RVal2, RSucc >>

Enqueue(self) == EnqLoopBegin(self) \/ EnqLoop(self) \/ EnqIf(self)
                    \/ GetTail1(self) \/ SuccEnq(self) \/ GetTail2(self)
                    \/ SwingTail(self)

DeqLoopBegin(self) == /\ pc[self] = "DeqLoopBegin"
                      /\ pc' = [pc EXCEPT ![self] = "DeqLoop"]
                      /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                      Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, 
                                      Val4, Succ, H1, H2, RSz1, RSz2, RVal1, 
                                      RVal2, RSucc >>

DeqLoop(self) == /\ pc[self] = "DeqLoop"
                 /\ H1' = [H1 EXCEPT ![self] = Head(queue)]
                 /\ pc' = [pc EXCEPT ![self] = "DeqTail"]
                 /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, Sz1, 
                                 Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, Succ, 
                                 H2, RSz1, RSz2, RVal1, RVal2, RSucc >>

DeqTail(self) == /\ pc[self] = "DeqTail"
                 /\ RSz1' = [RSz1 EXCEPT ![self] = Len(queue)]
                 /\ RVal1' = [RVal1 EXCEPT ![self] = queue[RSz1'[self]]]
                 /\ pc' = [pc EXCEPT ![self] = "DeqHead1"]
                 /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, Sz1, 
                                 Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, Succ, 
                                 H1, H2, RSz2, RVal2, RSucc >>

DeqHead1(self) == /\ pc[self] = "DeqHead1"
                  /\ IF H1[self] = Head(queue)
                        THEN /\ IF H1[self] = Val1[self]
                                   THEN /\ IF H1[self] = 0
                                              THEN /\ pc' = [pc EXCEPT ![self] = "QueueIsEmpty"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "GetTail3"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "DeqHead2"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "DeqLoopBegin"]
                  /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                  Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, 
                                  Succ, H1, H2, RSz1, RSz2, RVal1, RVal2, 
                                  RSucc >>

DeqHead2(self) == /\ pc[self] = "DeqHead2"
                  /\ H2' = [H2 EXCEPT ![self] = Head(queue)]
                  /\ pc' = [pc EXCEPT ![self] = "RSuccEnq"]
                  /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                  Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, 
                                  Succ, H1, RSz1, RSz2, RVal1, RVal2, RSucc >>

RSuccEnq(self) == /\ pc[self] = "RSuccEnq"
                  /\ IF (H1[self] = H2[self])
                        THEN /\ H1' = [H1 EXCEPT ![self] = H1[self] + 1]
                             /\ RSucc' = [RSucc EXCEPT ![self] = TRUE]
                        ELSE /\ RSucc' = [RSucc EXCEPT ![self] = FALSE]
                             /\ H1' = H1
                  /\ IF Succ[self]
                        THEN /\ queue' = Tail(queue)
                             /\ MsgRead' = MsgRead + 1
                             /\ RFlags' = [RFlags EXCEPT ![self] = TRUE]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "DeqLoopBegin"]
                             /\ UNCHANGED << queue, MsgRead, RFlags, stack >>
                  /\ UNCHANGED << Idx, Msgs, Sz1, Sz2, Sz3, Sz4, Val1, Val2, 
                                  Val3, Val4, Succ, H2, RSz1, RSz2, RVal1, 
                                  RVal2 >>

QueueIsEmpty(self) == /\ pc[self] = "QueueIsEmpty"
                      /\ RFlags' = [RFlags EXCEPT ![self] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << queue, MsgRead, Idx, Msgs, Sz1, Sz2, Sz3, 
                                      Sz4, Val1, Val2, Val3, Val4, Succ, H1, 
                                      H2, RSz1, RSz2, RVal1, RVal2, RSucc >>

GetTail3(self) == /\ pc[self] = "GetTail3"
                  /\ RSz2' = [RSz2 EXCEPT ![self] = Len(queue)]
                  /\ RVal2' = [RVal2 EXCEPT ![self] = queue[RSz2'[self]]]
                  /\ pc' = [pc EXCEPT ![self] = "AdvanceTail"]
                  /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                  Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, Val4, 
                                  Succ, H1, H2, RSz1, RVal1, RSucc >>

AdvanceTail(self) == /\ pc[self] = "AdvanceTail"
                     /\ IF (RVal1[self] = RVal2[self])
                           THEN /\ RVal1' = [RVal1 EXCEPT ![self] = Val1[self] + 1]
                                /\ RSucc' = [RSucc EXCEPT ![self] = TRUE]
                           ELSE /\ RSucc' = [RSucc EXCEPT ![self] = FALSE]
                                /\ RVal1' = RVal1
                     /\ pc' = [pc EXCEPT ![self] = "DeqLoopBegin"]
                     /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, stack, 
                                     Sz1, Sz2, Sz3, Sz4, Val1, Val2, Val3, 
                                     Val4, Succ, H1, H2, RSz1, RSz2, RVal2 >>

Dequeue(self) == DeqLoopBegin(self) \/ DeqLoop(self) \/ DeqTail(self)
                    \/ DeqHead1(self) \/ DeqHead2(self) \/ RSuccEnq(self)
                    \/ QueueIsEmpty(self) \/ GetTail3(self)
                    \/ AdvanceTail(self)

Write(self) == /\ pc[self] = "Write"
               /\ IF Msgs /= 0
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                                   pc        |->  "Write" ] >>
                                                               \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "EnqLoopBegin"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ stack' = stack
               /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, Sz1, Sz2, 
                               Sz3, Sz4, Val1, Val2, Val3, Val4, Succ, H1, H2, 
                               RSz1, RSz2, RVal1, RVal2, RSucc >>

writer(self) == Write(self)

Read(self) == /\ pc[self] = "Read"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Dequeue",
                                                       pc        |->  "Read" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "DeqLoopBegin"]
              /\ UNCHANGED << queue, MsgRead, Idx, Msgs, RFlags, Sz1, Sz2, Sz3, 
                              Sz4, Val1, Val2, Val3, Val4, Succ, H1, H2, RSz1, 
                              RSz2, RVal1, RVal2, RSucc >>

reader(self) == Read(self)

Next == (\E self \in ProcSet: Enqueue(self) \/ Dequeue(self))
           \/ (\E self \in Writers: writer(self))
           \/ (\E self \in Readers: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat May 06 20:56:26 MSK 2023 by bg
\* Created Sat Apr 22 10:57:36 MSK 2023 by bg
