------------------------------- MODULE queue -------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS Readers, Writers, MsgCount
(*--algorithm message_queue
variables queue = <<>>,
         MsgRead = 0,
         sem = 1,
         Res = [w \in Readers |-> ""],
         Msgs = MsgCount,
         RFlags = [w \in Readers |-> FALSE];


define
AllRead == MsgRead + Len(queue) + Msgs = MsgCount
end define;

procedure Enqueue(val="") begin
  En:
    await sem = 1;
    sem := 0;
   l1:
    queue := Append(queue, val);
    Msgs := Msgs - 1;
 
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
  l1:
        Res[self] := Head(queue);
  l2:
        RFlags[self] := TRUE;
  l3:
        queue := Tail(queue);
        MsgRead := MsgRead + 1;
   unlock_succ: sem:= 1;
        return;
    end if;
end procedure;
    

process writer \in Writers
begin Write:
    while Msgs /= 0 do
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


\* BEGIN TRANSLATION (chksum(pcal) = "1fe73c46" /\ chksum(tla) = "781738a4")
\* Label l1 of procedure Enqueue at line 23 col 5 changed to l1_
\* Label unlock of procedure Enqueue at line 26 col 12 changed to unlock_
VARIABLES queue, MsgRead, sem, Res, Msgs, RFlags, pc, stack

(* define statement *)
AllRead == MsgRead + Len(queue) + Msgs = MsgCount

VARIABLES val, curr_msg, res

vars == << queue, MsgRead, sem, Res, Msgs, RFlags, pc, stack, val, curr_msg, 
           res >>

ProcSet == (Writers) \cup (Readers)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ MsgRead = 0
        /\ sem = 1
        /\ Res = [w \in Readers |-> ""]
        /\ Msgs = MsgCount
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
            /\ sem = 1
            /\ sem' = 0
            /\ pc' = [pc EXCEPT ![self] = "l1_"]
            /\ UNCHANGED << queue, MsgRead, Res, Msgs, RFlags, stack, val, 
                            curr_msg, res >>

l1_(self) == /\ pc[self] = "l1_"
             /\ queue' = Append(queue, val[self])
             /\ Msgs' = Msgs - 1
             /\ pc' = [pc EXCEPT ![self] = "unlock_"]
             /\ UNCHANGED << MsgRead, sem, Res, RFlags, stack, val, curr_msg, 
                             res >>

unlock_(self) == /\ pc[self] = "unlock_"
                 /\ sem' = 1
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << queue, MsgRead, Res, Msgs, RFlags, curr_msg, 
                                 res >>

Enqueue(self) == En(self) \/ l1_(self) \/ unlock_(self)

Dq(self) == /\ pc[self] = "Dq"
            /\ sem = 1 /\ queue /= <<>>
            /\ sem' = 0
            /\ IF queue /= <<>>
                  THEN /\ pc' = [pc EXCEPT ![self] = "unlock"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << queue, MsgRead, Res, Msgs, RFlags, stack, val, 
                            curr_msg, res >>

unlock(self) == /\ pc[self] = "unlock"
                /\ sem' = 1
                /\ RFlags' = [RFlags EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << queue, MsgRead, Res, Msgs, val, curr_msg, res >>

l1(self) == /\ pc[self] = "l1"
            /\ Res' = [Res EXCEPT ![self] = Head(queue)]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << queue, MsgRead, sem, Msgs, RFlags, stack, val, 
                            curr_msg, res >>

l2(self) == /\ pc[self] = "l2"
            /\ RFlags' = [RFlags EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << queue, MsgRead, sem, Res, Msgs, stack, val, 
                            curr_msg, res >>

l3(self) == /\ pc[self] = "l3"
            /\ queue' = Tail(queue)
            /\ MsgRead' = MsgRead + 1
            /\ pc' = [pc EXCEPT ![self] = "unlock_succ"]
            /\ UNCHANGED << sem, Res, Msgs, RFlags, stack, val, curr_msg, res >>

unlock_succ(self) == /\ pc[self] = "unlock_succ"
                     /\ sem' = 1
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << queue, MsgRead, Res, Msgs, RFlags, val, 
                                     curr_msg, res >>

Dequeue(self) == Dq(self) \/ unlock(self) \/ l1(self) \/ l2(self)
                    \/ l3(self) \/ unlock_succ(self)

Write(self) == /\ pc[self] = "Write"
               /\ IF Msgs /= 0
                     THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                                      pc        |->  "Write",
                                                                      val       |->  val[self] ] >>
                                                                  \o stack[self]]
                             /\ val' = [val EXCEPT ![self] = "msg"]
                          /\ pc' = [pc EXCEPT ![self] = "En"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << stack, val >>
               /\ UNCHANGED << queue, MsgRead, sem, Res, Msgs, RFlags, 
                               curr_msg, res >>

writer(self) == Write(self)

Read(self) == /\ pc[self] = "Read"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Dequeue",
                                                       pc        |->  "lab" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "Dq"]
              /\ UNCHANGED << queue, MsgRead, sem, Res, Msgs, RFlags, val, 
                              curr_msg, res >>

lab(self) == /\ pc[self] = "lab"
             /\ curr_msg' = [curr_msg EXCEPT ![self] = Res[self]]
             /\ res' = [res EXCEPT ![self] = RFlags[self]]
             /\ IF res'[self] = TRUE
                   THEN /\ Assert((curr_msg'[self] = "msg"), 
                                  "Failure of assertion at line 69, column 13.")
                   ELSE /\ Assert((curr_msg'[self] = ""), 
                                  "Failure of assertion at line 71, column 13.")
             /\ pc' = [pc EXCEPT ![self] = "Read"]
             /\ UNCHANGED << queue, MsgRead, sem, Res, Msgs, RFlags, stack, 
                             val >>

reader(self) == Read(self) \/ lab(self)

Next == (\E self \in ProcSet: Enqueue(self) \/ Dequeue(self))
           \/ (\E self \in Writers: writer(self))
           \/ (\E self \in Readers: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed May 03 09:54:35 MSK 2023 by bg
\* Created Sat Apr 22 10:57:36 MSK 2023 by bg
