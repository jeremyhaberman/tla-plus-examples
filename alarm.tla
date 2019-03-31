------------------------------- MODULE alarm -------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets

(*--algorithm alarm

\* Simple Timer
\* - alarm time can be set for any minute
\* - alarm can be on or off
\* - 3-minute snooze
\* - alarm rings for max of 5 minutes

variables

    max_time = 60,
    
    on = FALSE,
    ringing = FALSE,
    snoozing = FALSE,
    alarm_time \in 1..max_time,
    snooze_time = 0,
    current_time = 0,
    
    effective_alarm_time = alarm_time;
    
define

    NoRingingWhileOff == ~(ringing = TRUE /\ on = FALSE)
    NoRingingWhileSnoozing == ~(ringing = TRUE /\ snoozing = TRUE)
    NoSnoozingWhileOff == ~(snoozing = TRUE /\ on = FALSE)
    NoSnoozingMoreThanThreeMinutes == ~(snoozing = TRUE /\ (current_time - snooze_time > 3))
    NoRingingMoreThanFiveMinutes == ~(ringing = TRUE /\ (current_time - effective_alarm_time > 5))
    
end define;

macro turn_on() begin
    on := TRUE;
end macro;

macro ring_alarm() begin
    ringing := TRUE;
    snoozing := FALSE;
    snooze_time := 0;
end macro;

macro turn_off() begin
    ringing := FALSE;
    snoozing := FALSE;
    effective_alarm_time := alarm_time;
end macro;

macro snooze() begin
    ringing := FALSE;
    snoozing := TRUE;
    snooze_time := current_time;    
    effective_alarm_time := current_time + 3;
end macro;

begin
    
    while current_time <= max_time do
        current_time := current_time + 1;
        
        \* -------------------------------------------------------
        \* These first two parts are automatic system functions
        \* -------------------------------------------------------
        
        \* If ringing more than five minutes, stop
        if ringing = TRUE /\ (current_time - effective_alarm_time >= 5) then
            turn_off()
        end if;

        \* If the alarm is on and it's time, ring the alarm!
        if on = TRUE /\ (effective_alarm_time >= current_time) then
            ring_alarm()
        end if;
        
        \* --------------------------------------------
        \* This section handles the user's response:
        \*     turn on, turn off, snooze, or do nothing
        \* --------------------------------------------
        
        either     
            if on = FALSE then
                turn_on()
            end if;
        or
            if on = TRUE then
                turn_off()
            end if;
        or
            if ringing = TRUE then
                either
                    snooze()
                or
                    turn_off()
                end either;
            end if;
        or
            skip
            
        end either;
        
    end while;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES max_time, on, ringing, snoozing, alarm_time, snooze_time, 
          current_time, effective_alarm_time, pc

(* define statement *)
NoRingingWhileOff == ~(ringing = TRUE /\ on = FALSE)
NoRingingWhileSnoozing == ~(ringing = TRUE /\ snoozing = TRUE)
NoSnoozingWhileOff == ~(snoozing = TRUE /\ on = FALSE)
NoSnoozingMoreThanThreeMinutes == ~(snoozing = TRUE /\ (current_time - snooze_time > 3))
NoRingingMoreThanFiveMinutes == ~(ringing = TRUE /\ (current_time - effective_alarm_time > 5))


vars == << max_time, on, ringing, snoozing, alarm_time, snooze_time, 
           current_time, effective_alarm_time, pc >>

Init == (* Global variables *)
        /\ max_time = 60
        /\ on = FALSE
        /\ ringing = FALSE
        /\ snoozing = FALSE
        /\ alarm_time \in 1..max_time
        /\ snooze_time = 0
        /\ current_time = 0
        /\ effective_alarm_time = alarm_time
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF current_time <= max_time
               THEN /\ current_time' = current_time + 1
                    /\ IF ringing = TRUE /\ (current_time' - effective_alarm_time >= 5)
                          THEN /\ ringing' = FALSE
                               /\ snoozing' = FALSE
                               /\ effective_alarm_time' = alarm_time
                          ELSE /\ TRUE
                               /\ UNCHANGED << ringing, snoozing, 
                                               effective_alarm_time >>
                    /\ IF on = TRUE /\ (effective_alarm_time' >= current_time')
                          THEN /\ pc' = "Lbl_2"
                          ELSE /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << ringing, snoozing, current_time, 
                                    effective_alarm_time >>
         /\ UNCHANGED << max_time, on, alarm_time, snooze_time >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ \/ /\ IF on = FALSE
                     THEN /\ on' = TRUE
                     ELSE /\ TRUE
                          /\ on' = on
               /\ UNCHANGED <<ringing, snoozing, snooze_time, effective_alarm_time>>
            \/ /\ IF on = TRUE
                     THEN /\ ringing' = FALSE
                          /\ snoozing' = FALSE
                          /\ effective_alarm_time' = alarm_time
                     ELSE /\ TRUE
                          /\ UNCHANGED << ringing, snoozing, 
                                          effective_alarm_time >>
               /\ UNCHANGED <<on, snooze_time>>
            \/ /\ IF ringing = TRUE
                     THEN /\ \/ /\ ringing' = FALSE
                                /\ snoozing' = TRUE
                                /\ snooze_time' = current_time
                                /\ effective_alarm_time' = current_time + 3
                             \/ /\ ringing' = FALSE
                                /\ snoozing' = FALSE
                                /\ effective_alarm_time' = alarm_time
                                /\ UNCHANGED snooze_time
                     ELSE /\ TRUE
                          /\ UNCHANGED << ringing, snoozing, snooze_time, 
                                          effective_alarm_time >>
               /\ on' = on
            \/ /\ TRUE
               /\ UNCHANGED <<on, ringing, snoozing, snooze_time, effective_alarm_time>>
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << max_time, alarm_time, current_time >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ ringing' = TRUE
         /\ snoozing' = FALSE
         /\ snooze_time' = 0
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << max_time, on, alarm_time, current_time, 
                         effective_alarm_time >>

Next == Lbl_1 \/ Lbl_3 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Mar 31 13:14:46 CDT 2019 by jeremy
\* Created Sun Mar 31 07:15:24 CDT 2019 by jeremy
