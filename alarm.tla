------------------------------- MODULE alarm -------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets

(*--algorithm alarm

\* Alarm Clock
\* - 24-hour clock
\* - alarm time can be set for any hour+minute
\* - alarm can be on or off
\* - 3-minute snooze
\* - alarm rings for max of 5 minutes

variables

    max_time = 20,
    
    on = FALSE,
    ringing = FALSE,
    alarm_time \in 1..max_time,
    current_time = 0;
    
define

    \* Is there a simpler way to specify this?
    OnlyRingIfOn == (ringing = TRUE /\ on = TRUE)
                    \/ (ringing = FALSE /\ on = TRUE)
                    \/ (ringing = FALSE /\ on = FALSE)
    
end define;

begin
    ClockTick:
        while current_time <= max_time do
            current_time := current_time + 1;
            
            \* ring alarm
            if on /\ alarm_time = current_time then
                RingAlarm:
                    ringing := TRUE;
            end if;
       
            \* turn on, ignore if ringing, or turn off
            Reaction:
                either     
                    TurnOn:
                        on := TRUE;
                or
                    if ringing = TRUE then
                        either
                            TurnOff:
                                ringing := FALSE;
                        or
                            skip
                        end either;
                    end if;
                end either;
            
        end while;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES max_time, on, ringing, alarm_time, current_time, pc

(* define statement *)
OnlyRingIfOn == (ringing = TRUE /\ on = TRUE)
                \/ (ringing = FALSE /\ on = TRUE)
                \/ (ringing = FALSE /\ on = FALSE)


vars == << max_time, on, ringing, alarm_time, current_time, pc >>

Init == (* Global variables *)
        /\ max_time = 20
        /\ on = FALSE
        /\ ringing = FALSE
        /\ alarm_time \in 1..max_time
        /\ current_time = 0
        /\ pc = "ClockTick"

ClockTick == /\ pc = "ClockTick"
             /\ IF current_time <= max_time
                   THEN /\ current_time' = current_time + 1
                        /\ IF on /\ alarm_time = current_time'
                              THEN /\ pc' = "RingAlarm"
                              ELSE /\ pc' = "Reaction"
                   ELSE /\ pc' = "Done"
                        /\ UNCHANGED current_time
             /\ UNCHANGED << max_time, on, ringing, alarm_time >>

Reaction == /\ pc = "Reaction"
            /\ \/ /\ pc' = "TurnOn"
               \/ /\ IF ringing = TRUE
                        THEN /\ \/ /\ pc' = "TurnOff"
                                \/ /\ TRUE
                                   /\ pc' = "ClockTick"
                        ELSE /\ pc' = "ClockTick"
            /\ UNCHANGED << max_time, on, ringing, alarm_time, current_time >>

TurnOn == /\ pc = "TurnOn"
          /\ on' = TRUE
          /\ pc' = "ClockTick"
          /\ UNCHANGED << max_time, ringing, alarm_time, current_time >>

TurnOff == /\ pc = "TurnOff"
           /\ ringing' = FALSE
           /\ pc' = "ClockTick"
           /\ UNCHANGED << max_time, on, alarm_time, current_time >>

RingAlarm == /\ pc = "RingAlarm"
             /\ ringing' = TRUE
             /\ pc' = "Reaction"
             /\ UNCHANGED << max_time, on, alarm_time, current_time >>

Next == ClockTick \/ Reaction \/ TurnOn \/ TurnOff \/ RingAlarm
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Mar 31 11:05:49 CDT 2019 by jeremy
\* Created Sun Mar 31 07:15:24 CDT 2019 by jeremy
