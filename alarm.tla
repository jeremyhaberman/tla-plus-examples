------------------------------- MODULE alarm -------------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets

(*--algorithm alarm

\* Alarm Clock
\*
\* This is a spec of the Marathon Analog Desk Alarm Clock (pretend it's digital)
\* https://www.marathonwatch.com/collections/clocks/products/analog-desk-alarm-clock-with-auto-night-light
\*
\* - alarm time can be set for any minute
\* - alarm can be on or off
\* - 3-minute snooze
\* - alarm rings for max of 5 minutes
\* - alarm time can be changed
\* - show backlight when not ringing (not currently supported)
\* - auto-night light (not currently supported)

\* Time is handled by counting minutes. Minutes are the smallest and only
\* unit of time. This was my first attempt at writing a TLA+ spec after reading
\* chapter 2 of Practical TLA+.

variables    

    \* Total minutes in a day
    \* I used '20' during development, and it would run within ~10 seconds.
    \* '1440' took ~5 minutes (on an old iMac) and found 69,236,189 distinct
    \* states.
    max_time = 1440,
    
    on = FALSE,
    ringing = FALSE,
    snoozing = FALSE,
    alarm_time \in 1..max_time,
    snooze_time = 0,
    current_time = 0,
    
    \* Used to distinguish between the actual alarm time set on the clock and
    \* an effecitve alarm time to support snoozing.
    effective_alarm_time = alarm_time;
    
define

    \* These specify what cannot happen. I'm not confident the program does
    \* what it should. I feel like I'm missing something.

    NoRingingWhileOff == ~(ringing = TRUE /\ on = FALSE)
    NoRingingWhileSnoozing == ~(ringing = TRUE /\ snoozing = TRUE)
    NoSnoozingWhileOff == ~(snoozing = TRUE /\ on = FALSE)
    NoSnoozingMoreThanThreeMinutes == ~(snoozing = TRUE /\ (current_time - snooze_time > 3))
    NoRingingMoreThanFiveMinutes == ~(ringing = TRUE /\ (current_time - effective_alarm_time > 5))
    
    \* I think these help make the algorithm easier to read. I'm not sure if
    \* or how these and the macros may help or hurt––or perhaps some of both.
    
    AlarmOff == on = FALSE
    AlarmOn == on = TRUE
    Ringing == ringing = TRUE
    RingingForAtLeastFiveMinutes == Ringing /\ (current_time - effective_alarm_time >= 5)
    OnAndCurrentTimeIsAlarmTime == AlarmOn /\ ~Ringing /\ (effective_alarm_time >= current_time)
    
end define;

macro simulate_clock_tick() begin
    current_time := current_time + 1;
end macro;

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

macro press_on_off_button() begin
    if AlarmOff then
        turn_on()
    else
        turn_off()
    end if;
end macro;

macro press_snooze_light_button() begin
    if Ringing then
        snooze()
    end if;
end macro;

macro change_alarm_time() begin
    \* this works, but it seems like there should be a simpler way
    \* to get a number between 1..max_time
    alarm_time := CHOOSE x \in 1..max_time : x <= max_time;
end macro;

begin
    
    while current_time <= max_time do
    
        simulate_clock_tick();
        
        \* Automatic system functions
        
        if RingingForAtLeastFiveMinutes then
            turn_off()
        elsif OnAndCurrentTimeIsAlarmTime then
            ring_alarm()
        end if;
        
        \* Possible user actions
        
        either
            \* If off:
            \* - turn on
            \* If on:
            \* - alarm ringing and want to turn it off or
            \* - turn off alarm before it rings.
            press_on_off_button()
        or
            \* If alarm is ringing:
            \* - snooze
            \* If alarm is not ringing:
            \* - Turn on backlight (not currently supported)
            press_snooze_light_button()
        or
            \* Do nothing cause the alarm isn't ringing or
            \* the alarm is ringing but being ignored.
            skip;
        or
            \* Allow changing the alarm time but only if the alarm is not
            \* already ringing
            if ~Ringing then
                change_alarm_time();
            end if;
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




AlarmOff == on = FALSE
AlarmOn == on = TRUE
Ringing == ringing = TRUE
RingingForAtLeastFiveMinutes == Ringing /\ (current_time - effective_alarm_time >= 5)
OnAndCurrentTimeIsAlarmTime == AlarmOn /\ ~Ringing /\ (effective_alarm_time >= current_time)


vars == << max_time, on, ringing, snoozing, alarm_time, snooze_time, 
           current_time, effective_alarm_time, pc >>

Init == (* Global variables *)
        /\ max_time = 20
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
                    /\ IF RingingForAtLeastFiveMinutes
                          THEN /\ ringing' = FALSE
                               /\ snoozing' = FALSE
                               /\ effective_alarm_time' = alarm_time
                               /\ UNCHANGED snooze_time
                          ELSE /\ IF OnAndCurrentTimeIsAlarmTime
                                     THEN /\ ringing' = TRUE
                                          /\ snoozing' = FALSE
                                          /\ snooze_time' = 0
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << ringing, snoozing, 
                                                          snooze_time >>
                               /\ UNCHANGED effective_alarm_time
                    /\ \/ /\ IF AlarmOff
                                THEN /\ on' = TRUE
                                     /\ pc' = "Lbl_1"
                                ELSE /\ pc' = "Lbl_2"
                                     /\ on' = on
                          /\ UNCHANGED alarm_time
                       \/ /\ IF Ringing
                                THEN /\ pc' = "Lbl_3"
                                ELSE /\ pc' = "Lbl_1"
                          /\ UNCHANGED <<on, alarm_time>>
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
                          /\ UNCHANGED <<on, alarm_time>>
                       \/ /\ IF ~Ringing
                                THEN /\ alarm_time' = (CHOOSE x \in 1..max_time : x <= max_time)
                                ELSE /\ TRUE
                                     /\ UNCHANGED alarm_time
                          /\ pc' = "Lbl_1"
                          /\ on' = on
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << on, ringing, snoozing, alarm_time, 
                                    snooze_time, current_time, 
                                    effective_alarm_time >>
         /\ UNCHANGED max_time

Lbl_2 == /\ pc = "Lbl_2"
         /\ ringing' = FALSE
         /\ snoozing' = FALSE
         /\ effective_alarm_time' = alarm_time
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << max_time, on, alarm_time, snooze_time, current_time >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ ringing' = FALSE
         /\ snoozing' = TRUE
         /\ snooze_time' = current_time
         /\ effective_alarm_time' = current_time + 3
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << max_time, on, alarm_time, current_time >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Mar 31 19:02:11 CDT 2019 by jeremy
\* Created Sun Mar 31 07:15:24 CDT 2019 by jeremy
