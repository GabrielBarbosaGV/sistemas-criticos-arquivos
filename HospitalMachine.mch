/* HospitalMachine
 * Author: Gabriel
 * Creation date: 26/05/2019
 */
MACHINE
    HospitalMachine
SETS
    INGREDIENTS;
    PATIENTS
VARIABLES
    admittees,
    prohibitions,
    time_fifths_of_day,
    was_served,
    has_eaten,
    eaten_dish
INVARIANT
    admittees <: NATURAL
    & prohibitions : admittees --> POW(NATURAL)
    & time_fifths_of_day : NATURAL
    & has_eaten : admittees * NATURAL +-> BOOL
    & was_served : admittees * NATURAL +-> BOOL
    & eaten_dish : admittees * NATURAL +-> POW(NATURAL)
INITIALISATION
    admittees := 1..3
    || prohibitions := {(1 |-> {1}),(2 |-> {2, 3}),(3 |-> {})}
    || time_fifths_of_day := 0
    || has_eaten := {}
    || was_served := {}
    || eaten_dish := {}
OPERATIONS
was_fed <-- has_eaten_at(admittee, time) =
    PRE admittee : admittees
        & time : NATURAL
        & time < time_fifths_of_day
        & admittee |-> time : dom(has_eaten)
    THEN was_fed := has_eaten(admittee, time)
    END
    
END
