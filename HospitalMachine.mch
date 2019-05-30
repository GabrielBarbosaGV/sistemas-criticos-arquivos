/* HospitalMachine
 * Author: Gabriel
 * Creation date: 26/05/2019
 */
MACHINE
    HospitalMachine
SETS
    INGREDIENTS;
    PATIENTS
CONSTANTS
    MIN_AMOUNT_FOOD,
    MAX_AMOUNT_FOOD
PROPERTIES
    MIN_AMOUNT_FOOD : NATURAL
    & MAX_AMOUNT_FOOD : NATURAL
    & MIN_AMOUNT_FOOD = 0
    & MAX_AMOUNT_FOOD = 5
    & card(PATIENTS) > 0
    & card(INGREDIENTS) > 0
VARIABLES
    admittees,
    prohibitions,
    time_fifths_of_day,
    was_served,
    has_eaten,
    eaten_dish
INVARIANT
    admittees <: PATIENTS
    & prohibitions : admittees --> POW(INGREDIENTS)
    & time_fifths_of_day : NATURAL
    & has_eaten : admittees * NATURAL +-> MIN_AMOUNT_FOOD..MAX_AMOUNT_FOOD
    & was_served : admittees * NATURAL +-> BOOL
    & eaten_dish : admittees * NATURAL +-> POW(NATURAL)
INITIALISATION
    admittees := {}
    || prohibitions := admittees * {}
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
    END;

feed(admittee, dish, amount) =
    PRE admittee : admittees
        & dish <: INGREDIENTS
        & dish /\ prohibitions(admittee) = {}
        & amount : NATURAL
        & amount >= MIN_AMOUNT_FOOD
        & amount <= MAX_AMOUNT_FOOD
    THEN has_eaten(admittee, time_fifths_of_day) := amount
    END
END