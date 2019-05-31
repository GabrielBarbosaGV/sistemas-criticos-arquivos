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
    amount_eaten,
    eaten_dish,
    time_of_admission
INVARIANT
    admittees <: PATIENTS
    & prohibitions : admittees --> POW(INGREDIENTS)
    & time_fifths_of_day : NATURAL
    & amount_eaten : admittees * NATURAL +-> MIN_AMOUNT_FOOD..MAX_AMOUNT_FOOD
    & eaten_dish : admittees * NATURAL +-> POW(INGREDIENTS)
    & time_of_admission : admittees +-> NATURAL
INITIALISATION
    admittees := {}
    || prohibitions := {} * {}
    || time_fifths_of_day := 0
    || amount_eaten := {}
    || eaten_dish := {}
    || time_of_admission := {}
OPERATIONS
was_fed <-- amount_eaten_at(admittee, time) =
    PRE admittee : admittees
        & time : NATURAL
        & time < time_fifths_of_day
        & admittee |-> time : dom(amount_eaten)
    THEN was_fed := amount_eaten(admittee, time)
    END;

feed(admittee, dish, amount) =
    PRE admittee : admittees
        & dish <: INGREDIENTS
        & dish /= {}
        & dish /\ prohibitions(admittee) = {}
        & ((admittee, time_fifths_of_day) : dom(amount_eaten) => amount_eaten(admittee, time_fifths_of_day) = 0)
        & amount : NATURAL
        & amount >= MIN_AMOUNT_FOOD
        & amount <= MAX_AMOUNT_FOOD
        & time_of_admission(admittee) /= time_fifths_of_day
        & (((time_fifths_of_day mod 5 = 0)
                or (time_fifths_of_day mod 5 = 2)
                or (time_fifths_of_day mod 5 = 4)) => amount > 0)
    THEN IF amount > 0 THEN
            amount_eaten(admittee, time_fifths_of_day) := amount
            || eaten_dish(admittee, time_fifths_of_day) := dish
        ELSE amount_eaten(admittee, time_fifths_of_day) := amount
        END
    END;

food_history <-- get_food_history(admittee) =
    PRE admittee : admittees
        & time_fifths_of_day > 0
    THEN food_history := { admittee } * (0..(time_fifths_of_day-1)) <| eaten_dish
    END;
    
amount_history <-- get_amount_history(admittee) =
    PRE admittee : admittees
        & time_fifths_of_day > 0
    THEN amount_history := { admittee } * (0..(time_fifths_of_day-1)) <| amount_eaten
    END;
    
admit_patient(to_admit, prohibited_ingredients) =
    PRE to_admit : PATIENTS
        & to_admit /: admittees
        & prohibited_ingredients <: INGREDIENTS
    THEN admittees := admittees \/ { to_admit }
        || prohibitions(to_admit) := prohibited_ingredients
        || time_of_admission(to_admit) := time_fifths_of_day
    END;
    
discharge_patient(to_discharge) =
    PRE to_discharge : admittees
    THEN admittees := admittees - { to_discharge }
        || prohibitions := { to_discharge } <<| prohibitions
        || amount_eaten := ({ to_discharge } <| dom(amount_eaten)) <<| amount_eaten
        || eaten_dish := ({to_discharge } <| dom(eaten_dish)) <<| eaten_dish
        || time_of_admission := { to_discharge } <<| time_of_admission
    END;
    
change_prohibitions(admittee, new_prohibitions) = 
    PRE admittee : admittees
        & new_prohibitions <: INGREDIENTS
        & new_prohibitions /= prohibitions(admittee)
    THEN prohibitions(admittee) := new_prohibitions
    END;
    
pass_time =
    PRE (((time_fifths_of_day mod 5 = 0)
            or (time_fifths_of_day mod 5 = 2)
            or (time_fifths_of_day mod 5 = 4)) =>
            dom((dom(amount_eaten) |> { time_fifths_of_day })) = admittees
            & 0 /: ran(admittees * { time_fifths_of_day } <| amount_eaten))
    THEN time_fifths_of_day := time_fifths_of_day + 1
    END;
    
day <-- get_day(time_fifths) =
    PRE time_fifths : NATURAL
        & time_fifths >= 0
    THEN day := time_fifths / 5
    END;
    
month <-- get_month(days) =
    PRE days : NATURAL
        & days >= 0
    THEN month := days / 30
    END
    
END