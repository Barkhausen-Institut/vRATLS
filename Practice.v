(** Practice to learn Coq **)

(*Data type is defined like the following*)
Inductive day : Type :=
    | monday   : day
    | tuesday  : day
    | wednesday: day
    | thursday : day
    | friday   : day
    | saturday : day
    | sunday   : day.

(*The Function on days are defined like the following*)
Definition next_weekday (d:day) : day := 
    match d with 
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
end.




