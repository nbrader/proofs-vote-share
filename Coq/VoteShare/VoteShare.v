Require Import Coq.Reals.Reals.
Require Import Psatz.
Open Scope R_scope.

Definition unit_interval_real (x : R) := 0 <= x <= 1.
Definition complement (x : R) := 1 - x.

Theorem if_half_of_pop_is_f_and_half_of_pop_voted_yes_then_f_voted_yes_is_complement_of_m_voted_yes :
    forall
        (f : R) (* Female Electorate: Fraction of electorate who are women. *)
        (m : R) (* Male Electorate: Fraction of electorate who are men. *)
        (f_voted_yes : R) (* Fraction of female Electorate who voted 'Yes'. *)
        (m_voted_yes : R) (* Fraction of male Electorate who voted 'Yes'. *)
        (pop_voted_yes : R) (* Fraction of Electorate who voted 'Yes'. *)

        (pop_voted_yes_parts : pop_voted_yes = f * f_voted_yes + m * m_voted_yes) (* By the meaning of these variables. *)
        (f_is_m_complement : f = complement m), (* Assume members are male or female. *)

    forall
        (half_of_pop_is_f : f = 0.5)
        (half_of_pop_voted_yes : pop_voted_yes = 0.5),
    
    f_voted_yes = complement m_voted_yes.
  
Proof.
    intros.
    unfold complement in *.

    assert (half_of_pop_is_m : m = 0.5) by lra.
    
    rewrite half_of_pop_is_f in *.
    rewrite half_of_pop_is_m in *.
    
    assert (m_voted_yes = 2*pop_voted_yes - f_voted_yes).
    {
        rewrite pop_voted_yes_parts.
        replace (2 * (0.5 * f_voted_yes + 0.5 * m_voted_yes) - f_voted_yes) with (f_voted_yes + m_voted_yes - f_voted_yes) by lra.
        lra.
    }

    rewrite H.
    rewrite half_of_pop_voted_yes.
    replace (1 - (2 * 0.5 - f_voted_yes)) with f_voted_yes by lra.

    reflexivity.
Qed.