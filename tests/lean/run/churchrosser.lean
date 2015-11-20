-- Excerpts from "Term Rewriting and All That" Chapter 2
definition relation [reducible] (A : Type) := A → A → Prop
namespace churchrosser

variables {A : Type} (R : relation A)

inductive rc : A → A → Prop :=
| base : ∀ a, rc a a
| core : ∀ {a b}, R a b → rc a b

inductive sc : A → A → Prop :=
| step1 : ∀{a b}, R a b → sc a b
| step2 : ∀{a b}, R b a → sc a b

inductive tc : A → A → Prop :=
| step  : ∀{a b}, R a b → tc a b
| trans : ∀{a b c}, R a b → tc b c → tc a c

inductive rsc : A → A → Prop :=
| base : ∀ a, rsc a a
| core : ∀ {a b}, sc R a b → rsc a b

inductive rtc : A → A → Prop :=
| base  : ∀a, rtc a a
| trans : ∀{a b c}, R a b → rtc b c → rtc a c

inductive rstc : A → A → Prop :=
| base  : ∀a, rstc a a
| trans : ∀{a b c}, sc R a b → rstc b c → rstc a c

lemma tc_of_rtc : subrelation (tc R) (rtc R) := by blast
lemma rtc_of_rstc [backward] : subrelation (rtc R) (rstc R) := by blast
lemma tc_of_rstc : subrelation (tc R) (rstc R) := by blast
lemma R_of_sc [backward] : subrelation R (sc R) := by blast
lemma sc_of_rstc : subrelation (sc R) (rstc R) := by blast

lemma tc_trans [backward] : transitive (tc R) := by blast
lemma rtc_trans [backward] : transitive (rtc R) := by blast
lemma rstc_trans [backward] : transitive (rstc R) := by blast

definition reducible (x : A) := ∃ y, R x y
definition in_normal_form (x : A) := ¬ (reducible R x)
definition normal_form_of (x y : A) := tc R x y ∧ in_normal_form R y
definition direct_successor_of (x y : A) := R x y
definition successor_of (x y : A) := tc R x y
definition joinable [reducible] (x y : A) := ∃ z, rtc R x z ∧ rtc R y z

definition church_rosser := ∀ {x y : A}, rstc R x y → joinable R x y
definition confluent := ∀ {x y1 y2 : A}, rtc R x y1 → rtc R x y2 → joinable R y1 y2
definition normalizing := ∀ (x : A), ∃ y, normal_form_of R x y
definition semiconfluent [backward] := ∀ {x y1 y2 : A}, R x y1 → rtc R x y2 → joinable R y1 y2

lemma church_rosser_of_confluent : church_rosser R → confluent R := by blast
lemma confluent_of_semiconfluent : confluent R → semiconfluent R := by blast

set_option formatter.hide_full_terms false
lemma semiconfluent_of_church_rosser : semiconfluent R → church_rosser R :=
assume H_semi : semiconfluent R,
take x y : A,
assume H : rstc R x y,
begin
  induction H,
    blast,
    induction v_0,
    have rtc_b_a3 : rtc R b a_3, by blast,
      induction a_1,
        --
        have rtc_a_a3 : rtc R a a_3, from rtc.trans a_1 rtc_b_a3,
        blast,
        --
        have rtc_b_a3 : rtc R b a_3, by blast,
        have join_a_a3 : joinable R a a_3, from H_semi a_1 rtc_b_a3,
        induction join_a_a3,
        induction a_4,
--        have rtc R c a_5, from rtc.trans


--        exact (H_semi a_1 rtc_b_a3)

--        have joinable

--      have rtc R a a_3, by rtc_trans `R a b` this,
/-
        blast,
    induction v_0,
      have rtc_b_a3 : rtc R b a_3, by blast,
      have rtc_c_a3 : rtc R c a_3, by blast,
      clear a_4,
      have join_a_a3 : joinable R a a_3, from H_semi a_1 rtc_b_a3,
      unfold joinable at join_a_a3,
      unfold joinable,
      induction join_a_a3,
      eapply exists.intro a_4,
      split, blast,
      apply rtc_trans, blast, blast
-/
end

end churchrosser
