-- Excerpts from "Term Rewriting and All That" Chapter 2
definition relation [reducible] (A : Type) := A → A → Prop
namespace churchrosser

variables {A : Type} (R : relation A)

inductive tc : A → A → Prop :=
| step  : ∀{a b}, R a b → tc a b
| trans : ∀{a b c}, R a b → tc b c → tc a c

inductive rtc : A → A → Prop :=
| base  : ∀a, rtc a a
| step  : ∀{a b}, R a b → rtc a b
| trans : ∀{a b c}, R a b → rtc b c → rtc a c

inductive rstc : A → A → Prop :=
| base  : ∀a, rstc a a
| step1  : ∀{a b}, R a b → rstc a b
| step2  : ∀{a b}, R b a → rstc a b
| trans1 : ∀{a b c}, R a b → rstc b c → rstc a c
| trans2 : ∀a b c, R b a → rstc b c → rstc a c

lemma tc_of_rtc : subrelation (rtc R) (tc R) := by blast
lemma rtc_of_rstc [backward] : subrelation (rstc R) (rtc R) := by blast
lemma tc_of_rstc : subrelation (rstc R) (tc R) := by blast

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
    blast,
    blast,
    induction v_0,
      eapply exists.intro a_3,
        have rtc R b a_3, by blast,
        have rtc R a a_3, from rtc.trans a_1 this,
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
end

end churchrosser
