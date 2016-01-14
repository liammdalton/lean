/-
I will ignore flexible functions and currying for now.

Invariant: `e : f a1 ... aN` and `e' : f a1' ... aN'` are in the
same equivalence class (denoted [He : e ~ e']) provided

1. [H1 : a1 ~ a1', ..., HN : aN ~ aN'], and
2. `He` is [eq.rec_on HN (... (eq.rec_on H1 e)) = e'].

Note that equality can be taken as a special case where the Hi are refl.

Then whenever we merge two equivalence classes with a new proof of the form
[eq.rec_on HN (... (eq.rec_on H1 e)) = e'],
we can produce theorems of this form for every pair of elements
in the merged class, using the following family of synthesized lemmas:
-/

-- 1. Type-specific symmetry results
-- example 1: congr_symm(f : Π (A : Type) (B : A → Type), <C>)
definition congr_symm₁ {A : Type} {B : A → Type} :
            ∀ {a₁ a₂ : A} {Ha12 : a₁ = a₂}
              {b₁ : B a₁} {b₂ : B a₂},
              eq.rec_on Ha12 b₁ = b₂ → eq.rec_on (eq.symm Ha12) b₂ = b₁ :=
begin
intros a1 a2 Ha12, induction Ha12,
intros b1 b2 Hb12, induction Hb12,
esimp
end

-- example2: congr_symm(f : Π (A : Type) (B : A → Type) (C : Π a, B a → Type), <D>)
set_option pp.implicit true
definition congr_symm₂ {A : Type} {B : A → Type} {C : Π a, B a → Type} :
            ∀ {a₁ a₂ : A} {Ha12 : a₁ = a₂}
              {b₁ : B a₁} {b₂ : B a₂} {Hb12 : eq.rec_on Ha12 b₁ = b₂}
              {c₁ : C a₁ b₁} {c₂ : C a₂ b₂},
              eq.rec_on Hb12 (eq.rec_on Ha12 c₁) = c₂ →
                eq.rec_on (congr_symm₁ Hb12) (eq.rec_on (eq.symm Ha12) c₂) = c₁ :=
begin
intros a1 a2 Ha12, induction Ha12,
intros b1 b2 Hb12, induction Hb12,
intros c1 c2 Hc12, induction Hc12,
esimp
end

-- 2. Type-specific transitivity results
-- congr_trans(f : Π (A : Type) (B : A → Type), <C>)
definition congr_trans₂ {A : Type} {B : A → Type} :
            ∀ {a₁ a₂ a₃ : A} {Ha12 : a₁ = a₂} {Ha23 : a₂ = a₃}
              {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
              (Hb12 : eq.rec_on Ha12 b₁ = b₂) (Hb23 : eq.rec_on Ha23 b₂ = b₃),
              let Ha13 : a₁ = a₃ := eq.trans Ha12 Ha23 in
              eq.rec_on Ha13 b₁ = b₃ :=
begin
intros a1 a2 a3 Ha12, induction Ha12, intros Ha23, induction Ha23,
intros b1 b2 b3, intros Hb12, induction Hb12, intros Hb23, induction Hb23,
esimp
end

-- Example: congr_trans(f : Π (A : Type) (B : A → Type) (C : Π a, B a → Type), <D>)
lemma congr_trans₃ {A : Type} {B : A → Type} {C : Π a, B a → Type} :
            ∀ (a₁ a₂ a₃ : A) (Ha12 : a₁ = a₂) (Ha23 : a₂ = a₃)
              (b₁ : B a₁) (b₂ : B a₂) (b₃ : B a₃)
              (Hb12 : eq.rec_on Ha12 b₁ = b₂) (Hb23 : eq.rec_on Ha23 b₂ = b₃),
              let Ha13 : a₁ = a₃ := eq.trans Ha12 Ha23 in
              ∀ (c₁ : C a₁ b₁) (c₂ : C a₂ b₂) (c₃ : C a₃ b₃)
                (Hc12 : eq.rec_on Hb12 (eq.rec_on Ha12 c₁) = c₂)
                (hc23 : eq.rec_on Hb23 (eq.rec_on Ha23 c₂) = c₃),
                let Hb13 : eq.rec_on Ha13 b₁ = b₃ := congr_trans₂ Hb12 Hb23 in
                  eq.rec_on Hb13 (eq.rec_on Ha13 c₁) = c₃ :=
begin
intros a1 a2 a3 Ha12, induction Ha12, intro Ha23, induction Ha23,
intros b1 b2 b3 Hb12, induction Hb12, intro Hb23, induction Hb23,
intros c1 c2 c3 Hc12, induction Hc12, intro Hc23, induction Hc23,
esimp
end

/- Remark: we simply would not accept any asserted equality that is not of the form (upto a prefix of `refl`s). -/
