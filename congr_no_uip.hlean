/-
Note: I will ignore flexible functions and currying for now.
-----------------

Suppose:

1. we only accept asserted equalities of the following form:

For [e : f a1 ... aN] and [e' : f a1' ... aN'],
[eq.rec_on HN (eq.rec_on ... (eq.rec_on H1 e)...) = e']

where [H1 : a1 = a1', ..., HN : eq.rec_on H{n-1} (... (eq.rec_on H1 aN)...) = aN'
(refl-prefixes ok)

2. whenever such an equality is asserted, we merge the equivalence classes of [e] and [e']
(and the classes of every argument as necessary)

3. whenever we have [f a1 ... aN] and [f a1' ... aN'] and all pairs are in the same
equivalence class, we assert the generic non-UIP congruence lemma for
[f a1 ... aN] and [f a1' ... aN'].

Claim:

Whenever we merge [e] and [e'], we can produce a proof that
[eq.rec_on HN (eq.rec_on ... (eq.rec_on H1 e)...) = e'] for _some_ H1, ..., HN
for every pair in the new equivalence class.

Proof:

It suffices to show that we can construct the appropriate [symmetry]
and [transitivity] lemmas for the family. It would require an inductive argument to
prove, but the recipe is straightforward:
-/

-- 1. Type-specific symmetry results
-- example 1: congr_symm(Π (A : Type), (B : A → Type))
definition congr_symm₁ {A : Type} {B : A → Type} :
            ∀ {a₁ a₂ : A} {Ha12 : a₁ = a₂}
              {b₁ : B a₁} {b₂ : B a₂},
              eq.rec_on Ha12 b₁ = b₂ → eq.rec_on (eq.symm Ha12) b₂ = b₁ :=
begin
intros a1 a2 Ha12, induction Ha12,
intros b1 b2 Hb12, induction Hb12,
esimp
end

-- example2: congr_symm(Π (A : Type) (B : A → Type), (C : Π a, B a → Type))
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
-- congr_trans(Π (A : Type) (B : A → Type))
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

-- Example: congr_trans(Π (A : Type) (B : A → Type) (C : Π a, B a → Type))
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











Invariant: `e : f a1 ... aN` and `e' : f a1' ... aN'` are in the
same equivalence class (denoted [He : e ~ e']) provided

1. [H1 : a1 ~ a1', ..., HN : aN ~ aN'], and
2. `He` is [eq.rec_on HN (... (eq.rec_on H1 e)) = e'].

Note that (1) & (2) together imply that the types are in the
same equivalence class as well, given the generic congruence lemma.


Then whenever we merge two equivalence classes with a new proof of the form
[eq.rec_on HN (... (eq.rec_on H1 e)) = e'],
we can produce theorems of this form for every pair of elements
in the merged class, using the following family of synthesized lemmas:
-/


-- Remark: we simply would not accept any asserted equality that is not of the form (upto a prefix of `refl`s).
