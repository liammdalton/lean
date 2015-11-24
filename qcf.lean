/-
Batch 1: only cases that can be handled by simple matching
===================

Example 1: we do not instantiate even if we do not know

foo : ∀ x, P x
{ a }
{ P a } { true } { false }

falsify(∀ x, P x)
locals: [(l_x : A)]

falsify(P l_x)
constraints: [P l_x ↔ false]

P l_x =?= P a
l_x =?= a -- INFEASIBLE (P a ↔ false)

Comment: the frozen strategy seems to make less sense for iff when we know there can only be two partitions in the end.

-----

Example 2: simplest example that instantiates

foo : ∀ x, P x
{ a }
{ P a, false } { true }

falsify(∀ x, P x)
locals: [(l_x : A)]

falsify(P l_x)
constraints: [P l_x ↔ false]

P l_x =?= P a
l_x =?= a

assignment: { l_x ← a }
result: foo a

-----

Example 3: non-Prop implication does not instantiate

foo : A → false
{ a }

falsify(A → false)
ignore: (l_x : A)

falsify(false)

constraints: [false ↔ false]

assignment: { }

Comment: we do not instantiate even though we succeeded in falsifying, and even though our unit module will not instantiate either since the antecedent is not a prop.

------

Example 4: vanilla shuffling

foo : ∀ (x : A), P x → ∀ (y : B), Q y → R x y
{ a } { b }
{ P a, Q b, true} { R a b, false }

locals: [(l_x : A), (l_y : B)]

assignment: { l_x ← a , l_y ← b }
skipped: [(l_P : P l_x), (l_Q : Q l_y)]
result: λ l_P l_Q, foo a l_P b l_Q

comment: we instantiate foo with locals for all the skipped arguments, and then abstract them at the end.

------

Example 5: basic type classes

foo : ∀ {A : Type} [s : monoid A] (a : A), @eq A (@mul A (@monoid.to.has_mul A s) (@one A (@monoid.to_has_one A s)) a) a

{ X } { t } { x } { @one X (@monoid.to_has_one X t) }
{ mul A (@monoid.to.has_mul A s) (@one A (@monoid.to_has_one A s)) a }

comment: everything gets assigned, the result is M-feasible, and so we instantiate in the obvious way.
also, nothing is skipped -- do we just use the assigned type class instances in this case?

------

Conjecture for approach:
1. Always a create a local whenever we hit a Pi. Falsify whenever it is a Prop (or some subset of Props?).
2. Check which ones are assigned at the end, and use the app-builder to apply foo to the assignments when they exist, or else the original locals when there is no assignment.
3. If the app-builder succeeds, abstract the locals with no assignments.
4. The result might not be type correct. Do we need to check at the end? Or do I do more bookkeeping before and reject cases earlier so that I know the result is type correct at this stage?
-/
