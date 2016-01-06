universes l1 l2 l3
constants (A : Type.{l1}) (P : A → Type.{l2}) (P_ss : ∀ a, subsingleton (P a))
attribute P_ss [instance]
constants (Q : ∀ a, P a → Type.{l3}) (Q_ss : ∀ a (pa : P a), subsingleton (Q a pa))
attribute Q_ss [instance]
constant g (a : A) (pa : P a) : Q a pa → Prop
#congr_simp g
