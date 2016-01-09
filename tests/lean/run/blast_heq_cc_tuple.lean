import data.tuple
open tuple function

-- TODO tag commented lemmas for instantiation if necessary

universes l1 l2 l3
constants {A : Type.{l1}} (a b c : A) (f g : A → A)
          (m n p q : ℕ)
          (xs : tuple A m) (ys : tuple A n) (zs : tuple A p) (ws : tuple A q)
          {B : Type.{l2}} (h1 h2 : A → B)
          {C : Type.{l3}} (k1 k2 : B → C)

example : a = b → xs == ys → cons a xs == cons b ys := by blast
example : a = b → b = c → xs == ys → cons a xs == cons c ys := by blast
example : a = b → b = c → xs == ys → ys == zs → cons a (cons b xs) == cons c (cons a zs) := by blast
example : a = b → b = c → xs == ys → ys == zs → cons (f a) (cons (g b) xs) == cons (f c) (cons (g a) zs) := by blast

example : xs == ys → xs ++ zs == ys ++ zs := by blast
example : xs == ys → zs == ws → xs ++ zs == ys ++ ws := by blast

-- theorem append_nil_left_heq {n : nat} (v : tuple A n) : nil ++ v == v :=
example : xs == ys → nil ++ xs == ys := by blast

-- theorem append.assoc_heq {n₁ n₂ n₃} (v₁ : tuple A n₁) (v₂ : tuple A n₂) (v₃ : tuple A n₃) : (v₁ ++ v₂) ++ v₃ == v₁ ++ (v₂ ++ v₃)
example : xs ++ ys == zs → zs ++ ws == xs ++ (ys ++ ws) := by blast
example : xs == ys → zs == ws → xs ++ ys == zs → ws ++ ws == ys ++ xs ++ xs ++ ys := by blast

-- theorem reverse_reverse {n : nat} (v : tuple A n) : reverse (reverse v) = v
example : xs == reverse ys → ys == reverse zs → xs == zs := by blast

-- theorem map_cons {n : nat} (f : A → B) (a : A) (v : tuple A n) : map f (a::v) = f a :: map f v
example : xs == ys → f = g → a = b → map f (a::xs) == g b :: map g ys := by blast

-- theorem map_map {n : nat} (g : B → C) (f : A → B) (v : tuple A n) : map g (map f v) = map (g ∘ f) v
example : m = n → xs == ys → h1 = h2 → k1 = k2 → map k1 (map h1 xs) == map (k2 ∘ h2) ys := by blast

-- lemma ith_succ_eq_ith_tail {n : nat} (v : tuple A (nat.succ n)) (i : fin n) : ith v (succ i) = ith (tail v) i
example : ∀ (xs : tuple A (nat.succ m)) (ys : tuple A (nat.succ n))
            (i : fin m) (j : fin n),
            m = n → i == j → xs == ys → ith xs (fin.succ i) == ith (tail ys) j := by blast

