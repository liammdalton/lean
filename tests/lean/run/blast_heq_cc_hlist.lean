import data.hlist
open hlist

universes l1 l2 l3
constants (A : Type.{l1}) (B : A → Type.{l2})
          (a1 a2 a3 : A)
          (b11 b12 : B a1) (b21 b22 : B a2) (b31 b32 : B a3)
          (ls1 ls2 ls3 ls4 : list A)
          (xs : hlist B ls1) (ys : hlist B ls2) (zs : hlist B ls3)
          {C : A → Type.{l3}} (f1 f2 : Π ⦃a⦄, B a → C a)

example : b11 = b12 → cons b11 xs = cons b12 xs := by blast
example : b11 == b21 → cons b11 xs == cons b21 xs := by blast
example : b11 == b21 → xs == ys → cons b11 xs == cons b21 ys := by blast
example : b11 == b21 → b21 == b31 → xs == ys → ys == zs → cons b11 xs == cons b31 zs := by blast

-- lemma tail_cons : ∀ {a l} (b : B a) (h : hlist B l), tail (cons b h) = h
example : xs == ys → tail (cons b11 xs) == tail (cons b21 ys) := by blast

-- lemma eta_cons : ∀ {a l} (h : hlist B (a::l)), h = cons (head h) (tail h) :=
example : ∀ (ys : hlist B (list.cons a2 ls2)), xs == ys → xs == cons (head ys) (tail ys) := by blast

-- lemma append_nil_right_heq {l} (h : hlist B l) : append h nil == h
example : xs == append ys nil → ys == append zs nil → append xs nil == zs := by blast

-- lemma map_cons : ∀ {a l} (b : B a) (h : hlist B l), map f (cons b h) = cons (f b) (map f h)
example : f1 = f2 → 
          b11 = b12 → b12 == b21 → b21 = b22 → b22 == b31 → b31 = b32 → 
          xs == ys → ys == zs →
          map f1 (cons b11 xs) == cons (f2 b32) (map f2 zs) := by blast

