universes l1 l2 l3 l4 l5 l6
constants (A : Type.{l1}) (B : A → Type.{l2}) (C : ∀ (a : A) (ba : B a), Type.{l3}) 
          (D : ∀ (a : A) (ba : B a) (cba : C a ba), Type.{l4})
          (E : ∀ (a : A) (ba : B a) (cba : C a ba) (dcba : D a ba cba), Type.{l5})
          (F : ∀ (a : A) (ba : B a) (cba : C a ba) (dcba : D a ba cba) (edcba : E a ba cba dcba), Type.{l6})
          (C_ss : ∀ a ba, subsingleton (C a ba))
          (a1 a2 a3 : A)
          (b11 b12 : B a1) (b21 b22 : B a2) (b31 b32 : B a3)
          (c11 : C a1 b11) (c12 : C a1 b12)
          (c21 : C a2 b21) (c22 : C a2 b22)
          (c31 : C a3 b31) (c32 : C a3 b32)
          
          (f : ∀ {a : A} {ba : B a} (cba : C a ba), D a ba cba)
          (g : ∀ {a : A} {ba : B a} {cba : C a ba} (dcba : D a ba cba), E a ba cba dcba)
          (h : ∀ {a : A} {ba : B a} {cba : C a ba} {dcba : D a ba cba} (edcba : E a ba cba dcba), F a ba cba dcba edcba)

attribute C_ss [instance]

theorem f_congr : ∀ {a a' : A}, a == a' →
                  ∀ {b : B a} {b' : B a'}, b == b' →
                  ∀ {c : C a b} {c' : C a' b'},
                  f c == f c' := 
begin
  intro a a' Ha, 
  have Ha' : a = a', from heq.to_eq Ha,
  induction Ha',
  intro b b' Hb,
  have Hb' : b = b', from heq.to_eq Hb,
  induction Hb',
  intro c c',
  have Hc' : c = c', from subsingleton.elim c c',
  induction Hc',
  apply heq.refl
end

theorem g_congr : ∀ {a a' : A}, a == a' →
                  ∀ {b : B a} {b' : B a'}, b == b' →
                  ∀ {c : C a b} {c' : C a' b'},
                  ∀ {d : D a b c} {d' : D a' b' c'}, d == d' →
                  g d == g d' :=
begin
  intro a a' Ha, 
  have Ha' : a = a', from heq.to_eq Ha,
  induction Ha',
  intro b b' Hb,
  have Hb' : b = b', from heq.to_eq Hb,
  induction Hb',
  intro c c',
  have Hc' : c = c', from subsingleton.elim c c',
  induction Hc',
  intro d d' Hd,
  have Hd' : d = d', from heq.to_eq Hd,
  induction Hd',
  apply heq.refl
end

theorem h_congr : ∀ {a a' : A}, a == a' →
                  ∀ {b : B a} {b' : B a'}, b == b' →
                  ∀ {c : C a b} {c' : C a' b'},
                  ∀ {d : D a b c} {d' : D a' b' c'}, d == d' →
                  ∀ {e : E a b c d} {e' : E a' b' c' d'}, e == e' →
                  h e == h e' :=

begin
  intro a a' Ha, 
  have Ha' : a = a', from heq.to_eq Ha,
  induction Ha',
  intro b b' Hb,
  have Hb' : b = b', from heq.to_eq Hb,
  induction Hb',
  intro c c',
  have Hc' : c = c', from subsingleton.elim c c',
  induction Hc',
  intro d d' Hd,
  have Hd' : d = d', from heq.to_eq Hd,
  induction Hd',
 intro e e' He,
  have He' : e = e', from heq.to_eq He,
  induction He',
  apply heq.refl
end

example : a1 = a2 → b11 == b21 → f c11 == f c21 := 
  begin intros, apply f_congr, apply heq.of_eq a, assumption end

example : a1 = a2 → a2 = a3 →
          b11 = b12 → b12 == b21 → b21 = b22 → b22 == b31 → b31 = b32 →
          f c11 == f c32 := 
  begin intros, apply f_congr, apply heq.of_eq (eq.trans a a_1), 
        exact heq.trans (heq.of_eq a_2) (heq.trans a_3 (heq.trans (heq.of_eq a_4) (heq.trans a_5 (heq.of_eq a_6))))
  end

example : a1 = a2 → b11 == b21 → g (f c11) == g (f c21) := 
begin
  intros, apply g_congr, apply heq.of_eq a, assumption, apply f_congr, 
  apply heq.of_eq a, assumption
end

example : a1 = a2 → a2 = a3 →
          b11 = b12 → b12 == b21 → b21 = b22 → b22 == b31 → b31 = b32 →
          g (f c11) == g (f c32) := 
begin
  intros, apply g_congr, exact heq.of_eq (eq.trans a a_1),
  exact heq.trans (heq.of_eq a_2) (heq.trans a_3 (heq.trans (heq.of_eq a_4) (heq.trans a_5 (heq.of_eq a_6)))),
  apply f_congr,
  exact heq.of_eq (eq.trans a a_1),
  exact heq.trans (heq.of_eq a_2) (heq.trans a_3 (heq.trans (heq.of_eq a_4) (heq.trans a_5 (heq.of_eq a_6))))
end

example : a1 = a2 → b11 == b21 → h (g (f c11)) == h (g (f c21)) := 
begin
intros Ha' Hb,
have Ha : a1 == a2, from heq.of_eq Ha',
have Hf : f c11 == f c21, from f_congr Ha Hb,
have Hg : g (f c11) == g (f c21), from g_congr Ha Hb Hf,
exact h_congr Ha Hb Hf Hg
end

example : a1 == a2 → a2 == a3 →
          b11 == b12 → b12 == b21 → b21 == b22 → b22 == b31 → b31 == b32 →
          h (g (f c11)) == h (g (f c32)) := 
begin
intros H1 H2 G1 G2 G3 G4 G5,
have Ha : a1 == a3, from heq.trans H1 H2,
have Hb : b11 == b32, from heq.trans G1 (heq.trans G2 (heq.trans G3 (heq.trans G4 G5))),
have Hf : f c11 == f c32, from f_congr Ha Hb,
have Hg : g (f c11) == g (f c32), from g_congr Ha Hb Hf,
exact h_congr Ha Hb Hf Hg
end





