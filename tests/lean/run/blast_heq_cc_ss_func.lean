universes l1 l2 l3 l4 l5 l6
constants (A : Type.{l1}) (B : A → Type.{l2}) (C : ∀ (a : A) (ba : B a), Type.{l3}) 
          (D : ∀ (a : A) (ba : B a) (cba : C a ba), Type.{l4})
          (E : ∀ (a : A) (ba : B a) (cba : C a ba) (dcba : D a ba cba), Type.{l5})
          (F : ∀ (a : A) (ba : B a) (cba : C a ba) (dcba : D a ba cba) (edcba : E a ba cba dcba), Type.{l6})
          (C_ss : ∀ a ba, subsingleton (C a ba))
          (a1 a2 a3 : A)
          (mk_B1 mk_B2 : ∀ a, B a)
          (mk_C1 mk_C2 : ∀ {a} ba, C a ba)

          (tr_B : ∀ {a}, B a → B a)
          (x y z : A → A)
          
          (f f' : ∀ {a : A} {ba : B a} (cba : C a ba), D a ba cba)
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

theorem f'_congr : ∀ {a a' : A}, a == a' →
                  ∀ {b : B a} {b' : B a'}, b == b' →
                  ∀ {c : C a b} {c' : C a' b'},
                  f' c == f' c' := 
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

theorem mk_B1_congr : ∀ {a a' : A}, a == a' → mk_B1 a == mk_B1 a' :=
begin
  intro a a' Ha, have Ha' : a = a', from heq.to_eq Ha, induction Ha',
  apply heq.refl
end

theorem mk_B2_congr : ∀ {a a' : A}, a == a' → mk_B2 a == mk_B2 a' :=
begin
  intro a a' Ha, have Ha' : a = a', from heq.to_eq Ha, induction Ha',
  apply heq.refl
end

theorem tr_B_congr : ∀ {a a' : A}, a == a' → 
                     ∀ {b : B a} {b' : B a'}, b == b' →
                     tr_B b == tr_B b' := 
begin
  intro a a' Ha, have Ha' : a = a', from heq.to_eq Ha, induction Ha',
  intro b b' Hb, have Hb' : b = b', from heq.to_eq Hb, induction Hb',
  apply heq.refl
end

example : a1 == y a2 → mk_B1 a1 == mk_B1 (y a2) := 
begin
  intro Ha, 
  have Ha' : a1 = y a2, from heq.to_eq Ha, 
  rewrite Ha'
end

example : a1 == x a2 → a2 == y a1 → mk_B1 (x (y a1)) == mk_B1 (x (y (x a2))) := 
begin
  intro H1 H2,
  have H1' : a1 = x a2, from heq.to_eq H1,
  have H2' : a2 = y a1, from heq.to_eq H2,
  apply mk_B1_congr,
  rewrite H1'
end

example : a1 == y a2 → mk_B1 a1 == mk_B2 (y a2) → f (mk_C1 (mk_B2 a1)) == f (mk_C2 (mk_B1 (y a2))) := 
begin
  intro H1, have H1' : a1 = y a2, from heq.to_eq H1, rewrite H1',
  intro H2, have H2' : mk_B1 (y a2) = mk_B2 (y a2), from heq.to_eq H2, rewrite H2',
  apply f_congr, apply heq.refl, apply heq.refl
end

example : a1 == y a2 → tr_B (mk_B1 a1) == mk_B2 (y a2) → f (mk_C1 (mk_B2 a1)) == f (mk_C2 (tr_B (mk_B1 (y a2)))) := 
begin
intros,
apply f_congr,
assumption,
have H1 : mk_B2 a1 == mk_B2 (y a2), from begin rewrite (heq.to_eq a) end ,
have H2 : mk_B2 (y a2) == tr_B (mk_B1 a1), from heq.symm a_1,
have H3 : mk_B1 a1 == mk_B1 (y a2), from begin rewrite (heq.to_eq a) end,
have H4 : tr_B (mk_B1 a1) == tr_B (mk_B1 (y a2)), by apply tr_B_congr, assumption, assumption, 
apply (heq.trans H1 (heq.trans H2 H4))
end

example : a1 == y a2 → mk_B1 a1 == mk_B2 (y a2) → g (f (mk_C1 (mk_B2 a1))) == g (f (mk_C2 (mk_B1 (y a2)))) := 
begin
intro H1, have H1' : a1 = y a2, from heq.to_eq H1, rewrite H1',
intro H2, have H2' : mk_B1 (y a2) = mk_B2 (y a2), from heq.to_eq H2, rewrite H2',
apply g_congr, apply heq.refl, apply heq.refl, apply f_congr, apply heq.refl, apply heq.refl
end

example : a1 == y a2 → tr_B (mk_B1 a1) == mk_B2 (y a2) → g (f (mk_C1 (mk_B2 a1))) == g (f (mk_C2 (tr_B (mk_B1 (y a2))))) := 
begin
intro H1, have H1' : a1 = y a2, from heq.to_eq H1, rewrite -H1',
intro H2, have H2' : tr_B (mk_B1 a1) = mk_B2 a1, from heq.to_eq H2, rewrite H2',
apply g_congr, apply heq.refl, apply heq.refl, apply f_congr, apply heq.refl, apply heq.refl
end

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → mk_B1 a1 == mk_B2 (y (z (x a1))) → 
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (mk_B1 a1)) →
          g (f (mk_C1 (mk_B2 (y (z (x a1)))))) == g (f' (mk_C2 (mk_B1 a1))) := 
begin
intro H1, have H1' : a1 = y a2, from heq.to_eq H1, rewrite H1',
intro H2, have H2' : a2 = z a3, from heq.to_eq H2, rewrite H2',
intro H3, have H3' : a3 = x (y (z a3)), from heq.to_eq H3,
have H4 : y (z a3) = y (z (x (y (z a3)))), by rewrite H3' at {1}, 
intro H6 H7,
apply g_congr,
exact heq.of_eq (eq.symm H4),
exact heq.symm H6,
assumption,
end

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → mk_B1 a1 == mk_B2 (y (z (x a1))) → 
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (mk_B1 a1)) →
          f' (mk_C1 (mk_B1 a1)) == f (mk_C2 (mk_B2 (y (z (x a1))))) →
          g (f (mk_C1 (mk_B1 (y (z (x a1)))))) == g (f' (mk_C2 (mk_B2 a1))) := 
begin
intro H1, have H1' : a1 = y a2, from heq.to_eq H1, rewrite H1',
intro H2, have H2' : a2 = z a3, from heq.to_eq H2, rewrite H2',
intro H3, have H3' : a3 = x (y (z a3)), from heq.to_eq H3,
have H4 : y (z a3) = y (z (x (y (z a3)))), by rewrite H3' at {1}, 
have H5 : mk_B1 (y (z a3)) == mk_B1 (y (z (x (y (z a3))))), from begin apply mk_B1_congr, apply heq.of_eq, assumption end,
have H6 : mk_B2 (y (z a3)) == mk_B2 (y (z (x (y (z a3))))), from begin apply mk_B2_congr, apply heq.of_eq, assumption end,
intro H7 H8 H9,
apply g_congr,
exact heq.of_eq (eq.symm H4),
exact heq.trans (heq.symm H5) (heq.trans H7 (heq.symm H6)),
have H10 : f (mk_C1 (mk_B1 (y (z (x (y (z a3))))))) == f (mk_C2 (mk_B2 (y (z (x (y (z a3))))))), from
  begin apply f_congr, apply heq.refl, exact heq.trans (heq.symm H5) H7 end,
have H11 : f' (mk_C1 (mk_B1 (y (z (x (y (z a3))))))) == f' (mk_C2 (mk_B2 (y (z (x (y (z a3))))))), from
  begin apply f'_congr, apply heq.refl, exact heq.trans (heq.symm H5) H7 end,
have H12 : f' (mk_C1 (mk_B1 (y (z a3)))) == f' (mk_C2 (mk_B2 (y (z a3)))), from
  begin apply f'_congr, apply heq.of_eq, exact rfl, exact heq.trans H7 (heq.symm H6) end,
exact heq.trans H10 (heq.trans (heq.symm H9) H12)
end

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → tr_B (mk_B1 a1) == mk_B2 (y (z (x a1))) → 
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (tr_B (mk_B1 a1))) →
          f' (mk_C1 (tr_B (mk_B1 a1))) == f (mk_C2 (mk_B2 (y (z (x a1))))) →
          g (f (mk_C1 (tr_B (mk_B1 (y (z (x a1))))))) == g (f' (mk_C2 (mk_B2 a1))) := 
begin
intro H1, have H1' : a1 = y a2, from heq.to_eq H1, rewrite H1',
intro H2, have H2' : a2 = z a3, from heq.to_eq H2, rewrite H2',
intro H3, have H3' : a3 = x (y (z a3)), from heq.to_eq H3,
have H4 : y (z a3) = y (z (x (y (z a3)))), by rewrite H3' at {1}, 
have H5 : tr_B (mk_B1 (y (z a3))) == tr_B (mk_B1 (y (z (x (y (z a3)))))), from 
  begin apply tr_B_congr, apply heq.of_eq, assumption, apply mk_B1_congr, apply heq.of_eq, assumption end,
have H6 : mk_B2 (y (z a3)) == mk_B2 (y (z (x (y (z a3))))), from begin apply mk_B2_congr, apply heq.of_eq, assumption end,
intro H7 H8 H9,
apply g_congr,
exact heq.of_eq (eq.symm H4),
exact heq.trans (heq.symm H5) (heq.trans H7 (heq.symm H6)),
have H10 : f (mk_C1 (tr_B (mk_B1 (y (z (x (y (z a3)))))))) == f (mk_C2 (mk_B2 (y (z (x (y (z a3))))))), from
  begin apply f_congr, apply heq.refl, exact heq.trans (heq.symm H5) H7 end,
have H11 : f' (mk_C1 (tr_B (mk_B1 (y (z (x (y (z a3)))))))) == f' (mk_C2 (mk_B2 (y (z (x (y (z a3))))))), from
  begin apply f'_congr, apply heq.refl, exact heq.trans (heq.symm H5) H7 end,
have H12 : f' (mk_C1 (tr_B (mk_B1 (y (z a3))))) == f' (mk_C2 (mk_B2 (y (z a3)))), from
  begin apply f'_congr, apply heq.of_eq, exact rfl, exact heq.trans H7 (heq.symm H6) end,
exact heq.trans H10 (heq.trans (heq.symm H9) H12)
end

