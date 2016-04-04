namespace lean
  inductive name :=
  | nil  : name
  | cons : string → name → name

  inductive level :=
  | zero   : level
  | succ   : level → level
  | max    : level → level → level
  | imax   : level → level → level
  | param  : name → level
  | global : name → level

  inductive expr :=
  | var   : ℕ → expr
  | const : name → expr
  | sort  : level → expr
  | pi    : name  → expr → expr → expr
  | lam   : name  → expr → expr → expr
  | app   : expr  → expr → expr
  | elet  : name  → expr → expr → expr → expr
end lean
