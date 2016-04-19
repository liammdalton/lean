import data.list
open sum

namespace lean
  definition name := list (string + num)

  namespace syntax
    inductive level : Type₁ :=
    | meta   : name → level
    | zero   : level
    | succ   : level → level
    | max    : level → level → level
    | imax   : level → level → level
    | param  : name → level
    | global : name → level

    inductive expr : Type₁ :=
    | var   : ℕ → expr
    | const : name  → list level → expr
    | loc   : name  → expr → expr
    | meta  : name  → expr → expr
    | sort  : level → expr
    | pi    : name  → expr → expr → expr
    | lam   : name  → expr → expr → expr
    | app   : expr  → expr → expr
    | elet  : name  → expr → expr → expr → expr
  end syntax
end lean
