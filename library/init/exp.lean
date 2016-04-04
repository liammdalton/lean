inductive name :=
| nil : name
| cons : string → name → name

inductive level :=
| lvar : name → level
| gvar : name → level
| zero : level
| suc : level → level
| max : level → level → level
| imax : level → level → level

inductive expr :=
| const : name → expr
| bvar  : ℕ → expr
| sort  : level → expr
| pi    : expr  → expr → expr
| lam   : expr  → expr → expr
| app   : expr  → expr → expr
