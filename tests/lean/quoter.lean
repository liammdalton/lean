import data.reflection

eval quote (λ x, x) -- lambdas, variables, metavariables
eval quote (λ x, nat.succ x)
eval quote ((λ x, x) nat.zero)
