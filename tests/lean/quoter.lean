import data.reflection

print num
print pos_num
eval quote (λ x, x)
eval quote (λ A (x : A), x)
eval quote (λ x, nat.succ x)
eval quote ((λ x, x) nat.zero)
