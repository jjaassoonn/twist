import algebra.direct_sum.basic

namespace direct_sum

universes u v w u₁

variables (ι : Type v) [decidable_eq ι] (β : ι → Type w)
variables [Π (i : ι), add_comm_monoid (β i)]

lemma of_congr {i j : ι} (h : i = j) (x : β i) (y : β j) (h' : y = (by rw h at x; exact x : β j)) :
  of β i x = of β j y := 
begin
  subst h,
  subst h',
  refl,
end

end direct_sum