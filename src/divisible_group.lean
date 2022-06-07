import algebra.category.Group
import category_theory.preadditive.injective
import group_theory.subgroup.pointwise
import tactic

namespace add_comm_group

open_locale pointwise

variables (A : Type*) [add_comm_group A]

class divisible : Prop :=
(div : ∀ (n : ℕ), 0 < n → n • (⊤ : add_subgroup A) = ⊤)


instance : divisible ℚ :=
{ div := λ n hn, add_subgroup.ext $ λ q, 
  { mp := λ _, trivial,
    mpr := λ _, ⟨q/n, trivial, by norm_num; rw [div_eq_mul_inv, mul_comm q, ←mul_assoc, mul_inv_cancel (by norm_cast; linarith : (n : ℚ) ≠ 0), one_mul]⟩ } }

lemma injective_of_divisible [divisible A] :
  category_theory.injective (AddCommGroup.of A) :=
{ factors := λ X Y g f m, _ }

lemma divisible_iff_injective :
  divisible A ↔ category_theory.injective (AddCommGroup.of A) := sorry

end add_comm_group