import ring_theory.graded_algebra.basic
import module_localisation.basic

section graded_module

open_locale direct_sum big_operators

variables {ι R A : Type*}
variables [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → submodule R A) [graded_algebra 𝓐]
variables {M : Type*} [add_comm_monoid M] [module A M]
variables (𝓜 : ι → add_submonoid M)

class graded_module :=
(decompose' : M → ⨁ i, 𝓜 i)
(left_inv : function.left_inverse decompose' (direct_sum.coe_add_monoid_hom 𝓜))
(right_inv : function.right_inverse decompose' (direct_sum.coe_add_monoid_hom 𝓜))
(smul_mem : ∀ ⦃i j : ι⦄ {a : A} {m : M} (hi : a ∈ 𝓐 i) (hj : m ∈ 𝓜 j), a • m ∈ 𝓜 (i + j))

namespace graded_module

variables [graded_module 𝓐 𝓜]

protected lemma is_internal : direct_sum.is_internal 𝓜 :=
{ left := (@graded_module.left_inv ι R A _ _ _ _ _ 𝓐 _ M _ _ 𝓜 _).injective,
  right := (@graded_module.right_inv ι R A _ _ _ _ _ 𝓐 _ M _ _ 𝓜 _).surjective }

def decompose : M ≃+ ⨁ i, 𝓜 i := add_equiv.symm
{ to_fun := direct_sum.coe_add_monoid_hom 𝓜,
  inv_fun := graded_module.decompose' 𝓐,
  left_inv := graded_module.left_inv,
  right_inv := graded_module.right_inv,
  map_add' := λ x y, by rw map_add }

instance self : @graded_module ι R A _ _ _ _ _ 𝓐 _ A _ _ (λ i, (𝓐 i).to_add_submonoid) :=
{ decompose' := graded_algebra.decompose 𝓐,
  left_inv := graded_algebra.left_inv,
  right_inv := graded_algebra.right_inv,
  smul_mem := λ i j x y hi hj, set_like.graded_monoid.mul_mem hi hj }

end graded_module

end graded_module