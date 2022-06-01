import ring_theory.graded_algebra.basic
import module_localisation.basic

section

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

instance self : graded_module 𝓐 (λ i, (𝓐 i).to_add_submonoid) :=
{ decompose' := graded_algebra.decompose 𝓐,
  left_inv := graded_algebra.left_inv,
  right_inv := graded_algebra.right_inv,
  smul_mem := λ i j x y hi hj, set_like.graded_monoid.mul_mem hi hj }

def twisted_by (i : ι) : ι → add_submonoid M := λ j, 𝓜 (j + i)

end graded_module

end

namespace graded_module

open_locale direct_sum big_operators

namespace twisted_by

variables {ι R A : Type*}
variables [decidable_eq ι] [add_group ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → submodule R A) [graded_algebra 𝓐]
variables {M : Type*} [add_comm_monoid M] [module A M]
variables (𝓜 : ι → add_submonoid M) [graded_module 𝓐 𝓜]

variables (i : ι)

def to_twisted_by : (⨁ j, 𝓜 j) →+ (⨁ j, twisted_by 𝓜 i j) :=
direct_sum.to_add_monoid $ λ j, 
{ to_fun := λ m, direct_sum.of _ (j - i) begin
    refine ⟨m.1, _⟩,
    convert m.2,
    dunfold twisted_by,
    rw sub_add_cancel,
  end,
  map_zero' := begin
    generalize_proofs h,
    have : (⟨(0 : 𝓜 j), h⟩ : twisted_by 𝓜 i (j - i)) = 0,
    { ext, refl, },
    erw this,
    rw [map_zero],
  end,
  map_add' := λ x y, begin
    generalize_proofs hadd hx hy,
    have : (⟨(x + y).1, hadd⟩ : twisted_by 𝓜 i (j - i)) = ⟨x.1, hx⟩ + ⟨y.1, hy⟩,
    { ext, refl },
    erw this,
    rw [map_add],
  end }

def to_untwisted : (⨁ j, twisted_by 𝓜 i j) →+ (⨁ j, 𝓜 j) :=
direct_sum.to_add_monoid $ λ j, 
{ to_fun := λ m, direct_sum.of _ (j + i) $ by exact m,
  map_zero' := by rw map_zero,
  map_add' := λ _ _, by rw map_add }

def untwisted_equiv_twisted : (⨁ j, 𝓜 j) ≃+ (⨁ j, twisted_by 𝓜 i j) :=
{ to_fun := to_twisted_by _ _,
  inv_fun := to_untwisted _ _,
  left_inv := _,
  right_inv := _,
  map_add' := _ }

end twisted_by

instance twisted_by_module (i : ι) : graded_module 𝓐 (twisted_by 𝓜 i) :=
{ decompose' := _,
  left_inv := _,
  right_inv := _,
  smul_mem := _ }

end graded_module
