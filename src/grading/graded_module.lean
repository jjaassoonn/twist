import ring_theory.graded_algebra.basic
import module_localisation.basic
import lemmas.about_direct_sum

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

@[simp] lemma decompose_symm_of {i : ι} (x : 𝓜 i) :
  (graded_module.decompose 𝓐 𝓜).symm (direct_sum.of _ i x) = x :=
direct_sum.coe_add_monoid_hom_of _ _ _

instance self : graded_module 𝓐 (λ i, (𝓐 i).to_add_submonoid) :=
{ decompose' := graded_algebra.decompose 𝓐,
  left_inv := graded_algebra.left_inv,
  right_inv := graded_algebra.right_inv,
  smul_mem := λ i j x y hi hj, set_like.graded_monoid.mul_mem hi hj }

@[simp] lemma decompose_coe {i : ι} (x : 𝓜 i) :
  graded_module.decompose 𝓐 𝓜 x = direct_sum.of _ i x :=
by rw [← decompose_symm_of 𝓐 𝓜, add_equiv.apply_symm_apply]

lemma decompose_of_mem {x : M} {i : ι} (hx : x ∈ 𝓜 i) :
  graded_module.decompose 𝓐 𝓜 x = direct_sum.of _ i (⟨x, hx⟩ : 𝓜 i) :=
graded_module.decompose_coe _ _ ⟨x, hx⟩

lemma decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ 𝓜 i) (hij : i ≠ j):
  (graded_module.decompose 𝓐 𝓜 x j : M) = 0 :=
by rw [graded_module.decompose_of_mem _ _ hx, direct_sum.of_eq_of_ne _ _ _ _ hij, add_submonoid.coe_zero]

def twisted_by (i : ι) : ι → add_submonoid M := λ j, 𝓜 (j + i)

end graded_module

end

namespace graded_module

open_locale direct_sum big_operators


variables {ι R A : Type*}
variables [decidable_eq ι] [add_group ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → submodule R A) [graded_algebra 𝓐]
variables {M : Type*} [add_comm_monoid M] [module A M]
variables (𝓜 : ι → add_submonoid M) [graded_module 𝓐 𝓜]

namespace twisted_by

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

lemma to_twisted_by.apply_of {k : ι} (x : 𝓜 k) :
  to_twisted_by 𝓜 i (direct_sum.of _ k x) = 
  direct_sum.of _ (k - i) begin
    refine ⟨x.1, _⟩,
    convert x.2,
    dunfold twisted_by,
    rw sub_add_cancel,
  end := by { rw [to_twisted_by, direct_sum.to_add_monoid_of], refl }

def to_untwisted : (⨁ j, twisted_by 𝓜 i j) →+ (⨁ j, 𝓜 j) :=
direct_sum.to_add_monoid $ λ j, 
{ to_fun := λ m, direct_sum.of _ (j + i) $ by exact m,
  map_zero' := by rw map_zero,
  map_add' := λ _ _, by rw map_add }

lemma to_untwisted.apply_of {k : ι} (x : twisted_by 𝓜 i k) :
  to_untwisted 𝓜 i (direct_sum.of _ k x) = 
  direct_sum.of _ (k + i) (by exact x) := by { rw [to_untwisted, direct_sum.to_add_monoid_of], refl }

lemma to_untwisted.left_inv : function.left_inverse (to_untwisted 𝓜 i) (to_twisted_by 𝓜 i) :=
begin
  intros x,
  induction x using direct_sum.induction_on with j x x y hx hy,
  { rw [map_zero, map_zero] },
  { rw [to_twisted_by.apply_of, to_untwisted.apply_of],
    apply direct_sum.of_congr,
    work_on_goal 2
    { rw sub_add_cancel, },
    { simp only [sub_add_cancel, subtype.val_eq_coe, eq_mp_eq_cast, set_coe_cast, set_like.eta], } },
  { rw [map_add, map_add, hx, hy], },
end

lemma to_untwisted.right_inv : function.right_inverse (to_untwisted 𝓜 i) (to_twisted_by 𝓜 i) :=
begin
  intros x,
  induction x using direct_sum.induction_on with j x x y hx hy,
  { rw [map_zero, map_zero] },
  { rw [to_untwisted.apply_of, to_twisted_by.apply_of],
    apply direct_sum.of_congr,
    work_on_goal 2
    { rw add_sub_cancel, },
    { simp only [add_sub_cancel, subtype.val_eq_coe, eq_mp_eq_cast, set_coe_cast, set_like.eta], } },
  { rw [map_add, map_add, hx, hy], },
end

def untwisted_equiv_twisted : (⨁ j, 𝓜 j) ≃+ (⨁ j, twisted_by 𝓜 i j) :=
{ to_fun := to_twisted_by _ _,
  inv_fun := to_untwisted _ _,
  left_inv := to_untwisted.left_inv _ _,
  right_inv := to_untwisted.right_inv _ _,
  map_add' := λ x y, by rw [map_add] }

lemma smul_mem' ⦃j k : ι⦄ {a : A} {m : M} (hj : a ∈ 𝓐 j) (hk : m ∈ (twisted_by 𝓜 i k)) :
  a • m ∈ twisted_by 𝓜 i (j + k) :=
have hm : m ∈ 𝓜 (k + i), from hk,
begin
  have := graded_module.smul_mem hj hm,
  convert this using 1,
  dunfold twisted_by,
  rw [add_assoc],
end

def decompose : M ≃+ (⨁ (j : ι), (twisted_by 𝓜 i j)) :=
  add_equiv.trans (graded_module.decompose 𝓐 𝓜) (untwisted_equiv_twisted 𝓜 i) 

protected lemma decompose_of_mem' {j : ι} {x : M} (hx : x ∈ 𝓜 (j + i)) : 
  decompose 𝓐 𝓜 i x = direct_sum.of _ j (⟨x, hx⟩ : twisted_by 𝓜 i j) := 
begin
  dunfold decompose,
  simp only [add_equiv.trans_apply],
  apply_fun (untwisted_equiv_twisted 𝓜 i).symm,
  change _ = to_untwisted 𝓜 i (direct_sum.of _ j _),
  rw [to_untwisted.apply_of, add_equiv.symm_apply_apply, graded_module.decompose_of_mem],
  work_on_goal 2 { exact hx },
  refl,
end

lemma left_inv.of (j : ι) (x : twisted_by 𝓜 i j) :
  (twisted_by.decompose 𝓐 𝓜 i)
    (direct_sum.coe_add_monoid_hom (twisted_by 𝓜 i) (direct_sum.of _ j x)) =
  direct_sum.of _ j x := 
begin
  ext1 k,
  simp only [direct_sum.coe_add_monoid_hom_of],
  rw twisted_by.decompose_of_mem' 𝓐 𝓜 i (by convert x.2 : (x : M) ∈ 𝓜 (j + i)),
  congr' 2,
  ext,
  refl,
end

lemma right_inv.mem (j : ι) (x : M) (hj : x ∈ 𝓜 j) :
  (direct_sum.coe_add_monoid_hom (twisted_by 𝓜 i)) 
    ((twisted_by.decompose 𝓐 𝓜 i) x) = x := 
begin
  rw twisted_by.decompose_of_mem',
  work_on_goal 3 { exact j - i, },
  work_on_goal 2 { convert hj, rw sub_add_cancel, },
  erw [direct_sum.coe_add_monoid_hom, direct_sum.to_add_monoid_of],
  refl,
end

end twisted_by

instance twisted_by_module (i : ι) : graded_module 𝓐 (twisted_by 𝓜 i) :=
have m : ∀ x, x ∈ supr 𝓜,
from λ x, (direct_sum.is_internal.add_submonoid_supr_eq_top _ (graded_module.is_internal 𝓐 𝓜)).symm ▸ trivial,
{ decompose' := twisted_by.decompose 𝓐 𝓜 i,
  left_inv := λ x, direct_sum.induction_on x (by simp only [map_zero]) begin
    intros j x,
    apply twisted_by.left_inv.of,
  end (λ x y hx hy, by simp only [map_add, hx, hy]),
  right_inv := λ x, add_submonoid.supr_induction 𝓜 (m x) (twisted_by.right_inv.mem 𝓐 𝓜 i) (by simp only [map_zero]) (λ _ _ hx hy, by simp only [map_add, hx, hy]),
  smul_mem := twisted_by.smul_mem' 𝓐 𝓜 i }

end graded_module
