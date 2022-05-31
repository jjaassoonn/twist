import ring_theory.graded_algebra.basic
import ring_theory.graded_algebra.homogeneous_ideal

namespace graded_algebra

variables {R A : Type*}
variables [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ℕ → submodule R A) [graded_algebra 𝓐]

open_locale direct_sum big_operators

def nat_to_int : ℤ → submodule R A
| (int.of_nat n) := 𝓐 n
| (int.neg_succ_of_nat n) := ⊥

namespace nat_to_int

instance (n : ℕ) : unique (nat_to_int 𝓐 (int.neg_succ_of_nat n)) :=
{ default := 0,
  uniq := λ ⟨a, ha⟩, begin
    change a ∈ ⊥ at ha,
    simpa only [submodule.mem_bot, submodule.mk_eq_zero] using ha,
  end }

lemma supr_eq_top : (⨆ i, nat_to_int 𝓐 i) = ⊤ :=
have m : ∀ x, x ∈ supr 𝓐,
from λ x, (graded_algebra.is_internal 𝓐).submodule_supr_eq_top.symm ▸ submodule.mem_top,
begin
  ext a,
  split; intros ha,
  { trivial },
  { refine submodule.supr_induction 𝓐 (m a) (λ n x hx, _) _ _,
    { rw submodule.supr_eq_span,
      apply submodule.subset_span,
      exact set.mem_Union.mpr ⟨int.of_nat n, hx⟩, },
    { rw submodule.supr_eq_span,
      apply submodule.subset_span,
      exact set.mem_Union.mpr ⟨0, submodule.zero_mem _⟩, },
    { intros x y hx hy,
      exact submodule.add_mem _ hx hy, }, },
end

lemma one_mem' : (1 : A) ∈ (nat_to_int 𝓐 0) :=
begin
  have triv : (0 : ℤ) = int.of_nat 0 := rfl,
  rw triv,
  change _ ∈ 𝓐 0,
  exact set_like.graded_monoid.one_mem,
end

lemma mul_mem' ⦃i j : ℤ⦄ {gi gj : A}
  (hi : gi ∈ nat_to_int 𝓐 i) (hj : gj ∈ nat_to_int 𝓐 j) :
  gi * gj ∈ nat_to_int 𝓐 (i + j) :=
begin
  cases i; cases j,
  { change _ ∈ 𝓐 i at hi,
    change _ ∈ 𝓐 j at hj,
    change _ ∈ 𝓐 (i + j),
    exact set_like.graded_monoid.mul_mem hi hj },
  { change _ ∈ ⊥ at hj,
    rw [submodule.mem_bot] at hj,
    subst hj,
    rw [mul_zero],
    exact submodule.zero_mem _ },
  { change _ ∈ ⊥ at hi,
    rw [submodule.mem_bot] at hi,
    subst hi,
    rw [zero_mul],
    exact submodule.zero_mem _ },
  { change _ ∈ ⊥ at hi,
    rw [submodule.mem_bot] at hi,
    subst hi,
    rw [zero_mul],
    exact submodule.zero_mem _ },
end

def add_hom_nat_to_int : (⨁ i, 𝓐 i) →+ (⨁ i, nat_to_int 𝓐 i) :=
{ to_fun := direct_sum.to_add_monoid begin
    rintro n,
    refine { to_fun := _, map_zero' := _, map_add' := _ },
    { intros a, refine direct_sum.of _ (int.of_nat n) _, exact a, },
    { rw [map_zero], },
    { intros a b, rw [map_add], },
  end,
  map_zero' := by rw [map_zero],
  map_add' := λ x y, begin
    dsimp only,
    rw [map_add],
  end }

def add_hom_int_to_nat : (⨁ i, nat_to_int 𝓐 i) →+ (⨁ i, 𝓐 i) :=
{ to_fun := direct_sum.to_add_monoid $ begin
    rintro n,
    cases n,
    { refine { to_fun := _, map_zero' := _, map_add' := _},
      { exact λ x, direct_sum.of _ n x, },
      { rw map_zero },
      { intros x y,
        simp [map_add] }, },
    { exact 0 },
  end,
  map_zero' := by simp only [map_zero],
  map_add' := λ x y, by simp [map_add] }

def equiv_nat_to_int : (⨁ i, 𝓐 i) ≃+ (⨁ i, nat_to_int 𝓐 i) :=
{ to_fun := add_hom_nat_to_int 𝓐,
  inv_fun := add_hom_int_to_nat 𝓐,
  left_inv := λ x, begin
    induction x using direct_sum.induction_on with i x x y hx hy,
    { simp [map_zero] },
    { simp only [add_hom_nat_to_int, add_hom_int_to_nat, add_monoid_hom.mk_coe, direct_sum.to_add_monoid_of],
      ext1 j,
      by_cases ineq1 : i = j,
      { subst ineq1,
        rw [direct_sum.of_eq_same, direct_sum.of_eq_same], },
      { rw [direct_sum.of_eq_of_ne, direct_sum.of_eq_of_ne];
        exact ineq1 }, },
    { rw [map_add, map_add, hx, hy], },
  end,
  right_inv := λ x, begin
    induction x using direct_sum.induction_on with i x x y hx hy,
    { simp [map_zero] },
    { cases i,
      { simp only [add_hom_nat_to_int, add_hom_int_to_nat, add_monoid_hom.mk_coe, direct_sum.to_add_monoid_of],
        erw [direct_sum.to_add_monoid_of], },
      { simp only [add_hom_int_to_nat, add_monoid_hom.mk_coe, direct_sum.to_add_monoid_of, add_monoid_hom.zero_apply, map_zero],
        have : x = 0,
        { have := x.2,
          change _ ∈ ⊥ at this,
          rw submodule.mem_bot at this,
          ext, },
        subst this,
        rw [map_zero], }, },
    { rw [map_add, map_add, hx, hy], },
  end,
  map_add' := λ x y, by simp [map_add] }

def decompose_to_int : A →+ ⨁ (i : ℤ), nat_to_int 𝓐 i :=
(equiv_nat_to_int 𝓐).to_add_monoid_hom.comp (graded_algebra.decompose 𝓐).to_add_equiv.to_add_monoid_hom

lemma decompose_to_int_apply_of_nat (i : ℕ) (a : A) :
  decompose_to_int 𝓐 a (int.of_nat i) = graded_algebra.decompose 𝓐 a i :=
have m : ∀ x, x ∈ supr 𝓐,
from λ x, (graded_algebra.is_internal 𝓐).submodule_supr_eq_top.symm ▸ submodule.mem_top,
begin
  refine submodule.supr_induction 𝓐 (m a) _ _ _,
  { intros j x hj,
    rw [graded_algebra.decompose_of_mem 𝓐 hj, decompose_to_int],
    simp only [add_monoid_hom.coe_comp, function.comp_app],
    erw [graded_algebra.decompose_of_mem 𝓐 hj],
    simp only [equiv_nat_to_int, add_hom_nat_to_int, add_monoid_hom.mk_coe],
    erw [direct_sum.to_add_monoid_of],
    by_cases ineq : i = j,
    { subst ineq,
      erw [direct_sum.of_eq_same, direct_sum.of_eq_same], },
    { erw [direct_sum.of_eq_of_ne _ _ _ _ (ne.symm ineq), direct_sum.of_eq_of_ne],
      contrapose! ineq,
      subst ineq, }, },
    { simp only [map_zero, direct_sum.zero_apply], },
    { intros x y hx hy,
      rw [map_add, map_add, direct_sum.add_apply, direct_sum.add_apply, hx, hy], },
end


lemma decompose_to_int_apply_of_neg_succ_of_nat (i : ℕ) (a : A) :
  decompose_to_int 𝓐 a (int.neg_succ_of_nat i) = 0 := by simp only [eq_iff_true_of_subsingleton]

lemma decompose_to_int_of_aux (a : ⨁ i, 𝓐 i) :
  decompose_to_int 𝓐 (direct_sum.coe_add_monoid_hom 𝓐 a) = add_hom_nat_to_int 𝓐 a :=
begin
  apply_fun (equiv_nat_to_int 𝓐).symm using (equiv_nat_to_int 𝓐).symm.injective,
  change _ = (equiv_nat_to_int 𝓐).symm ((equiv_nat_to_int 𝓐) a),
  simp only [decompose_to_int, add_monoid_hom.coe_comp, add_equiv.coe_to_add_monoid_hom, add_equiv.symm_apply_apply],
  convert graded_algebra.left_inv a,
end

lemma decompose_to_int_of_mem (i : ℤ) (a : A) (h : a ∈ nat_to_int 𝓐 i) :
  decompose_to_int 𝓐 a = direct_sum.of (λ i, nat_to_int 𝓐 i) i ⟨a, h⟩ :=
begin
  have eq1 : (direct_sum.coe_add_monoid_hom 𝓐) (graded_algebra.decompose 𝓐 a) = a := graded_algebra.right_inv a,
  have : decompose_to_int 𝓐 a = decompose_to_int 𝓐 ((direct_sum.coe_add_monoid_hom 𝓐) (graded_algebra.decompose 𝓐 a)),
  { rw eq1 },
  rw [this, decompose_to_int_of_aux],
  rw [add_hom_nat_to_int],
  simp only [add_monoid_hom.mk_coe],
  rw direct_sum.coe_add_monoid_hom at eq1,

  cases i,
  { change _ ∈ 𝓐 _ at h,
    rw graded_algebra.decompose_of_mem 𝓐 h,
    erw direct_sum.to_add_monoid_of, },
  { change a ∈ ⊥ at h,
    rw submodule.mem_bot at h,
    simp only [h, map_zero],
    generalize_proofs h2,
    have : (⟨0, h2⟩ : {x // x ∈ nat_to_int 𝓐 -[1+ i]}) = 0,
    { ext, refl, },
    rw this,
    simp only [map_zero], },
end

lemma left_inverse' : function.left_inverse (decompose_to_int 𝓐)
  (direct_sum.coe_add_monoid_hom (nat_to_int 𝓐)) := λ x,
begin
  induction x using direct_sum.induction_on with i x x y hx hy,
  { rw [map_zero],
    ext1 i,
    simp only [decompose, function.comp_app, map_zero, direct_sum.zero_apply], },
  { erw [direct_sum.coe_add_monoid_hom_of],
    cases i,
    { ext1 j,
      by_cases ineq : int.of_nat i = j,
      { subst ineq,
        erw [decompose_to_int_apply_of_nat, graded_algebra.decompose_of_mem 𝓐 x.2, direct_sum.of_eq_same, direct_sum.of_eq_same],
        ext,
        refl, },
      { cases j,
        { have ineq2 : i ≠ j,
          { contrapose! ineq, exact ineq },
          erw [decompose_to_int_apply_of_nat, direct_sum.of_eq_of_ne _ _ _ _ ineq],
          have := graded_algebra.decompose_of_mem_ne 𝓐 x.2 ineq2,
          simpa only [subtype.val_eq_coe, decompose_coe, submodule.coe_eq_zero] using this, },
        { simp only [eq_iff_true_of_subsingleton], }, }, },
    { have := x.2,
      change _ ∈ ⊥ at this,
      rw submodule.mem_bot at this,
      have eqz : x = 0,
      { ext, },
      change ↑x = _ at this,
      rw [this, eqz],
      simp only [map_zero], }, },
  { rw [map_add, map_add, hx, hy], },
end

lemma right_inverse' : function.right_inverse (decompose_to_int 𝓐)
  (direct_sum.coe_add_monoid_hom (nat_to_int 𝓐)) := λ a,
have m : ∀ x, x ∈ supr (nat_to_int 𝓐), from λ x, by rw [supr_eq_top 𝓐]; trivial,
begin
  refine submodule.supr_induction (nat_to_int 𝓐) (m a) _ _ _,
  { intros i a hi,
    rw [decompose_to_int_of_mem 𝓐 i a hi, direct_sum.coe_add_monoid_hom_of],
    refl, },
  { simp [map_zero] },
  { intros x y hx hy,
    rw [map_add, map_add, hx, hy], },
end

section

variable [Π (i : ℕ) (x : 𝓐 i), decidable (x ≠ 0)]

instance : graded_algebra (nat_to_int 𝓐) :=
{ one_mem := nat_to_int.one_mem' _,
  mul_mem := nat_to_int.mul_mem' _,
  decompose' := nat_to_int.decompose_to_int _,
  left_inv := nat_to_int.left_inverse' _,
  right_inv := nat_to_int.right_inverse' _, }

lemma decompose_eq (a : A) :
  graded_algebra.decompose (nat_to_int 𝓐) a = decompose_to_int 𝓐 a := rfl

lemma ideal.is_homogeneous_int_iff_is_homogeneous_nat (I : ideal A) :
  I.is_homogeneous (nat_to_int 𝓐) ↔ I.is_homogeneous 𝓐 :=
{ mp := λ hI i a ha, begin
    specialize hI (int.of_nat i) ha,
    convert hI,
    rw [decompose_eq, decompose_to_int_apply_of_nat],
  end,
  mpr := λ hI i a ha, begin
    cases i,
    { specialize hI i ha,
      convert hI,
      rw [decompose_eq, decompose_to_int_apply_of_nat], },
    { rw [decompose_eq, decompose_to_int_apply_of_neg_succ_of_nat, submodule.coe_zero],
      exact submodule.zero_mem _, },
  end }

end

end nat_to_int

end graded_algebra