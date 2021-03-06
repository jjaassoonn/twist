import ring_theory.graded_algebra.basic
import ring_theory.graded_algebra.homogeneous_ideal

namespace graded_algebra

variables {R A : Type*}
variables [comm_semiring R] [semiring A] [algebra R A]
variables (π : β β submodule R A) [graded_algebra π]

open_locale direct_sum big_operators

def nat_to_int : β€ β submodule R A
| (int.of_nat n) := π n
| (int.neg_succ_of_nat n) := β₯

namespace nat_to_int

instance (n : β) : unique (nat_to_int π (int.neg_succ_of_nat n)) :=
{ default := 0,
  uniq := Ξ» β¨a, haβ©, begin
    change a β β₯ at ha,
    simpa only [submodule.mem_bot, submodule.mk_eq_zero] using ha,
  end }

lemma supr_eq_top : (β¨ i, nat_to_int π i) = β€ :=
have m : β x, x β supr π,
from Ξ» x, (graded_algebra.is_internal π).submodule_supr_eq_top.symm βΈ submodule.mem_top,
begin
  ext a,
  split; intros ha,
  { trivial },
  { refine submodule.supr_induction π (m a) (Ξ» n x hx, _) _ _,
    { rw submodule.supr_eq_span,
      apply submodule.subset_span,
      exact set.mem_Union.mpr β¨int.of_nat n, hxβ©, },
    { rw submodule.supr_eq_span,
      apply submodule.subset_span,
      exact set.mem_Union.mpr β¨0, submodule.zero_mem _β©, },
    { intros x y hx hy,
      exact submodule.add_mem _ hx hy, }, },
end

lemma one_mem' : (1 : A) β (nat_to_int π 0) :=
begin
  have triv : (0 : β€) = int.of_nat 0 := rfl,
  rw triv,
  change _ β π 0,
  exact set_like.graded_monoid.one_mem,
end

lemma mul_mem' β¦i j : β€β¦ {gi gj : A}
  (hi : gi β nat_to_int π i) (hj : gj β nat_to_int π j) :
  gi * gj β nat_to_int π (i + j) :=
begin
  cases i; cases j,
  { change _ β π i at hi,
    change _ β π j at hj,
    change _ β π (i + j),
    exact set_like.graded_monoid.mul_mem hi hj },
  { change _ β β₯ at hj,
    rw [submodule.mem_bot] at hj,
    subst hj,
    rw [mul_zero],
    exact submodule.zero_mem _ },
  { change _ β β₯ at hi,
    rw [submodule.mem_bot] at hi,
    subst hi,
    rw [zero_mul],
    exact submodule.zero_mem _ },
  { change _ β β₯ at hi,
    rw [submodule.mem_bot] at hi,
    subst hi,
    rw [zero_mul],
    exact submodule.zero_mem _ },
end

def add_hom_nat_to_int : (β¨ i, π i) β+ (β¨ i, nat_to_int π i) :=
{ to_fun := direct_sum.to_add_monoid begin
    rintro n,
    refine { to_fun := _, map_zero' := _, map_add' := _ },
    { intros a, refine direct_sum.of _ (int.of_nat n) _, exact a, },
    { rw [map_zero], },
    { intros a b, rw [map_add], },
  end,
  map_zero' := by rw [map_zero],
  map_add' := Ξ» x y, begin
    dsimp only,
    rw [map_add],
  end }

def add_hom_int_to_nat : (β¨ i, nat_to_int π i) β+ (β¨ i, π i) :=
{ to_fun := direct_sum.to_add_monoid $ begin
    rintro n,
    cases n,
    { refine { to_fun := _, map_zero' := _, map_add' := _},
      { exact Ξ» x, direct_sum.of _ n x, },
      { rw map_zero },
      { intros x y,
        simp [map_add] }, },
    { exact 0 },
  end,
  map_zero' := by simp only [map_zero],
  map_add' := Ξ» x y, by simp [map_add] }

def equiv_nat_to_int : (β¨ i, π i) β+ (β¨ i, nat_to_int π i) :=
{ to_fun := add_hom_nat_to_int π,
  inv_fun := add_hom_int_to_nat π,
  left_inv := Ξ» x, begin
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
  right_inv := Ξ» x, begin
    induction x using direct_sum.induction_on with i x x y hx hy,
    { simp [map_zero] },
    { cases i,
      { simp only [add_hom_nat_to_int, add_hom_int_to_nat, add_monoid_hom.mk_coe, direct_sum.to_add_monoid_of],
        erw [direct_sum.to_add_monoid_of], },
      { simp only [add_hom_int_to_nat, add_monoid_hom.mk_coe, direct_sum.to_add_monoid_of, add_monoid_hom.zero_apply, map_zero],
        have : x = 0,
        { have := x.2,
          change _ β β₯ at this,
          rw submodule.mem_bot at this,
          ext, },
        subst this,
        rw [map_zero], }, },
    { rw [map_add, map_add, hx, hy], },
  end,
  map_add' := Ξ» x y, by simp [map_add] }

def decompose_to_int : A β+ β¨ (i : β€), nat_to_int π i :=
(equiv_nat_to_int π).to_add_monoid_hom.comp (graded_algebra.decompose π).to_add_equiv.to_add_monoid_hom

lemma decompose_to_int_apply_of_nat (i : β) (a : A) :
  decompose_to_int π a (int.of_nat i) = graded_algebra.decompose π a i :=
have m : β x, x β supr π,
from Ξ» x, (graded_algebra.is_internal π).submodule_supr_eq_top.symm βΈ submodule.mem_top,
begin
  refine submodule.supr_induction π (m a) _ _ _,
  { intros j x hj,
    rw [graded_algebra.decompose_of_mem π hj, decompose_to_int],
    simp only [add_monoid_hom.coe_comp, function.comp_app],
    erw [graded_algebra.decompose_of_mem π hj],
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


lemma decompose_to_int_apply_of_neg_succ_of_nat (i : β) (a : A) :
  decompose_to_int π a (int.neg_succ_of_nat i) = 0 := by simp only [eq_iff_true_of_subsingleton]

lemma decompose_to_int_of_aux (a : β¨ i, π i) :
  decompose_to_int π (direct_sum.coe_add_monoid_hom π a) = add_hom_nat_to_int π a :=
begin
  apply_fun (equiv_nat_to_int π).symm using (equiv_nat_to_int π).symm.injective,
  change _ = (equiv_nat_to_int π).symm ((equiv_nat_to_int π) a),
  simp only [decompose_to_int, add_monoid_hom.coe_comp, add_equiv.coe_to_add_monoid_hom, add_equiv.symm_apply_apply],
  convert graded_algebra.left_inv a,
end

lemma decompose_to_int_of_mem (i : β€) (a : A) (h : a β nat_to_int π i) :
  decompose_to_int π a = direct_sum.of (Ξ» i, nat_to_int π i) i β¨a, hβ© :=
begin
  have eq1 : (direct_sum.coe_add_monoid_hom π) (graded_algebra.decompose π a) = a := graded_algebra.right_inv a,
  have : decompose_to_int π a = decompose_to_int π ((direct_sum.coe_add_monoid_hom π) (graded_algebra.decompose π a)),
  { rw eq1 },
  rw [this, decompose_to_int_of_aux],
  rw [add_hom_nat_to_int],
  simp only [add_monoid_hom.mk_coe],
  rw direct_sum.coe_add_monoid_hom at eq1,

  cases i,
  { change _ β π _ at h,
    rw graded_algebra.decompose_of_mem π h,
    erw direct_sum.to_add_monoid_of, },
  { change a β β₯ at h,
    rw submodule.mem_bot at h,
    simp only [h, map_zero],
    generalize_proofs h2,
    have : (β¨0, h2β© : {x // x β nat_to_int π -[1+ i]}) = 0,
    { ext, refl, },
    rw this,
    simp only [map_zero], },
end

lemma left_inverse' : function.left_inverse (decompose_to_int π)
  (direct_sum.coe_add_monoid_hom (nat_to_int π)) := Ξ» x,
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
        erw [decompose_to_int_apply_of_nat, graded_algebra.decompose_of_mem π x.2, direct_sum.of_eq_same, direct_sum.of_eq_same],
        ext,
        refl, },
      { cases j,
        { have ineq2 : i β  j,
          { contrapose! ineq, exact ineq },
          erw [decompose_to_int_apply_of_nat, direct_sum.of_eq_of_ne _ _ _ _ ineq],
          have := graded_algebra.decompose_of_mem_ne π x.2 ineq2,
          simpa only [subtype.val_eq_coe, decompose_coe, submodule.coe_eq_zero] using this, },
        { simp only [eq_iff_true_of_subsingleton], }, }, },
    { have := x.2,
      change _ β β₯ at this,
      rw submodule.mem_bot at this,
      have eqz : x = 0,
      { ext, },
      change βx = _ at this,
      rw [this, eqz],
      simp only [map_zero], }, },
  { rw [map_add, map_add, hx, hy], },
end

lemma right_inverse' : function.right_inverse (decompose_to_int π)
  (direct_sum.coe_add_monoid_hom (nat_to_int π)) := Ξ» a,
have m : β x, x β supr (nat_to_int π), from Ξ» x, by rw [supr_eq_top π]; trivial,
begin
  refine submodule.supr_induction (nat_to_int π) (m a) _ _ _,
  { intros i a hi,
    rw [decompose_to_int_of_mem π i a hi, direct_sum.coe_add_monoid_hom_of],
    refl, },
  { simp [map_zero] },
  { intros x y hx hy,
    rw [map_add, map_add, hx, hy], },
end

section

variable [Ξ  (i : β) (x : π i), decidable (x β  0)]

instance : graded_algebra (nat_to_int π) :=
{ one_mem := nat_to_int.one_mem' _,
  mul_mem := nat_to_int.mul_mem' _,
  decompose' := nat_to_int.decompose_to_int _,
  left_inv := nat_to_int.left_inverse' _,
  right_inv := nat_to_int.right_inverse' _, }

lemma decompose_eq (a : A) :
  graded_algebra.decompose (nat_to_int π) a = decompose_to_int π a := rfl

lemma ideal.is_homogeneous_int_iff_is_homogeneous_nat (I : ideal A) :
  I.is_homogeneous (nat_to_int π) β I.is_homogeneous π :=
{ mp := Ξ» hI i a ha, begin
    specialize hI (int.of_nat i) ha,
    convert hI,
    rw [decompose_eq, decompose_to_int_apply_of_nat],
  end,
  mpr := Ξ» hI i a ha, begin
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