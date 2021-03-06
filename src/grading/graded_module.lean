import ring_theory.graded_algebra.basic
import module_localisation.basic
import lemmas.about_direct_sum

section

open_locale direct_sum big_operators

variables {ฮน R A : Type*}
variables [decidable_eq ฮน] [add_monoid ฮน] [comm_semiring R] [semiring A] [algebra R A]
variables (๐ : ฮน โ submodule R A) [graded_algebra ๐]
variables {M : Type*} [add_comm_monoid M] [module A M]
variables (๐ : ฮน โ add_submonoid M)

class graded_module :=
(decompose' : M โ โจ i, ๐ i)
(left_inv : function.left_inverse decompose' (direct_sum.coe_add_monoid_hom ๐))
(right_inv : function.right_inverse decompose' (direct_sum.coe_add_monoid_hom ๐))
(smul_mem : โ โฆi j : ฮนโฆ {a : A} {m : M} (hi : a โ ๐ i) (hj : m โ ๐ j), a โข m โ ๐ (i + j))

namespace graded_module

variables [graded_module ๐ ๐]

protected lemma is_internal : direct_sum.is_internal ๐ :=
{ left := (@graded_module.left_inv ฮน R A _ _ _ _ _ ๐ _ M _ _ ๐ _).injective,
  right := (@graded_module.right_inv ฮน R A _ _ _ _ _ ๐ _ M _ _ ๐ _).surjective }

def decompose : M โ+ โจ i, ๐ i := add_equiv.symm
{ to_fun := direct_sum.coe_add_monoid_hom ๐,
  inv_fun := graded_module.decompose' ๐,
  left_inv := graded_module.left_inv,
  right_inv := graded_module.right_inv,
  map_add' := ฮป x y, by rw map_add }

@[simp] lemma decompose_symm_of {i : ฮน} (x : ๐ i) :
  (graded_module.decompose ๐ ๐).symm (direct_sum.of _ i x) = x :=
direct_sum.coe_add_monoid_hom_of _ _ _

instance self : graded_module ๐ (ฮป i, (๐ i).to_add_submonoid) :=
{ decompose' := graded_algebra.decompose ๐,
  left_inv := graded_algebra.left_inv,
  right_inv := graded_algebra.right_inv,
  smul_mem := ฮป i j x y hi hj, set_like.graded_monoid.mul_mem hi hj }

@[simp] lemma decompose_coe {i : ฮน} (x : ๐ i) :
  graded_module.decompose ๐ ๐ x = direct_sum.of _ i x :=
by rw [โ decompose_symm_of ๐ ๐, add_equiv.apply_symm_apply]

lemma decompose_of_mem {x : M} {i : ฮน} (hx : x โ ๐ i) :
  graded_module.decompose ๐ ๐ x = direct_sum.of _ i (โจx, hxโฉ : ๐ i) :=
graded_module.decompose_coe _ _ โจx, hxโฉ

lemma decompose_of_mem_ne {x : M} {i j : ฮน} (hx : x โ ๐ i) (hij : i โ? j):
  (graded_module.decompose ๐ ๐ x j : M) = 0 :=
by rw [graded_module.decompose_of_mem _ _ hx, direct_sum.of_eq_of_ne _ _ _ _ hij, add_submonoid.coe_zero]

def twisted_by (i : ฮน) : ฮน โ add_submonoid M := ฮป j, ๐ (j + i)

end graded_module

end

namespace graded_module

open_locale direct_sum big_operators


variables {ฮน R A : Type*}
variables [decidable_eq ฮน] [add_group ฮน] [comm_semiring R] [semiring A] [algebra R A]
variables (๐ : ฮน โ submodule R A) [graded_algebra ๐]
variables {M : Type*} [add_comm_monoid M] [module A M]
variables (๐ : ฮน โ add_submonoid M) [graded_module ๐ ๐]

namespace twisted_by

variables (i : ฮน)

def to_twisted_by : (โจ j, ๐ j) โ+ (โจ j, twisted_by ๐ i j) :=
direct_sum.to_add_monoid $ ฮป j, 
{ to_fun := ฮป m, direct_sum.of _ (j - i) begin
    refine โจm.1, _โฉ,
    convert m.2,
    dunfold twisted_by,
    rw sub_add_cancel,
  end,
  map_zero' := begin
    generalize_proofs h,
    have : (โจ(0 : ๐ j), hโฉ : twisted_by ๐ i (j - i)) = 0,
    { ext, refl, },
    erw this,
    rw [map_zero],
  end,
  map_add' := ฮป x y, begin
    generalize_proofs hadd hx hy,
    have : (โจ(x + y).1, haddโฉ : twisted_by ๐ i (j - i)) = โจx.1, hxโฉ + โจy.1, hyโฉ,
    { ext, refl },
    erw this,
    rw [map_add],
  end }

lemma to_twisted_by.apply_of {k : ฮน} (x : ๐ k) :
  to_twisted_by ๐ i (direct_sum.of _ k x) = 
  direct_sum.of _ (k - i) begin
    refine โจx.1, _โฉ,
    convert x.2,
    dunfold twisted_by,
    rw sub_add_cancel,
  end := by { rw [to_twisted_by, direct_sum.to_add_monoid_of], refl }

def to_untwisted : (โจ j, twisted_by ๐ i j) โ+ (โจ j, ๐ j) :=
direct_sum.to_add_monoid $ ฮป j, 
{ to_fun := ฮป m, direct_sum.of _ (j + i) $ by exact m,
  map_zero' := by rw map_zero,
  map_add' := ฮป _ _, by rw map_add }

lemma to_untwisted.apply_of {k : ฮน} (x : twisted_by ๐ i k) :
  to_untwisted ๐ i (direct_sum.of _ k x) = 
  direct_sum.of _ (k + i) (by exact x) := by { rw [to_untwisted, direct_sum.to_add_monoid_of], refl }

lemma to_untwisted.left_inv : function.left_inverse (to_untwisted ๐ i) (to_twisted_by ๐ i) :=
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

lemma to_untwisted.right_inv : function.right_inverse (to_untwisted ๐ i) (to_twisted_by ๐ i) :=
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

def untwisted_equiv_twisted : (โจ j, ๐ j) โ+ (โจ j, twisted_by ๐ i j) :=
{ to_fun := to_twisted_by _ _,
  inv_fun := to_untwisted _ _,
  left_inv := to_untwisted.left_inv _ _,
  right_inv := to_untwisted.right_inv _ _,
  map_add' := ฮป x y, by rw [map_add] }

lemma smul_mem' โฆj k : ฮนโฆ {a : A} {m : M} (hj : a โ ๐ j) (hk : m โ (twisted_by ๐ i k)) :
  a โข m โ twisted_by ๐ i (j + k) :=
have hm : m โ ๐ (k + i), from hk,
begin
  have := graded_module.smul_mem hj hm,
  convert this using 1,
  dunfold twisted_by,
  rw [add_assoc],
end

def decompose : M โ+ (โจ (j : ฮน), (twisted_by ๐ i j)) :=
  add_equiv.trans (graded_module.decompose ๐ ๐) (untwisted_equiv_twisted ๐ i) 

protected lemma decompose_of_mem' {j : ฮน} {x : M} (hx : x โ ๐ (j + i)) : 
  decompose ๐ ๐ i x = direct_sum.of _ j (โจx, hxโฉ : twisted_by ๐ i j) := 
begin
  dunfold decompose,
  simp only [add_equiv.trans_apply],
  apply_fun (untwisted_equiv_twisted ๐ i).symm,
  change _ = to_untwisted ๐ i (direct_sum.of _ j _),
  rw [to_untwisted.apply_of, add_equiv.symm_apply_apply, graded_module.decompose_of_mem],
  work_on_goal 2 { exact hx },
  refl,
end

lemma left_inv.of (j : ฮน) (x : twisted_by ๐ i j) :
  (twisted_by.decompose ๐ ๐ i)
    (direct_sum.coe_add_monoid_hom (twisted_by ๐ i) (direct_sum.of _ j x)) =
  direct_sum.of _ j x := 
begin
  ext1 k,
  simp only [direct_sum.coe_add_monoid_hom_of],
  rw twisted_by.decompose_of_mem' ๐ ๐ i (by convert x.2 : (x : M) โ ๐ (j + i)),
  congr' 2,
  ext,
  refl,
end

lemma right_inv.mem (j : ฮน) (x : M) (hj : x โ ๐ j) :
  (direct_sum.coe_add_monoid_hom (twisted_by ๐ i)) 
    ((twisted_by.decompose ๐ ๐ i) x) = x := 
begin
  rw twisted_by.decompose_of_mem',
  work_on_goal 3 { exact j - i, },
  work_on_goal 2 { convert hj, rw sub_add_cancel, },
  erw [direct_sum.coe_add_monoid_hom, direct_sum.to_add_monoid_of],
  refl,
end

end twisted_by

instance twisted_by_module (i : ฮน) : graded_module ๐ (twisted_by ๐ i) :=
have m : โ x, x โ supr ๐,
from ฮป x, (direct_sum.is_internal.add_submonoid_supr_eq_top _ (graded_module.is_internal ๐ ๐)).symm โธ trivial,
{ decompose' := twisted_by.decompose ๐ ๐ i,
  left_inv := ฮป x, direct_sum.induction_on x (by simp only [map_zero]) begin
    intros j x,
    apply twisted_by.left_inv.of,
  end (ฮป x y hx hy, by simp only [map_add, hx, hy]),
  right_inv := ฮป x, add_submonoid.supr_induction ๐ (m x) (twisted_by.right_inv.mem ๐ ๐ i) (by simp only [map_zero]) (ฮป _ _ hx hy, by simp only [map_add, hx, hy]),
  smul_mem := twisted_by.smul_mem' ๐ ๐ i }

instance internal.has_scalar (i : ฮน) : has_scalar A (โจ j, twisted_by ๐ i j) :=
{ smul := ฮป a z, graded_module.decompose ๐ (twisted_by ๐ i) (a โข (graded_module.decompose ๐ (twisted_by ๐ i)).symm z) }

lemma internal.one_smul (i : ฮน) (z : โจ j, twisted_by ๐ i j) :
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) (1 : A) z = z := 
begin
  change graded_module.decompose _ _ _ = _,
  rw [one_smul, add_equiv.apply_symm_apply],
end

lemma internal.smul_add (i : ฮน) (a : A) (x y : โจ j, twisted_by ๐ i j) :
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) a (x + y) = 
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) a x +
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) a y := 
begin
  change graded_module.decompose _ _ _ = graded_module.decompose _ _ _ + graded_module.decompose _ _ _,
  simp only [map_add, smul_add],
end 

lemma internal.smul_zero (i : ฮน) (a : A) :
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) a 0 = 0 :=
begin
  change graded_module.decompose _ _ _ = _,
  simp only [map_zero, smul_zero],
end

lemma internal.add_smul (i : ฮน) (a b : A) (x : โจ j, twisted_by ๐ i j) :
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) (a + b) x =
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) a x +
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) b x :=
begin
  change graded_module.decompose _ _ _ = graded_module.decompose _ _ _ + graded_module.decompose _ _ _,
  simp only [map_add, add_smul],
end

lemma internal.zero_smul (i : ฮน) (x : โจ j, twisted_by ๐ i j) :
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) 0 x = 0 :=
begin
  change graded_module.decompose _ _ _ = _,
  simp only [zero_smul, map_zero],
end

lemma internal.mul_smul_of_of (i : ฮน) {j j' : ฮน} {a b : A} (hj : a โ ๐ j) (hj' : b โ ๐ j')
  (x : โจ j, twisted_by ๐ i j) :
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) (a * b) x = 
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) a 
    (@has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) b x) := 
begin
  change graded_module.decompose _ _ _ = graded_module.decompose _ _ _,
  unfold has_scalar.smul,
  rw add_equiv.symm_apply_apply,
  rw mul_smul,
end

lemma internal.mul_smul (i : ฮน) (a b : A) (x : โจ j, twisted_by ๐ i j) :
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) (a * b) x = 
  @has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) a 
    (@has_scalar.smul _ _ (internal.has_scalar ๐ ๐ i) b x) :=
have m : โ x, x โ supr ๐,
from ฮป x, (graded_algebra.is_internal ๐).submodule_supr_eq_top.symm โธ submodule.mem_top,
begin
  change graded_module.decompose _ _ _ = graded_module.decompose _ _ _,
  rw [mul_smul],
  refine submodule.supr_induction ๐ (m a) _ _ _,
  { intros j a hj,
    refine submodule.supr_induction ๐ (m b) _ _ _,
    { intros j' b hj',
      have := internal.mul_smul_of_of ๐ ๐ i hj hj' x,
      change graded_module.decompose _ _ _ = graded_module.decompose _ _ _ at this,
      rwa [mul_smul] at this, },
    { unfold has_scalar.smul,
      simp only [zero_smul, map_zero, smul_zero], },
    { unfold has_scalar.smul,
      intros b c hb hc,
      simp only [smul_add, add_smul, hb, hc, map_add], }, },
  { simp only [smul_zero, zero_smul, map_zero], },
  { intros b c hb hc,
    simp only [add_smul, smul_add, hb, hc, map_add], }
end

instance internal.is_module (i : ฮน) : module A (โจ j, twisted_by ๐ i j) :=
{ smul := (internal.has_scalar ๐ ๐ i).smul,
  one_smul := internal.one_smul _ _ _,
  mul_smul := internal.mul_smul _ _ _,
  smul_add := internal.smul_add _ _ _,
  smul_zero := internal.smul_zero _ _ _,
  add_smul := internal.add_smul _ _ _,
  zero_smul := internal.zero_smul _ _ _ }

end graded_module

namespace graded_module

open_locale direct_sum

variables {ฮน R A : Type*}
variables [decidable_eq ฮน] [add_monoid ฮน] [comm_semiring R] [semiring A] [algebra R A]
variables (๐ : ฮน โ submodule R A) [graded_algebra ๐]
variables {M : Type*} [add_comm_group M] [module A M]
variables (๐ : ฮน โ add_subgroup M)

instance (i : ฮน) : has_neg (โจ j, twisted_by (ฮป k, (๐ k).to_add_submonoid) i j) :=
{ neg := direct_sum.to_add_monoid begin
    intros j,
    refine { to_fun := _, map_add' := _, map_zero' := _ },
    { intros x,
      refine direct_sum.of _ j _,
      refine โจ-x.1, _โฉ,
      apply add_subgroup.neg_mem,
      exact x.2, },
    { convert map_zero _,
      rw neg_eq_zero,
      refl, },
    { intros x y,
      rw โmap_add,
      congr,
      dsimp only,
      change -(x.1 + y.1) = _,
      rw neg_add, },
  end }

instance is_add_comm_group (i : ฮน) : add_comm_group (โจ j, twisted_by (ฮป k, (๐ k).to_add_submonoid) i j) :=
have aux1 : โ (a b c d : โจ j, twisted_by (ฮป k, (๐ k).to_add_submonoid) i j), a + b + (c + d) = (a + c) + (b + d), from
ฮป a b c d, by { rw [add_assoc, add_assoc], congr' 1, rw [โadd_assoc, add_comm b c, add_assoc], },
{ neg := has_neg.neg,
  add_left_neg := ฮป a, begin
    change (direct_sum.to_add_monoid _) _ + a = 0,
    induction a using direct_sum.induction_on with k x x y hx hy,
    { rw [map_zero, zero_add], },
    { rw [direct_sum.to_add_monoid_of],
      simp only [add_monoid_hom.coe_mk],
      generalize_proofs h,
      rw โmap_add,
      convert map_zero _,
      rw [subtype.ext_iff_val],
      change -x.1 + x.1 = 0,
      rw add_left_neg, },
    { simp only [map_add],
      rw [aux1, hx, hy, add_zero] },
  end,
  ..(by apply_instance : add_comm_monoid (โจ j, twisted_by (ฮป k, (๐ k).to_add_submonoid) i j))}

end graded_module