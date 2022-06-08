import algebra.category.Group.abelian
import algebra.category.Module.colimits
import enough_injectives.adjunction_transfer_enough_injective
import enough_injectives.divisible_group
import category_theory.adjunction.adjoint_functor_theorems
import algebra.category.Ring
import linear_algebra.tensor_product

section

universes v
variables (R : CommRing.{v})

open tensor_product
open category_theory
open_locale tensor_product

namespace coextension

variable (A : Ab.{v})


instance : module R ((⟨R⟩ : Ab) ⟶ A) :=
{ smul := λ r f, 
  { to_fun := λ r', f (r' * r),
    map_zero' := by rw [zero_mul, map_zero],
    map_add' := λ a b, by rw [add_mul, map_add] },
  one_smul := λ f, begin
    ext1 r,
    change f _ = _,
    rw [mul_one],
  end,
  mul_smul := λ r1 r2 f, begin
    ext1 r,
    change f _ = f _,
    rw mul_assoc,
  end,
  smul_add := λ r f g, begin
    ext1 x,
    change (f + g) _ = f _ + g _,
    refl,
  end,
  smul_zero := λ r, begin
    ext1 x,
    change (0 : (⟨R⟩ : Ab) ⟶ A) _ = _,
    refl,
  end,
  add_smul := λ r s f, begin
    ext1 x,
    change f _ = f _ + f _,
    rw [mul_add, map_add],
  end,
  zero_smul := λ f, begin
    ext1 x,
    change f _ = _,
    rw [mul_zero, map_zero, add_monoid_hom.zero_apply],
  end }

@[simp] lemma smul_apply (r : R) (f : (⟨R⟩ : Ab) ⟶ A) (x : R) :
  (r • f) x = f (x * r) :=
begin
  change f _ = _,
  refl,
end

def map {B C : Ab.{v}} (f : B ⟶ C) :
  (⟨(⟨R⟩ : Ab) ⟶ B⟩ : Module R) ⟶ ⟨(⟨R⟩ : Ab) ⟶ C⟩ :=
{ to_fun := λ g, 
  { to_fun := λ r, f (g r),
    map_zero' := by rw [map_zero, map_zero],
    map_add' := λ x y, by rw [map_add, map_add] },
  map_add' := λ g1 g2, begin
    ext1 x,
    simp only [map_add, add_monoid_hom.add_apply, add_monoid_hom.coe_mk],
  end,
  map_smul' := λ r g, begin
    ext1 x,
    simp only [add_monoid_hom.coe_mk, ring_hom.id_apply, smul_apply],
  end }

@[simp] lemma map_apply {B C : Ab.{v}} (f : B ⟶ C) 
  (g : (⟨R⟩ : Ab) ⟶ B) (x : R) :
  map R f g x = f (g x) := rfl

@[simps]
def functor : Ab.{v} ⥤ Module.{v} R :=
{ obj := λ A, ⟨(⟨R⟩ : Ab) ⟶ A⟩,
  map := λ X Y g, map R g,
  map_id' := λ X, begin
    ext f x,
    simp only [Module.id_apply, map_apply],
    refl,
  end,
  map_comp' := λ X Y Z g1 g2, begin
    ext f x,
    simp only [map_apply, comp_apply],
  end }

end coextension

namespace adj

variables (M : Module.{v} R) (A : Ab.{v})

namespace hom_equiv


def forward (f : (forget₂ (Module.{v} R) Ab.{v}).obj M ⟶ A) :
  M ⟶ (coextension.functor R).obj A :=
{ to_fun := λ m, 
  { to_fun := λ r, f (@has_scalar.smul R M _ r m),
    map_zero' := by rw [zero_smul, map_zero],
    map_add' := λ x y, by rw [add_smul, map_add] },
  map_add' := λ x y, begin
    ext1 z,
    simp only [map_add, smul_add, add_monoid_hom.coe_mk, add_monoid_hom.add_apply],
  end,
  map_smul' := λ r x, begin
    ext1 z,
    simp only [add_monoid_hom.coe_mk, ring_hom.id_apply, coextension.smul_apply],
    rw [mul_smul],
  end }

def backward (f : M ⟶ (coextension.functor R).obj A) :
  (forget₂ (Module.{v} R) Ab.{v}).obj M ⟶ A :=
{ to_fun := λ m, (f m).to_fun 1,
  map_zero' := by simp only [map_zero, add_monoid_hom.to_fun_eq_coe, AddCommGroup.zero_apply],
  map_add' := λ x y, by simp only [map_add, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply] }

lemma fb (f : (forget₂ (Module.{v} R) Ab.{v}).obj M ⟶ A) :
  backward R M A (forward R M A f) = f :=
begin
  ext,
  dunfold backward forward,
  simp only [linear_map.coe_mk, add_monoid_hom.coe_mk, one_smul],
end

lemma bf (f : M ⟶ (coextension.functor R).obj A) :
  forward R M A (backward R M A f) = f :=
begin
  ext,
  dunfold forward backward,
  simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.coe_mk, linear_map.map_smulₛₗ, ring_hom.id_apply,
    coextension.smul_apply, one_mul, add_monoid_hom.mk_coe, linear_map.mk_coe],
end

end hom_equiv

@[simps]
def unit : 
  𝟭 (Module R) ⟶ 
  forget₂ (Module ↥R) Ab ⋙ coextension.functor R :=
{ app := λ M, 
  { to_fun := λ m, 
    { to_fun := λ r, @has_scalar.smul R M _ r m,
      map_zero' := by rw [zero_smul],
      map_add' := λ x y, by rw [add_smul] },
    map_add' := λ x y, begin
      ext1 z,
      simp only [smul_add, add_monoid_hom.coe_mk, add_monoid_hom.add_apply],
    end,
    map_smul' := λ r m, begin
      ext1 z,
      simp only [mul_smul, add_monoid_hom.coe_mk, ring_hom.id_apply, coextension.smul_apply],
    end },
  naturality' := λ X Y f, begin
    ext r r',
    simp only [add_monoid_hom.coe_mk, ring_hom.id_apply, functor.id_map, Module.coe_comp, linear_map.coe_mk, functor.comp_map,
      Module.forget₂_map, coextension.functor_map, coextension.map_apply, linear_map.to_add_monoid_hom_coe,
      linear_map.map_smulₛₗ],
  end }

@[simps]
def counit : (coextension.functor R ⋙ forget₂ (Module.{v} R) Ab.{v}) ⟶ 𝟭 Ab :=
{ app := λ A,
  { to_fun := λ f, f.to_fun 1,
    map_zero' := rfl,
    map_add' := λ x y, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply] },
  naturality' := λ X Y g, begin
    ext,
    simp only [add_monoid_hom.to_fun_eq_coe, functor.comp_map, coextension.functor_map, Module.forget₂_map, comp_apply,
      linear_map.to_add_monoid_hom_coe, add_monoid_hom.coe_mk, coextension.map_apply, functor.id_map],
  end }

end adj

instance left_adj  : is_left_adjoint (forget₂ (Module.{v} R) Ab.{v}) :=
{ right := coextension.functor R,
  adj := 
  { hom_equiv := λ X Y,
    { to_fun := adj.hom_equiv.forward R X Y,
      inv_fun := adj.hom_equiv.backward R X Y,
      left_inv := adj.hom_equiv.fb R X Y,
      right_inv := adj.hom_equiv.bf R X Y },
    unit := adj.unit R,
    counit := adj.counit R,
    hom_equiv_unit' := λ M A f, begin
      ext m r,
      simp only [adj.hom_equiv.forward, equiv.coe_fn_mk, linear_map.coe_mk, add_monoid_hom.coe_mk, coextension.functor_map,
        Module.coe_comp, coextension.map_apply, adj.unit_app_apply_apply],
    end,
    hom_equiv_counit' := λ M A f, begin
      ext,
      simp only [adj.hom_equiv.backward, equiv.coe_fn_symm_mk, add_monoid_hom.coe_mk, Module.forget₂_map, comp_apply,
        linear_map.to_add_monoid_hom_coe, adj.counit_app_apply],
    end } }

open add_comm_group category_theory

instance : category_theory.enough_injectives (Module.{v} R) :=
@@category_theory.enough_injectives.of_adjunction _ _ _ _ _ _ _ begin
  haveI h := category_theory.adjunction.left_adjoint_preserves_colimits (left_adj R).adj,
  have h2 := @h.1,
  simp only [auto_param_eq] at h2,
  exact ⟨λ J i1 i2, @h2 J i1⟩,
end (left_adj R).adj


end