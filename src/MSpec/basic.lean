import topology.sheaves.sheaf
import algebraic_geometry.prime_spectrum.basic
import algebraic_geometry.structure_sheaf
import algebraic_geometry.Spec
import algebra.category.Module.basic
import module_localisation.basic
import algebra.category.Group.limits

namespace algebraic_geometry

open Top
open Top.presheaf
open topological_space
open category_theory
open opposite
open localized_module

universes u v

variables {R : CommRing.{u}} (M : Module.{u} R)

local notation `Spec.T` := Spec.Top_obj R

namespace MSpec

abbreviation localizations (p : Spec.T) : Type u :=
localized_module M (p.as_ideal.prime_compl)

def is_fraction {U : opens Spec.T} (f : Π x : U, localizations M x) : Prop :=
∃ (m : M) (s : R), ∀ x : U, ∃ nin: ¬ (s ∈ x.1.as_ideal), f x = localized_module.mk m ⟨s, nin⟩

def is_fraction_prelocal : @prelocal_predicate Spec.T (localizations M) :=
{ pred := λ U f, is_fraction M f,
  res := λ U V i f ⟨m, s, h⟩, ⟨m, s, λ x, begin
    rcases h (i x) with ⟨nin, h⟩,
    exact ⟨nin, h⟩,
  end⟩ }

def is_locally_fraction : local_predicate (localizations M) :=
(is_fraction_prelocal M).sheafify

lemma is_locally_fraction_pred {U : opens Spec.T}
  (f : Π x : U, localizations M x) :
  (is_locally_fraction M).pred f = 
  ∀ x : U, ∃ (V : opens Spec.T) (m : x.1 ∈ V) (i : V ⟶ U) (m : M) (s : R), 
    ∀ (y : V), ∃ (nin : ¬ (s ∈ y.1.as_ideal)), 
      f (by exact i y) = localized_module.mk m ⟨s, nin⟩ := rfl

def section_add_group (U : (opens Spec.T)ᵒᵖ) : add_subgroup (Π (x : U.unop), localizations M x) :=
{ carrier := {f | (is_locally_fraction M).pred f},
  add_mem' := λ f g hf hg x, begin
    rcases hf x with ⟨Vf, mem1, i1, m1, s1, hf⟩,
    rcases hg x with ⟨Vg, mem2, i2, m2, s2, hg⟩,
    refine ⟨Vf ⊓ Vg, ⟨mem1, mem2⟩, hom_of_le inf_le_left ≫ i1, s2 • m1 + s1 • m2, s1 * s2, _⟩,
    intros y,
    rcases hf ((hom_of_le inf_le_left : Vf ⊓ Vg ⟶ Vf) y) with ⟨nin1, h1⟩,
    rcases hg ((hom_of_le inf_le_right : Vf ⊓ Vg ⟶ Vg) y) with ⟨nin2, h2⟩,
    refine ⟨λ r, (y.1.is_prime.mem_or_mem r).elim nin1 nin2, _⟩,
    dsimp only at h1 h2 ⊢,
    rw [pi.add_apply],
    erw [h1, h2],
    rw [localized_module.mk_add_mk],
    congr' 1,
  end,
  zero_mem' := λ x, begin
    refine ⟨U.unop, x.2, 𝟙 _, 0, 1, λ y, ⟨by simpa [←ideal.eq_top_iff_one] using y.1.is_prime.ne_top, _⟩⟩,
    dsimp only,
    rw [localized_module.mk_zero],
    refl,
  end,
  neg_mem' := λ f hf x, begin
    rcases hf x with ⟨Vf, mem1, i1, m1, s1, hf⟩,
    refine ⟨Vf, mem1, i1, -m1, s1, λ y, _⟩,
    rcases hf y with ⟨nin1, hf⟩,
    refine ⟨nin1, _⟩,
    simp only at hf ⊢,
    change - (f _) = _,
    rw [hf, localized_module.neg_mk],
  end }

def structure_sheaf_in_Type : sheaf Type* (Spec.T):=
subsheaf_to_Types (is_locally_fraction M)

instance ab_structure_sheaf_in_Type_obj (U : (opens Spec.T)ᵒᵖ) :
  add_comm_group ((structure_sheaf_in_Type M).1.obj U) := (section_add_group M U).to_add_comm_group

def structure_presheaf_in_Ab : presheaf Ab.{u} (Spec.T) :=
{ obj := λ U, AddCommGroup.of ((structure_sheaf_in_Type M).1.obj U),
  map := λ U V i, 
  { to_fun := (structure_sheaf_in_Type M).1.map i,
    map_zero' := rfl,
    map_add' := λ _ _, rfl } }

def structure_presheaf_comp_forget :
  structure_presheaf_in_Ab M ⋙ (forget AddCommGroup) ≅ (structure_sheaf_in_Type M).1 :=
nat_iso.of_components (λ U, iso.refl _) (by tidy)

def structure_sheaf : sheaf Ab.{u} (Spec.T) :=
⟨structure_presheaf_in_Ab M,
  (@@is_sheaf_iff_is_sheaf_comp _ _ (forget Ab) _ _ _ (AddCommGroup.forget_preserves_limits.{u u}) (structure_presheaf_in_Ab M)).mpr
    (is_sheaf_of_iso (structure_presheaf_comp_forget M).symm (structure_sheaf_in_Type M).2)⟩

instance (U : (opens Spec.T)ᵒᵖ) (x : U.unop) :
  module (structure_sheaf.localizations R (x : Spec.T)) (localizations M x) :=
localized_module.is_module

instance (U : (opens Spec.T)ᵒᵖ) :
  has_smul ((Spec.structure_sheaf R).1.obj U) ((MSpec.structure_sheaf M).1.obj U) :=
{ smul := λ r m, ⟨λ x, (r.1 x) • (m.1 x), λ x, begin
    rcases r.2 x with ⟨Vr, mem1, i1, ρ, s, hr⟩,
    rcases m.2 x with ⟨Vm, mem2, i2, m, t, ht⟩,
    refine ⟨Vr ⊓ Vm, ⟨mem1, mem2⟩, hom_of_le inf_le_left ≫ i1, ρ • m, s * t, λ y, _⟩,
    rcases hr ((hom_of_le (inf_le_left : Vr ⊓ Vm ≤ _)) y) with ⟨nin1, h1⟩,
    rcases ht ((hom_of_le (inf_le_right : Vr ⊓ Vm ≤ _)) y) with ⟨nin2, h2⟩,
    dsimp only at h1 h2 ⊢,
    refine ⟨λ r, (y.1.is_prime.mem_or_mem r).elim nin1 nin2, _⟩,
    have h3 : r.1 ((hom_of_le (inf_le_left : Vr ⊓ Vm ≤ _) ≫ i1) y) = localization.mk ρ ⟨s, nin1⟩,
    { rw [localization.mk_eq_mk'],
      erw is_localization.eq_mk'_iff_mul_eq,
      exact h1, },
    erw [h3, h2],
    rw localized_module.mk_smul_mk,
    refl,
  end⟩ }

protected lemma smul.val {U : (opens Spec.T)ᵒᵖ} (r : (Spec.structure_sheaf R).1.obj U) (m : (MSpec.structure_sheaf M).1.obj U) :
  (r • m).1 = r.1 • m.1 := rfl

protected lemma smul.apply {U : (opens Spec.T)ᵒᵖ} (r : (Spec.structure_sheaf R).1.obj U) (m : (MSpec.structure_sheaf M).1.obj U) (x : U.unop) :
  (r • m).1 x = r.1 x • m.1 x := rfl

protected lemma one_smul {U : (opens Spec.T)ᵒᵖ} (m : (MSpec.structure_sheaf M).1.obj U) :
  (1 : (Spec.structure_sheaf R).1.obj U) • m = m :=
begin
  rw [subtype.ext_iff_val],
  ext1 x,
  rw [MSpec.smul.apply],
  change (1 : Π x : U.unop, structure_sheaf.localizations R (x : Spec.T)) x • (m.1 x) = m.1 x,
  erw pi.one_apply,
  rw one_smul,
end

protected lemma mul_smul {U : (opens Spec.T)ᵒᵖ} 
  (r1 r2 : (Spec.structure_sheaf R).1.obj U) (m : (MSpec.structure_sheaf M).1.obj U) :
  (r1 * r2) • m = r1 • r2 • m :=
begin
  rw [subtype.ext_iff_val],
  ext1 x,
  rw [MSpec.smul.apply, MSpec.smul.apply, MSpec.smul.apply],
  change (r1.1 * r2.1) x • _ = _,
  erw [pi.mul_apply],
  rw mul_smul,
end

protected lemma smul_add {U : (opens Spec.T)ᵒᵖ} 
  (r : (Spec.structure_sheaf R).1.obj U) (m1 m2 : (MSpec.structure_sheaf M).1.obj U) :
  r • (m1 + m2) = r • m1 + r • m2 :=
begin
  rw [subtype.ext_iff_val],
  ext1 x,
  rw [MSpec.smul.apply],
  change r.1 x • (m1.1 + m2.1) x = (r.1 x • m1.1 x) + (r.1 x • m2.1 x),
  rw [pi.add_apply, smul_add],
end

protected lemma smul_zero {U : (opens Spec.T)ᵒᵖ} 
  (r : (Spec.structure_sheaf R).1.obj U) :
  r • (0 : (MSpec.structure_sheaf M).1.obj U) = 0 :=
begin
  rw [subtype.ext_iff_val],
  ext1 x,
  rw [MSpec.smul.apply],
  change r.1 x • (0 : Π x, localizations M x) x = (0 : Π x, localizations M x) x,
  rw [pi.zero_apply, smul_zero],
end

protected lemma add_smul {U : (opens Spec.T)ᵒᵖ} 
  (r1 r2 : (Spec.structure_sheaf R).1.obj U) (m : (MSpec.structure_sheaf M).1.obj U) :
  (r1 + r2) • m = r1 • m + r2 • m :=
begin
  rw [subtype.ext_iff_val],
  ext1 x,
  rw [MSpec.smul.apply],
  change (r1.1 + r2.1) x • _ = (r1.1 x • m.1 x + r2.1 x • m.1 x),
  rw [pi.add_apply, add_smul],
end

protected lemma zero_smul {U : (opens Spec.T)ᵒᵖ} (m : (MSpec.structure_sheaf M).1.obj U) :
  (0 : (Spec.structure_sheaf R).1.obj U) • m = 0 :=
begin
  rw [subtype.ext_iff_val],
  ext1 x,
  rw [MSpec.smul.apply],
  change (0 : Π x, structure_sheaf.localizations R (x : Spec.T)) x • m.1 x = (0 : Π x, localizations M x) x,
  rw [pi.zero_apply, zero_smul, pi.zero_apply],
end

instance (U : (opens Spec.T)ᵒᵖ) :
  module ((Spec.structure_sheaf R).1.obj U) ((MSpec.structure_sheaf M).1.obj U) :=
{ smul := (•),
  one_smul := MSpec.one_smul M,
  mul_smul := MSpec.mul_smul M,
  smul_add := MSpec.smul_add M,
  smul_zero := MSpec.smul_zero M,
  add_smul := MSpec.add_smul M,
  zero_smul := MSpec.zero_smul M }


end MSpec

end algebraic_geometry