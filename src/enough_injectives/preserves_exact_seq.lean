import category_theory.abelian.exact
import category_theory.limits.constructions.epi_mono

noncomputable theory

namespace category_theory

open limits

universes u v

variables {𝓐 𝓑 : Type u} [category.{v} 𝓐] [category.{v} 𝓑]
variables [abelian 𝓐] [abelian 𝓑]
variables (L : 𝓐 ⥤ 𝓑) [preserves_finite_limits L] [preserves_finite_colimits L]


lemma preserve_image {X Y : 𝓐} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
have aux1 : strong_epi_mono_factorisation (L.map f) :=
{ I := L.obj (image f),
  m := L.map $ image.ι _,
  m_mono := by apply_instance,
  e := L.map $ factor_thru_image _,
  e_strong_epi := strong_epi_of_epi _,
  fac' := by rw [←L.map_comp, image.fac] },
is_image.iso_ext (image.is_image (L.map f)) aux1.to_mono_is_image

lemma preserve_image.precomp_factor_thru_image {X Y : 𝓐} (f : X ⟶ Y) :
  factor_thru_image  (L.map f) ≫ (preserve_image L f).hom =
  L.map (factor_thru_image f) :=
begin
  dunfold preserve_image,
  simp only [is_image.iso_ext_hom],
  erw image.fac_lift,
end

def apply_image_subobject_iso_image_subobject_apply {X Y : 𝓐} (f : X ⟶ Y) :
   L.obj (image_subobject f) ≅ (image_subobject (L.map f)) := 
{ hom := L.map (image_subobject_iso _).hom ≫ (preserve_image L f).inv,
  inv := (preserve_image L f).hom ≫ L.map (image_subobject_iso _).inv,
  hom_inv_id' := by rw [category.assoc, ←category.assoc _ _ (L.map _), iso.inv_hom_id, category.id_comp,
    ←L.map_comp, iso.hom_inv_id, L.map_id],
  inv_hom_id' := by rw [category.assoc, ←category.assoc _ _ (preserve_image L f).inv, 
    ←L.map_comp, iso.inv_hom_id, L.map_id, category.id_comp, iso.hom_inv_id] } 
≪≫ (image_subobject_iso _).symm


def apply_kernel_subobject_iso_kernel_subobject_apply {X Y : 𝓐} (f : X ⟶ Y) :
  L.obj (kernel_subobject f) ≅ (kernel_subobject (L.map f)) :=
{ hom := L.map (kernel_subobject_iso _).hom ≫ (preserves_kernel.iso L f).hom,
  inv := (preserves_kernel.iso L f).inv ≫ L.map (kernel_subobject_iso _).inv,
  hom_inv_id' := by rw [category.assoc, ←category.assoc _ _ (L.map _), iso.hom_inv_id, category.id_comp, ←L.map_comp, iso.hom_inv_id, L.map_id],
  inv_hom_id' := by rw [category.assoc, ←category.assoc _ _ (preserves_kernel.iso _ _).hom, ←L.map_comp, iso.inv_hom_id, L.map_id, category.id_comp, iso.inv_hom_id] } 
≪≫ (kernel_subobject_iso _).symm

lemma exact_of_exact_functor {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z)
  (e1 : exact f g) :
  exact (L.map f) (L.map g) := 
have H : is_iso (image_to_kernel f g e1.w) := is_iso_of_mono_of_epi _,
begin
  rw abelian.exact_iff_image_eq_kernel,
  ext,
  work_on_goal 2 
  { refine (preserve_image L f) ≪≫ _ ≪≫ (preserves_kernel.iso _ _),
    exact
    { hom := L.map $ (image_subobject_iso _).inv ≫ image_to_kernel f g e1.w ≫ (kernel_subobject_iso _).hom,
      inv := L.map $ (kernel_subobject_iso _).inv ≫ (@as_iso _ _ _ _ (image_to_kernel _ _ e1.w) H).inv ≫ (image_subobject_iso _).hom,
      hom_inv_id' := begin
        simp only [←L.map_comp, category.assoc],
        have h1 := (kernel_subobject_iso g).hom_inv_id,
        reassoc h1,
        rw [h1, ←category.assoc _ _ (image_subobject_iso _).hom, as_iso_inv,
          is_iso.hom_inv_id, category.id_comp, iso.inv_hom_id, L.map_id],
      end,
      inv_hom_id' := begin
        simp only [←L.map_comp, category.assoc],
        have h1 := (image_subobject_iso f).hom_inv_id,
        reassoc h1,
        rw [h1, ←category.assoc _ _ (kernel_subobject_iso _).hom, as_iso_inv,
          is_iso.inv_hom_id, category.id_comp, iso.inv_hom_id, L.map_id],
      end } },
  { simp only [functor.map_comp, category.assoc, iso.trans_hom, preserves_kernel.iso_hom, kernel_comparison_comp_ι, image.fac],
    simp only [←L.map_comp, kernel_subobject_arrow, image_to_kernel_arrow, image_subobject_arrow'],
    rw [←category.assoc, preserve_image.precomp_factor_thru_image, ←L.map_comp, image.fac] }
end

end category_theory