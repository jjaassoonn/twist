import category_theory.preadditive.injective
import category_theory.adjunction
import category_theory.limits.constructions.epi_mono
import category_theory.abelian.exact
import enough_injectives.preserves_exact_seq

noncomputable theory

namespace category_theory

open limits

universes u v

variables {𝓐 𝓑 : Type u} [category.{v} 𝓐] [category.{v} 𝓑]
variables [abelian 𝓐] [abelian 𝓑]
variables [enough_injectives 𝓑]
variables (L : 𝓐 ⥤ 𝓑) (R : 𝓑 ⥤ 𝓐)
variables [faithful L] [preserves_finite_limits L] [preserves_finite_colimits L]
variables (adj : L ⊣ R)

namespace enough_injectives

-- instance {X Y : 𝓐} (f : X ⟶ Y) [mono f] : mono (L.map f) := category_theory.preserves_mono L f
-- { right_cancellation := λ B g h cancel, begin
--   type_check g ≫ L.map f,
--   have g' := (adj.hom_equiv _ _).symm g,

-- end }


section


def injective_presentation_of_apply (A : 𝓐) :
  injective_presentation (L.obj A) :=
(nonempty.some (enough_injectives.presentation (L.obj A)))

def injective_object_of_adjunction (A : 𝓐) : 𝓐 :=
  R.obj $ (injective_presentation_of_apply L A).J


include adj
variables {L R}

def to_J_of_injective_presentation_of_apply {A X Y : 𝓐}
  (g : X ⟶ injective_object_of_adjunction L R A)
  (f : X ⟶ Y) [mono f] :
  L.obj Y ⟶ (injective_presentation_of_apply L A).J :=
let factors := (injective_presentation_of_apply L A).injective.factors in
(factors ((adj.hom_equiv X (injective_presentation_of_apply L A).J).symm g) (L.map f)).some

lemma comp_to_J_of_injective_presentation_of_apply {A X Y : 𝓐}
  (g : X ⟶ injective_object_of_adjunction L R A)
  (f : X ⟶ Y) [mono f] : 
  L.map f ≫ (to_J_of_injective_presentation_of_apply adj g f) = 
  (adj.hom_equiv X (injective_presentation_of_apply L A).J).symm g :=
let factors := (injective_presentation_of_apply L A).injective.factors in
(factors ((adj.hom_equiv _ _).symm g) (L.map f)).some_spec

def injective_object_of_adjunction.factor {A X Y : 𝓐}
  (g: X ⟶ injective_object_of_adjunction L R A)
  (f : X ⟶ Y) [mono f] :
  Y ⟶ injective_object_of_adjunction L R A :=
adj.hom_equiv _ _ $ to_J_of_injective_presentation_of_apply adj g f

lemma injective_object_of_adjunction.comp {A X Y : 𝓐}
  (g: X ⟶ injective_object_of_adjunction L R A)
  (f : X ⟶ Y) [mono f]:
  f ≫ injective_object_of_adjunction.factor adj g f = g :=
begin
  have := comp_to_J_of_injective_presentation_of_apply adj g f,
  rw ←adj.hom_equiv_apply_eq at this,
  rw [←this],
  simp only [injective_object_of_adjunction.factor, to_J_of_injective_presentation_of_apply, adjunction.hom_equiv_counit,
    adjunction.hom_equiv_naturality_left_symm, adjunction.hom_equiv_naturality_right_symm,
    adjunction.left_triangle_components, category.id_comp, adjunction.hom_equiv_naturality_left,
    adjunction.hom_equiv_unit, functor.map_comp, adjunction.unit_naturality_assoc],
  congr,
  ext,
  generalize_proofs h1,
  rw h1.some_spec,
end

lemma injective_object_of_adjunction_is_injective (A : 𝓐) :
  injective (injective_object_of_adjunction L R A) :=
{ factors := λ X Y g f m, ⟨by resetI; exact injective_object_of_adjunction.factor adj g f, begin
  resetI,
  apply injective_object_of_adjunction.comp,
end⟩ }

def of_adjunction.presentation.J (A : 𝓐) : 𝓐 := 
injective_object_of_adjunction L R A

def of_adjunction.presentation.injective (A : 𝓐) :
  injective (of_adjunction.presentation.J adj A) :=
by apply injective_object_of_adjunction_is_injective adj

def of_adjunction.presentation.f (A : 𝓐) :
  A ⟶ injective_object_of_adjunction L R A :=
adj.hom_equiv A (injective_presentation_of_apply L A).J (injective_presentation_of_apply L A).f

instance of_adjunction.presentation.mono (A : 𝓐) :
  mono $ of_adjunction.presentation.f adj A :=
have e1 : exact _ (of_adjunction.presentation.f adj A) := exact_kernel_ι,
have e2 : exact (L.map (kernel.ι (of_adjunction.presentation.f adj A))) (L.map (of_adjunction.presentation.f adj A)), from exact_of_exact_functor L _ _ e1,
have eq1 : L.map (of_adjunction.presentation.f adj A) ≫ (adj.counit.app _) = (injective_presentation_of_apply L A).f, begin
  dunfold of_adjunction.presentation.f,
  simp only [adjunction.hom_equiv_unit, functor.map_comp, category.assoc, adjunction.counit_naturality,
    adjunction.left_triangle_components_assoc],
end,
have m2 : mono (L.map (of_adjunction.presentation.f adj A)), from begin
  haveI : mono (L.map (of_adjunction.presentation.f adj A) ≫ (adj.counit.app _)),
  { rw eq1,
    exactI (injective_presentation_of_apply L A).mono, },
  exactI mono_of_mono (L.map (of_adjunction.presentation.f adj A)) (adj.counit.app (injective_presentation_of_apply L A).J),
end,
have eq2 : L.map (kernel.ι (of_adjunction.presentation.f adj A)) = 0, begin
  rw abelian.mono_iff_kernel_ι_eq_zero at m2,
  have : L.map (kernel.ι (of_adjunction.presentation.f adj A)) = (preserves_kernel.iso L (of_adjunction.presentation.f adj A)).hom ≫ kernel.ι (L.map (of_adjunction.presentation.f adj A)),
  { simp only [preserves_kernel.iso_hom, kernel_comparison_comp_ι], },
  rw [this, m2, comp_zero],
end,
have eq3 : kernel.ι (of_adjunction.presentation.f adj A) = 0, from L.zero_of_map_zero _ eq2,
by rw [abelian.mono_iff_kernel_ι_eq_zero, eq3]

instance of_adjunction : enough_injectives 𝓐 :=
{ presentation := λ A, nonempty.intro 
  { J := of_adjunction.presentation.J adj _,
    injective := of_adjunction.presentation.injective adj _,
    f := of_adjunction.presentation.f adj _,
    mono := of_adjunction.presentation.mono adj _ } }

end

end enough_injectives

end category_theory