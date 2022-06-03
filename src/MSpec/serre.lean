import MSpec.basic
import ring_theory.graded_algebra.basic
import grading.graded_module
import grading.nat_to_int
import algebra.direct_sum.basic

namespace algebraic_geometry

namespace serre_twisting_sheaf

open graded_algebra.nat_to_int
open Top
open direct_sum

open_locale direct_sum

variables {R A : Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝓐 : ℕ → submodule R A) [graded_algebra 𝓐]
variable [Π (i : ℕ) (x : 𝓐 i), decidable (x ≠ 0)]

local notation `Spec.T` := Spec.Top_obj ⟨A⟩

@[derive [add_comm_monoid]]
def twisted_module.grade (m : ℤ) : ℤ → add_submonoid A := 
graded_module.twisted_by (λ n, (graded_algebra.nat_to_int 𝓐 n).to_add_submonoid) m


@[derive [add_comm_monoid]]
def twisted_module (m : ℤ) := ⨁ i, twisted_module.grade 𝓐 m i

instance (m : ℤ) : graded_module (graded_algebra.nat_to_int 𝓐) (twisted_module.grade 𝓐 m) :=
graded_module.twisted_by_module _ _ _

instance (m : ℤ) : module A (twisted_module 𝓐 m) :=
@graded_module.internal.is_module ℤ R A _ _ _ _ _ (graded_algebra.nat_to_int 𝓐) _ A _ _
    (λ i, (graded_algebra.nat_to_int 𝓐 i).to_add_submonoid) _ m

instance (m : ℤ) : add_comm_group (twisted_module 𝓐 m) :=
graded_module.is_add_comm_group (λ m, (graded_algebra.nat_to_int 𝓐 m).to_add_subgroup) m

def Serre_twisting_sheaf (m : ℤ) : sheaf Ab (Spec.T) :=
  MSpec.structure_sheaf ⟨twisted_module 𝓐 m⟩

end serre_twisting_sheaf

end algebraic_geometry