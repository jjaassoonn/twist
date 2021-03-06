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
variables (π : β β submodule R A) [graded_algebra π]
variable [Ξ  (i : β) (x : π i), decidable (x β  0)]

local notation `Spec.T` := Spec.Top_obj β¨Aβ©

@[derive [add_comm_monoid]]
def twisted_module.grade (m : β€) : β€ β add_submonoid A := 
graded_module.twisted_by (Ξ» n, (graded_algebra.nat_to_int π n).to_add_submonoid) m


@[derive [add_comm_monoid]]
def twisted_module (m : β€) := β¨ i, twisted_module.grade π m i

instance (m : β€) : graded_module (graded_algebra.nat_to_int π) (twisted_module.grade π m) :=
graded_module.twisted_by_module _ _ _

instance (m : β€) : module A (twisted_module π m) :=
@graded_module.internal.is_module β€ R A _ _ _ _ _ (graded_algebra.nat_to_int π) _ A _ _
    (Ξ» i, (graded_algebra.nat_to_int π i).to_add_submonoid) _ m

instance (m : β€) : add_comm_group (twisted_module π m) :=
graded_module.is_add_comm_group (Ξ» m, (graded_algebra.nat_to_int π m).to_add_subgroup) m

def Serre_twisting_sheaf (m : β€) : sheaf Ab (Spec.T) :=
  MSpec.structure_sheaf β¨twisted_module π mβ©

end serre_twisting_sheaf

end algebraic_geometry