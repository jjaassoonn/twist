import algebra.module.basic

variables (R M M' : Type*) [semiring R] [add_comm_monoid M] [add_comm_monoid M'] [module R M]

instance module.is_module_of_add_equiv (e : M ≃+ M') : module R M' :=
{ smul := λ r m, e (r • e.symm m),
  one_smul := λ m, begin
    change e _ = _,
    rw [one_smul, add_equiv.apply_symm_apply],
  end,
  mul_smul := λ x y m, begin
    change e _ = _,
    rw [mul_smul],
  end,
  smul_add := _,
  smul_zero := _,
  add_smul := _,
  zero_smul := _ }