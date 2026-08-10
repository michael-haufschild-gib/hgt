import GaloisForLFunctions.HTGeometry.AbelianZetaGas.KMSState

/-!
# Positivity of the Gibbs functional

The Gram kernel of the Gibbs functional has a closed form: `φ(x* y)` vanishes unless the two
monomials carry the same charge, and on that locus it is `∏_i q_i^{max(x.lower i, y.lower i)}`.
That kernel is a Hadamard product of the charge-equality kernel with one kernel per mode, and each
mode kernel is a finite nonnegative combination of rank-one kernels because
`q^{max(b,d)} = q^b q^d q^{-min(b,d)}` and `q^{-min}` telescopes with nonnegative increments.
-/

namespace GaloisForLFunctions.HTGeometry

namespace GasWord

variable {M : Type*}

/-! ## The Gram kernel in closed form -/

theorem zprod_natToInt (q : M → ℂ) (f : M →₀ ℕ) :
    zprod q (natToInt f) = f.prod fun i n => q i ^ n := by
  rw [zprod, natToInt, Finsupp.prod_mapRange_index (fun i => zpow_zero (q i))]
  exact Finsupp.prod_congr fun i _ => zpow_natCast (q i) (f i)

/-- The natural-exponent weight of a monomial. -/
noncomputable def natWeight (q : M → ℂ) (f : M →₀ ℕ) : ℂ := f.prod fun i n => q i ^ n

theorem gibbsWeight_eq_natWeight {q : M → ℂ} {x : GasWord M} (h : x.raise = x.lower) :
    gibbsWeight q x = natWeight q x.raise := by
  rw [gibbsWeight_of_diag h, zprod_natToInt, natWeight]

theorem charge_eq_iff (x y : GasWord M) :
    charge x = charge y ↔ ∀ i, (x.raise i : ℤ) - x.lower i = (y.raise i : ℤ) - y.lower i := by
  constructor
  · intro h i
    have := congrFun (congrArg (fun f : M →₀ ℤ => (f : M → ℤ)) h) i
    rwa [charge_apply, charge_apply] at this
  · intro h
    refine Finsupp.ext fun i => ?_
    rw [charge_apply, charge_apply]
    exact h i

/-- **The Gram pairing is charge-diagonal.** -/
theorem diag_wstar_mul_iff (x y : GasWord M) :
    (wstar x * y).raise = (wstar x * y).lower ↔ charge x = charge y := by
  rw [diag_iff_charge, charge_mul, charge_wstar]
  constructor
  · intro h
    have := congrArg (fun f : M →₀ ℤ => charge x + f) h
    simpa using this.symm
  · intro h
    rw [h, neg_add_cancel]

/-- **The Gram exponent is the pointwise maximum of the two lower exponents.** -/
theorem raise_wstar_mul_eq_sup {x y : GasWord M} (h : charge x = charge y) :
    (wstar x * y).raise = x.lower ⊔ y.lower := by
  refine Finsupp.ext fun i => ?_
  rw [raise_apply_mul, wstar_raise, wstar_lower, Finsupp.sup_apply]
  have hi := (charge_eq_iff x y).mp h i
  omega

open Classical in
/-- **The Gram kernel of the Gibbs functional, in closed form.** -/
theorem gibbsWeight_wstar_mul (q : M → ℂ) (x y : GasWord M) :
    gibbsWeight q (wstar x * y)
      = if charge x = charge y then natWeight q (x.lower ⊔ y.lower) else 0 := by
  classical
  by_cases h : charge x = charge y
  · rw [if_pos h, gibbsWeight_eq_natWeight ((diag_wstar_mul_iff x y).mpr h),
      raise_wstar_mul_eq_sup h]
  · rw [if_neg h, gibbsWeight_of_not_diag]
    exact fun hd => h ((diag_wstar_mul_iff x y).mp hd)

end GasWord

end GaloisForLFunctions.HTGeometry
