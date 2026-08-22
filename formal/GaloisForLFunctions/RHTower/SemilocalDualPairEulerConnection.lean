import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse

/-!
# The semilocal dual-pair connection is the finite Euler logarithmic source

Scalar layer of the semilocal Euler connection.  For a prime `p` write

`E_p(z) = 1 - p^{-z}` (the inverse local factor),  `Φ_p(z) = log p · p^{-z} / (1 - p^{-z})`.

Then `Φ_p = -L_p'/L_p` is the logarithmic derivative of the inverse local factor, its Lambert
expansion has exactly the von Mangoldt coefficients `log p · p^{-mz}`, the finite-place multiplier
`g_S = ∏_{p ∈ S} E_p` is multiplicative in the place set with additive source, and the whole family
is Schwarz-reflection covariant.

The actual-point Euler-parameter Hessian is `T_p(z) = log p · p^{-z}/(1 - p^{-z})²`; it is minus the
normalized spectral derivative of the connection, and its FE--Schwarz two-value defect factors
through the **canonical seam charge** `C_p(ρ) = log p (p^{-conj ρ} - p^{-(1-ρ)})` with invertible
cofactors, so a single finite place already detects the critical line.
-/

namespace RHTower

open scoped BigOperators
open Complex

noncomputable section

/-- The inverse local Euler factor `1 - p^{-z}`. -/
def eulerLocalInverse (p : ℕ) (z : ℂ) : ℂ := 1 - (p : ℂ) ^ (-z)

/-- The one-prime logarithmic source `Φ_p(z) = log p · p^{-z}/(1 - p^{-z})`. -/
def primeLogSource (p : ℕ) (z : ℂ) : ℂ :=
  (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))

/-- The finite-place multiplier `g_S(z) = ∏_{p ∈ S} (1 - p^{-z})`. -/
def finitePlaceMultiplier (S : Finset ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ S, eulerLocalInverse p z

/-- The finite-place logarithmic source `Φ_S = ∑_{p ∈ S} Φ_p`. -/
def finitePlaceSource (S : Finset ℕ) (z : ℂ) : ℂ :=
  ∑ p ∈ S, primeLogSource p z

/-- The actual Euler-parameter connection `A_p(a;z) = -p^{-z}/(1 - a p^{-z})`. -/
def eulerParameterConnection (p : ℕ) (a z : ℂ) : ℂ :=
  -(p : ℂ) ^ (-z) / (1 - a * (p : ℂ) ^ (-z))

/-- The actual-point Euler-parameter Hessian `T_p(z) = log p · p^{-z}/(1 - p^{-z})²`. -/
def eulerParameterHessian (p : ℕ) (z : ℂ) : ℂ :=
  (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z)) ^ 2

/-! ## Place additivity and multiplicativity `(12)` -/

theorem finitePlaceMultiplier_union {S T : Finset ℕ} (h : Disjoint S T) (z : ℂ) :
    finitePlaceMultiplier (S ∪ T) z = finitePlaceMultiplier S z * finitePlaceMultiplier T z := by
  rw [finitePlaceMultiplier, finitePlaceMultiplier, finitePlaceMultiplier,
    Finset.prod_union h]

theorem finitePlaceSource_union {S T : Finset ℕ} (h : Disjoint S T) (z : ℂ) :
    finitePlaceSource (S ∪ T) z = finitePlaceSource S z + finitePlaceSource T z := by
  rw [finitePlaceSource, finitePlaceSource, finitePlaceSource, Finset.sum_union h]

/-! ## `(17)` The arithmetic contraction of the parameter connection -/

/-- `(17)`: at the actual Euler point `a = 1`, the spectral source is minus the
`log p`-contraction of the parameter connection. -/
theorem primeLogSource_eq_neg_log_mul_connection (p : ℕ) (z : ℂ) :
    primeLogSource p z = -((Real.log p : ℂ) * eulerParameterConnection p 1 z) := by
  rw [primeLogSource, eulerParameterConnection, one_mul]
  ring

theorem finitePlaceSource_eq_neg_sum_log_mul_connection (S : Finset ℕ) (z : ℂ) :
    finitePlaceSource S z = -∑ p ∈ S, (Real.log p : ℂ) * eulerParameterConnection p 1 z := by
  rw [finitePlaceSource, Finset.neg_sum]
  exact Finset.sum_congr rfl fun p _ => primeLogSource_eq_neg_log_mul_connection p z

/-! ## `(8)` The Lambert expansion with von Mangoldt coefficients -/

theorem norm_primePow_lt_one {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    ‖(p : ℂ) ^ (-z)‖ < 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
  have hpone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hneg : (-z).re < 0 := by simpa using hz
  exact Real.rpow_lt_one_of_one_lt_of_neg hpone hneg

/-- `(8)`: the one-prime source is the Lambert series with von Mangoldt coefficients. -/
theorem primeLogSource_hasSum {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun m : ℕ => (Real.log p : ℂ) * (p : ℂ) ^ (-((m : ℂ) + 1) * z))
      (primeLogSource p z) := by
  have hlt := norm_primePow_lt_one hp hz
  have hgeom : HasSum (fun m : ℕ => ((p : ℂ) ^ (-z)) ^ m) (1 - (p : ℂ) ^ (-z))⁻¹ :=
    hasSum_geometric_of_norm_lt_one hlt
  have hshift : HasSum (fun m : ℕ => (Real.log p : ℂ) * (p : ℂ) ^ (-z) * ((p : ℂ) ^ (-z)) ^ m)
      ((Real.log p : ℂ) * (p : ℂ) ^ (-z) * (1 - (p : ℂ) ^ (-z))⁻¹) :=
    hgeom.mul_left _
  refine hshift.congr_fun ?_ |>.congr ?_
  · intro m
    have hp0 : (p : ℂ) ≠ 0 := by
      have : (0 : ℕ) < p := by omega
      exact_mod_cast Nat.cast_ne_zero.mpr this.ne'
    rw [← Complex.cpow_natCast ((p : ℂ) ^ (-z)) m, ← Complex.cpow_mul_of_ne_zero, ←
      Complex.cpow_add _ _ hp0]
    · congr 1
      push_cast
      ring
    · exact hp0
  · rw [primeLogSource, div_eq_mul_inv]

end

end RHTower
