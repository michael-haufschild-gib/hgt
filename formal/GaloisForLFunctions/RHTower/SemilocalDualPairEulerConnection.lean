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
  rw [finitePlaceSource,
    Finset.sum_congr rfl fun p _ => primeLogSource_eq_neg_log_mul_connection p z]
  simp

/-! ## `(8)` The Lambert expansion with von Mangoldt coefficients -/

theorem primePow_eq_exp {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    (p : ℂ) ^ (-z) = Complex.exp (-(z * (Real.log p : ℂ))) := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast Nat.cast_ne_zero.mpr this.ne'
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
  congr 1
  ring

theorem norm_primePow_lt_one {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    ‖(p : ℂ) ^ (-z)‖ < 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
  have hpone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hneg : (-z).re < 0 := by simpa using hz
  exact Real.rpow_lt_one_of_one_lt_of_neg hpone hneg

/-- The `m`-th power of the prime phase is the `m`-fold dilated power. -/
theorem primePow_pow {p : ℕ} (hp : 2 ≤ p) (z : ℂ) (m : ℕ) :
    ((p : ℂ) ^ (-z)) ^ m = (p : ℂ) ^ (-((m : ℂ) * z)) := by
  rw [primePow_eq_exp hp, primePow_eq_exp hp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `(8)`: the one-prime source is the Lambert series whose coefficients are exactly the finite
von Mangoldt coefficients `log p · p^{-mz}`. -/
theorem primeLogSource_hasSum {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun m : ℕ => (Real.log p : ℂ) * ((p : ℂ) ^ (-z)) ^ (m + 1))
      (primeLogSource p z) := by
  have hlt := norm_primePow_lt_one hp hz
  have hgeom : HasSum (fun m : ℕ => ((p : ℂ) ^ (-z)) ^ m) (1 - (p : ℂ) ^ (-z))⁻¹ :=
    hasSum_geometric_of_norm_lt_one hlt
  have hshift := (hgeom.mul_left ((Real.log p : ℂ) * (p : ℂ) ^ (-z)))
  have hfun : (fun m : ℕ => (Real.log p : ℂ) * (p : ℂ) ^ (-z) * ((p : ℂ) ^ (-z)) ^ m)
      = fun m : ℕ => (Real.log p : ℂ) * ((p : ℂ) ^ (-z)) ^ (m + 1) := by
    funext m
    rw [pow_succ]
    ring
  have hval : (Real.log p : ℂ) * (p : ℂ) ^ (-z) * (1 - (p : ℂ) ^ (-z))⁻¹
      = primeLogSource p z := by
    rw [primeLogSource, div_eq_mul_inv]
  rw [hfun, hval] at hshift
  exact hshift

/-- The same expansion written with the literal von Mangoldt exponent `p^{-(m+1)z}`. -/
theorem primeLogSource_hasSum_cpow {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun m : ℕ => (Real.log p : ℂ) * (p : ℂ) ^ (-(((m : ℂ) + 1) * z)))
      (primeLogSource p z) := by
  refine (primeLogSource_hasSum hp hz).congr_fun ?_
  intro m
  rw [primePow_pow hp z (m + 1)]
  congr 2
  push_cast
  ring

/-! ## `(7)` The connection is the logarithmic derivative of the inverse local factor -/

theorem hasDerivAt_primePow {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (p : ℂ) ^ (-w)) (-(Real.log p : ℂ) * (p : ℂ) ^ (-z)) z := by
  have hinner : HasDerivAt (fun w : ℂ => -(w * (Real.log p : ℂ))) (-(Real.log p : ℂ)) z := by
    have h0 : HasDerivAt (fun w : ℂ => (-(Real.log p : ℂ)) * w) ((-(Real.log p : ℂ)) * 1) z :=
      (hasDerivAt_id z).const_mul _
    rw [mul_one] at h0
    exact h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by ring)
  have h : HasDerivAt (fun w : ℂ => Complex.exp (-(w * (Real.log p : ℂ))))
      (Complex.exp (-(z * (Real.log p : ℂ))) * -(Real.log p : ℂ)) z := hinner.cexp
  have hfun : (fun w : ℂ => (p : ℂ) ^ (-w))
      = fun w : ℂ => Complex.exp (-(w * (Real.log p : ℂ))) := by
    funext w
    exact primePow_eq_exp hp w
  rw [hfun]
  convert h using 1
  rw [primePow_eq_exp hp]
  ring

theorem hasDerivAt_eulerLocalInverse {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    HasDerivAt (eulerLocalInverse p) ((Real.log p : ℂ) * (p : ℂ) ^ (-z)) z := by
  have h := (hasDerivAt_primePow hp z).const_sub 1
  have hval : -(-(Real.log p : ℂ) * (p : ℂ) ^ (-z)) = (Real.log p : ℂ) * (p : ℂ) ^ (-z) := by
    ring
  rw [hval] at h
  exact h

/-- **`(7)`: `Φ_p = -L_p'/L_p` is the logarithmic derivative of the inverse local factor.** -/
theorem logDeriv_eulerLocalInverse {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    logDeriv (eulerLocalInverse p) z = primeLogSource p z := by
  rw [logDeriv_apply, (hasDerivAt_eulerLocalInverse hp z).deriv, eulerLocalInverse, primeLogSource]

/-! ## `(13)` Schwarz reflection -/

theorem conj_primePow {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    (starRingEnd ℂ) ((p : ℂ) ^ (-z)) = (p : ℂ) ^ (-(starRingEnd ℂ) z) := by
  rw [primePow_eq_exp hp, primePow_eq_exp hp, ← Complex.exp_conj]
  congr 1
  rw [map_neg, map_mul, Complex.conj_ofReal]

theorem conj_eulerLocalInverse {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    (starRingEnd ℂ) (eulerLocalInverse p z) = eulerLocalInverse p ((starRingEnd ℂ) z) := by
  rw [eulerLocalInverse, eulerLocalInverse, map_sub, map_one, conj_primePow hp]

/-- `(13)`: the one-prime source is Schwarz-reflection covariant. -/
theorem conj_primeLogSource {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    (starRingEnd ℂ) (primeLogSource p z) = primeLogSource p ((starRingEnd ℂ) z) := by
  rw [primeLogSource, primeLogSource, map_div₀, map_mul, map_sub, map_one,
    Complex.conj_ofReal, conj_primePow hp]

/-! ## `(18e)`–`(18i)` The actual-point Hessian and the one-place seam detector -/

/-- `(18h)`: the spectral derivative of the connection is minus `log p` times the actual-point
Euler-parameter Hessian. -/
theorem hasDerivAt_primeLogSource {p : ℕ} (hp : 2 ≤ p) {z : ℂ}
    (hz : eulerLocalInverse p z ≠ 0) :
    HasDerivAt (primeLogSource p)
      (-((Real.log p : ℂ) * eulerParameterHessian p z)) z := by
  have hu := hasDerivAt_primePow hp z
  have hnum : HasDerivAt (fun w : ℂ => (Real.log p : ℂ) * (p : ℂ) ^ (-w))
      ((Real.log p : ℂ) * (-(Real.log p : ℂ) * (p : ℂ) ^ (-z))) z := hu.const_mul _
  have hden := hasDerivAt_eulerLocalInverse hp z
  have hdiv := hnum.div hden hz
  have hfun : ((fun w : ℂ => (Real.log p : ℂ) * (p : ℂ) ^ (-w)) / eulerLocalInverse p)
      = primeLogSource p := by
    funext w
    simp only [Pi.div_apply]
    rw [primeLogSource, eulerLocalInverse]
  rw [hfun] at hdiv
  have hgoal : -((Real.log p : ℂ) * eulerParameterHessian p z)
      = ((Real.log p : ℂ) * (-(Real.log p : ℂ) * (p : ℂ) ^ (-z)) * eulerLocalInverse p z -
          (Real.log p : ℂ) * (p : ℂ) ^ (-z) * ((Real.log p : ℂ) * (p : ℂ) ^ (-z))) /
        eulerLocalInverse p z ^ 2 := by
    rw [eulerParameterHessian]
    simp only [eulerLocalInverse] at hz ⊢
    field_simp
    ring
  rw [hgoal]
  exact hdiv

/-- `(18f)`: the two-value defect of the actual-point Hessian factors through the canonical seam
with invertible cofactors. -/
theorem eulerParameterHessian_sub {p : ℕ} (w₁ w₂ : ℂ)
    (h₁ : (1 : ℂ) - (p : ℂ) ^ (-w₁) ≠ 0) (h₂ : (1 : ℂ) - (p : ℂ) ^ (-w₂) ≠ 0) :
    eulerParameterHessian p w₁ - eulerParameterHessian p w₂ =
      (Real.log p : ℂ) * ((p : ℂ) ^ (-w₁) - (p : ℂ) ^ (-w₂)) *
        (1 - (p : ℂ) ^ (-w₁) * (p : ℂ) ^ (-w₂)) /
          (((1 : ℂ) - (p : ℂ) ^ (-w₁)) ^ 2 * ((1 : ℂ) - (p : ℂ) ^ (-w₂)) ^ 2) := by
  rw [eulerParameterHessian, eulerParameterHessian]
  field_simp
  ring

/-! ## The finite-place logarithmic derivative and the orientation/metric split `(14)` -/

theorem eulerLocalInverse_ne_zero {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    eulerLocalInverse p z ≠ 0 := by
  intro h
  have hu : (p : ℂ) ^ (-z) = 1 := by
    rw [eulerLocalInverse, sub_eq_zero] at h
    exact h.symm
  have := norm_primePow_lt_one hp hz
  rw [hu, norm_one] at this
  exact lt_irrefl 1 this

theorem differentiableAt_eulerLocalInverse {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    DifferentiableAt ℂ (eulerLocalInverse p) z :=
  (hasDerivAt_eulerLocalInverse hp z).differentiableAt

/-- The finite-place multiplier has the finite-place source as its logarithmic derivative. -/
theorem logDeriv_finitePlaceMultiplier {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {z : ℂ}
    (hz : 0 < z.re) :
    logDeriv (finitePlaceMultiplier S) z = finitePlaceSource S z := by
  have hprod : finitePlaceMultiplier S = fun w => ∏ p ∈ S, eulerLocalInverse p w := by
    funext w
    rw [finitePlaceMultiplier]
  rw [hprod, logDeriv_prod (fun p hp => eulerLocalInverse_ne_zero (hS p hp) hz)
    (fun p hp => differentiableAt_eulerLocalInverse (hS p hp) z), finitePlaceSource]
  exact Finset.sum_congr rfl fun p hp => logDeriv_eulerLocalInverse (hS p hp) z

/-- `(7)` in the critical-line coordinate: the `t`-derivative of the one-prime multiplier is
`i Φ_p` times the multiplier itself. -/
theorem hasDerivAt_criticalLineEulerLocalInverse {p : ℕ} (hp : 2 ≤ p) (t : ℝ) :
    HasDerivAt (fun u : ℝ => eulerLocalInverse p (1 / 2 + (u : ℂ) * Complex.I))
      (Complex.I * primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) *
        eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I)) t := by
  have hline : HasDerivAt (fun u : ℝ => (1 / 2 + (u : ℂ) * Complex.I)) Complex.I t := by
    have h0 : HasDerivAt (fun u : ℝ => ((u : ℂ) * Complex.I)) ((1 : ℂ) * Complex.I) t :=
      (Complex.ofRealCLM.hasDerivAt).mul_const Complex.I
    rw [one_mul] at h0
    simpa using h0.const_add (1 / 2 : ℂ)
  have hcomp := (hasDerivAt_eulerLocalInverse hp (1 / 2 + (t : ℂ) * Complex.I)).scomp t hline
  simp only [Function.comp_def, smul_eq_mul] at hcomp
  have hval : Complex.I * ((Real.log p : ℂ) * (p : ℂ) ^ (-(1 / 2 + (t : ℂ) * Complex.I)))
      = Complex.I * primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) *
        eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I) := by
    have hne : (1 : ℂ) - (p : ℂ) ^ (-(1 / 2 + (t : ℂ) * Complex.I)) ≠ 0 := by
      have hre : (0 : ℝ) < ((1 : ℂ) / 2 + (t : ℂ) * Complex.I).re := by
        simp
      simpa [eulerLocalInverse] using eulerLocalInverse_ne_zero hp hre
    have hcancel : (Real.log p : ℂ) * (p : ℂ) ^ (-(1 / 2 + (t : ℂ) * Complex.I)) /
        (1 - (p : ℂ) ^ (-(1 / 2 + (t : ℂ) * Complex.I))) *
          (1 - (p : ℂ) ^ (-(1 / 2 + (t : ℂ) * Complex.I)))
        = (Real.log p : ℂ) * (p : ℂ) ^ (-(1 / 2 + (t : ℂ) * Complex.I)) :=
      div_mul_cancel₀ _ hne
    rw [primeLogSource, eulerLocalInverse, mul_assoc, hcancel]
  rw [hval] at hcomp
  exact hcomp

/-- `(14)`: the two components of the logarithmic derivative are the imaginary and real parts of
the source.  The orientation component is `Re Φ`, the metric component is `-Im Φ`. -/
theorem criticalLine_logDeriv_components (p : ℕ) (t : ℝ) :
    (Complex.I * primeLogSource p (1 / 2 + (t : ℂ) * Complex.I)).re
        = -(primeLogSource p (1 / 2 + (t : ℂ) * Complex.I)).im ∧
      (Complex.I * primeLogSource p (1 / 2 + (t : ℂ) * Complex.I)).im
        = (primeLogSource p (1 / 2 + (t : ℂ) * Complex.I)).re := by
  constructor <;> simp

/-! ## `(18g)` One finite place already detects the critical line -/

theorem primePow_ne_one_of_pos_re {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    (1 : ℂ) - (p : ℂ) ^ (-z) ≠ 0 := by
  simpa [eulerLocalInverse] using eulerLocalInverse_ne_zero hp hz

/-- The general-scale seam charge is a faithful detector of the critical line. -/
theorem orbitwiseScaleSeamCharge_eq_zero_iff {x : ℝ} (hx : 1 < x) (rho : ℂ) :
    orbitwiseScaleSeamCharge x rho = 0 ↔ rho.re = 1 / 2 := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hlog : (Real.log x : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hx).ne'
  constructor
  · intro hzero
    rw [orbitwiseScaleSeamCharge] at hzero
    have hcpow : (x : ℂ) ^ (-(starRingEnd ℂ) rho) = (x : ℂ) ^ (-(1 - rho)) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hlog)
    have hnorm := congrArg norm hcpow
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_cpow_eq_rpow_re_of_pos hx0] at hnorm
    have hre : (-(starRingEnd ℂ) rho).re = (-(1 - rho)).re := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd hnorm (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hx h))
      · exact absurd hnorm.symm (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hx h))
    simp only [Complex.neg_re, Complex.conj_re, Complex.sub_re, Complex.one_re] at hre
    linarith
  · intro hhalf
    rw [orbitwiseScaleSeamCharge]
    have hz : -(starRingEnd ℂ) rho = -(1 - rho) := by
      refine Complex.ext ?_ ?_
      · simp only [Complex.neg_re, Complex.conj_re, Complex.sub_re, Complex.one_re, hhalf]
        linarith
      · simp only [Complex.neg_im, Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    rw [hz, sub_self, mul_zero]

/-- **`(18g)`: at any one finite place, the actual-point Hessian FE--Schwarz two-value defect
vanishes exactly on the critical line.** -/
theorem eulerParameterHessian_reflect_eq_iff {p : ℕ} (hp : 2 ≤ p) {rho : ℂ}
    (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    eulerParameterHessian p ((starRingEnd ℂ) rho) = eulerParameterHessian p (1 - rho) ↔
      rho.re = 1 / 2 := by
  have hpx : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hconjre : ((starRingEnd ℂ) rho).re = rho.re := Complex.conj_re rho
  have hsubre : ((1 : ℂ) - rho).re = 1 - rho.re := by simp
  have hq : (1 : ℂ) - (p : ℂ) ^ (-(starRingEnd ℂ) rho) ≠ 0 :=
    primePow_ne_one_of_pos_re hp (by rw [hconjre]; exact h0)
  have hr : (1 : ℂ) - (p : ℂ) ^ (-((1 : ℂ) - rho)) ≠ 0 :=
    primePow_ne_one_of_pos_re hp (by rw [hsubre]; linarith)
  have hqr : (1 : ℂ) - (p : ℂ) ^ (-(starRingEnd ℂ) rho) * (p : ℂ) ^ (-((1 : ℂ) - rho)) ≠ 0 := by
    intro hcon
    have hprod : (p : ℂ) ^ (-(starRingEnd ℂ) rho) * (p : ℂ) ^ (-((1 : ℂ) - rho)) = 1 :=
      (sub_eq_zero.mp hcon).symm
    have hn := congrArg norm hprod
    rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), norm_one, ← Real.rpow_add
        (by positivity)] at hn
    have hexp : (-(starRingEnd ℂ) rho).re + (-((1 : ℂ) - rho)).re = -1 := by
      simp only [Complex.neg_re, Complex.conj_re, Complex.sub_re, Complex.one_re]
      ring
    rw [hexp] at hn
    have : ((p : ℝ)) ^ (-1 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpx (by norm_num)
    rw [hn] at this
    exact lt_irrefl 1 this
  have hdiff := eulerParameterHessian_sub (p := p) ((starRingEnd ℂ) rho) (1 - rho) hq hr
  have hseam : orbitwiseScaleSeamCharge ((p : ℕ) : ℝ) rho
      = (Real.log p : ℂ) *
        ((p : ℂ) ^ (-(starRingEnd ℂ) rho) - (p : ℂ) ^ (-((1 : ℂ) - rho))) := by
    rw [orbitwiseScaleSeamCharge, hcast]
  constructor
  · intro heq
    have hzero : eulerParameterHessian p ((starRingEnd ℂ) rho) -
        eulerParameterHessian p (1 - rho) = 0 := by rw [heq, sub_self]
    rw [hdiff, div_eq_zero_iff] at hzero
    have hden : (((1 : ℂ) - (p : ℂ) ^ (-(starRingEnd ℂ) rho)) ^ 2 *
        ((1 : ℂ) - (p : ℂ) ^ (-((1 : ℂ) - rho))) ^ 2) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hr)
    have hnum := hzero.resolve_right hden
    have hcharge : orbitwiseScaleSeamCharge ((p : ℕ) : ℝ) rho = 0 := by
      rw [hseam]
      exact (mul_eq_zero.mp hnum).resolve_right hqr
    exact (orbitwiseScaleSeamCharge_eq_zero_iff hpx rho).mp hcharge
  · intro hhalf
    have hcharge : orbitwiseScaleSeamCharge ((p : ℕ) : ℝ) rho = 0 :=
      (orbitwiseScaleSeamCharge_eq_zero_iff hpx rho).mpr hhalf
    rw [hseam] at hcharge
    have : eulerParameterHessian p ((starRingEnd ℂ) rho) -
        eulerParameterHessian p (1 - rho) = 0 := by
      rw [hdiff, hcharge, zero_mul, zero_div]
    exact sub_eq_zero.mp this

/-! ## `(5)`–`(6)` The commutator of the logarithmic-position generator with the multiplier -/

/-- The commutator of `D = -i d/dt` with multiplication by `g` is multiplication by `-i g'`.
This is the whole differential content of the connection identity; no Hilbert-space structure is
used. -/
theorem commutator_logPosition_mul (g f : ℝ → ℂ) (gd fd : ℂ) (t : ℝ)
    (hg : HasDerivAt g gd t) (hf : HasDerivAt f fd t) :
    (-Complex.I) * deriv (fun u => g u * f u) t - g t * ((-Complex.I) * fd)
      = ((-Complex.I) * gd) * f t := by
  have hd : deriv (fun u => g u * f u) t = gd * f t + g t * fd := by
    have hmul : HasDerivAt (fun u => g u * f u) (gd * f t + g t * fd) t := hg.mul hf
    exact hmul.deriv
  rw [hd]
  ring

/-- **`(5)`: the commutator symbol of the one-prime multiplier is `g · Φ`.**  Equivalently
`[D, M_g] = M_g M_Φ`, with the finite von Mangoldt coefficients supplied by
`primeLogSource_hasSum`. -/
theorem commutator_symbol_criticalLineEulerLocalInverse (p : ℕ) (t : ℝ) :
    (-Complex.I) *
        (Complex.I * primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) *
          eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I))
      = eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I) *
          primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) := by
  have hI : (-Complex.I) * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  calc (-Complex.I) *
        (Complex.I * primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) *
          eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I))
      = ((-Complex.I) * Complex.I) * (primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) *
          eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I)) := by ring
    _ = eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I) *
          primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) := by
        rw [hI, one_mul, mul_comm]

/-! ## The finite-place connection identity on the common differentiable core -/

/-- The `t`-derivative of the finite-place multiplier on the critical line. -/
theorem hasDerivAt_criticalLineFinitePlaceMultiplier {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p)
    (t : ℝ) :
    HasDerivAt (fun u : ℝ => finitePlaceMultiplier S (1 / 2 + (u : ℂ) * Complex.I))
      (Complex.I * finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) *
        finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I)) t := by
  classical
  induction S using Finset.induction with
  | empty =>
      have hfun : (fun u : ℝ => finitePlaceMultiplier (∅ : Finset ℕ)
          (1 / 2 + (u : ℂ) * Complex.I)) = fun _ : ℝ => (1 : ℂ) := by
        funext u
        rw [finitePlaceMultiplier, Finset.prod_empty]
      rw [hfun]
      have hval : Complex.I * finitePlaceSource (∅ : Finset ℕ) (1 / 2 + (t : ℂ) * Complex.I) *
          finitePlaceMultiplier (∅ : Finset ℕ) (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
        rw [finitePlaceSource, Finset.sum_empty, mul_zero, zero_mul]
      rw [hval]
      exact hasDerivAt_const t (1 : ℂ)
  | insert p S hpS ih =>
      have hp : 2 ≤ p := hS p (Finset.mem_insert_self p S)
      have hSmem : ∀ q ∈ S, 2 ≤ q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hrest := ih hSmem
      have hfirst := hasDerivAt_criticalLineEulerLocalInverse hp t
      have hmul' : HasDerivAt
          (fun u : ℝ => eulerLocalInverse p (1 / 2 + (u : ℂ) * Complex.I) *
            finitePlaceMultiplier S (1 / 2 + (u : ℂ) * Complex.I))
          (Complex.I * primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) *
              eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I) *
              finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I) +
            eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I) *
              (Complex.I * finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) *
                finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I))) t :=
        hfirst.mul hrest
      have hfun : (fun u : ℝ => finitePlaceMultiplier (insert p S) (1 / 2 + (u : ℂ) * Complex.I))
          = fun u : ℝ => eulerLocalInverse p (1 / 2 + (u : ℂ) * Complex.I) *
              finitePlaceMultiplier S (1 / 2 + (u : ℂ) * Complex.I) := by
        funext u
        simp only [finitePlaceMultiplier]
        rw [Finset.prod_insert hpS]
      have hsum : finitePlaceSource (insert p S) (1 / 2 + (t : ℂ) * Complex.I)
          = primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) +
            finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) := by
        simp only [finitePlaceSource]
        rw [Finset.sum_insert hpS]
      have hprodins : finitePlaceMultiplier (insert p S) (1 / 2 + (t : ℂ) * Complex.I)
          = eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I) *
            finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I) := by
        simp only [finitePlaceMultiplier]
        rw [Finset.prod_insert hpS]
      have hval : Complex.I * finitePlaceSource (insert p S) (1 / 2 + (t : ℂ) * Complex.I) *
            finitePlaceMultiplier (insert p S) (1 / 2 + (t : ℂ) * Complex.I)
          = Complex.I * primeLogSource p (1 / 2 + (t : ℂ) * Complex.I) *
              eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I) *
              finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I) +
            eulerLocalInverse p (1 / 2 + (t : ℂ) * Complex.I) *
              (Complex.I * finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) *
                finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I)) := by
        rw [hsum, hprodins]
        ring
      rw [hfun, hval]
      exact hmul'

/-- **`(5)`–`(6)` on the common core.**  For every differentiable test function, the commutator of
the logarithmic-position generator `D = -i d/dt` with multiplication by the finite-place multiplier
is multiplication by `g_S · Φ_S`, whose Fourier coefficients are the finite von Mangoldt
coefficients. -/
theorem commutator_finitePlaceMultiplier {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p)
    (f : ℝ → ℂ) (fd : ℂ) (t : ℝ) (hf : HasDerivAt f fd t) :
    (-Complex.I) *
          deriv (fun u : ℝ =>
            finitePlaceMultiplier S (1 / 2 + (u : ℂ) * Complex.I) * f u) t -
        finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I) * ((-Complex.I) * fd)
      = finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I) *
          finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) * f t := by
  have hg := hasDerivAt_criticalLineFinitePlaceMultiplier hS t
  have hcomm := commutator_logPosition_mul
    (fun u : ℝ => finitePlaceMultiplier S (1 / 2 + (u : ℂ) * Complex.I)) f
    (Complex.I * finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) *
      finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I)) fd t hg hf
  rw [hcomm]
  have hI : (-Complex.I) * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  calc (-Complex.I) * (Complex.I * finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) *
        finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I)) * f t
      = ((-Complex.I) * Complex.I) *
          (finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) *
            finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I) * f t) := by ring
    _ = finitePlaceMultiplier S (1 / 2 + (t : ℂ) * Complex.I) *
          finitePlaceSource S (1 / 2 + (t : ℂ) * Complex.I) * f t := by
        rw [hI, one_mul]
        ring

end

end RHTower
