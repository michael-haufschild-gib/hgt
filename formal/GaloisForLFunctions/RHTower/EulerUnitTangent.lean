import GaloisForLFunctions.RHTower.EulerTruncationRigidity

/-!
# Actual-source Euler-unit tangents

This file isolates the exact infinitesimal family used by the prime Euler-unit
completeness theorem.  It contains no density hypothesis: the formulas, domain
of holomorphy, functional-equation parity, and parameter derivative are proved
directly for the genuine degree-one local Euler factor at `a = 1`.
-/

noncomputable section

namespace RHTower

open Complex

/-- The logarithmic flux of the degree-one local factor
`(1 - a * p^(-s))⁻¹`. -/
def degreeOneEulerLocalFlux (p : ℕ) (a s : ℂ) : ℂ :=
  (Real.log p : ℂ) * (a * (p : ℂ) ^ (-s)) /
    (1 - a * (p : ℂ) ^ (-s))

/-- The actual-source parameter tangent of the local logarithmic flux. -/
def primeEulerUnitTangent (p : ℕ) (s : ℂ) : ℂ :=
  (Real.log p : ℂ) * (p : ℂ) ^ (-s) /
    (1 - (p : ℂ) ^ (-s)) ^ 2

/-- The functional-equation-odd prime tangent. -/
def primeEulerUnitFETangent (p : ℕ) (s : ℂ) : ℂ :=
  primeEulerUnitTangent p s - primeEulerUnitTangent p (1 - s)

/-- The local denominator at the actual zeta parameter is nonzero throughout
the open right half-plane. -/
theorem one_sub_prime_cpow_neg_ne_zero {p : ℕ} (hp : 2 ≤ p)
    {s : ℂ} (hs : 0 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  exact eulerFactor_ne_zero hp hs

/-- The displayed prime tangent is exactly the complex derivative, at `a = 1`,
of the genuine local Euler logarithmic flux. -/
theorem hasDerivAt_degreeOneEulerLocalFlux_one {p : ℕ} (hp : 2 ≤ p)
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun a : ℂ ↦ degreeOneEulerLocalFlux p a s)
      (primeEulerUnitTangent p s) 1 := by
  let q : ℂ := (p : ℂ) ^ (-s)
  have hden : 1 - q ≠ 0 := by
    simpa only [q] using one_sub_prime_cpow_neg_ne_zero hp hs
  have hnum : HasDerivAt (fun a : ℂ ↦ a * q) q 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).mul_const q
  have hdenDeriv : HasDerivAt (fun a : ℂ ↦ 1 - a * q) (-q) 1 := by
    simpa using ((hasDerivAt_id (1 : ℂ)).mul_const q).const_sub 1
  have hquot := hnum.div hdenDeriv (by simpa using hden)
  have hscaled := hquot.const_mul (Real.log p : ℂ)
  have hderiv :
      (Real.log p : ℂ) *
          ((q * (1 - 1 * q) - 1 * q * (-q)) / (1 - 1 * q) ^ 2) =
        (Real.log p : ℂ) * q / (1 - q) ^ 2 := by
    field_simp [hden]
    ring
  convert hscaled.congr_deriv hderiv using 1
  funext a
  unfold degreeOneEulerLocalFlux
  dsimp only [q]
  simp only [Pi.div_apply]
  ring

/-- The actual-source tangent has the exact prime-power Lambert expansion used
by the completeness proof.  The `m = 0` summand is zero, so this is the same
series as `Σ_(m≥1) m (log p) p^(-m s)`. -/
theorem primeEulerUnitTangent_hasSum {p : ℕ} (hp : 2 ≤ p)
    {s : ℂ} (hs : 0 < s.re) :
    HasSum
      (fun m : ℕ ↦ (Real.log p : ℂ) * (m : ℂ) *
        ((p : ℂ) ^ (-s)) ^ m)
      (primeEulerUnitTangent p s) := by
  have hgeom := hasSum_coe_mul_geometric_of_norm_lt_one
    (norm_natCast_cpow_neg_lt_one hp hs)
  have hscaled := hgeom.mul_left (Real.log p : ℂ)
  convert hscaled using 1
  · funext m
    ring
  · unfold primeEulerUnitTangent
    ring

/-- The actual-source tangent is analytic at every point of the open right
half-plane. -/
theorem primeEulerUnitTangent_analyticAt {p : ℕ} (hp : 2 ≤ p)
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (primeEulerUnitTangent p) s := by
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow : AnalyticAt ℂ (fun z : ℂ ↦ (p : ℂ) ^ (-z)) s :=
    analyticAt_natCast_cpow_neg p hpc s
  have hden : 1 - (p : ℂ) ^ (-s) ≠ 0 :=
    one_sub_prime_cpow_neg_ne_zero hp hs
  unfold primeEulerUnitTangent
  exact (analyticAt_const.mul hpow).div
    ((analyticAt_const.sub hpow).pow 2) (pow_ne_zero 2 hden)

/-- The paired tangent is analytic throughout the open critical strip. -/
theorem primeEulerUnitFETangent_analyticAt {p : ℕ} (hp : 2 ≤ p)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    AnalyticAt ℂ (primeEulerUnitFETangent p) s := by
  have href : 0 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hleft := primeEulerUnitTangent_analyticAt hp hs0
  have hrightAt := primeEulerUnitTangent_analyticAt hp href
  have hreflection : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) s :=
    analyticAt_const.sub analyticAt_id
  unfold primeEulerUnitFETangent
  exact hleft.sub (hrightAt.comp hreflection)

/-- Functional-equation pairing makes the tangent exactly odd under
`s ↦ 1 - s`. -/
theorem primeEulerUnitFETangent_one_sub (p : ℕ) (s : ℂ) :
    primeEulerUnitFETangent p (1 - s) =
      -primeEulerUnitFETangent p s := by
  unfold primeEulerUnitFETangent
  ring_nf

/-- Every paired tangent vanishes at the functional-equation fixed point. -/
@[simp]
theorem primeEulerUnitFETangent_half (p : ℕ) :
    primeEulerUnitFETangent p (1 / 2 : ℂ) = 0 := by
  rw [primeEulerUnitFETangent]
  have hhalf : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
  rw [hhalf, sub_self]

/-- The actual-source prime tangent is Schwarz real. -/
theorem primeEulerUnitTangent_conj (p : ℕ) (s : ℂ) :
    primeEulerUnitTangent p (starRingEnd ℂ s) =
      starRingEnd ℂ (primeEulerUnitTangent p s) := by
  have harg : Complex.arg (p : ℂ) ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact ne_of_lt Real.pi_pos
  have hpow : (p : ℂ) ^ (-(starRingEnd ℂ s)) =
      starRingEnd ℂ ((p : ℂ) ^ (-s)) := by
    have h := Complex.conj_cpow (p : ℂ) (-s) harg
    have hc := congrArg (starRingEnd ℂ) h
    simpa using hc.symm
  unfold primeEulerUnitTangent
  rw [hpow]
  rw [map_div₀ (starRingEnd ℂ), map_mul, map_pow, map_sub, map_one]
  have hlog : (starRingEnd ℂ) (Real.log p : ℂ) = (Real.log p : ℂ) :=
    RCLike.conj_ofReal _
  rw [hlog]

/-- The FE-paired actual-source tangent is Schwarz real. -/
theorem primeEulerUnitFETangent_conj (p : ℕ) (s : ℂ) :
    primeEulerUnitFETangent p (starRingEnd ℂ s) =
      starRingEnd ℂ (primeEulerUnitFETangent p s) := by
  unfold primeEulerUnitFETangent
  rw [primeEulerUnitTangent_conj p]
  have hreflect : 1 - starRingEnd ℂ s = starRingEnd ℂ (1 - s) := by simp
  rw [hreflect, primeEulerUnitTangent_conj p]
  rw [map_sub]

end RHTower
