import GaloisForLFunctions.RHTower.CriticalDiscEulerOrbitDensity
import GaloisForLFunctions.RHTower.XiPrimeSeamReflectionEnergy

/-!
# The Xi horizontal prime seam as an empty-parameter Euler tangent

The canonical seam square energy depends only on the horizontal coordinate.  This file identifies
its height-free representative with the first coefficient, at local parameter `a = 0`, of the
genuine FE-paired degree-one Euler flux

`log p * (a p^{-s} / (1 - a p^{-s}) - a p^{-(1-s)} / (1 - a p^{-(1-s)}))`.

The same differentiation is proved in the compact-carrier Banach algebra used by the nonlinear
Euler-orbit density theorem.  Thus the weighted one-particle seam has a source-defined finite
coefficient realization.  No cofinal Calkin estimate, Xi zero-location input, or RH assumption is
used here.
-/

noncomputable section

namespace RHTower

open Complex Metric Set Filter Topology ComplexConjugate

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- At the empty local parameter, the Banach-algebra Mobius flux has first coefficient `q`. -/
theorem hasDerivAt_compactMobiusFlux_zero (q : C(K, ℂ)) :
    HasDerivAt (compactMobiusFlux q) q 0 := by
  have hnum : HasDerivAt (fun a : ℂ ↦ a • q) q 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const q
  have hden : HasDerivAt (fun a : ℂ ↦ 1 - a • q) (-q) 0 := by
    simpa using hnum.const_sub 1
  have hinvBase : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ C(K, ℂ) 1 1) 1 := by
    simpa using (hasFDerivAt_ringInverse (𝕜 := ℂ) (1 : C(K, ℂ)ˣ))
  have hinvBase' : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ C(K, ℂ) 1 1)
        (1 - (0 : ℂ) • q) := by
    simpa using hinvBase
  have hinv := hinvBase'.comp (0 : ℂ) hden.hasFDerivAt
  have hprod := hnum.hasFDerivAt.mul hinv
  show HasFDerivAt (compactMobiusFlux q)
    (ContinuousLinearMap.toSpanSingleton ℂ q) 0
  convert hprod using 1
  ext c
  simp

/-- FE-paired degree-one Euler flux on a compact carrier, before choosing a local parameter. -/
def compactDegreeOneEulerFEFlux
    (q : C(K, ℂ)) (tau : C(K, K)) (p : ℕ) (a : ℂ) : C(K, ℂ) :=
  compactDegreeOneEulerLocalFlux q p a -
    compactDegreeOneEulerLocalFlux (q.comp tau) p a

/-- The empty-parameter FE tangent in the compact Banach algebra. -/
def compactDegreeOneEulerZeroFETangent
    (q : C(K, ℂ)) (tau : C(K, K)) (p : ℕ) : C(K, ℂ) :=
  (Real.log p : ℂ) • (q - q.comp tau)

theorem hasDerivAt_compactDegreeOneEulerLocalFlux_zero
    (q : C(K, ℂ)) (p : ℕ) :
    HasDerivAt (compactDegreeOneEulerLocalFlux q p)
      ((Real.log p : ℂ) • q) 0 := by
  exact (hasDerivAt_compactMobiusFlux_zero q).const_smul (Real.log p : ℂ)

/-- The first finite coefficient of the compact FE-paired Euler source is its literal degree-one
reflection difference. -/
theorem hasDerivAt_compactDegreeOneEulerFEFlux_zero
    (q : C(K, ℂ)) (tau : C(K, K)) (p : ℕ) :
    HasDerivAt (compactDegreeOneEulerFEFlux q tau p)
      (compactDegreeOneEulerZeroFETangent q tau p) 0 := by
  have h := (hasDerivAt_compactDegreeOneEulerLocalFlux_zero q p).sub
      (hasDerivAt_compactDegreeOneEulerLocalFlux_zero (q.comp tau) p)
  convert h using 1
  simp only [compactDegreeOneEulerZeroFETangent]
  module

theorem compactDegreeOneEulerZeroFETangent_exponential_apply
    (s : C(K, ℂ)) (tau : C(K, K)) (p : ℕ) (k : K) :
    compactDegreeOneEulerZeroFETangent
        (compactExponentialTest s (Real.log p)) tau p k =
      (Real.log p : ℂ) *
        (Complex.exp (-(Real.log p : ℂ) * s k) -
          Complex.exp (-(Real.log p : ℂ) * s (tau k))) := by
  simp [compactDegreeOneEulerZeroFETangent, compactExponentialTest_apply]

/-- Scalar FE-paired local Euler flux.  This is the pointwise source formula whose first
coefficient is compared with the Xi seam below. -/
def degreeOneEulerFEFlux (p : ℕ) (s a : ℂ) : ℂ :=
  let q := (((p : ℝ) : ℂ) ^ (-s))
  let qFE := (((p : ℝ) : ℂ) ^ (-(1 - s)))
  (Real.log p : ℂ) *
    (a * q / (1 - a * q) - a * qFE / (1 - a * qFE))

private theorem hasDerivAt_scalarMobius_zero (q : ℂ) :
    HasDerivAt (fun a : ℂ => a * q / (1 - a * q)) q 0 := by
  have hnum : HasDerivAt (fun a : ℂ => a * q) q 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const q
  have hden : HasDerivAt (fun a : ℂ => 1 - a * q) (-q) 0 := by
    simpa using hnum.const_sub 1
  have hdiv := hnum.div hden (by simp)
  convert hdiv using 1
  all_goals simp

/-- Exact first coefficient of the scalar FE-paired Euler source. -/
theorem hasDerivAt_degreeOneEulerFEFlux_zero (p : ℕ) (s : ℂ) :
    HasDerivAt (degreeOneEulerFEFlux p s)
      ((Real.log p : ℂ) *
        ((((p : ℝ) : ℂ) ^ (-s)) - (((p : ℝ) : ℂ) ^ (-(1 - s))))) 0 := by
  let q := (((p : ℝ) : ℂ) ^ (-s))
  let qFE := (((p : ℝ) : ℂ) ^ (-(1 - s)))
  have h := (hasDerivAt_scalarMobius_zero q).sub
    (hasDerivAt_scalarMobius_zero qFE)
  have hs := h.const_mul (Real.log p : ℂ)
  change HasDerivAt
    (fun a : ℂ => (Real.log p : ℂ) *
      (a * q / (1 - a * q) - a * qFE / (1 - a * qFE)))
    ((Real.log p : ℂ) * (q - qFE)) 0
  exact hs

/-- On the real axis the first Euler coefficient is exactly the canonical horizontal Xi seam. -/
theorem degreeOneEulerFEFlux_deriv_zero_eq_horizontalPrimeSeam
    (p : ℕ) (sigma : ℝ) :
    deriv (degreeOneEulerFEFlux p (sigma : ℂ)) 0 =
      orbitwiseNatPrimeSeamCharge p (sigma : ℂ) := by
  rw [(hasDerivAt_degreeOneEulerFEFlux_zero p (sigma : ℂ)).deriv]
  simp [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge]

/-- Per prime, the first-coefficient energy at the horizontal projection of `rho` equals the
original FE--Schwarz seam energy at `rho`. -/
theorem degreeOneEulerFEFlux_deriv_zero_weighted_norm_sq_eq_primeSeam
    (rho : ℂ) (p : Nat.Primes) :
    ‖deriv (degreeOneEulerFEFlux (p : ℕ) (rho.re : ℂ)) 0‖ ^ 2 / (p : ℝ) =
      ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ) := by
  rw [degreeOneEulerFEFlux_deriv_zero_eq_horizontalPrimeSeam]
  exact orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_of_re_eq (by simp) p

/-- The total empty-parameter Euler first-coefficient energy on the horizontal projection. -/
def degreeOneEulerFEFirstCoefficientEnergy (rho : ℂ) : ℝ :=
  ∑' p : Nat.Primes,
    ‖deriv (degreeOneEulerFEFlux (p : ℕ) (rho.re : ℂ)) 0‖ ^ 2 / (p : ℝ)

/-- The source-defined finite-coefficient energy is exactly the Xi prime-seam reflection
distance. -/
theorem degreeOneEulerFEFirstCoefficientEnergy_eq_primeSeamWeightedNormSq
    (rho : ℂ) :
    degreeOneEulerFEFirstCoefficientEnergy rho = orbitwisePrimeSeamWeightedNormSq rho := by
  unfold degreeOneEulerFEFirstCoefficientEnergy orbitwisePrimeSeamWeightedNormSq
  apply tsum_congr
  exact degreeOneEulerFEFlux_deriv_zero_weighted_norm_sq_eq_primeSeam rho

/-- Quantitative consequence: this source coefficient controls horizontal displacement from the
critical line. -/
theorem horizontalDisplacement_sq_mul_log_two_pow_four_le_degreeOneEulerFEFirstCoefficientEnergy
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    (rho.re - 1 / 2) ^ 2 * (Real.log 2) ^ 4 ≤
      degreeOneEulerFEFirstCoefficientEnergy rho := by
  rw [degreeOneEulerFEFirstCoefficientEnergy_eq_primeSeamWeightedNormSq]
  exact horizontalDisplacement_sq_mul_log_two_pow_four_le_orbitwisePrimeSeamWeightedNormSq hstrip

end RHTower
