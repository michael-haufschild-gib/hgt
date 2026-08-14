import GaloisForLFunctions.RHTower.HedenmalmExteriorSourceNativePrimeWardClock

/-!
# Julia-phase source clock for the exterior reflection projector

The fixed-prime Ward clock has a lossless two-channel source realization before scalar Cayley
compression.  Its real coordinate is the normalized Hardy overlap and its imaginary coordinate is
the Ward displacement.  Source Julia--Pythagoras puts their complex combination on the unit circle.

Critical-line reflection takes this phase to its adjoint, while equality of phases retains the
full horizontal coordinate.  Consequently this genuine Julia-unitary phase replaces the scalar
Cayley phase in the mixed exterior projector without changing its reflected Pluecker-square or
fixed-center Abel landing.  This removes scalar clock provenance as the exterior source obstacle;
it does not assert the still-missing uniform source-row bound.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Normalized critical Hardy overlap paired with the fixed-prime Ward displacement. -/
def xiPrimeWardJuliaOverlap
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  mobiusCriticalTwoSidedUnitHardyGram
    (burnolXiPrimeCayleyAperture (xiDivisorSupportCanonicalCopy rho) p) 0

theorem xiPrimeWardJuliaOverlap_nonneg
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    0 ≤ xiPrimeWardJuliaOverlap p rho := by
  rw [xiPrimeWardJuliaOverlap, mobiusCriticalTwoSidedUnitHardyGram]
  have hu := burnolXiPrimeCayleyAperture_gt_neg_half
    (xiDivisorSupportCanonicalCopy rho) p
  have hden : 0 < 1 +
      burnolXiPrimeCayleyAperture (xiDivisorSupportCanonicalCopy rho) p + 0 := by
    linarith
  exact div_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hden.le

/-- Fixed-source Ward displacement and normalized Hardy overlap are one Julia unit vector. -/
theorem xiPrimeWardTranslationCoordinate_sq_add_JuliaOverlap_sq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    xiPrimeWardTranslationCoordinate p rho ^ 2 +
      xiPrimeWardJuliaOverlap p rho ^ 2 = 1 := by
  rw [xiPrimeWardTranslationCoordinate_eq_fixedSource]
  exact sq_mobiusCriticalTwoSidedCayleyDiscrepancy_add_sq_unitHardyGram
    (burnolXiPrimeCayleyAperture_gt_neg_half
      (xiDivisorSupportCanonicalCopy rho) p) (by norm_num)

/-- The Hardy-overlap channel is reflection-even. -/
theorem xiPrimeWardJuliaOverlap_lineConj
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    xiPrimeWardJuliaOverlap p (xiZeroLineConjEquiv rho) =
      xiPrimeWardJuliaOverlap p rho := by
  have href := xiPrimeWardTranslationCoordinate_sq_add_JuliaOverlap_sq
    p (xiZeroLineConjEquiv rho)
  have horig := xiPrimeWardTranslationCoordinate_sq_add_JuliaOverlap_sq p rho
  rw [xiPrimeWardTranslationCoordinate_lineConj] at href
  have hrefNonneg := xiPrimeWardJuliaOverlap_nonneg p (xiZeroLineConjEquiv rho)
  have horigNonneg := xiPrimeWardJuliaOverlap_nonneg p rho
  nlinarith

/-- Eigenphase of the genuine two-channel source Julia cell. -/
def xiPrimeWardJuliaPhase
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  (xiPrimeWardJuliaOverlap p rho : ℂ) +
    I * (xiPrimeWardTranslationCoordinate p rho : ℂ)

theorem normSq_xiPrimeWardJuliaPhase
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    Complex.normSq (xiPrimeWardJuliaPhase p rho) = 1 := by
  rw [xiPrimeWardJuliaPhase, Complex.normSq_apply]
  simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
    mul_zero, sub_zero, add_zero, add_im, mul_im, zero_add, one_mul]
  nlinarith [xiPrimeWardTranslationCoordinate_sq_add_JuliaOverlap_sq p rho]

theorem xiPrimeWardJuliaPhase_norm
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ‖xiPrimeWardJuliaPhase p rho‖ = 1 := by
  have hsq := normSq_xiPrimeWardJuliaPhase p rho
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (xiPrimeWardJuliaPhase p rho)]

/-- Critical-line reflection takes the Julia phase to its adjoint. -/
theorem xiPrimeWardJuliaPhase_lineConj
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    xiPrimeWardJuliaPhase p (xiZeroLineConjEquiv rho) =
      star (xiPrimeWardJuliaPhase p rho) := by
  rw [xiPrimeWardJuliaPhase, xiPrimeWardJuliaPhase,
    xiPrimeWardJuliaOverlap_lineConj,
    xiPrimeWardTranslationCoordinate_lineConj]
  apply Complex.ext <;> simp

theorem xiPrimeWardJuliaPhase_mul_lineConj
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    xiPrimeWardJuliaPhase p rho *
      xiPrimeWardJuliaPhase p (xiZeroLineConjEquiv rho) = 1 := by
  rw [xiPrimeWardJuliaPhase_lineConj]
  change xiPrimeWardJuliaPhase p rho *
      starRingEnd ℂ (xiPrimeWardJuliaPhase p rho) = 1
  rw [Complex.mul_conj, normSq_xiPrimeWardJuliaPhase]
  norm_num

/-- Julia phase retains the full horizontal Ward coordinate. -/
theorem eq_re_of_xiPrimeWardJuliaPhase_eq
    (p : Nat.Primes) {rho sigma : XiDivisorSupport}
    (h : xiPrimeWardJuliaPhase p rho = xiPrimeWardJuliaPhase p sigma) :
    (rho : ℂ).re = (sigma : ℂ).re := by
  apply eq_re_of_xiPrimeWardTranslationCoordinate_eq p
  have him := congrArg Complex.im h
  simpa [xiPrimeWardJuliaPhase] using him

/-- Two ordinate clocks plus the lossless Julia phase select exactly critical-line reflection. -/
theorem xiPrimeWardJuliaPhase_selector_iff
    (p : Nat.Primes) (rho sigma : XiDivisorSupport) :
    (xiHorizontalPrimePhase 2 (rho : ℂ).im =
        xiHorizontalPrimePhase 2 (sigma : ℂ).im ∧
      xiHorizontalPrimePhase 3 (rho : ℂ).im =
        xiHorizontalPrimePhase 3 (sigma : ℂ).im ∧
      xiPrimeWardJuliaPhase p rho * xiPrimeWardJuliaPhase p sigma = 1) ↔
      sigma = xiZeroLineConjEquiv rho := by
  constructor
  · rintro ⟨h2, h3, hu⟩
    have him : (rho : ℂ).im = (sigma : ℂ).im :=
      xiHorizontalPrimePhase_pair_injective (Prod.ext h2 h3)
    have href := xiPrimeWardJuliaPhase_mul_lineConj p rho
    have hne : xiPrimeWardJuliaPhase p rho ≠ 0 :=
      norm_ne_zero_iff.mp (by rw [xiPrimeWardJuliaPhase_norm]; norm_num)
    have hphase : xiPrimeWardJuliaPhase p sigma =
        xiPrimeWardJuliaPhase p (xiZeroLineConjEquiv rho) := by
      apply mul_left_cancel₀ hne
      exact hu.trans href.symm
    apply Subtype.ext
    apply Complex.ext
    · exact eq_re_of_xiPrimeWardJuliaPhase_eq p hphase
    · simpa [xiZeroLineConjEquiv_apply] using him.symm
  · intro hsigma
    subst sigma
    exact ⟨
      congrArg (xiHorizontalPrimePhase 2) (by simp [xiZeroLineConjEquiv_apply]),
      congrArg (xiHorizontalPrimePhase 3) (by simp [xiZeroLineConjEquiv_apply]),
      xiPrimeWardJuliaPhase_mul_lineConj p rho⟩

/-- Mixed pair projector whose third clock is the full source Julia eigenphase. -/
def xiPrimeWardJuliaExteriorReflectionProjector
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (C : XiDivisorSupport → XiDivisorSupport → ℂ) (N : ℕ) : ℂ :=
  finiteExteriorReflectionProjector S C
    (fun rho => xiHorizontalPrimePhase 2 (rho : ℂ).im)
    (fun rho => xiHorizontalPrimePhase 3 (rho : ℂ).im)
    (xiPrimeWardJuliaPhase p) N

theorem tendsto_xiPrimeWardJuliaExteriorReflectionProjector
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (C : XiDivisorSupport → XiDivisorSupport → ℂ) :
    Tendsto (xiPrimeWardJuliaExteriorReflectionProjector p S C) atTop
      (nhds (∑ rho ∈ S, ∑ sigma ∈ S,
        if sigma = xiZeroLineConjEquiv rho then C rho sigma else 0)) := by
  have hlim := tendsto_finiteExteriorReflectionProjector S C
    (fun rho => xiHorizontalPrimePhase 2 (rho : ℂ).im)
    (fun rho => xiHorizontalPrimePhase 3 (rho : ℂ).im)
    (xiPrimeWardJuliaPhase p)
    (fun rho _ => xiHorizontalPrimePhase_norm 2 (rho : ℂ).im)
    (fun rho _ => xiHorizontalPrimePhase_norm 3 (rho : ℂ).im)
    (fun rho _ => xiPrimeWardJuliaPhase_norm p rho)
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    apply Finset.sum_congr rfl
    intro rho hrho
    apply Finset.sum_congr rfl
    intro sigma hsigma
    simp only [xiPrimeWardJuliaPhase_selector_iff]

/-- Exterior determinant driven by the source Julia eigenphase. -/
def xiPrimeWardJuliaExteriorReflectionDeterminant
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (r f g : XiDivisorSupport → ℂ) (a b c : ℕ) : ℂ :=
  finiteExteriorReflectionDeterminant S r f g
    (fun rho => xiHorizontalPrimePhase 2 (rho : ℂ).im)
    (fun rho => xiHorizontalPrimePhase 3 (rho : ℂ).im)
    (xiPrimeWardJuliaPhase p) a b c

/-- Julia-phase exterior projection has the same reflected Pluecker-square landing as every
faithful mixed clock. -/
theorem tendsto_xiPrimeWardJuliaExteriorReflectionDeterminant
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S)
    (r f g : XiDivisorSupport → ℂ) :
    Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeWardJuliaExteriorReflectionDeterminant p S r f g a b c)
      atTop
      (nhds ((1 / 2 : ℂ) * ∑ rho ∈ S,
        r rho * r (xiZeroLineConjEquiv rho) *
          (f rho * g (xiZeroLineConjEquiv rho) -
            f (xiZeroLineConjEquiv rho) * g rho) ^ 2)) := by
  let C : XiDivisorSupport → XiDivisorSupport → ℂ := fun rho sigma =>
    r rho * r sigma * (f rho * g sigma) *
      (f rho * g sigma - f sigma * g rho)
  have hprojector := tendsto_xiPrimeWardJuliaExteriorReflectionProjector p S C
  have hdet : Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeWardJuliaExteriorReflectionDeterminant p S r f g a b c)
      atTop
      (nhds (∑ rho ∈ S, ∑ sigma ∈ S,
        if sigma = xiZeroLineConjEquiv rho then C rho sigma else 0)) := by
    apply hprojector.congr'
    filter_upwards with N
    rw [xiPrimeWardJuliaExteriorReflectionProjector,
      finiteExteriorReflectionProjector_eq_detCesaro]
    rfl
  rw [xiExteriorReflectionSelectedPairSum_eq S hclosed C] at hdet
  have hsym := xiReflectionOrientedMinor_sum_eq_half_square S hclosed r f g
  have hlimitEq :
      (∑ rho ∈ S, C rho (xiZeroLineConjEquiv rho)) =
        (1 / 2 : ℂ) * ∑ rho ∈ S,
          r rho * r (xiZeroLineConjEquiv rho) *
            (f rho * g (xiZeroLineConjEquiv rho) -
              f (xiZeroLineConjEquiv rho) * g rho) ^ 2 := by
    simpa only [C] using hsym
  rw [hlimitEq] at hdet
  exact hdet

/-- Fixed-feature Abel determinant with the lossless source Julia clock. -/
def xiPrimeWardJuliaExteriorAbelDeterminant
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (R t : ℝ) (a b c : ℕ) : ℂ :=
  xiPrimeWardJuliaExteriorReflectionDeterminant p S
    (xiExteriorAbelRowWeight R)
    (xiCriticalFeatureSpectralValue t)
    (xiCriticalFeatureSpectralValue (t + 1)) a b c

/-- The lossless Julia clock lands on exactly the same fixed-center positive exterior energy. -/
theorem tendsto_xiPrimeWardJuliaExteriorAbelDeterminant_one
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S)
    (t : ℝ) :
    Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeWardJuliaExteriorAbelDeterminant p S 1 t a b c)
      atTop
      (nhds (((1 / 2 : ℝ) *
        xiExteriorCayleyAbelFixedPacketEnergy S 1 t : ℝ) : ℂ)) := by
  have hlim := tendsto_xiPrimeWardJuliaExteriorReflectionDeterminant p S hclosed
    (xiExteriorAbelRowWeight 1)
    (xiCriticalFeatureSpectralValue t)
    (xiCriticalFeatureSpectralValue (t + 1))
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    rw [xiExteriorCayleyAbelFixedPacketEnergy]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [xiExteriorBoundaryReflectedMinor_eq_normSq,
      xiExteriorAbelRowWeight_mul_wedge_eq_fixedCoefficient]

end

end RHTower
