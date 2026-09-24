import GaloisForLFunctions.RHTower.MobiusReciprocalGammaFrequency

/-!
# Finite reciprocal-moment transfer between source orders

The Gamma height density at shape `p + 2` dominates that at shape `p` up to
`(p + 1) / p`. Finite phase-polynomial integrability converts this pointwise
comparison into a positive-semidefinite order law. The identical Möbius
polynomial appears at every reciprocal order; only the Gamma shape changes.
-/

open Finset Complex MeasureTheory
open scoped ComplexConjugate
namespace RHTower
noncomputable section

/-- The Gamma-weighted squared norm of every finite phase polynomial is integrable. -/
theorem integrable_gammaPhasePolynomial_normSq_density
    (S : Finset ℕ) (a freq : ℕ → ℝ) {p : ℝ} (hp : 0 < p) :
    Integrable (fun t : ℝ =>
      Complex.normSq (gammaPhasePolynomial S a freq t) *
        gammaHeightDensity p t) := by
  have hpair (u : ℝ) :
      Integrable (fun t : ℝ =>
        Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
          (gammaHeightDensity p t : ℂ)) := by
    simpa [gammaEulerTiltedDensity, gammaEulerFiniteWeight] using
      integrable_cexp_mul_gammaEulerTiltedDensity hp [] u
  have hterm (m n : ℕ) :
      Integrable (fun t : ℝ =>
        ((a m : ℂ) * (a n : ℂ)) *
          (Complex.exp (((t * (freq m - freq n) : ℝ) : ℂ) * Complex.I) *
            (gammaHeightDensity p t : ℂ))) :=
    (hpair _).const_mul _
  have hpoint (t : ℝ) :
      ((Complex.normSq (gammaPhasePolynomial S a freq t) : ℝ) : ℂ) *
          (gammaHeightDensity p t : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S,
          ((a m : ℂ) * (a n : ℂ)) *
            (Complex.exp (((t * (freq m - freq n) : ℝ) : ℂ) * Complex.I) *
              (gammaHeightDensity p t : ℂ)) := by
    rw [gammaPhasePolynomial_normSq_eq_pairSum]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hsum : Integrable (fun t : ℝ =>
      ∑ m ∈ S, ∑ n ∈ S,
        ((a m : ℂ) * (a n : ℂ)) *
          (Complex.exp (((t * (freq m - freq n) : ℝ) : ℂ) * Complex.I) *
            (gammaHeightDensity p t : ℂ))) :=
    integrable_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => hterm m n))
  have hc : Integrable (fun t : ℝ =>
      ((Complex.normSq (gammaPhasePolynomial S a freq t) : ℝ) : ℂ) *
        (gammaHeightDensity p t : ℂ)) :=
    hsum.congr (Filter.Eventually.of_forall fun t => (hpoint t).symm)
  simpa [← Complex.ofReal_mul] using hc.re

/-- A two-step rise in Gamma shape controls the preceding finite Gram energy. -/
theorem integral_gammaPhasePolynomial_normSq_le_succ_two
    (S : Finset ℕ) (a freq : ℕ → ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ t : ℝ,
      Complex.normSq (gammaPhasePolynomial S a freq t) *
        gammaHeightDensity p t) ≤
      ((p + 1) / p) *
        (∫ t : ℝ,
          Complex.normSq (gammaPhasePolynomial S a freq t) *
            gammaHeightDensity (p + 2) t) := by
  have hp2 : 0 < p + 2 := by linarith
  have hi := integrable_gammaPhasePolynomial_normSq_density S a freq hp2
  have hc : Integrable (fun t : ℝ =>
      ((p + 1) / p) *
        (Complex.normSq (gammaPhasePolynomial S a freq t) *
          gammaHeightDensity (p + 2) t)) := hi.const_mul _
  have hnonneg : ∀ᵐ t : ℝ, 0 ≤
      Complex.normSq (gammaPhasePolynomial S a freq t) *
        gammaHeightDensity p t := by
    filter_upwards with t
    exact mul_nonneg (Complex.normSq_nonneg _) (gammaHeightDensity_nonneg hp t)
  have hle : ∀ᵐ t : ℝ,
      Complex.normSq (gammaPhasePolynomial S a freq t) *
        gammaHeightDensity p t ≤
      ((p + 1) / p) *
        (Complex.normSq (gammaPhasePolynomial S a freq t) *
          gammaHeightDensity (p + 2) t) := by
    filter_upwards with t
    have h := mul_le_mul_of_nonneg_left (gammaHeightDensity_le_succ_two hp t)
      (Complex.normSq_nonneg (gammaPhasePolynomial S a freq t))
    nlinarith [h]
  have h := integral_mono_of_nonneg hnonneg hc hle
  simpa only [integral_const_mul] using h

/-- Full signed finite reciprocal moment at arbitrary real source order. -/
def finiteGeneralReciprocalEnergy (R δ : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    mobiusRealCoefficient m * mobiusRealCoefficient n *
      generalReciprocalMomentKernel R δ m n

/-- Every reciprocal order has the same finite Möbius polynomial, with shape
`2R - 1 - δ` in the Gamma-frequency density. -/
theorem finiteGeneralReciprocalEnergy_eq_gammaPolynomialIntegral
    (R δ : ℝ) (hp : 0 < 2 * R - 1 - δ) (N : ℕ) :
    (finiteGeneralReciprocalEnergy R δ N : ℂ) =
      (Real.rpow 2 (-(2 * R - 1 - δ)) : ℂ) *
        (∫ t : ℝ,
          ((Complex.normSq (finiteCubicMobiusPolynomial δ N t) : ℝ) : ℂ) *
            (gammaHeightDensity (2 * R - 1 - δ) t : ℂ)) := by
  let S := Finset.Icc 1 N
  let a := cubicMomentDirichletWeight δ
  let freq : ℕ → ℝ := fun n => Real.log (n : ℝ)
  have hgram := integral_gammaPhasePolynomial_normSq_eq_pairSum S a freq hp
  have hkernel (m n : ℕ) (hm : m ∈ S) (hn : n ∈ S) :
      generalReciprocalStationaryKernel R δ m n =
        Real.rpow 2 (-(2 * R - 1 - δ)) *
          Real.cosh ((freq m - freq n) / 2) ^ (-(2 * R - 1 - δ)) := by
    have hmR : (0 : ℝ) < m := by
      exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast (Finset.mem_Icc.mp hn).1
    simpa [generalReciprocalStationaryKernel, freq] using
      ratio_kernel_eq_cosh hmR hnR (2 * R - 1 - δ)
  change (finiteGeneralReciprocalEnergy R δ N : ℂ) =
    (Real.rpow 2 (-(2 * R - 1 - δ)) : ℂ) *
      (∫ t : ℝ,
        ((Complex.normSq (gammaPhasePolynomial S a freq t) : ℝ) : ℂ) *
          (gammaHeightDensity (2 * R - 1 - δ) t : ℂ))
  rw [hgram]
  unfold finiteGeneralReciprocalEnergy
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hmpos := (Finset.mem_Icc.mp hm).1
  have hnpos := (Finset.mem_Icc.mp hn).1
  rw [generalReciprocalMomentKernel_eq_stationary R δ hmpos hnpos,
    hkernel m n hm hn]
  unfold a cubicMomentDirichletWeight
  push_cast
  ring

/-- Real Gamma-frequency representation of the full signed finite moment. -/
theorem finiteGeneralReciprocalEnergy_eq_realGammaIntegral
    (R δ : ℝ) (hp : 0 < 2 * R - 1 - δ) (N : ℕ) :
    finiteGeneralReciprocalEnergy R δ N =
      Real.rpow 2 (-(2 * R - 1 - δ)) *
        (∫ t : ℝ,
          Complex.normSq (finiteCubicMobiusPolynomial δ N t) *
            gammaHeightDensity (2 * R - 1 - δ) t) := by
  have h := finiteGeneralReciprocalEnergy_eq_gammaPolynomialIntegral R δ hp N
  have hr := congrArg Complex.re h
  simpa [integral_complex_ofReal, ← Complex.ofReal_mul] using hr

/-- The next reciprocal source order controls the preceding finite moment.
The constant includes the exact `2^(-p)` normalization. -/
theorem finiteGeneralReciprocalEnergy_le_succ
    (R δ : ℝ) (hp : 0 < 2 * R - 1 - δ) (N : ℕ) :
    finiteGeneralReciprocalEnergy R δ N ≤
      (4 * ((2 * R - δ) / (2 * R - 1 - δ))) *
        finiteGeneralReciprocalEnergy (R + 1) δ N := by
  let p : ℝ := 2 * R - 1 - δ
  have hp' : 0 < p := hp
  have hshape : 2 * (R + 1) - 1 - δ = p + 2 := by
    dsimp [p]
    ring
  have hnum : 2 * R - δ = p + 1 := by
    dsimp [p]
    ring
  have hpow : Real.rpow 2 (-p) =
      4 * Real.rpow 2 (-(p + 2)) := by
    change (2 : ℝ) ^ (-p) = 4 * (2 : ℝ) ^ (-(p + 2))
    rw [show -p = -(p + 2) + 2 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring
  let S := Finset.Icc 1 N
  let a := cubicMomentDirichletWeight δ
  let freq : ℕ → ℝ := fun n => Real.log (n : ℝ)
  have hcomp := integral_gammaPhasePolynomial_normSq_le_succ_two S a freq hp'
  rw [finiteGeneralReciprocalEnergy_eq_realGammaIntegral R δ hp N,
    finiteGeneralReciprocalEnergy_eq_realGammaIntegral (R + 1) δ
      (by rw [hshape]; linarith) N,
    hshape, hnum]
  change Real.rpow 2 (-p) *
      (∫ t : ℝ,
        Complex.normSq (gammaPhasePolynomial S a freq t) *
          gammaHeightDensity p t) ≤
    (4 * ((p + 1) / p)) *
      (Real.rpow 2 (-(p + 2)) *
        (∫ t : ℝ,
          Complex.normSq (gammaPhasePolynomial S a freq t) *
            gammaHeightDensity (p + 2) t))
  calc
    _ ≤ Real.rpow 2 (-p) *
        (((p + 1) / p) *
          (∫ t : ℝ,
            Complex.normSq (gammaPhasePolynomial S a freq t) *
              gammaHeightDensity (p + 2) t)) :=
      mul_le_mul_of_nonneg_left hcomp (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [hpow]; ring

end
end RHTower
