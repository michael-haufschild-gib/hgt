import GaloisForLFunctions.RHTower.SuzukiGammaHalfLineClassification
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Variation of constants for the forced Gamma transport

For the forced equation

`f' = [-1/(2η) + (i/2)(r(η)I - T)]f + b`

the exact integrating factor `η^{1/2}Q(η)^{-1}` turns the homogeneous part into zero and leaves
only the forcing:

`(η^{1/2}Q(η)^{-1}f(η))' = η^{1/2}Q(η)^{-1}b(η)`.

Integrating gives the variation-of-constants representation, and the resulting particular solution
is `O(η)` near the origin: the half-power weight of the homogeneous branch is cancelled by the
`η^{1/2}` of the integrating factor, so the forcing contributes no half-log branch.
-/

open Complex Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {Rint r : ℝ → ℝ} {T : X →L[ℂ] X}

/-- The forced integrating factor. -/
def forcedFactor (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (f : ℝ → X) (η : ℝ) : X :=
  (η ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T η (f η))

/-- **The integrating factor absorbs the homogeneous part exactly.** -/
theorem hasDerivAt_forcedFactor {f f' b : ℝ → X} {η : ℝ} (hη : 0 < η)
    (hRint : HasDerivAt Rint (r η) η) (hf : HasDerivAt f (f' η) η)
    (hode : f' η = ((((-(1 / (2 * η)) : ℝ)) : ℂ)) • f η
      + I • (shiftedSymbolOp (r η / 2) T (f η)) + b η) :
    HasDerivAt (forcedFactor Rint T f)
      ((η ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T η (b η))) η := by
  have hQ := hasDerivAt_gammaTransportInv (T := T) (r := r) hRint
  have happ := hasDerivAt_clm_apply hQ hf
  have hpow : HasDerivAt (fun y : ℝ => y ^ ((1:ℝ)/2)) ((1:ℝ)/2 * η ^ ((1:ℝ)/2 - 1)) η :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hη))
  have hg := hpow.smul happ
  have hcomm := commute_shiftedSymbolOp_gammaTransportInv (T := T) (Rint := Rint) (r η / 2) η
  have hterm1 : (-(I • (shiftedSymbolOp (r η / 2) T * gammaTransportInv Rint T η))) (f η)
      = -(I • (gammaTransportInv Rint T η (shiftedSymbolOp (r η / 2) T (f η)))) := by
    rw [hcomm]
    rfl
  have hterm2 : gammaTransportInv Rint T η (f' η)
      = ((((-(1 / (2 * η)) : ℝ)) : ℂ)) • (gammaTransportInv Rint T η (f η))
        + I • (gammaTransportInv Rint T η (shiftedSymbolOp (r η / 2) T (f η)))
        + gammaTransportInv Rint T η (b η) := by
    rw [hode, map_add, map_add, map_smul, map_smul]
  have hsum : (-(I • (shiftedSymbolOp (r η / 2) T * gammaTransportInv Rint T η))) (f η)
      + gammaTransportInv Rint T η (f' η)
      = ((-(1 / (2 * η)) : ℝ)) • (gammaTransportInv Rint T η (f η))
        + gammaTransportInv Rint T η (b η) := by
    rw [hterm1, hterm2, ofReal_smul_eq]
    abel
  have hscal : (η ^ ((1:ℝ)/2)) * (-(1 / (2 * η)) : ℝ) + (1:ℝ)/2 * η ^ ((1:ℝ)/2 - 1) = 0 := by
    have hsub : η ^ ((1:ℝ)/2 - 1) = η ^ ((1:ℝ)/2) / η ^ (1:ℝ) := Real.rpow_sub hη _ _
    rw [hsub, Real.rpow_one]
    field_simp
    ring
  have hval : (η ^ ((1:ℝ)/2)) •
        ((-(I • (shiftedSymbolOp (r η / 2) T * gammaTransportInv Rint T η))) (f η)
          + gammaTransportInv Rint T η (f' η))
      + ((1:ℝ)/2 * η ^ ((1:ℝ)/2 - 1)) • (gammaTransportInv Rint T η (f η))
      = (η ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T η (b η)) := by
    rw [hsum, smul_add, smul_smul]
    rw [show (η ^ ((1:ℝ)/2)) * (-(1 / (2 * η)) : ℝ)
        = -((1:ℝ)/2 * η ^ ((1:ℝ)/2 - 1)) from by linarith [hscal]]
    rw [neg_smul]
    abel
  rw [← hval]
  exact hg

/-- **Variation of constants for the forced Gamma transport.** -/
theorem forced_representation {f f' b : ℝ → X} {η₀ η : ℝ} (hη : 0 < η)
    (hRint : ∀ x : ℝ, 0 < x → HasDerivAt Rint (r x) x)
    (hf : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hode : ∀ x : ℝ, 0 < x → f' x = ((((-(1 / (2 * x)) : ℝ)) : ℂ)) • f x
      + I • (shiftedSymbolOp (r x / 2) T (f x)) + b x)
    (hbc : ContinuousOn (fun s : ℝ => (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s)))
      (uIcc η₀ η))
    (hpos : ∀ s ∈ uIcc η₀ η, 0 < s) :
    f η = (η ^ (-(1:ℝ)/2)) • gammaTransport Rint T η
      (forcedFactor Rint T f η₀
        + ∫ s in η₀..η, (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s))) := by
  have hderiv : ∀ s ∈ uIcc η₀ η, HasDerivAt (forcedFactor Rint T f)
      ((s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s))) s := by
    intro s hs
    exact hasDerivAt_forcedFactor (hpos s hs) (hRint s (hpos s hs)) (hf s (hpos s hs))
      (hode s (hpos s hs))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hbc.intervalIntegrable
  have hgη : forcedFactor Rint T f η
      = forcedFactor Rint T f η₀
        + ∫ s in η₀..η, (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s)) := by
    rw [hftc]
    abel
  have hpowmul : (η ^ (-(1:ℝ)/2)) * (η ^ ((1:ℝ)/2)) = 1 := by
    rw [← Real.rpow_add hη]
    norm_num
  have hstep : gammaTransportInv Rint T η (f η)
      = (η ^ (-(1:ℝ)/2)) • (forcedFactor Rint T f η) := by
    rw [forcedFactor, smul_smul, hpowmul, one_smul]
  have h2 := congrArg (gammaTransport Rint T η) hstep
  rw [gammaTransport_apply_inv_apply, map_real_smul] at h2
  rw [hgη] at h2
  exact h2

section Hilbert

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [Nontrivial Y]

/-- **The forced particular solution has no half-log branch.**  Near the origin it is `O(η)`, so it
contributes nothing to the critical `η^{-1/2}` coefficient. -/
theorem norm_particular_le {Rint : ℝ → ℝ} {T : Y →L[ℂ] Y} {b : ℝ → Y} {A Mb η : ℝ}
    (hT : IsSelfAdjoint T)
    (hb : ∀ s ∈ Icc (0:ℝ) A, ‖b s‖ ≤ Mb)
    (hη : 0 < η) (hηA : η ≤ A) :
    ‖(η ^ (-(1:ℝ)/2)) • gammaTransport Rint T η
        (∫ s in (0:ℝ)..η, (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s)))‖
      ≤ (2/3) * Mb * η := by
  have hTneg : IsSelfAdjoint (-T) := hT.neg
  have hQnorm : ‖gammaTransport Rint T η‖ = 1 := norm_freqPropagator hT 0 Rint η
  have hQinv : ∀ s : ℝ, ‖gammaTransportInv Rint T s‖ = 1 := fun s =>
    norm_freqPropagator hTneg 0 (fun x => -Rint x) s
  have hIcc : uIcc (0:ℝ) η = Icc 0 η := uIcc_of_le hη.le
  have hptwise : ∀ s ∈ Icc (0:ℝ) η,
      ‖(s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s))‖ ≤ Mb * s ^ ((1:ℝ)/2) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := hs.1
    have hbs : ‖b s‖ ≤ Mb := hb s ⟨hs0, le_trans hs.2 hηA⟩
    have hop : ‖gammaTransportInv Rint T s (b s)‖ ≤ ‖b s‖ := by
      have h := ContinuousLinearMap.le_opNorm (gammaTransportInv Rint T s) (b s)
      rwa [hQinv s, one_mul] at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    calc s ^ ((1:ℝ)/2) * ‖gammaTransportInv Rint T s (b s)‖
        ≤ s ^ ((1:ℝ)/2) * Mb := by
          exact mul_le_mul_of_nonneg_left (le_trans hop hbs) (Real.rpow_nonneg hs0 _)
      _ = Mb * s ^ ((1:ℝ)/2) := by ring
  have hmajor : IntervalIntegrable (fun s : ℝ => Mb * s ^ ((1:ℝ)/2)) volume 0 η :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul Mb
  have hnorm : ‖∫ s in (0:ℝ)..η, (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s))‖
      ≤ ∫ s in (0:ℝ)..η, Mb * s ^ ((1:ℝ)/2) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hη.le ?_ hmajor
    filter_upwards with s hs
    exact hptwise s ⟨le_of_lt hs.1, hs.2⟩
  have hvalue : (∫ s in (0:ℝ)..η, Mb * s ^ ((1:ℝ)/2)) = (2/3) * Mb * η ^ ((3:ℝ)/2) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    have hexp : (1:ℝ)/2 + 1 = (3:ℝ)/2 := by ring
    rw [hexp, Real.zero_rpow (by norm_num)]
    ring
  have hpowmul : (η ^ (-(1:ℝ)/2)) * (η ^ ((3:ℝ)/2)) = η := by
    rw [← Real.rpow_add hη]
    norm_num
  calc ‖(η ^ (-(1:ℝ)/2)) • gammaTransport Rint T η
        (∫ s in (0:ℝ)..η, (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s)))‖
      = (η ^ (-(1:ℝ)/2)) * ‖gammaTransport Rint T η
          (∫ s in (0:ℝ)..η, (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s)))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hη.le _)]
    _ ≤ (η ^ (-(1:ℝ)/2)) * ‖∫ s in (0:ℝ)..η,
          (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s))‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hη.le _)
        have h := ContinuousLinearMap.le_opNorm (gammaTransport Rint T η)
          (∫ s in (0:ℝ)..η, (s ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T s (b s)))
        rwa [hQnorm, one_mul] at h
    _ ≤ (η ^ (-(1:ℝ)/2)) * ((2/3) * Mb * η ^ ((3:ℝ)/2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hη.le _)
        rw [← hvalue]
        exact hnorm
    _ = (2/3) * Mb * η := by
        rw [show (η ^ (-(1:ℝ)/2)) * ((2/3) * Mb * η ^ ((3:ℝ)/2))
          = (2/3) * Mb * ((η ^ (-(1:ℝ)/2)) * (η ^ ((3:ℝ)/2))) from by ring, hpowmul]

end Hilbert

end

end GaloisForLFunctions.RHTower
