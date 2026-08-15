import GaloisForLFunctions.RHTower.GammaRatioBranchDerivative
import GaloisForLFunctions.RHTower.WallGeneratorLogCoercivity
import GaloisForLFunctions.RHTower.SuzukiGammaForcedStripHardy
import GaloisForLFunctions.HTGeometry.PhaseGeneratorIntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The generator equation of the Gamma strip propagator

The propagator factors as a scalar times a bounded exponential of the adjacency,

`H(z) = a(z)·exp(−izT/2)`,   `a(z) = z^{-1/2}e^{iγz}E(z)`,

so its logarithmic derivative is the sum of the scalar one and the constant `−iT/2`.  The scalar
logarithmic derivative is computed from the branch: the Gamma ratio has logarithmic derivative
`i(ψ(1+iz) + ψ(1−iz))`, its square root has half of it, and adding the contributions of `z^{-1/2}`
and `e^{iγz}` gives

`−i a'/a = r(z)/2 + i/(2z)`,

which is exactly the scalar part of the phase generator.  Consequently the inverse propagator
satisfies

`(H^{-1})' = −i H^{-1}B`,   `B(z) = (1/2)(r(z)·I − T) + i/(2z)·I`,

and the phase-weighted map `E(t,L) = H(t+iσ)^{-1}e^{-itL}` satisfies the same equation with the
generator shifted by the position, `C(t,L) = B(t+iσ) + L·I`.  Since the shifted generator is
invertible wherever the frequency logarithm and the position together open a gap, this is precisely
the hypothesis consumed by the integration by parts against an invertible phase generator: the
amplitude is traded for one more power of the resolvent at every step.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The scalar factor -/

/-- The scalar factor `z^{-1/2}e^{iγz}E(z)` of the Gamma strip propagator. -/
def stripScalar (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (-(1 : ℂ) / 2) * (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z)

theorem shiftedLine_mem_slitPlane {σ : ℝ} (hσ0 : 0 < σ) (t : ℝ) :
    ((t : ℂ) + (σ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  refine Or.inr ?_
  simp
  linarith

theorem shiftedLine_mem_imStrip {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    ((t : ℂ) + (σ : ℂ) * Complex.I) ∈ imStrip (-1) 1 := by
  constructor <;> simp <;> linarith

theorem shiftedLine_ne_zero {σ : ℝ} (hσ0 : 0 < σ) (t : ℝ) :
    ((t : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem hasDerivAt_shiftedLine (σ : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) + (σ : ℂ) * Complex.I) 1 t := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((σ : ℂ) * Complex.I)

theorem gammaArg_lower {σ t : ℝ} :
    1 + Complex.I * ((t : ℂ) + (σ : ℂ) * Complex.I) = ((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination ((σ : ℂ)) * hI

theorem gammaArg_upper {σ t : ℝ} :
    1 - Complex.I * ((t : ℂ) + (σ : ℂ) * Complex.I)
      = ((1 + σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-(σ : ℂ)) * hI

theorem stripScalar_ne_zero {E : ℂ → ℂ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (t : ℝ) :
    stripScalar E ((t : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := by
  refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (shiftedLine_ne_zero hσ0 t))) ?_
  exact mul_ne_zero (Complex.exp_ne_zero _) (hEne _ (shiftedLine_mem_imStrip hσ0 hσ1 t))

/-- **The scalar factor has logarithmic derivative `i·(r/2 + i/(2z))` on the shifted line.** -/
theorem hasDerivAt_stripScalar_line {E : ℂ → ℂ} {σ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => stripScalar E ((s : ℂ) + (σ : ℂ) * Complex.I))
      (Complex.I * wallGeneratorScalar σ t
        * stripScalar E ((t : ℂ) + (σ : ℂ) * Complex.I)) t := by
  have hzne : ((t : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := shiftedLine_ne_zero hσ0 t
  have hline := hasDerivAt_shiftedLine σ t
  have hslit : ((t : ℂ) + (σ : ℂ) * Complex.I) ∈ Complex.slitPlane :=
    shiftedLine_mem_slitPlane hσ0 t
  have hstrip : ((t : ℂ) + (σ : ℂ) * Complex.I) ∈ imStrip (-1) 1 :=
    shiftedLine_mem_imStrip hσ0 hσ1 t
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2))
      ((-(1 : ℂ) / 2) * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ ((-(1 : ℂ) / 2) - 1) * 1) t := by
    have hcomp :=
      ((Complex.hasStrictDerivAt_cpow_const (c := (-(1 : ℂ) / 2)) hslit).hasDerivAt).comp t hline
    exact hcomp
  have hlin : HasDerivAt
      (fun s : ℝ =>
        Complex.I * (Real.eulerMascheroniConstant : ℂ) * ((s : ℂ) + (σ : ℂ) * Complex.I))
      (Complex.I * (Real.eulerMascheroniConstant : ℂ)) t := by
    simpa using hline.const_mul (Complex.I * (Real.eulerMascheroniConstant : ℂ))
  have h2 : HasDerivAt
      (fun s : ℝ => Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ)
        * ((s : ℂ) + (σ : ℂ) * Complex.I)))
      (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ)
          * ((t : ℂ) + (σ : ℂ) * Complex.I))
        * (Complex.I * (Real.eulerMascheroniConstant : ℂ))) t := hlin.cexp
  have h3 : HasDerivAt (fun s : ℝ => E ((s : ℂ) + (σ : ℂ) * Complex.I))
      (E ((t : ℂ) + (σ : ℂ) * Complex.I) * (Complex.I / 2 *
        (Complex.digamma (1 + Complex.I * ((t : ℂ) + (σ : ℂ) * Complex.I))
          + Complex.digamma (1 - Complex.I * ((t : ℂ) + (σ : ℂ) * Complex.I)))) * 1) t :=
    (hasDerivAt_gammaRatioSqrt hEdiff hE hEne hstrip).comp t hline
  have hprod := h1.mul (h2.mul h3)
  refine hprod.congr_deriv ?_
  have hpow : ((t : ℂ) + (σ : ℂ) * Complex.I) ^ ((-(1 : ℂ) / 2) - 1)
      = ((t : ℂ) + (σ : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2)
        * ((t : ℂ) + (σ : ℂ) * Complex.I)⁻¹ := by
    rw [Complex.cpow_sub _ _ hzne, Complex.cpow_one, div_eq_mul_inv]
  have hdig : Complex.digamma (1 + Complex.I * ((t : ℂ) + (σ : ℂ) * Complex.I))
        + Complex.digamma (1 - Complex.I * ((t : ℂ) + (σ : ℂ) * Complex.I))
      = wallSymbol σ t - 2 * (Real.eulerMascheroniConstant : ℂ) := by
    rw [gammaArg_lower, gammaArg_upper, wallSymbol]
    ring
  have hscal : Complex.I * wallGeneratorScalar σ t
      = (-(1 : ℂ) / 2) * ((t : ℂ) + (σ : ℂ) * Complex.I)⁻¹
        + Complex.I * (Real.eulerMascheroniConstant : ℂ)
        + Complex.I / 2 * (wallSymbol σ t - 2 * (Real.eulerMascheroniConstant : ℂ)) := by
    have hA : Complex.I * (Complex.I / (2 * ((t : ℂ) + (σ : ℂ) * Complex.I)))
        = (-(1 : ℂ) / 2) * ((t : ℂ) + (σ : ℂ) * Complex.I)⁻¹ := by
      rw [mul_div_assoc', Complex.I_mul_I, div_eq_mul_inv, mul_inv]
      ring
    rw [wallGeneratorScalar, mul_add, hA]
    ring
  simp only [Pi.mul_apply]
  rw [stripScalar, hpow, hdig, hscal]
  ring

section Operator

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem stripExp_line_eq (T : X →L[ℂ] X) (σ : ℝ) (s : ℝ) :
    ((Complex.I / 2) * ((s : ℂ) + (σ : ℂ) * Complex.I)) • T
      = s • ((Complex.I / 2 : ℂ) • T)
        + (((Complex.I / 2) * ((σ : ℂ) * Complex.I)) • T) := by
  have hcast : ((s : ℂ)) • ((Complex.I / 2 : ℂ) • T) = s • ((Complex.I / 2 : ℂ) • T) := by
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  rw [← hcast, smul_smul, ← add_smul]
  congr 1
  ring

theorem hasDerivAt_stripExp_line (T : X →L[ℂ] X) (σ : ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => NormedSpace.exp (((Complex.I / 2) * ((s : ℂ) + (σ : ℂ) * Complex.I)) • T))
      (NormedSpace.exp (((Complex.I / 2) * ((t : ℂ) + (σ : ℂ) * Complex.I)) • T)
        * ((Complex.I / 2 : ℂ) • T)) t := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  set A : X →L[ℂ] X := (Complex.I / 2 : ℂ) • T with hA
  set B₀ : X →L[ℂ] X := ((Complex.I / 2) * ((σ : ℂ) * Complex.I)) • T with hB
  have hcomm : ∀ s : ℝ, Commute (s • A) B₀ := by
    intro s
    rw [hA, hB]
    exact (((Commute.refl T).smul_left _).smul_right _).smul_left _
  have hsplit : ∀ s : ℝ,
      NormedSpace.exp (((Complex.I / 2) * ((s : ℂ) + (σ : ℂ) * Complex.I)) • T)
        = NormedSpace.exp (s • A) * NormedSpace.exp B₀ := by
    intro s
    rw [stripExp_line_eq T σ s, ← hA, ← hB, NormedSpace.exp_add_of_commute (hcomm s)]
  have hbase := hasDerivAt_exp_smul_const A t
  have hmul := hbase.mul_const (NormedSpace.exp B₀)
  have hfun : (fun s : ℝ => NormedSpace.exp (s • A) * NormedSpace.exp B₀)
      = fun s : ℝ => NormedSpace.exp (((Complex.I / 2) * ((s : ℂ) + (σ : ℂ) * Complex.I)) • T) := by
    funext s
    rw [hsplit s]
  rw [hfun] at hmul
  refine hmul.congr_deriv ?_
  have hAB : Commute A B₀ := by
    rw [hA, hB]
    exact ((Commute.refl T).smul_left _).smul_right _
  have hAexp : A * NormedSpace.exp B₀ = NormedSpace.exp B₀ * A := (hAB.exp_right).eq
  rw [hsplit t, mul_assoc, hAexp, ← mul_assoc]

end Operator

section Generator

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- **`(1)`: the inverse Gamma propagator solves `(H^{-1})' = -i H^{-1} B`.** -/
theorem hasDerivAt_stripPropagatorInv_line {E : ℂ → ℂ} {T : X →L[ℂ] X} {σ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => stripPropagatorInv E T ((s : ℂ) + (σ : ℂ) * Complex.I))
      ((-Complex.I) • (stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
        * wallGenerator T σ t)) t := by
  have hsne := stripScalar_ne_zero (E := E) hσ0 hσ1 hEne t
  have hs := hasDerivAt_stripScalar_line hEdiff hE hEne hσ0 hσ1 t
  have hinv := hs.inv hsne
  have hexp := hasDerivAt_stripExp_line T σ t
  have hmul := hinv.smul hexp
  have hfun : ((fun s : ℝ => stripScalar E ((s : ℂ) + (σ : ℂ) * Complex.I))⁻¹ •
      fun s : ℝ => NormedSpace.exp (((Complex.I / 2) * ((s : ℂ) + (σ : ℂ) * Complex.I)) • T))
      = fun s : ℝ => stripPropagatorInv E T ((s : ℂ) + (σ : ℂ) * Complex.I) := by
    funext s
    rfl
  rw [hfun] at hmul
  refine hmul.congr_deriv ?_
  simp only [Pi.inv_apply]
  set a : ℂ := stripScalar E ((t : ℂ) + (σ : ℂ) * Complex.I) with ha
  set U : X →L[ℂ] X :=
    NormedSpace.exp (((Complex.I / 2) * ((t : ℂ) + (σ : ℂ) * Complex.I)) • T) with hU
  set c : ℂ := wallGeneratorScalar σ t with hc
  have hPinv : stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) = a⁻¹ • U := rfl
  have hcoef : -(Complex.I * c * a) / a ^ 2 = -(Complex.I * c) * a⁻¹ := by
    field_simp
  have hRHS : (-Complex.I) • ((a⁻¹ • U) * wallGenerator T σ t)
      = (a⁻¹ * (Complex.I / 2)) • (U * T) + (-(Complex.I * c) * a⁻¹) • U := by
    have hid : (ContinuousLinearMap.id ℂ X) = (1 : X →L[ℂ] X) := rfl
    rw [wallGenerator, ← hc, mul_sub, smul_mul_assoc, mul_smul_comm, mul_smul_comm, hid, mul_one,
      smul_mul_assoc]
    module
  rw [hPinv, hRHS, hcoef, mul_smul_comm, smul_smul]

end Generator

section Phase

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The shifted generator `C(t,L) = B(t+iσ) + L·I` of the block equation. -/
def wallGeneratorShift (T : X →L[ℂ] X) (σ L t : ℝ) : X →L[ℂ] X :=
  wallGenerator T σ t + (L : ℂ) • ContinuousLinearMap.id ℂ X

/-- The phase-weighted inverse propagator `E(t,L) = H(t+iσ)^{-1}e^{-itL}`. -/
def wallPhaseMap (E : ℂ → ℂ) (T : X →L[ℂ] X) (σ L t : ℝ) : X →L[ℂ] X :=
  Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ))
    • stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)

/-- **`(17)`: the phase-weighted inverse propagator has the shifted generator.** -/
theorem hasDerivAt_wallPhaseMap {E : ℂ → ℂ} {T : X →L[ℂ] X} {σ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (L t : ℝ) :
    HasDerivAt (wallPhaseMap E T σ L)
      ((-(Complex.I) : ℂ) • (wallPhaseMap E T σ L t * wallGeneratorShift T σ L t)) t := by
  have hlineC : HasDerivAt (fun s : ℝ => -(Complex.I) * (L : ℂ) * (s : ℂ))
      (-(Complex.I) * (L : ℂ)) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(Complex.I) * (L : ℂ))
  have hp : HasDerivAt (fun s : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (s : ℂ)))
      (Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) * (-(Complex.I) * (L : ℂ))) t := hlineC.cexp
  have hQ := hasDerivAt_stripPropagatorInv_line hEdiff hE hEne hσ0 hσ1 (T := T) t
  have hmul := hp.smul hQ
  refine hmul.congr_deriv ?_
  set p : ℂ := Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) with hpdef
  set Q : X →L[ℂ] X := stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) with hQdef
  set B : X →L[ℂ] X := wallGenerator T σ t with hBdef
  have hid : (ContinuousLinearMap.id ℂ X) = (1 : X →L[ℂ] X) := rfl
  have hmap : wallPhaseMap E T σ L t = p • Q := rfl
  rw [hmap, wallGeneratorShift, ← hBdef, hid, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, mul_one]
  module

/-! ## The generator is a unit on the tail -/

theorem isUnit_wallGeneratorShift {T : X →L[ℂ] X} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {t L : ℝ} (hgap : 0 < wallFloor T σ t + L) :
    IsUnit (wallGeneratorShift T σ L t) := by
  obtain ⟨S, h₁, h₂, _⟩ := exists_inverse_wallGenerator_shift hσ0 hσ1 t L hgap
  refine ⟨⟨wallGeneratorShift T σ L t, S, ?_, ?_⟩, rfl⟩
  · ext v
    exact h₁ v
  · ext v
    exact h₂ v

/-- **`(15)` in the form the integration by parts consumes.**  The pointwise ring inverse of the
shifted generator is bounded by the reciprocal of the floor. -/
theorem norm_invFamily_wallGeneratorShift_le {T : X →L[ℂ] X} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {t L : ℝ} (hgap : 0 < wallFloor T σ t + L) :
    ‖GaloisForLFunctions.HTGeometry.invFamily (wallGeneratorShift T σ L) t‖
      ≤ (wallFloor T σ t + L)⁻¹ := by
  obtain ⟨S, h₁, h₂, h₃⟩ := exists_inverse_wallGenerator_shift hσ0 hσ1 t L hgap
  have hunit : (wallGeneratorShift T σ L t) * S = 1 := by
    ext v
    exact h₁ v
  have hunit' : S * (wallGeneratorShift T σ L t) = 1 := by
    ext v
    exact h₂ v
  set u : (X →L[ℂ] X)ˣ := ⟨wallGeneratorShift T σ L t, S, hunit, hunit'⟩ with hu
  have hinv : GaloisForLFunctions.HTGeometry.invFamily (wallGeneratorShift T σ L) t = S := by
    rw [GaloisForLFunctions.HTGeometry.invFamily]
    have : (wallGeneratorShift T σ L t) = (u : X →L[ℂ] X) := rfl
    rw [this, Ring.inverse_unit]
    rfl
  rw [hinv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  exact h₃ v

end Phase

end GaloisForLFunctions.RHTower
