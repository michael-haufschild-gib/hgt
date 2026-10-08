import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCutoffIntegration
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPrimitiveGamma

/-!
# Exact overlap of the actual primitive's Mellin head and tail

The lower pairing uses the continuous primitive with its value at zero
subtracted. Its convergence follows from the already checked primitive Mellin
transform. Both endpoint contributions cancel exactly, leaving the explicit
Gamma multiplier of the original Dirichlet quotient on `1 < re s < 2`.
Moving compact-test limits and defect regularity remain separate obligations.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

/-- Complementary cutoff derivatives recover the uncut Mellin kernel. -/
theorem iteratedDeriv_two_complement_add_cutoff {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x +
      iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x =
        (s - 1) * (s - 2) * (x : ℂ) ^ (s - 3) := by
  rw [iteratedDeriv_two_cutoff_cpow (contDiff_const.sub hψ) s hx,
    iteratedDeriv_two_cutoff_cpow hψ s hx,
    iteratedDeriv_const_sub (by decide : 0 < 2),
    iteratedDeriv_const_sub (by decide : 0 < 1)]
  simp only [iteratedDeriv_neg]
  ring

/-- The lower cutoff pairing with the primitive's value at zero subtracted. -/
def primitiveMellinHead (F : ℝ → ℂ) (A : ℂ) (ψ : ℝ → ℂ) (s : ℂ) : ℂ :=
  A * mellin (fun x => 1 - ψ x) s +
    ∫ x : ℝ in Ioi 0, (F x - F 0) *
      iteratedDeriv 2 (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x

/-- The actual absolutely convergent head and tail have the full primitive Mellin overlap. -/
theorem integrable_mellinHead_and_overlap {ψ F : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) (A : ℂ) {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2)
    (hM : MellinConvergent (fun x => F x - F 0) (s - 2)) :
    IntegrableOn (fun x : ℝ => (F x - F 0) *
      iteratedDeriv 2 (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x) (Ioi 0) ∧
      primitiveMellinHead F A ψ s + primitiveMellinTail F A ψ s =
        (s - 1) * (s - 2) * mellin (fun x => F x - F 0) (s - 2) := by
  let f : ℝ → ℂ := fun x => F x - F 0
  let D : ℝ → ℂ := iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1))
  have hf : Continuous f := hF.sub continuous_const
  have hBf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hB
    exact ⟨C + ‖F 0‖, fun x => (norm_sub_le _ _).trans (add_le_add (hC x) (le_refl _))⟩
  have hiD : IntegrableOn D (Ioi 0) := by
    simpa only [one_mul] using (integral_primitive_cutoff_cpow hψ
      (F := fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ hs2).1
  have hiF : IntegrableOn (fun x => F x * D x) (Ioi 0) :=
    (integral_primitive_cutoff_cpow hψ hF hB hs2).1
  have hif : IntegrableOn (fun x => f x * D x) (Ioi 0) :=
    (integral_primitive_cutoff_cpow hψ hf hBf hs2).1
  have him : IntegrableOn (fun x : ℝ => (s - 1) * (s - 2) *
      ((x : ℂ) ^ (s - 3) * f x)) (Ioi 0) := by
    simpa only [MellinConvergent, IntegrableOn, f, smul_eq_mul, show s - 2 - 1 = s - 3 by ring]
      using hM.const_mul ((s - 1) * (s - 2))
  have he : (fun x : ℝ => f x *
      iteratedDeriv 2 (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x) =ᵐ[
        volume.restrict (Ioi 0)] fun x =>
          (s - 1) * (s - 2) * ((x : ℂ) ^ (s - 3) * f x) - f x * D x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := iteratedDeriv_two_complement_add_cutoff hψ.smooth s hx
    dsimp only [D]
    linear_combination f x * h
  have hi := (him.sub hif).congr he.symm
  refine ⟨hi, ?_⟩
  have hh : (∫ x : ℝ in Ioi 0, f x *
      iteratedDeriv 2 (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x) =
        (s - 1) * (s - 2) * mellin f (s - 2) - ∫ x : ℝ in Ioi 0, f x * D x := by
    rw [integral_congr_ae he, integral_sub him hif, integral_const_mul]
    simp only [mellin, smul_eq_mul, show s - 2 - 1 = s - 3 by ring]
  have hshift : (∫ x : ℝ in Ioi 0, f x * D x) = ∫ x : ℝ in Ioi 0, F x * D x := by
    simp only [f, sub_mul]
    rw [integral_sub hiF (hiD.const_mul (F 0)), integral_const_mul,
      integral_mellinCutoff_second_eq_zero hψ hs2, mul_zero, sub_zero]
  rw [hshift] at hh
  have hc : mellin (fun x => 1 - ψ x) s =
      (∫ x : ℝ in Ioi 0, iteratedDeriv 1 ψ x * (x : ℂ) ^ s) / s := by
    simpa only [mellin, smul_eq_mul, mul_comm] using integral_mellinCutoff_complement hψ hs0
  rw [primitiveMellinHead, primitiveMellinTail_eq_integral hψ hF hB A hs2, hc]
  change A * ((∫ x : ℝ in Ioi 0, iteratedDeriv 1 ψ x * (x : ℂ) ^ s) / s) +
    (∫ x : ℝ in Ioi 0, f x *
      iteratedDeriv 2 (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x) +
    (-(A / s) * (∫ x : ℝ in Ioi 0, iteratedDeriv 1 ψ x * (x : ℂ) ^ s) +
      ∫ x : ℝ in Ioi 0, F x * D x) = _
  rw [hh]
  ring

/-- All convergence hypotheses of the cutoff overlap follow from the original cubic datum. -/
theorem degreeTwoQuotient_cutoff_overlap {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (A : ℂ) {s : ℂ}
    (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    IntegrableOn (fun x : ℝ =>
      (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x -
        fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) 0) *
      iteratedDeriv 2 (fun y : ℝ => (1 - mellinTailCutoff y) * (y : ℂ) ^ (s - 1)) x)
        (Ioi 0) ∧
    primitiveMellinHead (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A mellinTailCutoff s +
      primitiveMellinTail (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A mellinTailCutoff s =
        (s - 1) * (s - 2) * ((LSeries g s / riemannZeta s) * primitiveMellinGammaFactor s) := by
  have hq := degreeTwoQuotientCoeff_summable_shift_square hD
  have H := integrable_mellinHead_and_overlap isMellinTailCutoff_mellinTailCutoff
    (continuous_fourierBoundaryPrimitive hq)
    ⟨_, norm_fourierBoundaryPrimitive_le hq⟩ A (by linarith) hs2
    (degreeTwoQuotient_primitive_mellinConvergent hD hs1 hs2)
  rw [(hasMellin_degreeTwoQuotient_primitive_gamma hD hs1 hs2).2] at H
  exact H
end RHTower.WeilHigherDenominator
