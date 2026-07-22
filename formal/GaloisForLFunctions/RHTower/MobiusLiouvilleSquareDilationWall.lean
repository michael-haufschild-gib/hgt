import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier

/-!
# Square-dilation unit invariance of the Möbius--Laplace Mellin wall

Multiplying the canonical Mellin identity by an analytic nowhere-zero factor cannot improve its
continuation domain.  The Liouville square-dilation channel has factor `ζ(2s)`, which is an
analytic unit on `Re s > 1/2`.  Its continuation wall is therefore exactly the Möbius wall and
hence exactly RH.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Mellin continuation wall obtained by multiplying the canonical Möbius identity by `U`. -/
def MobiusLaplaceUnitTwistedMellinContinuationWall (U : ℂ → ℂ) : Prop :=
  ∃ G : ℂ → ℂ,
    AnalyticOnNhd ℂ G rightHalf ∧
      ∀ s ∈ rightHalf,
        G s * zetaResidueUnit s = Complex.Gamma s * (s - 1) * U s

/-- **Analytic-unit invariance.** A twist by an analytic nowhere-zero multiplier on the target
half-plane preserves the Möbius--Laplace continuation wall exactly. -/
theorem mobiusLaplaceUnitTwistedMellinContinuationWall_iff
    {U : ℂ → ℂ} (hU : AnalyticOnNhd ℂ U rightHalf)
    (hUne : ∀ s ∈ rightHalf, U s ≠ 0) :
    MobiusLaplaceUnitTwistedMellinContinuationWall U ↔
      MobiusLaplaceMellinContinuationWall := by
  constructor
  · rintro ⟨H, hH, hidentity⟩
    refine ⟨fun s => H s / U s, ?_, ?_⟩
    · intro s hs
      exact (hH s hs).div (hU s hs) (hUne s hs)
    · intro s hs
      calc
        (H s / U s) * zetaResidueUnit s =
            (H s * zetaResidueUnit s) / U s := by ring
        _ = (Complex.Gamma s * (s - 1) * U s) / U s := by
          rw [hidentity s hs]
        _ = Complex.Gamma s * (s - 1) :=
          mul_div_cancel_right₀ _ (hUne s hs)
  · rintro ⟨G, hG, hidentity⟩
    refine ⟨fun s => G s * U s, ?_, ?_⟩
    · intro s hs
      exact (hG s hs).mul (hU s hs)
    · intro s hs
      calc
        (G s * U s) * zetaResidueUnit s =
            (G s * zetaResidueUnit s) * U s := by ring
        _ = Complex.Gamma s * (s - 1) * U s := by
          rw [hidentity s hs]

/-- Square-dilation multiplier connecting the Möbius and Liouville Dirichlet/Mellin channels. -/
def mobiusLiouvilleSquareDilationUnit (s : ℂ) : ℂ :=
  riemannZeta (2 * s)

/-- `ζ(2s)` is analytic throughout `Re s > 1/2`. -/
theorem mobiusLiouvilleSquareDilationUnit_analyticOnNhd :
    AnalyticOnNhd ℂ mobiusLiouvilleSquareDilationUnit rightHalf := by
  intro s hs
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    have hhalf : 1 / 2 < s.re := mem_rightHalf.mp hs
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      one_re] at hre
    linarith
  exact (analyticOn_riemannZeta (2 * s) h2one).comp
    (show AnalyticAt ℂ (fun z : ℂ => 2 * z) s by fun_prop)

/-- `ζ(2s)` has no zero throughout `Re s > 1/2`. -/
theorem mobiusLiouvilleSquareDilationUnit_ne_zero
    {s : ℂ} (hs : s ∈ rightHalf) :
    mobiusLiouvilleSquareDilationUnit s ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  have hhalf : 1 / 2 < s.re := mem_rightHalf.mp hs
  simp only [mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero]
  linarith

/-- Liouville square-dilation version of the Möbius--Laplace Mellin wall. -/
def MobiusLiouvilleSquareDilationMellinContinuationWall : Prop :=
  MobiusLaplaceUnitTwistedMellinContinuationWall mobiusLiouvilleSquareDilationUnit

/-- **Square-dilation no-go.** The Liouville-twisted and Möbius continuation walls coincide. -/
theorem mobiusLiouvilleSquareDilationMellinContinuationWall_iff_mobius :
    MobiusLiouvilleSquareDilationMellinContinuationWall ↔
      MobiusLaplaceMellinContinuationWall :=
  mobiusLaplaceUnitTwistedMellinContinuationWall_iff
    mobiusLiouvilleSquareDilationUnit_analyticOnNhd
    (fun _ hs => mobiusLiouvilleSquareDilationUnit_ne_zero hs)

/-- The Liouville square-dilation continuation wall is itself exactly RH. -/
theorem mobiusLiouvilleSquareDilationMellinContinuationWall_iff_riemannHypothesis :
    MobiusLiouvilleSquareDilationMellinContinuationWall ↔ RiemannHypothesis :=
  mobiusLiouvilleSquareDilationMellinContinuationWall_iff_mobius.trans
    mobiusLaplaceMellinContinuationWall_iff_riemannHypothesis

/-- Any Liouville square-dilation wall witness proves RH, but the twist supplies no easier source. -/
theorem mobiusLiouvilleSquareDilationMellinContinuationWall_implies_riemannHypothesis
    (h : MobiusLiouvilleSquareDilationMellinContinuationWall) :
    RiemannHypothesis :=
  mobiusLiouvilleSquareDilationMellinContinuationWall_iff_riemannHypothesis.mp h

end

end RHTower
