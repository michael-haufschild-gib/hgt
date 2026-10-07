import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalKernel
import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalCoefficients
import GaloisForLFunctions.RHTower.WeilShiftPairLandau

/-!
# Real windows of the modified full Weil datum

The bounded translate identity controls the actual signed coefficient windows
by the two pole exponentials. The window integral is the bridge from this
identity to the real Dirichlet residue.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open scoped Real ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided WeilSpectral

/-- The actual locally finite signed arithmetic window. -/
def criticalWindow (lam : ℕ → ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then lam n else 0) * windowValue g y n

theorem criticalAtomLinear_transl_liftC (lam : ℕ → ℝ) (g : ℝ → ℝ) (y : ℝ) :
    criticalAtomLinear lam (transl y (EF.weilTest (liftC g) (liftC g))) =
      (criticalWindow lam g y : ℂ) := by
  rw [criticalAtomLinear, criticalWindow, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [transl, weilTest_liftC]
  by_cases hn : 2 ≤ n
  · rw [if_pos hn, if_pos hn, windowValue,
      show -Real.log n - y = -(Real.log n + y) by ring, autoCorr_neg]
    push_cast
    ring
  · simp [hn]

/-- The pole pairing of a real autocorrelation is the same positive/negative exponential pair. -/
theorem poleLinear_transl_liftC {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (y : ℝ) :
    poleLinear (transl y (EF.weilTest (liftC g) (liftC g))) =
      (poleConst g * (Real.exp (y / 2) + Real.exp (-y / 2)) : ℝ) := by
  have hc : Continuous (liftC g) := Complex.continuous_ofReal.comp hg
  have hcs := hasCompactSupport_liftC hgc
  have hconj1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hconj2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  have e1 : Complex.exp (I * (I / 2) * (y : ℂ)) = (Real.exp (-y / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    rw [show I * (I / 2) * (y : ℂ) = (I * I) * y / 2 by ring, Complex.I_mul_I]
    push_cast
    ring
  have e2 : Complex.exp (I * (-I / 2) * (y : ℂ)) = (Real.exp (y / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    rw [show I * (-I / 2) * (y : ℂ) = -(I * I) * y / 2 by ring, Complex.I_mul_I]
    push_cast
    ring
  rw [poleLinear, paperFT_transl, paperFT_transl,
    EF.paperFT_weilTest hc hc hcs hcs, EF.paperFT_weilTest hc hc hcs hcs,
    hconj1, hconj2, paperFT_liftC_half_I, paperFT_liftC_neg_half_I, e1, e2]
  simp only [Complex.conj_ofReal, poleConst]
  push_cast
  ring

/-- The signed arithmetic windows differ from the required pole profile by a bounded amount. -/
theorem exists_abs_criticalWindow_sub_poles_le {a b C : ℝ} {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ M : ℝ, ∀ y : ℝ,
      |criticalWindow lam g y - b * poleConst g *
        (Real.exp (y / 2) + Real.exp (-y / 2))| ≤ M := by
  have hG : ContDiff ℝ ∞ (liftC g) := ofRealCLM.contDiff.comp hg
  obtain ⟨M, hM⟩ := exists_norm_pole_sub_atoms_transl_le h hG (hasCompactSupport_liftC hgc)
  refine ⟨M, fun y => ?_⟩
  have hm := hM y
  rw [criticalAtomLinear_transl_liftC, poleLinear_transl_liftC hg.continuous hgc,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hm
  simpa only [mul_assoc, abs_sub_comm] using hm

end RHTower.WeilWorkPBAP
