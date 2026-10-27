import GaloisForLFunctions.ArithmeticCorrespondencePositivity.EveryRightZeroReachesAnOutwardZetaRay
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiRealReciprocalField
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheSquareSeesTheRegularLogDerivative
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalRegularField

/-!
# Local outward-field witnesses for the Xi divisor

The outward ray at a quadratic terminal and the real reciprocal field of the
other Xi zeros provide a local source witness.
-/

open Finset Filter Set RHTower
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Every off-line Xi zero reaches a nearby right-hand quadratic terminal with a
positive transverse field. On its outward ray the same reserve holds for the
Gamma-corrected zeta logarithmic derivative; at the terminal it forces a
lower bound for the simple coefficient of its square. -/
theorem exists_local_outward_field_witness :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
      ∃ p : XiZeroCopy, ∃ B : ℂ → ℂ,
        1 / 2 < (p.1 : ℂ).re ∧
        |xiZeroHeight p - xiZeroHeight q| ≤ C * Real.log (|xiZeroHeight q| + 3) ∧
        xiZeroDepth q ≤ xiZeroDepth p ∧ 0 < (xiZeroCopyFiber p.1).card ∧
        (∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
          xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2) ∧
        Summable (fun r : XiZeroCopy =>
          ‖((p.1 : ℂ).re - (r.1 : ℂ).re) /
            ‖(p.1 : ℂ) - (r.1 : ℂ)‖ ^ 2‖) ∧
        ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p) +
          c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤ xiTransverseField p ∧
        (∀ h : ℝ, 0 < h → h < 1 / 2 - xiZeroDepth p →
          xi ((p.1 : ℂ) + (h : ℂ)) ≠ 0 ∧
          riemannZeta ((p.1 : ℂ) + (h : ℂ)) ≠ 0 ∧
          ((xiZeroCopyFiber p.1).card : ℝ) / h +
            ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
            c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤
              (logDeriv riemannZeta ((p.1 : ℂ) + (h : ℂ))).re +
              (logDeriv archFactor ((p.1 : ℂ) + (h : ℂ))).re) ∧
        AnalyticAt ℂ B (p.1 : ℂ) ∧
        logDeriv riemannZeta =ᶠ[𝓝[≠] (p.1 : ℂ)]
          (fun z => ((xiZeroCopyFiber p.1).card : ℂ) / (z - (p.1 : ℂ)) + B z) ∧
        xiTransverseField p = (B (p.1 : ℂ)).re + (logDeriv archFactor (p.1 : ℂ)).re ∧
        GaloisForLFunctions.HTGeometry.laurentCoeff
          (fun z => (logDeriv riemannZeta z) ^ 2) (p.1 : ℂ) (-1) =
            2 * ((xiZeroCopyFiber p.1).card : ℂ) * B (p.1 : ℂ) ∧
        ((xiZeroCopyFiber p.1).card : ℝ) ^ 2 / xiZeroDepth p +
          2 * ((xiZeroCopyFiber p.1).card : ℝ) * c * xiZeroDepth p *
            Real.log (|xiZeroHeight p| + 4) ≤
          (GaloisForLFunctions.HTGeometry.laurentCoeff
            (fun z => (logDeriv riemannZeta z) ^ 2) (p.1 : ℂ) (-1)).re +
          2 * ((xiZeroCopyFiber p.1).card : ℝ) * (logDeriv archFactor (p.1 : ℂ)).re := by
  classical
  obtain ⟨C, hC, hterminal⟩ := exists_right_xi_quadratic_terminal_near
  obtain ⟨c, hc, hbounds⟩ := exists_xiTerminal_transverseField_and_ray_lower
  refine ⟨C, c, hC, hc, fun q hq => ?_⟩
  have hright : ∃ q' : XiZeroCopy, 1 / 2 < (q'.1 : ℂ).re ∧
      xiZeroHeight q' = xiZeroHeight q ∧ xiZeroDepth q' = xiZeroDepth q := by
    by_cases hqright : 1 / 2 < (q.1 : ℂ).re
    · exact ⟨q, hqright, rfl, rfl⟩
    · let q' := xiZeroCopyLineConjEquiv q
      have hcoords := xiLineConj_coordinates q
      have hqleft : (q.1 : ℂ).re < 1 / 2 :=
        lt_of_le_of_ne (le_of_not_gt hqright) hq
      refine ⟨q', ?_, ?_, ?_⟩
      · dsimp only [q']
        rw [hcoords.1]
        linarith
      · exact hcoords.2
      · dsimp only [q', xiZeroDepth]
        rw [hcoords.1]
        have heq : 1 - (q.1 : ℂ).re - 1 / 2 = -((q.1 : ℂ).re - 1 / 2) := by ring
        rw [heq, abs_neg]
  obtain ⟨q', hq', hheight, hdepth⟩ := hright
  obtain ⟨p, hp, hpnear, hpdepth, hcone⟩ := hterminal q' hq'
  rw [hheight] at hpnear
  rw [hdepth] at hpdepth
  have hm : 0 < (xiZeroCopyFiber p.1).card :=
    Finset.card_pos.mpr ⟨p, mem_xiZeroCopyFiber.mpr rfl⟩
  obtain ⟨hfield, hray⟩ := hbounds p hp hcone
  obtain ⟨B, hB, hprincipal, hcoeff⟩ := xiZero_exists_zeta_regular_part p
  have hfieldEq := xiTransverseField_eq_zeta_regular_part p hp hcone hB hprincipal
  have hrayZeta : ∀ h : ℝ, 0 < h → h < 1 / 2 - xiZeroDepth p →
      xi ((p.1 : ℂ) + (h : ℂ)) ≠ 0 ∧
      riemannZeta ((p.1 : ℂ) + (h : ℂ)) ≠ 0 ∧
      ((xiZeroCopyFiber p.1).card : ℝ) / h +
        ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
        c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤
          (logDeriv riemannZeta ((p.1 : ℂ) + (h : ℂ))).re +
          (logDeriv archFactor ((p.1 : ℂ) + (h : ℂ))).re := by
    intro h hh hbound
    let s : ℂ := (p.1 : ℂ) + (h : ℂ)
    have hsre : s.re = (p.1 : ℂ).re + h := by dsimp only [s]; simp
    have hpdepth' : xiZeroDepth p = (p.1 : ℂ).re - 1 / 2 := by
      rw [xiZeroDepth, abs_of_pos (by linarith)]
    have hs0 : 0 < s.re := by rw [hsre]; linarith only [hp, hh]
    have hs1 : s.re < 1 := by
      rw [hsre]
      have hb := hbound
      rw [hpdepth'] at hb
      linarith only [hb]
    have hsone : s ≠ 1 := by intro heq; rw [heq] at hs1; norm_num at hs1
    have hxi : xi s ≠ 0 := xi_ne_zero_on_terminal_ray p hp hcone hh
    have hzeta : riemannZeta s ≠ 0 := by
      intro hz
      exact hxi ((xi_eq_zero_iff hs0 hsone).mpr hz)
    have heq : (logDeriv xi s).re =
        (logDeriv archFactor s).re + (logDeriv riemannZeta s).re := by
      rw [(logDeriv_xi_eq_archFactor_add_of_strip hs0 hs1 hzeta).2]
      simp
    have hreserve := hray h hh hbound
    change ((xiZeroCopyFiber p.1).card : ℝ) / h +
        ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
        c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤ (logDeriv xi s).re at hreserve
    rw [heq] at hreserve
    exact ⟨hxi, hzeta, by linarith only [hreserve]⟩
  have ha : 0 < xiZeroDepth p := by
    rw [xiZeroDepth, abs_of_pos (by linarith)]
    linarith
  have hcoeffRe : (GaloisForLFunctions.HTGeometry.laurentCoeff
      (fun z => (logDeriv riemannZeta z) ^ 2) (p.1 : ℂ) (-1)).re =
        2 * ((xiZeroCopyFiber p.1).card : ℝ) * (B (p.1 : ℂ)).re := by
    rw [hcoeff]
    simp
  have hscaled := mul_le_mul_of_nonneg_left hfield
    (show 0 ≤ 2 * ((xiZeroCopyFiber p.1).card : ℝ) by positivity)
  have hleft : 2 * ((xiZeroCopyFiber p.1).card : ℝ) *
      (((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p) +
        c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4)) =
      ((xiZeroCopyFiber p.1).card : ℝ) ^ 2 / xiZeroDepth p +
        2 * ((xiZeroCopyFiber p.1).card : ℝ) * c * xiZeroDepth p *
          Real.log (|xiZeroHeight p| + 4) := by
    field_simp [ne_of_gt ha] <;> ring
  have hright : 2 * ((xiZeroCopyFiber p.1).card : ℝ) * xiTransverseField p =
      (GaloisForLFunctions.HTGeometry.laurentCoeff
        (fun z => (logDeriv riemannZeta z) ^ 2) (p.1 : ℂ) (-1)).re +
      2 * ((xiZeroCopyFiber p.1).card : ℝ) * (logDeriv archFactor (p.1 : ℂ)).re := by
    rw [hfieldEq, hcoeffRe]
    ring
  rw [hleft, hright] at hscaled
  exact ⟨p, B, hp, hpnear, hpdepth, hm, hcone, xiTransverseField_norm_summable p,
    hfield, hrayZeta, hB, hprincipal, hfieldEq, hcoeff, hscaled⟩

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
