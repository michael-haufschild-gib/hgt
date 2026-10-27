import GaloisForLFunctions.ArithmeticCorrespondencePositivity.RightQuadraticTerminalsNearOffLineZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalPairRay
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiZerosSupplyLogarithmicBand
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalOutwardLogDeriv
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheVonMangoldtSquareIsTheZetaSource
import GaloisForLFunctions.RHTower.SpeiserLocalDisk

/-!
# Outward zeta rays from right-hand Xi zeros

Quadratic terminals, reflected zero pairs, and fixed-width zero counts give a
positive reserve for the completed zeta logarithmic derivative on a nearby ray.
-/

open Finset RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Every right-hand Xi zero reaches a nearby right-hand terminal whose
zero-free outward ray has the stated Gamma-corrected zeta-source reserve. -/
theorem exists_local_outward_zeta_ray :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re →
      ∃ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re ∧
        |xiZeroHeight p - xiZeroHeight q| ≤ C * Real.log (|xiZeroHeight q| + 3) ∧
        xiZeroDepth q ≤ xiZeroDepth p ∧ 0 < (xiZeroCopyFiber p.1).card ∧
        (∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
          xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2) ∧
        ∀ h : ℝ, 0 < h → h < 1 / 2 - xiZeroDepth p →
          xi ((p.1 : ℂ) + (h : ℂ)) ≠ 0 ∧
          riemannZeta ((p.1 : ℂ) + (h : ℂ)) ≠ 0 ∧
          ((xiZeroCopyFiber p.1).card : ℝ) / h +
            ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
            c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤
              (logDeriv riemannZeta ((p.1 : ℂ) + (h : ℂ))).re +
              (logDeriv archFactor ((p.1 : ℂ) + (h : ℂ))).re := by
  classical
  obtain ⟨C, hC, hterminal⟩ := exists_right_xi_quadratic_terminal_near
  obtain ⟨c, hc, hlower⟩ := exists_xiTerminal_logDeriv_lower
  refine ⟨C, c, hC, hc, fun q hq => ?_⟩
  obtain ⟨p, hp, hpnear, hpdepth, hcone⟩ := hterminal q hq
  have hm : 0 < (xiZeroCopyFiber p.1).card :=
    Finset.card_pos.mpr ⟨p, mem_xiZeroCopyFiber.mpr rfl⟩
  refine ⟨p, hp, hpnear, hpdepth, hm, hcone, ?_⟩
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
  have hsone : s ≠ 1 := by
    intro heq
    rw [heq] at hs1
    norm_num at hs1
  have hxi : xi s ≠ 0 := by
    dsimp only [s]
    exact xi_ne_zero_on_terminal_ray p hp hcone hh
  have hzeta : riemannZeta s ≠ 0 := by
    intro hz
    exact hxi ((xi_eq_zero_iff hs0 hsone).mpr hz)
  have heq : (logDeriv xi s).re =
      (logDeriv archFactor s).re + (logDeriv riemannZeta s).re := by
    rw [(logDeriv_xi_eq_archFactor_add_of_strip hs0 hs1 hzeta).2]
    simp
  have hreserve := hlower p hp hcone h hh hbound
  change ((xiZeroCopyFiber p.1).card : ℝ) / h +
      ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
      c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤ (logDeriv xi s).re at hreserve
  rw [heq] at hreserve
  refine ⟨hxi, hzeta, ?_⟩
  linarith only [hreserve]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
