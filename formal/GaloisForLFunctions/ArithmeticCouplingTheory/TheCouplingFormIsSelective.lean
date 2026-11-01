import GaloisForLFunctions.ArithmeticCouplingTheory.MixedDifferencesSeeEveryZero
import GaloisForLFunctions.HeckeKreinToeplitz.TheGoldenCurveIsDecidedOnItsTowerButNotOnTheLattice
import GaloisForLFunctions.HeckeKreinToeplitz.OnTheFiniteStratumEveryFlipHasInfiniteIndex

/-!
# The coupling form is selective

The coupling Laplacian `L_a L_b` annihilates every separable kernel, but on the orbit kernel of any
tempered zero configuration it keeps exactly the negative squares that the test sees
(`negIndex_lap_lap_orbitKernel`): one per right zero seen. So the coupling form separates
configurations exactly as the index does, with the constant (pole-type) square removed.

* `ζ`: `κ(L_a L_b K_ζ) = #{right zeros}`, zero iff RH (`MixedDifferencesSeeEveryZero`).
* The golden fake curve, with integral point counts and a functional equation, has infinitely many
  negative squares in its coupling form (`negIndex_lap_lap_golden`).
* A single-prime flip twin (signs of `Λ` reversed at the odd powers of `p`) changes the
  self-coupling of its tower at `(p, p)` by exactly `−4 log p ‖f‖²/√p`
  (`coupling_flip_sub_coupling_zeta`): the flip is visible to the coupling of the tower it touches.
-/

open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (realTests)
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros goldenConfig
  temperedConfig_goldenConfig)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- **The coupling form counts the seen right zeros** of every tempered configuration. -/
theorem negIndex_lap_lap_orbitKernel (Z : Zeta23.ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {a b : HeckeLattice} (ha : a ≠ 1) (hb : b ≠ 1) :
    negIndex (lap a (lap b (orbitKernel Z f))) = (seenRightZeros Z f).encard := by
  rw [← orbitKernel_mixedDiff Z hZ hf, negIndex_orbitKernel_mixedDiff Z hZ hf (scale_ne_zero ha)
    (scale_ne_zero hb), negIndex_orbitKernel Z hZ hf]

/-- **The golden fake curve has infinite coupling index.** -/
theorem negIndex_lap_lap_golden {a b : HeckeLattice} (ha : a ≠ 1) (hb : b ≠ 1) :
    negIndex (lap a (lap b (orbitKernel goldenConfig cubicSpline))) = ⊤ := by
  rw [← orbitKernel_mixedDiff _ temperedConfig_goldenConfig cubicSpline_mem_realTests,
    negIndex_orbitKernel_mixedDiff _ temperedConfig_goldenConfig cubicSpline_mem_realTests
      (scale_ne_zero ha) (scale_ne_zero hb), negIndex_orbitKernel_golden]

/-- **A prime flip changes the coupling of its tower.** For a test supported in `[−a, a]` with
`2a ≤ log p`, the coupling at `(p, p)` of the `p`-flipped twin differs from that of `ζ` by
`−4 log p ‖f‖²/√p`. -/
theorem coupling_flip_sub_coupling_zeta {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ} {a : ℝ}
    (ha : ∀ u, a ≤ |u| → f u = 0) (hap : 2 * a ≤ Real.log p) :
    coupling (weightKernel (ArithmeticCountingPositivity.primeFlipWeight p) f)
        (primeElt hp) (primeElt hp) -
      coupling (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f)
        (primeElt hp) (primeElt hp) =
      ((-(4 * Real.log p * RHTower.crossCorr f f 0 / Real.sqrt p)) : ℝ) := by
  have h := fun d : ℤ => weightKernel_flip_tower hp ha hap d
  have e2 : primeElt hp * primeElt hp = towerPt hp 2 := by
    rw [towerPt, show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one]
  have e1 : primeElt hp = towerPt hp 1 := by rw [towerPt, zpow_one]
  have e0 : (1 : HeckeLattice) = towerPt hp 0 := by rw [towerPt, zpow_zero]
  simp only [coupling]
  rw [e2, e1, e0, h 2, h 1, h 0]
  simp only [flipJump, show ¬Odd (2 : ℤ) by decide, show Odd (1 : ℤ) by decide,
    show ¬Odd (0 : ℤ) by decide, if_false, if_true, Int.natAbs_one, pow_one]
  push_cast
  ring

end GaloisForLFunctions.ArithmeticCouplingTheory
