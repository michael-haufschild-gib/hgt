import GaloisForLFunctions.RHTower.DivisorCoreMellinBoundary
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleNoLimit

open Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

private theorem half_pos : (0 : ℝ) < 1 / 2 := by norm_num

noncomputable def routeTInverseGeomDefect (t : ℝ) (p : Nat.Primes) : ℝ :=
  geomDefect (primeNome half_pos p).val (phaseAngle (primeNome half_pos p) (2 * t))

theorem routeTInverseGeomDefect_nonneg (t : ℝ) (p : Nat.Primes) :
    0 ≤ routeTInverseGeomDefect t p := by
  exact geomDefect_nonneg (primeNome half_pos p).pos
    (primeNome half_pos p).lt_one _

theorem not_summable_routeTInverseGeomDefect {t : ℝ} (ht : t ≠ 0) :
    ¬ Summable (routeTInverseGeomDefect t) := by
  intro hs
  have hlead := not_summable_leading (σ := (1 / 2 : ℝ)) (τ := 2 * t)
    half_pos (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ht)
  apply hlead
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hs.mul_left 4)
  · have hcos := Real.cos_le_one (phaseAngle (primeNome half_pos p) (2 * t))
    have hq := (primeNome half_pos p).pos
    dsimp [primeNome]
    positivity
  · have hge := geomDefect_ge (primeNome half_pos p).pos
      (primeNome half_pos p).lt_one (phaseAngle (primeNome half_pos p) (2 * t))
    change (primeNome half_pos p).val *
      (1 - Real.cos (phaseAngle (primeNome half_pos p) (2 * t))) ≤
        4 * routeTInverseGeomDefect t p
    unfold routeTInverseGeomDefect
    linarith

theorem tendsto_routeTInverseGeomDefect_sum {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun s : Finset Nat.Primes => ∑ p ∈ s, routeTInverseGeomDefect t p)
      atTop atTop :=
  tendsto_finsetSum_atTop_of_not_summable
    (routeTInverseGeomDefect_nonneg t) (not_summable_routeTInverseGeomDefect ht)

end RHTower
