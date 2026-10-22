import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.RHTower.ThetaWignerCenterMix
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Strict log-concavity of the Riemann--Jacobi theta kernel

The first theta atom has a large explicit negative logarithmic curvature.  This file keeps the
full `x`-dependent Gaussian in the higher-atom comparison and proves that the score variance of
the complete atom mixture cannot exhaust that curvature.  The result is an unconditional,
computation-free proof that `thetaCuspFullSource` is strictly log-concave on the nonnegative
half-line.

The proof repairs the missing perturbation step in the 2026 log-concavity preprints.  It does not
prove RH: order-two total positivity is strictly weaker than the all-order condition.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The natural positive exponential scale of the theta atoms. -/
def thetaCuspLogConcavityScale (x : ℝ) : ℝ :=
  Real.pi * Real.exp x ^ 2

/-- The fixed Gaussian tail weights used at derivative orders zero, one, and two. -/
def thetaCuspLogConcavityTailWeight (m k : ℕ) : ℝ :=
  ((k + 2 : ℕ) : ℝ) ^ m *
    Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))

theorem thetaCuspLogConcavityScale_gt_three {x : ℝ} (hx : 0 ≤ x) :
    3 < thetaCuspLogConcavityScale x := by
  have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hsq : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
  unfold thetaCuspLogConcavityScale
  nlinarith [Real.pi_gt_three, Real.pi_pos]

theorem thetaCuspLogConcavityScale_pos (x : ℝ) :
    0 < thetaCuspLogConcavityScale x := by
  unfold thetaCuspLogConcavityScale
  positivity

theorem summable_thetaCuspLogConcavityTailWeight (m : ℕ) :
    Summable (thetaCuspLogConcavityTailWeight m) := by
  have hbase := (summable_pow_mul_exp_neg_nat_sq m Real.pi_pos).mul_left
    (Real.exp Real.pi)
  have hfull : Summable (fun n : ℕ =>
      (n : ℝ) ^ m * Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) := by
    refine hbase.congr fun n => ?_
    rw [show -Real.pi * ((n : ℝ) ^ 2 - 1) =
      Real.pi + (-Real.pi * (n : ℝ) ^ 2) by ring, Real.exp_add]
    ring
  exact hfull.comp_injective (fun _ _ h => Nat.add_right_cancel h)

private theorem thetaCusp_nat_add_two_pow_six_le (k : ℕ) :
    (((k + 2 : ℕ) : ℝ) ^ 6) ≤ 64 * (64 : ℝ) ^ k := by
  have hnat := thetaCusp_nat_add_two_le_two_pow_succ k
  have hcast : ((k + 2 : ℕ) : ℝ) ≤ (2 ^ (k + 1) : ℕ) := by
    exact_mod_cast hnat
  calc
    (((k + 2 : ℕ) : ℝ) ^ 6) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) ^ 6 := by gcongr
    _ = 64 * (64 : ℝ) ^ k := by
      push_cast
      calc
        ((2 : ℝ) ^ (k + 1)) ^ 6 = (2 : ℝ) ^ ((k + 1) * 6) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (6 * (k + 1)) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ 6) ^ (k + 1) := by rw [pow_mul]
        _ = 64 * 64 ^ k := by rw [pow_succ']; norm_num

private theorem thetaCusp_nat_add_two_pow_eight_le (k : ℕ) :
    (((k + 2 : ℕ) : ℝ) ^ 8) ≤ 256 * (256 : ℝ) ^ k := by
  have hnat := thetaCusp_nat_add_two_le_two_pow_succ k
  have hcast : ((k + 2 : ℕ) : ℝ) ≤ (2 ^ (k + 1) : ℕ) := by
    exact_mod_cast hnat
  calc
    (((k + 2 : ℕ) : ℝ) ^ 8) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) ^ 8 := by gcongr
    _ = 256 * (256 : ℝ) ^ k := by
      push_cast
      calc
        ((2 : ℝ) ^ (k + 1)) ^ 8 = (2 : ℝ) ^ ((k + 1) * 8) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (8 * (k + 1)) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ 8) ^ (k + 1) := by rw [pow_mul]
        _ = 256 * 256 ^ k := by rw [pow_succ']; norm_num

private theorem thetaCusp_tail_exponent_add_two_le (k : ℕ) :
    Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1)) ≤
      Real.exp (-3 * Real.pi) * (Real.exp (-5 * Real.pi)) ^ k := by
  have hsquare :
      (3 : ℝ) + 5 * k ≤ (((k + 2 : ℕ) : ℝ) ^ 2 - 1) := by
    rcases k with _ | k
    · norm_num
    · push_cast
      nlinarith [sq_nonneg (k : ℝ)]
  have hexponent :
      -Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1) ≤
        -3 * Real.pi + (k : ℕ) * (-5 * Real.pi) := by
    nlinarith [Real.pi_pos]
  calc
    _ ≤ Real.exp (-3 * Real.pi + (k : ℕ) * (-5 * Real.pi)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]

private theorem thetaCusp_sixtyfour_mul_exp_neg_five_pi_le :
    64 * Real.exp (-5 * Real.pi) ≤ (1 : ℝ) / 250 := by
  nlinarith [thetaCusp_sixteen_mul_exp_neg_five_pi_lt]

private theorem thetaCusp_two_fiftysix_mul_exp_neg_five_pi_le :
    256 * Real.exp (-5 * Real.pi) ≤ (2 : ℝ) / 125 := by
  nlinarith [thetaCusp_sixteen_mul_exp_neg_five_pi_lt]

theorem thetaCuspLogConcavityTailWeight_six_add_two_le_geometric (k : ℕ) :
    thetaCuspLogConcavityTailWeight 6 k ≤
      (2 / 375 : ℝ) * ((1 / 250 : ℝ) ^ k) := by
  have hpow := thetaCusp_nat_add_two_pow_six_le k
  have hexp := thetaCusp_tail_exponent_add_two_le k
  have ha : Real.exp (-3 * Real.pi) ≤ (1 : ℝ) / 12000 :=
    thetaCusp_exp_neg_three_pi_lt.le
  have hr := thetaCusp_sixtyfour_mul_exp_neg_five_pi_le
  unfold thetaCuspLogConcavityTailWeight
  calc
    (((k + 2 : ℕ) : ℝ) ^ 6) *
        Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1)) ≤
      (64 * (64 : ℝ) ^ k) *
        (Real.exp (-3 * Real.pi) * (Real.exp (-5 * Real.pi)) ^ k) := by
      gcongr
    _ = 64 * Real.exp (-3 * Real.pi) *
        (64 * Real.exp (-5 * Real.pi)) ^ k := by ring
    _ ≤ 64 * ((1 : ℝ) / 12000) * ((1 / 250 : ℝ) ^ k) := by gcongr
    _ = (2 / 375 : ℝ) * ((1 / 250 : ℝ) ^ k) := by ring

theorem thetaCuspLogConcavityTailWeight_eight_add_two_le_geometric (k : ℕ) :
    thetaCuspLogConcavityTailWeight 8 k ≤
      (8 / 375 : ℝ) * ((2 / 125 : ℝ) ^ k) := by
  have hpow := thetaCusp_nat_add_two_pow_eight_le k
  have hexp := thetaCusp_tail_exponent_add_two_le k
  have ha : Real.exp (-3 * Real.pi) ≤ (1 : ℝ) / 12000 :=
    thetaCusp_exp_neg_three_pi_lt.le
  have hr := thetaCusp_two_fiftysix_mul_exp_neg_five_pi_le
  unfold thetaCuspLogConcavityTailWeight
  calc
    (((k + 2 : ℕ) : ℝ) ^ 8) *
        Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1)) ≤
      (256 * (256 : ℝ) ^ k) *
        (Real.exp (-3 * Real.pi) * (Real.exp (-5 * Real.pi)) ^ k) := by
      gcongr
    _ = 256 * Real.exp (-3 * Real.pi) *
        (256 * Real.exp (-5 * Real.pi)) ^ k := by ring
    _ ≤ 256 * ((1 : ℝ) / 12000) * ((2 / 125 : ℝ) ^ k) := by gcongr
    _ = (8 / 375 : ℝ) * ((2 / 125 : ℝ) ^ k) := by ring

theorem tsum_thetaCuspLogConcavityTailWeight_four_le :
    (∑' k : ℕ, thetaCuspLogConcavityTailWeight 4 k) ≤ (4 : ℝ) / 2997 := by
  have h := thetaCuspHigherAtomDominationWeight_le_geometric_rational
  unfold thetaCuspHigherAtomDominationWeight thetaCuspSourceAtomDominationWeight at h
  have heq :
      (2 : ℝ) * (∑' k : ℕ, thetaCuspLogConcavityTailWeight 4 k) =
        ∑' k : ℕ, 2 * (((k + 2 : ℕ) : ℝ) ^ 4) *
          Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    unfold thetaCuspLogConcavityTailWeight
    ring
  nlinarith [heq]

theorem tsum_thetaCuspLogConcavityTailWeight_six_le :
    (∑' k : ℕ, thetaCuspLogConcavityTailWeight 6 k) ≤ (4 : ℝ) / 747 := by
  have hweight := summable_thetaCuspLogConcavityTailWeight 6
  have hgeo : Summable (fun k : ℕ =>
      (2 / 375 : ℝ) * ((1 / 250 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one (by norm_num :
      ‖(1 / 250 : ℝ)‖ < 1)).mul_left _
  calc
    (∑' k : ℕ, thetaCuspLogConcavityTailWeight 6 k) ≤
        ∑' k : ℕ, (2 / 375 : ℝ) * ((1 / 250 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspLogConcavityTailWeight_six_add_two_le_geometric hweight hgeo
    _ = (2 / 375 : ℝ) * (1 - (1 / 250 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (4 : ℝ) / 747 := by norm_num

theorem tsum_thetaCuspLogConcavityTailWeight_eight_le :
    (∑' k : ℕ, thetaCuspLogConcavityTailWeight 8 k) ≤ (8 : ℝ) / 369 := by
  have hweight := summable_thetaCuspLogConcavityTailWeight 8
  have hgeo : Summable (fun k : ℕ =>
      (8 / 375 : ℝ) * ((2 / 125 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one (by norm_num :
      ‖(2 / 125 : ℝ)‖ < 1)).mul_left _
  calc
    (∑' k : ℕ, thetaCuspLogConcavityTailWeight 8 k) ≤
        ∑' k : ℕ, (8 / 375 : ℝ) * ((2 / 125 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspLogConcavityTailWeight_eight_add_two_le_geometric hweight hgeo
    _ = (8 / 375 : ℝ) * (1 - (2 / 125 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (8 : ℝ) / 369 := by norm_num

private theorem thetaCusp_scale_exp_tail_one
    {tau d : ℝ} (htau : Real.pi ≤ tau) (hd : 3 ≤ d) :
    tau * Real.exp (-tau * d) ≤ 4 * Real.exp (-Real.pi * d) := by
  let y : ℝ := tau - Real.pi
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hdy : 0 ≤ d * y := mul_nonneg (by linarith) hy
  have hexp : 1 + d * y ≤ Real.exp (d * y) := by
    simpa [add_comm] using Real.add_one_le_exp (d * y)
  have htauFour : tau ≤ 4 + y := by
    dsimp [y]
    nlinarith [Real.pi_lt_four]
  have hlin : 4 + y ≤ 4 * (1 + d * y) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hy]
  have htauExp : tau ≤ 4 * Real.exp (d * y) :=
    htauFour.trans (hlin.trans (mul_le_mul_of_nonneg_left hexp (by norm_num)))
  calc
    tau * Real.exp (-tau * d) ≤
        (4 * Real.exp (d * y)) * Real.exp (-tau * d) := by gcongr
    _ = 4 * Real.exp (-Real.pi * d) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [y]
      congr 2
      ring

private theorem thetaCusp_scale_exp_tail_two
    {tau d : ℝ} (htau : Real.pi ≤ tau) (hd : 3 ≤ d) :
    tau ^ 2 * Real.exp (-tau * d) ≤ 16 * Real.exp (-Real.pi * d) := by
  let y : ℝ := tau - Real.pi
  let z : ℝ := d * y
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; exact mul_nonneg (by linarith) hy
  have hzy : 3 * y ≤ z := by
    dsimp [z]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hy]
  have hTaylor0 := Real.sum_le_exp_of_nonneg hz 3
  have hTaylor : 1 + z + z ^ 2 / 2 ≤ Real.exp z := by
    norm_num [Finset.sum_range_succ] at hTaylor0 ⊢
    exact hTaylor0
  have htauFour : tau ≤ 4 + y := by
    dsimp [y]
    nlinarith [Real.pi_lt_four]
  have hsq : tau ^ 2 ≤ (4 + y) ^ 2 := by
    exact sq_le_sq₀ (le_trans Real.pi_pos.le htau)
      (by positivity) |>.2 htauFour
  have hpoly : (4 + y) ^ 2 ≤ 16 * (1 + z + z ^ 2 / 2) := by
    nlinarith [sq_nonneg z, sq_nonneg y]
  have htauExp : tau ^ 2 ≤ 16 * Real.exp z :=
    hsq.trans (hpoly.trans (mul_le_mul_of_nonneg_left hTaylor (by norm_num)))
  calc
    tau ^ 2 * Real.exp (-tau * d) ≤
        (16 * Real.exp z) * Real.exp (-tau * d) := by gcongr
    _ = 16 * Real.exp (-Real.pi * d) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [z, y]
      congr 2
      ring

theorem thetaCuspLogConcavityScale_mul_exp_tail_one
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLogConcavityScale x *
        Real.exp (-thetaCuspLogConcavityScale x * ((n : ℝ) ^ 2 - 1)) ≤
      4 * Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) := by
  have htau : Real.pi ≤ thetaCuspLogConcavityScale x := by
    unfold thetaCuspLogConcavityScale
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hs : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
    nlinarith [Real.pi_pos]
  have hd : (3 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact thetaCusp_scale_exp_tail_one htau hd

theorem thetaCuspLogConcavityScale_sq_mul_exp_tail_two
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLogConcavityScale x ^ 2 *
        Real.exp (-thetaCuspLogConcavityScale x * ((n : ℝ) ^ 2 - 1)) ≤
      16 * Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) := by
  have htau : Real.pi ≤ thetaCuspLogConcavityScale x := by
    unfold thetaCuspLogConcavityScale
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hs : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
    nlinarith [Real.pi_pos]
  have hd : (3 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact thetaCusp_scale_exp_tail_two htau hd

theorem thetaCuspSourceTerm_one_pos_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspSourceTerm x 1 := by
  let u : ℝ := Real.exp x
  have hu : 1 ≤ u := by dsimp [u]; exact Real.one_le_exp hx
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hcore : 0 < 2 * Real.pi * u ^ 2 - 3 := by
    nlinarith [Real.pi_gt_three, sq_nonneg u]
  rw [thetaCuspSourceTerm, thetaCuspSeed]
  simp only [Nat.cast_one, one_mul]
  rw [show 2 * Real.pi * u ^ 4 - 3 * u ^ 2 =
    u ^ 2 * (2 * Real.pi * u ^ 2 - 3) by ring]
  positivity

/-- The source comparison retaining the full Gaussian separation at the current point. -/
theorem thetaCuspSourceTerm_le_first_dynamic
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x n ≤
      (2 * (n : ℝ) ^ 4 *
        Real.exp (-thetaCuspLogConcavityScale x * ((n : ℝ) ^ 2 - 1))) *
          thetaCuspSourceTerm x 1 := by
  let u : ℝ := Real.exp x
  have hu : 1 ≤ u := by dsimp [u]; exact Real.one_le_exp hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly_u :
      0 ≤ 2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2) := by
    have hcore : 0 ≤ 2 * Real.pi * u ^ 2 - 3 := by
      nlinarith [Real.pi_gt_three, sq_nonneg u]
    rw [show 2 * Real.pi * u ^ 4 - 3 * u ^ 2 =
      u ^ 2 * (2 * Real.pi * u ^ 2 - 3) by ring]
    positivity
  have hpolyUpper :
      2 * Real.pi *
          (2 * Real.pi * ((n : ℝ) * u) ^ 4 - 3 * ((n : ℝ) * u) ^ 2) ≤
        2 * (n : ℝ) ^ 4 *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2)) := by
    have hcore : 0 ≤ 2 * Real.pi * u ^ 2 - 6 := by
      nlinarith [Real.pi_gt_three, sq_nonneg u]
    have hbracket :
        0 ≤ (n : ℝ) ^ 2 * (2 * Real.pi * u ^ 2 - 6) + 3 := by positivity
    have hid :
        2 * (n : ℝ) ^ 4 *
              (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2)) -
            2 * Real.pi *
              (2 * Real.pi * ((n : ℝ) * u) ^ 4 - 3 * ((n : ℝ) * u) ^ 2) =
          2 * Real.pi * (n : ℝ) ^ 2 * u ^ 2 *
            ((n : ℝ) ^ 2 * (2 * Real.pi * u ^ 2 - 6) + 3) := by ring
    apply sub_nonneg.mp
    rw [hid]
    positivity
  have hgauss :
      Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2) =
        Real.exp (-thetaCuspLogConcavityScale x * ((n : ℝ) ^ 2 - 1)) *
          Real.exp (-Real.pi * u ^ 2) := by
    rw [← Real.exp_add]
    unfold thetaCuspLogConcavityScale
    dsimp [u]
    congr 1
    ring
  unfold thetaCuspSourceTerm thetaCuspSeed
  simp only [Nat.cast_one, one_mul]
  change Real.exp (x / 2) *
      (2 * Real.pi *
        (2 * Real.pi * ((n : ℝ) * u) ^ 4 - 3 * ((n : ℝ) * u) ^ 2) *
          Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2)) ≤ _
  change _ ≤ (2 * (n : ℝ) ^ 4 *
      Real.exp (-thetaCuspLogConcavityScale x * ((n : ℝ) ^ 2 - 1))) *
        (Real.exp (x / 2) *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2) *
            Real.exp (-Real.pi * u ^ 2)))
  rw [hgauss]
  calc
    Real.exp (x / 2) *
        (2 * Real.pi *
          (2 * Real.pi * ((n : ℝ) * u) ^ 4 - 3 * ((n : ℝ) * u) ^ 2) *
            (Real.exp (-thetaCuspLogConcavityScale x * ((n : ℝ) ^ 2 - 1)) *
              Real.exp (-Real.pi * u ^ 2))) ≤
      Real.exp (x / 2) *
        ((2 * (n : ℝ) ^ 4 *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2))) *
            (Real.exp (-thetaCuspLogConcavityScale x * ((n : ℝ) ^ 2 - 1)) *
              Real.exp (-Real.pi * u ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right hpolyUpper
        positivity
    _ = _ := by ring

private theorem thetaCuspMorseScale_eq_logConcavityScale_mul_sq (n : ℕ) (x : ℝ) :
    thetaCuspMorseScale n x =
      thetaCuspLogConcavityScale x * (n : ℝ) ^ 2 := by
  simp only [thetaCuspMorseScale, thetaCuspLogConcavityScale]
  ring

theorem abs_two_mul_thetaCuspBornWittenSuperpotential_le
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    |-2 * thetaCuspBornWittenSuperpotential n x| ≤
      2 * thetaCuspLogConcavityScale x * (n : ℝ) ^ 2 := by
  let A : ℝ := thetaCuspLogConcavityScale x * (n : ℝ) ^ 2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htau := thetaCuspLogConcavityScale_gt_three hx
  have hA : 3 < A := by
    dsimp [A]
    nlinarith [sq_nonneg ((n : ℝ) - 1), thetaCuspLogConcavityScale_pos x]
  have hden : 0 < A - 3 / 2 := by linarith
  have hquot0 : 0 ≤ A / (A - 3 / 2) :=
    div_nonneg (by linarith) hden.le
  have hquot2 : A / (A - 3 / 2) ≤ 2 := by
    rw [div_le_iff₀ hden]
    linarith
  have hlower :
      -(2 * A) ≤ -2 * (A - 5 / 4 - A / (A - 3 / 2)) := by
    nlinarith
  have hupper :
      -2 * (A - 5 / 4 - A / (A - 3 / 2)) ≤ 2 * A := by
    nlinarith
  rw [thetaCuspBornWittenSuperpotential, thetaCuspMorseSuperpotential,
    thetaCuspBornWittenWeight_eq,
    thetaCuspMorseScale_eq_logConcavityScale_mul_sq]
  simpa only [A, mul_assoc] using (abs_le.mpr ⟨hlower, hupper⟩)

theorem thetaCuspBornWittenLogCurvature_bounds
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    4 * thetaCuspLogConcavityScale x * (n : ℝ) ^ 2 ≤
        thetaCuspBornWittenLogCurvature n x ∧
      thetaCuspBornWittenLogCurvature n x ≤
        3 * (thetaCuspLogConcavityScale x * (n : ℝ) ^ 2) ^ 2 := by
  let A : ℝ := thetaCuspLogConcavityScale x * (n : ℝ) ^ 2
  have htau := thetaCuspLogConcavityScale_gt_three hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : 3 < A := by
    dsimp [A]
    nlinarith [sq_nonneg ((n : ℝ) - 1), thetaCuspLogConcavityScale_pos x]
  have hden : 3 / 2 < A - 3 / 2 := by linarith
  have hden0 : 0 < A - 3 / 2 := hden.trans' (by norm_num)
  have hdenSq : (9 / 4 : ℝ) ≤ (A - 3 / 2) ^ 2 := by nlinarith
  have hcorr0 : 0 ≤ 6 * A / (A - 3 / 2) ^ 2 := by positivity
  have hcorr : 6 * A / (A - 3 / 2) ^ 2 ≤ (8 / 3 : ℝ) * A := by
    rw [div_le_iff₀ (sq_pos_of_pos hden0)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ A) (sub_nonneg.mpr hdenSq)]
  rw [thetaCuspBornWittenLogCurvature, thetaCuspBornWittenCurvature,
    thetaCuspBornWittenWeight_eq,
    thetaCuspMorseScale_eq_logConcavityScale_mul_sq]
  simpa only [A, mul_assoc] using (show
    4 * A ≤ 2 * (2 * A + 3 * A / (A - 3 / 2) ^ 2) ∧
      2 * (2 * A + 3 * A / (A - 3 / 2) ^ 2) ≤ 3 * A ^ 2 by
        constructor
        · calc
            4 * A ≤ 4 * A + 6 * A / (A - 3 / 2) ^ 2 :=
              le_add_of_nonneg_right hcorr0
            _ = 2 * (2 * A + 3 * A / (A - 3 / 2) ^ 2) := by ring
        · have hA0 : 0 ≤ A := by linarith
          have hfactor : 0 ≤ 3 * A - 20 / 3 := by linarith
          have hquad := mul_nonneg hA0 hfactor
          calc
            2 * (2 * A + 3 * A / (A - 3 / 2) ^ 2) =
                4 * A + 6 * A / (A - 3 / 2) ^ 2 := by ring
            _ ≤ 4 * A + (8 / 3 : ℝ) * A := by
              simpa only [add_comm] using add_le_add_left hcorr (4 * A)
            _ = (20 / 3 : ℝ) * A := by ring
            _ ≤ 3 * A ^ 2 := by nlinarith)

theorem abs_iteratedDeriv_one_thetaCuspSourceTerm_le
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv 1 (fun y : ℝ => thetaCuspSourceTerm y n) x| ≤
      2 * thetaCuspLogConcavityScale x * (n : ℝ) ^ 2 *
        thetaCuspSourceTerm x n := by
  have hw := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hn).le
  rw [iteratedDeriv_one,
    (hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hn hx).deriv,
    abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right
    (abs_two_mul_thetaCuspBornWittenSuperpotential_le hn hx.le) hw

theorem iteratedDeriv_two_thetaCuspSourceTerm_eq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y n) x =
      (((-2 * thetaCuspBornWittenSuperpotential n x) ^ 2 -
          thetaCuspBornWittenLogCurvature n x) *
        thetaCuspSourceTerm x n) := by
  have hEq :
      (fun y : ℝ => deriv (fun z : ℝ => thetaCuspSourceTerm z n) y) =ᶠ[nhds x]
        fun y : ℝ => -2 * thetaCuspBornWittenSuperpotential n y *
          thetaCuspSourceTerm y n := by
    filter_upwards [show ∀ᶠ y : ℝ in nhds x, y ∈ Ioi 0 from Ioi_mem_nhds hx] with y hy
    exact (hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hn hy).deriv
  have hscore :=
    (hasDerivAt_thetaCuspBornWittenSuperpotential hn hx.le).const_mul (-2)
  have hterm := hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hn hx
  have hprod := hscore.mul hterm
  have hsecond := hprod.congr_of_eventuallyEq hEq
  rw [show iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y n) x =
      deriv (fun y : ℝ => deriv (fun z : ℝ => thetaCuspSourceTerm z n) y) x by
    simp [iteratedDeriv_succ]]
  rw [hsecond.deriv]
  simp only [thetaCuspBornWittenLogCurvature]
  ring

theorem abs_iteratedDeriv_two_thetaCuspSourceTerm_le
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y n) x| ≤
      7 * (thetaCuspLogConcavityScale x * (n : ℝ) ^ 2) ^ 2 *
        thetaCuspSourceTerm x n := by
  let A : ℝ := thetaCuspLogConcavityScale x * (n : ℝ) ^ 2
  have hs := abs_two_mul_thetaCuspBornWittenSuperpotential_le hn hx.le
  have hc := (thetaCuspBornWittenLogCurvature_bounds hn hx.le).2
  have hscale0 : 0 ≤ thetaCuspLogConcavityScale x :=
    (thetaCuspLogConcavityScale_pos x).le
  have hbase : 0 ≤ 4 * thetaCuspLogConcavityScale x * (n : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hscale0) (sq_nonneg _)
  have hc0 : 0 ≤ thetaCuspBornWittenLogCurvature n x :=
    hbase.trans (thetaCuspBornWittenLogCurvature_bounds hn hx.le).1
  have hsA : |-2 * thetaCuspBornWittenSuperpotential n x| ≤ 2 * A := by
    simpa only [A, mul_assoc] using hs
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hsq : (-2 * thetaCuspBornWittenSuperpotential n x) ^ 2 ≤
      (2 * A) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (-2 * thetaCuspBornWittenSuperpotential n x))
        (mul_nonneg (by norm_num) hA0)).2 hsA
  have hcA : thetaCuspBornWittenLogCurvature n x ≤ 3 * A ^ 2 := by
    simpa only [A] using hc
  have hw := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hn).le
  rw [iteratedDeriv_two_thetaCuspSourceTerm_eq hn hx, abs_mul,
    abs_of_nonneg hw]
  apply mul_le_mul_of_nonneg_right _ hw
  calc
    |(-2 * thetaCuspBornWittenSuperpotential n x) ^ 2 -
        thetaCuspBornWittenLogCurvature n x| ≤
      (-2 * thetaCuspBornWittenSuperpotential n x) ^ 2 +
        thetaCuspBornWittenLogCurvature n x := by
      calc
        _ ≤ |(-2 * thetaCuspBornWittenSuperpotential n x) ^ 2| +
            |thetaCuspBornWittenLogCurvature n x| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hc0]
    _ ≤ 4 * A ^ 2 + 3 * A ^ 2 := by
      nlinarith [hsq, hcA]
    _ = 7 * A ^ 2 := by ring

theorem thetaCuspSourceTerm_logConcavityNumerator_le
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y n) x *
          thetaCuspSourceTerm x n -
        iteratedDeriv 1 (fun y : ℝ => thetaCuspSourceTerm y n) x ^ 2 ≤
      -(4 * thetaCuspLogConcavityScale x * (n : ℝ) ^ 2) *
        thetaCuspSourceTerm x n ^ 2 := by
  have hfirst := (hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hn hx).deriv
  have hcurv := (thetaCuspBornWittenLogCurvature_bounds hn hx.le).1
  have hw := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hn).le
  rw [iteratedDeriv_one, hfirst,
    iteratedDeriv_two_thetaCuspSourceTerm_eq hn hx]
  have hmul := mul_le_mul_of_nonneg_right hcurv (sq_nonneg (thetaCuspSourceTerm x n))
  nlinarith

/-- The higher-atom tail of the `m`th derivative series. -/
def thetaCuspHigherDerivative (m : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, iteratedDeriv m
    (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x

private theorem iteratedDeriv_thetaCuspSourceTerm_zero (m : ℕ) (x : ℝ) :
    iteratedDeriv m (fun y : ℝ => thetaCuspSourceTerm y 0) x = 0 := by
  rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  unfold thetaCuspPolynomialAtom
  simp only [Nat.cast_zero, zero_mul]
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    thetaCuspLogDerivativePolynomial_coeff_zero]
  ring

theorem thetaCuspFullDerivative_eq_one_add_higher (m : ℕ) (x : ℝ) :
    thetaCuspFullDerivative m x =
      iteratedDeriv m (fun y : ℝ => thetaCuspSourceTerm y 1) x +
        thetaCuspHigherDerivative m x := by
  have hs := summable_iteratedDeriv_thetaCuspSourceTerm m x
  rw [thetaCuspFullDerivative, thetaCuspHigherDerivative,
    ← hs.sum_add_tsum_nat_add 2]
  simp [Finset.sum_range_succ, iteratedDeriv_thetaCuspSourceTerm_zero]

theorem thetaCuspHigherDerivative_zero_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ thetaCuspHigherDerivative 0 x := by
  unfold thetaCuspHigherDerivative
  exact tsum_nonneg fun k => by
    simp only [iteratedDeriv_zero]
    exact (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by omega)).le

theorem thetaCuspHigherDerivative_zero_le
    {x : ℝ} (hx : 0 < x) :
    thetaCuspHigherDerivative 0 x ≤
      (8 / 2997 : ℝ) * thetaCuspSourceTerm x 1 := by
  have hsplit := thetaCuspFullDerivative_eq_one_add_higher 0 x
  simp only [iteratedDeriv_zero] at hsplit
  have h := thetaCuspFullSource_sub_first_le hx.le
  rw [show thetaCuspFullDerivative 0 x = thetaCuspFullSource x by rfl] at hsplit
  have hweight : thetaCuspHigherAtomDominationWeight ≤ (8 : ℝ) / 2997 :=
    thetaCuspHigherAtomDominationWeight_le_geometric_rational
  have hw :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos (n := 1) hx (by norm_num)).le
  have hmul : thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1 ≤
      (8 / 2997 : ℝ) * thetaCuspSourceTerm x 1 :=
    mul_le_mul_of_nonneg_right hweight hw
  calc
    thetaCuspHigherDerivative 0 x =
        thetaCuspFullSource x - thetaCuspSourceTerm x 1 := by linarith
    _ ≤ thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1 := h
    _ ≤ (8 / 2997 : ℝ) * thetaCuspSourceTerm x 1 := hmul

theorem thetaCuspLogConcavityScale_sq_mul_higher_zero_le
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogConcavityScale x ^ 2 * thetaCuspHigherDerivative 0 x ≤
      (128 / 2997 : ℝ) * thetaCuspSourceTerm x 1 := by
  let tau := thetaCuspLogConcavityScale x
  let w := thetaCuspSourceTerm x 1
  have htau0 : 0 ≤ tau := (thetaCuspLogConcavityScale_pos x).le
  have hw : 0 ≤ w := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).le
  have htail : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + 2)) :=
    (summable_thetaCuspSourceTerm x).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hweight := summable_thetaCuspLogConcavityTailWeight 4
  have hmajor : Summable (fun k : ℕ =>
      32 * thetaCuspLogConcavityTailWeight 4 k * w) :=
    (hweight.mul_left 32).mul_right w
  change tau ^ 2 * (∑' k : ℕ, thetaCuspSourceTerm x (k + 2)) ≤ _
  rw [← tsum_mul_left]
  calc
    (∑' k : ℕ, tau ^ 2 * thetaCuspSourceTerm x (k + 2)) ≤
        ∑' k : ℕ, 32 * thetaCuspLogConcavityTailWeight 4 k * w := by
      apply Summable.tsum_le_tsum _ (htail.mul_left _) hmajor
      intro k
      let n := k + 2
      have hn : 2 ≤ n := by dsimp [n]; omega
      have hterm := thetaCuspSourceTerm_le_first_dynamic
        (n := n) (by omega) hx.le
      have hexp := thetaCuspLogConcavityScale_sq_mul_exp_tail_two hn hx.le
      have hnonneg : 0 ≤ thetaCuspSourceTerm x n :=
        (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by omega)).le
      dsimp [n] at hterm hexp ⊢
      unfold thetaCuspLogConcavityTailWeight
      calc
        tau ^ 2 * thetaCuspSourceTerm x (k + 2) ≤
            tau ^ 2 *
              ((2 * (((k + 2 : ℕ) : ℝ) ^ 4) *
                Real.exp (-tau * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w) := by
          gcongr
        _ = 2 * (((k + 2 : ℕ) : ℝ) ^ 4) *
            (tau ^ 2 * Real.exp (-tau * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by ring
        _ ≤ 2 * (((k + 2 : ℕ) : ℝ) ^ 4) *
            (16 * Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by
          gcongr
        _ = 32 * ((((k + 2 : ℕ) : ℝ) ^ 4) *
            Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by ring
    _ = 32 * (∑' k : ℕ, thetaCuspLogConcavityTailWeight 4 k) * w := by
      rw [tsum_mul_right, tsum_mul_left]
    _ ≤ 32 * ((4 : ℝ) / 2997) * w := by
      gcongr
      exact tsum_thetaCuspLogConcavityTailWeight_four_le
    _ = (128 / 2997 : ℝ) * w := by ring

theorem thetaCuspLogConcavityScale_mul_abs_higher_one_le
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogConcavityScale x * |thetaCuspHigherDerivative 1 x| ≤
      (256 / 747 : ℝ) * thetaCuspSourceTerm x 1 := by
  let tau := thetaCuspLogConcavityScale x
  let w := thetaCuspSourceTerm x 1
  have htau0 : 0 ≤ tau := (thetaCuspLogConcavityScale_pos x).le
  have hw : 0 ≤ w := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).le
  have hderiv : Summable (fun k : ℕ =>
      iteratedDeriv 1 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x) :=
    (summable_iteratedDeriv_thetaCuspSourceTerm 1 x).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have habs : Summable (fun k : ℕ =>
      |iteratedDeriv 1 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x|) := by
    simpa only [Real.norm_eq_abs] using hderiv.norm
  have hweight := summable_thetaCuspLogConcavityTailWeight 6
  have hmajor : Summable (fun k : ℕ =>
      64 * thetaCuspLogConcavityTailWeight 6 k * w) :=
    (hweight.mul_left 64).mul_right w
  unfold thetaCuspHigherDerivative
  calc
    tau * |∑' k : ℕ,
        iteratedDeriv 1 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x| ≤
      tau * ∑' k : ℕ,
        |iteratedDeriv 1 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x| := by
      apply mul_le_mul_of_nonneg_left _ htau0
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hderiv.norm
    _ = ∑' k : ℕ, tau *
        |iteratedDeriv 1 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x| := by
      rw [tsum_mul_left]
    _ ≤ ∑' k : ℕ, 64 * thetaCuspLogConcavityTailWeight 6 k * w := by
      apply Summable.tsum_le_tsum _ (habs.mul_left _) hmajor
      intro k
      let n := k + 2
      have hn : 2 ≤ n := by dsimp [n]; omega
      have hfirst := abs_iteratedDeriv_one_thetaCuspSourceTerm_le
        (n := n) (by omega) hx
      have hterm := thetaCuspSourceTerm_le_first_dynamic
        (n := n) (by omega) hx.le
      have hexp := thetaCuspLogConcavityScale_sq_mul_exp_tail_two hn hx.le
      dsimp [n] at hfirst hterm hexp ⊢
      unfold thetaCuspLogConcavityTailWeight
      calc
        tau * |iteratedDeriv 1
            (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x| ≤
          tau * (2 * tau * (((k + 2 : ℕ) : ℝ) ^ 2) *
            thetaCuspSourceTerm x (k + 2)) := by gcongr
        _ ≤ tau * (2 * tau * (((k + 2 : ℕ) : ℝ) ^ 2) *
            ((2 * (((k + 2 : ℕ) : ℝ) ^ 4) *
              Real.exp (-tau * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w)) := by
          gcongr
        _ = 4 * (((k + 2 : ℕ) : ℝ) ^ 6) *
            (tau ^ 2 * Real.exp (-tau * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by ring
        _ ≤ 4 * (((k + 2 : ℕ) : ℝ) ^ 6) *
            (16 * Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by
          gcongr
        _ = 64 * ((((k + 2 : ℕ) : ℝ) ^ 6) *
            Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by ring
    _ = 64 * (∑' k : ℕ, thetaCuspLogConcavityTailWeight 6 k) * w := by
      rw [tsum_mul_right, tsum_mul_left]
    _ ≤ 64 * ((4 : ℝ) / 747) * w := by
      gcongr
      exact tsum_thetaCuspLogConcavityTailWeight_six_le
    _ = (256 / 747 : ℝ) * w := by ring

theorem abs_thetaCuspHigherDerivative_two_le
    {x : ℝ} (hx : 0 < x) :
    |thetaCuspHigherDerivative 2 x| ≤
      (1792 / 369 : ℝ) * thetaCuspSourceTerm x 1 := by
  let tau := thetaCuspLogConcavityScale x
  let w := thetaCuspSourceTerm x 1
  have hw : 0 ≤ w := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).le
  have hderiv : Summable (fun k : ℕ =>
      iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x) :=
    (summable_iteratedDeriv_thetaCuspSourceTerm 2 x).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have habs : Summable (fun k : ℕ =>
      |iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x|) := by
    simpa only [Real.norm_eq_abs] using hderiv.norm
  have hweight := summable_thetaCuspLogConcavityTailWeight 8
  have hmajor : Summable (fun k : ℕ =>
      224 * thetaCuspLogConcavityTailWeight 8 k * w) :=
    (hweight.mul_left 224).mul_right w
  unfold thetaCuspHigherDerivative
  calc
    |∑' k : ℕ,
        iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x| ≤
      ∑' k : ℕ,
        |iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x| :=
      by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hderiv.norm
    _ ≤ ∑' k : ℕ, 224 * thetaCuspLogConcavityTailWeight 8 k * w := by
      apply Summable.tsum_le_tsum _ habs hmajor
      intro k
      let n := k + 2
      have hn : 2 ≤ n := by dsimp [n]; omega
      have hsecond := abs_iteratedDeriv_two_thetaCuspSourceTerm_le
        (n := n) (by omega) hx
      have hterm := thetaCuspSourceTerm_le_first_dynamic
        (n := n) (by omega) hx.le
      have hexp := thetaCuspLogConcavityScale_sq_mul_exp_tail_two hn hx.le
      dsimp [n] at hsecond hterm hexp ⊢
      unfold thetaCuspLogConcavityTailWeight
      calc
        |iteratedDeriv 2
            (fun y : ℝ => thetaCuspSourceTerm y (k + 2)) x| ≤
          7 * (tau * (((k + 2 : ℕ) : ℝ) ^ 2)) ^ 2 *
            thetaCuspSourceTerm x (k + 2) := hsecond
        _ ≤ 7 * (tau * (((k + 2 : ℕ) : ℝ) ^ 2)) ^ 2 *
            ((2 * (((k + 2 : ℕ) : ℝ) ^ 4) *
              Real.exp (-tau * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w) := by
          gcongr
        _ = 14 * (((k + 2 : ℕ) : ℝ) ^ 8) *
            (tau ^ 2 * Real.exp (-tau * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by ring
        _ ≤ 14 * (((k + 2 : ℕ) : ℝ) ^ 8) *
            (16 * Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by
          gcongr
        _ = 224 * ((((k + 2 : ℕ) : ℝ) ^ 8) *
            Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1))) * w := by ring
    _ = 224 * (∑' k : ℕ, thetaCuspLogConcavityTailWeight 8 k) * w := by
      rw [tsum_mul_right, tsum_mul_left]
    _ ≤ 224 * ((8 : ℝ) / 369) * w := by
      gcongr
      exact tsum_thetaCuspLogConcavityTailWeight_eight_le
    _ = (1792 / 369 : ℝ) * w := by ring

/-- Log-concavity numerator of the full Riemann--Jacobi theta source. -/
def thetaCuspLogConcavityNumerator (x : ℝ) : ℝ :=
  iteratedDeriv 2 thetaCuspFullSource x * thetaCuspFullSource x -
    iteratedDeriv 1 thetaCuspFullSource x ^ 2

theorem thetaCuspLogConcavityNumerator_le_firstAtom_sq
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogConcavityNumerator x ≤
      -5 * thetaCuspSourceTerm x 1 ^ 2 := by
  let tau := thetaCuspLogConcavityScale x
  let w := thetaCuspSourceTerm x 1
  let a := iteratedDeriv 1 (fun y : ℝ => thetaCuspSourceTerm y 1) x
  let b := iteratedDeriv 2 (fun y : ℝ => thetaCuspSourceTerm y 1) x
  let r0 := thetaCuspHigherDerivative 0 x
  let r1 := thetaCuspHigherDerivative 1 x
  let r2 := thetaCuspHigherDerivative 2 x
  have htau : 3 < tau := thetaCuspLogConcavityScale_gt_three hx.le
  have hw : 0 < w := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hr0 : 0 ≤ r0 := thetaCuspHigherDerivative_zero_nonneg hx
  have hq1 : b * w - a ^ 2 ≤ -(4 * tau) * w ^ 2 := by
    simpa [a, b, w, tau] using
      thetaCuspSourceTerm_logConcavityNumerator_le (n := 1) (by norm_num) hx
  have ha : |a| ≤ 2 * tau * w := by
    simpa [a, w, tau] using
      abs_iteratedDeriv_one_thetaCuspSourceTerm_le (n := 1) (by norm_num) hx
  have hb : |b| ≤ 7 * tau ^ 2 * w := by
    simpa [b, w, tau] using
      abs_iteratedDeriv_two_thetaCuspSourceTerm_le (n := 1) (by norm_num) hx
  have hr0small : r0 ≤ (8 / 2997 : ℝ) * w := by
    simpa [r0, w] using thetaCuspHigherDerivative_zero_le hx
  have htau2r0 : tau ^ 2 * r0 ≤ (128 / 2997 : ℝ) * w := by
    simpa [tau, r0, w] using
      thetaCuspLogConcavityScale_sq_mul_higher_zero_le hx
  have htaur1 : tau * |r1| ≤ (256 / 747 : ℝ) * w := by
    simpa [tau, r1, w] using
      thetaCuspLogConcavityScale_mul_abs_higher_one_le hx
  have hr2 : |r2| ≤ (1792 / 369 : ℝ) * w := by
    simpa [r2, w] using abs_thetaCuspHigherDerivative_two_le hx
  have hwr2 : w * r2 ≤ (1792 / 369 : ℝ) * w ^ 2 := by
    calc
      w * r2 ≤ w * |r2| := mul_le_mul_of_nonneg_left (le_abs_self r2) hw.le
      _ ≤ w * ((1792 / 369 : ℝ) * w) := by gcongr
      _ = (1792 / 369 : ℝ) * w ^ 2 := by ring
  have hbr0 : b * r0 ≤ (896 / 2997 : ℝ) * w ^ 2 := by
    calc
      b * r0 ≤ |b| * r0 := mul_le_mul_of_nonneg_right (le_abs_self b) hr0
      _ ≤ (7 * tau ^ 2 * w) * r0 := by gcongr
      _ = 7 * w * (tau ^ 2 * r0) := by ring
      _ ≤ 7 * w * ((128 / 2997 : ℝ) * w) := by gcongr
      _ = (896 / 2997 : ℝ) * w ^ 2 := by ring
  have hr0r2 : r0 * r2 ≤
      ((8 / 2997 : ℝ) * (1792 / 369 : ℝ)) * w ^ 2 := by
    calc
      r0 * r2 ≤ r0 * |r2| := mul_le_mul_of_nonneg_left (le_abs_self r2) hr0
      _ ≤ ((8 / 2997 : ℝ) * w) * ((1792 / 369 : ℝ) * w) := by gcongr
      _ = ((8 / 2997 : ℝ) * (1792 / 369 : ℝ)) * w ^ 2 := by ring
  have har1 : -2 * a * r1 ≤ (1024 / 747 : ℝ) * w ^ 2 := by
    calc
      -2 * a * r1 ≤ |-2 * a * r1| := le_abs_self _
      _ = 2 * |a| * |r1| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * (2 * tau * w) * |r1| := by gcongr
      _ = 4 * w * (tau * |r1|) := by ring
      _ ≤ 4 * w * ((256 / 747 : ℝ) * w) := by gcongr
      _ = (1024 / 747 : ℝ) * w ^ 2 := by ring
  let C : ℝ := (1792 / 369 : ℝ) + 896 / 2997 +
    (8 / 2997) * (1792 / 369) + 1024 / 747
  have hC : C < 7 := by norm_num [C]
  have hcross :
      w * r2 + b * r0 + r0 * r2 - 2 * a * r1 - r1 ^ 2 ≤ C * w ^ 2 := by
    have hsquare : 0 ≤ r1 ^ 2 := sq_nonneg r1
    dsimp [C]
    nlinarith
  have hcoeff : -(4 * tau) + C ≤ -5 := by linarith
  have htotal :
      (b * w - a ^ 2) +
          (w * r2 + b * r0 + r0 * r2 - 2 * a * r1 - r1 ^ 2) ≤
        -5 * w ^ 2 := by
    calc
      _ ≤ (-(4 * tau) + C) * w ^ 2 := by nlinarith
      _ ≤ -5 * w ^ 2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg w)
  have h0 := thetaCuspFullDerivative_eq_one_add_higher 0 x
  have h1 := thetaCuspFullDerivative_eq_one_add_higher 1 x
  have h2 := thetaCuspFullDerivative_eq_one_add_higher 2 x
  rw [← iteratedDeriv_thetaCuspFullSource] at h1 h2
  simp only [iteratedDeriv_zero] at h0
  change thetaCuspFullSource x = w + r0 at h0
  change iteratedDeriv 1 thetaCuspFullSource x = a + r1 at h1
  change iteratedDeriv 2 thetaCuspFullSource x = b + r2 at h2
  rw [thetaCuspLogConcavityNumerator, h0, h1, h2]
  nlinarith

theorem continuous_thetaCuspLogConcavityNumerator :
    Continuous thetaCuspLogConcavityNumerator := by
  have hderiv (m : ℕ) : Continuous (iteratedDeriv m thetaCuspFullSource) := by
    rw [iteratedDeriv_thetaCuspFullSource]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspFullDerivative m x).continuousAt
  unfold thetaCuspLogConcavityNumerator
  exact (hderiv 2).mul contDiff_thetaCuspFullSource.continuous |>.sub ((hderiv 1).pow 2)

theorem continuous_thetaCuspSourceTerm_one :
    Continuous (fun x : ℝ => thetaCuspSourceTerm x 1) := by
  unfold thetaCuspSourceTerm thetaCuspSeed
  fun_prop

/-- Uniform strict half-line log-concavity of the actual Riemann--Jacobi theta source. -/
theorem thetaCuspLogConcavityNumerator_neg
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLogConcavityNumerator x < 0 := by
  let S : Set ℝ := {y : ℝ |
    thetaCuspLogConcavityNumerator y ≤ -5 * thetaCuspSourceTerm y 1 ^ 2}
  have hclosed : IsClosed S := by
    exact isClosed_le continuous_thetaCuspLogConcavityNumerator
      (continuous_const.mul (continuous_thetaCuspSourceTerm_one.pow 2))
  have hsub : Ioi (0 : ℝ) ⊆ S := by
    intro y hy
    exact thetaCuspLogConcavityNumerator_le_firstAtom_sq hy
  have hclosure : closure (Ioi (0 : ℝ)) ⊆ S := closure_minimal hsub hclosed
  have hle : thetaCuspLogConcavityNumerator x ≤
      -5 * thetaCuspSourceTerm x 1 ^ 2 := by
    exact hclosure (by simpa only [closure_Ioi, mem_Ici] using hx)
  have hfirst := thetaCuspSourceTerm_one_pos_of_nonneg hx
  nlinarith [sq_pos_of_pos hfirst]

end

end RHTower

namespace RHTower

noncomputable section

/-! ## Global log-concavity and the exact Hedenmalm two-node consequence -/

private theorem thetaCuspSourceTerm_zero_nonneg (n : ℕ) :
    0 ≤ thetaCuspSourceTerm 0 n := by
  have hcontinuous : Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hlimit : Tendsto (fun k : ℕ =>
      thetaCuspSourceTerm (1 / ((k : ℝ) + 1)) n) atTop
      (𝓝 (thetaCuspSourceTerm 0 n)) :=
    hcontinuous.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto' hlimit fun k =>
    thetaCuspSourceTerm_nonneg_of_pos (by positivity) n

/-- The actual theta source is strictly positive on the whole logarithmic line, including the
reflection center. -/
theorem thetaCuspFullSource_pos_all (x : ℝ) :
    0 < thetaCuspFullSource x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [← thetaCuspFullSource_neg x]
    exact thetaCuspFullSource_pos_of_pos (neg_pos.mpr hx)
  · rw [thetaCuspFullSource]
    exact (summable_thetaCuspSourceTerm 0).tsum_pos
      thetaCuspSourceTerm_zero_nonneg 1
      (thetaCuspSourceTerm_one_pos_of_nonneg le_rfl)
  · exact thetaCuspFullSource_pos_of_pos hx

/-- Reflection upgrades the half-line estimate to a strict global log-concavity numerator law. -/
theorem thetaCuspLogConcavityNumerator_neg_all (x : ℝ) :
    thetaCuspLogConcavityNumerator x < 0 := by
  by_cases hx : 0 ≤ x
  · exact thetaCuspLogConcavityNumerator_neg hx
  · have hneg := thetaCuspLogConcavityNumerator_neg (x := -x) (by linarith)
    have hzero := thetaCuspFullSource_neg (-x)
    have hone := iteratedDeriv_thetaCuspFullSource_neg 1 (-x)
    have htwo := iteratedDeriv_thetaCuspFullSource_neg 2 (-x)
    norm_num at hzero hone htwo
    unfold thetaCuspLogConcavityNumerator at hneg ⊢
    simp only [iteratedDeriv_one] at hneg ⊢
    rw [hzero, hone, htwo]
    nlinarith

/-- Logarithm of the actual positive theta-cusp source. -/
def thetaCuspLogSource (x : ℝ) : ℝ :=
  Real.log (thetaCuspFullSource x)

theorem hasDerivAt_thetaCuspFullSource_iterate_zero (x : ℝ) :
    HasDerivAt thetaCuspFullSource
      (iteratedDeriv 1 thetaCuspFullSource x) x := by
  have h := hasDerivAt_thetaCuspFullDerivative 0 x
  rw [← iteratedDeriv_thetaCuspFullSource 0,
    ← iteratedDeriv_thetaCuspFullSource 1] at h
  simpa using h

private theorem hasDerivAt_thetaCuspFullSource_iterate_one (x : ℝ) :
    HasDerivAt (iteratedDeriv 1 thetaCuspFullSource)
      (iteratedDeriv 2 thetaCuspFullSource x) x := by
  have h := hasDerivAt_thetaCuspFullDerivative 1 x
  rw [← iteratedDeriv_thetaCuspFullSource 1,
    ← iteratedDeriv_thetaCuspFullSource 2] at h
  simpa using h

/-- First logarithmic derivative of the actual theta source. -/
theorem hasDerivAt_thetaCuspLogSource (x : ℝ) :
    HasDerivAt thetaCuspLogSource
      (iteratedDeriv 1 thetaCuspFullSource x / thetaCuspFullSource x) x := by
  exact (hasDerivAt_thetaCuspFullSource_iterate_zero x).log
    (thetaCuspFullSource_pos_all x).ne'

/-- The second derivative of the logarithm is exactly the normalized log-concavity numerator. -/
theorem iteratedDeriv_two_thetaCuspLogSource_eq (x : ℝ) :
    iteratedDeriv 2 thetaCuspLogSource x =
      thetaCuspLogConcavityNumerator x / thetaCuspFullSource x ^ 2 := by
  have hquot := (hasDerivAt_thetaCuspFullSource_iterate_one x).div
    (hasDerivAt_thetaCuspFullSource_iterate_zero x)
    (thetaCuspFullSource_pos_all x).ne'
  have hderiv : deriv thetaCuspLogSource =
      iteratedDeriv 1 thetaCuspFullSource / thetaCuspFullSource := by
    funext y
    simp only [Pi.div_apply]
    exact (hasDerivAt_thetaCuspLogSource y).deriv
  rw [show iteratedDeriv 2 thetaCuspLogSource x =
      deriv (deriv thetaCuspLogSource) x by simp [iteratedDeriv_succ], hderiv]
  unfold thetaCuspLogConcavityNumerator
  simpa only [pow_two] using hquot.deriv

/-- The logarithm of the actual theta source is strictly concave on the whole real line. -/
theorem strictConcaveOn_thetaCuspLogSource :
    StrictConcaveOn ℝ Set.univ thetaCuspLogSource := by
  apply strictConcaveOn_univ_of_deriv2_neg
  · exact contDiff_thetaCuspFullSource.continuous.log fun x =>
      (thetaCuspFullSource_pos_all x).ne'
  · intro x
    have hnum := thetaCuspLogConcavityNumerator_neg_all x
    have hden : 0 < thetaCuspFullSource x ^ 2 :=
      sq_pos_of_pos (thetaCuspFullSource_pos_all x)
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    rw [show deriv (deriv thetaCuspLogSource) x =
      iteratedDeriv 2 thetaCuspLogSource x by simp [iteratedDeriv_succ],
      iteratedDeriv_two_thetaCuspLogSource_eq]
    exact div_neg_of_neg_of_pos hnum hden

/-- Multiplicative midpoint law forced by global theta-kernel log-concavity. -/
theorem thetaCuspFullSource_mul_reflect_le_sq (u t : ℝ) :
    thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) ≤
      thetaCuspFullSource u ^ 2 := by
  have hconc := strictConcaveOn_thetaCuspLogSource.concaveOn
  have hlog :
      (1 / 2 : ℝ) * thetaCuspLogSource (u + t) +
          (1 / 2 : ℝ) * thetaCuspLogSource (u - t) ≤
        thetaCuspLogSource u := by
    have hj := hconc.2 (Set.mem_univ (u + t)) (Set.mem_univ (u - t))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simpa only [smul_eq_mul, show
      (1 / 2 : ℝ) * (u + t) + (1 / 2 : ℝ) * (u - t) = u by ring] using hj
  have hplus := thetaCuspFullSource_pos_all (u + t)
  have hminus := thetaCuspFullSource_pos_all (u - t)
  have hcenter := thetaCuspFullSource_pos_all u
  have hlogs :
      Real.log (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)) ≤
        Real.log (thetaCuspFullSource u ^ 2) := by
    rw [Real.log_mul hplus.ne' hminus.ne', Real.log_pow]
    dsimp [thetaCuspLogSource] at hlog
    norm_num at hlog ⊢
    nlinarith
  calc
    thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) =
        Real.exp (Real.log
          (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))) := by
      rw [Real.exp_log (mul_pos hplus hminus)]
    _ ≤ Real.exp (Real.log (thetaCuspFullSource u ^ 2)) :=
      Real.exp_le_exp.mpr hlogs
    _ = thetaCuspFullSource u ^ 2 := Real.exp_log (sq_pos_of_pos hcenter)

theorem integrableOn_thetaCuspCenterMixedIntegrand
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    IntegrableOn (fun r : ℝ =>
      r * Real.sinh (a * r) *
        (thetaCuspFullSource (r / 2 + t) * thetaCuspFullSource (r / 2 - t)))
      (Ioi 0) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let C := thetaCuspDerivativeExpConstant 0
  let c : ℝ := 1 / 2 - a
  let f : ℝ → ℝ := fun r =>
    r * Real.sinh (a * r) *
      (thetaCuspFullSource (r / 2 + t) * thetaCuspFullSource (r / 2 - t))
  let bound : ℝ → ℝ := fun r =>
    C ^ 2 * (r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ)))
  have hc : 0 < c := by dsimp [c]; linarith
  have hbound : Integrable bound mu := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := c) (by norm_num) (by norm_num) hc
    exact h.const_mul (C ^ 2)
  have hf : Integrable f mu := by
    apply hbound.mono
    · have hk : Continuous thetaCuspFullSource :=
        contDiff_thetaCuspFullSource.continuous
      dsimp [f]
      exact (by fun_prop (disch := aesop) : Continuous (fun r : ℝ =>
        r * Real.sinh (a * r) *
          (thetaCuspFullSource (r / 2 + t) * thetaCuspFullSource (r / 2 - t))))
        |>.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hrpos : 0 < r := hr
      have hk := norm_thetaWignerCenterMixKernel_le
        (a := a) (r := r) (t := t) (b := 0) hrpos ha0
      have hphase : thetaWignerDifferencePhase 0 t = 1 := by
        simp [thetaWignerDifferencePhase]
      have heq : ‖f r‖ =
          ‖thetaWignerCenterMixKernel thetaCuspComplexSource a 0 (r, t)‖ := by
        rw [thetaWignerCenterMixKernel, hphase]
        simp only [mul_one, f, thetaCuspComplexSource, Complex.conj_ofReal]
        norm_cast
      rw [heq]
      calc
        _ ≤ C ^ 2 * r * Real.exp (-(1 / 2 - a) * r) * Real.exp (-|t|) := hk
        _ ≤ C ^ 2 * r * Real.exp (-(1 / 2 - a) * r) := by
          exact mul_le_of_le_one_right
            (mul_nonneg (mul_nonneg (sq_nonneg C) hrpos.le) (Real.exp_pos _).le)
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg t)))
        _ = ‖bound r‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · simp [bound, C, c, Real.rpow_one, mul_assoc]
          · dsimp [bound]
            exact mul_nonneg (sq_nonneg C)
              (mul_nonneg (Real.rpow_nonneg hrpos.le _) (Real.exp_pos _).le)
  simpa [IntegrableOn, f, mu] using hf

/-- The center-mixed Hedenmalm density attains its maximum at the reflection center. -/
theorem thetaCuspCenterMixedDensity_le_zero
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    thetaCuspCenterMixedDensity a t ≤ thetaCuspCenterMixedDensity a 0 := by
  unfold thetaCuspCenterMixedDensity
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg
      (mul_nonneg hr.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0 hr.le)))
      (mul_nonneg (thetaCuspFullSource_pos_all _).le
        (thetaCuspFullSource_pos_all _).le)
  · exact integrableOn_thetaCuspCenterMixedIntegrand ha0 ha 0
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hweight : 0 ≤ r * Real.sinh (a * r) :=
      mul_nonneg hr.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0 hr.le))
    have hprod := thetaCuspFullSource_mul_reflect_le_sq (r / 2) t
    simpa [pow_two] using mul_le_mul_of_nonneg_left hprod hweight

/-- The real symmetric two-node Bochner matrix of the center-mixed density. -/
def thetaCuspCenterMixedTwoNodeMatrix (a t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then thetaCuspCenterMixedDensity a 0
    else thetaCuspCenterMixedDensity a t

private theorem twoNodeConstantMatrix_posSemidef {d o : ℝ}
    (ho0 : 0 ≤ o) (hod : o ≤ d) :
    Matrix.PosSemidef
      ((fun i j : Fin 2 => if i = j then d else o) : Matrix (Fin 2) (Fin 2) ℝ) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then d else o
  change Matrix.PosSemidef M
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [M]
  · intro c
    have hp : 0 ≤ (d + o) / 2 := by linarith
    have hm : 0 ≤ (d - o) / 2 := by linarith
    rw [show star c ⬝ᵥ M.mulVec c =
        ((d + o) / 2) * (c 0 + c 1) ^ 2 +
          ((d - o) / 2) * (c 0 - c 1) ^ 2 by
      simp [M, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring]
    positivity

/-- Every two-node Bochner matrix supplied by the theta log-concavity theorem is positive
semidefinite.  This is the exact order-two endpoint; it does not assert the all-node positive
definiteness equivalent to RH. -/
theorem thetaCuspCenterMixedTwoNodeMatrix_posSemidef
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    Matrix.PosSemidef (thetaCuspCenterMixedTwoNodeMatrix a t) := by
  exact twoNodeConstantMatrix_posSemidef
    (thetaCuspCenterMixedDensity_nonneg ha0)
    (thetaCuspCenterMixedDensity_le_zero ha0 ha t)

/-- Equivalent determinant form of the two-node wall. -/
theorem thetaCuspCenterMixedTwoNode_det_nonneg
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    0 ≤ thetaCuspCenterMixedDensity a 0 ^ 2 -
      thetaCuspCenterMixedDensity a t ^ 2 := by
  have hzero := thetaCuspCenterMixedDensity_nonneg (a := a) (t := 0) ha0
  have ht := thetaCuspCenterMixedDensity_nonneg (a := a) (t := t) ha0
  have hle := thetaCuspCenterMixedDensity_le_zero ha0 ha t
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hzero ht)]

end

end RHTower
