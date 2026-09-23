import Mathlib
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModeExpectation

/-!
# Theta--Hasse--KMS execution balance

This module certifies the scalar and symmetric-pair core of ULF-RFDM-2.  The Hasse recovery
parameter is strictly source-reconstructing.  Its geometric packet is normalized, its collision
loss is exactly the KMS linear entropy, and its Shannon loss is exactly the KMS von Neumann
entropy.  Any strictly increasing statistic of the recovered source has a unique reflected
balance point in every nondegenerate even two-point source fibre.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry.AbelianZetaParameters

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hasse recovery ratio attached to logarithmic source scale `x`. -/
def thetaHasseRatio (x : ℝ) : ℝ := (1 - Real.exp (-Real.exp x)) / 2

/-- Geometric packet collision loss, equivalently KMS linear entropy. -/
def geometricExecutionTV (q : ℝ) : ℝ := 2 * q / (1 + q)

/-- Geometric packet Shannon loss, equivalently KMS von Neumann entropy. -/
def geometricExecutionEntropy (q : ℝ) : ℝ :=
  -Real.log (1 - q) - q / (1 - q) * Real.log q

/-- Mass of depth `n` in the geometric Hasse/KMS packet. -/
def geometricLayerMass (q : ℝ) (n : ℕ) : ℝ := (1 - q) * q ^ n

/-- Shannon contribution of depth `n`. -/
def geometricLayerShannonTerm (q : ℝ) (n : ℕ) : ℝ :=
  -geometricLayerMass q n * Real.log (geometricLayerMass q n)

/-- The geometric Hasse/KMS packet has total mass one. -/
theorem tsum_geometricLayerMass_eq_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ, geometricLayerMass q n = 1 := by
  have h1 : 1 - q ≠ 0 := by linarith
  rw [show (fun n : ℕ => geometricLayerMass q n) = fun n => (1 - q) * q ^ n by rfl,
    tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  field_simp

/-- One adjacent-depth ratio reconstructs the geometric recovery parameter. -/
theorem geometricLayerMass_succ_div (n : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    geometricLayerMass q (n + 1) / geometricLayerMass q n = q := by
  have hqne : q ≠ 0 := hq0.ne'
  have h1ne : 1 - q ≠ 0 := by linarith
  unfold geometricLayerMass
  rw [pow_succ]
  field_simp

/-- Purity of the geometric KMS packet. -/
theorem tsum_sq_geometricLayerMass {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ, geometricLayerMass q n ^ (2 : ℕ) = (1 - q) / (1 + q) := by
  have hq2 : q ^ (2 : ℕ) < 1 := by nlinarith
  calc
    ∑' n : ℕ, geometricLayerMass q n ^ (2 : ℕ) =
        ∑' n : ℕ, (1 - q) ^ (2 : ℕ) * (q ^ (2 : ℕ)) ^ n := by
          apply tsum_congr
          intro n
          simp only [geometricLayerMass]
          ring
    _ = (1 - q) ^ (2 : ℕ) * (1 - q ^ (2 : ℕ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg q) hq2]
    _ = (1 - q) / (1 + q) := by
      have h1 : 1 - q ≠ 0 := by linarith
      have hp : 1 + q ≠ 0 := by linarith
      have h2 : 1 - q ^ (2 : ℕ) ≠ 0 := by nlinarith
      rw [inv_eq_one_div]
      field_simp [h2]
      ring

/-- Reset-path collision loss equals KMS linear entropy exactly. -/
theorem geometricExecutionTV_eq_one_sub_purity {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    geometricExecutionTV q = 1 - ∑' n : ℕ, geometricLayerMass q n ^ (2 : ℕ) := by
  rw [tsum_sq_geometricLayerMass hq0 hq1]
  unfold geometricExecutionTV
  have hp : 1 + q ≠ 0 := by linarith
  field_simp
  ring

/-- Shannon entropy of the geometric packet equals the closed KMS entropy formula. -/
theorem tsum_geometricLayerShannonTerm {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∑' n : ℕ, geometricLayerShannonTerm q n = geometricExecutionEntropy q := by
  have hq0' : 0 ≤ q := hq0.le
  have hqne : q ≠ 0 := hq0.ne'
  have h1pos : 0 < 1 - q := sub_pos.mpr hq1
  have h1ne : 1 - q ≠ 0 := h1pos.ne'
  have hmass : Summable (geometricLayerMass q) := by
    exact ((summable_geometric_of_lt_one hq0' hq1).mul_left (1 - q)).congr
      (fun n => by rfl)
  have hnat : Summable (fun n : ℕ => (n : ℝ) * geometricLayerMass q n) := by
    exact (summable_natCast_mul_geometric hq0' hq1).congr (fun n => by
      simp only [geometricLayerMass]
      ring)
  have hterm : ∀ n : ℕ, geometricLayerShannonTerm q n =
      (-Real.log (1 - q)) * geometricLayerMass q n +
        (-Real.log q) * ((n : ℝ) * geometricLayerMass q n) := by
    intro n
    unfold geometricLayerShannonTerm geometricLayerMass
    rw [Real.log_mul h1ne (pow_ne_zero n hqne), Real.log_pow]
    ring
  rw [tsum_congr hterm,
    Summable.tsum_add (hmass.mul_left (-Real.log (1 - q)))
      (hnat.mul_left (-Real.log q)),
    tsum_mul_left, tsum_mul_left,
    tsum_geometricLayerMass_eq_one hq0' hq1]
  have hmean : (∑' n : ℕ, (n : ℝ) * geometricLayerMass q n) = q / (1 - q) := by
    calc
      (∑' n : ℕ, (n : ℝ) * geometricLayerMass q n) =
          ∑' n : ℕ, (n : ℝ) * q ^ n * (1 - q) := by
            apply tsum_congr
            intro n
            simp only [geometricLayerMass]
            ring
      _ = q / (1 - q) := tsum_natCast_mul_geometric hq0' hq1
  rw [hmean]
  unfold geometricExecutionEntropy
  ring

theorem thetaHasseRatio_pos (x : ℝ) : 0 < thetaHasseRatio x := by
  have hneg : -Real.exp x < 0 := neg_lt_zero.mpr (Real.exp_pos x)
  have he : Real.exp (-Real.exp x) < 1 := (Real.exp_lt_one_iff).2 hneg
  dsimp [thetaHasseRatio]
  linarith

theorem thetaHasseRatio_lt_half (x : ℝ) : thetaHasseRatio x < 1 / 2 := by
  have he := Real.exp_pos (-Real.exp x)
  dsimp [thetaHasseRatio]
  linarith

/-- Hasse formation is source-reconstructing: its recovery ratio is strictly increasing. -/
theorem strictMono_thetaHasseRatio : StrictMono thetaHasseRatio := by
  intro x y hxy
  have h1 : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr hxy
  have h2 : -Real.exp y < -Real.exp x := neg_lt_neg h1
  have h3 : Real.exp (-Real.exp y) < Real.exp (-Real.exp x) := Real.exp_lt_exp.mpr h2
  dsimp [thetaHasseRatio]
  linarith

theorem strictMonoOn_geometricExecutionTV :
    StrictMonoOn geometricExecutionTV (Set.Ioi (-1)) := by
  intro x hx y hy hxy
  change -1 < x at hx
  change -1 < y at hy
  have hxden : 0 < 1 + x := by linarith [hx]
  have hyden : 0 < 1 + y := by linarith [hy]
  dsimp [geometricExecutionTV]
  rw [div_lt_div_iff₀ hxden hyden]
  nlinarith

theorem hasDerivAt_geometricExecutionEntropy {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    HasDerivAt geometricExecutionEntropy (-Real.log q / (1 - q) ^ (2 : ℕ)) q := by
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hA : HasDerivAt (fun x : ℝ => -Real.log (1 - x)) (1 / (1 - q)) q := by
    have h := (((hasDerivAt_const q 1).sub (hasDerivAt_id q)).log hden).neg
    change HasDerivAt (fun x : ℝ => -Real.log (1 - x)) (-((0 - 1) / (1 - q))) q at h
    convert h using 1
    ring
  have hB : HasDerivAt (fun x : ℝ => x / (1 - x)) (1 / (1 - q) ^ (2 : ℕ)) q := by
    have h := (hasDerivAt_id q).div
      ((hasDerivAt_const q 1).sub (hasDerivAt_id q)) hden
    change HasDerivAt (fun x : ℝ => x / (1 - x))
      ((1 * (1 - q) - q * (0 - 1)) / (1 - q) ^ (2 : ℕ)) q at h
    convert h using 1
    ring
  have hC : HasDerivAt (fun x : ℝ => Real.log x) (1 / q) q := by
    simpa using (hasDerivAt_id q).log hq0
  have h := hA.sub (hB.mul hC)
  change HasDerivAt geometricExecutionEntropy
    (1 / (1 - q) - (1 / (1 - q) ^ (2 : ℕ) * Real.log q + q / (1 - q) * (1 / q))) q at h
  convert h using 1
  · field_simp
    ring

theorem strictMonoOn_geometricExecutionEntropy :
    StrictMonoOn geometricExecutionEntropy (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · exact continuousOn_of_forall_continuousAt fun q hq =>
      (hasDerivAt_geometricExecutionEntropy hq.1.ne' hq.2.ne).continuousAt
  intro q hq
  rw [interior_Ioo] at hq
  rw [(hasDerivAt_geometricExecutionEntropy hq.1.ne' hq.2.ne).deriv]
  have hlog : Real.log q < 0 := Real.log_neg hq.1 hq.2
  exact div_pos (neg_pos.mpr hlog)
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hq.2.ne.symm))

/-- KMS linear entropy strictly increases with source scale. -/
theorem strictMono_thetaHasseExecutionTV :
    StrictMono (fun x => geometricExecutionTV (thetaHasseRatio x)) := by
  intro x y hxy
  exact strictMonoOn_geometricExecutionTV
    (by change -1 < thetaHasseRatio x; linarith [thetaHasseRatio_pos x])
    (by change -1 < thetaHasseRatio y; linarith [thetaHasseRatio_pos y])
    (strictMono_thetaHasseRatio hxy)

/-- KMS von Neumann entropy strictly increases with source scale. -/
theorem strictMono_thetaHasseExecutionEntropy :
    StrictMono (fun x => geometricExecutionEntropy (thetaHasseRatio x)) := by
  intro x y hxy
  apply strictMonoOn_geometricExecutionEntropy
  · exact ⟨thetaHasseRatio_pos x, lt_trans (thetaHasseRatio_lt_half x) (by norm_num)⟩
  · exact ⟨thetaHasseRatio_pos y, lt_trans (thetaHasseRatio_lt_half y) (by norm_num)⟩
  · exact strictMono_thetaHasseRatio hxy

/-- Mean of `g` in a nondegenerate even two-point source tilted by `a`. -/
def symmetricSourceTiltMean (g : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (Real.exp (a * x) * g x + Real.exp (-a * x) * g (-x)) /
    (Real.exp (a * x) + Real.exp (-a * x))

/-- Positive tilt has strictly positive reflected response for every increasing statistic. -/
theorem symmetricSourceTiltMean_reflection_gap_pos {g : ℝ → ℝ} {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hg : g (-x) < g x) :
    0 < symmetricSourceTiltMean g a x - symmetricSourceTiltMean g (-a) x := by
  have hA : 0 < Real.exp (a * x) := Real.exp_pos _
  have hB : 0 < Real.exp (-a * x) := Real.exp_pos _
  have hBA : Real.exp (-a * x) < Real.exp (a * x) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hden : 0 < Real.exp (a * x) + Real.exp (-a * x) := add_pos hA hB
  have heq :
      symmetricSourceTiltMean g a x - symmetricSourceTiltMean g (-a) x =
        ((Real.exp (a * x) - Real.exp (-a * x)) * (g x - g (-x))) /
          (Real.exp (a * x) + Real.exp (-a * x)) := by
    unfold symmetricSourceTiltMean
    simp only [neg_mul, neg_neg]
    field_simp
    ring
  rw [heq]
  positivity

/-- Reflected execution balance selects the central source tilt and only that tilt. -/
theorem symmetricSourceTiltMean_reflection_gap_eq_zero_iff {g : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hg : g (-x) < g x) (a : ℝ) :
    symmetricSourceTiltMean g a x - symmetricSourceTiltMean g (-a) x = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    rcases lt_or_gt_of_ne ha with ha | ha
    · have hp := symmetricSourceTiltMean_reflection_gap_pos (g := g) (a := -a) (x := x)
          (neg_pos.mpr ha) hx hg
      rw [neg_neg] at hp
      linarith
    · exact (ne_of_gt (symmetricSourceTiltMean_reflection_gap_pos ha hx hg)) h
  · rintro rfl
    simp

/-- Linear-entropy balance of a two-point even theta fibre selects the centre. -/
theorem thetaHasseExecutionTV_balance_eq_zero_iff {x : ℝ} (hx : 0 < x) (a : ℝ) :
    symmetricSourceTiltMean (fun y => geometricExecutionTV (thetaHasseRatio y)) a x -
      symmetricSourceTiltMean (fun y => geometricExecutionTV (thetaHasseRatio y)) (-a) x = 0 ↔
        a = 0 :=
  symmetricSourceTiltMean_reflection_gap_eq_zero_iff hx
    (strictMono_thetaHasseExecutionTV (neg_lt_self hx)) a

/-- Entropy balance of a two-point even theta fibre selects the centre. -/
theorem thetaHasseExecutionEntropy_balance_eq_zero_iff {x : ℝ} (hx : 0 < x) (a : ℝ) :
    symmetricSourceTiltMean (fun y => geometricExecutionEntropy (thetaHasseRatio y)) a x -
      symmetricSourceTiltMean (fun y => geometricExecutionEntropy (thetaHasseRatio y)) (-a) x = 0 ↔
        a = 0 :=
  symmetricSourceTiltMean_reflection_gap_eq_zero_iff hx
    (strictMono_thetaHasseExecutionEntropy (neg_lt_self hx)) a

/-- Mean in a finite weighted source fibre. -/
def finiteWeightedMean {ι : Type*} [Fintype ι] (w f : ι → ℝ) : ℝ :=
  ∑ i, w i * f i

/-- Variance in a finite weighted source fibre. -/
def finiteWeightedVariance {ι : Type*} [Fintype ι] (w f : ι → ℝ) : ℝ :=
  ∑ i, w i * (f i - finiteWeightedMean w f) ^ (2 : ℕ)

/-- Covariance in a finite weighted source fibre. -/
def finiteWeightedCovariance {ι : Type*} [Fintype ι] (w f g : ι → ℝ) : ℝ :=
  ∑ i, w i * (f i - finiteWeightedMean w f) * (g i - finiteWeightedMean w g)

/-- Finite Fisher-response law: every execution response is bounded by source variance times
statistic variance.  No probability normalization is needed for this weighted Cauchy--Schwarz
form; nonnegative weights are sufficient. -/
theorem finiteWeightedCovariance_sq_le_variance_mul_variance
    {ι : Type*} [Fintype ι] {w f g : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    finiteWeightedCovariance w f g ^ (2 : ℕ) ≤
      finiteWeightedVariance w f * finiteWeightedVariance w g := by
  unfold finiteWeightedCovariance finiteWeightedVariance
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro i hi
    exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i hi
    ring_nf
    exact le_rfl

end

end GaloisForLFunctions.HTGeometry
