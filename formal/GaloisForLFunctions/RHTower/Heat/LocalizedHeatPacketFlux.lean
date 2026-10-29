import GaloisForLFunctions.RHTower.Heat.LocalizedHeatPairForce
import Mathlib.Analysis.Complex.Basic

/-!
# The localized flux of a finite conjugate packet

Summing the gap-independent pair estimate retains a fixed negative contribution
from each nonreal conjugate pair. The reciprocal-field identity identifies this
sum with the work of the zero velocities. A real-symmetric exterior field costs
only squared heights, so real zeros are never charged as off-line energy.
-/

open Finset Complex

noncomputable section
namespace GaloisForLFunctions.HTGeometry


private theorem heat_pair_separation {a b : ℂ} (hab : a ≠ b) :
    0 < (a.re - b.re)^2 + (a.im - b.im)^2 := by
  have h := Complex.normSq_pos.mpr (sub_ne_zero.mpr hab)
  simpa only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, sq] using h

private theorem heat_pair_force_with_conjugate {w v : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|) (hwn : ∀ x, 0 ≤ w x)
    (a b : ℂ) :
    localizedHeatPairForce w v a.re b.re a.im b.im ≤
      -(if a.im ≠ 0 ∧ b = starRingEnd ℂ a then 4 * w a.re else 0) +
        2 * M * (a.im^2 + b.im^2) := by
  by_cases hc : a.im ≠ 0 ∧ b = starRingEnd ℂ a
  · rcases hc with ⟨ha, rfl⟩
    simp only [ha, ne_eq, not_false_eq_true, and_self, if_true, Complex.conj_re,
      Complex.conj_im]
    rw [localizedHeatPairForce_conjugate w v a.re ha]
    have hnon : 0 ≤ 2 * M * (a.im^2 + (-a.im)^2) := by positivity
    linarith only [hnon]
  rw [if_neg hc, neg_zero, zero_add]
  by_cases hab : a = b
  · subst b
    simp only [localizedHeatPairForce, sub_self, mul_zero, zero_div]
    positivity
  have hs := heat_pair_separation hab
  have hf := localizedHeatPairForce_le hM hw hv a.re b.re a.im b.im hs
  have hn : -2 * (w a.re + w b.re) * (a.im - b.im)^2 /
      ((a.re - b.re)^2 + (a.im - b.im)^2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hs.le
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (add_nonneg (hwn _) (hwn _))
  linarith only [hf, hn]

/-- Squared heights of a finite zero packet. -/
def heatPacketVerticalEnergy (S : Finset ℂ) : ℝ := ∑ a ∈ S, a.im^2

/-- The localized count of nonreal members of a simple packet. -/
def heatPacketNonrealWeight (S : Finset ℂ) (w : ℝ → ℝ) : ℝ :=
  ∑ a ∈ S, if a.im = 0 then 0 else w a.re

/-- Sum of the pair contributions, counting each unordered pair once. -/
def heatPacketPairDrift (S : Finset ℂ) (w v : ℝ → ℝ) : ℝ :=
  (∑ a ∈ S, ∑ b ∈ S, localizedHeatPairForce w v a.re b.re a.im b.im) / 2

/-- Conjugate pairs pay the nonreal count; cutoff error costs only squared heights. -/
theorem heatPacketPairDrift_le {S : Finset ℂ} {w v : ℝ → ℝ} {M : ℝ}
    (hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S)
    (hM : 0 ≤ M) (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|) (hwn : ∀ x, 0 ≤ w x) :
    heatPacketPairDrift S w v ≤ -2 * heatPacketNonrealWeight S w +
      2 * M * S.card * heatPacketVerticalEnergy S := by
  classical
  have hsum := sum_le_sum fun a (_ : a ∈ S) =>
    sum_le_sum fun b (_ : b ∈ S) => heat_pair_force_with_conjugate hM hw hv hwn a b
  have hpen : (∑ a ∈ S, ∑ b ∈ S,
      if a.im ≠ 0 ∧ b = starRingEnd ℂ a then 4 * w a.re else 0) =
      4 * heatPacketNonrealWeight S w := by
    rw [heatPacketNonrealWeight, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    by_cases hy : a.im = 0
    · simp only [hy, ne_eq, not_true_eq_false, false_and, if_false, if_true, sum_const_zero, mul_zero]
    · simp [hy, hconj a ha]
  have herr : (∑ a ∈ S, ∑ b ∈ S, 2 * M * (a.im^2 + b.im^2)) =
      4 * M * S.card * heatPacketVerticalEnergy S := by
    calc
      _ = 2 * M * (∑ a ∈ S, ∑ b ∈ S, (a.im^2 + b.im^2)) := by
        simp only [mul_sum]
      _ = 2 * M * ((S.card : ℝ) * heatPacketVerticalEnergy S +
          (S.card : ℝ) * heatPacketVerticalEnergy S) := by
        congr 1
        simp only [heatPacketVerticalEnergy, sum_add_distrib, sum_const, nsmul_eq_mul,
          ← mul_sum]
      _ = _ := by ring
  simp only [sum_add_distrib, sum_neg_distrib] at hsum
  rw [hpen, herr] at hsum
  unfold heatPacketPairDrift
  linarith only [hsum]

/-- Exterior-field contribution to the derivative of the squared-height energy. -/
def heatPacketExteriorDrift (S : Finset ℂ) (w v : ℝ → ℝ) (Q : ℂ → ℂ) : ℝ :=
  ∑ a ∈ S, (v a.re * a.im^2 * (2 * (Q a).re) + 2 * w a.re * a.im * (2 * (Q a).im))

/-- A real-symmetric exterior field charges only squared heights. -/
theorem heatPacketExteriorDrift_le {S : Finset ℂ} {w v : ℝ → ℝ} {Q : ℂ → ℂ}
    {K V W : ℝ} (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hw : ∀ a ∈ S, 0 ≤ w a.re ∧ w a.re ≤ W)
    (hv : ∀ a ∈ S, |v a.re| ≤ V)
    (hQr : ∀ a ∈ S, |(Q a).re| ≤ K)
    (hQi : ∀ a ∈ S, |(Q a).im| ≤ K * |a.im|) :
    heatPacketExteriorDrift S w v Q ≤ (2 * V + 4 * W) * K * heatPacketVerticalEnergy S := by
  unfold heatPacketExteriorDrift heatPacketVerticalEnergy
  rw [mul_sum]
  refine sum_le_sum fun a ha => ?_
  have hvr : v a.re * (Q a).re ≤ V * K := by
    calc
      _ ≤ |v a.re * (Q a).re| := le_abs_self _
      _ = |v a.re| * |(Q a).re| := abs_mul _ _
      _ ≤ V * K := mul_le_mul (hv a ha) (hQr a ha) (abs_nonneg _) hV
  have hyi : a.im * (Q a).im ≤ K * a.im^2 := by
    calc
      _ ≤ |a.im * (Q a).im| := le_abs_self _
      _ = |a.im| * |(Q a).im| := abs_mul _ _
      _ ≤ |a.im| * (K * |a.im|) := mul_le_mul_of_nonneg_left (hQi a ha) (abs_nonneg _)
      _ = K * a.im^2 := by rw [← mul_assoc, mul_comm |a.im| K, mul_assoc, ← sq, sq_abs]
  have h1 := mul_le_mul_of_nonneg_left hvr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg a.im))
  have h2 := mul_le_mul_of_nonneg_left hyi (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hw a ha).1)
  have h3 := mul_le_mul_of_nonneg_right (hw a ha).2 (mul_nonneg hK (sq_nonneg a.im))
  nlinarith only [h1, h2, h3]

/-- The complete finite-packet bound retains conjugate dissipation and the exact cutoff costs. -/
theorem heatPacket_drift_le {S : Finset ℂ} {w v : ℝ → ℝ} {Q : ℂ → ℂ}
    {M K V W : ℝ} (hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|)
    (hwn : ∀ x, 0 ≤ w x) (hwW : ∀ a ∈ S, w a.re ≤ W)
    (hvV : ∀ a ∈ S, |v a.re| ≤ V)
    (hQr : ∀ a ∈ S, |(Q a).re| ≤ K)
    (hQi : ∀ a ∈ S, |(Q a).im| ≤ K * |a.im|) :
    heatPacketPairDrift S w v + heatPacketExteriorDrift S w v Q ≤
      -2 * heatPacketNonrealWeight S w +
        (2 * M * S.card + (2 * V + 4 * W) * K) * heatPacketVerticalEnergy S := by
  have hp := heatPacketPairDrift_le hconj hM hw hv hwn
  have he := heatPacketExteriorDrift_le hK hV
    (fun a ha => ⟨hwn a.re, hwW a ha⟩) hvV hQr hQi
  nlinarith only [hp, he]

private theorem heat_pair_force_eq_field_pair (w v : ℝ → ℝ) (a b : ℂ) :
    (v a.re * a.im^2 * (2 * (a - b)⁻¹.re) +
      2 * w a.re * a.im * (2 * (a - b)⁻¹.im)) +
    (v b.re * b.im^2 * (2 * (b - a)⁻¹.re) +
      2 * w b.re * b.im * (2 * (b - a)⁻¹.im)) =
      localizedHeatPairForce w v a.re b.re a.im b.im := by
  have hn : Complex.normSq (b - a) = Complex.normSq (a - b) := by
    rw [← Complex.normSq_neg, neg_sub]
  simp only [Complex.inv_re, Complex.inv_im, Complex.sub_re, Complex.sub_im, hn,
    localizedHeatPairForce]
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- The pair drift is exactly the work of the finite reciprocal field. -/
theorem heatPacketPairDrift_eq_field (S : Finset ℂ) (w v : ℝ → ℝ) :
    heatPacketPairDrift S w v =
      ∑ a ∈ S, (v a.re * a.im^2 * (2 * (∑ b ∈ S, (a - b)⁻¹).re) +
        2 * w a.re * a.im * (2 * (∑ b ∈ S, (a - b)⁻¹).im)) := by
  let F := fun a b : ℂ => v a.re * a.im^2 * (2 * (a - b)⁻¹.re) +
    2 * w a.re * a.im * (2 * (a - b)⁻¹.im)
  have he : (∑ a ∈ S, ∑ b ∈ S, (F a b + F b a)) =
      2 * (∑ a ∈ S, ∑ b ∈ S, F a b) := by
    simp only [sum_add_distrib]
    rw [sum_comm (f := fun a b => F b a)]
    ring
  have hp : (∑ a ∈ S, ∑ b ∈ S, localizedHeatPairForce w v a.re b.re a.im b.im) =
      2 * (∑ a ∈ S, ∑ b ∈ S, F a b) := by
    rw [← he]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
      (heat_pair_force_eq_field_pair w v a b).symm
  unfold heatPacketPairDrift
  rw [hp, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  refine sum_congr rfl fun a _ => ?_
  simp only [F, Complex.re_sum, Complex.im_sum, mul_sum, sum_add_distrib]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.heatPacket_drift_le
#print axioms GaloisForLFunctions.HTGeometry.heatPacketPairDrift_eq_field
