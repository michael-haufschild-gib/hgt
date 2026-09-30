import GaloisForLFunctions.HTGeometry.CpowHarmonicTailAsymptotic
import Mathlib.Analysis.Real.Sqrt
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-!
# Hilbert estimates for the natural Abel mesh

Square-summable source rows give interior holomorphy and zero scaled critical residue.
These generic estimates have no actual-source continuation dependency.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower.WoldNaturalAbelHilbert
noncomputable section

def atom (r : ℕ → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  (r n : ℂ) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
    (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s))

def current (r : ℕ → ℝ) (s : ℂ) : ℂ := ∑' n, atom r s n

lemma atom_norm_le (r : ℕ → ℝ) {s : ℂ} (hs : -1 ≤ s.re) (n : ℕ) :
    ‖atom r s n‖ ≤ ‖s‖ * (|r n| * ((n : ℝ) + 1) ^ (-s.re - 1)) := by
  by_cases hs0 : s = 0
  · subst s
    simp [atom]
  have h := GaloisForLFunctions.HTGeometry.norm_ofReal_cpow_sub_le
    (neg_ne_zero.mpr hs0) (show (-s).re ≤ 1 by simp; linarith)
    (show 0 < (n : ℝ) + 1 by positivity)
    (show (n : ℝ) + 2 ∈ Icc ((n : ℝ) + 1) ((n : ℝ) + 1 + 1) by
      constructor <;> linarith)
  rw [norm_sub_rev] at h
  simp only [norm_neg, neg_re] at h
  rw [atom, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |r n| * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

lemma sq_rpow_summable {q : ℝ} (hq : q < -1 / 2) :
    Summable (fun n : ℕ => (((n : ℝ) + 1) ^ q) ^ 2) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (q * 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift := (summable_nat_add_iff 1).mpr h
  refine hshift.congr fun n => ?_
  rw [Nat.cast_add, Nat.cast_one, ← Real.rpow_natCast,
    ← Real.rpow_mul (show 0 ≤ (n : ℝ) + 1 by positivity)]
  norm_num

lemma weighted_summable {r : ℕ → ℝ} (hr : Summable (fun n => (r n) ^ 2))
    {q : ℝ} (hq : q < -1 / 2) :
    Summable (fun n => |r n| * ((n : ℝ) + 1) ^ q) := by
  have habs : Summable (fun n => |r n| ^ 2) := by
    simpa only [sq_abs] using hr
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((habs.add (sq_rpow_summable hq)).div_const 2)
  nlinarith [sq_nonneg (|r n| - ((n : ℝ) + 1) ^ q)]

lemma atom_summable {r : ℕ → ℝ} (hr : Summable (fun n => (r n) ^ 2))
    {s : ℂ} (hs : -1 / 2 < s.re) : Summable (atom r s) := by
  exact Summable.of_norm_bounded
    ((weighted_summable hr (show -s.re - 1 < -1 / 2 by linarith)).mul_left ‖s‖)
    (atom_norm_le r (by linarith))

lemma pseries_bound {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 * x - 1)) ≤ 1 + 1 / (2 * x) := by
  have h := GaloisForLFunctions.HTGeometry.tsum_shift_rpow_le
    (q := -2 * x) (by linarith) (N := 1) le_rfl
  have hs := GaloisForLFunctions.HTGeometry.summable_shift_rpow
    (q := -2 * x) (by linarith) 0
  have hs' : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * x - 1)) := by
    simpa [add_comm] using hs
  rw [← hs'.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, Real.one_rpow]
  have heq : (∑' i : ℕ, (((i + 1 : ℕ) : ℝ) + 1) ^ (-2 * x - 1)) =
      ∑' i : ℕ, ((1 : ℝ) + 1 + (i : ℝ)) ^ (-2 * x - 1) := by
    apply tsum_congr
    intro i
    congr 1
    push_cast
    ring
  rw [heq]
  simp only [Nat.cast_one, Real.one_rpow, neg_mul, neg_neg] at h
  have h' : (∑' i : ℕ, ((1 : ℝ) + 1 + (i : ℝ)) ^ (-2 * x - 1)) ≤ 1 / (2*x) := by
    simpa only [neg_mul] using h
  simpa only [add_comm] using add_le_add_left h' 1

lemma tsum_mul_le {a b : ℕ → ℝ} (ha : Summable (fun n => (a n)^2))
    (hb : Summable (fun n => (b n)^2)) (ha0 : ∀ n, 0 ≤ a n)
    (hb0 : ∀ n, 0 ≤ b n) :
    (∑' n, a n * b n) ≤ Real.sqrt (∑' n, (a n)^2) *
      Real.sqrt (∑' n, (b n)^2) := by
  have hab : Summable (fun n => a n * b n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 n) (hb0 n))
      (fun n => by nlinarith [sq_nonneg (a n - b n)]) ((ha.add hb).div_const 2)
  apply le_of_tendsto hab.hasSum.tendsto_sum_nat
  filter_upwards [] with N
  calc
    _ ≤ Real.sqrt (∑ n ∈ Finset.range N, (a n)^2) *
        Real.sqrt (∑ n ∈ Finset.range N, (b n)^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ a b
    _ ≤ _ := mul_le_mul
      (Real.sqrt_le_sqrt (ha.sum_le_tsum _ (fun n _ => sq_nonneg _)))
      (Real.sqrt_le_sqrt (hb.sum_le_tsum _ (fun n _ => sq_nonneg _)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma current_norm_le {r : ℕ → ℝ} (hr : Summable (fun n => (r n)^2))
    {s : ℂ} (hs : -1/2 < s.re) :
    ‖current r s‖ ≤ ‖s‖ * (Real.sqrt (∑' n, (r n)^2) *
      Real.sqrt (∑' n : ℕ, ((n : ℝ)+1)^(-2*s.re-2))) := by
  have hw := weighted_summable hr (show -s.re-1 < -1/2 by linarith)
  have hg := sq_rpow_summable (show -s.re-1 < -1/2 by linarith)
  have habs : Summable (fun n => |r n|^2) := by simpa using hr
  have hcs := tsum_mul_le habs hg (fun n => abs_nonneg _) (fun n => by positivity)
  have heq : (fun n : ℕ => (((n:ℝ)+1)^(-s.re-1))^2) =
      fun n : ℕ => ((n:ℝ)+1)^(-2*s.re-2) := by
    funext n
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (n:ℝ)+1 by positivity)]
    congr 1
    norm_num
    ring
  rw [heq] at hcs
  simp only [sq_abs] at hcs
  calc
    _ ≤ ∑' n, ‖atom r s n‖ := norm_tsum_le_tsum_norm (atom_summable hr hs).norm
    _ ≤ ∑' n, ‖s‖ * (|r n| * ((n:ℝ)+1)^(-s.re-1)) :=
      Summable.tsum_le_tsum (atom_norm_le r (by linarith))
        (atom_summable hr hs).norm (hw.mul_left ‖s‖)
    _ = ‖s‖ * ∑' n, |r n| * ((n:ℝ)+1)^(-s.re-1) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hcs (norm_nonneg _)

lemma current_radial_zero {r : ℕ → ℝ} (hr : Summable (fun n => (r n)^2))
    {s0 : ℂ} (hs0 : s0.re = -1/2) :
    Tendsto (fun x : ℝ => (x:ℂ) * current r (s0 + (x:ℂ))) (𝓝[>] 0) (𝓝 0) := by
  let Q : ℝ := ∑' n, (r n)^2
  have hQ : 0 ≤ Q := tsum_nonneg (fun n => sq_nonneg _)
  have hbound : ∀ x : ℝ, 0 < x →
      ‖(x:ℂ)*current r (s0+(x:ℂ))‖ ≤
        Real.sqrt (‖s0+(x:ℂ)‖^2 * Q * (x^2+x/2)) := by
    intro x hx
    have hs : -1/2 < (s0+(x:ℂ)).re := by simp [hs0]; linarith
    have h := current_norm_le hr hs
    have heq : -2*(s0+(x:ℂ)).re-2 = -2*x-1 := by simp [hs0]; ring
    rw [heq] at h
    have hH : 0 ≤ ∑' n : ℕ, ((n:ℝ)+1)^(-2*x-1) := tsum_nonneg (fun n => by positivity)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hH, ← mul_assoc] at hsq
    have hsq' : ‖current r (s0+(x:ℂ))‖^2 ≤
        ‖s0+(x:ℂ)‖^2 * Q * (1+1/(2*x)) :=
      hsq.trans (mul_le_mul_of_nonneg_left (pseries_bound hx) (mul_nonneg (sq_nonneg _) hQ))
    apply Real.le_sqrt_of_sq_le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, mul_pow]
    calc
      _ ≤ x^2 * (‖s0+(x:ℂ)‖^2 * Q * (1+1/(2*x))) :=
        mul_le_mul_of_nonneg_left hsq' (sq_nonneg _)
      _ = _ := by field_simp
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _))
    (eventually_mem_nhdsWithin.mono (fun x hx => hbound x hx))
  have hc : Continuous (fun x : ℝ =>
      Real.sqrt (‖s0+(x:ℂ)‖^2 * Q * (x^2+x/2))) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

lemma current_differentiableAt {r : ℕ → ℝ} (hr : Summable (fun n => (r n)^2))
    {s : ℂ} (hs : -1/2 < s.re) : DifferentiableAt ℂ (current r) s := by
  let radius : ℝ := (s.re + 1/2)/2
  let q : ℝ := -s.re + radius - 1
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hq : q < -1/2 := by dsimp [q, radius]; linarith
  have hsum := (weighted_summable hr hq).mul_left (‖s‖+radius)
  apply GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated
    (f := fun n z => atom r z n) hradius _ _ hsum
  · intro n z hz
    have h1 : (((n:ℝ)+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have h2 : (((n:ℝ)+2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    exact (((DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl h1)).sub
      (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl h2))).const_mul
        (r n : ℂ)).differentiableWithinAt
  · intro n z hz
    have hdist : ‖z-s‖ < radius := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hre := Complex.re_le_norm (s-z)
    simp only [sub_re, norm_sub_rev s z] at hre
    have hzre : -1 ≤ z.re := by dsimp [radius] at hdist; linarith
    have hexp : -z.re-1 ≤ q := by dsimp [q]; linarith
    have hn : ‖z‖ ≤ ‖s‖+radius := by
      calc
        ‖z‖ = ‖(z-s)+s‖ := by rw [sub_add_cancel]
        _ ≤ ‖z-s‖+‖s‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ ≤ ‖z‖*(|r n| *((n:ℝ)+1)^(-z.re-1)) := atom_norm_le r hzre n
      _ ≤ (‖s‖+radius)*(|r n| *((n:ℝ)+1)^q) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le
            (show 1 ≤ (n:ℝ)+1 by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]) hexp) (abs_nonneg _))
          (by positivity) (by positivity)

end
end RHTower.WoldNaturalAbelHilbert

