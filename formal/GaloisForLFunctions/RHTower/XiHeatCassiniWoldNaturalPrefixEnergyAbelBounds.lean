import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelHilbert
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Sharp prefix energy bounds for the natural Abel current

A logarithmic prefix-energy upper bound is dominated by the harmonic prefix.  Finite Abel
summation preserves this order and yields `D(x) <= c(1+1/x)+C`.  Equal exponent splitting
bounds the scaled critical current square with limiting constant `c |s0|^2`.
-/

open Complex Filter Set Topology
open scoped BigOperators
namespace RHTower.WoldNaturalAbelPrefixEnergy
noncomputable section
open WoldNaturalAbelHilbert

def prefixEnergy (r : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, (r n)^2

def discount (r : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (r n)^2*((n:ℝ)+1)^(-x)

lemma power_increment_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 ≤ ((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x) := by
  exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (by positivity)
    (by linarith) (by linarith))

lemma power_increment_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x) ≤ x*((n:ℝ)+1)^(-x-1) := by
  have h := atom_norm_le (fun _ => (1:ℝ))
    (s := (x:ℂ)) (by simp; linarith) n
  simp only [atom, Complex.ofReal_one, one_mul] at h
  rw [show -(x:ℂ)=((-x:ℝ):ℂ) by simp,
    ← Complex.ofReal_cpow (show 0 ≤ (n:ℝ)+1 by positivity),
    ← Complex.ofReal_cpow (show 0 ≤ (n:ℝ)+2 by positivity),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (power_increment_nonneg hx n)] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
    Complex.ofReal_re, abs_one, one_mul] using h

lemma finite_abel (r : ℕ → ℝ) (x : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, discount r x n) =
      (N:ℝ)^(-x)*prefixEnergy r N +
        ∑ n ∈ Finset.range (N-1), prefixEnergy r (n+1)*
          (((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [discount, prefixEnergy]
  have h := Finset.sum_range_by_parts (f := fun n : ℕ => ((n:ℝ)+1)^(-x))
    (g := fun n : ℕ => (r n)^2) N
  simp only [smul_eq_mul] at h
  have hc : ((N-1:ℕ):ℝ)+1=(N:ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ N by omega)]
    push_cast
    ring
  rw [hc] at h
  have hs : (∑ n ∈ Finset.range (N-1),
      ((((n+1:ℕ):ℝ)+1)^(-x)-((n:ℝ)+1)^(-x))*prefixEnergy r (n+1)) =
      -(∑ n ∈ Finset.range (N-1), prefixEnergy r (n+1)*
        (((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show ((n+1:ℕ):ℝ)+1=(n:ℝ)+2 by push_cast; ring]
    ring
  change (∑ n ∈ Finset.range N, ((n:ℝ)+1)^(-x)*(r n)^2) = _ at h
  change (∑ n ∈ Finset.range N, (r n)^2*((n:ℝ)+1)^(-x)) = _
  change (∑ n ∈ Finset.range N, ((n:ℝ)+1)^(-x)*(r n)^2) =
    (N:ℝ)^(-x)*prefixEnergy r N - (∑ n ∈ Finset.range (N-1),
      ((((n+1:ℕ):ℝ)+1)^(-x)-((n:ℝ)+1)^(-x))*prefixEnergy r (n+1)) at h
  rw [hs] at h
  simpa only [mul_comm, sub_neg_eq_add] using h

lemma power_series_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^(-x-1)) := by
  have h : Summable (fun n : ℕ => (n:ℝ)^(-x-1)) := Real.summable_nat_rpow.mpr (by linarith)
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h

lemma power_series_bound {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, ((n:ℝ)+1)^(-x-1)) ≤ 1+1/x := by
  have h := pseries_bound (show 0 < x/2 by linarith)
  have heq : (fun n : ℕ => ((n:ℝ)+1)^(-2*(x/2)-1)) =
      fun n : ℕ => ((n:ℝ)+1)^(-x-1) := by funext n; congr 1; ring
  rw [heq] at h
  convert h using 1; congr 1; ring

lemma power_increment_sum (x : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x))) =
      1-((N:ℝ)+1)^(-x) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring_nf

lemma discount_sum_le {r : ℕ → ℝ} {c C x : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hx : 0 < x) (hbound : ∀ N : ℕ, 0 < N → prefixEnergy r N ≤ c*Real.log (N:ℝ)+C)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, discount r x n) ≤ c*(1+1/x)+C := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  let q : ℕ → ℝ := fun n => Real.sqrt (((n:ℝ)+1)⁻¹)
  have hq (n : ℕ) : (q n)^2 = ((n:ℝ)+1)⁻¹ := Real.sq_sqrt (by positivity)
  have hqE (K : ℕ) : prefixEnergy q K = (harmonic K : ℝ) := by
    simp only [prefixEnergy, hq, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    simp only [Nat.cast_add, Nat.cast_one]
  have hBound (K : ℕ) (hK : 0 < K) : prefixEnergy r K ≤ c*prefixEnergy q K+C := by
    have hlog := log_le_harmonic_floor (K:ℝ) (Nat.cast_nonneg K)
    have hlog' : Real.log (K:ℝ) ≤ prefixEnergy q K := by simpa only [Nat.floor_natCast, hqE] using hlog
    exact (hbound K hK).trans (add_le_add (mul_le_mul_of_nonneg_left hlog' hc) le_rfl)
  have hCast : ((N-1:ℕ):ℝ)+1 = (N:ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ N by omega)]
    push_cast
    ring
  have hTel : (N:ℝ)^(-x)+(∑ n ∈ Finset.range (N-1),
      (((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x)))=1 := by
    rw [power_increment_sum, hCast]
    ring
  have hCompare : (∑ n ∈ Finset.range N, discount r x n) ≤
      c*(∑ n ∈ Finset.range N, discount q x n)+C := by
    rw [finite_abel r, finite_abel q]
    calc
      _ ≤ (N:ℝ)^(-x)*(c*prefixEnergy q N+C)+
          ∑ n ∈ Finset.range (N-1), (c*prefixEnergy q (n+1)+C)*
            (((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hBound N hN) (by positivity)
        · apply Finset.sum_le_sum
          intro n hn
          exact mul_le_mul_of_nonneg_right (hBound (n+1) (by omega)) (power_increment_nonneg hx n)
      _ = c*((N:ℝ)^(-x)*prefixEnergy q N+
          ∑ n ∈ Finset.range (N-1), prefixEnergy q (n+1)*
            (((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x)))+
          C*((N:ℝ)^(-x)+∑ n ∈ Finset.range (N-1),
            (((n:ℝ)+1)^(-x)-((n:ℝ)+2)^(-x))) := by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc,
          ← Finset.mul_sum]
        ring
      _ = _ := by rw [hTel, mul_one]
  have hqDiscount (n : ℕ) : discount q x n = ((n:ℝ)+1)^(-x-1) := by
    dsimp only [discount]
    rw [hq, ← Real.rpow_neg_one, ← Real.rpow_add (show 0 < (n:ℝ)+1 by positivity)]
    congr 1
    ring
  calc
    _ ≤ c*(∑ n ∈ Finset.range N, discount q x n)+C := hCompare
    _ = c*(∑ n ∈ Finset.range N, ((n:ℝ)+1)^(-x-1))+C := by simp_rw [hqDiscount]
    _ ≤ c*(∑' n : ℕ, ((n:ℝ)+1)^(-x-1))+C := add_le_add
      (mul_le_mul_of_nonneg_left ((power_series_summable hx).sum_le_tsum _ (fun n _ => by positivity)) hc) le_rfl
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (power_series_bound hx) hc) le_rfl

lemma discount_bound {r : ℕ → ℝ} {c C x : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hx : 0 < x) (hbound : ∀ N : ℕ, 0 < N → prefixEnergy r N ≤ c*Real.log (N:ℝ)+C) :
    (∑' n, discount r x n) ≤ c*(1+1/x)+C :=
  Real.tsum_le_of_sum_range_le (fun n => by dsimp [discount]; positivity)
    (discount_sum_le hc hC hx hbound)


lemma discount_summable {r : ℕ → ℝ} {c C x : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hx : 0 < x) (hbound : ∀ N : ℕ, 0 < N → prefixEnergy r N ≤ c*Real.log (N:ℝ)+C) :
    Summable (discount r x) :=
  summable_of_sum_range_le (fun n => by dsimp [discount]; positivity)
    (discount_sum_le hc hC hx hbound)

lemma rpow_square_half (e : ℝ) (n : ℕ) :
    (((n:ℝ)+1)^(-e/2))^2 = ((n:ℝ)+1)^(-e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (n:ℝ)+1 by positivity)]
  congr 1
  norm_num

lemma prefix_weighted_summable {r : ℕ → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 0 < N → prefixEnergy r N ≤ c*Real.log (N:ℝ)+C)
    {q : ℝ} (hq : q < -1/2) : Summable (fun n => |r n| *((n:ℝ)+1)^q) := by
  let e : ℝ := -q-1/2
  have he : 0 < e := by dsimp [e]; linarith
  let a : ℕ → ℝ := fun n => r n*((n:ℝ)+1)^(-e/2)
  have ha : Summable (fun n => (a n)^2) := by
    have h := discount_summable hc hC he hbound
    refine h.congr fun n => ?_
    dsimp [a, discount]
    rw [mul_pow, rpow_square_half]
  have hq' : q+e/2 < -1/2 := by dsimp [e]; linarith
  have h := weighted_summable ha hq'
  refine h.congr fun n => ?_
  dsimp [a]
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ (n:ℝ)+1 by positivity) _),
    mul_assoc, ← Real.rpow_add (show 0 < (n:ℝ)+1 by positivity)]
  congr 2
  ring

lemma prefix_atom_summable {r : ℕ → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 0 < N → prefixEnergy r N ≤ c*Real.log (N:ℝ)+C)
    {s : ℂ} (hs : -1/2 < s.re) : Summable (atom r s) := by
  exact Summable.of_norm_bounded
    ((prefix_weighted_summable hc hC hbound (show -s.re-1 < -1/2 by linarith)).mul_left ‖s‖)
    (atom_norm_le r (by linarith))

lemma prefix_current_differentiableAt {r : ℕ → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 0 < N → prefixEnergy r N ≤ c*Real.log (N:ℝ)+C)
    {s : ℂ} (hs : -1/2 < s.re) : DifferentiableAt ℂ (current r) s := by
  let radius : ℝ := (s.re + 1/2)/2
  let q : ℝ := -s.re + radius - 1
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hq : q < -1/2 := by dsimp [q, radius]; linarith
  have hsum := (prefix_weighted_summable hc hC hbound hq).mul_left (‖s‖+radius)
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

lemma scaled_current_sq_le {r : ℕ → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 0 < N → prefixEnergy r N ≤ c*Real.log (N:ℝ)+C)
    {s0 : ℂ} (hs0 : s0.re = -1/2) {x : ℝ} (hx : 0 < x) :
    ‖(x:ℂ)*current r (s0+(x:ℂ))‖^2 ≤
      ‖s0+(x:ℂ)‖^2*(c+(c+C)*x)*(1+x) := by
  let a : ℕ → ℝ := fun n => |r n| *((n:ℝ)+1)^(-x/2)
  let b : ℕ → ℝ := fun n => ((n:ℝ)+1)^(-1/2-x/2)
  let w : ℕ → ℝ := fun n => |r n| *((n:ℝ)+1)^(-1/2-x)
  let D : ℝ := ∑' n, discount r x n
  let P : ℝ := ∑' n : ℕ, ((n:ℝ)+1)^(-x-1)
  have haEq : (fun n => (a n)^2) = discount r x := by
    funext n
    dsimp [a, discount]
    rw [mul_pow, sq_abs, rpow_square_half]
  have hbEq : (fun n => (b n)^2) = fun n : ℕ => ((n:ℝ)+1)^(-x-1) := by
    funext n
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (n:ℝ)+1 by positivity)]
    congr 1
    norm_num
    ring
  have habEq : (fun n => a n*b n) = w := by
    funext n
    dsimp [a, b, w]
    rw [mul_assoc, ← Real.rpow_add (show 0 < (n:ℝ)+1 by positivity)]
    congr 2
    ring
  have ha : Summable (fun n => (a n)^2) := by rw [haEq]; exact discount_summable hc hC hx hbound
  have hb : Summable (fun n => (b n)^2) := by rw [hbEq]; exact power_series_summable hx
  have hcs := tsum_mul_le ha hb (fun n => by dsimp [a]; positivity) (fun n => by dsimp [b]; positivity)
  rw [haEq, hbEq, habEq] at hcs
  have hD0 : 0 ≤ D := tsum_nonneg (fun n => by dsimp [discount]; positivity)
  have hP0 : 0 ≤ P := tsum_nonneg (fun n => by positivity)
  have hs : -1/2 < (s0+(x:ℂ)).re := by simp [hs0]; linarith
  have hexp : -(s0+(x:ℂ)).re-1 = -1/2-x := by simp [hs0]; ring
  have hsum := prefix_atom_summable hc hC hbound hs
  have hw : Summable w := prefix_weighted_summable hc hC hbound (by linarith)
  have hNorm : ‖current r (s0+(x:ℂ))‖ ≤ ‖s0+(x:ℂ)‖*(Real.sqrt D*Real.sqrt P) := by
    calc
      _ ≤ ∑' n, ‖atom r (s0+(x:ℂ)) n‖ := norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' n, ‖s0+(x:ℂ)‖*w n := hsum.norm.tsum_le_tsum (fun n => by
        simpa only [hexp, w] using atom_norm_le r (s := s0+(x:ℂ)) (by linarith) n) (hw.mul_left _)
      _ = ‖s0+(x:ℂ)‖*(∑' n, w n) := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hD0, Real.sq_sqrt hP0] at hsq
  have hDP : D*P ≤ (c*(1+1/x)+C)*(1+1/x) :=
    mul_le_mul (discount_bound hc hC hx hbound) (power_series_bound hx) hP0 (by positivity)
  have hsq' : ‖current r (s0+(x:ℂ))‖^2 ≤
      ‖s0+(x:ℂ)‖^2*((c*(1+1/x)+C)*(1+1/x)) :=
    hsq.trans (mul_le_mul_of_nonneg_left hDP (sq_nonneg _))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, mul_pow]
  calc
    _ ≤ x^2*(‖s0+(x:ℂ)‖^2*((c*(1+1/x)+C)*(1+1/x))) :=
      mul_le_mul_of_nonneg_left hsq' (sq_nonneg _)
    _ = _ := by field_simp [ne_of_gt hx]; ring

end
end RHTower.WoldNaturalAbelPrefixEnergy
