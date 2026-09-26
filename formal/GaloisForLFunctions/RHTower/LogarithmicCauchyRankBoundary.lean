import GaloisForLFunctions.HTGeometry.AlternatingHarmonicPair
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The joint rank boundary of the logarithmic Cauchy model

The formal kernel `(L + atanh z + atanh w)/(1-z*w)` has diagonal coefficient L
and reciprocal odd off-diagonals. Its 2m-coordinate form is positive for
`L >= 2 h_m`, but the alternating vector is negative for `L < 2 h_m - 1`,
where `h_m` is the m-th odd harmonic sum. The exact logarithmic corner and
necessary cost of a repair are proved below. Every fixed rank eventually becomes
positive; no fixed diagonal level, even with a uniformly bounded repair, works
in every rank.

The Cayley identity connects the model to a logarithm-weighted Cauchy kernel.
No theorem here identifies this model with the literal theta kernel or proves
an actual-theta asymptotic. In particular these obstructions do not refute RH.
-/

open Filter Finset PowerSeries
open scoped BigOperators Topology
noncomputable section
namespace RHTower.LogCauchyRank


def oddCoefficient (n : ℕ) : ℝ := if Odd n then 1/(n : ℝ) else 0
def entry (L : ℝ) (i j : ℕ) : ℝ :=
  if i=j then L else oddCoefficient ((i-j)+(j-i))
def oddSeries : PowerSeries ℝ := PowerSeries.mk oddCoefficient
def series (L : ℝ) : PowerSeries (PowerSeries ℝ) :=
  PowerSeries.mk (fun i => PowerSeries.mk (entry L i))

@[simp] theorem entry_diagonal (L : ℝ) (i : ℕ) : entry L i i = L := by simp [entry]
@[simp] theorem entry_succ_succ (L : ℝ) (i j : ℕ) :
    entry L (i+1) (j+1) = entry L i j := by simp [entry]
@[simp] theorem entry_zero_succ (L : ℝ) (j : ℕ) :
    entry L 0 (j+1) = oddCoefficient (j+1) := by simp [entry]
@[simp] theorem entry_succ_zero (L : ℝ) (i : ℕ) :
    entry L (i+1) 0 = oddCoefficient (i+1) := by simp [entry]
@[simp] theorem oddCoefficient_zero : oddCoefficient 0 = 0 := by simp [oddCoefficient]
@[simp] theorem series_coefficient (L : ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (series L)) = entry L i j := by
  simp [series]

/-- Every odd off-diagonal coefficient is retained with its exact weight. -/
theorem entry_odd_shift (L : ℝ) (i j : ℕ) :
    entry L i (i+(2*j+1)) = 1/(2*(j : ℝ)+1) := by
  have hne : i ≠ i+(2*j+1) := by omega
  have hleft : i-(i+(2*j+1)) = 0 := by omega
  have hright : i+(2*j+1)-i = 2*j+1 := by omega
  have ho : Odd (2*j+1) := ⟨j, by omega⟩
  simp only [entry, if_neg hne, hleft, hright, zero_add, oddCoefficient, if_pos ho]
  norm_num

/-- Nonzero even off-diagonals vanish. -/
theorem entry_even_shift (L : ℝ) (i j : ℕ) (hj : 0 < j) :
    entry L i (i+2*j) = 0 := by
  have hne : i ≠ i+2*j := by omega
  have hleft : i-(i+2*j) = 0 := by omega
  have hright : i+2*j-i = 2*j := by omega
  have ho : ¬ Odd (2*j) := by rintro ⟨k, hk⟩; omega
  simp only [entry, if_neg hne, hleft, hright, zero_add, oddCoefficient, if_neg ho]

theorem entry_comm (L : ℝ) (i j : ℕ) : entry L i j = entry L j i := by
  simp [entry, eq_comm, Nat.add_comm]

/-- Exact two-variable formal-series equation of the logarithmic Cauchy model. -/
theorem series_equation (L : ℝ) :
    (1 - PowerSeries.C PowerSeries.X * PowerSeries.X) * series L =
      PowerSeries.C (PowerSeries.C L) + PowerSeries.C oddSeries +
        PowerSeries.mk (fun i => PowerSeries.C (oddCoefficient i)) := by
  rw [sub_mul, one_mul, mul_assoc]
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  cases i with
  | zero =>
    cases j with
    | zero => simp [oddSeries, series, entry]
    | succ j => simp [oddSeries, series, entry]
  | succ i =>
    cases j with
    | zero => simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, oddSeries, series, entry]
    | succ j => simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, oddSeries, series, entry]

/-- Analytic real expression whose odd Taylor coefficients are encoded above. -/
def logOdd (z : ℝ) : ℝ := (Real.log (1+z) - Real.log (1-z))/2
def cayley (u z : ℝ) : ℝ := u*(1+z)/(1-z)
def logarithmicKernel (R u v : ℝ) : ℝ :=
  (2*R+(Real.log u+Real.log v)/2)/(u+v)

theorem log_cayley {u z : ℝ} (hu : 0 < u) (hz0 : -1 < z) (hz1 : z < 1) :
    Real.log (cayley u z) = Real.log u + 2*logOdd z := by
  have ha : 0 < 1+z := by linarith
  have hb : 0 < 1-z := by linarith
  unfold cayley logOdd
  rw [Real.log_div (mul_pos hu ha).ne' hb.ne', Real.log_mul hu.ne' ha.ne']
  ring

/-- Exact Cayley congruence; no theta asymptotic is assumed or asserted. -/
theorem cayley_kernel_identity (R : ℝ) {u z w : ℝ} (hu : 0 < u)
    (hz0 : -1 < z) (hz1 : z < 1) (hw0 : -1 < w) (hw1 : w < 1) :
    logarithmicKernel R (cayley u z) (cayley u w) =
      (1-z)*(1-w)/(2*u) *
        ((2*R+Real.log u+logOdd z+logOdd w)/(1-z*w)) := by
  have hz : 1-z ≠ 0 := by linarith
  have hw : 1-w ≠ 0 := by linarith
  have hzw : 1-z*w ≠ 0 := by
    have ha : 0 < (1-z)*(1+w) := mul_pos (by linarith) (by linarith)
    have hb : 0 < (1-w)*(1+z) := mul_pos (by linarith) (by linarith)
    nlinarith
  unfold logarithmicKernel
  rw [log_cayley hu hz0 hz1, log_cayley hu hw0 hw1]
  unfold cayley
  have hd : u*(1+z)/(1-z)+u*(1+w)/(1-w) ≠ 0 := by
    apply ne_of_gt
    exact add_pos (div_pos (mul_pos hu (by linarith)) (by linarith))
      (div_pos (mul_pos hu (by linarith)) (by linarith))
  have htwo : 2-z*w*2 ≠ 0 := by nlinarith
  field_simp [hu.ne', hz, hw, hzw]
  ring_nf
  field_simp [htwo]
  ring


def oddHarmonic (m : ℕ) : ℝ := ∑ j ∈ range m, 1 / (2 * (j : ℝ) + 1)
def energy (n : ℕ) (a : ℕ → ℝ) : ℝ := ∑ i ∈ range n, a i ^ 2
def correlation (n k : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n-k), a i * a (i+k)
def form (L : ℝ) (m : ℕ) (a : ℕ → ℝ) : ℝ :=
  L * energy (2*m) a +
    2 * ∑ j ∈ range m, correlation (2*m) (2*j+1) a / (2*(j : ℝ)+1)
def Positive (L : ℝ) (m : ℕ) : Prop := ∀ a : ℕ → ℝ, 0 ≤ form L m a

/-- Grouping the nonzero formal coefficients by their odd lag gives `form`. -/
theorem form_eq_coefficient_lags (L : ℝ) (m : ℕ) (a : ℕ → ℝ) :
    form L m a =
      (∑ i ∈ range (2*m), a i^2 * PowerSeries.coeff i (PowerSeries.coeff i (series L))) +
      2*∑ j ∈ range m, ∑ i ∈ range (2*m-(2*j+1)),
        a i*a (i+(2*j+1)) *
          PowerSeries.coeff (i+(2*j+1)) (PowerSeries.coeff i (series L)) := by
  simp only [series_coefficient, entry_diagonal, entry_odd_shift]
  unfold form energy correlation
  rw [← sum_mul, mul_comm L]
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [sum_div]
  apply sum_congr rfl
  intro i hi
  ring

theorem energy_nonneg (n : ℕ) (a : ℕ → ℝ) : 0 ≤ energy n a :=
  sum_nonneg (fun i _ => sq_nonneg (a i))

theorem oddHarmonic_nonneg (m : ℕ) : 0 ≤ oddHarmonic m := by
  apply sum_nonneg
  intro i hi
  positivity

private theorem energy_initial_le (n k : ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ range (n-k), a i ^ 2) ≤ energy n a := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le n k))
    (fun i _ _ => sq_nonneg (a i))

private theorem energy_shift_le {n k : ℕ} (hk : k ≤ n) (a : ℕ → ℝ) :
    (∑ i ∈ range (n-k), a (i+k) ^ 2) ≤ energy n a := by
  have h := sum_range_add (fun i => a i ^ 2) k (n-k)
  rw [Nat.add_sub_of_le hk] at h
  have h0 : 0 ≤ ∑ i ∈ range k, a i ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
  simpa only [energy, Nat.add_comm] using (show
    (∑ i ∈ range (n-k), a (k+i)^2) ≤ ∑ i ∈ range n, a i^2 by linarith)

theorem abs_correlation_le {n k : ℕ} (hk : k ≤ n) (a : ℕ → ℝ) :
    |correlation n k a| ≤ energy n a := by
  have hb : 2 * (∑ i ∈ range (n-k), |a i * a (i+k)|) ≤
      (∑ i ∈ range (n-k), a i^2) + ∑ i ∈ range (n-k), a (i+k)^2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    rw [abs_mul]
    nlinarith [sq_nonneg (|a i|-|a (i+k)|), sq_abs (a i), sq_abs (a (i+k))]
  have hs := abs_sum_le_sum_abs (fun i => a i * a (i+k)) (range (n-k))
  have hp := energy_initial_le n k a
  have ht := energy_shift_le hk a
  dsimp [correlation]
  linarith

theorem abs_form_sub_diagonal_le (L : ℝ) (m : ℕ) (a : ℕ → ℝ) :
    |form L m a - L * energy (2*m) a| ≤
      2 * oddHarmonic m * energy (2*m) a := by
  have hb : (∑ j ∈ range m, |correlation (2*m) (2*j+1) a / (2*(j : ℝ)+1)|) ≤
      oddHarmonic m * energy (2*m) a := by
    unfold oddHarmonic
    rw [sum_mul]
    apply sum_le_sum
    intro j hj
    have hjm : j < m := mem_range.mp hj
    have hd : 0 < 2*(j : ℝ)+1 := by positivity
    rw [abs_div, abs_of_pos hd]
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      div_le_div_of_nonneg_right (abs_correlation_le (by omega : 2*j+1 ≤ 2*m) a) hd.le
  have hs := abs_sum_le_sum_abs
    (fun j => correlation (2*m) (2*j+1) a / (2*(j : ℝ)+1)) (range m)
  unfold form
  rw [add_sub_cancel_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem positive_of_two_oddHarmonic_le {L : ℝ} (m : ℕ)
    (hL : 2 * oddHarmonic m ≤ L) : Positive L m := by
  intro a
  have hb := (abs_le.mp (abs_form_sub_diagonal_le L m a)).1
  have he := energy_nonneg (2*m) a
  nlinarith

theorem alternating_energy (n : ℕ) : energy n (fun i => (-1 : ℝ)^i) = n := by
  unfold energy
  have hp (i : ℕ) : ((-1 : ℝ)^i)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm i 2, pow_mul]
    norm_num
  simp [hp]

private theorem alternating_pair (i j : ℕ) :
    (-1 : ℝ)^i * (-1 : ℝ)^(i+(2*j+1)) = -1 := by
  rw [← pow_add]
  have he : i + (i + (2*j+1)) = 2*(i+j)+1 := by omega
  rw [he, pow_add, pow_mul]
  norm_num

theorem alternating_correlation (n j : ℕ) :
    correlation n (2*j+1) (fun i => (-1 : ℝ)^i) = -(n-(2*j+1) : ℕ) := by
  unfold correlation
  simp only [alternating_pair, sum_const, card_range, nsmul_eq_mul, mul_neg, mul_one]

theorem alternating_form (L : ℝ) (m : ℕ) :
    form L m (fun i => (-1 : ℝ)^i) = 2*(m : ℝ)*(L+1-2*oddHarmonic m) := by
  unfold form
  rw [alternating_energy]
  have hs : (∑ j ∈ range m,
      correlation (2*m) (2*j+1) (fun i => (-1 : ℝ)^i) / (2*(j : ℝ)+1)) =
      (m : ℝ) - 2*(m : ℝ)*oddHarmonic m := by
    trans ∑ j ∈ range m, (1 - 2*(m : ℝ)/(2*(j : ℝ)+1))
    · apply sum_congr rfl
      intro j hj
      have hjm := mem_range.mp hj
      rw [alternating_correlation, Nat.cast_sub (by omega : 2*j+1 ≤ 2*m)]
      push_cast
      field_simp
      ring
    · rw [sum_sub_distrib]
      simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
      unfold oddHarmonic
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro j hj
      ring
  rw [hs]
  push_cast
  ring

theorem alternating_negative_iff {m : ℕ} (hm : 0 < m) (L : ℝ) :
    form L m (fun i => (-1 : ℝ)^i) < 0 ↔ L < 2*oddHarmonic m-1 := by
  rw [alternating_form]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor <;> intro h <;> nlinarith

theorem necessary_threshold {L : ℝ} {m : ℕ} (hm : 0 < m) (h : Positive L m) :
    2*oddHarmonic m-1 ≤ L := by
  have hp := h (fun i => (-1 : ℝ)^i)
  rw [alternating_form] at hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  nlinarith

theorem oddHarmonic_tendsto_atTop : Tendsto oddHarmonic atTop atTop := by
  have hb := Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop
    (by norm_num : (0 : ℝ) < 1/2)
  apply Filter.tendsto_atTop_mono (fun m => ?_) hb
  unfold oddHarmonic
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : 0 < (j : ℝ)+1 := by positivity
  have h2 : 0 < 2*(j : ℝ)+1 := by positivity
  apply (le_div_iff₀ h2).mpr
  apply (mul_le_iff_le_one_right h1).mp
  field_simp
  nlinarith

theorem exists_negative_rank (L : ℝ) :
    ∃ m : ℕ, 0 < m ∧ form L m (fun i => (-1 : ℝ)^i) < 0 := by
  obtain ⟨m, hm, hH⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (oddHarmonic_tendsto_atTop.eventually_gt_atTop ((L+1)/2))).exists
  exact ⟨m, hm, (alternating_negative_iff hm L).2 (by linarith)⟩

theorem no_uniform_positive_level : ¬ ∃ L : ℝ, ∀ m : ℕ, Positive L m := by
  rintro ⟨L, hL⟩
  obtain ⟨m, _, hm⟩ := exists_negative_rank L
  exact (not_lt_of_ge (hL m _)) hm

/-- At every fixed rank a finite diagonal level suffices. -/
theorem fixed_rank_eventually_positive (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, Positive L m := by
  filter_upwards [eventually_ge_atTop (2*oddHarmonic m)] with L hL
  exact positive_of_two_oddHarmonic_le m hL

/-- Exact joint rank/diagonal boundary witnessed by alternating coefficients. -/
theorem joint_boundary_value (c : ℝ) (m : ℕ) :
    form (2*oddHarmonic m+c) m (fun i => (-1 : ℝ)^i) = 2*(m : ℝ)*(c+1) := by
  rw [alternating_form]
  ring

/-- Any repair making the model positive must pay the full harmonic deficit. -/
theorem repair_cost {L : ℝ} {m : ℕ} (r : (ℕ → ℝ) → ℝ)
    (h : ∀ a, 0 ≤ form L m a + r a) :
    2*(m : ℝ)*(2*oddHarmonic m-1-L) ≤ r (fun i => (-1 : ℝ)^i) := by
  have hb := h (fun i => (-1 : ℝ)^i)
  rw [alternating_form] at hb
  linarith

/-- Uniformly energy-bounded corrections cannot repair every rank. -/
theorem no_bounded_repair (L C : ℝ) :
    ¬ ∃ r : ℕ → (ℕ → ℝ) → ℝ,
      (∀ m a, r m a ≤ C * energy (2*m) a) ∧
      (∀ m a, 0 ≤ form L m a + r m a) := by
  rintro ⟨r, hbound, hpos⟩
  obtain ⟨m, hm, hneg⟩ := exists_negative_rank (L+C)
  have hc := repair_cost (r m) (hpos m)
  have hb := hbound m (fun i => (-1 : ℝ)^i)
  rw [alternating_energy] at hb
  rw [alternating_form] at hneg
  push_cast at hb
  nlinarith

/-- Parity reverses precisely the off-diagonal part. -/
theorem parity_reflection (L : ℝ) (m : ℕ) (a : ℕ → ℝ) :
    form L m (fun i => (-1 : ℝ)^i * a i) =
      2*L*energy (2*m) a - form L m a := by
  have he : energy (2*m) (fun i => (-1 : ℝ)^i*a i) = energy (2*m) a := by
    apply sum_congr rfl
    intro i hi
    rcases neg_one_pow_eq_or ℝ i with h | h <;> simp [h]
  have hc (j : ℕ) : correlation (2*m) (2*j+1) (fun i => (-1 : ℝ)^i*a i) =
      -correlation (2*m) (2*j+1) a := by
    unfold correlation
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    calc
      _ = ((-1 : ℝ)^i * (-1 : ℝ)^(i+(2*j+1))) * (a i*a (i+(2*j+1))) := by ring
      _ = _ := by rw [alternating_pair]; ring
  unfold form
  rw [he]
  simp only [hc, neg_div, sum_neg_distrib]
  ring

/-- The most adverse sign choice is alternating, with the original absolute amplitudes. -/
theorem alternating_absolute_minimizes (L : ℝ) (m : ℕ) (a : ℕ → ℝ) :
    form L m (fun i => (-1 : ℝ)^i * |a i|) ≤ form L m a := by
  have he : energy (2*m) (fun i => |a i|) = energy (2*m) a := by
    unfold energy
    simp only [sq_abs]
  have hc (j : ℕ) : -correlation (2*m) (2*j+1) (fun i => |a i|) ≤
      correlation (2*m) (2*j+1) a := by
    unfold correlation
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro i hi
    rw [← abs_mul]
    exact neg_abs_le _
  rw [parity_reflection]
  unfold form
  rw [he]
  have hsum : -(∑ j ∈ range m,
      correlation (2*m) (2*j+1) (fun i => |a i|) / (2*(j : ℝ)+1)) ≤
      ∑ j ∈ range m, correlation (2*m) (2*j+1) a / (2*(j : ℝ)+1) := by
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro j hj
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (hc j) (by positivity)
  linarith

/-- Positivity is completely decided by alternating-sign tests with nonnegative amplitudes. -/
theorem positive_iff_alternating_nonnegative (L : ℝ) (m : ℕ) :
    Positive L m ↔ ∀ b : ℕ → ℝ, (∀ i, 0 ≤ b i) →
      0 ≤ form L m (fun i => (-1 : ℝ)^i*b i) := by
  constructor
  · intro h b hb
    exact h _
  · intro h a
    exact (h (fun i => |a i|) (fun i => abs_nonneg _)).trans
      (alternating_absolute_minimizes L m a)

/-- The odd harmonic scale in ordinary harmonic coordinates. -/
theorem oddHarmonic_eq (m : ℕ) :
    oddHarmonic m = (harmonic (2*m) : ℝ) - (harmonic m : ℝ)/2 := by
  induction m with
  | zero => simp [oddHarmonic, harmonic_zero]
  | succ m ih =>
    unfold oddHarmonic at ih ⊢
    rw [sum_range_succ, ih]
    have h2 : 2*(m+1) = (2*m+1)+1 := by omega
    rw [h2, harmonic_succ, harmonic_succ, harmonic_succ]
    push_cast
    have h1 : 2*(m : ℝ)+1 ≠ 0 := by positivity
    have h2 : 2*(m : ℝ)+2 ≠ 0 := by positivity
    have h3 : (m : ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring

/-- Exact logarithmic rank scale, including its constant term. -/
theorem harmonic_threshold_asymptotic :
    Tendsto (fun m : ℕ => 2*oddHarmonic m - Real.log m) atTop
      (𝓝 (2*Real.log 2 + Real.eulerMascheroniConstant)) := by
  have h := (GaloisForLFunctions.HTGeometry.tendsto_harmonic_two_mul_sub_harmonic.const_mul 2).add
    Real.tendsto_harmonic_sub_log
  apply h.congr
  intro m
  rw [oddHarmonic_eq]
  ring

/-- The witness has an exact signed limit in the growing-rank logarithmic corner. -/
theorem logarithmic_corner_limit (c : ℝ) :
    Tendsto (fun m : ℕ => form (Real.log m+c) m (fun i => (-1 : ℝ)^i) / (2*(m : ℝ)))
      atTop (𝓝 (c+1-2*Real.log 2-Real.eulerMascheroniConstant)) := by
  have h := harmonic_threshold_asymptotic.const_sub (c+1)
  have h' : Tendsto (fun m : ℕ => c+1-(2*oddHarmonic m-Real.log m)) atTop
      (𝓝 (c+1-2*Real.log 2-Real.eulerMascheroniConstant)) := by
    have heq : c+1-(2*Real.log 2+Real.eulerMascheroniConstant) =
        c+1-2*Real.log 2-Real.eulerMascheroniConstant := by ring
    rw [heq] at h
    exact h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  rw [alternating_form]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring


end RHTower.LogCauchyRank
