import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivative
import GaloisForLFunctions.RHTower.LiClockPairedEtaArithmeticCancellation
import GaloisForLFunctions.RHTower.LiClockSineImaginaryEnvelope
import GaloisForLFunctions.HTGeometry.OddEvenFactorialSeriesCalculus

/-!
# Complete Gamma–dyadic moment contraction and massive cancellation

Let `c_j = Re CompletionMoment(j) = Σ_n x_n^{j+1} + d_j` with `x_n = (2n+5/2)^{-2} ≤ α = 4/25`
and the real dyadic moment `|d_j| ≤ 3β^{j+1}`, `β = 1/64`.  Then:

* `c_0 > 1657/8000`, hence the massive rate satisfies `ω² = c_0 - m_0 > 6429/40000`;
* the strict contraction `α c_j - c_{j+1} > (3/409600) β^j` for every `j`, so `c_j < c_0 α^j`
  (`j ≥ 1`), `c_j/α^{j+1} → 1` and `c_{j+1}/c_j → α`: the ceiling `4/25` is sharp;
* for the full completion clock `C(t) = Σ c_j t^{2j+1}/(2j+1)!`:
  `α C - C'' ≥ (3/51200) sinh(t/8)`, `C'' < α C` and `C < (5/2) c_0 sinh(2t/5)` on `t > 0`;
* the massive envelope `V = ω² C - C''` satisfies
  `V ≥ (ω² - α) C + (3/51200) sinh(t/8) ≥ (29/40000)(181/640) sinh(2t/5) + (3/51200) sinh(t/8)`.

With `P = F + 2 sinh(2t) - C` the arithmetic partition clock (the regular-circle arithmetic eta
clock plus its pole term) and `E = P'' - ω²P - 2(4-ω²) sinh(2t)`, the massive source
`S = F'' - ω²F` is exactly `E - V`; since `|S(t)| ≤ A(ω² + 1/150) t e^{t/300}`, the excess `E` is
eventually positive and `E/V → 1` with an explicit exponentially small two-sided relative error.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The real completion coefficients -/

/-- Real completion moments `c_j`. -/
def liClockCompletionCoeff (j : ℕ) : ℝ := (liClockPairedEtaCompletionMoment j).re

/-- Gamma squares `x_n = (2n + 5/2)^{-2}`. -/
def liClockCompletionGammaSquare (n : ℕ) : ℝ := liClockPairedEtaGammaReciprocal n ^ 2

/-- The real dyadic moment `d_j`. -/
def liClockCompletionDyadicMoment (j : ℕ) : ℝ :=
  (∑' k : ℤ, liClockPairedEtaDyadicReciprocal k ^ (2 * j + 2)).re

theorem summable_liClockCompletionGammaSquare_pow (j : ℕ) :
    Summable (fun n => liClockCompletionGammaSquare n ^ (j + 1)) := by
  refine (summable_liClockPairedEtaGammaReciprocal_pow j).congr fun n => ?_
  unfold liClockCompletionGammaSquare
  rw [← pow_mul]; ring_nf

theorem liClockCompletionCoeff_eq (j : ℕ) :
    liClockCompletionCoeff j =
      ∑' n, liClockCompletionGammaSquare n ^ (j + 1) + liClockCompletionDyadicMoment j := by
  unfold liClockCompletionCoeff liClockPairedEtaCompletionMoment liClockCompletionDyadicMoment
  rw [Complex.add_re, Complex.ofReal_re]
  congr 1
  refine tsum_congr fun n => ?_
  unfold liClockCompletionGammaSquare
  rw [← pow_mul]; ring_nf

theorem abs_liClockCompletionDyadicMoment_le (j : ℕ) :
    |liClockCompletionDyadicMoment j| ≤ 3 * (1 / 64 : ℝ) ^ (j + 1) :=
  (Complex.abs_re_le_norm _).trans (liClockPairedEtaDyadicMoment_norm_le j)

theorem liClockCompletionGammaSquare_nonneg (n : ℕ) : 0 ≤ liClockCompletionGammaSquare n :=
  sq_nonneg _

theorem liClockCompletionGammaSquare_le (n : ℕ) : liClockCompletionGammaSquare n ≤ 4 / 25 := by
  have h0 := liClockPairedEtaGammaReciprocal_nonneg n
  have h1 := liClockPairedEtaGammaReciprocal_le_two_fifths n
  unfold liClockCompletionGammaSquare
  nlinarith

private theorem gammaSquare_value (n : ℕ) :
    liClockCompletionGammaSquare n = 4 / (4 * (n : ℝ) + 5) ^ 2 := by
  unfold liClockCompletionGammaSquare liClockPairedEtaGammaReciprocal
  have : (2 * (n : ℝ) + 5 / 2) = (4 * n + 5) / 2 := by ring
  rw [this, inv_pow, div_pow]
  field_simp
  ring

/-- **Stronger mass coefficient.**  `c_0 > 1657/8000`. -/
theorem liClockCompletionCoeff_zero_gt : (1657 / 8000 : ℝ) < liClockCompletionCoeff 0 := by
  rw [liClockCompletionCoeff_eq]
  have hsum := (summable_liClockCompletionGammaSquare_pow 0).sum_le_tsum (Finset.range 5)
    (fun n _ => pow_nonneg (liClockCompletionGammaSquare_nonneg n) _)
  have hfin : (∑ n ∈ Finset.range 5, liClockCompletionGammaSquare n ^ (0 + 1)) =
      4 / 25 + 4 / 81 + 4 / 169 + 4 / 289 + 4 / 441 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one, gammaSquare_value]
    norm_num
  rw [hfin] at hsum
  have hd := (abs_le.mp (abs_liClockCompletionDyadicMoment_le 0)).1
  norm_num at hd hsum ⊢
  linarith

/-- **Improved massive rate.**  `ω² > 6429/40000 = 4/25 + 29/40000`. -/
theorem liEvenCrossActualClockGreenRate_sq_gt :
    (6429 / 40000 : ℝ) < liEvenCrossActualClockGreenRate ^ 2 := by
  rw [liEvenCrossActualClockGreenRate_bounds.1]
  have h1 := liClockCompletionCoeff_zero_gt
  have h2 := normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive
  unfold liClockCompletionCoeff at h1
  linarith

/-! ## Moment-ratio contraction -/

private theorem pow_ge_mul_pow {x b : ℝ} (hb : 0 ≤ b) (hx : b ≤ x) (j : ℕ) :
    x * b ^ j ≤ x ^ (j + 1) := by
  rw [pow_succ']
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hx j) (hb.trans hx)

/-- **Complete moment-ratio contraction.**  `α c_j - c_{j+1} > (3/409600) β^j`. -/
theorem liClockCompletionCoeff_contraction (j : ℕ) :
    (3 / 409600 : ℝ) * (1 / 64) ^ j <
      4 / 25 * liClockCompletionCoeff j - liClockCompletionCoeff (j + 1) := by
  have hs1 := summable_liClockCompletionGammaSquare_pow j
  have hs2 := summable_liClockCompletionGammaSquare_pow (j + 1)
  have hdiff : 4 / 25 * liClockCompletionCoeff j - liClockCompletionCoeff (j + 1) =
      (∑' n, liClockCompletionGammaSquare n ^ (j + 1) * (4 / 25 - liClockCompletionGammaSquare n)) +
        (4 / 25 * liClockCompletionDyadicMoment j - liClockCompletionDyadicMoment (j + 1)) := by
    rw [liClockCompletionCoeff_eq, liClockCompletionCoeff_eq]
    have hsum : (∑' n, liClockCompletionGammaSquare n ^ (j + 1) * (4 / 25 - liClockCompletionGammaSquare n)) =
        4 / 25 * (∑' n, liClockCompletionGammaSquare n ^ (j + 1)) -
          ∑' n, liClockCompletionGammaSquare n ^ (j + 1 + 1) := by
      rw [← tsum_mul_left, ← Summable.tsum_sub (hs1.mul_left _) hs2]
      refine tsum_congr fun n => ?_
      ring
    rw [hsum]; ring
  have hterm : ∀ n, 0 ≤ liClockCompletionGammaSquare n ^ (j + 1) *
      (4 / 25 - liClockCompletionGammaSquare n) := fun n =>
    mul_nonneg (pow_nonneg (liClockCompletionGammaSquare_nonneg n) _)
      (by linarith [liClockCompletionGammaSquare_le n])
  have hsumm : Summable (fun n => liClockCompletionGammaSquare n ^ (j + 1) *
      (4 / 25 - liClockCompletionGammaSquare n)) :=
    (hs1.mul_right (4 / 25)).sub hs2 |>.congr fun n => by ring
  have htwo := hsumm.sum_le_tsum (Finset.range 3) (fun n _ => hterm n)
  have hfin : (∑ n ∈ Finset.range 3, liClockCompletionGammaSquare n ^ (j + 1) *
      (4 / 25 - liClockCompletionGammaSquare n)) =
      (4 / 81) ^ (j + 1) * (224 / 2025) + (4 / 169) ^ (j + 1) * (576 / 4225) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, gammaSquare_value]
    norm_num
  rw [hfin] at htwo
  have hx1 : (4 / 81 : ℝ) * (1 / 64) ^ j ≤ (4 / 81) ^ (j + 1) :=
    pow_ge_mul_pow (by norm_num) (by norm_num) j
  have hx2 : (4 / 169 : ℝ) * (1 / 64) ^ j ≤ (4 / 169) ^ (j + 1) :=
    pow_ge_mul_pow (by norm_num) (by norm_num) j
  have hd1 := abs_le.mp (abs_liClockCompletionDyadicMoment_le j)
  have hd2 := abs_le.mp (abs_liClockCompletionDyadicMoment_le (j + 1))
  have hβ : (0 : ℝ) < (1 / 64) ^ j := by positivity
  have hpow1 : (1 / 64 : ℝ) ^ (j + 1) = (1 / 64) * (1 / 64) ^ j := by ring
  have hpow2 : (1 / 64 : ℝ) ^ (j + 1 + 1) = (1 / 64) ^ 2 * (1 / 64) ^ j := by ring
  rw [hpow1] at hd1
  rw [hpow2] at hd2
  rw [hdiff]
  nlinarith [mul_pos hβ (by norm_num : (0 : ℝ) < 3 / 409600)]

theorem liClockCompletionCoeff_pos (j : ℕ) : 0 < liClockCompletionCoeff j :=
  liClockPairedEtaCompletionMoment_re_pos j

/-- Strict geometric ceiling `c_j < c_0 α^j` for `j ≥ 1`, and `c_j ≤ c_0 α^j` for all `j`. -/
theorem liClockCompletionCoeff_le_geometric (j : ℕ) :
    liClockCompletionCoeff j ≤ liClockCompletionCoeff 0 * (4 / 25) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h := liClockCompletionCoeff_contraction j
      have : (0 : ℝ) < 3 / 409600 * (1 / 64) ^ j := by positivity
      rw [pow_succ]
      nlinarith

theorem liClockCompletionCoeff_lt_geometric {j : ℕ} (hj : 1 ≤ j) :
    liClockCompletionCoeff j < liClockCompletionCoeff 0 * (4 / 25) ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have h := liClockCompletionCoeff_contraction k
  have hk := liClockCompletionCoeff_le_geometric k
  have : (0 : ℝ) < 3 / 409600 * (1 / 64) ^ k := by positivity
  rw [pow_succ]
  nlinarith

theorem geometricCoeffBound_liClockCompletionCoeff :
    GeometricCoeffBound liClockCompletionCoeff (liClockCompletionCoeff 0) (4 / 25) := by
  intro j
  rw [abs_of_pos (liClockCompletionCoeff_pos j)]
  exact liClockCompletionCoeff_le_geometric j

/-- **Sharp ceiling.**  `c_j / α^{j+1} → 1`. -/
theorem tendsto_liClockCompletionCoeff_div_pow :
    Tendsto (fun j : ℕ => liClockCompletionCoeff j / (4 / 25) ^ (j + 1)) atTop (𝓝 1) := by
  -- `c_j = α^{j+1} + (Gamma tail) + d_j` with tail `≤ (4/81)^j Σ x_n`.
  set X := ∑' n, liClockCompletionGammaSquare n ^ (0 + 1)
  have hX0 : 0 ≤ X := tsum_nonneg fun n => pow_nonneg (liClockCompletionGammaSquare_nonneg n) _
  have hsplit : ∀ j, liClockCompletionCoeff j = (4 / 25) ^ (j + 1) +
      (∑' n, liClockCompletionGammaSquare (n + 1) ^ (j + 1)) + liClockCompletionDyadicMoment j := by
    intro j
    rw [liClockCompletionCoeff_eq, (summable_liClockCompletionGammaSquare_pow j).tsum_eq_zero_add]
    rw [gammaSquare_value]; norm_num
  have htail : ∀ j, 0 ≤ ∑' n, liClockCompletionGammaSquare (n + 1) ^ (j + 1) ∧
      ∑' n, liClockCompletionGammaSquare (n + 1) ^ (j + 1) ≤ (4 / 81) ^ j * X := by
    intro j
    have hs := (summable_liClockCompletionGammaSquare_pow j).comp_injective (add_left_injective 1)
    have hs0 := (summable_liClockCompletionGammaSquare_pow 0).comp_injective (add_left_injective 1)
    refine ⟨tsum_nonneg fun n => pow_nonneg (liClockCompletionGammaSquare_nonneg _) _, ?_⟩
    have hle : ∀ n, liClockCompletionGammaSquare (n + 1) ^ (j + 1) ≤
        (4 / 81) ^ j * liClockCompletionGammaSquare (n + 1) ^ (0 + 1) := by
      intro n
      have hx := liClockCompletionGammaSquare_nonneg (n + 1)
      have hx81 : liClockCompletionGammaSquare (n + 1) ≤ 4 / 81 := by
        rw [gammaSquare_value]; push_cast
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hp := pow_le_pow_left₀ hx hx81 j
      rw [zero_add, pow_one, pow_succ]
      nlinarith
    calc ∑' n, liClockCompletionGammaSquare (n + 1) ^ (j + 1) ≤
        ∑' n, (4 / 81) ^ j * liClockCompletionGammaSquare (n + 1) ^ (0 + 1) :=
          Summable.tsum_le_tsum hle hs (hs0.mul_left _)
      _ = (4 / 81) ^ j * ∑' n, liClockCompletionGammaSquare (n + 1) ^ (0 + 1) := tsum_mul_left
      _ ≤ (4 / 81) ^ j * X := by
          gcongr
          have hX : X = liClockCompletionGammaSquare 0 ^ (0 + 1) +
              ∑' n, liClockCompletionGammaSquare (n + 1) ^ (0 + 1) :=
            (summable_liClockCompletionGammaSquare_pow 0).tsum_eq_zero_add
          linarith [pow_nonneg (liClockCompletionGammaSquare_nonneg 0) (0 + 1)]
  have hr1 : Tendsto (fun j : ℕ => (4 / 81 : ℝ) ^ j * X / (4 / 25) ^ (j + 1)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 25 / 81)
      (by norm_num)).const_mul (X * (25 / 4))
    simp only [mul_zero] at h
    refine h.congr fun j => ?_
    rw [div_pow, pow_succ]
    field_simp
    rw [mul_assoc, mul_assoc, ← mul_pow, ← mul_pow]
    norm_num
  have hr2 : Tendsto (fun j : ℕ => 3 * (1 / 64 : ℝ) ^ (j + 1) / (4 / 25) ^ (j + 1)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 25 / 256)
      (by norm_num)).const_mul (3 * (25 / 256))
    simp only [mul_zero] at h
    refine h.congr fun j => ?_
    rw [mul_div_assoc, ← div_pow, show (1 / 64 : ℝ) / (4 / 25) = 25 / 256 by norm_num, pow_succ]
    ring
  have hupper : Tendsto (fun j : ℕ => 1 + (4 / 81 : ℝ) ^ j * X / (4 / 25) ^ (j + 1) +
      3 * (1 / 64 : ℝ) ^ (j + 1) / (4 / 25) ^ (j + 1)) atTop (𝓝 1) := by
    simpa using (hr1.const_add 1).add hr2
  have hlower : Tendsto (fun j : ℕ => 1 - 3 * (1 / 64 : ℝ) ^ (j + 1) / (4 / 25) ^ (j + 1))
      atTop (𝓝 1) := by
    simpa using hr2.const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun j => ?_) (fun j => ?_)
  · have hp : (0 : ℝ) < (4 / 25) ^ (j + 1) := by positivity
    rw [hsplit j, le_div_iff₀ hp]
    have hd := (abs_le.mp (abs_liClockCompletionDyadicMoment_le j)).1
    have ht := (htail j).1
    have : (1 - 3 * (1 / 64 : ℝ) ^ (j + 1) / (4 / 25) ^ (j + 1)) * (4 / 25) ^ (j + 1) =
        (4 / 25) ^ (j + 1) - 3 * (1 / 64) ^ (j + 1) := by field_simp
    rw [this]; linarith
  · have hp : (0 : ℝ) < (4 / 25) ^ (j + 1) := by positivity
    rw [hsplit j, div_le_iff₀ hp]
    have hd := (abs_le.mp (abs_liClockCompletionDyadicMoment_le j)).2
    have ht := (htail j).2
    have : (1 + (4 / 81 : ℝ) ^ j * X / (4 / 25) ^ (j + 1) +
        3 * (1 / 64) ^ (j + 1) / (4 / 25) ^ (j + 1)) * (4 / 25) ^ (j + 1) =
        (4 / 25) ^ (j + 1) + (4 / 81) ^ j * X + 3 * (1 / 64) ^ (j + 1) := by field_simp
    rw [this]; linarith

/-- **Sharp limiting ratio.**  `c_{j+1}/c_j → 4/25`: no smaller uniform ceiling holds eventually. -/
theorem tendsto_liClockCompletionCoeff_ratio :
    Tendsto (fun j : ℕ => liClockCompletionCoeff (j + 1) / liClockCompletionCoeff j) atTop
      (𝓝 (4 / 25)) := by
  have h := tendsto_liClockCompletionCoeff_div_pow
  have h1 := h.comp (tendsto_add_atTop_nat 1)
  have hq := (h1.div h (by norm_num)).const_mul (4 / 25 : ℝ)
  simp only [div_one, mul_one] at hq
  refine hq.congr fun j => ?_
  have hc := (liClockCompletionCoeff_pos j).ne'
  have hp : ((4 : ℝ) / 25) ^ (j + 1) ≠ 0 := by positivity
  show 4 / 25 * ((liClockCompletionCoeff (j + 1) / (4 / 25) ^ (j + 1 + 1)) /
    (liClockCompletionCoeff j / (4 / 25) ^ (j + 1))) = _
  rw [pow_succ ((4 : ℝ) / 25) (j + 1)]
  field_simp

/-! ## The real completion clock -/

/-- The full real completion clock `C(t) = Σ c_j t^{2j+1}/(2j+1)!`. -/
def liClockCompletionClock (t : ℝ) : ℝ := oddFactorialSeries liClockCompletionCoeff t

/-- The completion clock is the real part of the completion contour at every regular radius. -/
theorem liClockCompletionClock_eq_re {r : ℝ} (hr : 0 < r) (hrhalf : r < 1 / 2) (t : ℝ) :
    liClockCompletionClock t = (liClockPairedEtaCompletionClockResponse r (t : ℂ)).re := by
  rw [liClockPairedEtaCompletionClockResponse_eq_tsum hr hrhalf,
    Complex.re_tsum (summable_norm_liClockPairedEtaCompletionClockTerm (t : ℂ)).of_norm]
  unfold liClockCompletionClock oddFactorialSeries
  refine tsum_congr fun j => ?_
  unfold liClockPairedEtaCompletionClockTerm liClockCompletionCoeff
  rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast, Complex.div_ofReal_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem iteratedDeriv_two_liClockCompletionClock (t : ℝ) :
    iteratedDeriv 2 liClockCompletionClock t =
      oddFactorialSeries (fun j => liClockCompletionCoeff (j + 1)) t :=
  iteratedDeriv_two_oddFactorialSeries (by norm_num) geometricCoeffBound_liClockCompletionCoeff t

private theorem geom_shift_bound :
    GeometricCoeffBound (fun j => liClockCompletionCoeff (j + 1))
      (liClockCompletionCoeff 0 * (4 / 25)) (4 / 25) :=
  geometricCoeffBound_liClockCompletionCoeff.shift

private theorem geom_beta_bound :
    GeometricCoeffBound (fun j => (3 / 409600 : ℝ) * (1 / 64) ^ j) (3 / 409600) (1 / 64) := by
  intro j; rw [abs_of_pos (by positivity)]

/-- **Complete-clock curvature gap.**  `α C(t) - C''(t) ≥ (3/51200) sinh(t/8)` on `t ≥ 0`. -/
theorem liClockCompletionClock_curvature_gap {t : ℝ} (ht : 0 ≤ t) :
    (3 / 51200 : ℝ) * Real.sinh (t / 8) ≤
      4 / 25 * liClockCompletionClock t - iteratedDeriv 2 liClockCompletionClock t := by
  rw [iteratedDeriv_two_liClockCompletionClock]
  have hgap : GeometricCoeffBound (fun j => 4 / 25 * liClockCompletionCoeff j -
      liClockCompletionCoeff (j + 1)) (2 * liClockCompletionCoeff 0) (4 / 25) := by
    intro j
    have h1 := liClockCompletionCoeff_le_geometric j
    have h2 := liClockCompletionCoeff_le_geometric (j + 1)
    have h3 := liClockCompletionCoeff_pos j
    have h4 := liClockCompletionCoeff_pos (j + 1)
    have hc := liClockCompletionCoeff_contraction j
    have hb : (0 : ℝ) < 3 / 409600 * (1 / 64) ^ j := by positivity
    rw [abs_of_pos (by linarith), pow_succ] at *
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 25) j]
  have hlin : 4 / 25 * liClockCompletionClock t -
      oddFactorialSeries (fun j => liClockCompletionCoeff (j + 1)) t =
      oddFactorialSeries (fun j => 4 / 25 * liClockCompletionCoeff j -
        liClockCompletionCoeff (j + 1)) t := by
    unfold liClockCompletionClock oddFactorialSeries
    rw [← tsum_mul_left, ← Summable.tsum_sub
      ((summable_oddFactorialSeries_term (by norm_num)
        geometricCoeffBound_liClockCompletionCoeff t).mul_left _)
      (summable_oddFactorialSeries_term (by norm_num) geom_shift_bound t)]
    refine tsum_congr fun j => ?_
    ring
  rw [hlin]
  have hsinh := oddFactorialSeries_geometric (c := 3 / 409600) (R := 1 / 64) (by norm_num) t
  have hsq : Real.sqrt (1 / 64 : ℝ) = 1 / 8 := by
    rw [show (1 / 64 : ℝ) = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsq] at hsinh
  have hle := oddFactorialSeries_le_of_le (by norm_num) (by norm_num) geom_beta_bound hgap
    (fun j => (liClockCompletionCoeff_contraction j).le) ht
  rw [hsinh] at hle
  calc (3 / 51200 : ℝ) * Real.sinh (t / 8) = 3 / 409600 / (1 / 8) * Real.sinh (1 / 8 * t) := by
        rw [show 1 / 8 * t = t / 8 by ring]; norm_num
    _ ≤ _ := hle

/-- `C''(t) < α C(t)` for every positive clock. -/
theorem iteratedDeriv_two_liClockCompletionClock_lt {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 liClockCompletionClock t < 4 / 25 * liClockCompletionClock t := by
  have h := liClockCompletionClock_curvature_gap ht.le
  have hs : 0 < Real.sinh (t / 8) := Real.sinh_pos_iff.2 (by positivity)
  nlinarith

/-- `C(t) < (5/2) c_0 sinh(2t/5)` for every positive clock. -/
theorem liClockCompletionClock_lt_sinh {t : ℝ} (ht : 0 < t) :
    liClockCompletionClock t <
      5 / 2 * liClockCompletionCoeff 0 * Real.sinh (2 / 5 * t) := by
  have hb : GeometricCoeffBound (fun j => liClockCompletionCoeff 0 * (4 / 25) ^ j)
      (liClockCompletionCoeff 0) (4 / 25) := by
    intro j; rw [abs_of_pos (by have := liClockCompletionCoeff_pos 0; positivity)]
  have hlt := oddFactorialSeries_lt_of_le_of_lt (by norm_num) (by norm_num)
    geometricCoeffBound_liClockCompletionCoeff hb liClockCompletionCoeff_le_geometric
    (i := 1) (liClockCompletionCoeff_lt_geometric le_rfl) ht
  rw [oddFactorialSeries_geometric (by norm_num)] at hlt
  have hsq : Real.sqrt (4 / 25 : ℝ) = 2 / 5 := by
    rw [show (4 / 25 : ℝ) = (2 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsq] at hlt
  unfold liClockCompletionClock
  calc oddFactorialSeries liClockCompletionCoeff t <
      liClockCompletionCoeff 0 / (2 / 5) * Real.sinh (2 / 5 * t) := hlt
    _ = _ := by ring

/-- The completion clock dominates its installed hyperbolic floor. -/
theorem liClockCompletionClock_ge_sinh {t : ℝ} (ht : 0 ≤ t) :
    (181 / 640 : ℝ) * Real.sinh (2 / 5 * t) ≤ liClockCompletionClock t := by
  rw [liClockCompletionClock_eq_re (r := 1 / 4) (by norm_num) (by norm_num)]
  exact liClockPairedEtaCompletionClockResponse_re_ge_sinh (by norm_num) (by norm_num) ht

/-! ## The massive envelope and the arithmetic excess -/

/-- The positive massive completion envelope `V = ω² C - C''`. -/
def liClockMassiveCompletionEnvelope (t : ℝ) : ℝ :=
  liEvenCrossActualClockGreenRate ^ 2 * liClockCompletionClock t -
    iteratedDeriv 2 liClockCompletionClock t

/-- **Exact envelope decomposition.**  `V = (ω² - α) C + (α C - C'')`, so
`V ≥ (ω² - α) C + (3/51200) sinh(t/8)`. -/
theorem liClockMassiveCompletionEnvelope_ge {t : ℝ} (ht : 0 ≤ t) :
    (liEvenCrossActualClockGreenRate ^ 2 - 4 / 25) * liClockCompletionClock t +
        (3 / 51200 : ℝ) * Real.sinh (t / 8) ≤ liClockMassiveCompletionEnvelope t := by
  have h := liClockCompletionClock_curvature_gap ht
  unfold liClockMassiveCompletionEnvelope
  linarith

/-- **Positive massive envelope.**
`V(t) ≥ (29/40000)(181/640) sinh(2t/5) + (3/51200) sinh(t/8)` on `t ≥ 0`. -/
theorem liClockMassiveCompletionEnvelope_ge_sinh {t : ℝ} (ht : 0 ≤ t) :
    (29 / 40000 : ℝ) * (181 / 640) * Real.sinh (2 / 5 * t) + (3 / 51200 : ℝ) * Real.sinh (t / 8) ≤
      liClockMassiveCompletionEnvelope t := by
  have hV := liClockMassiveCompletionEnvelope_ge ht
  have hω := liEvenCrossActualClockGreenRate_sq_gt
  have hC := liClockCompletionClock_ge_sinh ht
  have hs : 0 ≤ Real.sinh (2 / 5 * t) := Real.sinh_nonneg_iff.2 (by positivity)
  have hC0 : 0 ≤ liClockCompletionClock t := le_trans (by positivity) hC
  have : (29 / 40000 : ℝ) * ((181 / 640) * Real.sinh (2 / 5 * t)) ≤
      (liEvenCrossActualClockGreenRate ^ 2 - 4 / 25) * liClockCompletionClock t :=
    mul_le_mul (by linarith) hC (by positivity) (by linarith)
  linarith

/-- The literal massive source `S = F'' - ω² F`. -/
def liEvenCrossActualClockMassiveSource (t : ℝ) : ℝ :=
  iteratedDeriv 2 liEvenCrossActualClockResponse t -
    liEvenCrossActualClockGreenRate ^ 2 * liEvenCrossActualClockResponse t

/-- **Complete-copy source bound.**  `|S(t)| ≤ A(ω² + 1/150) t e^{t/300}` on `t ≥ 0`. -/
theorem abs_liEvenCrossActualClockMassiveSource_le {t : ℝ} (ht : 0 ≤ t) :
    |liEvenCrossActualClockMassiveSource t| ≤
      xiShiftAbsoluteMass 0 * (liEvenCrossActualClockGreenRate ^ 2 + 1 / 150) * t *
        Real.exp (t / 300) := by
  have hF := norm_liEvenCrossActualClockResponse_le_mass_mul_exp ht
  rw [Real.norm_eq_abs] at hF
  have hF2 : |iteratedDeriv 2 liEvenCrossActualClockResponse t| ≤
      1 / 150 * (xiShiftAbsoluteMass 0 * t * Real.exp (t / 300)) := by
    rw [iteratedDeriv_two_liEvenCrossActualClockResponse, abs_neg]
    have hsum : Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖ ^ (0 + 1)) :=
      summable_xiShiftAbsoluteMass 0
    have hterm : ∀ q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹ ^ 3 *
        Complex.sin ((t : ℂ) * (xiSpectralPoint q)⁻¹)‖ ≤
        1 / 150 * (‖xiZeroCopyReciprocalSquare q‖ ^ (0 + 1) * t * Real.exp (t / 300)) := by
      intro q
      set w := (xiSpectralPoint q)⁻¹
      have h1 := liClock_norm_mul_sin_le_imaginary_exp ht w
      have hw2 : ‖w‖ ^ 2 = ‖xiZeroCopyReciprocalSquare q‖ := by
        simp [xiZeroCopyReciprocalSquare, w, norm_pow]
      have hsmall := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
      have him : |w.im| < 1 / 300 := abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q
      have hexp : Real.exp (t * |w.im|) ≤ Real.exp (t / 300) :=
        Real.exp_le_exp.2 (by nlinarith [abs_nonneg w.im])
      have heq : ‖w ^ 3 * Complex.sin ((t : ℂ) * w)‖ = ‖w‖ ^ 2 * ‖w * Complex.sin ((t : ℂ) * w)‖ := by
        rw [norm_mul, norm_mul, norm_pow]; ring
      rw [heq]
      calc ‖w‖ ^ 2 * ‖w * Complex.sin ((t : ℂ) * w)‖ ≤
          ‖w‖ ^ 2 * (t * ‖w‖ ^ 2 * Real.exp (t * |w.im|)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (1 / 150) * (‖w‖ ^ 2 * t * Real.exp (t / 300)) := by
            rw [hw2]
            have hn := norm_nonneg (xiZeroCopyReciprocalSquare q)
            have := mul_le_mul (hsmall.le) hexp (Real.exp_pos _).le (by norm_num)
            nlinarith [Real.exp_pos (t * |w.im|), Real.exp_pos (t / 300), mul_nonneg hn ht]
        _ = 1 / 150 * (‖xiZeroCopyReciprocalSquare q‖ ^ (0 + 1) * t * Real.exp (t / 300)) := by
            rw [hw2]; ring
    have hsummable : Summable (fun q : XiZeroCopy =>
        1 / 150 * (‖xiZeroCopyReciprocalSquare q‖ ^ (0 + 1) * t * Real.exp (t / 300))) :=
      ((hsum.mul_right t).mul_right _).mul_left _
    have hnorm : Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹ ^ 3 *
        Complex.sin ((t : ℂ) * (xiSpectralPoint q)⁻¹)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsummable
    refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hnorm).trans ?_)
    refine (Summable.tsum_le_tsum hterm hnorm hsummable).trans ?_
    rw [tsum_mul_left, tsum_mul_right, tsum_mul_right]
    rfl
  unfold liEvenCrossActualClockMassiveSource
  have hω0 : 0 ≤ liEvenCrossActualClockGreenRate ^ 2 := sq_nonneg _
  calc |iteratedDeriv 2 liEvenCrossActualClockResponse t -
        liEvenCrossActualClockGreenRate ^ 2 * liEvenCrossActualClockResponse t| ≤
      |iteratedDeriv 2 liEvenCrossActualClockResponse t| +
        |liEvenCrossActualClockGreenRate ^ 2 * liEvenCrossActualClockResponse t| := abs_sub _ _
    _ = |iteratedDeriv 2 liEvenCrossActualClockResponse t| +
        liEvenCrossActualClockGreenRate ^ 2 * |liEvenCrossActualClockResponse t| := by
        rw [abs_mul, abs_of_nonneg hω0]
    _ ≤ 1 / 150 * (xiShiftAbsoluteMass 0 * t * Real.exp (t / 300)) +
        liEvenCrossActualClockGreenRate ^ 2 * (xiShiftAbsoluteMass 0 * t * Real.exp (t / 300)) := by
        gcongr
    _ = _ := by ring

/-- The arithmetic partition clock `P = F + 2 sinh(2t) - C`. -/
def liClockArithmeticPartitionClock (t : ℝ) : ℝ :=
  liEvenCrossActualClockResponse t + 2 * Real.sinh (2 * t) - liClockCompletionClock t

/-- `P` is the regular-circle arithmetic eta clock plus its pole term `2 sinh(2t)`. -/
theorem exists_liClockArithmeticPartitionClock_eq_arithmetic :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ t : ℝ,
      liClockArithmeticPartitionClock t =
        (liClockPairedEtaArithmeticClockResponse r (t : ℂ)).re + 2 * Real.sinh (2 * t) := by
  obtain ⟨r₀, hr₀, hr₀small, h⟩ := exists_liClockPairedEtaArithmeticClockResponse_source_radius
  refine ⟨r₀, hr₀, fun r hr hrr t => ?_⟩
  have hrhalf : r < 1 / 2 := by linarith
  rw [h r hr hrr, Complex.sub_re, liEvenCrossActualComplexClockResponse_ofReal,
    Complex.ofReal_re, ← liClockCompletionClock_eq_re hr hrhalf]
  unfold liClockArithmeticPartitionClock
  ring

/-- The arithmetic excess `E = P'' - ω² P - 2(4 - ω²) sinh(2t)`. -/
def liClockArithmeticExcess (t : ℝ) : ℝ :=
  iteratedDeriv 2 liClockArithmeticPartitionClock t -
    liEvenCrossActualClockGreenRate ^ 2 * liClockArithmeticPartitionClock t -
    2 * (4 - liEvenCrossActualClockGreenRate ^ 2) * Real.sinh (2 * t)

/-- **Exact massive decomposition.**  `S = E - V`. -/
theorem liEvenCrossActualClockMassiveSource_eq (t : ℝ) :
    liEvenCrossActualClockMassiveSource t =
      liClockArithmeticExcess t - liClockMassiveCompletionEnvelope t := by
  have hF : ContDiff ℝ 2 liEvenCrossActualClockResponse :=
    contDiff_liEvenCrossActualClockResponse.of_le (by norm_cast)
  have hC : ContDiff ℝ 2 liClockCompletionClock :=
    contDiff_two_oddFactorialSeries (by norm_num) geometricCoeffBound_liClockCompletionCoeff
  have hS : ContDiff ℝ 2 (fun t : ℝ => 2 * Real.sinh (2 * t)) := by fun_prop
  have hlin : ∀ s : ℝ, HasDerivAt (fun x : ℝ => 2 * x) 2 s := fun s => by
    simpa using (hasDerivAt_id' s).const_mul (2 : ℝ)
  have hd1 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => 2 * Real.sinh (2 * t)) (4 * Real.cosh (2 * s)) s := by
    intro s
    have h := ((hlin s).sinh).const_mul (2 : ℝ)
    rw [show (2 : ℝ) * (Real.cosh (2 * s) * 2) = 4 * Real.cosh (2 * s) by ring] at h
    exact h
  have hd2 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => 4 * Real.cosh (2 * t)) (8 * Real.sinh (2 * s)) s := by
    intro s
    have h := ((hlin s).cosh).const_mul (4 : ℝ)
    rw [show (4 : ℝ) * (Real.sinh (2 * s) * 2) = 8 * Real.sinh (2 * s) by ring] at h
    exact h
  have hS2 : iteratedDeriv 2 (fun t : ℝ => 2 * Real.sinh (2 * t)) t = 8 * Real.sinh (2 * t) := by
    have h1 : deriv (fun t : ℝ => 2 * Real.sinh (2 * t)) = fun t => 4 * Real.cosh (2 * t) :=
      funext fun s => (hd1 s).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1, (hd2 t).deriv]
  have hP : iteratedDeriv 2 liClockArithmeticPartitionClock t =
      iteratedDeriv 2 liEvenCrossActualClockResponse t + 8 * Real.sinh (2 * t) -
        iteratedDeriv 2 liClockCompletionClock t := by
    have he : liClockArithmeticPartitionClock = fun t => (liEvenCrossActualClockResponse t +
        2 * Real.sinh (2 * t)) - liClockCompletionClock t := rfl
    rw [he, show (fun t => liEvenCrossActualClockResponse t + 2 * Real.sinh (2 * t) -
        liClockCompletionClock t) = ((liEvenCrossActualClockResponse +
          fun t => 2 * Real.sinh (2 * t)) - liClockCompletionClock) from rfl,
      iteratedDeriv_sub (show ContDiff ℝ 2 (liEvenCrossActualClockResponse +
        fun t => 2 * Real.sinh (2 * t)) from hF.add hS).contDiffAt hC.contDiffAt,
      iteratedDeriv_add hF.contDiffAt hS.contDiffAt, hS2]
  unfold liEvenCrossActualClockMassiveSource liClockArithmeticExcess
    liClockMassiveCompletionEnvelope
  rw [hP]
  unfold liClockArithmeticPartitionClock
  ring

private theorem tendsto_clock_exp_div_sinh (A : ℝ) :
    Tendsto (fun t : ℝ => A * t * Real.exp (t / 300) / Real.sinh (2 / 5 * t)) atTop (𝓝 0) := by
  have hc : (0 : ℝ) < 119 / 300 := by norm_num
  have hbase : Tendsto (fun t : ℝ => t * Real.exp (-(119 / 300 * t))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hc)
    have h2 := h.const_mul (300 / 119)
    simp only [mul_zero] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp_apply, id, pow_one]
    field_simp
  have hmaj := hbase.const_mul (4 * |A|)
  simp only [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  have hx : (6 / 5 : ℝ) ≤ 2 / 5 * t := by linarith
  have he2 : (2 : ℝ) ≤ Real.exp (2 / 5 * t) := by
    have := Real.add_one_le_exp (2 / 5 * t)
    linarith
  have hsinh : Real.exp (2 / 5 * t) / 4 ≤ Real.sinh (2 / 5 * t) := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-(2 / 5 * t))
    have : Real.exp (-(2 / 5 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hs0 : 0 < Real.sinh (2 / 5 * t) := lt_of_lt_of_le (by positivity) hsinh
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hs0, div_le_iff₀ hs0, abs_mul, abs_mul,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ t), abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (t / 300) = Real.exp (-(119 / 300 * t)) * Real.exp (2 / 5 * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  have hA := abs_nonneg A
  have hE := Real.exp_pos (-(119 / 300 * t))
  have hE2 := Real.exp_pos (2 / 5 * t)
  nlinarith [mul_le_mul_of_nonneg_left hsinh
    (by positivity : (0 : ℝ) ≤ 4 * |A| * (t * Real.exp (-(119 / 300 * t))))]

private abbrev massiveFloor : ℝ := (29 / 40000 : ℝ) * (181 / 640)

/-- **Two-sided relative cancellation.**  For `t > 0`,
`|E/V - 1| ≤ A(ω² + 1/150) t e^{t/300} / [(29/40000)(181/640) sinh(2t/5)]`. -/
theorem abs_liClockArithmeticExcess_div_sub_one_le {t : ℝ} (ht : 0 < t) :
    |liClockArithmeticExcess t / liClockMassiveCompletionEnvelope t - 1| ≤
      xiShiftAbsoluteMass 0 * (liEvenCrossActualClockGreenRate ^ 2 + 1 / 150) * t *
        Real.exp (t / 300) / ((29 / 40000 : ℝ) * (181 / 640) * Real.sinh (2 / 5 * t)) := by
  have hV := liClockMassiveCompletionEnvelope_ge_sinh ht.le
  have hs : 0 < Real.sinh (2 / 5 * t) := Real.sinh_pos_iff.2 (by positivity)
  have hs8 : 0 ≤ Real.sinh (t / 8) := Real.sinh_nonneg_iff.2 (by positivity)
  have hfloor : 0 < (29 / 40000 : ℝ) * (181 / 640) * Real.sinh (2 / 5 * t) := by positivity
  have hfV : (29 / 40000 : ℝ) * (181 / 640) * Real.sinh (2 / 5 * t) ≤
      liClockMassiveCompletionEnvelope t := by nlinarith
  have hVpos : 0 < liClockMassiveCompletionEnvelope t := hfloor.trans_le hfV
  have hE : liClockArithmeticExcess t / liClockMassiveCompletionEnvelope t - 1 =
      liEvenCrossActualClockMassiveSource t / liClockMassiveCompletionEnvelope t := by
    rw [liEvenCrossActualClockMassiveSource_eq]; field_simp
  rw [hE, abs_div, abs_of_pos hVpos]
  have hS := abs_liEvenCrossActualClockMassiveSource_le ht.le
  calc |liEvenCrossActualClockMassiveSource t| / liClockMassiveCompletionEnvelope t ≤
      |liEvenCrossActualClockMassiveSource t| /
        ((29 / 40000 : ℝ) * (181 / 640) * Real.sinh (2 / 5 * t)) :=
        div_le_div_of_nonneg_left (abs_nonneg _) hfloor hfV
    _ ≤ _ := div_le_div_of_nonneg_right hS hfloor.le

/-- **Relative cancellation limit.**  `E/V → 1`. -/
theorem tendsto_liClockArithmeticExcess_div_envelope :
    Tendsto (fun t => liClockArithmeticExcess t / liClockMassiveCompletionEnvelope t) atTop
      (𝓝 1) := by
  have h := tendsto_clock_exp_div_sinh
    (xiShiftAbsoluteMass 0 * (liEvenCrossActualClockGreenRate ^ 2 + 1 / 150) /
      ((29 / 40000 : ℝ) * (181 / 640)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_norm, Real.norm_eq_abs]
  refine (abs_liClockArithmeticExcess_div_sub_one_le ht).trans_eq ?_
  have hs : Real.sinh (2 / 5 * t) ≠ 0 := (Real.sinh_pos_iff.2 (by positivity)).ne'
  field_simp

/-- **The stronger arithmetic upper comparison `E ≤ 0` fails eventually:** `E(t) > 0` for all
sufficiently large clocks. -/
theorem eventually_liClockArithmeticExcess_pos :
    ∀ᶠ t : ℝ in atTop, 0 < liClockArithmeticExcess t := by
  have h := tendsto_liClockArithmeticExcess_div_envelope.eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  have hV := liClockMassiveCompletionEnvelope_ge_sinh htpos.le
  have hs : 0 < Real.sinh (2 / 5 * t) := Real.sinh_pos_iff.2 (by positivity)
  have hs8 : 0 ≤ Real.sinh (t / 8) := Real.sinh_nonneg_iff.2 (by positivity)
  have hVpos : 0 < liClockMassiveCompletionEnvelope t := by nlinarith
  have := (lt_div_iff₀ hVpos).1 ht
  linarith

end RHTower
