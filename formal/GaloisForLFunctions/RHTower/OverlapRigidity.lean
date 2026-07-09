/-
Overlap rigidity for reflection-symmetric Dirichlet series.

An ordinary Dirichlet series `∑ aₙ n^{−s}` absolutely convergent on `Re s ≥ σ₀` with
`σ₀ < 1/2`, satisfying the exact reflection symmetry `L(s) = L(1−s)` throughout the overlap
strip `σ₀ < Re s < 1 − σ₀`, has no coefficients beyond `n = 1`.  The whole proof is a
fixed-locus evaluation: at `s = ½ + iy` — on the central line, inside the overlap for every
real `y` — the symmetry becomes `L(½+iy) = L(½−iy)`, and termwise subtraction
`n^{−(½+iy)} − n^{−(½−iy)} = −2i·n^{−½}·sin(y log n)` turns it into the vanishing of the
absolutely convergent sine series `∑ bₙ sin(y log n)`, `bₙ = aₙ n^{−½}`, for all real `y`.
Mean-value orthogonality of the distinct frequencies `log n` then kills every coefficient:
the Cesàro average `T⁻¹∫₀ᵀ sin(y log m)·(∑ bₙ sin(y log n)) dy` is identically zero, while
term-by-term Kronecker–Weyl time averaging (dominated convergence over `n`) sends it to
`b_m/2`.

Consequence: an exactly symmetric carrier is the constant `a₁`.  Sparse coefficient support
forces a small abscissa of absolute convergence, so sparse supports are incompatible with
exact reflection symmetry across the center.

* `sine_series_coeffs_zero` — analytic core: an absolutely convergent sine series in the
  frequencies `log n` vanishing for every real `y` has zero coefficients for all `n ≥ 2`.
* `overlap_rigidity` — the fixed-locus evaluation: reflection symmetry on the overlap strip
  plus absolute convergence past the center collapses all coefficients `n ≥ 2`.
* `overlap_rigidity_lseries_eq_one` — support collapse: a normalized (`a 0 = 0`, `a 1 = 1`)
  symmetric series is constantly `1` on its half-plane of convergence.
-/
import Mathlib
import GaloisForLFunctions.RHTower.WeylEquidistribution

open MeasureTheory intervalIntegral Filter Topology Complex

noncomputable section

namespace RHTower

/-- The four frequencies of the product-to-sum expansion of `sin(tα)·sin(tβ)`:
`α−β, β−α, α+β, −(α+β)`. -/
private def sinProdFreq (α β : ℝ) : Fin 4 → ℝ := ![α - β, β - α, α + β, -(α + β)]

/-- The four coefficients of the phase expansion of `sin(tα)·sin(tβ)`:
`(1/4, 1/4, −1/4, −1/4)`. -/
private def sinProdCoeff : Fin 4 → ℂ := ![1 / 4, 1 / 4, -(1 / 4), -(1 / 4)]

/-- **Product-to-sum for two sines, phase-polynomial form.**  For real `α, β, t`,
`sin(tα)·sin(tβ) = ¼e^{i(α−β)t} + ¼e^{i(β−α)t} − ¼e^{i(α+β)t} − ¼e^{−i(α+β)t}`,
via `sin A sin B = (cos(A−B) − cos(A+B))/2` and the exponential form of the cosine.
This is the exact four-term character sum consumed by the Kronecker–Weyl time average. -/
private theorem sin_mul_sin_eq_sum_char (α β t : ℝ) :
    (Real.sin (t * α) : ℂ) * (Real.sin (t * β) : ℂ)
      = ∑ i, sinProdCoeff i * Complex.exp (↑(sinProdFreq α β i) * Complex.I * ↑t) := by
  rw [Fin.sum_univ_four]
  simp only [sinProdFreq, sinProdCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  rw [Complex.ofReal_sin, Complex.ofReal_sin]
  have hsin : ∀ A B : ℂ, Complex.sin A * Complex.sin B
      = (Complex.exp ((A - B) * Complex.I) + Complex.exp (-(A - B) * Complex.I)
          - Complex.exp ((A + B) * Complex.I) - Complex.exp (-(A + B) * Complex.I)) / 4 := by
    intro A B
    have h1 : Complex.sin A * Complex.sin B
        = (Complex.cos (A - B) - Complex.cos (A + B)) / 2 := by
      rw [Complex.cos_sub, Complex.cos_add]; ring
    rw [h1, Complex.cos, Complex.cos]; ring
  rw [hsin]
  rw [show ((↑(t * α) : ℂ) - ↑(t * β)) * Complex.I = ↑(α - β) * Complex.I * ↑t by
        push_cast; ring,
      show -((↑(t * α) : ℂ) - ↑(t * β)) * Complex.I = ↑(β - α) * Complex.I * ↑t by
        push_cast; ring,
      show ((↑(t * α) : ℂ) + ↑(t * β)) * Complex.I = ↑(α + β) * Complex.I * ↑t by
        push_cast; ring,
      show -((↑(t * α) : ℂ) + ↑(t * β)) * Complex.I = ↑(-(α + β)) * Complex.I * ↑t by
        push_cast; ring]
  ring

/-- **Mean-value orthogonality of distinct sine frequencies.**  For `α ≠ β` with
`α + β ≠ 0`, the Cesàro time average `T⁻¹∫₀ᵀ sin(yα)·sin(yβ) dy` tends to `0`: all four
frequencies of the product-to-sum expansion are nonzero, so every character averages out. -/
private theorem sin_cross_average_tendsto_zero {α β : ℝ} (hne : α ≠ β) (hab : α + β ≠ 0) :
    Tendsto (fun T : ℝ =>
        (↑T)⁻¹ * ∫ y in (0:ℝ)..T, (Real.sin (y * α) : ℂ) * (Real.sin (y * β) : ℂ))
      atTop (𝓝 0) := by
  have hW := Weyl.trig_time_average (Finset.univ : Finset (Fin 4)) (sinProdFreq α β) sinProdCoeff
  have hrw : ∀ T : ℝ,
      (∫ t in (0:ℝ)..T, ∑ i, sinProdCoeff i * Complex.exp (↑(sinProdFreq α β i) * Complex.I * ↑t))
        = ∫ y in (0:ℝ)..T, (Real.sin (y * α) : ℂ) * (Real.sin (y * β) : ℂ) :=
    fun T => intervalIntegral.integral_congr fun t _ => (sin_mul_sin_eq_sum_char α β t).symm
  have hW2 := hW.congr
    (f₂ := fun T : ℝ =>
      (↑T)⁻¹ * ∫ y in (0:ℝ)..T, (Real.sin (y * α) : ℂ) * (Real.sin (y * β) : ℂ))
    (fun T => by rw [hrw T])
  rw [Finset.sum_filter, Fin.sum_univ_four] at hW2
  simp only [sinProdFreq, sinProdCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hW2
  rw [if_neg (sub_ne_zero.mpr hne), if_neg (sub_ne_zero.mpr hne.symm), if_neg hab,
    if_neg (neg_ne_zero.mpr hab)] at hW2
  simpa using hW2

/-- **Mean value of a squared sine.**  For `α ≠ 0`, the Cesàro time average
`T⁻¹∫₀ᵀ sin(yα)² dy` tends to `1/2`: in the product-to-sum expansion the two zero
frequencies each carry coefficient `1/4`, while `±2α ≠ 0` average out. -/
private theorem sin_sq_average_tendsto_half {α : ℝ} (hα : α ≠ 0) :
    Tendsto (fun T : ℝ =>
        (↑T)⁻¹ * ∫ y in (0:ℝ)..T, (Real.sin (y * α) : ℂ) * (Real.sin (y * α) : ℂ))
      atTop (𝓝 (1 / 2)) := by
  have hW := Weyl.trig_time_average (Finset.univ : Finset (Fin 4)) (sinProdFreq α α) sinProdCoeff
  have hrw : ∀ T : ℝ,
      (∫ t in (0:ℝ)..T, ∑ i, sinProdCoeff i * Complex.exp (↑(sinProdFreq α α i) * Complex.I * ↑t))
        = ∫ y in (0:ℝ)..T, (Real.sin (y * α) : ℂ) * (Real.sin (y * α) : ℂ) :=
    fun T => intervalIntegral.integral_congr fun t _ => (sin_mul_sin_eq_sum_char α α t).symm
  have hW2 := hW.congr
    (f₂ := fun T : ℝ =>
      (↑T)⁻¹ * ∫ y in (0:ℝ)..T, (Real.sin (y * α) : ℂ) * (Real.sin (y * α) : ℂ))
    (fun T => by rw [hrw T])
  rw [Finset.sum_filter, Fin.sum_univ_four] at hW2
  simp only [sinProdFreq, sinProdCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hW2
  have h2 : α + α ≠ 0 := fun h => hα (by linarith)
  rw [if_pos (sub_self α), if_neg h2, if_neg (neg_ne_zero.mpr h2)] at hW2
  rw [show (1 / 4 : ℂ) + 1 / 4 + 0 + 0 = 1 / 2 by norm_num] at hW2
  exact hW2

/-- **Injectivity of `log` across the coefficient index.**  For `m ≥ 2` and `n ≠ m`,
`log m ≠ log n`: on positive integers the logarithm is strictly monotone, and `log 0 = 0`
is separated from `log m > 0`. -/
private theorem log_ne_log_of_ne {m n : ℕ} (hm : 2 ≤ m) (hne : n ≠ m) :
    Real.log m ≠ Real.log n := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rcases Nat.lt_or_ge n m with h | h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, Real.log_zero]
      exact (Real.log_pos (Nat.one_lt_cast.mpr (by omega))).ne'
    · exact (Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast h)).ne'
  · have h' : m < n := lt_of_le_of_ne h (Ne.symm hne)
    exact (Real.log_lt_log hmpos (by exact_mod_cast h')).ne

/-- **Vanishing sine series have zero coefficients (mean-value orthogonality).**
If `∑ ‖bₙ‖ < ∞` and the sine series `∑ bₙ sin(y log n)` vanishes for every real `y`, then
`bₘ = 0` for all `m ≥ 2`.  Mechanism: the Cesàro average
`T⁻¹∫₀ᵀ sin(y log m)·(∑ bₙ sin(y log n)) dy` is identically zero because the inner sum is;
interchanging integral and sum (absolute convergence on a finite interval) and letting
`T → ∞` term by term (dominated convergence with the summable bound `‖bₙ‖`, each cross
average bounded by `1`), the same quantity tends to `bₘ/2` — the diagonal survives with mean
`1/2` while distinct frequencies `log n ≠ log m` average out. -/
theorem sine_series_coeffs_zero {b : ℕ → ℂ} (hsum : Summable fun n => ‖b n‖)
    (hvan : ∀ y : ℝ, ∑' n, b n * Real.sin (y * Real.log n) = 0) :
    ∀ m, 2 ≤ m → b m = 0 := by
  intro m hm
  have hm1 : (1:ℝ) < (m:ℝ) := Nat.one_lt_cast.mpr (by omega)
  have hlam_pos : 0 < Real.log m := Real.log_pos hm1
  -- Step 1: the averaged series vanishes for every window length `T ≥ 0`.
  have hzero : ∀ T : ℝ, 0 ≤ T →
      (∑' n, b n * ((↑T)⁻¹ * ∫ y in (0:ℝ)..T,
        (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ))) = 0 := by
    intro T hT
    have hcont : ∀ n : ℕ, Continuous fun y : ℝ =>
        (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ)) := by
      intro n; fun_prop
    have hle : ∀ n : ℕ, ∀ y : ℝ,
        ‖(Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ))‖ ≤ ‖b n‖ := by
      intro n y
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      calc |Real.sin (y * Real.log m)| * (‖b n‖ * |Real.sin (y * Real.log n)|)
          ≤ 1 * (‖b n‖ * 1) := by
            have h1 := Real.abs_sin_le_one (y * Real.log m)
            have h2 := Real.abs_sin_le_one (y * Real.log n)
            gcongr
        _ = ‖b n‖ := by ring
    have hIocVol : volume.real (Set.Ioc (0:ℝ) T) = T := by
      rw [Real.volume_real_Ioc, sub_zero, max_eq_left hT]
    -- interchange of sum and integral over the finite window
    have hInterchange : (∑' n : ℕ, ∫ y in Set.Ioc (0:ℝ) T,
        (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ)))
        = ∫ y in Set.Ioc (0:ℝ) T, ∑' n : ℕ,
        (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ)) := by
      refine MeasureTheory.integral_tsum_of_summable_integral_norm (fun n => ?_) ?_
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
          ((hcont n).intervalIntegrable 0 T)
      · refine Summable.of_nonneg_of_le
          (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_) (hsum.mul_right T)
        calc (∫ y in Set.Ioc (0:ℝ) T,
              ‖(Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ))‖)
            ≤ |∫ y in Set.Ioc (0:ℝ) T,
              ‖(Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ))‖| :=
              le_abs_self _
          _ = ‖∫ y in Set.Ioc (0:ℝ) T,
              ‖(Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ))‖‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖b n‖ * volume.real (Set.Ioc (0:ℝ) T) :=
              norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top (fun y _ => by
                rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hle n y)
          _ = ‖b n‖ * T := by rw [hIocVol]
    -- the integrand of the interchanged integral is identically zero
    have hInner : ∀ y : ℝ, (∑' n : ℕ,
        (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ))) = 0 := by
      intro y
      rw [tsum_mul_left, hvan y, mul_zero]
    have hRight : (∫ y in Set.Ioc (0:ℝ) T, ∑' n : ℕ,
        (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ))) = 0 := by
      rw [show (fun y : ℝ => ∑' n : ℕ,
        (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ)))
          = fun _ => (0:ℂ) from funext hInner, integral_zero]
    -- pull the coefficient out of the integral and reassemble
    have hpull : ∀ n : ℕ, (∫ y in (0:ℝ)..T,
        (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ)))
        = b n * ∫ y in (0:ℝ)..T,
          (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ) := by
      intro n
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun y _ => by ring
    have hsum0 : (∑' n : ℕ, ∫ y in (0:ℝ)..T,
        (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ))) = 0 := by
      rw [tsum_congr fun n : ℕ =>
        (intervalIntegral.integral_of_le hT :
          (∫ y in (0:ℝ)..T,
            (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ))) = _),
        hInterchange, hRight]
    calc (∑' n, b n * ((↑T)⁻¹ * ∫ y in (0:ℝ)..T,
          (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ)))
        = ∑' n : ℕ, (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
          (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ)) :=
          tsum_congr fun n => by rw [hpull n]; ring
      _ = (↑T)⁻¹ * ∑' n : ℕ, ∫ y in (0:ℝ)..T,
          (Real.sin (y * Real.log m) : ℂ) * (b n * (Real.sin (y * Real.log n) : ℂ)) :=
          tsum_mul_left
      _ = 0 := by rw [hsum0, mul_zero]
  -- Step 2: term-by-term limit of the averaged series (dominated convergence over `n`).
  have hlim : Tendsto (fun T : ℝ => ∑' n, b n * ((↑T)⁻¹ * ∫ y in (0:ℝ)..T,
      (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ))) atTop
      (𝓝 (∑' n, b n * (if n = m then (1/2 : ℂ) else 0))) := by
    apply tendsto_tsum_of_dominated_convergence hsum
    · intro n
      by_cases hn : n = m
      · rw [hn]
        have := (sin_sq_average_tendsto_half hlam_pos.ne').const_mul (b m)
        simpa using this
      · rw [if_neg hn]
        have hne : Real.log m ≠ Real.log n := log_ne_log_of_ne hm hn
        have hab : Real.log m + Real.log n ≠ 0 := by
          have h0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
          exact (by linarith : (0:ℝ) < Real.log m + Real.log n).ne'
        exact (sin_cross_average_tendsto_zero hne hab).const_mul (b n)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
      intro n
      rw [norm_mul]
      have hbound : ‖(↑T)⁻¹ * ∫ y in (0:ℝ)..T,
          (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ)‖ ≤ 1 := by
        rw [norm_mul]
        have hI : ‖∫ y in (0:ℝ)..T,
            (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ)‖ ≤ 1 * |T - 0| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => ?_
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _)
        rw [one_mul, sub_zero, abs_of_pos hT] at hI
        have hTinv : ‖((T:ℝ) : ℂ)⁻¹‖ = T⁻¹ := by
          rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
        rw [hTinv]
        calc T⁻¹ * ‖∫ y in (0:ℝ)..T,
              (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ)‖
            ≤ T⁻¹ * T := by gcongr
          _ = 1 := inv_mul_cancel₀ hT.ne'
      calc ‖b n‖ * ‖(↑T)⁻¹ * ∫ y in (0:ℝ)..T,
            (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ)‖
          ≤ ‖b n‖ * 1 := by gcongr
        _ = ‖b n‖ := mul_one _
  -- Step 3: the two limits agree, so `bₘ/2 = 0`.
  have h0lim : Tendsto (fun T : ℝ => ∑' n, b n * ((↑T)⁻¹ * ∫ y in (0:ℝ)..T,
      (Real.sin (y * Real.log m) : ℂ) * (Real.sin (y * Real.log n) : ℂ))) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    exact (hzero T hT).symm
  have huniq := tendsto_nhds_unique hlim h0lim
  rw [tsum_eq_single m (fun n hn => by rw [if_neg hn, mul_zero]),
    if_pos rfl] at huniq
  rcases mul_eq_zero.mp huniq with h | h
  · exact h
  · norm_num at h

/-- **Termwise reflection difference on the central line.**  For any coefficient `aₙ` and
real `y`, `aₙ n^{−(½+iy)} − aₙ n^{−(½−iy)} = −2i·(aₙ n^{−½})·sin(y log n)`: the exponential
form of the natural-power `cpow` splits off the modulus `n^{−½}` and leaves the phase
difference `e^{−iy log n} − e^{iy log n} = −2i sin(y log n)`.  The `n = 0` term vanishes on
both sides. -/
private theorem term_sub_reflected (a : ℕ → ℂ) (y : ℝ) (n : ℕ) :
    LSeries.term a ((1/2 : ℂ) + ↑y * Complex.I) n
      - LSeries.term a ((1/2 : ℂ) - ↑y * Complex.I) n
      = (-2 * Complex.I) * ((a n * (n : ℂ) ^ (-(1/2 : ℂ))) * (Real.sin (y * Real.log n) : ℂ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, LSeries.term_zero]
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (by norm_num : -(1/2 : ℂ) ≠ 0)]
    ring
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
    have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
    have hcpow : ∀ w : ℂ, ((n : ℕ) : ℂ) ^ w = Complex.exp (((Real.log n : ℝ) : ℂ) * w) := by
      intro w
      rw [Complex.cpow_def_of_ne_zero hn0, hlog]
    have hdiv : ∀ w : ℂ, a n / ((n : ℕ) : ℂ) ^ w
        = a n * Complex.exp (-(((Real.log n : ℝ) : ℂ) * w)) := by
      intro w
      rw [hcpow w, div_eq_mul_inv, ← Complex.exp_neg]
    rw [hdiv, hdiv, hcpow]
    have e1 : -(((Real.log n : ℝ) : ℂ) * ((1/2 : ℂ) + ↑y * Complex.I))
        = ((Real.log n : ℝ) : ℂ) * (-(1/2 : ℂ))
          + -((y * Real.log n : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have e2 : -(((Real.log n : ℝ) : ℂ) * ((1/2 : ℂ) - ↑y * Complex.I))
        = ((Real.log n : ℝ) : ℂ) * (-(1/2 : ℂ))
          + ((y * Real.log n : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e1, e2, Complex.exp_add, Complex.exp_add, Complex.ofReal_sin]
    have hsin : Complex.exp (-((y * Real.log n : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((y * Real.log n : ℝ) : ℂ) * Complex.I)
        = -2 * Complex.I * Complex.sin ((y * Real.log n : ℝ) : ℂ) := by
      rw [Complex.sin]
      rw [show (-2 : ℂ) * Complex.I
            * ((Complex.exp (-((y * Real.log n : ℝ) : ℂ) * Complex.I)
                - Complex.exp (((y * Real.log n : ℝ) : ℂ) * Complex.I)) * Complex.I / 2)
          = -(Complex.I * Complex.I)
            * (Complex.exp (-((y * Real.log n : ℝ) : ℂ) * Complex.I)
                - Complex.exp (((y * Real.log n : ℝ) : ℂ) * Complex.I)) by ring,
        Complex.I_mul_I]
      ring
    linear_combination
      (a n * Complex.exp (((Real.log n : ℝ) : ℂ) * (-(1/2 : ℂ)))) * hsin

/-- **Overlap rigidity.**  An ordinary Dirichlet series absolutely convergent at the real
point `σ₀ < 1/2` and satisfying the exact reflection symmetry `L(s) = L(1−s)` on the
overlap strip `σ₀ < Re s < 1 − σ₀` has vanishing coefficients for all `n ≥ 2`.  The proof
evaluates the symmetry on the reflection's fixed line `Re s = 1/2`: subtracting the two
absolutely convergent series at `½ ± iy` leaves the sine series
`∑ (aₙ n^{−½}) sin(y log n) = 0` for every real `y` (after cancelling the unit `−2i`), and
mean-value orthogonality of the distinct frequencies `log n` kills each coefficient. -/
theorem overlap_rigidity {a : ℕ → ℂ} {σ₀ : ℝ} (hσ : σ₀ < 1/2)
    (hsum : LSeriesSummable a σ₀)
    (hsym : ∀ s : ℂ, σ₀ < s.re → s.re < 1 - σ₀ → LSeries a s = LSeries a (1 - s)) :
    ∀ n, 2 ≤ n → a n = 0 := by
  -- absolute convergence of the central-line coefficients `aₙ n^{−½}`
  have hb_sum : Summable fun n : ℕ => ‖a n * (n : ℂ) ^ (-(1/2 : ℂ))‖ := by
    have hhalf : LSeriesSummable a (((1:ℝ)/2 : ℝ) : ℂ) :=
      hsum.of_re_le_re (by rw [Complex.ofReal_re, Complex.ofReal_re]; linarith)
    have hnorm : Summable fun n => ‖LSeries.term a (((1:ℝ)/2 : ℝ) : ℂ) n‖ :=
      summable_norm_iff.mpr hhalf
    refine hnorm.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero, norm_zero, Nat.cast_zero]
      rw [Complex.zero_cpow (by norm_num : -(1/2 : ℂ) ≠ 0), mul_zero, norm_zero]
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.norm_term_eq, if_neg hn, norm_mul,
        Complex.norm_natCast_cpow_of_pos hn0, Complex.ofReal_re,
        show (-(1/2 : ℂ)).re = -((1:ℝ)/2) by simp,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  -- the sine series vanishes identically on the fixed line
  have hvan : ∀ y : ℝ,
      ∑' n, (a n * (n : ℂ) ^ (-(1/2 : ℂ))) * (Real.sin (y * Real.log n) : ℂ) = 0 := by
    intro y
    have hre1 : ((1/2 : ℂ) + ↑y * Complex.I).re = 1/2 := by simp
    have hre2 : ((1/2 : ℂ) - ↑y * Complex.I).re = 1/2 := by simp
    have hs1 : LSeriesSummable a ((1/2 : ℂ) + ↑y * Complex.I) :=
      hsum.of_re_le_re (by rw [Complex.ofReal_re, hre1]; linarith)
    have hs2 : LSeriesSummable a ((1/2 : ℂ) - ↑y * Complex.I) :=
      hsum.of_re_le_re (by rw [Complex.ofReal_re, hre2]; linarith)
    have hsymy : LSeries a ((1/2 : ℂ) + ↑y * Complex.I)
        = LSeries a ((1/2 : ℂ) - ↑y * Complex.I) := by
      have h := hsym ((1/2 : ℂ) + ↑y * Complex.I) (by rw [hre1]; linarith)
        (by rw [hre1]; linarith)
      rwa [show (1:ℂ) - ((1/2 : ℂ) + ↑y * Complex.I) = (1/2 : ℂ) - ↑y * Complex.I by ring] at h
    have h1 : Summable (LSeries.term a ((1/2 : ℂ) + ↑y * Complex.I)) := hs1
    have h2 : Summable (LSeries.term a ((1/2 : ℂ) - ↑y * Complex.I)) := hs2
    have hsub : (∑' n, (LSeries.term a ((1/2 : ℂ) + ↑y * Complex.I) n
        - LSeries.term a ((1/2 : ℂ) - ↑y * Complex.I) n)) = 0 := by
      rw [Summable.tsum_sub h1 h2,
        show (∑' n, LSeries.term a ((1/2 : ℂ) + ↑y * Complex.I) n)
          = LSeries a ((1/2 : ℂ) + ↑y * Complex.I) from rfl,
        show (∑' n, LSeries.term a ((1/2 : ℂ) - ↑y * Complex.I) n)
          = LSeries a ((1/2 : ℂ) - ↑y * Complex.I) from rfl,
        hsymy, sub_self]
    rw [tsum_congr (term_sub_reflected a y), tsum_mul_left] at hsub
    exact (mul_eq_zero.mp hsub).resolve_left
      (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  intro n hn
  have hbz := sine_series_coeffs_zero hb_sum hvan n hn
  have hnz : ((n : ℂ) ^ (-(1/2 : ℂ))) ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
    exact (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _).ne'
  exact (mul_eq_zero.mp hbz).resolve_right hnz

/-- **Support collapse.**  A normalized exactly-symmetric Dirichlet series (`a 0 = 0`,
`a 1 = 1`) that converges absolutely past the reflection center is the constant `1` on its
half-plane of convergence: every coefficient `n ≥ 2` vanishes by overlap rigidity, so the
series is its single `n = 1` term. -/
theorem overlap_rigidity_lseries_eq_one {a : ℕ → ℂ} {σ₀ : ℝ} (hσ : σ₀ < 1/2)
    (h1 : a 1 = 1) (h0 : a 0 = 0) (hsum : LSeriesSummable a σ₀)
    (hsym : ∀ s : ℂ, σ₀ < s.re → s.re < 1 - σ₀ → LSeries a s = LSeries a (1 - s)) :
    ∀ s : ℂ, σ₀ < s.re → LSeries a s = 1 := by
  have hcoeff : ∀ n : ℕ, n ≠ 1 → a n = 0 := by
    intro n hn
    match n, hn with
    | 0, _ => exact h0
    | 1, hn => exact absurd rfl hn
    | (k + 2), _ => exact overlap_rigidity hσ hsum hsym (k + 2) (by omega)
  intro s _
  have hterm : ∀ n : ℕ, n ≠ 1 → LSeries.term a s n = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · exact LSeries.term_zero a s
    · rw [LSeries.term_of_ne_zero hn0, hcoeff n hn, zero_div]
  rw [show LSeries a s = ∑' n, LSeries.term a s n from rfl,
    tsum_eq_single 1 hterm, LSeries.term_of_ne_zero one_ne_zero, h1,
    Nat.cast_one, Complex.one_cpow, div_one]

end RHTower
