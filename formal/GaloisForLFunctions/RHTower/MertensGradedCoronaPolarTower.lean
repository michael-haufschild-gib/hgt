import GaloisForLFunctions.RHTower.PrimeLogPowZetaAbelPole
import GaloisForLFunctions.RHTower.MertensCoronaTimeOneResidue
import GaloisForLFunctions.RHTower.MertensGradedCoronaTower

/-!
# The time-one differentiated polar tower of the graded Mertens corona

The time-one Gamma--Meixner weight is `w_1(p) = cosh(2 log p)^{-1/2} = √2 p^{-1}(1+p^{-4})^{-1/2}`,
and the degree-`k` source of the graded corona is `u_k(p) = (log p)^k`.  Its time-one
prime--Laplace transform

```text
F_k(s) = ∑_p w_1(p)(log p)^{k+1} p^{-s}
```

has the exact principal part `√2 k!/s^{k+1}` at the source boundary: the correction factor
`(1+p^{-4})^{-1/2} - 1` is `O(p^{-4})`, hence contributes a bounded Dirichlet series, while the
bare graded prime log-zeta function carries the pole
`lim_{s ↓ 0} s^{k+1} ∑_p (log p)^{k+1} p^{-1-s} = k!`.

The transform intertwines the two source operators exactly: the logarithmic clock is minus the
`s`-derivative, and a positive Euler translation is a shift of `s`.  Under the local reflection
`s ↦ -s` the principal symbol `s^{-(k+1)}` has parity `(-1)^{k+1}`.
-/

open Filter MeasureTheory Set Topology

open scoped Topology

namespace RHTower

noncomputable section

/-! ## The graded time-one source -/

theorem abelWeighted_gradeSource (k : ℕ) (s : ℝ) (n : ℕ) :
    abelWeighted (gradeSource k) s n = primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s) := by
  rw [abelWeighted, gradeSource]
  by_cases hp : n.Prime
  · rw [mertensPrimeWeight, if_pos hp, primeLogPowWeight, if_pos hp]
    ring
  · rw [mertensPrimeWeight, if_neg hp, primeLogPowWeight, if_neg hp]
    ring

/-- **Equations (23)--(24).**  The graded time-one prime--Laplace source. -/
theorem timeOnePrimeLaplace_gradeSource_eq (k : ℕ) (s : ℝ) :
    timeOnePrimeLaplace (gradeSource k) s
      = Real.sqrt 2 * ∑' n : ℕ, timeOneCorrection n
          * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s)) := by
  rw [timeOnePrimeLaplace_eq]
  congr 1
  exact tsum_congr fun n => by rw [abelWeighted_gradeSource]

theorem summable_timeOneCorrection_primeLogPowWeight (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable fun n : ℕ =>
      timeOneCorrection n * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s)) := by
  refine (summable_primeLogPowWeight_rpow k hs).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (timeOneCorrection_pos n).le
      (mul_nonneg (primeLogPowWeight_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · have hnn : (0 : ℝ) ≤ primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s) :=
      mul_nonneg (primeLogPowWeight_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    nlinarith [timeOneCorrection_le_one n, hnn]

/-- The bounded defect of the time-one correction against the bare graded prime log-zeta. -/
theorem abs_gradedTimeOneDefect_le (k : ℕ) {s : ℝ} (hs : 0 < s) :
    |(∑' n : ℕ, timeOneCorrection n * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s)))
        - gradedPrimeLogZeta k s|
      ≤ ∑' n : ℕ, primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-(4 : ℝ)) := by
  have h4 : Summable fun n : ℕ => primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-(4 : ℝ)) :=
    summable_primeLogPowWeight_rpow k (by norm_num)
  have hs' := summable_primeLogPowWeight_rpow k hs
  have hcorr := summable_timeOneCorrection_primeLogPowWeight k hs
  have hterm : ∀ n : ℕ,
      ‖(timeOneCorrection n - 1) * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s))‖
        ≤ primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-(4 : ℝ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [primeLogPowWeight_zero_index]
      simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hw : 0 ≤ primeLogPowWeight (k + 1) n := primeLogPowWeight_nonneg _ _
      have hrs : (n : ℝ) ^ (-s) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
      have hrs0 : (0 : ℝ) ≤ (n : ℝ) ^ (-s) := Real.rpow_nonneg (by linarith) _
      have hr4 : (0 : ℝ) ≤ (n : ℝ) ^ (-(4 : ℝ)) := Real.rpow_nonneg (by linarith) _
      have hc := abs_timeOneCorrection_sub_one_le n
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hrs0]
      calc |timeOneCorrection n - 1| * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s))
          ≤ (n : ℝ) ^ (-(4 : ℝ)) * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s)) :=
            mul_le_mul_of_nonneg_right hc (mul_nonneg hw hrs0)
        _ ≤ (n : ℝ) ^ (-(4 : ℝ)) * (primeLogPowWeight (k + 1) n * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrs hw) hr4
        _ = primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-(4 : ℝ)) := by ring
  have hnorm : Summable fun n : ℕ =>
      ‖(timeOneCorrection n - 1) * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s))‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm h4
  have hdiff : (∑' n : ℕ, timeOneCorrection n * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s)))
      - gradedPrimeLogZeta k s
      = ∑' n : ℕ, (timeOneCorrection n - 1) * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s)) := by
    rw [gradedPrimeLogZeta, ← hcorr.tsum_sub hs']
    exact tsum_congr fun n => by ring
  rw [hdiff, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hterm hnorm h4)

theorem timeOnePrimeLaplace_gradeSource_eq' (k : ℕ) (s : ℝ) :
    timeOnePrimeLaplace (gradeSource k) s
      = Real.sqrt 2 * ∑' n : ℕ, (timeOneCorrection n * primeLogPowWeight (k + 1) n)
          * (n : ℝ) ^ (-s) := by
  rw [timeOnePrimeLaplace_gradeSource_eq]
  congr 1
  exact tsum_congr fun n => (mul_assoc _ _ _).symm

theorem primeLogPowWeight_mul_log (k n : ℕ) :
    primeLogPowWeight k n * Real.log n = primeLogPowWeight (k + 1) n := by
  by_cases hp : n.Prime
  · rw [primeLogPowWeight, primeLogPowWeight, if_pos hp, if_pos hp]
    ring
  · rw [primeLogPowWeight, primeLogPowWeight, if_neg hp, if_neg hp]
    ring

/-- **Equations (25)--(27).**  The exact principal part of the graded time-one source:
`lim_{s ↓ 0} s^{k+1} F_k(s) = √2 · k!`. -/
theorem tendsto_gradedTimeOnePrimeLaplace (k : ℕ) :
    Tendsto (fun s : ℝ => s ^ (k + 1) * timeOnePrimeLaplace (gradeSource k) s)
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.sqrt 2 * (Nat.factorial k : ℝ))) := by
  set D : ℝ := ∑' n : ℕ, primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-(4 : ℝ)) with hD
  have hD0 : 0 ≤ D := tsum_nonneg fun n =>
    mul_nonneg (primeLogPowWeight_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hdefect : Tendsto (fun s : ℝ => s ^ (k + 1)
      * (Real.sqrt 2 * ((∑' n : ℕ, timeOneCorrection n
          * (primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-s))) - gradedPrimeLogZeta k s)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hmaj : Tendsto (fun s : ℝ => s ^ (k + 1) * (Real.sqrt 2 * D))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hcont : Tendsto (fun s : ℝ => s ^ (k + 1) * (Real.sqrt 2 * D)) (nhds 0)
          (nhds ((0 : ℝ) ^ (k + 1) * (Real.sqrt 2 * D))) :=
        ((continuous_pow (k + 1)).mul continuous_const).tendsto 0
      rw [zero_pow (by omega), zero_mul] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : (0 : ℝ) < s := hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ (k + 1)),
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (abs_gradedTimeOneDefect_le k hspos) (Real.sqrt_nonneg 2))
      (by positivity)
  have hmain := (tendsto_gradedPrimeLogZeta k).const_mul (Real.sqrt 2)
  have hsum := hmain.add hdefect
  rw [add_zero] at hsum
  refine hsum.congr fun s => ?_
  rw [timeOnePrimeLaplace_gradeSource_eq]
  ring

/-- **Equation (28), the logarithmic clock.**  The time-one transform carries the logarithmic
clock to minus the boundary derivative. -/
theorem hasDerivAt_timeOnePrimeLaplace_gradeSource (k : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ : ℝ => timeOnePrimeLaplace (gradeSource k) σ)
      (-timeOnePrimeLaplace (gradeSource (k + 1)) s) s := by
  set c : ℕ → ℝ := fun n => timeOneCorrection n * primeLogPowWeight (k + 1) n with hcdef
  have hc0 : c 0 = 0 := by
    rw [hcdef]
    simp only
    rw [primeLogPowWeight_zero_index, mul_zero]
  have hcnn : ∀ n, 0 ≤ c n := fun n =>
    mul_nonneg (timeOneCorrection_pos n).le (primeLogPowWeight_nonneg _ _)
  have hu : Summable fun n : ℕ =>
      timeOneCorrection n * (primeLogPowWeight (k + 2) n * (n : ℝ) ^ (-(s / 2))) :=
    summable_timeOneCorrection_primeLogPowWeight (k + 1) (by linarith)
  have hderiv : ∀ n : ℕ, ∀ y ∈ Ioi (s / 2),
      HasDerivAt (fun σ : ℝ => c n * (n : ℝ) ^ (-σ))
        (c n * (Real.log n * (-1) * (n : ℝ) ^ (-y))) y := by
    intro n y _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hc0]
      simp only [zero_mul]
      exact hasDerivAt_const _ _
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact (((hasDerivAt_id y).neg).const_rpow hn0).const_mul (c n)
  have hbound : ∀ n : ℕ, ∀ y ∈ Ioi (s / 2),
      ‖c n * (Real.log n * (-1) * (n : ℝ) ^ (-y))‖
        ≤ timeOneCorrection n * (primeLogPowWeight (k + 2) n * (n : ℝ) ^ (-(s / 2))) := by
    intro n y hy
    have hy' : s / 2 < y := hy
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hc0]
      simp only [zero_mul, norm_zero]
      exact mul_nonneg (timeOneCorrection_pos 0).le
        (mul_nonneg (primeLogPowWeight_nonneg _ _) (Real.rpow_nonneg (by norm_num) _))
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      have hmono : (n : ℝ) ^ (-y) ≤ (n : ℝ) ^ (-(s / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-y) := Real.rpow_nonneg (by linarith) _
      have hkey : c n * Real.log n = timeOneCorrection n * primeLogPowWeight (k + 2) n := by
        rw [hcdef]
        simp only
        rw [mul_assoc, primeLogPowWeight_mul_log]
      rw [Real.norm_eq_abs, show c n * (Real.log n * (-1) * (n : ℝ) ^ (-y))
          = -((c n * Real.log n) * (n : ℝ) ^ (-y)) by ring, abs_neg, abs_mul, hkey,
        abs_of_nonneg (mul_nonneg (timeOneCorrection_pos n).le (primeLogPowWeight_nonneg _ _)),
        abs_of_nonneg hnn, ← mul_assoc]
      refine mul_le_mul_of_nonneg_left hmono ?_
      exact mul_nonneg (timeOneCorrection_pos n).le (primeLogPowWeight_nonneg _ _)
  have hmem : s ∈ Ioi (s / 2) := by
    simp only [mem_Ioi]
    linarith
  have hf0 : Summable fun n : ℕ => c n * (n : ℝ) ^ (-s) := by
    have := summable_timeOneCorrection_primeLogPowWeight k hs
    refine this.congr fun n => ?_
    rw [hcdef]
    simp only
    ring
  have hD := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hderiv hbound
    hmem hf0 hmem
  have hfun : (fun σ : ℝ => timeOnePrimeLaplace (gradeSource k) σ)
      = fun σ : ℝ => Real.sqrt 2 * ∑' n : ℕ, c n * (n : ℝ) ^ (-σ) := by
    funext σ
    rw [timeOnePrimeLaplace_gradeSource_eq' k σ]
  rw [hfun]
  have hval : Real.sqrt 2 * ∑' n : ℕ, c n * (Real.log n * (-1) * (n : ℝ) ^ (-s))
      = -timeOnePrimeLaplace (gradeSource (k + 1)) s := by
    rw [timeOnePrimeLaplace_gradeSource_eq' (k + 1) s, ← mul_neg]
    congr 1
    rw [← tsum_neg]
    refine tsum_congr fun n => ?_
    have hkey : c n * Real.log n = timeOneCorrection n * primeLogPowWeight (k + 1 + 1) n := by
      rw [hcdef]
      simp only
      rw [mul_assoc, primeLogPowWeight_mul_log]
    calc c n * (Real.log n * (-1) * (n : ℝ) ^ (-s))
        = -((c n * Real.log n) * (n : ℝ) ^ (-s)) := by ring
      _ = -(timeOneCorrection n * primeLogPowWeight (k + 1 + 1) n * (n : ℝ) ^ (-s)) := by
          rw [hkey]
  rw [← hval]
  exact hD.const_mul (Real.sqrt 2)

/-- **Equation (28), the Euler translation.**  A positive Euler translation of the source is a
shift of the boundary variable. -/
theorem timeOnePrimeLaplace_gradeSource_shift (k : ℕ) (h s : ℝ) :
    timeOnePrimeLaplace (fun n : ℕ => gradeSource k n * (n : ℝ) ^ (-h)) s
      = timeOnePrimeLaplace (gradeSource k) (s + h) := by
  rw [timeOnePrimeLaplace, timeOnePrimeLaplace]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mertensPrimeWeight]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsplit : (n : ℝ) ^ (-h) * (n : ℝ) ^ (-s) = (n : ℝ) ^ (-(s + h)) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    calc meixnerShape 1 n * ((n : ℝ) * mertensPrimeWeight n)
          * (gradeSource k n * (n : ℝ) ^ (-h)) * (n : ℝ) ^ (-s)
        = (meixnerShape 1 n * ((n : ℝ) * mertensPrimeWeight n) * gradeSource k n)
            * ((n : ℝ) ^ (-h) * (n : ℝ) ^ (-s)) := by ring
      _ = meixnerShape 1 n * ((n : ℝ) * mertensPrimeWeight n) * gradeSource k n
            * (n : ℝ) ^ (-(s + h)) := by rw [hsplit]

/-- **Equation (29).**  Under the local reflection `s ↦ -s` the principal symbol `s^{-(k+1)}`
has parity `(-1)^{k+1}`. -/
theorem principalPart_reflection (k : ℕ) (c s : ℝ) :
    c / (-s) ^ (k + 1) = (-1) ^ (k + 1) * (c / s ^ (k + 1)) := by
  have hpm : ((-1 : ℝ) ^ (k + 1)) * ((-1 : ℝ) ^ (k + 1)) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [neg_pow, show ((-1 : ℝ) ^ (k + 1) * s ^ (k + 1)) = s ^ (k + 1) * (-1 : ℝ) ^ (k + 1) by ring,
    ← div_div, div_eq_mul_inv (c / s ^ (k + 1)) ((-1 : ℝ) ^ (k + 1)),
    inv_eq_of_mul_eq_one_right hpm]
  ring

end

end RHTower
