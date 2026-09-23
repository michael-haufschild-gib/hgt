import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzLattice

/-!
# Rapid decay of a dilated Schwartz lattice sum

Appendix I (46) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The size of the periodization `E(f)(λx)` for `|λ| → ∞` is controlled by the punctured lattice
sum `∑_{n ≠ 0} |f_1(λ x_∞ n)|` of the archimedean factor.  Because `f_1` is Schwartz, the
`m`-th Schwartz seminorm bounds each term by `S/(λ c |n|)^m`, so the whole sum is
`O(λ^{-m})`: the periodization decays faster than every power of `|λ|`.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The punctured lattice sum of the moduli of a dilated Schwartz function. -/
def connesLatticeSum (f : SchwartzMap ℝ ℂ) (a : ℝ) : ℝ :=
  ∑' n : ℤ, (if n = 0 then 0 else ‖f (a * (n : ℝ))‖)

theorem connes_latticeSum_summable (f : SchwartzMap ℝ ℂ) {a : ℝ} (ha : a ≠ 0) :
    Summable fun n : ℤ => (if n = 0 then 0 else ‖f (a * (n : ℝ))‖) := by
  refine (ccmRationalArchimedeanSchwartz_lattice_summable f ha).of_nonneg_of_le
    (fun n => ?_) (fun n => ?_)
  · by_cases h : n = 0 <;> simp [h]
  · by_cases h : n = 0 <;> simp [h, norm_nonneg]

theorem connes_latticeSum_nonneg (f : SchwartzMap ℝ ℂ) (a : ℝ) :
    0 ≤ connesLatticeSum f a := by
  refine tsum_nonneg fun n => ?_
  by_cases h : n = 0 <;> simp [h, norm_nonneg]

/-- **Appendix I (46).**  The punctured Schwartz lattice sum decays faster than every power of
the dilation parameter. -/
theorem connes_latticeSum_rapidDecay (f : SchwartzMap ℝ ℂ) {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun lam : ℝ => lam ^ k * connesLatticeSum f (lam * c)) atTop (𝓝 0) := by
  set m : ℕ := 2 * k + 2 with hm
  set S : ℝ := SchwartzMap.seminorm ℂ m 0 f with hS
  have hS0 : (0 : ℝ) ≤ S := apply_nonneg _ f
  have hpowm : ∀ n : ℤ, (0 : ℝ) ≤ (n : ℝ) ^ m := by
    intro n
    have he : (n : ℝ) ^ m = ((n : ℝ) ^ (k + 1)) ^ (2 : ℕ) := by
      rw [← pow_mul]; congr 1; omega
    rw [he]; positivity
  have hZsummable : Summable fun n : ℤ => (if n = 0 then 0 else 1 / ((n : ℝ) ^ m)) := by
    refine ((Real.summable_one_div_int_pow (p := m)).2 (by omega)).of_nonneg_of_le
      (fun n => ?_) (fun n => ?_)
    · by_cases h : n = 0
      · simp [h]
      · simp only [if_neg h, one_div]
        exact inv_nonneg.mpr (hpowm n)
    · by_cases h : n = 0
      · simp [h]
      · simp only [if_neg h, le_refl]
  set Z : ℝ := ∑' n : ℤ, (if n = 0 then 0 else 1 / ((n : ℝ) ^ m)) with hZ
  have hZ0 : 0 ≤ Z := by
    refine tsum_nonneg fun n => ?_
    by_cases h : n = 0
    · simp [h]
    · simp only [if_neg h, one_div]
      exact inv_nonneg.mpr (hpowm n)
  set K : ℝ := S * Z / c ^ m with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) < c ^ m := by positivity
    positivity
  -- the pointwise majorant
  have hmaj : ∀ lam : ℝ, 1 ≤ lam →
      lam ^ k * connesLatticeSum f (lam * c) ≤ K * (1 / lam ^ (k + 2)) := by
    intro lam hlam
    have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
    have hac : (lam * c) ≠ 0 := by positivity
    have hterm : ∀ n : ℤ, (if n = 0 then 0 else ‖f (lam * c * (n : ℝ))‖)
        ≤ (S / (lam * c) ^ m) * (if n = 0 then 0 else 1 / ((n : ℝ) ^ m)) := by
      intro n
      by_cases h : n = 0
      · simp [h]
      · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h
        have hx : (0 : ℝ) < ‖lam * c * (n : ℝ)‖ ^ m := by
          refine pow_pos (norm_pos_iff.mpr ?_) _
          exact mul_ne_zero hac hn
        have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ f m (lam * c * (n : ℝ))
        have hle : ‖f (lam * c * (n : ℝ))‖ ≤ S / ‖lam * c * (n : ℝ)‖ ^ m := by
          rw [le_div_iff₀ hx]
          simpa [hS, mul_comm] using hsem
        have hnorm : ‖lam * c * (n : ℝ)‖ ^ m = (lam * c) ^ m * (n : ℝ) ^ m := by
          rw [Real.norm_eq_abs, abs_mul, mul_pow, abs_of_pos (by positivity : (0:ℝ) < lam * c)]
          congr 1
          have : |(n : ℝ)| ^ m = ((|(n : ℝ)|) ^ (k + 1)) ^ (2 : ℕ) := by
            rw [← pow_mul]; congr 1; omega
          rw [this, ← pow_mul]
          rw [show (k + 1) * 2 = m by omega, ← abs_pow, abs_of_nonneg]
          have h2 : (n : ℝ) ^ m = ((n : ℝ) ^ (k + 1)) ^ (2 : ℕ) := by
            rw [← pow_mul]; congr 1; omega
          rw [h2]
          positivity
        simp only [if_neg h]
        rw [hnorm] at hle
        refine le_trans hle (le_of_eq ?_)
        field_simp
    have hsum1 := connes_latticeSum_summable f hac
    have hsum2 := hZsummable.mul_left (S / (lam * c) ^ m)
    have hcmp : connesLatticeSum f (lam * c) ≤ (S / (lam * c) ^ m) * Z := by
      rw [connesLatticeSum, hZ, ← tsum_mul_left]
      exact hsum1.tsum_le_tsum hterm hsum2
    have hlamk : (0 : ℝ) ≤ lam ^ k := by positivity
    calc lam ^ k * connesLatticeSum f (lam * c)
        ≤ lam ^ k * ((S / (lam * c) ^ m) * Z) := mul_le_mul_of_nonneg_left hcmp hlamk
      _ = K * (1 / lam ^ (k + 2)) := by
          rw [hK, hm]
          field_simp
          ring
  have hgoal : Tendsto (fun lam : ℝ => K * (1 / lam ^ (k + 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun lam : ℝ => lam ^ (k + 2)) atTop atTop :=
      tendsto_pow_atTop (by omega)
    have h2 : Tendsto (fun lam : ℝ => 1 / lam ^ (k + 2)) atTop (𝓝 0) := by
      have h3 := h1.inv_tendsto_atTop
      simpa [one_div, Pi.inv_def] using h3
    simpa using h2.const_mul K
  refine squeeze_zero' ?_ ?_ hgoal
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with lam hlam
    have : (0 : ℝ) ≤ lam ^ k := by positivity
    exact mul_nonneg this (connes_latticeSum_nonneg f _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with lam hlam
    exact hmaj lam hlam

end

end GaloisForLFunctions.RHTower
