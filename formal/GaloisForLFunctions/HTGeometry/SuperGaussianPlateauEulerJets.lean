import GaloisForLFunctions.HTGeometry.SuperGaussianMonomialization
import GaloisForLFunctions.HTGeometry.StrelitzLogJetDefs
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# Euler jets on a geometrically separated circle

Suppose that on the circle `|z| = t` every Taylor term of `f = Σ a_m z^m` is dominated by the
`n`-th one with the geometric separation `‖a_m‖ t^m ≤ q^{|m-n|} ‖a_n‖ t^n`, where `q ≤ 1/32`.
Then, uniformly on the circle,

* `|f(z)| ≥ ‖a_n‖ t^n / 2`;
* `|z f'(z)/f(z) - n| ≤ 32 q`;
* `|z (z f'/f)'(z)| ≤ 64 q`.

The index-deviation series `G₁ = Σ (m-n) a_m z^m` and `G₂ = Σ (m-n)² a_m z^m` carry the estimates
through the exact identities `u = n + G₁/f` and `v = (G₂ f - G₁²)/f²`.  All errors are absolute:
they do not grow with the dominant index `n`.  The separation holds at the midpoint of every
central-index plateau (`term_le_midplateau`).
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

variable {a : ℕ → ℂ}

/-- The two-sided geometric weight `ω^{|i-k|}` is summable. -/
theorem summable_pow_idxDist {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω < 1) (k : ℕ) :
    Summable (fun i : ℕ => ω ^ idxDist i k) := by
  rw [← summable_nat_add_iff (k + 1)]
  refine ((summable_geometric_of_lt_one h0 h1).mul_left ω).congr fun j => ?_
  rw [idxDist_eq_sub_of_le (by omega), show j + (k + 1) - k = j + 1 by omega, pow_succ]
  ring

/-- The punctured two-sided geometric weight sums to at most `4ω` when `ω ≤ 1/2`. -/
theorem tsum_ite_pow_idxDist_le {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1 / 2) (k : ℕ) :
    ∑' i : ℕ, (if i = k then (0 : ℝ) else ω ^ idxDist i k) ≤ 4 * ω := by
  set g : ℕ → ℝ := fun i => if i = k then 0 else ω ^ idxDist i k with hg
  have hω1 : ω < 1 := by linarith
  have hshift : ∀ j : ℕ, g (j + (k + 1)) = ω * ω ^ j := by
    intro j
    simp only [hg]
    rw [if_neg (by omega), idxDist_eq_sub_of_le (by omega),
      show j + (k + 1) - k = j + 1 by omega, pow_succ]
    ring
  have hgeo : Summable (fun j : ℕ => ω * ω ^ j) :=
    (summable_geometric_of_lt_one h0 hω1).mul_left ω
  have hsum : Summable g := by
    rw [← summable_nat_add_iff (k + 1)]
    exact hgeo.congr fun j => (hshift j).symm
  have hsplit := hsum.sum_add_tsum_nat_add (k + 1)
  have hgeo_sum : ∑' j : ℕ, ω * ω ^ j = ω * (1 - ω)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one h0 hω1]
  have htail : ∑' j : ℕ, g (j + (k + 1)) = ω * (1 - ω)⁻¹ := by
    rw [tsum_congr hshift, hgeo_sum]
  have hhead : ∑ i ∈ Finset.range (k + 1), g i ≤ ω * (1 - ω)⁻¹ := by
    rw [Finset.sum_range_succ]
    have hgk : g k = 0 := by simp [hg]
    rw [hgk, add_zero]
    have hrefl : ∑ i ∈ Finset.range k, g i = ∑ j ∈ Finset.range k, ω * ω ^ j := by
      rw [← Finset.sum_range_reflect (fun j => ω * ω ^ j) k]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i < k := Finset.mem_range.mp hi
      simp only [hg]
      rw [if_neg (by omega), idxDist_eq_sub_of_ge hik.le,
        show k - i = (k - 1 - i) + 1 by omega, pow_succ]
      ring
    rw [hrefl, ← hgeo_sum]
    exact hgeo.sum_le_tsum _ fun j _ => by positivity
  have hinv : ω * (1 - ω)⁻¹ ≤ 2 * ω := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith
  rw [← hsplit]
  linarith

/-- Polynomial weights up to degree two are absorbed by quadrupling the geometric ratio. -/
theorem natCast_pow_mul_pow_le_four_mul_pow {q : ℝ} (hq : 0 ≤ q) (d : ℕ) {p : ℕ}
    (hp : p ≤ 2) : (d : ℝ) ^ p * q ^ d ≤ (4 * q) ^ d := by
  have hd2 : (d : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
  have hdp : (d : ℝ) ^ p ≤ 4 ^ d := by
    interval_cases p
    · rw [pow_zero]
      exact one_le_pow₀ (by norm_num)
    · calc (d : ℝ) ^ 1 = d := pow_one _
        _ ≤ 2 ^ d := hd2
        _ ≤ 4 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    · calc (d : ℝ) ^ 2 ≤ (2 ^ d) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg d) hd2 2
        _ = 4 ^ d := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hdp (pow_nonneg hq d)

/-- The distance of two natural numbers, read in `ℂ`. -/
theorem norm_natCast_sub_natCast_eq_idxDist (m n : ℕ) :
    ‖(m : ℂ) - (n : ℂ)‖ = (idxDist m n : ℝ) := by
  have hcast : (m : ℂ) - (n : ℂ) = (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.lt_or_ge m n with h | h
  · rw [idxDist_eq_sub_of_ge h.le, Nat.cast_sub h.le, abs_of_neg (by exact_mod_cast
      (sub_neg.mpr (Nat.cast_lt.mpr h) : ((m : ℝ) - (n : ℝ)) < 0))]
    ring
  · rw [idxDist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]

/-- **Euler jets on a geometrically separated circle.**  Separation with ratio `q ≤ 1/32` around
the dominant index `n` makes `f` at least half its dominant term on the whole circle, puts the
first Euler jet within `32 q` of `n`, and bounds the second Euler jet by `64 q`. -/
theorem eulerJets_of_geometric_separation (ha : EntireCoeffs a) {n : ℕ} (han : a n ≠ 0)
    {t q : ℝ} (ht : 0 < t) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 32)
    (hsep : ∀ m : ℕ, ‖a m‖ * t ^ m ≤ ‖a n‖ * t ^ n * q ^ idxDist m n)
    {z : ℂ} (hz : ‖z‖ = t) :
    ‖a n‖ * t ^ n / 2 ≤ ‖coeffFun a z‖ ∧
      ‖eulerLogDeriv (coeffFun a) z - n‖ ≤ 32 * q ∧
      ‖eulerLogDerivSecond (coeffFun a) z‖ ≤ 64 * q := by
  classical
  set μ := ‖a n‖ * t ^ n with hμ
  have hμpos : 0 < μ := mul_pos (norm_pos_iff.mpr han) (pow_pos ht n)
  set ω := 4 * q with hω
  have hω0 : 0 ≤ ω := by positivity
  have hω1 : ω < 1 := by linarith
  set g : ℕ → ℝ := fun i => if i = n then 0 else ω ^ idxDist i n with hg
  have hgnn : ∀ i, 0 ≤ g i := fun i => by
    simp only [hg]
    split_ifs
    · exact le_rfl
    · positivity
  have hwsum := summable_pow_idxDist hω0 hω1 n
  have hgsum : Summable g :=
    Summable.of_nonneg_of_le hgnn (fun i => by
      simp only [hg]
      split_ifs
      · positivity
      · exact le_rfl) hwsum
  have hgle : ∑' i, g i ≤ 4 * ω := tsum_ite_pow_idxDist_le hω0 (by linarith) n
  have hq_le_ω : ∀ m, q ^ idxDist m n ≤ ω ^ idxDist m n := fun m =>
    pow_le_pow_left₀ hq0 (by linarith) _
  -- termwise dominations
  have hterm0 : ∀ m, ‖a m * z ^ m‖ ≤ μ * ω ^ idxDist m n := fun m => by
    rw [norm_mul, norm_pow, hz]
    exact (hsep m).trans (mul_le_mul_of_nonneg_left (hq_le_ω m) hμpos.le)
  have htermp : ∀ p : ℕ, 1 ≤ p → p ≤ 2 → ∀ m : ℕ,
      ‖((m : ℂ) - (n : ℂ)) ^ p * a m * z ^ m‖ ≤ μ * g m := by
    intro p hp1 hp2 m
    rw [norm_mul, norm_mul, norm_pow, norm_pow, hz, norm_natCast_sub_natCast_eq_idxDist]
    by_cases hmn : m = n
    · subst hmn
      rw [idxDist_self]
      simp only [hg, if_pos rfl, Nat.cast_zero, zero_pow (by omega : p ≠ 0), zero_mul, mul_zero,
        le_refl]
    · simp only [hg, if_neg hmn]
      calc (idxDist m n : ℝ) ^ p * ‖a m‖ * t ^ m
          = (idxDist m n : ℝ) ^ p * (‖a m‖ * t ^ m) := by ring
        _ ≤ (idxDist m n : ℝ) ^ p * (μ * q ^ idxDist m n) :=
            mul_le_mul_of_nonneg_left (hsep m) (by positivity)
        _ = μ * ((idxDist m n : ℝ) ^ p * q ^ idxDist m n) := by ring
        _ ≤ μ * ω ^ idxDist m n :=
            mul_le_mul_of_nonneg_left (natCast_pow_mul_pow_le_four_mul_pow hq0 _ hp2) hμpos.le
  have htermite : ∀ m, ‖(if m = n then (0 : ℂ) else a m * z ^ m)‖ ≤ μ * g m := fun m => by
    by_cases hmn : m = n
    · simp [hmn, hg]
    · simp only [hmn, if_false, hg]
      exact hterm0 m
  -- summability
  have hS0 : Summable (fun m => a m * z ^ m) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm0
      (hwsum.mul_left μ))
  have hGsum : ∀ p : ℕ, 1 ≤ p → p ≤ 2 →
      Summable (fun m : ℕ => ((m : ℂ) - (n : ℂ)) ^ p * a m * z ^ m) := fun p hp1 hp2 =>
    Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (htermp p hp1 hp2)
      (hgsum.mul_left μ))
  have hGbound : ∀ p : ℕ, 1 ≤ p → p ≤ 2 →
      ‖∑' m : ℕ, ((m : ℂ) - (n : ℂ)) ^ p * a m * z ^ m‖ ≤ 16 * q * μ := by
    intro p hp1 hp2
    have hnorm := norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (htermp p hp1 hp2) (hgsum.mul_left μ))
    refine hnorm.trans ?_
    calc ∑' m : ℕ, ‖((m : ℂ) - (n : ℂ)) ^ p * a m * z ^ m‖
        ≤ ∑' m, μ * g m := (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
          (htermp p hp1 hp2) (hgsum.mul_left μ)).tsum_le_tsum (htermp p hp1 hp2)
            (hgsum.mul_left μ)
      _ = μ * ∑' m, g m := tsum_mul_left
      _ ≤ μ * (4 * ω) := mul_le_mul_of_nonneg_left hgle hμpos.le
      _ = 16 * q * μ := by rw [hω]; ring
  set G₁ := ∑' m : ℕ, ((m : ℂ) - (n : ℂ)) ^ 1 * a m * z ^ m with hG₁
  set G₂ := ∑' m : ℕ, ((m : ℂ) - (n : ℂ)) ^ 2 * a m * z ^ m with hG₂
  have hG₁b : ‖G₁‖ ≤ 16 * q * μ := hGbound 1 le_rfl (by norm_num)
  have hG₂b : ‖G₂‖ ≤ 16 * q * μ := hGbound 2 (by norm_num) le_rfl
  -- the value
  set F := coeffFun a z with hF
  have hFsum : F = ∑' m, a m * z ^ m := coeffFun_eq_tsum a z
  have hFsplit : F - a n * z ^ n = ∑' m, (if m = n then (0 : ℂ) else a m * z ^ m) := by
    rw [hFsum, hS0.tsum_eq_add_tsum_ite n]
    ring
  have hFdev : ‖F - a n * z ^ n‖ ≤ 16 * q * μ := by
    rw [hFsplit]
    have hsumite : Summable (fun m => ‖(if m = n then (0 : ℂ) else a m * z ^ m)‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) htermite (hgsum.mul_left μ)
    calc ‖∑' m, (if m = n then (0 : ℂ) else a m * z ^ m)‖
        ≤ ∑' m, ‖(if m = n then (0 : ℂ) else a m * z ^ m)‖ := norm_tsum_le_tsum_norm hsumite
      _ ≤ ∑' m, μ * g m := hsumite.tsum_le_tsum htermite (hgsum.mul_left μ)
      _ = μ * ∑' m, g m := tsum_mul_left
      _ ≤ μ * (4 * ω) := mul_le_mul_of_nonneg_left hgle hμpos.le
      _ = 16 * q * μ := by rw [hω]; ring
  have hlead : ‖a n * z ^ n‖ = μ := by rw [norm_mul, norm_pow, hz]
  have hFlow : μ / 2 ≤ ‖F‖ := by
    have htri := norm_sub_norm_le (a n * z ^ n) (a n * z ^ n - F)
    rw [sub_sub_cancel, hlead, norm_sub_rev] at htri
    have : 16 * q * μ ≤ μ / 2 := by nlinarith
    linarith
  have hFpos : 0 < ‖F‖ := lt_of_lt_of_le (by positivity) hFlow
  have hFne : F ≠ 0 := norm_pos_iff.mp hFpos
  -- the first jet
  set b : ℕ → ℂ := fun m => (m : ℂ) * a m with hb
  have hbE : EntireCoeffs b := entireCoeffs_mul_index ha
  have hS1fun : ∀ w : ℂ, w * deriv (coeffFun a) w = coeffFun b w := fun w => by
    rw [mul_deriv_coeffFun_eq ha w, coeffFun_eq_tsum]
  have hS1 : z * deriv (coeffFun a) z = G₁ + n * F := by
    rw [mul_deriv_coeffFun_eq ha z, hFsum, ← tsum_mul_left,
      ← (hGsum 1 le_rfl (by norm_num)).tsum_add (hS0.mul_left (n : ℂ))]
    exact tsum_congr fun m => by ring
  have hu : eulerLogDeriv (coeffFun a) z = n + G₁ / F := by
    rw [eulerLogDeriv, hS1, ← hF]
    field_simp
    ring
  refine ⟨hFlow, ?_, ?_⟩
  · rw [hu, add_sub_cancel_left, norm_div]
    rw [div_le_iff₀ hFpos]
    calc ‖G₁‖ ≤ 16 * q * μ := hG₁b
      _ = 32 * q * (μ / 2) := by ring
      _ ≤ 32 * q * ‖F‖ := mul_le_mul_of_nonneg_left hFlow (by positivity)
  · -- the second jet
    have hS2 : z * deriv (coeffFun b) z = G₂ + 2 * n * G₁ + n ^ 2 * F := by
      rw [mul_deriv_coeffFun_eq hbE z, hFsum, ← tsum_mul_left, ← tsum_mul_left,
        ← (hGsum 2 (by norm_num) le_rfl).tsum_add
          ((hGsum 1 le_rfl (by norm_num)).mul_left (2 * (n : ℂ))),
        ← ((hGsum 2 (by norm_num) le_rfl).add
          ((hGsum 1 le_rfl (by norm_num)).mul_left (2 * (n : ℂ)))).tsum_add
          (hS0.mul_left ((n : ℂ) ^ 2))]
      exact tsum_congr fun m => by simp only [hb]; ring
    have hufun : eulerLogDeriv (coeffFun a) = fun w => coeffFun b w / coeffFun a w := by
      funext w
      rw [eulerLogDeriv, hS1fun]
    have hderiv : HasDerivAt (eulerLogDeriv (coeffFun a))
        ((deriv (coeffFun b) z * coeffFun a z - coeffFun b z * deriv (coeffFun a) z) /
          coeffFun a z ^ 2) z := by
      rw [hufun]
      exact ((differentiable_coeffFun hbE z).hasDerivAt).div
        ((differentiable_coeffFun ha z).hasDerivAt) hFne
    have hv : eulerLogDerivSecond (coeffFun a) z = (G₂ * F - G₁ ^ 2) / F ^ 2 := by
      rw [eulerLogDerivSecond, hderiv.deriv, ← hF]
      have h1 : coeffFun b z = G₁ + n * F := by rw [← hS1fun, hS1]
      have hnum : z * ((deriv (coeffFun b) z * F - coeffFun b z * deriv (coeffFun a) z) / F ^ 2)
          = ((z * deriv (coeffFun b) z) * F - coeffFun b z * (z * deriv (coeffFun a) z)) /
            F ^ 2 := by ring
      rw [hnum, hS2, h1, hS1]
      ring
    rw [hv, norm_div, norm_sub_rev]
    have hF2 : ‖F ^ 2‖ = ‖F‖ ^ 2 := norm_pow _ _
    rw [hF2, div_le_iff₀ (by positivity)]
    calc ‖G₁ ^ 2 - G₂ * F‖ ≤ ‖G₁‖ ^ 2 + ‖G₂‖ * ‖F‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_pow, norm_mul]
      _ ≤ (16 * q * μ) ^ 2 + (16 * q * μ) * ‖F‖ := by
          gcongr
      _ ≤ (32 * q * ‖F‖) ^ 2 + 32 * q * ‖F‖ * ‖F‖ := by
          have h2 : 16 * q * μ ≤ 32 * q * ‖F‖ := by nlinarith
          gcongr
      _ ≤ 64 * q * ‖F‖ ^ 2 := by
          have : 1024 * q ^ 2 ≤ 32 * q := by nlinarith
          nlinarith [sq_nonneg ‖F‖]

end

end GaloisForLFunctions.HTGeometry
