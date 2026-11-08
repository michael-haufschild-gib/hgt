import GaloisForLFunctions.CountingHolography.TheFareyReadingOfTheHorocycle
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic

/-!
# The rate of a sharp shell

A sharp shell `a ≤ Im z < b` is a source with a jump, outside the smooth class of Zagier's theorem. Its
Farey kernel is explicit (`fareyKernel_shell`): the horocycle at height `y` spends the time
`2(√(y/(c²a) − y²) − √(y/(c²b) − y²))` in the shell of one cusp image of denominator `c`. So the mean
number of cusp images met (`horocycleMean_shell_eq`) is

  `4y (H(X_a) − H(X_b))`,  `H(X) = Σ_c φ(c) √((X/c)² − 1)`,  `X_a = (ay)^{-1/2}`,

a totient-weighted horoball profile.

* **The horoball count is a Möbius sum of circle counts** (`horoballSum_eq_moebius`):

    `Σ_c φ(c) √((X/c)² − 1) = Σ_d μ(d) Σ_{m ≥ 1} √((X/d)² − m²)`.

  The inner sum is the column sum of the lattice points of the quarter disc of radius `X/d`; it is
  within `Y` of the area `πY²/4` (`quarterDisc_bounds`).
* **The exact decomposition of the error** (`horoballSum_decomposition`): with
  `E(Y) = Σ_{m ≥ 1} √(Y² − m²) − πY²/4 + Y/2` the remainder of the quarter disc,

    `H(X) − (3/2π)X² = Σ_{d ≤ X} μ(d) E(X/d) − (X/2) Σ_{d ≤ X} μ(d)/d
                        + (π/4) X² (Σ_{d ≤ X} μ(d)/d² − 6/π²)`.

* **Sharp shells thermalize at rate `y^{1/2} log(1/y)`, unconditionally** (`shell_rate`):

    `|mean_y(shell) − (6/π)(1/a − 1/b)| ≤ 12 (√(y/a)(1 + log X_a) + √(y/b)(1 + log X_b))`.

  The limit `(6/π)(1/a − 1/b)` is twice the hyperbolic area of the shell over the area `π/3` of the
  modular surface (each cusp image is met by the two rows `±(c, d)`).

The decomposition locates the question of an RH rate for shells. The last two terms are sums of `μ`
weighted by `1/d` and `1/d²`, and RH bounds both by `X^{1/2+ε}`. The first term pairs `μ` with the
remainder of the circle problem; RH does not control it, and `y^{3/4}` for sharp shells would require
`Σ_{d ≤ X} μ(d) E(X/d) = O(X^{1/2+ε})`.
-/

open MeasureTheory Finset Real
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open BlackHoleRingdown

/-! ### The quarter disc -/

/-- The column sum of the quarter disc of radius `Y`: `Σ_{1 ≤ m ≤ M} √(Y² − m²)`. -/
def quarterDisc (Y : ℝ) (M : ℕ) : ℝ := ∑ m ∈ Icc 1 M, √(Y ^ 2 - (m : ℝ) ^ 2)

theorem antitoneOn_disc (Y : ℝ) : AntitoneOn (fun x : ℝ => √(Y ^ 2 - x ^ 2)) (Set.Ici 0) := by
  intro x hx z _ hxz
  apply Real.sqrt_le_sqrt
  have : x ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hx hxz 2
  linarith

theorem sum_Icc_eq_sum_range (g : ℕ → ℝ) (M : ℕ) : ∑ m ∈ Icc 1 M, g m = ∑ i ∈ range M, g (i + 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `∫₀¹ √(1 − t²) dt = π/4`. -/
theorem integral_sqrt_one_sub_sq_half : ∫ t in (0 : ℝ)..1, √(1 - t ^ 2) = π / 4 := by
  have hc : Continuous fun t : ℝ => √(1 - t ^ 2) := by fun_prop
  have h := integral_sqrt_one_sub_sq
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)] at h
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun t : ℝ => √(1 - t ^ 2))
  simp only [neg_sq, neg_zero] at hneg
  linarith

/-- **The area of the quarter disc**: `∫₀^M √(Y² − x²) dx = πY²/4` for `0 ≤ Y ≤ M`. -/
theorem integral_disc {Y M : ℝ} (hY : 0 ≤ Y) (hYM : Y ≤ M) :
    ∫ x in (0 : ℝ)..M, √(Y ^ 2 - x ^ 2) = π * Y ^ 2 / 4 := by
  have hc : Continuous fun x : ℝ => √(Y ^ 2 - x ^ 2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Y) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h2 : ∫ x in Y..M, √(Y ^ 2 - x ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
    intro x hx
    rw [Set.uIcc_of_le hYM] at hx
    refine Real.sqrt_eq_zero'.mpr ?_
    nlinarith [hx.1]
  rw [h2, add_zero]
  rcases hY.eq_or_lt with h0 | hYpos
  · rw [← h0]
    simp
  · have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
      (fun x : ℝ => √(Y ^ 2 - x ^ 2)) hYpos.ne'
    simp only [mul_zero, mul_one] at hsub
    have hfac : ∀ t : ℝ, √(Y ^ 2 - (Y * t) ^ 2) = Y * √(1 - t ^ 2) := fun t => by
      rw [show Y ^ 2 - (Y * t) ^ 2 = Y ^ 2 * (1 - t ^ 2) by ring, Real.sqrt_mul (sq_nonneg Y),
        Real.sqrt_sq hY]
    simp only [hfac, intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq_half,
      smul_eq_mul] at hsub
    field_simp at hsub
    linarith

/-- **The quarter disc is within its radius of its area.** -/
theorem quarterDisc_bounds {Y : ℝ} (hY : 0 ≤ Y) {M : ℕ} (hM : ⌊Y⌋₊ ≤ M) :
    π * Y ^ 2 / 4 - Y ≤ quarterDisc Y M ∧ quarterDisc Y M ≤ π * Y ^ 2 / 4 := by
  set f : ℝ → ℝ := fun x => √(Y ^ 2 - x ^ 2)
  have hf0 : ∀ x, 0 ≤ f x := fun x => Real.sqrt_nonneg _
  -- terms beyond `⌊Y⌋` vanish, so the sum is the sum up to `M' = ⌊Y⌋ + 1 ≥ Y` minus nothing
  set M' := ⌊Y⌋₊ + 1
  have hYM' : Y ≤ M' := by
    have := Nat.lt_floor_add_one Y
    push_cast [M']
    linarith
  have hvan : ∀ m : ℕ, ⌊Y⌋₊ < m → f m = 0 := by
    intro m hm
    refine Real.sqrt_eq_zero'.mpr ?_
    have : Y < m := by
      have h1 := Nat.lt_floor_add_one Y
      have h2 : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
      push_cast at h2
      linarith
    nlinarith
  have heq : ∀ K : ℕ, ⌊Y⌋₊ ≤ K → quarterDisc Y K = quarterDisc Y ⌊Y⌋₊ := by
    intro K hK
    unfold quarterDisc
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hK)]
    intro m hm hnot
    simp only [Finset.mem_Icc] at hm hnot
    exact hvan m (by omega)
  rw [heq M hM]
  have hanti : AntitoneOn f (Set.Icc (0 : ℝ) (0 + (M' : ℕ))) := (antitoneOn_disc Y).mono fun x hx => hx.1
  have hint : ∫ x in (0 : ℝ)..(0 + (M' : ℕ)), f x = π * Y ^ 2 / 4 := by
    rw [zero_add]
    exact integral_disc hY hYM'
  have hup := hanti.sum_le_integral
  have hlo := hanti.integral_le_sum
  rw [hint] at hup hlo
  have hQ : quarterDisc Y M' = ∑ i ∈ range M', f (0 + ((i + 1 : ℕ) : ℝ)) := by
    unfold quarterDisc
    rw [sum_Icc_eq_sum_range]
    simp [f]
  have hQ' : f 0 + quarterDisc Y ⌊Y⌋₊ = ∑ i ∈ range M', f (0 + (i : ℝ)) := by
    unfold quarterDisc
    rw [sum_Icc_eq_sum_range, Finset.sum_range_succ']
    simp only [f, zero_add, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    ring
  have hf00 : f 0 = Y := by
    simp only [f]
    rw [show Y ^ 2 - (0 : ℝ) ^ 2 = Y ^ 2 by ring, Real.sqrt_sq hY]
  rw [heq M' (by omega)] at hQ
  constructor <;> linarith

/-! ### The horoball profile is a Möbius sum of quarter discs -/

/-- **The horoball profile**: `Σ_{1 ≤ c ≤ N} φ(c) √((X/c)² − 1)`. -/
def horoballSum (X : ℝ) (N : ℕ) : ℝ := ∑ c ∈ Icc 1 N, (c.totient : ℝ) * √((X / c) ^ 2 - 1)

/-- **The horoball count is a Möbius sum of circle counts.** -/
theorem horoballSum_eq_moebius (X : ℝ) (N : ℕ) :
    horoballSum X N = ∑ d ∈ Icc 1 N, (μ d : ℝ) * quarterDisc (X / d) (N / d) := by
  unfold horoballSum quarterDisc
  simp_rw [Finset.mul_sum]
  rw [← RHTower.Sieve.sum_divisors_swap N (fun d k => (μ d : ℝ) * √((X / d) ^ 2 - (k : ℝ) ^ 2))]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc0 : 0 < c := (Finset.mem_Icc.mp hc).1
  rw [RHTower.Sieve.totient_eq_sum_moebius_mul c hc0, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hc0
  rw [Nat.mul_div_cancel_left k hd0, mul_assoc]
  congr 1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have e : (X / d) ^ 2 - (k : ℝ) ^ 2 = (k : ℝ) ^ 2 * ((X / ((d * k : ℕ) : ℝ)) ^ 2 - 1) := by
    push_cast
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hkR.le]

/-- The remainder of the quarter disc: `Σ_{m ≥ 1} √(Y² − m²) − πY²/4 + Y/2`. -/
def circleRemainder (Y : ℝ) : ℝ := quarterDisc Y ⌊Y⌋₊ - π * Y ^ 2 / 4 + Y / 2

theorem abs_circleRemainder_le {Y : ℝ} (hY : 0 ≤ Y) : |circleRemainder Y| ≤ Y / 2 := by
  obtain ⟨h1, h2⟩ := quarterDisc_bounds hY le_rfl
  unfold circleRemainder
  rw [abs_le]
  constructor <;> linarith

/-- Only the denominators `d ≤ X` contribute, each through the full quarter disc of radius `X/d`. -/
theorem horoballSum_eq_floor {X : ℝ} (hX : 0 ≤ X) {N : ℕ} (hN : X ≤ N) :
    horoballSum X N = ∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * quarterDisc (X / d) ⌊X / d⌋₊ := by
  rw [horoballSum_eq_moebius]
  have hDN : ⌊X⌋₊ ≤ N := Nat.floor_le_of_le hN
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hDN)]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    congr 1
    -- the columns beyond `⌊X/d⌋` vanish
    have hfl : ⌊X / d⌋₊ ≤ N / d := by
      rw [Nat.floor_div_natCast]
      exact Nat.div_le_div_right hDN
    have hY : 0 ≤ X / d := div_nonneg hX (Nat.cast_nonneg _)
    unfold quarterDisc
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hfl)]
    intro m hm hnot
    simp only [Finset.mem_Icc, not_and, not_le] at hm hnot
    refine Real.sqrt_eq_zero'.mpr ?_
    have hm' : X / d < m := by
      have h1 := Nat.lt_floor_add_one (X / d)
      have h2 : ((⌊X / d⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hnot hm.1
      push_cast at h2
      linarith
    nlinarith
  · intro d hd hnot
    simp only [Finset.mem_Icc, not_and, not_le] at hd hnot
    -- `d > X`: the quarter disc of radius `X/d < 1` has no column
    have hdX : X < d := by
      have h1 := Nat.lt_floor_add_one X
      have h2 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hnot hd.1
      push_cast at h2
      linarith
    have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
    have hY1 : X / d < 1 := (div_lt_one hdR).mpr hdX
    unfold quarterDisc
    rw [Finset.sum_eq_zero, mul_zero]
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    refine Real.sqrt_eq_zero'.mpr ?_
    have hY0 : 0 ≤ X / d := div_nonneg hX hdR.le
    nlinarith

/-- **The exact decomposition of the horoball error.** -/
theorem horoballSum_decomposition {X : ℝ} (hX : 0 ≤ X) {N : ℕ} (hN : X ≤ N) :
    horoballSum X N - 3 / (2 * π) * X ^ 2 =
      ∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * circleRemainder (X / d) -
        X / 2 * ∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / d +
          π / 4 * X ^ 2 * (∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / π ^ 2) := by
  rw [horoballSum_eq_floor hX hN]
  unfold circleRemainder
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have e1 : ∀ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * (π * (X / d) ^ 2 / 4) =
      π / 4 * X ^ 2 * ((μ d : ℝ) / (d : ℝ) ^ 2) := fun d _ => by ring
  have e2 : ∀ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * (X / d / 2) = X / 2 * ((μ d : ℝ) / d) := fun d _ => by ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  field_simp
  ring

/-- **The horoball profile is `(3/2π)X²` up to `3X(1 + log X)`, unconditionally.** -/
theorem abs_horoballSum_sub_le {X : ℝ} (hX : 1 ≤ X) {N : ℕ} (hN : X ≤ N) :
    |horoballSum X N - 3 / (2 * π) * X ^ 2| ≤ 3 * X * (1 + Real.log X) := by
  have hX0 : 0 ≤ X := by linarith
  set D := ⌊X⌋₊
  have hD1 : 1 ≤ D := Nat.le_floor (by exact_mod_cast hX)
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDX : (D : ℝ) ≤ X := Nat.floor_le hX0
  have hXD : X < D + 1 := Nat.lt_floor_add_one X
  rw [horoballSum_eq_floor hX0 hN]
  -- split off the area term
  have hsplit : ∑ d ∈ Icc 1 D, (μ d : ℝ) * quarterDisc (X / d) ⌊X / d⌋₊ - 3 / (2 * π) * X ^ 2 =
      ∑ d ∈ Icc 1 D, (μ d : ℝ) * (quarterDisc (X / d) ⌊X / d⌋₊ - π * (X / d) ^ 2 / 4) +
        π / 4 * X ^ 2 * (∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / π ^ 2) := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have e1 : ∀ d ∈ Icc 1 D, (μ d : ℝ) * (π * (X / d) ^ 2 / 4) =
        π / 4 * X ^ 2 * ((μ d : ℝ) / (d : ℝ) ^ 2) := fun d _ => by ring
    rw [Finset.sum_congr rfl e1]
    field_simp
    ring
  rw [hsplit]
  -- the circle terms: `|Q(Y) − πY²/4| ≤ Y`
  have hfirst : |∑ d ∈ Icc 1 D, (μ d : ℝ) * (quarterDisc (X / d) ⌊X / d⌋₊ - π * (X / d) ^ 2 / 4)| ≤
      X * (1 + Real.log X) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D,
        |(μ d : ℝ) * (quarterDisc (X / d) ⌊X / d⌋₊ - π * (X / d) ^ 2 / 4)| ≤ X * (1 / (d : ℝ)) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
      have hY : 0 ≤ X / d := div_nonneg hX0 hd0.le
      obtain ⟨h1, h2⟩ := quarterDisc_bounds hY le_rfl
      have hμ : |(μ d : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      rw [abs_mul]
      have habs : |quarterDisc (X / d) ⌊X / d⌋₊ - π * (X / d) ^ 2 / 4| ≤ X / d := by
        rw [abs_le]; constructor <;> linarith
      calc |(μ d : ℝ)| * |quarterDisc (X / d) ⌊X / d⌋₊ - π * (X / d) ^ 2 / 4|
          ≤ 1 * (X / d) := mul_le_mul hμ habs (abs_nonneg _) zero_le_one
        _ = X * (1 / d) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hX0
    refine (RHTower.Sieve.sum_Icc_one_div_le_one_add_log D).trans ?_
    have := Real.log_le_log (by linarith) hDX
    linarith
  -- the tail of `Σ μ(d)/d²`
  have hsecond : |π / 4 * X ^ 2 * (∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / π ^ 2)| ≤ 2 * X := by
    have ht := RHTower.abs_sum_moebius_div_sq_sub_le hD1
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hinv : 1 / (D : ℝ) ≤ 2 / X := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    calc π / 4 * X ^ 2 * |∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / π ^ 2|
        ≤ π / 4 * X ^ 2 * (2 / X) := by
          refine mul_le_mul_of_nonneg_left (ht.trans hinv) (by positivity)
      _ = π / 2 * X := by field_simp; norm_num
      _ ≤ 2 * X := by nlinarith [Real.pi_le_four]
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ X * (1 + Real.log X) + 2 * X := add_le_add hfirst hsecond
    _ ≤ 3 * X * (1 + Real.log X) := by nlinarith

/-! ### The horocycle mean of a sharp shell -/

theorem volume_sq_le (A : ℝ) : volume {v : ℝ | v ^ 2 ≤ A} = ENNReal.ofReal (2 * √A) := by
  rcases le_or_gt 0 A with hA | hA
  · have : {v : ℝ | v ^ 2 ≤ A} = Set.Icc (-√A) √A := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      exact Real.sq_le hA
    rw [this, Real.volume_Icc]
    congr 1
    ring
  · have : {v : ℝ | v ^ 2 ≤ A} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      nlinarith [sq_nonneg v]
    rw [this, measure_empty, Real.sqrt_eq_zero'.mpr hA.le]
    simp

/-- **The Farey kernel of a sharp shell**: the time spent in the shell `a ≤ Im < b` of one cusp image
of denominator `c` by the horocycle at height `y`. -/
theorem fareyKernel_shell {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {y : ℝ} (hy : 0 < y) {c : ℕ}
    (hc : 1 ≤ c) :
    fareyKernel ((Set.Ico a b).indicator 1) y c =
      ((2 * (√(y / (c ^ 2 * a) - y ^ 2) - √(y / (c ^ 2 * b) - y ^ 2)) : ℝ) : ℂ) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set A := y / (c ^ 2 * a) - y ^ 2
  set B := y / (c ^ 2 * b) - y ^ 2
  set S := {v : ℝ | v ^ 2 ≤ A} \ {v : ℝ | v ^ 2 ≤ B}
  have hBA : B ≤ A := by
    have : y / (c ^ 2 * b) ≤ y / (c ^ 2 * a) :=
      div_le_div_of_nonneg_left hy.le (by positivity) (by gcongr)
    linarith
  have hpt : ∀ v : ℝ, (Set.Ico a b).indicator (1 : ℝ → ℂ) (y / ((c : ℝ) ^ 2 * (v ^ 2 + y ^ 2))) =
      S.indicator (fun _ => (1 : ℂ)) v := by
    intro v
    have hP : 0 < (c : ℝ) ^ 2 * (v ^ 2 + y ^ 2) := by positivity
    have e1 : a ≤ y / ((c : ℝ) ^ 2 * (v ^ 2 + y ^ 2)) ↔ v ^ 2 ≤ A := by
      rw [le_div_iff₀ hP, le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    have e2 : y / ((c : ℝ) ^ 2 * (v ^ 2 + y ^ 2)) < b ↔ ¬ v ^ 2 ≤ B := by
      rw [div_lt_iff₀ hP, not_le, sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    simp only [S, Set.indicator_apply, Set.mem_Ico, Set.mem_sdiff, Set.mem_setOf_eq, e1, e2,
      Pi.one_apply]
  have hmeasA : MeasurableSet {v : ℝ | v ^ 2 ≤ A} := measurableSet_le (by fun_prop) measurable_const
  have hmeasB : MeasurableSet {v : ℝ | v ^ 2 ≤ B} := measurableSet_le (by fun_prop) measurable_const
  have hsub : {v : ℝ | v ^ 2 ≤ B} ⊆ {v : ℝ | v ^ 2 ≤ A} := fun v hv => le_trans hv hBA
  unfold fareyKernel
  simp_rw [hpt]
  rw [integral_indicator_const _ (hmeasA.diff hmeasB), Measure.real, measure_sdiff hsub
    hmeasB.nullMeasurableSet (by rw [volume_sq_le]; exact ENNReal.ofReal_ne_top), volume_sq_le,
    volume_sq_le, ← ENNReal.ofReal_sub _ (by positivity),
    ENNReal.toReal_ofReal (by linarith [Real.sqrt_le_sqrt hBA])]
  simp only [Complex.real_smul, mul_one]
  push_cast
  ring

/-- `√(y/(c²a) − y²) = y √((X/c)² − 1)` with `X = (ay)^{-1/2}`. -/
theorem sqrt_kernel_eq {a y : ℝ} (ha : 0 < a) (hy : 0 < y) {c : ℕ} (hc : 1 ≤ c) :
    √(y / (c ^ 2 * a) - y ^ 2) = y * √((1 / √(a * y) / c) ^ 2 - 1) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hay : 0 < a * y := mul_pos ha hy
  have hs : √(a * y) ^ 2 = a * y := Real.sq_sqrt hay.le
  have hs0 : 0 < √(a * y) := Real.sqrt_pos.mpr hay
  have e : y / (c ^ 2 * a) - y ^ 2 = y ^ 2 * ((1 / √(a * y) / c) ^ 2 - 1) := by
    rw [div_pow, div_pow, one_pow, hs]
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq hy.le]

/-- **The mean number of cusp images in a sharp shell is a difference of two horoball profiles.** -/
theorem horocycleMean_shell_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {y : ℝ} (hy : 0 < y) (hya : y < a)
    {C : ℕ} (hC : 1 < ((C : ℝ) + 1) ^ 2 * a * y) :
    horocycleMean (fun z => (shellCount a b z : ℂ)) y =
      ((4 * y * (horoballSum (1 / √(a * y)) C - horoballSum (1 / √(b * y)) C) : ℝ) : ℂ) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [horocycleMean_shellCount ha hy hC, Set.indicator_of_notMem (fun h => by linarith [h.1]),
    mul_zero, zero_add]
  have hterm : ∀ c ∈ Finset.Icc 1 C, (c.totient : ℂ) * fareyKernel ((Set.Ico a b).indicator 1) y c =
      ((2 * y * ((c.totient : ℝ) * √((1 / √(a * y) / c) ^ 2 - 1) -
        (c.totient : ℝ) * √((1 / √(b * y) / c) ^ 2 - 1)) : ℝ) : ℂ) := by
    intro c hc
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    rw [fareyKernel_shell ha hab hy hc1, sqrt_kernel_eq ha hy hc1, sqrt_kernel_eq hb hy hc1]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, horoballSum, horoballSum]
  push_cast
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **Sharp shells thermalize at rate `y^{1/2} log(1/y)`, unconditionally.** For `0 < a ≤ b` and
`0 < y ≤ 1/b`, `y < a`, the mean number of cusp images in the shell `a ≤ Im < b` along the closed
horocycle of height `y` is within `12(√(y/a)(1 + log X_a) + √(y/b)(1 + log X_b))` of
`(6/π)(1/a − 1/b)`, `X_a = (ay)^{-1/2}`. -/
theorem shell_rate {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {y : ℝ} (hy : 0 < y) (hyb : y ≤ 1 / b)
    (hya : y < a) :
    ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y - ((6 / π * (1 / a - 1 / b) : ℝ) : ℂ)‖ ≤
      12 * (√(y / a) * (1 + Real.log (1 / √(a * y))) + √(y / b) * (1 + Real.log (1 / √(b * y)))) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set Xa := 1 / √(a * y)
  set Xb := 1 / √(b * y)
  have hay : 0 < a * y := mul_pos ha hy
  have hby : 0 < b * y := mul_pos hb hy
  have hsa : √(a * y) ^ 2 = a * y := Real.sq_sqrt hay.le
  have hsb : √(b * y) ^ 2 = b * y := Real.sq_sqrt hby.le
  have hsa0 : 0 < √(a * y) := Real.sqrt_pos.mpr hay
  have hsb0 : 0 < √(b * y) := Real.sqrt_pos.mpr hby
  -- `X_b ≥ 1` and `X_a ≥ X_b`
  have hby1 : b * y ≤ 1 := by
    have := (le_div_iff₀ hb).mp hyb
    linarith
  have hXb : 1 ≤ Xb := by
    rw [le_div_iff₀ hsb0, one_mul]
    exact Real.sqrt_le_one.mpr hby1
  have hXab : Xb ≤ Xa := one_div_le_one_div_of_le hsa0 (Real.sqrt_le_sqrt (by nlinarith))
  have hXa : 1 ≤ Xa := hXb.trans hXab
  -- the order of the Farey points seen
  set C := ⌈Xa⌉₊
  have hCa : Xa ≤ C := Nat.le_ceil Xa
  have hC : 1 < ((C : ℝ) + 1) ^ 2 * a * y := by
    have h1 : Xa ^ 2 * (a * y) = 1 := by
      rw [div_pow, one_pow, hsa]
      field_simp
    have h2 : Xa ^ 2 < ((C : ℝ) + 1) ^ 2 := by
      have : Xa < (C : ℝ) + 1 := by linarith
      exact pow_lt_pow_left₀ this (by linarith) two_ne_zero
    nlinarith
  rw [horocycleMean_shell_eq ha hab hy hya hC, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have ha' := abs_horoballSum_sub_le hXa hCa
  have hb' := abs_horoballSum_sub_le hXb (hXab.trans hCa)
  -- the main terms: `4y (3/2π)(X_a² − X_b²) = (6/π)(1/a − 1/b)`
  have hmain : 4 * y * (3 / (2 * π) * Xa ^ 2 - 3 / (2 * π) * Xb ^ 2) = 6 / π * (1 / a - 1 / b) := by
    simp only [Xa, Xb, div_pow, one_pow, hsa, hsb]
    field_simp
    ring
  have hya' : 4 * y * (3 * Xa * (1 + Real.log Xa)) = 12 * (√(y / a) * (1 + Real.log Xa)) := by
    have : y * Xa = √(y / a) := by
      simp only [Xa]
      rw [Real.sqrt_div hy.le, mul_one_div]
      rw [div_eq_div_iff hsa0.ne' (Real.sqrt_pos.mpr ha).ne', Real.sqrt_mul ha.le,
        ← mul_assoc, mul_comm (√y) (√a), mul_assoc, Real.mul_self_sqrt hy.le]
      ring
    linear_combination (12 * (1 + Real.log Xa)) * this
  have hyb' : 4 * y * (3 * Xb * (1 + Real.log Xb)) = 12 * (√(y / b) * (1 + Real.log Xb)) := by
    have : y * Xb = √(y / b) := by
      simp only [Xb]
      rw [Real.sqrt_div hy.le, mul_one_div]
      rw [div_eq_div_iff hsb0.ne' (Real.sqrt_pos.mpr hb).ne', Real.sqrt_mul hb.le,
        ← mul_assoc, mul_comm (√y) (√b), mul_assoc, Real.mul_self_sqrt hy.le]
      ring
    linear_combination (12 * (1 + Real.log Xb)) * this
  have key : 4 * y * (horoballSum Xa C - horoballSum Xb C) - 6 / π * (1 / a - 1 / b) =
      4 * y * (horoballSum Xa C - 3 / (2 * π) * Xa ^ 2) -
        4 * y * (horoballSum Xb C - 3 / (2 * π) * Xb ^ 2) := by
    rw [← hmain]
    ring
  rw [key]
  have h4y : 0 ≤ 4 * y := by linarith
  calc _ ≤ |4 * y * (horoballSum Xa C - 3 / (2 * π) * Xa ^ 2)| +
        |4 * y * (horoballSum Xb C - 3 / (2 * π) * Xb ^ 2)| := abs_sub _ _
    _ ≤ 4 * y * (3 * Xa * (1 + Real.log Xa)) + 4 * y * (3 * Xb * (1 + Real.log Xb)) := by
        rw [abs_mul (4 * y), abs_mul (4 * y), abs_of_nonneg h4y]
        exact add_le_add (mul_le_mul_of_nonneg_left ha' h4y) (mul_le_mul_of_nonneg_left hb' h4y)
    _ = _ := by rw [hya', hyb']; ring

end GaloisForLFunctions.CountingHolography

end
