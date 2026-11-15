import GaloisForLFunctions.SurfaceOfSpecZ.TheTensorPowerTrick
import GaloisForLFunctions.SquareRootThreshold.TheSevenEighthsStripBoundsTheZeroWidth
import Mathlib.NumberTheory.Primorial

/-!
# The prime-trace moments of ζ read the width with base loss at most one

The tensor-power trick over `Spec ℤ` (`SurfaceOfSpecZ.riemannHypothesis_iff_moments_primeTraces`)
uses the prime-trace moments `M_k(N) = Σ_{p ≤ N} log p · (2 Re S(log p))^{2k}`. Their growth
exponent `a_k` (`momentExponent`, the least `a ≥ 0` with `M_k(N) = O(N^a)`) lies in a window of
width one around `2kw`, `w` the zero width:

* **Upper end** (`momentBound_one_add`): `M_k(N) = O(N^{1 + 2kw})`. The width law at the primes
  bounds the traces by `K p^w` on both sides, and Chebyshev's `Σ_{p ≤ N} log p ≤ N log 4` is the
  base loss `1`.
* **Lower end** (`two_mul_width_le_of_momentBound`): `M_k(N) = O(N^a)` forces `2kw ≤ a`, from a
  single prime.
* **The window** (`two_mul_width_le_momentExponent`, `momentExponent_le`,
  `tendsto_momentExponent_div`): `2kw ≤ a_k ≤ 1 + 2kw`, so `a_k/(2k) → w`.
* **The pole law at any weight is the width** (`exists_momentPoleLaw_iff`): bounds
  `M_k(N) = O(N^{2k w₀ + A})` for all `k` with `A` independent of `k` hold iff `w ≤ w₀`.
  At `w₀ = 0` this is the tensor-power trick; at every `w₀` it is a ruler.

The motive of the zeros is a flow datum; for finite configurations the exponent is exactly
`1 + 2kW` (`summable_flowMomentTerm_iff`). For `ζ` the window is what the width law at the
primes gives without any count of the zeros.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

open SurfaceOfSpecZ ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold
  Zeta23

/-- The prime trace `2 Re S(log p)` of `ζ` at `p`. -/
abbrev primeTrace (p : ℕ) : ℝ := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re

/-- The `k`-th prime-trace moment grows at most like `N^a`. -/
def MomentBound (k : ℕ) (a : ℝ) : Prop := ∃ C : ℝ, ∀ N : ℕ, primeTraceMoment k N ≤ C * (N : ℝ) ^ a

/-- The growth exponent of the `k`-th prime-trace moment. -/
def momentExponent (k : ℕ) : ℝ := sInf {a : ℝ | 0 ≤ a ∧ MomentBound k a}

theorem zetaZeroWidth_lt_half : zetaZeroWidth < 1 / 2 := by
  linarith [zetaZeroWidth_le_three_eighths]

/-- Chebyshev: `Σ_{p ≤ N} log p ≤ N log 4`. -/
theorem sum_log_primes_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ≤ N * Real.log 4 := by
  have hprod : ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p =
      Real.log (primorial N : ℝ) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero
  rw [hprod, ← Real.log_rpow (by norm_num : (0 : ℝ) < 4)]
  have h4 : (primorial N : ℝ) ≤ (4 : ℝ) ^ (N : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast primorial_le_4_pow N
  exact Real.log_le_log (by exact_mod_cast primorial_pos N) h4

/-- The width law at the primes, both sides: `|2 Re S(log p)| ≤ K p^w`. -/
theorem exists_abs_primeTrace_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℕ, p.Prime →
    |primeTrace p| ≤ K * (p : ℝ) ^ zetaZeroWidth := by
  obtain ⟨K₁, hK₁⟩ := (zetaZeroWidth_le_iff_bddBelow_primeDegrees zetaZeroWidth_nonneg
    zetaZeroWidth_lt_half).mp le_rfl
  obtain ⟨K₂, hK₂⟩ := (zetaZeroWidth_le_iff_bddAbove_primeDegrees zetaZeroWidth_nonneg
    zetaZeroWidth_lt_half).mp le_rfl
  refine ⟨|K₁| + |K₂|, by positivity, fun p hp => ?_⟩
  have hpw : 0 ≤ (p : ℝ) ^ zetaZeroWidth := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have h1 := hK₁ p hp
  have h2 := hK₂ p hp
  rw [abs_le]
  constructor <;> nlinarith [le_abs_self K₁, le_abs_self K₂, neg_abs_le K₁, abs_nonneg K₂]

/-- **Upper end of the window**: `M_k(N) = O(N^{1 + 2kw})`. -/
theorem momentBound_one_add (k : ℕ) : MomentBound k (1 + 2 * k * zetaZeroWidth) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_primeTrace_le
  set w := zetaZeroWidth
  have hw0 : 0 ≤ w := zetaZeroWidth_nonneg
  refine ⟨K ^ (2 * k) * Real.log 4, fun N => ?_⟩
  have hterm : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      Real.log p * primeTrace p ^ (2 * k) ≤ Real.log p * (K ^ (2 * k) * (N : ℝ) ^ (2 * k * w)) := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := Finset.mem_filter.mp hp
    have hpN' : (p : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hpN)
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    refine mul_le_mul_of_nonneg_left ?_ hlog
    have h1 : primeTrace p ^ (2 * k) = |primeTrace p| ^ (2 * k) := by
      rw [pow_mul, pow_mul, sq_abs]
    have h2 : |primeTrace p| ≤ K * (N : ℝ) ^ w :=
      (hK p hpp).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg p) hpN' hw0) hK0)
    rw [h1]
    calc |primeTrace p| ^ (2 * k) ≤ (K * (N : ℝ) ^ w) ^ (2 * k) :=
          pow_le_pow_left₀ (abs_nonneg _) h2 _
      _ = K ^ (2 * k) * (N : ℝ) ^ (2 * k * w) := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ w), ← Real.rpow_mul (Nat.cast_nonneg N)]
          push_cast; ring_nf
  calc primeTraceMoment k N
      ≤ ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
          Real.log p * (K ^ (2 * k) * (N : ℝ) ^ (2 * k * w)) := Finset.sum_le_sum hterm
    _ = (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p) *
          (K ^ (2 * k) * (N : ℝ) ^ (2 * k * w)) := by rw [Finset.sum_mul]
    _ ≤ (N * Real.log 4) * (K ^ (2 * k) * (N : ℝ) ^ (2 * k * w)) :=
        mul_le_mul_of_nonneg_right (sum_log_primes_le N) (by positivity)
    _ = K ^ (2 * k) * Real.log 4 * (N : ℝ) ^ (1 + 2 * k * w) := by
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp
        · rw [Real.rpow_add (by exact_mod_cast hN), Real.rpow_one]
          ring

/-- Moment bounds weaken to larger exponents. -/
theorem MomentBound.mono {k : ℕ} {a b : ℝ} (hab : a ≤ b) (h : MomentBound k a) : MomentBound k b := by
  obtain ⟨C, hC⟩ := h
  refine ⟨|C|, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : primeTraceMoment k 0 = 0 := by
      simp [primeTraceMoment, Finset.filter_singleton, Nat.not_prime_zero]
    rw [h0]
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg le_rfl _)
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    calc primeTraceMoment k N ≤ C * (N : ℝ) ^ a := hC N
      _ ≤ |C| * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right (le_abs_self C)
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ ≤ |C| * (N : ℝ) ^ b := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN1 hab) (abs_nonneg _)

/-- **Lower end of the window**: `M_k(N) = O(N^a)` with `a ≥ 0` forces `2kw ≤ a`. -/
theorem two_mul_width_le_of_momentBound {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 ≤ a)
    (h : MomentBound k a) : 2 * k * zetaZeroWidth ≤ a := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hw38 := zetaZeroWidth_le_three_eighths
  by_cases hak : (k : ℝ) ≤ a
  · nlinarith
  push Not at hak
  obtain ⟨C, hC⟩ := h
  set a' := a / (2 * k) with ha'
  have ha'0 : 0 ≤ a' := by positivity
  have ha'1 : a' < 1 / 2 := by
    rw [ha', div_lt_iff₀ (by positivity)]
    linarith
  have hw : zetaZeroWidth ≤ a' := by
    rw [zetaZeroWidth_le_iff_bddBelow_primeDegrees ha'0 ha'1]
    set B : ℝ := |C| / Real.log 2 with hB
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    refine ⟨B ^ ((1 : ℝ) / (2 * k)), fun p hp => ?_⟩
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    set c := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re with hc
    -- one term of the moment at N = p
    have hone : Real.log p * c ^ (2 * k) ≤ C * (p : ℝ) ^ a := by
      have hmem : p ∈ (Finset.range (p + 1)).filter Nat.Prime :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self p), hp⟩
      have h := hC p
      unfold primeTraceMoment at h
      refine le_trans (Finset.single_le_sum (f := fun q : ℕ => Real.log q *
        (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log q)).re) ^ (2 * k))
        (fun q hq => mul_nonneg (Real.log_nonneg (by
          exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le)) (by
            rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)) hmem) h
    have hc2k : |c| ^ (2 * k) ≤ B * (p : ℝ) ^ a := by
      rw [show |c| ^ (2 * k) = c ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
      have h1 : Real.log 2 * c ^ (2 * k) ≤ Real.log p * c ^ (2 * k) :=
        mul_le_mul_of_nonneg_right hlogp (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
      have h2 : C * (p : ℝ) ^ a ≤ |C| * (p : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      rw [hB, div_mul_eq_mul_div, le_div_iff₀ hlog2]
      linarith
    have hroot : |c| ≤ B ^ ((1 : ℝ) / (2 * k)) * (p : ℝ) ^ a' := by
      have h1 := Real.rpow_le_rpow (by positivity) hc2k (by positivity : (0 : ℝ) ≤ 1 / (2 * k))
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c),
        show ((2 * k : ℕ) : ℝ) * (1 / (2 * k)) = 1 by push_cast; field_simp, Real.rpow_one,
        Real.mul_rpow hB0 (by positivity), ← Real.rpow_mul hp0.le] at h1
      have he : a * (1 / (2 * k)) = a' := by rw [ha']; ring
      rwa [he] at h1
    linarith [neg_abs_le c]
  calc 2 * k * zetaZeroWidth ≤ 2 * k * a' := by gcongr
    _ = a := by rw [ha']; field_simp

/-- **The window, lower end**: `2kw ≤ a_k`. -/
theorem two_mul_width_le_momentExponent {k : ℕ} (hk : 1 ≤ k) :
    2 * k * zetaZeroWidth ≤ momentExponent k := by
  have hw0 := zetaZeroWidth_nonneg
  exact le_csInf ⟨1 + 2 * k * zetaZeroWidth, ⟨by positivity, momentBound_one_add k⟩⟩
    fun a ha => two_mul_width_le_of_momentBound hk ha.1 ha.2

/-- **The window, upper end**: `a_k ≤ 1 + 2kw`. -/
theorem momentExponent_le (k : ℕ) : momentExponent k ≤ 1 + 2 * k * zetaZeroWidth := by
  have hw0 := zetaZeroWidth_nonneg
  exact csInf_le ⟨0, fun a ha => ha.1⟩ ⟨by positivity, momentBound_one_add k⟩

/-- `a_k/(2k) → w`: the tensor-power moments are a ruler for the zero width. -/
theorem tendsto_momentExponent_div :
    Tendsto (fun k : ℕ => momentExponent k / (2 * k)) atTop (𝓝 zetaZeroWidth) := by
  have hup : Tendsto (fun k : ℕ => zetaZeroWidth + 1 / 2 * (1 / (k : ℝ))) atTop
      (𝓝 (zetaZeroWidth + 1 / 2 * 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat.const_mul (1 / 2))
  rw [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [le_div_iff₀ (by positivity)]
    linarith [two_mul_width_le_momentExponent hk]
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity)]
    have := momentExponent_le k
    have h2 : (zetaZeroWidth + 1 / 2 * (1 / (k : ℝ))) * (2 * k) = 1 + 2 * k * zetaZeroWidth := by
      field_simp
      ring
    linarith

/-- **The pole law at any weight is the width.** For `w₀ ≥ 0`: bounds `M_k(N) = O(N^{2kw₀ + A})`
for every `k ≥ 1`, with `A` independent of `k`, hold iff `w ≤ w₀`. -/
theorem exists_momentPoleLaw_iff {w₀ : ℝ} (hw₀ : 0 ≤ w₀) :
    (∃ A : ℝ, ∀ k : ℕ, 1 ≤ k → MomentBound k (2 * k * w₀ + A)) ↔ zetaZeroWidth ≤ w₀ := by
  constructor
  · rintro ⟨A, hA⟩
    by_contra hlt
    push Not at hlt
    have hd : 0 < zetaZeroWidth - w₀ := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (|A| / (2 * (zetaZeroWidth - w₀))))
    have hk1 : 1 ≤ k := by
      have : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
      exact_mod_cast this.le
    have hk2 : |A| / (2 * (zetaZeroWidth - w₀)) < k := (le_max_right _ _).trans_lt hk
    rw [div_lt_iff₀ (by positivity)] at hk2
    have hb := two_mul_width_le_of_momentBound hk1 (le_max_right _ _)
      ((hA k hk1).mono (le_max_left (2 * k * w₀ + A) 0))
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    rcases le_total (2 * k * w₀ + A) 0 with h0 | h0
    · rw [max_eq_right h0] at hb
      nlinarith
    · rw [max_eq_left h0] at hb
      nlinarith [le_abs_self A]
  · intro hle
    refine ⟨1, fun k _ => (momentBound_one_add k).mono ?_⟩
    have : (2 * k * zetaZeroWidth : ℝ) ≤ 2 * k * w₀ := by gcongr
    linarith

end GaloisForLFunctions.TensorPowerProgramme
