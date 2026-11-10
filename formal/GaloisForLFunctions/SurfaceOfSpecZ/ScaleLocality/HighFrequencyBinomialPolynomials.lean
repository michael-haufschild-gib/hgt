import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import GaloisForLFunctions.SurfaceOfSpecZ.HeightsAtTheZerosOfTheSplineAreInPhase
import GaloisForLFunctions.SurfaceOfSpecZ.ConfigurationsNeedAnAttainedTopAtAlmostAllPrimes

/-!
# High-frequency binomial polynomials and phase-split spline harmonics

To construct a zero configuration in the class `𝒵` whose smoothed trace stays positive on
windows `[T_k − R_k, T_k + R_k]` of unbounded length while all frequencies lie above `Γ_k`
and all multiplicities equal `1`, we combine two algebraic ingredients:

1. **High-frequency binomial polynomials (`highFreqPoly`).** Expanding `1 = (z + (1 − z))^{2m₀}`
   and retaining the upper half `m₀ ≤ m ≤ 2m₀` produces a polynomial
   `P_{m₀}(z) = ∑_{d = m₀}^{2m₀} a(m₀, d) z^d` supported solely on frequencies `[m₀, 2m₀]`
   such that `‖1 − P_{m₀}(z)‖ ≤ 1/4` and `Re P_{m₀}(z) ≥ 3/4` on the arc `‖z‖ = 1, ‖1 − z‖ ≤ 1/4`.
2. **Phase-split pair synthesis.** At each frequency `γ_d = d δ_k`, two simple zeros (`mult = 1`)
   placed at `γ_d + η⁺` and `γ_d + η⁻` with `η^± ∈ (0, 26 / T_k]` align with the target phases
   `θ_d − arg(sinc(γ_d − ix_k)^8) ± arccos(b_d)` at the window center `T_k`, canceling the
   `d`-variation of `‖sinc(γ_d − ix_k)^8‖` and reproducing `a(m₀, d) e^{i γ_d v}` on `v ∈ [−R_k, R_k]`
   up to `O((R_k + 8) / T_k)`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-! ### High-frequency binomial polynomial on a short arc -/

/-- Upper half of the binomial expansion of `(z + (1 − z))^{2m₀}`:
`P_{m₀}(z) = ∑_{m = m₀}^{2m₀} C(2m₀, m) z^m (1 − z)^{2m₀ − m}`. -/
def highFreqPoly (m₀ : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc m₀ (2 * m₀),
    (Nat.choose (2 * m₀) m : ℂ) * z ^ m * (1 - z) ^ (2 * m₀ - m)

/-- Monomial coefficient of `z^d` in `highFreqPoly m₀ z` for `m₀ ≤ d ≤ 2m₀`. -/
def highFreqCoeff (m₀ d : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m₀ d,
    (-1 : ℝ) ^ (d - m) * (Nat.choose (2 * m₀) m : ℝ) * (Nat.choose (2 * m₀ - m) (d - m) : ℝ)

theorem highFreqPoly_add_low (m₀ : ℕ) (z : ℂ) :
    (∑ m ∈ Finset.range m₀,
        (Nat.choose (2 * m₀) m : ℂ) * z ^ m * (1 - z) ^ (2 * m₀ - m)) +
      highFreqPoly m₀ z = 1 := by
  unfold highFreqPoly
  have hsplit : Finset.range (2 * m₀ + 1) =
      Finset.range m₀ ∪ Finset.Icc m₀ (2 * m₀) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.range m₀) (Finset.Icc m₀ (2 * m₀)) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_range, Finset.mem_Icc] at hm1 hm2
    omega
  rw [← Finset.sum_union hdisj, ← hsplit]
  have hbin := add_pow z (1 - z) (2 * m₀)
  rw [add_sub_cancel, one_pow] at hbin
  rw [← hbin]
  refine Finset.sum_congr rfl fun m _ => by ring

/-- On the arc `‖z‖ = 1, ‖1 − z‖ ≤ 1/4`, `highFreqPoly m₀ z` is within `1/4` of `1`. -/
theorem norm_one_sub_highFreqPoly_le (m₀ : ℕ) {z : ℂ} (hz : ‖z‖ = 1)
    (h1z : ‖1 - z‖ ≤ 1 / 4) :
    ‖1 - highFreqPoly m₀ z‖ ≤ 1 / 4 := by
  have heq : 1 - highFreqPoly m₀ z =
      ∑ m ∈ Finset.range m₀,
        (Nat.choose (2 * m₀) m : ℂ) * z ^ m * (1 - z) ^ (2 * m₀ - m) := by
    rw [← highFreqPoly_add_low m₀ z]
    ring
  rw [heq]
  calc ‖∑ m ∈ Finset.range m₀,
          (Nat.choose (2 * m₀) m : ℂ) * z ^ m * (1 - z) ^ (2 * m₀ - m)‖
      ≤ ∑ m ∈ Finset.range m₀,
          ‖(Nat.choose (2 * m₀) m : ℂ) * z ^ m * (1 - z) ^ (2 * m₀ - m)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range m₀,
          (Nat.choose (2 * m₀) m : ℝ) * (1 / 4 : ℝ) ^ (m₀ + 1) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm_lt : m < m₀ := Finset.mem_range.mp hm
        have hexp : m₀ + 1 ≤ 2 * m₀ - m := by omega
        rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, hz, one_pow, mul_one, norm_pow]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc ‖1 - z‖ ^ (2 * m₀ - m)
            ≤ (1 / 4 : ℝ) ^ (2 * m₀ - m) := pow_le_pow_left₀ (norm_nonneg _) h1z _
          _ ≤ (1 / 4 : ℝ) ^ (m₀ + 1) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
    _ = (∑ m ∈ Finset.range m₀, (Nat.choose (2 * m₀) m : ℝ)) * (1 / 4 : ℝ) ^ (m₀ + 1) := by
        rw [← Finset.sum_mul]
    _ ≤ (2 : ℝ) ^ (2 * m₀) * (1 / 4 : ℝ) ^ (m₀ + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hsub : Finset.range m₀ ⊆ Finset.range (2 * m₀ + 1) :=
          Finset.range_mono (by omega)
        calc ∑ m ∈ Finset.range m₀, (Nat.choose (2 * m₀) m : ℝ)
            ≤ ∑ m ∈ Finset.range (2 * m₀ + 1), (Nat.choose (2 * m₀) m : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
          _ = ((∑ m ∈ Finset.range (2 * m₀ + 1), Nat.choose (2 * m₀) m : ℕ) : ℝ) := by
              push_cast; rfl
          _ = (2 : ℝ) ^ (2 * m₀) := by
              rw [Nat.sum_range_choose]; push_cast; rfl
    _ = 1 / 4 := by
        rw [pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ]
        have h4 : (4 : ℝ) ^ m₀ * (1 / 4 : ℝ) ^ m₀ = 1 := by
          rw [← mul_pow]; norm_num
        calc (4 : ℝ) ^ m₀ * ((1 / 4 : ℝ) ^ m₀ * (1 / 4))
            = ((4 : ℝ) ^ m₀ * (1 / 4 : ℝ) ^ m₀) * (1 / 4) := by ring
          _ = 1 / 4 := by rw [h4, one_mul]

/-- On the arc `‖z‖ = 1, ‖1 − z‖ ≤ 1/4`, `Re (highFreqPoly m₀ z) ≥ 3/4`. -/
theorem three_quarters_le_re_highFreqPoly (m₀ : ℕ) {z : ℂ} (hz : ‖z‖ = 1)
    (h1z : ‖1 - z‖ ≤ 1 / 4) :
    3 / 4 ≤ (highFreqPoly m₀ z).re := by
  have h1 : (1 - highFreqPoly m₀ z).re ≤ 1 / 4 :=
    (Complex.re_le_norm _).trans (norm_one_sub_highFreqPoly_le m₀ hz h1z)
  rw [Complex.sub_re, Complex.one_re] at h1
  linarith

/-- Monomial expansion of `highFreqPoly m₀ z` in powers `z^d` for `m₀ ≤ d ≤ 2m₀`. -/
theorem highFreqPoly_eq_sum_monomial (m₀ : ℕ) (z : ℂ) :
    highFreqPoly m₀ z =
      ∑ d ∈ Finset.Icc m₀ (2 * m₀), (highFreqCoeff m₀ d : ℂ) * z ^ d := by
  unfold highFreqPoly highFreqCoeff
  have hexp : ∀ m ∈ Finset.Icc m₀ (2 * m₀),
      (Nat.choose (2 * m₀) m : ℂ) * z ^ m * (1 - z) ^ (2 * m₀ - m) =
        ∑ d ∈ Finset.Icc m (2 * m₀),
          ((-1 : ℂ) ^ (d - m) * (Nat.choose (2 * m₀) m : ℂ) *
            (Nat.choose (2 * m₀ - m) (d - m) : ℂ)) * z ^ d := by
    intro m hm
    have hm_hi : m ≤ 2 * m₀ := (Finset.mem_Icc.mp hm).2
    have hsub : (1 - z) ^ (2 * m₀ - m) =
        ∑ j ∈ Finset.range (2 * m₀ - m + 1),
          (-1 : ℂ) ^ j * (Nat.choose (2 * m₀ - m) j : ℂ) * z ^ j := by
      rw [show (1 - z : ℂ) = -z + 1 by ring, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_pow, mul_one, show (-z : ℂ) = (-1 : ℂ) * z by ring, mul_pow]
      ring
    rw [hsub, Finset.mul_sum]
    have hbij : (∑ d ∈ Finset.Icc m (2 * m₀),
        ((-1 : ℂ) ^ (d - m) * (Nat.choose (2 * m₀) m : ℂ) *
          (Nat.choose (2 * m₀ - m) (d - m) : ℂ)) * z ^ d) =
        ∑ j ∈ Finset.range (2 * m₀ - m + 1),
          (Nat.choose (2 * m₀) m : ℂ) * z ^ m *
            ((-1 : ℂ) ^ j * (Nat.choose (2 * m₀ - m) j : ℂ) * z ^ j) := by
      have hIcc : Finset.Icc m (2 * m₀) = Finset.Ico m (2 * m₀ + 1) := rfl
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      rw [show 2 * m₀ + 1 - m = 2 * m₀ - m + 1 by omega]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.add_sub_cancel_left, pow_add]
      ring
    exact hbij.symm
  rw [Finset.sum_congr rfl hexp]
  -- Swap triangular double sum `m₀ ≤ m ≤ d ≤ 2m₀`
  let S := (Finset.Icc m₀ (2 * m₀) ×ˢ Finset.Icc m₀ (2 * m₀)).filter fun p => p.1 ≤ p.2
  let f : ℕ × ℕ → ℂ := fun p =>
    ((-1 : ℂ) ^ (p.2 - p.1) * (Nat.choose (2 * m₀) p.1 : ℂ) *
      (Nat.choose (2 * m₀ - p.1) (p.2 - p.1) : ℂ)) * z ^ p.2
  have hL : (∑ m ∈ Finset.Icc m₀ (2 * m₀), ∑ d ∈ Finset.Icc m (2 * m₀), f (m, d)) =
      ∑ p ∈ S, f p := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_lo : m₀ ≤ m := (Finset.mem_Icc.mp hm).1
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  have hR : (∑ d ∈ Finset.Icc m₀ (2 * m₀), ∑ m ∈ Finset.Icc m₀ d, f (m, d)) =
      ∑ p ∈ S, f p := by
    rw [Finset.sum_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_hi : d ≤ 2 * m₀ := (Finset.mem_Icc.mp hd).2
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  change (∑ m ∈ Finset.Icc m₀ (2 * m₀), ∑ d ∈ Finset.Icc m (2 * m₀), f (m, d)) = _
  rw [hL, ← hR]
  refine Finset.sum_congr rfl fun d _ => ?_
  push_cast
  rw [Finset.sum_mul]
  rfl

/-- Elementary upper bound `|highFreqCoeff m₀ d| ≤ 64^{m₀}` for `m₀ ≥ 1` and `d ≤ 2m₀`. -/
theorem abs_highFreqCoeff_le {m₀ d : ℕ} (hm₀ : 1 ≤ m₀) (hd : d ≤ 2 * m₀) :
    |highFreqCoeff m₀ d| ≤ (64 : ℝ) ^ m₀ := by
  unfold highFreqCoeff
  have hbin : ∀ n k : ℕ, (Nat.choose n k : ℝ) ≤ (2 : ℝ) ^ n := by
    intro n k
    by_cases hk : k ≤ n
    · have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hle : Nat.choose n k ≤ ∑ i ∈ Finset.range (n + 1), Nat.choose n i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      rw [Nat.sum_range_choose] at hle
      exact_mod_cast hle
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
      positivity
  calc |∑ m ∈ Finset.Icc m₀ d,
          (-1 : ℝ) ^ (d - m) * (Nat.choose (2 * m₀) m : ℝ) *
            (Nat.choose (2 * m₀ - m) (d - m) : ℝ)|
      ≤ ∑ m ∈ Finset.Icc m₀ d,
          |(-1 : ℝ) ^ (d - m) * (Nat.choose (2 * m₀) m : ℝ) *
            (Nat.choose (2 * m₀ - m) (d - m) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.Icc m₀ d, ((4 : ℝ) ^ m₀ * (4 : ℝ) ^ m₀) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
        have h1 : (Nat.choose (2 * m₀) m : ℝ) ≤ (4 : ℝ) ^ m₀ := by
          calc (Nat.choose (2 * m₀) m : ℝ) ≤ (2 : ℝ) ^ (2 * m₀) := hbin (2 * m₀) m
            _ = (4 : ℝ) ^ m₀ := by rw [pow_mul]; norm_num
        have h2 : (Nat.choose (2 * m₀ - m) (d - m) : ℝ) ≤ (4 : ℝ) ^ m₀ := by
          calc (Nat.choose (2 * m₀ - m) (d - m) : ℝ)
              ≤ (2 : ℝ) ^ (2 * m₀ - m) := hbin (2 * m₀ - m) (d - m)
            _ ≤ (2 : ℝ) ^ (2 * m₀) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = (4 : ℝ) ^ m₀ := by rw [pow_mul]; norm_num
        exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
    _ = ((Finset.Icc m₀ d).card : ℝ) * ((4 : ℝ) ^ m₀ * (4 : ℝ) ^ m₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 : ℝ) ^ m₀ * ((4 : ℝ) ^ m₀ * (4 : ℝ) ^ m₀) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hcard : (Finset.Icc m₀ d).card ≤ 2 * m₀ := by
          rw [Nat.card_Icc]; omega
        have hpow : 2 * m₀ ≤ 4 ^ m₀ := by
          induction m₀ with
          | zero => omega
          | succ n ih =>
            rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn
            · norm_num
            · have := ih hn
              rw [pow_succ]
              omega
        exact_mod_cast hcard.trans hpow
    _ = (64 : ℝ) ^ m₀ := by
        rw [← mul_pow, ← mul_pow]
        norm_num

/-! ### Chord bound and cosine polynomial positivity on `[-R, R]` -/

/-- For every real angle `θ`, `‖1 − e^{iθ}‖ ≤ |θ|`. -/
theorem norm_one_sub_exp_I_le (θ : ℝ) :
    ‖(1 : ℂ) - cexp ((θ : ℂ) * I)‖ ≤ |θ| := by
  have hsq : ‖(1 : ℂ) - cexp ((θ : ℂ) * I)‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
      Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_sub]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h1 := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h1
      linarith [Real.sin_sq_add_cos_sq (θ / 2)]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h1 : ‖(1 : ℂ) - cexp ((θ : ℂ) * I)‖ = |2 * Real.sin (θ / 2)| := by
    have := sq_eq_sq_iff_abs_eq_abs.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  rw [h1, abs_mul, abs_two, ← abs_div, abs_two]
  have hsin := Real.abs_sin_le_abs (θ / 2)
  linarith

/-- For `|v| ≤ R` (`R > 0`) and step `δ = 1 / (4 R)`, the cosine sum with coefficients
`highFreqCoeff m₀ d` stays at least `3 / 4`. -/
theorem three_quarters_le_sum_highFreqCoeff_cos (m₀ : ℕ) {R v : ℝ} (hR : 0 < R)
    (hv : |v| ≤ R) :
    3 / 4 ≤ ∑ d ∈ Finset.Icc m₀ (2 * m₀),
      highFreqCoeff m₀ d * Real.cos ((d : ℝ) * (1 / (4 * R)) * v) := by
  set z : ℂ := cexp (((1 / (4 * R)) * v : ℝ) * I)
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have h1z : ‖1 - z‖ ≤ 1 / 4 := by
    refine (norm_one_sub_exp_I_le ((1 / (4 * R)) * v)).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (4 * R))]
    calc (1 / (4 * R)) * |v| ≤ (1 / (4 * R)) * R :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ = 1 / 4 := by field_simp
  have hre := three_quarters_le_re_highFreqPoly m₀ hz h1z
  rw [highFreqPoly_eq_sum_monomial, Complex.re_sum] at hre
  refine hre.trans (le_of_eq (Finset.sum_congr rfl fun d _ => ?_))
  have hpow : z ^ d = cexp (((d : ℝ) * (1 / (4 * R)) * v : ℝ) * I) := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-! ### Spline transform norm bounds and Lipschitz continuity at general real frequencies -/

/-- Spectral point `γ − ix` for a general real ordinate `γ`. -/
def generalSplinePoint (γ x : ℝ) : ℂ := (γ : ℂ) - (x : ℂ) * I

@[simp] theorem generalSplinePoint_re (γ x : ℝ) : (generalSplinePoint γ x).re = γ := by
  simp [generalSplinePoint]

@[simp] theorem generalSplinePoint_im (γ x : ℝ) : (generalSplinePoint γ x).im = -x := by
  simp [generalSplinePoint]

theorem norm_generalSplinePoint_ge {γ : ℝ} (hγ : 0 ≤ γ) (x : ℝ) :
    γ ≤ ‖generalSplinePoint γ x‖ := by
  have h := Complex.abs_re_le_norm (generalSplinePoint γ x)
  rwa [generalSplinePoint_re, abs_of_nonneg hγ] at h

theorem norm_generalSplinePoint_le {γ x : ℝ} (hγ : 0 ≤ γ) (hx : 0 ≤ x) :
    ‖generalSplinePoint γ x‖ ≤ γ + x := by
  have h := Complex.norm_le_abs_re_add_abs_im (generalSplinePoint γ x)
  rwa [generalSplinePoint_re, generalSplinePoint_im, abs_of_nonneg hγ, abs_neg,
    abs_of_nonneg hx] at h

theorem generalSplinePoint_ne_zero {γ : ℝ} (hγ : 0 < γ) (x : ℝ) :
    generalSplinePoint γ x ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [generalSplinePoint_re, Complex.zero_re] at this
  linarith

theorem norm_sin_generalSplinePoint_sq (γ x : ℝ) :
    ‖Complex.sin (generalSplinePoint γ x)‖ ^ 2 =
      Real.sin γ ^ 2 * Real.cosh x ^ 2 + Real.cos γ ^ 2 * Real.sinh x ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, generalSplinePoint, Complex.sin_sub,
    Complex.sin_ofReal_re, Complex.cos_ofReal_re]
  have h1 : Complex.sin ((x : ℂ) * I) = (Real.sinh x : ℂ) * I := by
    rw [Complex.sin_mul_I, Complex.ofReal_sinh]
  have h2 : Complex.cos ((x : ℂ) * I) = (Real.cosh x : ℂ) := by
    rw [Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [h1, h2]
  have hsplit : Complex.sin (γ : ℂ) * (Real.cosh x : ℂ) -
      Complex.cos (γ : ℂ) * ((Real.sinh x : ℂ) * I) =
      ((Real.sin γ * Real.cosh x : ℝ) : ℂ) +
        ((-Real.cos γ * Real.sinh x : ℝ) : ℂ) * I := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    push_cast
    ring
  rw [hsplit, Complex.normSq_add_mul_I]
  ring

theorem norm_cos_generalSplinePoint_sq (γ x : ℝ) :
    ‖Complex.cos (generalSplinePoint γ x)‖ ^ 2 =
      Real.cos γ ^ 2 * Real.cosh x ^ 2 + Real.sin γ ^ 2 * Real.sinh x ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, generalSplinePoint, Complex.cos_sub]
  have h1 : Complex.sin ((x : ℂ) * I) = (Real.sinh x : ℂ) * I := by
    rw [Complex.sin_mul_I, Complex.ofReal_sinh]
  have h2 : Complex.cos ((x : ℂ) * I) = (Real.cosh x : ℂ) := by
    rw [Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [h1, h2]
  have hsplit : Complex.cos (γ : ℂ) * (Real.cosh x : ℂ) +
      Complex.sin (γ : ℂ) * ((Real.sinh x : ℂ) * I) =
      ((Real.cos γ * Real.cosh x : ℝ) : ℂ) +
        ((Real.sin γ * Real.sinh x : ℝ) : ℂ) * I := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    push_cast
    ring
  rw [hsplit, Complex.normSq_add_mul_I]
  ring

theorem sinh_le_norm_sin_generalSplinePoint (γ : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ ‖Complex.sin (generalSplinePoint γ x)‖ := by
  have hsq : Real.sinh x ^ 2 ≤ ‖Complex.sin (generalSplinePoint γ x)‖ ^ 2 := by
    rw [norm_sin_generalSplinePoint_sq]
    have hcs := Real.cosh_sq_sub_sinh_sq x
    have hsc := Real.sin_sq_add_cos_sq γ
    have hsin0 : 0 ≤ Real.sin γ ^ 2 := sq_nonneg _
    nlinarith
  have hsinh0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
  nlinarith [norm_nonneg (Complex.sin (generalSplinePoint γ x))]

theorem norm_sin_generalSplinePoint_le_cosh (γ x : ℝ) :
    ‖Complex.sin (generalSplinePoint γ x)‖ ≤ Real.cosh x := by
  have hsq : ‖Complex.sin (generalSplinePoint γ x)‖ ^ 2 ≤ Real.cosh x ^ 2 := by
    rw [norm_sin_generalSplinePoint_sq]
    have hcs := Real.cosh_sq_sub_sinh_sq x
    have hsc := Real.sin_sq_add_cos_sq γ
    have hcos0 : 0 ≤ Real.cos γ ^ 2 := sq_nonneg _
    nlinarith
  have hcosh0 : 0 < Real.cosh x := Real.cosh_pos x
  nlinarith [norm_nonneg (Complex.sin (generalSplinePoint γ x))]

theorem norm_cos_generalSplinePoint_le_cosh (γ x : ℝ) :
    ‖Complex.cos (generalSplinePoint γ x)‖ ≤ Real.cosh x := by
  have hsq : ‖Complex.cos (generalSplinePoint γ x)‖ ^ 2 ≤ Real.cosh x ^ 2 := by
    rw [norm_cos_generalSplinePoint_sq]
    have hcs := Real.cosh_sq_sub_sinh_sq x
    have hsc := Real.sin_sq_add_cos_sq γ
    have hsin0 : 0 ≤ Real.sin γ ^ 2 := sq_nonneg _
    nlinarith
  have hcosh0 : 0 < Real.cosh x := Real.cosh_pos x
  nlinarith [norm_nonneg (Complex.cos (generalSplinePoint γ x))]

theorem cosh_le_two_of_le_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.cosh x ≤ 2 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  linarith

theorem norm_sincC_generalSplinePoint_le {γ x : ℝ} (hγ : 2 ≤ γ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / 2) :
    ‖sincC (generalSplinePoint γ x)‖ ≤ 2 / γ := by
  rw [sincC, if_neg (generalSplinePoint_ne_zero (by linarith) x), norm_div]
  have hnum : ‖Complex.sin (generalSplinePoint γ x)‖ ≤ 2 :=
    (norm_sin_generalSplinePoint_le_cosh γ x).trans (cosh_le_two_of_le_half hx0 hx1)
  have hden : γ ≤ ‖generalSplinePoint γ x‖ := norm_generalSplinePoint_ge (by linarith) x
  have hpos : 0 < ‖generalSplinePoint γ x‖ := by linarith
  exact (div_le_div_of_nonneg_right hnum hpos.le).trans
    (div_le_div_of_nonneg_left (by norm_num) (by linarith) hden)

theorem norm_sincC_generalSplinePoint_le_one {γ x : ℝ} (hγ : 2 ≤ γ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / 2) :
    ‖sincC (generalSplinePoint γ x)‖ ≤ 1 :=
  (norm_sincC_generalSplinePoint_le hγ hx0 hx1).trans ((div_le_one (by linarith)).mpr hγ)

theorem norm_sincC_generalSplinePoint_pow_eight_le {γ x : ℝ} (hγ : 2 ≤ γ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / 2) :
    ‖sincC (generalSplinePoint γ x) ^ 8‖ ≤ (2 / γ) ^ 8 := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sincC_generalSplinePoint_le hγ hx0 hx1) 8

theorem norm_sincC_generalSplinePoint_pow_eight_ge {Γ γ x : ℝ} (hΓ : 1 ≤ Γ)
    (hγlo : Γ ≤ γ) (hγhi : γ ≤ 3 * Γ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (x / (4 * Γ)) ^ 8 ≤ ‖sincC (generalSplinePoint γ x) ^ 8‖ := by
  rw [norm_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 8
  rw [sincC, if_neg (generalSplinePoint_ne_zero (by linarith) x), norm_div]
  have hnum : x ≤ ‖Complex.sin (generalSplinePoint γ x)‖ :=
    (Real.self_le_sinh_iff.mpr hx0).trans (sinh_le_norm_sin_generalSplinePoint γ hx0)
  have hden : ‖generalSplinePoint γ x‖ ≤ 4 * Γ := by
    calc ‖generalSplinePoint γ x‖ ≤ γ + x :=
          norm_generalSplinePoint_le (by linarith) hx0
      _ ≤ 4 * Γ := by linarith
  have hpos : 0 < ‖generalSplinePoint γ x‖ :=
    ( by linarith : 0 < γ ).trans_le (norm_generalSplinePoint_ge (by linarith) x)
  exact (div_le_div_of_nonneg_left hx0 hpos hden).trans
    (div_le_div_of_nonneg_right hnum hpos.le)

/-- General power-difference bound `‖a^n − b^n‖ ≤ n ‖a − b‖` for `‖a‖, ‖b‖ ≤ 1`. -/
theorem norm_pow_sub_pow_le_of_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    calc ‖a * (a ^ n - b ^ n) + (a - b) * b ^ n‖
        ≤ ‖a * (a ^ n - b ^ n)‖ + ‖(a - b) * b ^ n‖ := norm_add_le _ _
      _ = ‖a‖ * ‖a ^ n - b ^ n‖ + ‖a - b‖ * ‖b‖ ^ n := by
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ 1 * ((n : ℝ) * ‖a - b‖) + ‖a - b‖ * 1 := by
          refine add_le_add (mul_le_mul ha ih (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _))
      _ = ((n + 1 : ℕ) : ℝ) * ‖a - b‖ := by push_cast; ring

/-- Lipschitz bound on `sincC (generalSplinePoint γ x) ^ 8` under a real frequency shift `η ≥ 0`. -/
theorem norm_sincC_pow_eight_shift_sub_le {γ η x : ℝ} (hγ : 4 ≤ γ) (hη : 0 ≤ η)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    ‖sincC (generalSplinePoint (γ + η) x) ^ 8 - sincC (generalSplinePoint γ x) ^ 8‖ ≤ 8 * η := by
  set z₁ := generalSplinePoint (γ + η) x
  set z₂ := generalSplinePoint γ x
  have h1 : ‖sincC z₁‖ ≤ 1 := norm_sincC_generalSplinePoint_le_one (by linarith) hx0 hx1
  have h2 : ‖sincC z₂‖ ≤ 1 := norm_sincC_generalSplinePoint_le_one (by linarith) hx0 hx1
  have hpow := norm_pow_sub_pow_le_of_norm_le_one h1 h2 8
  push_cast at hpow
  refine hpow.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hz10 : z₁ ≠ 0 := generalSplinePoint_ne_zero (by linarith) x
  have hz20 : z₂ ≠ 0 := generalSplinePoint_ne_zero (by linarith) x
  have hnz1 : 4 ≤ ‖z₁‖ := (by linarith : 4 ≤ γ + η).trans (norm_generalSplinePoint_ge (by linarith) x)
  have hnz2 : 4 ≤ ‖z₂‖ := hγ.trans (norm_generalSplinePoint_ge (by linarith) x)
  rw [sincC, if_neg hz10, sincC, if_neg hz20]
  have hdiff : Complex.sin z₁ / z₁ - Complex.sin z₂ / z₂ =
      (Complex.sin z₁ - Complex.sin z₂) / z₁ + Complex.sin z₂ * (z₂ - z₁) / (z₁ * z₂) := by
    field_simp
    ring
  have hsub_z : z₁ - z₂ = (η : ℂ) := by
    dsimp only [z₁, z₂, generalSplinePoint]
    push_cast
    ring
  have hsub_z' : z₂ - z₁ = -(η : ℂ) := by rw [← neg_sub, hsub_z]
  have hadd_z : (z₁ + z₂) / 2 = generalSplinePoint (γ + η / 2) x := by
    dsimp only [z₁, z₂, generalSplinePoint]
    push_cast
    ring
  have hsin_diff : ‖Complex.sin z₁ - Complex.sin z₂‖ ≤ 2 * η := by
    rw [Complex.sin_sub_sin, hsub_z, hadd_z]
    rw [show (η : ℂ) / 2 = ((η / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin]
    rw [norm_mul, norm_mul, norm_two, Complex.norm_real, Real.norm_eq_abs]
    have hsin : |Real.sin (η / 2)| ≤ η / 2 := by
      refine (Real.abs_sin_le_abs (η / 2)).trans ?_
      rw [abs_of_nonneg (by positivity)]
    have hcos : ‖Complex.cos (generalSplinePoint (γ + η / 2) x)‖ ≤ 2 :=
      (norm_cos_generalSplinePoint_le_cosh _ _).trans (cosh_le_two_of_le_half hx0 hx1)
    nlinarith [norm_nonneg (Complex.cos (generalSplinePoint (γ + η / 2) x))]
  have hsin2 : ‖Complex.sin z₂‖ ≤ 2 :=
    (norm_sin_generalSplinePoint_le_cosh _ _).trans (cosh_le_two_of_le_half hx0 hx1)
  rw [hdiff]
  calc ‖(Complex.sin z₁ - Complex.sin z₂) / z₁ + Complex.sin z₂ * (z₂ - z₁) / (z₁ * z₂)‖
      ≤ ‖(Complex.sin z₁ - Complex.sin z₂) / z₁‖ +
          ‖Complex.sin z₂ * (z₂ - z₁) / (z₁ * z₂)‖ := norm_add_le _ _
    _ = ‖Complex.sin z₁ - Complex.sin z₂‖ / ‖z₁‖ +
          (‖Complex.sin z₂‖ * η) / (‖z₁‖ * ‖z₂‖) := by
        rw [norm_div, norm_div, norm_mul, norm_mul, hsub_z', norm_neg,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη]
    _ ≤ (2 * η) / 4 + (2 * η) / 16 := by
        refine add_le_add ?_ ?_
        · exact (div_le_div_of_nonneg_right hsin_diff (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by norm_num) hnz1)
        · have h16 : 16 ≤ ‖z₁‖ * ‖z₂‖ := by nlinarith
          have hnum : ‖Complex.sin z₂‖ * η ≤ 2 * η :=
            mul_le_mul_of_nonneg_right hsin2 hη
          exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by norm_num) h16)
    _ ≤ η := by linarith

/-! ### Phase-aligned frequency perturbation and pair synthesis -/

/-- Frequency perturbation `η(γ, ψ, s, T) ∈ (2πs/T, 2π(s+1)/T]` aligning `(γ + η) T ≡ ψ (mod 2π)`. -/
def phaseShift (γ ψ : ℝ) (s : ℕ) (T : ℝ) : ℝ :=
  (2 * Real.pi * ((⌊(γ * T - ψ) / (2 * Real.pi)⌋ : ℝ) + (s : ℝ) + 1) + ψ - γ * T) / T

theorem phaseShift_gt (γ ψ : ℝ) (s : ℕ) {T : ℝ} (hT : 0 < T) :
    2 * Real.pi * (s : ℝ) / T < phaseShift γ ψ s T := by
  unfold phaseShift
  rw [div_lt_div_iff_of_pos_right hT]
  have hfl := Int.sub_one_lt_floor ((γ * T - ψ) / (2 * Real.pi))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hmul := ( lt_div_iff₀ hpi ).mp (by linarith :
    (γ * T - ψ) / (2 * Real.pi) - 1 < (⌊(γ * T - ψ) / (2 * Real.pi)⌋ : ℝ))
  nlinarith

theorem phaseShift_le (γ ψ : ℝ) (s : ℕ) {T : ℝ} (hT : 0 < T) :
    phaseShift γ ψ s T ≤ 2 * Real.pi * ((s : ℝ) + 1) / T := by
  unfold phaseShift
  rw [div_le_div_iff_of_pos_right hT]
  have hfl := Int.floor_le ((γ * T - ψ) / (2 * Real.pi))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hmul := (div_le_iff₀ hpi).mp hfl
  nlinarith

theorem cexp_add_phaseShift_mul_T (γ ψ : ℝ) (s : ℕ) {T : ℝ} (hT : 0 < T) :
    cexp ((((γ + phaseShift γ ψ s T) * T : ℝ) : ℂ) * I) = cexp ((ψ : ℂ) * I) := by
  set n : ℤ := ⌊(γ * T - ψ) / (2 * Real.pi)⌋ + (s : ℤ) + 1
  have hId : (γ + phaseShift γ ψ s T) * T = ψ + (n : ℝ) * (2 * Real.pi) := by
    unfold phaseShift
    dsimp only [n]
    push_cast
    field_simp [hT.ne']
    ring
  rw [hId]
  have hsplit : (((ψ + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) =
      (ψ : ℂ) * I + (n : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Combined perturbation bound for `sinc(γ − ix)^8 e^{iγ(T + v)}` on `|v| ≤ R`. -/
theorem norm_shifted_mode_sub_ideal_le {γ ψ : ℝ} {s : ℕ} {T R x v : ℝ}
    (hγ : 4 ≤ γ) (hT : 0 < T) (hR : 0 ≤ R) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hv : |v| ≤ R) :
    ‖sincC (generalSplinePoint (γ + phaseShift γ ψ s T) x) ^ 8 *
        cexp ((((γ + phaseShift γ ψ s T) * (T + v) : ℝ) : ℂ) * I) -
      sincC (generalSplinePoint γ x) ^ 8 * cexp ((ψ : ℂ) * I) *
        cexp (((γ * v : ℝ) : ℂ) * I)‖ ≤
      (R + 8) * phaseShift γ ψ s T := by
  set η := phaseShift γ ψ s T
  have hη0 : 0 ≤ η := (by positivity : 0 ≤ 2 * Real.pi * (s : ℝ) / T).trans
    (phaseShift_gt γ ψ s hT).le
  have hexpT : cexp ((((γ + η) * (T + v) : ℝ) : ℂ) * I) =
      cexp ((ψ : ℂ) * I) * cexp (((γ * v : ℝ) : ℂ) * I) * cexp (((η * v : ℝ) : ℂ) * I) := by
    have h1 : (((γ + η) * (T + v) : ℝ) : ℂ) * I =
        ((((γ + η) * T : ℝ) : ℂ) * I) + (((γ * v : ℝ) : ℂ) * I) + (((η * v : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [h1, Complex.exp_add, Complex.exp_add, cexp_add_phaseShift_mul_T γ ψ s hT]
  rw [hexpT]
  set w₁ := sincC (generalSplinePoint (γ + η) x) ^ 8
  set w₀ := sincC (generalSplinePoint γ x) ^ 8
  set E₀ := cexp ((ψ : ℂ) * I) * cexp (((γ * v : ℝ) : ℂ) * I)
  set Eη := cexp (((η * v : ℝ) : ℂ) * I)
  have hE₀ : ‖E₀‖ = 1 := by
    dsimp only [E₀]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hEη : ‖Eη - 1‖ ≤ R * η := by
    dsimp only [Eη]
    rw [norm_sub_rev]
    refine (norm_one_sub_exp_I_le (η * v)).trans ?_
    rw [abs_mul, abs_of_nonneg hη0, mul_comm]
    exact mul_le_mul_of_nonneg_right hv hη0
  have hw₁ : ‖w₁‖ ≤ 1 := by
    dsimp only [w₁]
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _)
      (norm_sincC_generalSplinePoint_le_one (by linarith) hx0 hx1)
  have hw_diff : ‖w₁ - w₀‖ ≤ 8 * η :=
    norm_sincC_pow_eight_shift_sub_le hγ hη0 hx0 hx1
  have hsplit : w₁ * (E₀ * Eη) - w₀ * E₀ = w₁ * E₀ * (Eη - 1) + (w₁ - w₀) * E₀ := by ring
  calc ‖w₁ * (E₀ * Eη) - w₀ * E₀‖
      ≤ ‖w₁ * E₀ * (Eη - 1)‖ + ‖(w₁ - w₀) * E₀‖ := by rw [hsplit]; exact norm_add_le _ _
    _ = ‖w₁‖ * ‖E₀‖ * ‖Eη - 1‖ + ‖w₁ - w₀‖ * ‖E₀‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ 1 * 1 * (R * η) + (8 * η) * 1 := by
        rw [hE₀]
        refine add_le_add (mul_le_mul (mul_le_one₀ hw₁ (norm_nonneg _) le_rfl) hEη
          (norm_nonneg _) zero_le_one) (mul_le_mul_of_nonneg_right hw_diff zero_le_one)
    _ = (R + 8) * η := by ring

/-- Sign angle `0` for `a ≥ 0` and `π` for `a < 0`, satisfying `|a| e^{i θ_a} = a`. -/
def signAngle (a : ℝ) : ℝ := if 0 ≤ a then 0 else Real.pi

theorem abs_mul_cexp_signAngle (a : ℝ) :
    (|a| : ℂ) * cexp ((signAngle a : ℂ) * I) = (a : ℂ) := by
  unfold signAngle
  split_ifs with h
  · simp [abs_of_nonneg h]
  · push Not at h
    rw [abs_of_neg h, Complex.exp_pi_mul_I]
    push_cast
    ring

/-- **Exact phase-split pair identity.** For any `w ≠ 0`, amplitude scale `0 ≤ r₀ ≤ ‖w‖`, and
`|a| ≤ A` (`0 < A`), the sum of the two phase-split unit factors at `α = arccos(|a| r₀ / (A ‖w‖))`
cancels `w` and produces `(2 r₀ / A) a`. -/
theorem phase_split_pair_eq {w : ℂ} (hw : w ≠ 0) {r₀ a A : ℝ}
    (hr₀0 : 0 ≤ r₀) (hr₀ : r₀ ≤ ‖w‖) (hA : 0 < A) (ha : |a| ≤ A) :
    let b := (|a| / A) * (r₀ / ‖w‖)
    let α := Real.arccos b
    let ψ₁ := signAngle a - w.arg + α
    let ψ₂ := signAngle a - w.arg - α
    w * (cexp ((ψ₁ : ℂ) * I) + cexp ((ψ₂ : ℂ) * I)) =
      (((2 * r₀ / A) * a : ℝ) : ℂ) := by
  intro b α ψ₁ ψ₂
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp only [b]
    exact mul_le_one₀ ((div_le_one hA).mpr ha) (by positivity) ((div_le_one hwn).mpr hr₀)
  have hcos : Real.cos α = b := Real.cos_arccos (by linarith) hb1
  have hsum_exp : cexp ((ψ₁ : ℂ) * I) + cexp ((ψ₂ : ℂ) * I) =
      cexp (((signAngle a - w.arg : ℝ) : ℂ) * I) * ((2 * b : ℝ) : ℂ) := by
    dsimp only [ψ₁, ψ₂]
    have h1 : ((signAngle a - w.arg + α : ℝ) : ℂ) * I =
        (((signAngle a - w.arg : ℝ) : ℂ) * I) + ((α : ℂ) * I) := by push_cast; ring
    have h2 : ((signAngle a - w.arg - α : ℝ) : ℂ) * I =
        (((signAngle a - w.arg : ℝ) : ℂ) * I) - ((α : ℂ) * I) := by push_cast; ring
    rw [h1, h2, Complex.exp_add, Complex.exp_sub, ← hcos, Complex.ofReal_cos]
    field_simp [Complex.exp_ne_zero]
    ring
  rw [hsum_exp]
  have hw_polar := (Complex.norm_mul_exp_arg_mul_I w).symm
  have harg_cancel : cexp ((w.arg : ℂ) * I) * cexp (((signAngle a - w.arg : ℝ) : ℂ) * I) =
      cexp ((signAngle a : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc w * (cexp (((signAngle a - w.arg : ℝ) : ℂ) * I) * ((2 * b : ℝ) : ℂ))
      = (‖w‖ : ℂ) * (cexp ((w.arg : ℂ) * I) * cexp (((signAngle a - w.arg : ℝ) : ℂ) * I)) *
          ((2 * b : ℝ) : ℂ) := by
        conv_lhs => rw [hw_polar]
        ring
    _ = ((‖w‖ * (2 * b) : ℝ) : ℂ) * cexp ((signAngle a : ℂ) * I) := by
        rw [harg_cancel]
        push_cast
        ring
    _ = ((2 * r₀ / A : ℝ) : ℂ) * ((|a| : ℂ) * cexp ((signAngle a : ℂ) * I)) := by
        have hreal : ‖w‖ * (2 * b) = (2 * r₀ / A) * |a| := by
          dsimp only [b]
          field_simp [hwn.ne', hA.ne']
        rw [← mul_assoc, ← Complex.ofReal_mul, ← hreal, Complex.ofReal_mul]
    _ = (((2 * r₀ / A) * a : ℝ) : ℂ) := by
        rw [abs_mul_cexp_signAngle, Complex.ofReal_mul]

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
