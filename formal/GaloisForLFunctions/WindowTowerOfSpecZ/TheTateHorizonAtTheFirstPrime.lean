import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowFormIsTheDerivativeOfTheJordanCounts
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The Tate horizon at the first prime

On a window of the first stage, `log 2 < A < log 3`, only the folds `1` and `2` act, and the Tate
function is `τ_H(k) = ‖H‖² + (2^k − 1)2^{−1/2}∫H(u)H(u + log 2)` (`tateFunction_firstStage`). The
fold by `log 2 > A/2` couples the two disjoint collars of the window, so its correlation is at most
`‖H‖²/2` in absolute value (`abs_autocorr_le_half`); a test that is a bump on the left collar minus its translate on
the right collar attains `−‖H‖²/2` (`exists_tateFunction_neg_firstStage`). Hence the exact horizon:

**Theorem** (`tateFunction_nonneg_iff_firstStage`). On a first-stage window the Tate operator
`ρ_A(J_k)` is a positive form iff `2^k ≤ 1 + 2√2`, i.e. iff `k ≤ log₂(1 + 2√2) = 1.9367…`.

The extremal test lives on the atomic lattice of the window (one atom per collar, opposite signs):
at the first stage the atoms realize the horizon exactly. At later stages the window horizon is
smaller than the atomic one (numerically `k*(A) ≈ 1.66e^{−A/2}` against `≈ 1.56/log N` on atoms).
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory MeasureTheory Set

variable {A : ℝ} {H : ℝ → ℝ}

theorem windowLevel_eq_two (h1 : Real.log 2 ≤ A) (h2 : A < Real.log 3) : windowLevel A = 2 := by
  rw [windowLevel, Nat.floor_eq_iff (Real.exp_pos A).le]
  constructor
  · have := Real.exp_le_exp.mpr h1
    rw [Real.exp_log (by norm_num)] at this
    norm_num; exact this
  · have := Real.exp_lt_exp.mpr h2
    rw [Real.exp_log (by norm_num)] at this
    norm_num; exact this

/-- The Tate function on a first-stage window. -/
theorem tateFunction_firstStage (hH : IsWindowTest A H) (hlev : windowLevel A = 2) (k : ℝ) :
    tateFunction A H k = (∫ u, H u ^ 2) +
      ((2 : ℝ) ^ k - 1) / Real.sqrt 2 * ∫ u, H u * H (u + Real.log 2) := by
  rw [tateFunction_eq hH, hlev, show Finset.Icc 1 2 = {1, 2} by decide,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), jordanTotient_one]
  have h2 : jordanTotient k 2 = (2 : ℝ) ^ k - 1 := by
    have := jordanTotient_prime_pow Nat.prime_two k (a := 1) le_rfl
    simpa using this
  rw [h2]
  simp only [Nat.cast_one, Real.sqrt_one, div_one, one_mul, Real.log_one, add_zero, Nat.cast_ofNat]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp [sq])

/-- **A fold longer than half the window couples disjoint collars**: `|∫H(u)H(u + ℓ)| ≤ ‖H‖²/2`
for `A < 2ℓ`. -/
theorem abs_autocorr_le_half (hH : IsWindowTest A H) {ℓ : ℝ} (hℓ : A < 2 * ℓ) :
    |∫ u, H u * H (u + ℓ)| ≤ (∫ u, H u ^ 2) / 2 := by
  have hc := hH.continuous
  have iH : Integrable fun u => H u ^ 2 := _root_.RHTower.WeilMarkovPole.integrable_sq hc
    hH.hasCompactSupport
  set S : Set ℝ := Iic (-ℓ)
  set T : Set ℝ := Ici (ℓ - A)
  have iS : Integrable (S.indicator fun u => H u ^ 2) := iH.indicator measurableSet_Iic
  have iT : Integrable (T.indicator fun u => H u ^ 2) := iH.indicator measurableSet_Ici
  have iT' : Integrable fun u => T.indicator (fun u => H u ^ 2) (u + ℓ) := iT.comp_add_right ℓ
  have iX : Integrable fun u =>
      (S.indicator (fun u => H u ^ 2) u + T.indicator (fun u => H u ^ 2) (u + ℓ)) / 2 :=
    (iS.add iT').div_const 2
  have iP : Integrable fun u => H u * H (u + ℓ) :=
    (hc.mul (hc.comp (continuous_add_const ℓ))).integrable_of_hasCompactSupport
      hH.hasCompactSupport.mul_right
  -- pointwise: the product is supported where `u ∈ S` and `u + ℓ ∈ T`
  have hpt : ∀ u, |H u * H (u + ℓ)| ≤
      (S.indicator (fun u => H u ^ 2) u + T.indicator (fun u => H u ^ 2) (u + ℓ)) / 2 := fun u => by
    have hX : 0 ≤ S.indicator (fun u => H u ^ 2) u + T.indicator (fun u => H u ^ 2) (u + ℓ) :=
      add_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) _)
        (indicator_nonneg (fun _ _ => sq_nonneg _) _)
    by_cases h1 : H u = 0
    · rw [h1, zero_mul, abs_zero]; linarith
    by_cases h2 : H (u + ℓ) = 0
    · rw [h2, mul_zero, abs_zero]; linarith
    have hu : u ∈ Icc (-A) 0 := by by_contra h; exact h1 (hH.vanish u h)
    have hu' : u + ℓ ∈ Icc (-A) 0 := by by_contra h; exact h2 (hH.vanish _ h)
    rw [indicator_of_mem (show u ∈ S from mem_Iic.mpr (by linarith [hu'.2])),
      indicator_of_mem (show u + ℓ ∈ T from mem_Ici.mpr (by linarith [hu.1])), abs_le]
    constructor <;> nlinarith [sq_nonneg (H u + H (u + ℓ)), sq_nonneg (H u - H (u + ℓ))]
  have hX : ∫ u, (S.indicator (fun u => H u ^ 2) u + T.indicator (fun u => H u ^ 2) (u + ℓ)) / 2 =
      ((∫ u, S.indicator (fun u => H u ^ 2) u) + ∫ u, T.indicator (fun u => H u ^ 2) u) / 2 := by
    rw [integral_div, integral_add iS iT',
      integral_add_right_eq_self (fun u => T.indicator (fun u => H u ^ 2) u) ℓ]
  -- the collars are disjoint inside the window
  have hdisj : (∫ u, S.indicator (fun u => H u ^ 2) u) + ∫ u, T.indicator (fun u => H u ^ 2) u ≤
      ∫ u, H u ^ 2 := by
    rw [← integral_add iS iT]
    refine integral_mono (iS.add iT) iH fun u => ?_
    by_cases hu : u ∈ Icc (-A) 0
    · by_cases hS : u ∈ S
      · have hT : u ∉ T := fun hT => by
          have := mem_Iic.mp hS; have := mem_Ici.mp hT; linarith
        rw [indicator_of_mem hS, indicator_of_notMem hT, add_zero]
      · rw [indicator_of_notMem hS, zero_add]
        exact indicator_le_self' (fun _ _ => sq_nonneg _) u
    · have h0 : H u = 0 := hH.vanish u hu
      simp [Set.indicator_apply, h0]
  have := (abs_integral_le_integral_abs (f := fun u => H u * H (u + ℓ))).trans
    (integral_mono iP.abs iX hpt)
  rw [hX] at this
  linarith

/-- **Positivity below the first horizon**: on a first-stage window, `τ_H(k) ≥ 0` whenever
`2^k ≤ 1 + 2√2`. -/
theorem tateFunction_nonneg_firstStage (hH : IsWindowTest A H) (hlev : windowLevel A = 2)
    (hA : A < 2 * Real.log 2) {k : ℝ} (hk : (2 : ℝ) ^ k ≤ 1 + 2 * Real.sqrt 2) :
    0 ≤ tateFunction A H k := by
  rw [tateFunction_firstStage hH hlev]
  have habs := abs_le.mp (abs_autocorr_le_half hH hA)
  have hc := habs.1
  have hs : 0 < Real.sqrt 2 := by positivity
  have hpos : 0 < (2 : ℝ) ^ k := Real.rpow_pos_of_pos (by norm_num) k
  have hn : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hc' := habs.2
  rcases le_or_gt 1 ((2 : ℝ) ^ k) with h1 | h1
  · -- `0 ≤ 2^k − 1 ≤ 2√2`
    have hq : ((2 : ℝ) ^ k - 1) / Real.sqrt 2 ≤ 2 := by
      rw [div_le_iff₀ hs]; linarith
    have hq0 : 0 ≤ ((2 : ℝ) ^ k - 1) / Real.sqrt 2 := div_nonneg (by linarith) hs.le
    nlinarith [mul_le_mul_of_nonneg_left hc hq0]
  · -- `−1 < 2^k − 1 < 0` and `√2 > 1`
    have hq : -1 ≤ ((2 : ℝ) ^ k - 1) / Real.sqrt 2 := by
      rw [le_div_iff₀ hs]; nlinarith [Real.one_lt_sqrt_two]
    have hq0 : ((2 : ℝ) ^ k - 1) / Real.sqrt 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le
    nlinarith [mul_le_mul_of_nonpos_left hc' hq0]

/-- **The horizon is attained**: past `2^k = 1 + 2√2`, a bump on the left collar minus its translate
on the right collar has negative Tate function. -/
theorem exists_tateFunction_neg_firstStage (hA1 : Real.log 2 < A) (hlev : windowLevel A = 2)
    (hA : A < 2 * Real.log 2) {k : ℝ} (hk : 1 + 2 * Real.sqrt 2 < (2 : ℝ) ^ k) :
    ∃ H, IsWindowTest A H ∧ tateFunction A H k < 0 := by
  set ℓ := Real.log 2
  set c : ℝ := (-A - ℓ) / 2
  have hr : 0 < (A - ℓ) / 4 := by linarith
  let φ : ContDiffBump c := ⟨(A - ℓ) / 4, (A - ℓ) / 2, hr, by linarith⟩
  -- the bump lives on the open left collar `(−A, −ℓ)`
  have hsupp : ∀ u, φ u ≠ 0 → -A < u ∧ u < -ℓ := fun u hu => by
    have : u ∈ Function.support φ := hu
    rw [φ.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at this
    have hro : φ.rOut = (A - ℓ) / 2 := rfl
    have hcc : c = (-A - ℓ) / 2 := rfl
    rw [hro, hcc] at this
    constructor <;> linarith [this.1, this.2]
  set H : ℝ → ℝ := fun u => φ u - φ (u - ℓ)
  have hφc : Continuous φ := φ.continuous
  have hH : IsWindowTest A H := by
    refine ⟨φ.contDiff.sub (φ.contDiff.comp (contDiff_id.sub contDiff_const)), fun y hy => ?_⟩
    have h1 : φ y = 0 := by
      by_contra h; obtain ⟨a, b⟩ := hsupp y h; exact hy ⟨by linarith, by linarith⟩
    have h2 : φ (y - ℓ) = 0 := by
      by_contra h; obtain ⟨a, b⟩ := hsupp _ h; exact hy ⟨by linarith, by linarith⟩
    simp only [H, h1, h2, sub_zero]
  -- disjointness of the translates
  have hℓ : 0 < ℓ := Real.log_pos (by norm_num)
  have hz : ∀ u t, ℓ ≤ |t| → φ u * φ (u + t) = 0 := fun u t ht => by
    by_contra h
    obtain ⟨a1, b1⟩ := hsupp u (left_ne_zero_of_mul h)
    obtain ⟨a2, b2⟩ := hsupp _ (right_ne_zero_of_mul h)
    have : |t| < ℓ := by rw [abs_lt]; constructor <;> linarith
    linarith
  have hsq : ∀ u, H u ^ 2 = φ u ^ 2 + φ (u - ℓ) ^ 2 := fun u => by
    have e : φ u * φ (u - ℓ) = 0 := by
      have := hz u (-ℓ) (by rw [abs_neg, abs_of_pos hℓ])
      rwa [← sub_eq_add_neg] at this
    show (φ u - φ (u - ℓ)) ^ 2 = φ u ^ 2 + φ (u - ℓ) ^ 2
    linear_combination -2 * e
  have hcorr : ∀ u, H u * H (u + ℓ) = -φ u ^ 2 := fun u => by
    have e1 := hz u ℓ (le_abs_self ℓ)
    have e2 : φ (u - ℓ) * φ (u + ℓ) = 0 := by
      have := hz (u - ℓ) (2 * ℓ) (by rw [abs_of_pos (by positivity)]; linarith)
      rwa [show u - ℓ + 2 * ℓ = u + ℓ by ring] at this
    have e3 : φ (u - ℓ) * φ u = 0 := by
      have := hz (u - ℓ) ℓ (le_abs_self ℓ)
      rwa [show u - ℓ + ℓ = u by ring] at this
    show (φ u - φ (u - ℓ)) * (φ (u + ℓ) - φ (u + ℓ - ℓ)) = -φ u ^ 2
    rw [add_sub_cancel_right]
    linear_combination e1 - e2 + e3
  have iφ : Integrable fun u => φ u ^ 2 := _root_.RHTower.WeilMarkovPole.integrable_sq hφc
    φ.hasCompactSupport
  have hI : 0 < ∫ u, φ u ^ 2 := by
    rw [integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _) iφ]
    have : Function.support (fun u => φ u ^ 2) = Metric.ball c ((A - ℓ) / 2) := by
      rw [← φ.support_eq]
      ext u
      simp only [Function.mem_support, ne_eq, pow_eq_zero_iff two_ne_zero]
    rw [this, Real.volume_ball]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hnorm : ∫ u, H u ^ 2 = 2 * ∫ u, φ u ^ 2 := by
    simp_rw [hsq]
    rw [integral_add iφ (iφ.comp_sub_right ℓ), integral_sub_right_eq_self (fun u => φ u ^ 2) ℓ]
    ring
  have hc2 : ∫ u, H u * H (u + ℓ) = -∫ u, φ u ^ 2 := by
    rw [← integral_neg]; exact integral_congr_ae (Filter.Eventually.of_forall hcorr)
  refine ⟨H, hH, ?_⟩
  rw [tateFunction_firstStage hH hlev, hnorm, hc2]
  have hs : 0 < Real.sqrt 2 := by positivity
  have hq : 2 < ((2 : ℝ) ^ k - 1) / Real.sqrt 2 := by rw [lt_div_iff₀ hs]; linarith
  nlinarith

/-- **The exact Tate horizon at the first prime**: on a window with `log 2 < A < log 3`, the Tate
operator `ρ_A(J_k)` is a positive form iff `2^k ≤ 1 + 2√2`. -/
theorem tateFunction_nonneg_iff_firstStage (hA1 : Real.log 2 < A) (hA2 : A < Real.log 3) (k : ℝ) :
    (∀ H, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔ (2 : ℝ) ^ k ≤ 1 + 2 * Real.sqrt 2 := by
  have hlev := windowLevel_eq_two hA1.le hA2
  have hA : A < 2 * Real.log 2 := by
    have : Real.log 3 < 2 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  constructor
  · intro h
    by_contra hk
    obtain ⟨H, hH, hneg⟩ := exists_tateFunction_neg_firstStage hA1 hlev hA (not_le.mp hk)
    exact absurd (h H hH) (not_le.mpr hneg)
  · exact fun hk H hH => tateFunction_nonneg_firstStage hH hlev hA hk

end GaloisForLFunctions.WindowTowerOfSpecZ
