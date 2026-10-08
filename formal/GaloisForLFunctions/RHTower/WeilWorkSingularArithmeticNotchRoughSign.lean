import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchRampSign
import GaloisForLFunctions.RHTower.WeilRoughFibreSignLaw
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope

/-!
# A rough-sign alternative from full Weil positivity

The source supplies every analytic and Dirichlet summability input.
Either its absolute harmonic mass fails the sublogarithmic envelope,
or no fixed prime deletion has an eventually positive harmonic floor.
-/

noncomputable section
open Finset GaloisForLFunctions.HTGeometry

namespace RHTower.WeilSingularArithmetic
open WeilAbscissa ZetaNotch SmoothNumbers WeilFiniteSupport WeilLogSummable

private theorem nonpos_of_roughSum_ge_harmonic {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀)
    {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)))
    (hs1 : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hharm : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |sqrtScaled v n| / n) ≤ B + η * Real.log N)
    {Y : ℝ} {T : ℕ}
    (hfloor : ∀ k, T ≤ k → Y ≤ ∑ n ∈ range (k + 1),
      (if vecOf P n = 0 then v n * (Real.sqrt n)⁻¹ else 0)) : Y ≤ 0 := by
  by_contra hY
  push Not at hY
  let a (n : ℕ) := v n * mainWeight P 0 n₀ n
  have hS (k : ℕ) : rampPartial a k = ∑ n ∈ range (k + 1),
      (if vecOf P n = 0 then v n * (Real.sqrt n)⁻¹ else 0) :=
    Finset.sum_congr rfl fun n _ => mul_mainWeight_zero_eq v n₀ n
  let T' := max T 1
  let B := ∑ k ∈ range T', |rampPartial a k|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hlow (k : ℕ) : -B ≤ rampPartial a k := by
    rcases lt_or_ge k T' with hk | hk
    · have h := Finset.single_le_sum (f := fun j => |rampPartial a j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hk)
      have := neg_abs_le (rampPartial a k)
      dsimp [B]
      linarith
    · have h := hfloor k ((le_max_left T 1).trans hk)
      rw [← hS] at h
      linarith
  have hhigh (k : ℕ) (hk : T' ≤ k) : Y ≤ rampPartial a k := by
    rw [hS]
    exact hfloor k ((le_max_left T 1).trans hk)
  obtain ⟨Dr, hDr, hm⟩ := exists_sum_re_weightedMoment_ge_ramp hP (K := 7) (by norm_num) 0 hn₀
  obtain ⟨CQ, hCQ, hQb, hqb⟩ := exists_notchWeight_bound P 0 n₀
  have h := nonpos_of_rampPartial_ge_harmonic (differentiable_notchWeightC P 0 n₀) hQb
    (notchWeightC_ofReal P 0 n₀) (notchWeight_nonneg P 0 n₀) (continuous_notchWeight P 0 n₀) hqb
    (eulerProduct_pos hP) (by exact_mod_cast twistBound_pos hP n₀) hDr
    (fun hv N u hu => hm hv N hu) hv0 hA ha hs34 hs1 hPD hharm
    (le_max_right T 1) hlow hhigh
  linarith

private theorem source_coneDeviation_summable {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |WeilOneSided.coneDeviation lam n| * (n : ℝ) ^ (-σ) := by
  refine (WeilSpectral.summable_abs_deviationCoeff hW hσ).congr fun n => ?_
  dsimp [WeilSpectral.deviationCoeff, WeilOneSided.coneDeviation]
  split_ifs
  · rw [abs_mul, abs_sub_comm, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  · simp

/-- Harmonic smallness alone suffices for the source's fixed rough-sign law. -/
theorem roughSum_nonpos_of_weilPositiveFull_of_harmonic {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hharm : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |WeilOneSided.coneDeviation lam n| / n) ≤ B + η * Real.log N)
    {y : ℕ} (hy : 2 ≤ y) {Y : ℝ} {T : ℕ}
    (hfloor : ∀ k, T ≤ k → Y ≤ ∑ n ∈ range (k + 1),
      (if vecOf (primesUpTo y) n = 0 then WeilOneSided.coneDeviation lam n / n else 0)) :
    Y ≤ 0 := by
  let v := WeilExcess.weilDeviation lam
  obtain ⟨C, hC0, hC⟩ := WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [v, WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsc (n : ℕ) : sqrtScaled v n = WeilOneSided.coneDeviation lam n := by
    simp only [sqrtScaled, v, WeilExcess.weilDeviation, WeilOneSided.coneDeviation]
    split_ifs with hn
    · have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      field_simp
    · simp
  have hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by
    refine (source_coneDeviation_summable hW (σ := 5 / 4) (by norm_num)).congr fun n => ?_
    rw [abs_mul_rpow_three_quarters_eq v, hsc]
  have hs1 : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹ := by
    refine (source_coneDeviation_summable hW (σ := 1 + 1 / 2) (by norm_num)).congr fun n => ?_
    rw [abs_mul_inv_eq_rpow v, hsc]
  have hhv : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |sqrtScaled v n| / n) ≤ B + η * Real.log N := by
    simpa only [hsc] using hharm
  have hterm (n : ℕ) : v n * (Real.sqrt n)⁻¹ = WeilOneSided.coneDeviation lam n / n := by
    rw [← hsc, sqrtScaled, mul_comm (Real.sqrt n), mul_div_assoc, Real.sqrt_div_self]
  apply nonpos_of_roughSum_ge_harmonic (P := primesUpTo y) prime_of_mem_primesUpTo
    (n₀ := 2) (isSmoothOver_primesUpTo le_rfl hy) hv0 hC0 hC hs34 hs1 hPD hhv
  intro k hk
  simpa only [hterm] using hfloor k hk

/-- Unconditional alternative for every full-positive source: failure of the
sublogarithmic absolute harmonic envelope, or every fixed rough-sign law. -/
theorem not_harmonic_small_or_rough_sign_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    (¬ ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |WeilOneSided.coneDeviation lam n| / n) ≤ B + η * Real.log N) ∨
    (∀ y : ℕ, 2 ≤ y → ∀ Y : ℝ, 0 < Y → ∀ T : ℕ, ∃ k : ℕ, T ≤ k ∧
      (∑ n ∈ range (k + 1),
        (if vecOf (primesUpTo y) n = 0 then WeilOneSided.coneDeviation lam n / n else 0)) < Y) := by
  classical
  by_cases hharm : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |WeilOneSided.coneDeviation lam n| / n) ≤ B + η * Real.log N
  · right
    intro y hy Y hY T
    by_contra h
    push Not at h
    have := roughSum_nonpos_of_weilPositiveFull_of_harmonic hW hharm hy h
    linarith
  · exact Or.inl hharm

end RHTower.WeilSingularArithmetic
