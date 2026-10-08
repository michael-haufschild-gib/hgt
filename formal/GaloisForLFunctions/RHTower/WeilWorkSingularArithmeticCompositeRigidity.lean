import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchIsolation
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSummatory
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope

/-!
# A composite-mass alternative for every full-positive source

Average harmonic smallness and a summable composite tail force canonical
coefficients. The final alternative has only full positivity as its source
input; no coefficient sign or pointwise relative-size bound is imposed.
-/

noncomputable section
open Finset Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower.WeilSingularArithmetic
open WeilAbscissa

/-- Harmonic smallness and absolute harmonic summability on nonprimes
isolate all coefficients of an actual full-positive source. -/
theorem eq_vonMangoldt_of_harmonic_small_of_nonprime_summable {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hharm : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |WeilOneSided.coneDeviation lam n| / n) ≤ B + η * Real.log N)
    (hcomp : Summable fun n : ℕ => if n.Prime then 0 else
      |WeilOneSided.coneDeviation lam n| / n) :
    ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  let v := WeilExcess.weilDeviation lam
  obtain ⟨C, hC0, hC⟩ := WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [v, WeilExcess.weilDeviation]
  have hv1 : v 1 = 0 := by simp [v, WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsc (n : ℕ) : sqrtScaled v n = WeilOneSided.coneDeviation lam n := by
    simp only [sqrtScaled, v, WeilExcess.weilDeviation, WeilOneSided.coneDeviation]
    split_ifs with hn
    · have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      field_simp
    · simp
  have hseries {σ : ℝ} (hσ : 1 < σ) :
      Summable fun n : ℕ => |WeilOneSided.coneDeviation lam n| * (n : ℝ) ^ (-σ) := by
    refine (WeilSpectral.summable_abs_deviationCoeff hW hσ).congr fun n => ?_
    dsimp [WeilSpectral.deviationCoeff, WeilOneSided.coneDeviation]
    split_ifs
    · rw [abs_mul, abs_sub_comm, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    · simp
  have hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by
    refine (hseries (σ := 5 / 4) (by norm_num)).congr fun n => ?_
    rw [abs_mul_rpow_three_quarters_eq v, hsc]
  have hs1 : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹ := by
    refine (hseries (σ := 1 + 1 / 2) (by norm_num)).congr fun n => ?_
    rw [abs_mul_inv_eq_rpow v, hsc]
  have hhv : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |sqrtScaled v n| / n) ≤ B + η * Real.log N := by
    simpa only [hsc] using hharm
  have hcv : Summable fun n : ℕ => if n.Prime then 0 else |v n| * (Real.sqrt n)⁻¹ := by
    simpa only [abs_mul_inv_sqrt_eq, hsc] using hcomp
  have hterm (n : ℕ) : v n * (Real.sqrt n)⁻¹ = WeilOneSided.coneDeviation lam n / n := by
    rw [← hsc, sqrtScaled, mul_comm (Real.sqrt n), mul_div_assoc, Real.sqrt_div_self]
  obtain ⟨L, hL⟩ := exists_tendsto_coneDeviation_harmonic hW
  have hLv : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), v n * (Real.sqrt n)⁻¹)
      atTop (𝓝 L) := by simpa only [hterm] using hL
  have hv := eq_zero_of_harmonic_small_of_nonprime_summable hv0 hv1 hC0 hC
    hs34 hs1 hPD hhv hcv hLv
  intro n hn
  have hd : WeilOneSided.coneDeviation lam n = 0 := by
    rw [← hsc, sqrtScaled, hv]
    simp
  simpa only [WeilOneSided.coneDeviation, if_pos hn, sub_eq_zero] using hd

/-- Every noncanonical full-positive source either has non-sublogarithmic
absolute harmonic mass or has divergent absolute harmonic mass on composites. -/
theorem canonical_or_not_harmonic_small_or_nonprime_mass_diverges {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∨
    (¬ ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |WeilOneSided.coneDeviation lam n| / n) ≤ B + η * Real.log N) ∨
    ¬ Summable (fun n : ℕ => if n.Prime then 0 else
      |WeilOneSided.coneDeviation lam n| / n) := by
  classical
  by_cases hharm : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |WeilOneSided.coneDeviation lam n| / n) ≤ B + η * Real.log N
  · by_cases hcomp : Summable fun n : ℕ => if n.Prime then 0 else
        |WeilOneSided.coneDeviation lam n| / n
    · exact Or.inl (eq_vonMangoldt_of_harmonic_small_of_nonprime_summable hW hharm hcomp)
    · exact Or.inr (Or.inr hcomp)
  · exact Or.inr (Or.inl hharm)

end RHTower.WeilSingularArithmetic
