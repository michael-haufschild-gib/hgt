import GaloisForLFunctions.SignedArithmeticHodgeTheory.GrowingRamanujanFamiliesHaveAUniformGramBudget
import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneArithmeticRemainderControlsEveryRamanujanResidual

/-!
# Local capture costs for arithmetic mode families

The totient amplitude bound controls every coefficient family's mass in a
fixed integer window. Combined with the global Gram estimate, it measures
the fraction of a normalized modal source that the window can capture.
-/

noncomputable section

open Filter Topology Finset
open scoped BigOperators

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open RenormalizedArithmeticPotentialTheory

private theorem ramanujanPoleProfile_sq_le {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ramanujanPoleProfile m n ^ 2 ≤ (m.totient : ℝ) / n := by
  have h := abs_normalizedRamanujanMode_le_sqrt_totient hm n
  have hsq := mul_le_mul h h (abs_nonneg _) (Real.sqrt_nonneg _)
  rw [← sq, sq_abs, ← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)] at hsq
  rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right hsq (Nat.cast_nonneg n)

/-- One totient budget controls local mass for every coefficient vector. -/
theorem ramanujanPoleProfile_family_local_mass_le
    (S : Finset ℕ+) (c : ℕ+ → ℝ) (L : ℕ) :
    (∑ n ∈ Icc 1 L, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) ≤
      (∑ n ∈ Icc 1 L, 1 / (n : ℝ)) *
        (∑ m ∈ S, ((m : ℕ).totient : ℝ)) * (∑ m ∈ S, c m ^ 2) := by
  have hc : 0 ≤ ∑ m ∈ S, c m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ ∑ n ∈ Icc 1 L, (∑ m ∈ S, c m ^ 2) *
        ((∑ m ∈ S, ((m : ℕ).totient : ℝ)) / (n : ℝ)) := by
      apply sum_le_sum
      intro n _
      refine (sum_mul_sq_le_sq_mul_sq S c (fun m => ramanujanPoleProfile m n)).trans ?_
      apply mul_le_mul_of_nonneg_left ?_ hc
      calc
        _ ≤ ∑ m ∈ S, ((m : ℕ).totient : ℝ) / (n : ℝ) :=
          sum_le_sum fun m _ => ramanujanPoleProfile_sq_le (m := (m : ℕ)) m.property n
        _ = _ := by rw [sum_div]
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply sum_congr rfl
      intro n _
      ring

/-- Local capture is constrained by the global logarithmic Gram mass.
The inequality remains valid when its left coefficient is nonpositive. -/
theorem ramanujanPoleProfile_family_capture_bound
    (S : Finset ℕ+) (c : ℕ+ → ℝ) (L N : ℕ) :
    (Real.log N - (1 + 2 * ∑ m ∈ S, (m : ℝ) ^ 2)) *
        (∑ n ∈ Icc 1 L, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) ≤
      ((∑ n ∈ Icc 1 L, 1 / (n : ℝ)) * (∑ m ∈ S, ((m : ℕ).totient : ℝ))) *
        (∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) := by
  let d : ℝ := Real.log N - (1 + 2 * ∑ m ∈ S, (m : ℝ) ^ 2)
  let K : ℝ := (∑ n ∈ Icc 1 L, 1 / (n : ℝ)) *
    (∑ m ∈ S, ((m : ℕ).totient : ℝ))
  have hK : 0 ≤ K := mul_nonneg
    (sum_nonneg fun _ _ => by positivity) (sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hlocal := ramanujanPoleProfile_family_local_mass_le S c L
  have hgram := (abs_le.mp (ramanujanPoleProfile_family_log_gram_error_le S c N)).1
  have hglobal : d * (∑ m ∈ S, c m ^ 2) ≤
      ∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2 := by
    dsimp only [d]
    nlinarith only [hgram]
  change d * _ ≤ K * _
  by_cases hd : 0 ≤ d
  · calc
      _ ≤ d * (K * ∑ m ∈ S, c m ^ 2) := mul_le_mul_of_nonneg_left hlocal hd
      _ = K * (d * ∑ m ∈ S, c m ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hglobal hK
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd)
      (sum_nonneg fun _ _ => sq_nonneg _)).trans
        (mul_nonneg hK (sum_nonneg fun _ _ => sq_nonneg _))

/-- Above the Gram threshold, this is the exact local-to-global mass budget. -/
theorem ramanujanPoleProfile_family_local_fraction_le
    (S : Finset ℕ+) (c : ℕ+ → ℝ) (L N : ℕ)
    (hN : 1 + 2 * ∑ m ∈ S, (m : ℝ) ^ 2 < Real.log N) :
    (∑ n ∈ Icc 1 L, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) ≤
      (((∑ n ∈ Icc 1 L, 1 / (n : ℝ)) * (∑ m ∈ S, ((m : ℕ).totient : ℝ))) /
        (Real.log N - (1 + 2 * ∑ m ∈ S, (m : ℝ) ^ 2))) *
          (∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) := by
  have h := ramanujanPoleProfile_family_capture_bound S c L N
  have hd := sub_pos.mpr hN
  calc
    _ ≤ (((∑ n ∈ Icc 1 L, 1 / (n : ℝ)) * (∑ m ∈ S, ((m : ℕ).totient : ℝ))) *
        (∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2)) /
          (Real.log N - (1 + 2 * ∑ m ∈ S, (m : ℝ) ^ 2)) := by
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using h
    _ = _ := by ring

/-- Every fixed finite modal span loses its normalized mass on a fixed window,
uniformly over all coefficient vectors. -/
theorem eventually_ramanujanPoleProfile_family_local_mass_le
    (S : Finset ℕ+) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℕ+ → ℝ,
      (∑ n ∈ Icc 1 L, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) ≤
        ε * (∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) := by
  let D : ℝ := 1 + 2 * ∑ m ∈ S, (m : ℝ) ^ 2
  let K : ℝ := (∑ n ∈ Icc 1 L, 1 / (n : ℝ)) *
    (∑ m ∈ S, ((m : ℕ).totient : ℝ))
  have hK : 0 ≤ K := mul_nonneg
    (sum_nonneg fun _ _ => by positivity) (sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (D + K / ε + 1))] with N hN c
  have hdiv : 0 ≤ K / ε := div_nonneg hK hε.le
  have hND : D < Real.log N := by linarith only [hN, hdiv]
  have hratio : K / (Real.log N - D) ≤ ε := by
    apply (div_le_iff₀ (sub_pos.mpr hND)).mpr
    have hKd : K / ε ≤ Real.log N - D := by linarith only [hN]
    have h := (div_le_iff₀ hε).mp hKd
    simpa only [mul_comm] using h
  exact (ramanujanPoleProfile_family_local_fraction_le S c L N hND).trans
    (mul_le_mul_of_nonneg_right hratio (sum_nonneg fun _ _ => sq_nonneg _))

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.ramanujanPoleProfile_family_local_mass_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.ramanujanPoleProfile_family_capture_bound
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.ramanujanPoleProfile_family_local_fraction_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.eventually_ramanujanPoleProfile_family_local_mass_le
