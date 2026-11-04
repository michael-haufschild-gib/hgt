import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceCapacityCofactors
import GaloisForLFunctions.HTGeometry.InverseHarmonicLogSum
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Prime receiving capacity grows doubly logarithmically

The exact cofactor layers have total weight at most one. Prime Mertens
errors therefore remain bounded after summing those layers. The remaining
inverse harmonic mesh sum is the logarithm of the harmonic number up to
a summable error.
-/

noncomputable section
open Finset
open scoped Classical

namespace GaloisForLFunctions.ArithmeticCouplingTheory
open HTGeometry

private def primeMertensMass (N : ℕ) : ℝ :=
  ∑ p ∈ Icc 1 N with p.Prime, Real.log p / (p : ℝ)

private def capacityMertensConstant : ℝ :=
  |(Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)|

private theorem primeMertensMass_error {N : ℕ} (hN : 1 ≤ N) :
    |primeMertensMass N - Real.log N| ≤ capacityMertensConstant :=
  (RHTower.Mertens.mertens_first_prime N hN).trans (le_abs_self _)

private theorem cofactor_log_distortion {N k : ℕ} (hk : k ∈ Ico 1 N) :
    0 ≤ Real.log N - Real.log (N / (k + 1) : ℕ) - Real.log ((k : ℝ) + 1) ∧
    Real.log N - Real.log (N / (k + 1) : ℕ) - Real.log ((k : ℝ) + 1) ≤ Real.log 2 := by
  let M := N / (k + 1)
  have hkn : k + 1 ≤ N := by have := (mem_Ico.mp hk).2; omega
  have hM : 1 ≤ M := (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mpr (by
    simpa only [one_mul] using hkn)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := zero_lt_one.trans_le hM1
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlo : (M : ℝ) * ((k : ℝ) + 1) ≤ N := by
    exact_mod_cast (Nat.div_mul_le_self N (k + 1))
  have hhi : (N : ℝ) < ((M : ℝ) + 1) * ((k : ℝ) + 1) := by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).mp (Nat.lt_succ_self M))
  have hhi' : (N : ℝ) ≤ 2 * ((M : ℝ) * ((k : ℝ) + 1)) := by
    have h := mul_nonneg (sub_nonneg.mpr hM1) hk0.le
    nlinarith only [h, hhi]
  have hratio₁ : (1 : ℝ) ≤ N / ((M : ℝ) * ((k : ℝ) + 1)) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hlo)
  have hratio₂ : (N : ℝ) / ((M : ℝ) * ((k : ℝ) + 1)) ≤ 2 :=
    (div_le_iff₀ (by positivity)).mpr hhi'
  have he : Real.log ((N : ℝ) / ((M : ℝ) * ((k : ℝ) + 1))) =
      Real.log N - Real.log M - Real.log ((k : ℝ) + 1) := by
    rw [Real.log_div hN0.ne' (mul_ne_zero hM0.ne' hk0.ne'), Real.log_mul hM0.ne' hk0.ne']
    ring
  have ha := Real.log_nonneg hratio₁
  have hb := Real.log_le_log (div_pos hN0 (by positivity)) hratio₂
  rw [he] at ha hb
  exact ⟨ha, hb⟩

private theorem prime_cofactor_error {N k : ℕ} (hk : k ∈ Ico 1 N) :
    |primeMertensMass N - primeMertensMass (N / (k + 1)) - Real.log ((k : ℝ) + 1)| ≤
      2 * capacityMertensConstant + Real.log 2 := by
  have hN : 1 ≤ N := by have := mem_Ico.mp hk; omega
  have hM : 1 ≤ N / (k + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mpr (by
    have := (mem_Ico.mp hk).2
    omega)
  have hd := cofactor_log_distortion hk
  have hlog : |Real.log N - Real.log (N / (k + 1) : ℕ) - Real.log ((k : ℝ) + 1)| ≤
      Real.log 2 := by
    rw [abs_of_nonneg hd.1]
    exact hd.2
  have he : primeMertensMass N - primeMertensMass (N / (k + 1)) - Real.log ((k : ℝ) + 1) =
      ((primeMertensMass N - Real.log N) -
        (primeMertensMass (N / (k + 1)) - Real.log (N / (k + 1) : ℕ))) +
          (Real.log N - Real.log (N / (k + 1) : ℕ) - Real.log ((k : ℝ) + 1)) := by ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add (primeMertensMass_error hN) (primeMertensMass_error hM)))
    hlog)).trans_eq (by ring)

private theorem harmonic_drop_nonneg {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ 1 / (harmonic k : ℝ) - 1 / (harmonic (k + 1) : ℝ) := by
  have hH : 0 < (harmonic k : ℝ) := zero_lt_one.trans_le (one_le_real_harmonic hk)
  have hs : (harmonic k : ℝ) ≤ (harmonic (k + 1) : ℝ) := by
    rw [harmonic_succ, Rat.cast_add]
    exact le_add_of_nonneg_right (by positivity)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hH hs)

private theorem sum_harmonic_drop_le_one {N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Ico 1 N, (1 / (harmonic k : ℝ) - 1 / (harmonic (k + 1) : ℝ))) ≤ 1 := by
  let g : ℕ → ℝ := fun k => 1 / (harmonic k : ℝ)
  have ht : (∑ k ∈ Ico 1 N, ((-g (k + 1)) - (-g k))) = (-g N) - (-g 1) := by
    rw [sum_Ico_eq_sub _ hN, sum_range_sub (fun k => -g k) N,
      sum_range_sub (fun k => -g k) 1]
    ring
  simp only [neg_sub_neg] at ht
  have h1 : g 1 = 1 := by norm_num [g, harmonic]
  rw [h1] at ht
  change (∑ k ∈ Ico 1 N, (g k - g (k + 1))) ≤ 1
  rw [ht]
  apply sub_le_self
  dsimp only [g]
  exact div_nonneg zero_le_one (zero_le_one.trans (one_le_real_harmonic hN))

private theorem capacity_sub_harmonic_mesh_le {N : ℕ} (hN : 1 ≤ N) :
    |primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N -
      inverseHarmonicLogIncrementSum N| ≤ 3 * capacityMertensConstant + Real.log 2 := by
  let d : ℕ → ℝ := fun k => 1 / (harmonic k : ℝ) - 1 / (harmonic (k + 1) : ℝ)
  let E : ℕ → ℝ := fun k => primeMertensMass N - primeMertensMass (N / (k + 1)) -
    Real.log ((k : ℝ) + 1)
  let C := 2 * capacityMertensConstant + Real.log 2
  have hC0 : 0 ≤ capacityMertensConstant := abs_nonneg _
  have hC : 0 ≤ C := by
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [C]
    positivity
  have hdrop (k : ℕ) (hk : k ∈ Ico 1 N) : 0 ≤ d k :=
    harmonic_drop_nonneg (mem_Ico.mp hk).1
  have hs : |∑ k ∈ Ico 1 N, d k * E k| ≤ C := by
    calc
      _ ≤ ∑ k ∈ Ico 1 N, |d k * E k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Ico 1 N, C * d k := by
        apply sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (hdrop k hk)]
        exact (mul_le_mul_of_nonneg_left (prime_cofactor_error hk) (hdrop k hk)).trans_eq
          (by dsimp only [C]; ring)
      _ = C * ∑ k ∈ Ico 1 N, d k := (mul_sum _ _ _).symm
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (sum_harmonic_drop_le_one hN) hC
      _ = C := mul_one C
  have hp : |(primeMertensMass N - Real.log N) / (harmonic N : ℝ)| ≤
      capacityMertensConstant := by
    have hH := one_le_real_harmonic hN
    have hH0 := zero_lt_one.trans_le hH
    rw [abs_div, abs_of_pos hH0]
    exact (div_le_div_of_nonneg_right (primeMertensMass_error hN) hH0.le).trans
      ((div_le_div_of_nonneg_left hC0 zero_lt_one hH).trans_eq (div_one _))
  have he : primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N -
      inverseHarmonicLogIncrementSum N =
      (primeMertensMass N - Real.log N) / (harmonic N : ℝ) + ∑ k ∈ Ico 1 N, d k * E k := by
    rw [primeIncidenceReceivingCapacity_cofactor_decomposition,
      inverseHarmonicLogIncrementSum_eq_layers hN]
    have hs' : (∑ k ∈ Ico 1 N, d k * E k) =
        (∑ k ∈ Ico 1 N, d k * (primeMertensMass N - primeMertensMass (N / (k + 1)))) -
          ∑ k ∈ Ico 1 N, d k * Real.log ((k : ℝ) + 1) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun _ _ => by dsimp only [E]; ring
    rw [hs']
    change primeMertensMass N / (harmonic N : ℝ) +
      (∑ k ∈ Ico 1 N, d k * (primeMertensMass N - primeMertensMass (N / (k + 1)))) -
      (Real.log N / (harmonic N : ℝ) + ∑ k ∈ Ico 1 N, d k * Real.log ((k : ℝ) + 1)) = _
    ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add hp hs)).trans_eq (by dsimp only [C]; ring)

private theorem log_harmonic_sub_log_log_le {N : ℕ} (hN : 3 ≤ N) :
    |Real.log (harmonic N : ℝ) - Real.log (Real.log N)| ≤ 1 / Real.log 3 := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hH : 0 < (harmonic N : ℝ) := zero_lt_one.trans_le (one_le_real_harmonic hN1)
  have hLH : Real.log N ≤ (harmonic N : ℝ) :=
    (Real.log_le_log hN0 (by exact_mod_cast Nat.le_succ N)).trans (log_add_one_le_harmonic N)
  have hlo := Real.log_le_log hL hLH
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hu : (harmonic N : ℝ) / Real.log N - 1 ≤ 1 / Real.log N := by
    rw [sub_le_iff_le_add, div_le_iff₀ hL]
    calc
      _ ≤ 1 + Real.log N := harmonic_le_one_add_log N
      _ = (1 / Real.log N + 1) * Real.log N := by field_simp
  calc
    _ = Real.log ((harmonic N : ℝ) / Real.log N) := (Real.log_div hH.ne' hL.ne').symm
    _ ≤ (harmonic N : ℝ) / Real.log N - 1 := Real.log_le_sub_one_of_pos (div_pos hH hL)
    _ ≤ 1 / Real.log N := hu
    _ ≤ 1 / Real.log 3 := one_div_le_one_div_of_le (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) (by exact_mod_cast hN))

/-- The full prime receiving capacity is `log log N + O(1)` with an absolute error bound. -/
theorem primeIncidenceReceivingCapacity_log_log_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      |primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N -
        Real.log (Real.log N)| ≤ C := by
  have hC0 : 0 ≤ capacityMertensConstant := abs_nonneg _
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨3 * capacityMertensConstant + Real.log 2 + 2 + 1 / Real.log 3,
    by positivity, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hmesh0, hmesh2⟩ := inverseHarmonicLogIncrementSum_sub_log_bounds hN1
  have hmesh : |inverseHarmonicLogIncrementSum N - Real.log (harmonic N : ℝ)| ≤ 2 := by
    rwa [abs_of_nonneg hmesh0]
  have he : primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N - Real.log (Real.log N) =
      (primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N -
        inverseHarmonicLogIncrementSum N) +
      (inverseHarmonicLogIncrementSum N - Real.log (harmonic N : ℝ)) +
      (Real.log (harmonic N : ℝ) - Real.log (Real.log N)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (capacity_sub_harmonic_mesh_le hN1) hmesh))
    (log_harmonic_sub_log_log_le hN))

end GaloisForLFunctions.ArithmeticCouplingTheory

#print axioms GaloisForLFunctions.ArithmeticCouplingTheory.primeIncidenceReceivingCapacity_log_log_bounded
