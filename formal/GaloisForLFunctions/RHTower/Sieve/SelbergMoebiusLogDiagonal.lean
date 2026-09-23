import GaloisForLFunctions.RHTower.Sieve.BarbanVehovWeight
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusUniformBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusDiagonalSupport
import GaloisForLFunctions.RHTower.Sieve.ReciprocalTotientLogBound

/-!
# The Selberg diagonal of the Barban–Vehov weight

Reindexing the multiples of `e` identifies the inner sums of the Selberg diagonalisation with the
coprime logarithmic Möbius sums at the divided cutoff:

`∑_{m ≤ N, e ∣ m} μ(m) log(X/m)/m = (μ(e)/e) · T_e(X/e)` .

The uniform bound `|T_e| ≤ A·e/φ(e)` therefore gives `A/φ(e)` for each inner sum, and the inner sums
vanish beyond `e = X`, so the totient-weighted diagonal is at most `A²∑_{e ≤ X} 1/φ(e)`, which is
logarithmic.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- The truncated logarithmic weight underlying the Barban–Vehov coefficient. -/
noncomputable def barbanVehovLogWeight (X : ℕ) (m : ℕ) : ℝ :=
  (if m ≤ X then Real.log ((X : ℝ) / (m : ℝ)) else 0) / (m : ℝ)

theorem barbanVehovWeight_div_eq (X m : ℕ) :
    barbanVehovWeight X m / (m : ℝ) = (μ m : ℝ) * barbanVehovLogWeight X m := by
  rw [barbanVehovWeight, barbanVehovLogWeight]
  split
  · ring
  · simp

/-- **The inner sums of the Selberg diagonalisation.** -/
theorem barbanVehov_inner_eq {X N e : ℕ} (he : 0 < e) (hXN : X ≤ N) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ)
      = ((μ e : ℤ) : ℝ) / (e : ℝ) * coprimeLogMoebius e ((X : ℝ) / (e : ℝ)) := by
  classical
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hstep : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ)
      = ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m),
          (μ m : ℝ) * barbanVehovLogWeight X m :=
    Finset.sum_congr rfl fun m _ => barbanVehovWeight_div_eq X m
  rw [hstep, sum_filter_dvd_moebius_scaled he (barbanVehovLogWeight X)]
  have hfloor : ⌊(X : ℝ) / (e : ℝ)⌋₊ = X / e := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hsub : (Finset.Icc 1 (X / e)).filter (fun j => Nat.Coprime e j)
      ⊆ (Finset.Icc 1 (N / e)).filter (fun j => Nat.Coprime e j) := by
    intro j hj
    obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, ?_⟩, hc⟩
    exact le_trans hj2 (Nat.div_le_div_right hXN)
  have hvanish : ∀ j ∈ (Finset.Icc 1 (N / e)).filter (fun j => Nat.Coprime e j),
      j ∉ (Finset.Icc 1 (X / e)).filter (fun j => Nat.Coprime e j) →
      (μ e : ℝ) * (μ j : ℝ) * barbanVehovLogWeight X (e * j) = 0 := by
    intro j hj hnot
    obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp hmem
    have hgt : X / e < j := by
      by_contra hcon
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, by omega⟩, hc⟩)
    have hnotle : ¬ e * j ≤ X := by
      intro hle
      have hle' : j * e ≤ X := by
        rw [Nat.mul_comm] at hle
        exact hle
      have hdiv := (Nat.le_div_iff_mul_le he).mpr hle'
      omega
    rw [barbanVehovLogWeight, if_neg hnotle]
    simp
  rw [← Finset.sum_subset hsub hvanish, coprimeLogMoebius, hfloor, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hmem
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hle : e * j ≤ X := by
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le he).mp hj2
  have hcast : ((e * j : ℕ) : ℝ) = (e : ℝ) * (j : ℝ) := by push_cast; ring
  have harg : (X : ℝ) / ((e : ℝ) * (j : ℝ)) = (X : ℝ) / (e : ℝ) / (j : ℝ) :=
    (div_div (X : ℝ) (e : ℝ) (j : ℝ)).symm
  rw [barbanVehovLogWeight, if_pos hle, hcast, harg]
  ring

/-- Each inner sum is at most `A/φ(e)`. -/
theorem abs_barbanVehov_inner_le {X N e : ℕ} (he : 0 < e) (hXN : X ≤ N) :
    |∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ)|
      ≤ coprimeLogMoebiusConst / (Nat.totient e : ℝ) := by
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hφ : (0 : ℝ) < (Nat.totient e : ℝ) := by
    have := Nat.totient_pos.mpr he
    exact_mod_cast this
  rw [barbanVehov_inner_eq he hXN, abs_mul, abs_div]
  by_cases hsq : Squarefree e
  · have hT := abs_coprimeLogMoebius_le e hsq ((X : ℝ) / (e : ℝ))
    have hmu : |((μ e : ℤ) : ℝ)| ≤ 1 := abs_moebius_le_one e
    have hnn : (0 : ℝ) ≤ |((μ e : ℤ) : ℝ)| / |(e : ℝ)| := by positivity
    rw [abs_of_pos heR]
    calc |((μ e : ℤ) : ℝ)| / (e : ℝ) * |coprimeLogMoebius e ((X : ℝ) / (e : ℝ))|
        ≤ (1 / (e : ℝ)) * (coprimeLogMoebiusConst * ((e : ℝ) / (Nat.totient e : ℝ))) := by
          refine mul_le_mul (by exact div_le_div_of_nonneg_right hmu heR.le) hT (abs_nonneg _)
            (by positivity)
      _ = coprimeLogMoebiusConst / (Nat.totient e : ℝ) := by
          field_simp
  · have h0 : ((μ e : ℤ) : ℝ) = 0 := by
      have := moebius_eq_zero_of_not_squarefree hsq
      exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) this
    rw [h0]
    simp only [abs_zero, zero_div, zero_mul]
    exact div_nonneg coprimeLogMoebiusConst_nonneg hφ.le

/-- Beyond the mollifier length the inner sums vanish. -/
theorem barbanVehov_inner_eq_zero {X N e : ℕ} (he : 0 < e) (hXN : X ≤ N) (hXe : X < e) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ) = 0 := by
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hlt : (X : ℝ) / (e : ℝ) < 1 := by
    rw [div_lt_one heR]
    exact_mod_cast hXe
  rw [barbanVehov_inner_eq he hXN, coprimeLogMoebius_of_lt_one e hlt, mul_zero]

/-- **The totient-weighted Selberg diagonal is logarithmic.** -/
theorem barbanVehov_totient_diagonal_le {X N : ℕ} (hXN : X ≤ N) :
    ∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
        (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ)) ^ (2 : ℕ)
      ≤ 4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log X) := by
  classical
  have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 N := by
    intro e he
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp he
    exact Finset.mem_Icc.mpr ⟨h1, le_trans h2 hXN⟩
  have hvanish : ∀ e ∈ Finset.Icc 1 N, e ∉ Finset.Icc 1 X →
      (Nat.totient e : ℝ) *
        (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ)) ^ (2 : ℕ)
        = 0 := by
    intro e he hnot
    obtain ⟨he1, -⟩ := Finset.mem_Icc.mp he
    have hXe : X < e := by
      by_contra hcon
      exact hnot (Finset.mem_Icc.mpr ⟨he1, by omega⟩)
    rw [barbanVehov_inner_eq_zero (by omega) hXN hXe]
    ring
  rw [← Finset.sum_subset hsub hvanish]
  have hterm : ∀ e ∈ Finset.Icc 1 X, (Nat.totient e : ℝ) *
      (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ)) ^ (2 : ℕ)
      ≤ coprimeLogMoebiusConst ^ (2 : ℕ) * (1 / (Nat.totient e : ℝ)) := by
    intro e he
    obtain ⟨he1, -⟩ := Finset.mem_Icc.mp he
    have hepos : 0 < e := by omega
    have hφ : (0 : ℝ) < (Nat.totient e : ℝ) := by
      have := Nat.totient_pos.mpr hepos
      exact_mod_cast this
    have habs := abs_barbanVehov_inner_le (X := X) (N := N) hepos hXN
    have hsq : (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m),
        barbanVehovWeight X m / (m : ℝ)) ^ (2 : ℕ)
        ≤ (coprimeLogMoebiusConst / (Nat.totient e : ℝ)) ^ (2 : ℕ) := by
      have hnn : (0 : ℝ) ≤ coprimeLogMoebiusConst / (Nat.totient e : ℝ) :=
        div_nonneg coprimeLogMoebiusConst_nonneg hφ.le
      nlinarith [abs_nonneg (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m),
        barbanVehovWeight X m / (m : ℝ)),
        sq_abs (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m),
          barbanVehovWeight X m / (m : ℝ)), habs, hnn]
    calc (Nat.totient e : ℝ) * (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m),
            barbanVehovWeight X m / (m : ℝ)) ^ (2 : ℕ)
        ≤ (Nat.totient e : ℝ) * (coprimeLogMoebiusConst / (Nat.totient e : ℝ)) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hsq hφ.le
      _ = coprimeLogMoebiusConst ^ (2 : ℕ) * (1 / (Nat.totient e : ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hrec : ∑ e ∈ Finset.Icc 1 X, 1 / (Nat.totient e : ℝ) ≤ 4 * (1 + Real.log X) :=
    sum_inv_totient_le X
  have hAnn : (0 : ℝ) ≤ coprimeLogMoebiusConst ^ (2 : ℕ) := by positivity
  calc coprimeLogMoebiusConst ^ (2 : ℕ) * ∑ e ∈ Finset.Icc 1 X, 1 / (Nat.totient e : ℝ)
      ≤ coprimeLogMoebiusConst ^ (2 : ℕ) * (4 * (1 + Real.log X)) :=
        mul_le_mul_of_nonneg_left hrec hAnn
    _ = 4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log X) := by ring

end RHTower.Sieve
