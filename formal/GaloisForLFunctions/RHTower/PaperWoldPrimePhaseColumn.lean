import GaloisForLFunctions.RHTower.PaperWoldPhaseColumn
import GaloisForLFunctions.RHTower.PaperWoldPrimeRectangle

/-! # Prime column energy survives every unit phase

At the three-quarter endpoint, the literal prime windows already force
logarithmically divergent squared column norms. No choice of entrywise
unit phases can pay this obstruction.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem paperWoldDirectedKernel_half_square_lower (t : {t : ℝ // 3 / 4 ≤ t})
    (n j : ℕ) :
    ((n : ℝ) + 1) * ‖paperWoldDirectedKernel (1 / 2) (n, j)‖ ^ 2 ≤
      ‖paperWoldDirectedKernel t (n, j)‖ ^ 2 := by
  unfold paperWoldDirectedKernel
  split_ifs
  · simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ) + 1) _)]
    rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hw : ((n : ℝ) + 1) ^ 3 ≤ (((n : ℝ) + 1) ^ (2 * t.val)) ^ 2 := by
      calc
        _ = ((n : ℝ) + 1) ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
        _ ≤ ((n : ℝ) + 1) ^ (2 * t.val * 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
            (by linarith [t.property])
        _ = _ := Real.rpow_mul_natCast (by positivity) _ 2
    calc
      _ = ((n : ℝ) + 1) ^ 3 *
          (|xiHeatCassiniWoldNatIncrement n| * |xiHeatCassiniWoldNatIncrement j|) ^ 2 := by ring
      _ ≤ (((n : ℝ) + 1) ^ (2 * t.val)) ^ 2 *
          (|xiHeatCassiniWoldNatIncrement n| * |xiHeatCassiniWoldNatIncrement j|) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
      _ = _ := by ring
  · simp only [norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, le_refl]

/-- The finite native matrix columns have a divergent energy floor, before any realization. -/
theorem paperWold_eventual_prime_column_energy (t : {t : ℝ // 3 / 4 ≤ t}) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ paperWoldPrimeIndices (2 * N),
      Real.log N ^ 3 / (2 * 4096 ^ 2) ≤
        ∑ n ∈ paperWoldPrimeIndices N, ‖paperWoldDirectedKernel t (n, j)‖ ^ 2 := by
  filter_upwards [paperWoldPrimeIndices_eventual_pair_card,
    paperWoldPrimeRectangle_eventual_lower ⟨1 / 2, le_rfl⟩] with N hN hrect
  intro j hj
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlp : 0 < Real.log (N : ℝ) := by linarith [hN.2.1]
  have he (n : ℕ) (hn : n ∈ paperWoldPrimeIndices N) :
      (N : ℝ) * (Real.log N ^ 2 / (4096 * (N : ℝ))) ^ 2 ≤
        ‖paperWoldDirectedKernel t (n, j)‖ ^ 2 := by
    have hnlo : (N : ℝ) ≤ n + 1 := by
      exact_mod_cast (show N ≤ n + 1 by
        have h := (paperWoldPrimeIndices_mem N n).mp hn
        omega)
    have hk := (hrect n hn j hj).trans (Complex.re_le_norm _)
    exact (mul_le_mul hnlo
      ((sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hk)
      (sq_nonneg _) (by positivity)).trans (paperWoldDirectedKernel_half_square_lower t n j)
  have hs : ((paperWoldPrimeIndices N).card : ℝ) *
      ((N : ℝ) * (Real.log N ^ 2 / (4096 * (N : ℝ))) ^ 2) ≤
        ∑ n ∈ paperWoldPrimeIndices N, ‖paperWoldDirectedKernel t (n, j)‖ ^ 2 := by
    calc
      _ = ∑ _n ∈ paperWoldPrimeIndices N,
          (N : ℝ) * (Real.log N ^ 2 / (4096 * (N : ℝ))) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum he
  calc
    _ = ((N : ℝ) / (2 * Real.log N)) *
        ((N : ℝ) * (Real.log N ^ 2 / (4096 * (N : ℝ))) ^ 2) := by
      field_simp
    _ ≤ _ := (mul_le_mul_of_nonneg_right hN.2.2.1 (by positivity)).trans hs

/-- Unit phases preserve the native finite energy floor in any operator realization. -/
theorem paperWoldPhase_eventual_prime_column_energy (t : {t : ℝ // 3 / 4 ≤ t})
    (u : PaperWoldUnitPhase) (T : PaperWoldPhaseRealization t u) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ paperWoldPrimeIndices (2 * N),
      Real.log N ^ 3 / (2 * 4096 ^ 2) ≤ ‖T.val (lp.single 2 j 1)‖ ^ 2 := by
  filter_upwards [paperWold_eventual_prime_column_energy t] with N hN
  intro j hj
  apply (hN j hj).trans
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, paperWoldPhaseRealization_single_norm t.val u T] using
    lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
      (T.val (lp.single 2 j 1)) (paperWoldPrimeIndices N)

theorem paperWoldPhaseRealization_eventual_prime_norm_lower
    (t : {t : ℝ // 3 / 4 ≤ t}) (u : PaperWoldUnitPhase)
    (T : PaperWoldPhaseRealization t u) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ 3 / (2 * 4096 ^ 2) ≤ ‖T.val‖ ^ 2 := by
  filter_upwards [paperWoldPhase_eventual_prime_column_energy t u T,
    paperWoldPrimeIndices_eventual_pair_card] with N he hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcp : (0 : ℝ) < ((paperWoldPrimeIndices (2 * N)).card : ℝ) :=
    lt_of_lt_of_le (div_pos hNp (by linarith [hN.2.1])) hN.2.2.2
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (paperWoldPrimeIndices (2 * N)).card by
    exact_mod_cast hcp)
  have hb : ‖T.val (lp.single 2 j 1)‖ ≤ ‖T.val‖ := by
    simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one] using
      T.val.le_opNorm (lp.single 2 j 1)
  exact (he j hj).trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

end
end RHTower
