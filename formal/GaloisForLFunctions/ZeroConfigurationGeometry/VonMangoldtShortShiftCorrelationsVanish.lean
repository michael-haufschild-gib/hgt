import GaloisForLFunctions.ZeroConfigurationGeometry.VonMangoldtMomentDiagonalsVanish

/-!
# Vanishing arithmetic correlations along short additive shifts

Every injective index map has correlation bounded by the coefficient-square
diagonal. For normalized von Mangoldt moments, summing the absolute correlations
over `1 ≤ h ≤ floor(r^k)` still tends to zero when `r < R²` and
`1 < R < Re s - 1/2`. This is uniform in the ordinate and uses only `Λ(n) ≤ log n`.
-/

open Filter Topology ComplexConjugate

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- An injective change of integer index cannot increase the square-energy bound
for an absolutely convergent correlation. -/
theorem norm_tsum_mul_conj_comp_le_diagonal {a : ℕ → ℂ}
    (ha : Summable (fun n => ‖a n‖ ^ 2)) {i : ℕ → ℕ}
    (hi : Function.Injective i) :
    ‖∑' n : ℕ, a n * conj (a (i n))‖ ≤ ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hshift : Summable (fun n => ‖a (i n)‖ ^ 2) := ha.comp_injective hi
  have hshift_le : (∑' n : ℕ, ‖a (i n)‖ ^ 2) ≤ ∑' n : ℕ, ‖a n‖ ^ 2 :=
    tsum_comp_le_tsum_of_inj ha (fun n => sq_nonneg _) hi
  have hmajor := (ha.add hshift).div_const 2
  have hbound (n : ℕ) : ‖a n‖ * ‖a (i n)‖ ≤
      (‖a n‖ ^ 2 + ‖a (i n)‖ ^ 2) / 2 := by
    nlinarith only [sq_nonneg (‖a n‖ - ‖a (i n)‖)]
  have hprod : Summable (fun n => ‖a n‖ * ‖a (i n)‖) :=
    hmajor.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
  have hnorm : Summable (fun n => ‖a n * conj (a (i n))‖) := by
    simpa only [norm_mul, Complex.norm_conj] using hprod
  calc
    _ ≤ ∑' n : ℕ, ‖a n * conj (a (i n))‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : ℕ, ‖a n‖ * ‖a (i n)‖ := by simp only [norm_mul, Complex.norm_conj]
    _ ≤ ∑' n : ℕ, (‖a n‖ ^ 2 + ‖a (i n)‖ ^ 2) / 2 :=
      hprod.tsum_le_tsum hbound hmajor
    _ = ((∑' n : ℕ, ‖a n‖ ^ 2) + ∑' n : ℕ, ‖a (i n)‖ ^ 2) / 2 := by
      rw [tsum_div_const, ha.tsum_add hshift]
    _ ≤ ∑' n : ℕ, ‖a n‖ ^ 2 := by linarith only [hshift_le]

/-- Every additive shift obeys the same geometric bound as the diagonal. -/
theorem normalizedMangoldtShiftCorrelation_le_geometric {s : ℂ} {R : ℝ}
    (hR : 0 < R) (hRs : R < s.re - 1 / 2) (k h : ℕ) :
    ‖∑' n : ℕ,
      (LSeries.term (LSeries.logMul^[k]
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s n /
          (k.factorial : ℂ)) *
      conj (LSeries.term (LSeries.logMul^[k]
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s (n + h) /
          (k.factorial : ℂ))‖ ≤
      ((1 / R) ^ k) ^ 2 * ∑' n : ℕ,
        ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(2 * (s.re - R))) := by
  have hbase := (summable_vonMangoldt_sq_rpow
    (α := 2 * (s.re - R)) (by linarith only [hRs])).mul_left ((((1 : ℝ) / R) ^ k) ^ 2)
  have hdiag : Summable (fun n : ℕ => normalizedMangoldtCoefficient s.re 1 k n ^ 2) := by
    apply hbase.of_nonneg_of_le (fun n => sq_nonneg _)
    simpa only [one_mul] using
      (normalizedMangoldtCoefficient_sq_le_geometric (σ := s.re)
        (d := 1) (by norm_num) hR k)
  have hnormdiag : Summable (fun n : ℕ =>
      ‖LSeries.term (LSeries.logMul^[k]
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s n /
          (k.factorial : ℂ)‖ ^ 2) := by
    simpa only [norm_normalizedMangoldtTerm] using hdiag
  calc
    _ ≤ ∑' n : ℕ,
        ‖LSeries.term (LSeries.logMul^[k]
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s n /
            (k.factorial : ℂ)‖ ^ 2 :=
      norm_tsum_mul_conj_comp_le_diagonal hnormdiag (fun _ _ h => Nat.add_right_cancel h)
    _ ≤ _ := by
      simpa only [norm_normalizedMangoldtTerm, one_mul] using
        (normalizedMangoldtDiagonal_le_geometric (σ := s.re)
          (d := 1) (by norm_num) hR hRs k)

/-- Below the geometric diagonal threshold, even exponentially many additive
shift correlations have total absolute value tending to zero. -/
theorem tendsto_normalizedMangoldtShortShiftCorrelations_zero {s : ℂ} {R r : ℝ}
    (hR : 1 < R) (hRs : R < s.re - 1 / 2) (hr : 0 ≤ r) (hrR : r < R ^ 2) :
    let a : ℕ → ℕ → ℂ := fun k n =>
      LSeries.term (LSeries.logMul^[k]
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s n /
          (k.factorial : ℂ)
    Tendsto (fun k : ℕ => ∑ h ∈ Finset.range ⌊r ^ k⌋₊,
      ‖∑' n : ℕ, a k n * conj (a k (n + (h + 1)))‖) atTop (𝓝 0) := by
  dsimp only
  let C : ℝ := ∑' n : ℕ,
    ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(2 * (s.re - R)))
  have hC : 0 ≤ C := tsum_nonneg fun n => by positivity
  have hR0 : 0 < R := lt_trans zero_lt_one hR
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg hr (sq_nonneg R))
    ((div_lt_one (sq_pos_of_pos hR0)).mpr hrR)).mul_const C
  simp only [zero_mul] at hlim
  apply squeeze_zero (fun k => Finset.sum_nonneg fun h _ => norm_nonneg _) _ hlim
  intro k
  calc
    _ ≤ ∑ h ∈ Finset.range ⌊r ^ k⌋₊, ((1 / R) ^ k) ^ 2 * C :=
      Finset.sum_le_sum fun h _ => normalizedMangoldtShiftCorrelation_le_geometric hR0 hRs k (h + 1)
    _ = (⌊r ^ k⌋₊ : ℝ) * (((1 / R) ^ k) ^ 2 * C) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ r ^ k * (((1 / R) ^ k) ^ 2 * C) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (pow_nonneg hr k))
        (mul_nonneg (sq_nonneg _) hC)
    _ = (r / R ^ 2) ^ k * C := by
      have hpow : ((1 / R) ^ k) ^ 2 = 1 / (R ^ 2) ^ k := by
        simp only [div_pow, one_pow, ← pow_mul]
        rw [Nat.mul_comm k 2]
      rw [hpow, ← mul_assoc, mul_one_div, ← div_pow]

#print axioms norm_tsum_mul_conj_comp_le_diagonal
#print axioms tendsto_normalizedMangoldtShortShiftCorrelations_zero

end GaloisForLFunctions.ZeroConfigurationGeometry
