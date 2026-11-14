import GaloisForLFunctions.TransThresholdPairCorrelation.SelbergGapKernel
import GaloisForLFunctions.RHTower.AtlasBlindToUnfolded
import GaloisForLFunctions.RHTower.EvenSectorCosineBochner
import GaloisForLFunctions.HTGeometry.PositiveDefinitePacketCauchy

/-!
# From Selberg correlation surplus to close pairs

The explicit positive Fourier profile makes the complete finite correlation
nonnegative. Its sign outside the unit gap and its sharp diagonal bound turn
any surplus over self-pairs into close-pair mass, with arbitrary multiplicities.
-/

open Real MeasureTheory
open scoped BigOperators NNReal
namespace GaloisForLFunctions.TransThresholdPairCorrelation
noncomputable section

/-- Complete finite Selberg correlation, including its diagonal. -/
def selbergGram {n : ℕ} (x w : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * selbergKernel (x i - x j)

/-- The complete correlation is an integral of squared cosine and sine packets. -/
theorem selbergGram_eq_integral {n : ℕ} (x w : Fin n → ℝ) :
    selbergGram x w = 2 * ∫ u in (0 : ℝ)..1, selbergProfile u *
      ((∑ i, w i * cos ((2 * π * u) * x i)) ^ 2 +
        (∑ i, w i * sin ((2 * π * u) * x i)) ^ 2) := by
  simp_rw [← RHTower.pair_correlation_eq_squares w x, Finset.mul_sum]
  have hi (i j : Fin n) : IntervalIntegrable
      (fun u => selbergProfile u * (w i * w j * cos ((2 * π * u) * (x i - x j)))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold selbergProfile
    fun_prop
  have houter (i : Fin n) : IntervalIntegrable (fun u => ∑ j,
      selbergProfile u * (w i * w j * cos ((2 * π * u) * (x i - x j)))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold selbergProfile
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun i _ => houter i)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => hi _ j)]
  unfold selbergGram selbergKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun u => selbergProfile u * (w i * w j * cos ((2 * π * u) * (x i - x j)))) =
      fun u => (w i * w j) * (selbergProfile u * cos (2 * π * (x i - x j) * u)) := by
    funext u
    rw [show (2 * π * u) * (x i - x j) = 2 * π * (x i - x j) * u by ring]
    ring
  rw [he, intervalIntegral.integral_const_mul]
  ring

/-- The explicit kernel has nonnegative Gram energy for arbitrary signed coefficients. -/
theorem selbergGram_nonneg {n : ℕ} (x w : Fin n → ℝ) : 0 ≤ selbergGram x w := by
  rw [selbergGram_eq_integral]
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  exact mul_nonneg (selbergProfile_nonneg ⟨u, hu⟩) (add_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem selbergKernel_even (x : ℝ) : selbergKernel (-x) = selbergKernel x := by
  simp only [selbergKernel, mul_neg, neg_mul, cos_neg]

/-- The Selberg profile supplies the actual complex positive-definite kernel. -/
theorem selbergKernel_positiveDefinite :
    HTGeometry.PositiveDefiniteOnReal (fun x => (selbergKernel x : ℂ)) := by
  apply RHTower.EvenSector.positiveDefiniteOnReal_of_real selbergKernel_even
  intro n x w
  rw [Finset.sum_comm]
  simpa only [selbergGram, mul_comm] using selbergGram_nonneg x w

/-- The corpus's two-packet Cauchy law applies to the explicit Selberg kernel. -/
theorem selbergPacketCross_sq_le {N M : ℕ} (s a : Fin N → ℝ) (t b : Fin M → ℝ) :
    HTGeometry.realKernelPacketCross selbergKernel s a t b ^ 2 ≤
      HTGeometry.realKernelPacketEnergy selbergKernel s a *
        HTGeometry.realKernelPacketEnergy selbergKernel t b :=
  HTGeometry.realKernelPacketCross_sq_le_energy_mul_energy_of_positiveDefinite
    selbergKernel selbergKernel_positiveDefinite selbergKernel_even s a t b

/-- Every finite family of Selberg packet channels has a positive-semidefinite Gram. -/
theorem selbergPacketChannelGram_posSemidef {M N : ℕ}
    (t b : Fin M → Fin N → ℝ) :
    (HTGeometry.realKernelPacketChannelGram selbergKernel t b).PosSemidef :=
  HTGeometry.realKernelPacketChannelGram_posSemidef_of_positiveDefinite
    selbergKernel selbergKernel_positiveDefinite selbergKernel_even t b

/-- Weighted mass of ordered distinct pairs within the unit gap. -/
def selbergClosePairMass {n : ℕ} (x : Fin n → ℝ) (m : Fin n → ℝ≥0) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ |x i - x j| ≤ 1 then (m i : ℝ) * (m j : ℝ) else 0

/-- Correlation surplus forces close-pair mass with constant one. -/
theorem selbergGram_sub_diagonal_le_closePairs {n : ℕ}
    (x : Fin n → ℝ) (m : Fin n → ℝ≥0) :
    selbergGram x (fun i => m i) - ∑ i, (m i : ℝ) ^ 2 ≤ selbergClosePairMass x m := by
  have hpoint (i j : Fin n) :
      (m i : ℝ) * (m j : ℝ) * selbergKernel (x i - x j) ≤
        (if i = j then (m i : ℝ) ^ 2 else 0) +
          (if i ≠ j ∧ |x i - x j| ≤ 1 then (m i : ℝ) * (m j : ℝ) else 0) := by
    by_cases he : i = j
    · subst j
      simp [pow_two]
    · simp only [he, ↓reduceIte, ne_eq, not_false_eq_true, true_and, zero_add]
      have h := mul_le_mul_of_nonneg_left (selbergKernel_le_indicator (x i - x j))
        (mul_nonneg (m i).coe_nonneg (m j).coe_nonneg)
      split_ifs with hg <;> simpa only [hg, ↓reduceIte, mul_one, mul_zero] using h
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpoint i j
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h
  change selbergGram x (fun i => m i) ≤ (∑ i, (m i : ℝ) ^ 2) + selbergClosePairMass x m at h
  linarith only [h]

/-- For unit masses, the surplus is paid by the number of ordered close pairs. -/
theorem selbergGram_sub_card_le_closePairCard {n : ℕ} (x : Fin n → ℝ) :
    selbergGram x (fun _ => 1) - n ≤
      ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ |x p.1 - x p.2| ≤ 1)).card : ℝ) := by
  have h := selbergGram_sub_diagonal_le_closePairs x (fun _ => 1)
  have hc : selbergClosePairMass x (fun _ => 1) =
      ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ |x p.1 - x p.2| ≤ 1)).card : ℝ) := by
    unfold selbergClosePairMass
    simp only [NNReal.coe_one, one_mul]
    rw [← Finset.sum_product']
    simp only [Finset.univ_product_univ, Finset.sum_boole]
  simpa only [NNReal.coe_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, hc] using h

end
end GaloisForLFunctions.TransThresholdPairCorrelation

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergGram_sub_diagonal_le_closePairs

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergGram_nonneg

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergGram_sub_card_le_closePairCard
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergKernel_positiveDefinite
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergPacketCross_sq_le
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergPacketChannelGram_posSemidef
