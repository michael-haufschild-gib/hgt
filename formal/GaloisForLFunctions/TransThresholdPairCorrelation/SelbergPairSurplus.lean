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

/-- Cauchy--Schwarz between two finite Selberg packets. -/
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

private theorem selbergPacketEnergy_eq_gram {n : ℕ} (x w : Fin n → ℝ) :
    HTGeometry.realKernelPacketEnergy selbergKernel x w = selbergGram x w := by
  unfold HTGeometry.realKernelPacketEnergy selbergGram
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show x j - x i = -(x i - x j) by ring, selbergKernel_even]
  ring

private theorem selbergPacketCross_symm {n : ℕ} (x u v : Fin n → ℝ) :
    HTGeometry.realKernelPacketCross selbergKernel x v x u =
      HTGeometry.realKernelPacketCross selbergKernel x u x v := by
  unfold HTGeometry.realKernelPacketCross
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show x i - x j = -(x j - x i) by ring, selbergKernel_even]
  ring

private theorem selbergGram_sub {n : ℕ} (x u v : Fin n → ℝ) :
    selbergGram x (u - v) = selbergGram x u + selbergGram x v -
      2 * HTGeometry.realKernelPacketCross selbergKernel x u x v := by
  have he : HTGeometry.realKernelPacketEnergy selbergKernel x (u - v) =
      HTGeometry.realKernelPacketEnergy selbergKernel x u +
        HTGeometry.realKernelPacketEnergy selbergKernel x v -
        HTGeometry.realKernelPacketCross selbergKernel x u x v -
        HTGeometry.realKernelPacketCross selbergKernel x v x u := by
    unfold HTGeometry.realKernelPacketEnergy HTGeometry.realKernelPacketCross
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [selbergPacketEnergy_eq_gram, selbergPacketEnergy_eq_gram,
    selbergPacketEnergy_eq_gram, selbergPacketCross_symm x u v] at he
  linarith only [he]

/-- Sharp centered deletion law for the explicit Selberg correlation. -/
theorem selbergGram_deletion_centered {n : ℕ} (x u v : Fin n → ℝ) :
    (selbergGram x (u - v) - selbergGram x u - selbergGram x v) ^ 2 ≤
      4 * selbergGram x u * selbergGram x v := by
  have h := selbergPacketCross_sq_le x u x v
  rw [selbergPacketEnergy_eq_gram, selbergPacketEnergy_eq_gram] at h
  rw [selbergGram_sub]
  nlinarith only [h]

/-- Every exceptional direction pays its complete energy and geometric-mean interaction. -/
theorem selbergGram_deletion_error {n : ℕ} (x u v : Fin n → ℝ) :
    |selbergGram x (u - v) - selbergGram x u| ≤ selbergGram x v +
      2 * Real.sqrt (selbergGram x u * selbergGram x v) := by
  have h := selbergPacketCross_sq_le x u x v
  rw [selbergPacketEnergy_eq_gram, selbergPacketEnergy_eq_gram] at h
  have ha : |HTGeometry.realKernelPacketCross selbergKernel x u x v| ≤
      Real.sqrt (selbergGram x u * selbergGram x v) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  have hb := abs_le.mp ha
  rw [selbergGram_sub, abs_le]
  constructor <;> linarith [selbergGram_nonneg x v]

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

/-- Original correlation surplus still forces close pairs after any exceptional nodes are deleted.
The exceptional cost is explicit; no density or zero-counting estimate is assumed. -/
theorem selberg_surplus_after_deletion {n : ℕ} (x : Fin n → ℝ)
    (m : Fin n → ℝ≥0) (e : Finset (Fin n)) :
    selbergGram x (fun i => m i) -
      (selbergGram x (fun i => if i ∈ e then (m i : ℝ) else 0) +
        2 * Real.sqrt (selbergGram x (fun i => m i) *
          selbergGram x (fun i => if i ∈ e then (m i : ℝ) else 0))) -
      (∑ i, (if i ∈ e then (0 : ℝ) else (m i : ℝ)) ^ 2) ≤
      selbergClosePairMass x (fun i => if i ∈ e then 0 else m i) := by
  let u : Fin n → ℝ := fun i => m i
  let v : Fin n → ℝ := fun i => if i ∈ e then m i else 0
  let r : Fin n → ℝ≥0 := fun i => if i ∈ e then 0 else m i
  have he : (fun i => (r i : ℝ)) = u - v := by
    funext i
    dsimp only [r, u, v, Pi.sub_apply]
    split_ifs <;> simp
  have herror := (abs_le.mp (selbergGram_deletion_error x u v)).1
  have hpair := selbergGram_sub_diagonal_le_closePairs x r
  have hdiag : (∑ i, (r i : ℝ) ^ 2) =
      ∑ i, (if i ∈ e then (0 : ℝ) else (m i : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [r]
    split_ifs <;> simp
  rw [hdiag, he] at hpair
  change selbergGram x u - (selbergGram x v + 2 * Real.sqrt (selbergGram x u * selbergGram x v)) -
    (∑ i, (if i ∈ e then (0 : ℝ) else (m i : ℝ)) ^ 2) ≤ selbergClosePairMass x r
  linarith only [herror, hpair]

end
end GaloisForLFunctions.TransThresholdPairCorrelation

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergGram_sub_diagonal_le_closePairs

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergGram_nonneg

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergGram_sub_card_le_closePairCard
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergKernel_positiveDefinite
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergPacketCross_sq_le
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergPacketChannelGram_posSemidef

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergGram_deletion_centered
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selberg_surplus_after_deletion
