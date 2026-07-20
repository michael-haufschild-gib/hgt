import GaloisForLFunctions.HilbertMetric.QuasiFreeFillingFano
import Mathlib.Algebra.Order.Chebyshev

/-!
# Quasi-free rank--variance discriminant law

This module removes the arbitrary energy unit from the quasi-free filling--bandwidth Fano law.
For a band-limited additive spectral observable it identifies a homogeneous rank--variance
discriminant with the sum of endpoint leakage and Hilbert--Schmidt compression anisotropy.  The
result is a sharp rank-refined Bhatia--Davis inequality and a noise-certified support-rank law.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The band budget left after subtracting quasi-free variance from the affine secant moment. -/
def quasiFreeSpectralBandBudget (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) (lower upper : ℝ) : ℝ :=
  (lower + upper) * quasiFreeSpectralMean v energy occupation -
    lower * upper * (∑ i, occupation i) -
      quasiFreeSpectralVariance v energy occupation

/-- Homogeneous rank--variance discriminant of a band-limited quasi-free observable. -/
def quasiFreeSpectralRankVarianceDiscriminant
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) (lower upper : ℝ) : ℝ :=
  (Fintype.card ι : ℝ) *
      quasiFreeSpectralBandBudget v energy occupation lower upper -
    quasiFreeSpectralMean v energy occupation ^ 2

/-- Trace-free Hilbert--Schmidt anisotropy of the occupation-compressed observable. -/
def quasiFreeSpectralCompressionAnisotropy
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ) *
      quasiFreeCompressedSpectralEnergy v energy occupation -
    quasiFreeSpectralMean v energy occupation ^ 2

/-- Ordered pairwise dispersion of the occupation-rescaled orbital spectral means. -/
def quasiFreeSpectralPairwiseMeanDefect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) : ℝ :=
  (∑ i, ∑ j,
      (occupation i * orbitalSpectralMean v energy i -
        occupation j * orbitalSpectralMean v energy j) ^ 2) / 2

/-- Squared Hilbert--Schmidt distance from the occupation compression to its own scalar trace
part.  The synthetic endpoints merely reuse the generic balanced-compression metric. -/
def quasiFreeMeanBalancedCompressionHilbertSchmidtSq
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) : ℝ :=
  quasiFreeBalancedCompressionHilbertSchmidtSq v energy occupation 0
    (1 + 2 * quasiFreeSpectralMean v energy occupation / (Fintype.card ι : ℝ))

/-- Rank-one endpoint model for the homogeneous rank--variance discriminant. -/
def quasiFreeEndpointPairRankVarianceDiscriminant
    (lower upper occupation p : ℝ) : ℝ :=
  let mean := lower * (1 - p) + upper * p
  let secondMoment := lower ^ 2 * (1 - p) + upper ^ 2 * p
  let totalMean := occupation * mean
  let variance := occupation * secondMoment - occupation ^ 2 * mean ^ 2
  (lower + upper) * totalMean - lower * upper * occupation - variance - totalMean ^ 2

/-- Every rank-one endpoint pair saturates the rank-refined variance law, at every occupation and
endpoint mixture. -/
theorem quasiFreeEndpointPairRankVarianceDiscriminant_zero
    (lower upper occupation p : ℝ) :
    quasiFreeEndpointPairRankVarianceDiscriminant lower upper occupation p = 0 := by
  unfold quasiFreeEndpointPairRankVarianceDiscriminant
  ring

omit [DecidableEq ι] in
/-- The affine band budget is exactly endpoint leakage plus compressed Hilbert--Schmidt energy. -/
theorem quasiFreeSpectralBandBudget_eq_secant_add_compressed
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (lower upper : ℝ) :
    quasiFreeSpectralBandBudget v energy occupation lower upper =
      quasiFreeSpectralSecantDefect v energy occupation lower upper +
        quasiFreeCompressedSpectralEnergy v energy occupation := by
  have hedge :
      quasiFreeSpectralSecantDefect v energy occupation lower upper =
        (lower + upper) * quasiFreeSpectralMean v energy occupation -
          lower * upper * (∑ i, occupation i) -
            ∑ i, occupation i * orbitalSpectralSecondMoment v energy i := by
    unfold quasiFreeSpectralSecantDefect quasiFreeSpectralMean
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [quasiFreeSpectralBandBudget, hedge, quasiFreeSpectralVariance]
  ring

omit [DecidableEq ι] in
/-- **Rank--variance two-defect identity.**  The homogeneous discriminant is exactly support
rank times endpoint leakage plus the trace-free Hilbert--Schmidt anisotropy of the compressed
observable. -/
theorem quasiFreeSpectralRankVarianceDiscriminant_two_defect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (lower upper : ℝ) :
    quasiFreeSpectralRankVarianceDiscriminant
        v energy occupation lower upper =
      (Fintype.card ι : ℝ) *
          quasiFreeSpectralSecantDefect v energy occupation lower upper +
        quasiFreeSpectralCompressionAnisotropy v energy occupation := by
  rw [quasiFreeSpectralRankVarianceDiscriminant,
    quasiFreeSpectralBandBudget_eq_secant_add_compressed,
    quasiFreeSpectralCompressionAnisotropy]
  ring

omit [DecidableEq ι] in
/-- Pairwise mean dispersion is nonnegative. -/
theorem quasiFreeSpectralPairwiseMeanDefect_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) :
    0 ≤ quasiFreeSpectralPairwiseMeanDefect v energy occupation := by
  unfold quasiFreeSpectralPairwiseMeanDefect
  exact div_nonneg
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (by norm_num)

omit [DecidableEq ι] in
/-- The pairwise defect is the scalar trace-free part of the diagonal compression energy. -/
theorem quasiFreeSpectralPairwiseMeanDefect_eq_card_mul_diagonal_sub_mean_sq
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) :
    quasiFreeSpectralPairwiseMeanDefect v energy occupation =
      (Fintype.card ι : ℝ) *
          (∑ i, (occupation i * orbitalSpectralMean v energy i) ^ 2) -
        quasiFreeSpectralMean v energy occupation ^ 2 := by
  let x : ι → ℝ := fun i => occupation i * orbitalSpectralMean v energy i
  have hinner (i : ι) :
      (∑ j, (x i - x j) ^ 2) =
        (Fintype.card ι : ℝ) * x i ^ 2 -
          2 * x i * (∑ j, x j) + ∑ j, x j ^ 2 := by
    calc
      (∑ j, (x i - x j) ^ 2) =
          ∑ j, (x i ^ 2 - 2 * x i * x j + x j ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (Fintype.card ι : ℝ) * x i ^ 2 -
          2 * x i * (∑ j, x j) + ∑ j, x j ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum]
  unfold quasiFreeSpectralPairwiseMeanDefect quasiFreeSpectralMean
  change (∑ i, ∑ j, (x i - x j) ^ 2) / 2 =
    (Fintype.card ι : ℝ) * (∑ i, x i ^ 2) - (∑ i, x i) ^ 2
  have hcross :
      (∑ i, 2 * x i * (∑ j, x j)) =
        2 * (∑ i, x i) * (∑ j, x j) := by
    calc
      (∑ i, 2 * x i * (∑ j, x j)) =
          ∑ i, (2 * (∑ j, x j)) * x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (2 * (∑ j, x j)) * (∑ i, x i) := by
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset ι))
            (f := x) (a := 2 * (∑ j, x j))).symm
      _ = 2 * (∑ i, x i) * (∑ j, x j) := by
        ring
  simp_rw [hinner]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- Compression anisotropy splits into pairwise diagonal dispersion and support-rank times
off-diagonal coherence. -/
theorem quasiFreeSpectralCompressionAnisotropy_eq_pairwise_add_coherence
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) :
    quasiFreeSpectralCompressionAnisotropy v energy occupation =
      quasiFreeSpectralPairwiseMeanDefect v energy occupation +
        (Fintype.card ι : ℝ) *
          quasiFreeSpectralCoherenceDefect v energy occupation := by
  rw [quasiFreeSpectralCompressionAnisotropy,
    quasiFreeCompressedSpectralEnergy_eq_diagonal_add_coherence,
    quasiFreeSpectralPairwiseMeanDefect_eq_card_mul_diagonal_sub_mean_sq]
  have hdiagonal :
      (∑ i, occupation i ^ 2 * orbitalSpectralMean v energy i ^ 2) =
        ∑ i, (occupation i * orbitalSpectralMean v energy i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiagonal]
  ring

/-- **Rank--variance three-defect identity.**  In coordinates the exact remainder is endpoint
leakage, pairwise dispersion of occupied orbital means, and off-diagonal compression coherence. -/
theorem quasiFreeSpectralRankVarianceDiscriminant_three_defect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (lower upper : ℝ) :
    quasiFreeSpectralRankVarianceDiscriminant
        v energy occupation lower upper =
      (Fintype.card ι : ℝ) *
          quasiFreeSpectralSecantDefect v energy occupation lower upper +
        quasiFreeSpectralPairwiseMeanDefect v energy occupation +
        (Fintype.card ι : ℝ) *
          quasiFreeSpectralCoherenceDefect v energy occupation := by
  rw [quasiFreeSpectralRankVarianceDiscriminant_two_defect,
    quasiFreeSpectralCompressionAnisotropy_eq_pairwise_add_coherence]
  ring

/-- Trace-free compression anisotropy is nonnegative for nonnegative occupations. -/
theorem quasiFreeSpectralCompressionAnisotropy_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) :
    0 ≤ quasiFreeSpectralCompressionAnisotropy v energy occupation := by
  rw [quasiFreeSpectralCompressionAnisotropy_eq_pairwise_add_coherence]
  exact add_nonneg
    (quasiFreeSpectralPairwiseMeanDefect_nonneg v energy occupation)
    (mul_nonneg (Nat.cast_nonneg _) <|
      quasiFreeSpectralCoherenceDefect_nonneg v energy occupation hoccupation)

/-- The trace-free compression anisotropy is literally support rank times a squared
Hilbert--Schmidt distance from the scalar trace part. -/
theorem quasiFreeSpectralCompressionAnisotropy_eq_card_mul_hilbertSchmidtSq
    [Nonempty ι]
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) :
    quasiFreeSpectralCompressionAnisotropy v energy occupation =
      (Fintype.card ι : ℝ) *
        quasiFreeMeanBalancedCompressionHilbertSchmidtSq v energy occupation := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [quasiFreeMeanBalancedCompressionHilbertSchmidtSq,
    quasiFreeBalancedCompressionHilbertSchmidtSq_eq_compressionDefect
      v energy occupation hoccupation,
    quasiFreeSpectralCompressionAnisotropy,
    quasiFreeSpectralCompressionDefect]
  field_simp [hcard]
  ring

/-- **Literal Hilbert--Schmidt two-defect law.**  For nonempty support, the discriminant is
support rank times the sum of endpoint leakage and squared metric anisotropy. -/
theorem quasiFreeSpectralRankVarianceDiscriminant_hilbertSchmidt_two_defect
    [Nonempty ι]
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) (lower upper : ℝ) :
    quasiFreeSpectralRankVarianceDiscriminant
        v energy occupation lower upper =
      (Fintype.card ι : ℝ) *
        (quasiFreeSpectralSecantDefect v energy occupation lower upper +
          quasiFreeMeanBalancedCompressionHilbertSchmidtSq v energy occupation) := by
  rw [quasiFreeSpectralRankVarianceDiscriminant_two_defect,
    quasiFreeSpectralCompressionAnisotropy_eq_card_mul_hilbertSchmidtSq
      v energy occupation hoccupation]
  ring

/-- The homogeneous rank--variance discriminant is nonnegative throughout the spectral band. -/
theorem quasiFreeSpectralRankVarianceDiscriminant_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    0 ≤ quasiFreeSpectralRankVarianceDiscriminant
      v energy occupation lower upper := by
  rw [quasiFreeSpectralRankVarianceDiscriminant_two_defect]
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) <|
      quasiFreeSpectralSecantDefect_nonneg
        v energy occupation hframe hoccupation lower upper hlower hupper)
    (quasiFreeSpectralCompressionAnisotropy_nonneg
      v energy occupation hoccupation)

/-- **Rank-refined quasi-free Bhatia--Davis law.**  This division-free form is valid even for an
empty support and is homogeneous under every change of energy units. -/
theorem quasiFreeSpectralVariance_rank_bhatiaDavis
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    quasiFreeSpectralMean v energy occupation ^ 2 +
        (Fintype.card ι : ℝ) * quasiFreeSpectralVariance v energy occupation ≤
      (Fintype.card ι : ℝ) *
        ((lower + upper) * quasiFreeSpectralMean v energy occupation -
          lower * upper * ∑ i, occupation i) := by
  have h := quasiFreeSpectralRankVarianceDiscriminant_nonneg
    v energy occupation hframe hoccupation lower upper hlower hupper
  unfold quasiFreeSpectralRankVarianceDiscriminant
    quasiFreeSpectralBandBudget at h
  nlinarith

/-- Equality in the rank--variance bound is exactly simultaneous vanishing of endpoint leakage
and compression anisotropy, for nonempty support. -/
theorem quasiFreeSpectralRankVarianceDiscriminant_eq_zero_iff
    [Nonempty ι]
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    quasiFreeSpectralRankVarianceDiscriminant
        v energy occupation lower upper = 0 ↔
      quasiFreeSpectralSecantDefect v energy occupation lower upper = 0 ∧
        quasiFreeSpectralCompressionAnisotropy v energy occupation = 0 := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hedge := quasiFreeSpectralSecantDefect_nonneg
    v energy occupation hframe hoccupation lower upper hlower hupper
  have hanisotropy := quasiFreeSpectralCompressionAnisotropy_nonneg
    v energy occupation hoccupation
  rw [quasiFreeSpectralRankVarianceDiscriminant_two_defect]
  constructor
  · intro hzero
    constructor <;> nlinarith
  · rintro ⟨hedge0, hanisotropy0⟩
    rw [hedge0, hanisotropy0]
    ring

/-- First two cumulants give a tomography-free lower certificate for support rank whenever the
observable band budget is positive. -/
theorem quasiFreeSpectral_support_rank_lower_bound
    [Nonempty ι]
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper)
    (hbudget : 0 < quasiFreeSpectralBandBudget v energy occupation lower upper) :
    quasiFreeSpectralMean v energy occupation ^ 2 /
        quasiFreeSpectralBandBudget v energy occupation lower upper ≤
      (Fintype.card ι : ℝ) := by
  rw [div_le_iff₀ hbudget]
  have h := quasiFreeSpectralRankVarianceDiscriminant_nonneg
    v energy occupation hframe hoccupation lower upper hlower hupper
  unfold quasiFreeSpectralRankVarianceDiscriminant at h
  nlinarith

/-- The rank--variance theorem strictly contains the earlier fixed-unit Fano floor: completing the
remaining scalar square recovers the filling--bandwidth bound. -/
theorem quasiFreeSpectralFanoMargin_lower_bound_of_rankVariance
    [Nonempty ι]
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    lower * upper * (∑ i, occupation i) -
        (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4 ≤
      quasiFreeSpectralFanoMargin v energy occupation := by
  have hrank := quasiFreeSpectralVariance_rank_bhatiaDavis
    v energy occupation hframe hoccupation lower upper hlower hupper
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hsquare :
      0 ≤ (2 * quasiFreeSpectralMean v energy occupation -
        (Fintype.card ι : ℝ) * (lower + upper - 1)) ^ 2 := sq_nonneg _
  unfold quasiFreeSpectralFanoMargin
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- Scaling the one-particle energy scales each orbital spectral mean linearly. -/
theorem orbitalSpectralMean_scale
    (c : ℝ) (v : ι → κ → ℝ) (energy : κ → ℝ) (i : ι) :
    orbitalSpectralMean v (fun k => c * energy k) i =
      c * orbitalSpectralMean v energy i := by
  unfold orbitalSpectralMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
/-- Scaling the one-particle energy scales its quasi-free mean linearly. -/
theorem quasiFreeSpectralMean_scale
    (c : ℝ) (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) :
    quasiFreeSpectralMean v (fun k => c * energy k) occupation =
      c * quasiFreeSpectralMean v energy occupation := by
  unfold quasiFreeSpectralMean
  simp_rw [orbitalSpectralMean_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Scaling the one-particle energy scales its second spectral moment quadratically. -/
theorem orbitalSpectralSecondMoment_scale
    (c : ℝ) (v : ι → κ → ℝ) (energy : κ → ℝ) (i : ι) :
    orbitalSpectralSecondMoment v (fun k => c * energy k) i =
      c ^ 2 * orbitalSpectralSecondMoment v energy i := by
  unfold orbitalSpectralSecondMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
/-- Scaling the one-particle energy scales compressed Hilbert--Schmidt energy quadratically. -/
theorem quasiFreeCompressedSpectralEnergy_scale
    (c : ℝ) (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) :
    quasiFreeCompressedSpectralEnergy v (fun k => c * energy k) occupation =
      c ^ 2 * quasiFreeCompressedSpectralEnergy v energy occupation := by
  unfold quasiFreeCompressedSpectralEnergy
  have hinner (i j : ι) :
      (∑ k, (c * energy k) * v i k * v j k) =
        c * ∑ k, energy k * v i k * v j k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hinner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
/-- Scaling the one-particle energy scales quasi-free variance quadratically. -/
theorem quasiFreeSpectralVariance_scale
    (c : ℝ) (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) :
    quasiFreeSpectralVariance v (fun k => c * energy k) occupation =
      c ^ 2 * quasiFreeSpectralVariance v energy occupation := by
  unfold quasiFreeSpectralVariance
  rw [quasiFreeCompressedSpectralEnergy_scale]
  simp_rw [orbitalSpectralSecondMoment_scale]
  have hsum :
      (∑ i, occupation i *
        (c ^ 2 * orbitalSpectralSecondMoment v energy i)) =
        c ^ 2 * ∑ i, occupation i * orbitalSpectralSecondMoment v energy i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

omit [DecidableEq ι] in
/-- **Energy-unit covariance.**  The rank--variance discriminant is homogeneous of degree two
under simultaneous scaling of the observable and both spectral endpoints. -/
theorem quasiFreeSpectralRankVarianceDiscriminant_scale
    (c : ℝ) (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (lower upper : ℝ) :
    quasiFreeSpectralRankVarianceDiscriminant
        v (fun k => c * energy k) occupation (c * lower) (c * upper) =
      c ^ 2 * quasiFreeSpectralRankVarianceDiscriminant
        v energy occupation lower upper := by
  unfold quasiFreeSpectralRankVarianceDiscriminant quasiFreeSpectralBandBudget
  rw [quasiFreeSpectralMean_scale, quasiFreeSpectralVariance_scale]
  ring

end

end GaloisForLFunctions.HilbertMetric
