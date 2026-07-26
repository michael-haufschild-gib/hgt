import GaloisForLFunctions.HilbertMetric.SpectralBandwidthFano

/-!
# Quasi-free filling--bandwidth Fano law

This module extends the Slater spectral-bandwidth law from projection densities to arbitrary
finite positive occupation profiles.  The exact mean-minus-variance identity has a universal
floor controlled by total filling and support rank, plus occupation-weighted endpoint leakage,
occupation--energy centering, and coherence defects.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Mean of an additive spectral observable in a diagonal quasi-free occupation profile. -/
def quasiFreeSpectralMean (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) : ℝ :=
  ∑ i, occupation i * orbitalSpectralMean v energy i

/-- Occupation-weighted squared Hilbert--Schmidt energy of the compressed observable. -/
def quasiFreeCompressedSpectralEnergy (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, occupation i * occupation j *
    (∑ k, energy k * v i k * v j k) ^ 2

/-- Variance of an additive spectral observable in the finite quasi-free compression formula. -/
def quasiFreeSpectralVariance (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) : ℝ :=
  (∑ i, occupation i * orbitalSpectralSecondMoment v energy i) -
    quasiFreeCompressedSpectralEnergy v energy occupation

/-- Mean-minus-variance margin of the finite quasi-free spectral observable. -/
def quasiFreeSpectralFanoMargin (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) : ℝ :=
  quasiFreeSpectralMean v energy occupation -
    quasiFreeSpectralVariance v energy occupation

/-- Occupation-weighted failure of the orbitals to lie on the two spectral endpoints. -/
def quasiFreeSpectralSecantDefect (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) (lower upper : ℝ) : ℝ :=
  ∑ i, occupation i * ((lower + upper) * orbitalSpectralMean v energy i -
    lower * upper - orbitalSpectralSecondMoment v energy i)

/-- Squared failure of each occupation-rescaled orbital mean to balance the affine secant. -/
def quasiFreeSpectralCenteringDefect (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) (lower upper : ℝ) : ℝ :=
  ∑ i, (occupation i * orbitalSpectralMean v energy i -
    (lower + upper - 1) / 2) ^ 2

/-- Occupation-weighted off-diagonal energy of the compressed spectral observable. -/
def quasiFreeSpectralCoherenceDefect (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, occupation i * occupation j *
    (∑ k, energy k * v i k * v j k) ^ 2

/-- Basis-invariant trace polynomial representing squared Hilbert--Schmidt displacement of the
occupation-compressed observable from the balancing scalar on its support. -/
def quasiFreeSpectralCompressionDefect (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) (lower upper : ℝ) : ℝ :=
  quasiFreeCompressedSpectralEnergy v energy occupation -
    (lower + upper - 1) * quasiFreeSpectralMean v energy occupation +
    (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4

/-- Matrix of the occupation-compressed observable displaced from the balancing scalar.  For a
positive one-body density this is the coordinate matrix of
`Γ^(1/2) A Γ^(1/2) - ((lower + upper - 1) / 2) P_Γ` on its support. -/
def quasiFreeBalancedCompressionMatrix (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) (lower upper : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    Real.sqrt (occupation i) * Real.sqrt (occupation j) *
        (∑ k, energy k * v i k * v j k) -
      if i = j then (lower + upper - 1) / 2 else 0

/-- Squared Hilbert--Schmidt norm of the balanced occupation-compression matrix. -/
def quasiFreeBalancedCompressionHilbertSchmidtSq
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (occupation : ι → ℝ) (lower upper : ℝ) : ℝ :=
  ∑ i, ∑ j,
    quasiFreeBalancedCompressionMatrix v energy occupation lower upper i j ^ 2

/-- Rank-one quasi-free Fano margin for an orbital supported on two spectral endpoints. -/
def quasiFreeEndpointPairSpectralFanoMargin
    (lower upper occupation p : ℝ) : ℝ :=
  let mean := lower * (1 - p) + upper * p
  let secondMoment := lower ^ 2 * (1 - p) + upper ^ 2 * p
  occupation * mean -
    (occupation * secondMoment - occupation ^ 2 * mean ^ 2)

/-- **Quasi-free endpoint-pair square law.**  The rank-one endpoint model has exactly the
rank--filling floor plus one occupation--energy centering square. -/
theorem quasiFreeEndpointPairSpectralFanoMargin_square
    (lower upper occupation p : ℝ) :
    quasiFreeEndpointPairSpectralFanoMargin lower upper occupation p =
      occupation * lower * upper - (lower + upper - 1) ^ 2 / 4 +
        (occupation * (lower * (1 - p) + upper * p) -
          (lower + upper - 1) / 2) ^ 2 := by
  unfold quasiFreeEndpointPairSpectralFanoMargin
  ring

/-- At positive-degree bandwidth `1,...,M`, filling `M/4` and the endpoint mixture of mean two
attain the zero-margin phase boundary. -/
theorem positiveDegree_quasiFreeEndpointPair_at_filling_boundary
    (maxDegree : ℝ) (hwidth : maxDegree - 1 ≠ 0) :
    quasiFreeEndpointPairSpectralFanoMargin 1 maxDegree
        (maxDegree / 4) (1 / (maxDegree - 1)) = 0 := by
  rw [quasiFreeEndpointPairSpectralFanoMargin_square]
  field_simp
  ring

/-- The quasi-free compression energy splits into its occupation-weighted diagonal and
off-diagonal parts. -/
theorem quasiFreeCompressedSpectralEnergy_eq_diagonal_add_coherence
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ) :
    quasiFreeCompressedSpectralEnergy v energy occupation =
      (∑ i, occupation i ^ 2 * orbitalSpectralMean v energy i ^ 2) +
        quasiFreeSpectralCoherenceDefect v energy occupation := by
  unfold quasiFreeCompressedSpectralEnergy quasiFreeSpectralCoherenceDefect
  calc
    (∑ i, ∑ j, occupation i * occupation j *
        (∑ k, energy k * v i k * v j k) ^ 2) =
        ∑ i, (occupation i * occupation i *
          (∑ k, energy k * v i k * v i k) ^ 2 +
          ∑ j ∈ Finset.univ.erase i, occupation i * occupation j *
            (∑ k, energy k * v i k * v j k) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_erase_add Finset.univ
        (fun j => occupation i * occupation j *
          (∑ k, energy k * v i k * v j k) ^ 2) (Finset.mem_univ i)]
      ring
    _ = (∑ i, occupation i ^ 2 * orbitalSpectralMean v energy i ^ 2) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, occupation i * occupation j *
          (∑ k, energy k * v i k * v j k) ^ 2 := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      unfold orbitalSpectralMean
      have hdiag :
          (∑ k, energy k * v i k * v i k) =
            ∑ k, energy k * v i k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hdiag]
      ring

/-- Endpoint leakage is nonnegative for nonnegative occupations in the stated spectral band. -/
theorem quasiFreeSpectralSecantDefect_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    0 ≤ quasiFreeSpectralSecantDefect v energy occupation lower upper := by
  unfold quasiFreeSpectralSecantDefect
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hoccupation i) (by
      have hsecond := orbitalSpectralSecondMoment_le_secant
        v energy hframe lower upper hlower hupper i
      linarith)

omit [DecidableEq ι] in
/-- Occupation--energy centering is a sum of squares. -/
theorem quasiFreeSpectralCenteringDefect_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (lower upper : ℝ) :
    0 ≤ quasiFreeSpectralCenteringDefect v energy occupation lower upper := by
  unfold quasiFreeSpectralCenteringDefect
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Weighted occupied coherence is nonnegative for nonnegative occupations. -/
theorem quasiFreeSpectralCoherenceDefect_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) :
    0 ≤ quasiFreeSpectralCoherenceDefect v energy occupation := by
  unfold quasiFreeSpectralCoherenceDefect
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hoccupation i) (hoccupation j)) (sq_nonneg _)

/-- The invariant compression defect is exactly the sum of occupation-centering and weighted
coherence.  This is the coordinate expansion of a squared Hilbert--Schmidt distance. -/
theorem quasiFreeSpectralCompressionDefect_eq_centering_add_coherence
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (lower upper : ℝ) :
    quasiFreeSpectralCompressionDefect v energy occupation lower upper =
      quasiFreeSpectralCenteringDefect v energy occupation lower upper +
        quasiFreeSpectralCoherenceDefect v energy occupation := by
  rw [quasiFreeSpectralCompressionDefect,
    quasiFreeCompressedSpectralEnergy_eq_diagonal_add_coherence]
  unfold quasiFreeSpectralMean quasiFreeSpectralCenteringDefect
  have hsquares :
      (∑ i, (occupation i * orbitalSpectralMean v energy i -
        (lower + upper - 1) / 2) ^ 2) =
      ∑ i, (occupation i ^ 2 * orbitalSpectralMean v energy i ^ 2 -
        (lower + upper - 1) * occupation i * orbitalSpectralMean v energy i +
        (lower + upper - 1) ^ 2 / 4) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsquares, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  ring_nf

/-- The literal squared Hilbert--Schmidt metric of the balanced compression expands into the
occupation-centering and weighted-coherence defects. -/
theorem quasiFreeBalancedCompressionHilbertSchmidtSq_eq_centering_add_coherence
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) (lower upper : ℝ) :
    quasiFreeBalancedCompressionHilbertSchmidtSq
        v energy occupation lower upper =
      quasiFreeSpectralCenteringDefect v energy occupation lower upper +
        quasiFreeSpectralCoherenceDefect v energy occupation := by
  unfold quasiFreeBalancedCompressionHilbertSchmidtSq
  calc
    (∑ i, ∑ j,
        quasiFreeBalancedCompressionMatrix v energy occupation lower upper i j ^ 2) =
      ∑ i, (quasiFreeBalancedCompressionMatrix
          v energy occupation lower upper i i ^ 2 +
        ∑ j ∈ Finset.univ.erase i,
          quasiFreeBalancedCompressionMatrix
            v energy occupation lower upper i j ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_erase_add Finset.univ
        (fun j => quasiFreeBalancedCompressionMatrix
          v energy occupation lower upper i j ^ 2) (Finset.mem_univ i)]
      ring
    _ = ∑ i, ((occupation i * orbitalSpectralMean v energy i -
          (lower + upper - 1) / 2) ^ 2 +
        ∑ j ∈ Finset.univ.erase i, occupation i * occupation j *
          (∑ k, energy k * v i k * v j k) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      · have hsqrt : Real.sqrt (occupation i) * Real.sqrt (occupation i) =
            occupation i := by
          rw [← pow_two, Real.sq_sqrt (hoccupation i)]
        have hmean : (∑ k, energy k * v i k * v i k) =
            orbitalSpectralMean v energy i := by
          unfold orbitalSpectralMean
          apply Finset.sum_congr rfl
          intro k _
          ring
        simp only [quasiFreeBalancedCompressionMatrix, Matrix.of_apply, if_pos]
        rw [hsqrt, hmean]
      · apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hij : i ≠ j := Ne.symm hji
        simp only [quasiFreeBalancedCompressionMatrix, Matrix.of_apply, if_neg hij, sub_zero]
        rw [mul_pow, mul_pow, Real.sq_sqrt (hoccupation i),
          Real.sq_sqrt (hoccupation j)]
    _ = quasiFreeSpectralCenteringDefect v energy occupation lower upper +
        quasiFreeSpectralCoherenceDefect v energy occupation := by
      rw [Finset.sum_add_distrib]
      rfl

/-- The invariant trace-polynomial defect is literally the squared Hilbert--Schmidt distance of
the balanced occupation compression. -/
theorem quasiFreeBalancedCompressionHilbertSchmidtSq_eq_compressionDefect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) (lower upper : ℝ) :
    quasiFreeBalancedCompressionHilbertSchmidtSq
        v energy occupation lower upper =
      quasiFreeSpectralCompressionDefect v energy occupation lower upper := by
  rw [quasiFreeBalancedCompressionHilbertSchmidtSq_eq_centering_add_coherence
      v energy occupation hoccupation lower upper,
    ← quasiFreeSpectralCompressionDefect_eq_centering_add_coherence]

/-- The invariant compression defect is nonnegative for nonnegative occupations. -/
theorem quasiFreeSpectralCompressionDefect_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) (lower upper : ℝ) :
    0 ≤ quasiFreeSpectralCompressionDefect v energy occupation lower upper := by
  rw [quasiFreeSpectralCompressionDefect_eq_centering_add_coherence]
  exact add_nonneg
    (quasiFreeSpectralCenteringDefect_nonneg v energy occupation lower upper)
    (quasiFreeSpectralCoherenceDefect_nonneg v energy occupation hoccupation)

/-- **Quasi-free filling--bandwidth three-defect identity.**  The Fano margin is exactly a
rank--filling spectral floor plus endpoint leakage, occupation--energy centering, and weighted
coherence. -/
theorem quasiFreeSpectralFanoMargin_three_defect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (lower upper : ℝ) :
    quasiFreeSpectralFanoMargin v energy occupation =
      lower * upper * (∑ i, occupation i) -
          (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4 +
        quasiFreeSpectralSecantDefect v energy occupation lower upper +
        quasiFreeSpectralCenteringDefect v energy occupation lower upper +
        quasiFreeSpectralCoherenceDefect v energy occupation := by
  have hmargin :
      quasiFreeSpectralFanoMargin v energy occupation =
        (∑ i, (occupation i * orbitalSpectralMean v energy i -
          occupation i * orbitalSpectralSecondMoment v energy i +
          occupation i ^ 2 * orbitalSpectralMean v energy i ^ 2)) +
          quasiFreeSpectralCoherenceDefect v energy occupation := by
    unfold quasiFreeSpectralFanoMargin quasiFreeSpectralMean quasiFreeSpectralVariance
    rw [quasiFreeCompressedSpectralEnergy_eq_diagonal_add_coherence]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hmargin]
  unfold quasiFreeSpectralSecantDefect quasiFreeSpectralCenteringDefect
  apply congrArg (fun x => x + quasiFreeSpectralCoherenceDefect v energy occupation)
  calc
    (∑ i, (occupation i * orbitalSpectralMean v energy i -
        occupation i * orbitalSpectralSecondMoment v energy i +
        occupation i ^ 2 * orbitalSpectralMean v energy i ^ 2)) =
      ∑ i, ((lower * upper * occupation i - (lower + upper - 1) ^ 2 / 4) +
        occupation i * ((lower + upper) * orbitalSpectralMean v energy i -
          lower * upper - orbitalSpectralSecondMoment v energy i) +
        (occupation i * orbitalSpectralMean v energy i -
          (lower + upper - 1) / 2) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring

    _ = lower * upper * (∑ i, occupation i) -
          (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4 +
        (∑ i, occupation i * ((lower + upper) * orbitalSpectralMean v energy i -
          lower * upper - orbitalSpectralSecondMoment v energy i)) +
        ∑ i, (occupation i * orbitalSpectralMean v energy i -
          (lower + upper - 1) / 2) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.mul_sum]
      ring

/-- **Basis-free two-defect master law.**  The quasi-free Fano margin is its rank--filling floor
plus spectral endpoint leakage and the invariant Hilbert--Schmidt compression defect. -/
theorem quasiFreeSpectralFanoMargin_two_defect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (lower upper : ℝ) :
    quasiFreeSpectralFanoMargin v energy occupation =
      lower * upper * (∑ i, occupation i) -
          (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4 +
        quasiFreeSpectralSecantDefect v energy occupation lower upper +
        quasiFreeSpectralCompressionDefect v energy occupation lower upper := by
  rw [quasiFreeSpectralFanoMargin_three_defect v energy occupation lower upper,
    quasiFreeSpectralCompressionDefect_eq_centering_add_coherence]
  ring

/-- **Hilbert--Schmidt two-defect master law.**  For nonnegative occupations, the second defect
in the quasi-free Fano identity is the literal squared Hilbert--Schmidt distance of the balanced
occupation compression. -/
theorem quasiFreeSpectralFanoMargin_hilbertSchmidt_two_defect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) (lower upper : ℝ) :
    quasiFreeSpectralFanoMargin v energy occupation =
      lower * upper * (∑ i, occupation i) -
          (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4 +
        quasiFreeSpectralSecantDefect v energy occupation lower upper +
        quasiFreeBalancedCompressionHilbertSchmidtSq
          v energy occupation lower upper := by
  rw [quasiFreeSpectralFanoMargin_two_defect v energy occupation lower upper,
    quasiFreeBalancedCompressionHilbertSchmidtSq_eq_compressionDefect
      v energy occupation hoccupation lower upper]

/-- **Quasi-free filling--bandwidth Fano law.**  The universal floor depends only on the spectral
endpoints, total occupation, and support rank. -/
theorem quasiFreeSpectralFanoMargin_lower_bound
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    lower * upper * (∑ i, occupation i) -
        (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4 ≤
      quasiFreeSpectralFanoMargin v energy occupation := by
  rw [quasiFreeSpectralFanoMargin_three_defect v energy occupation lower upper]
  have hedge := quasiFreeSpectralSecantDefect_nonneg
    v energy occupation hframe hoccupation lower upper hlower hupper
  have hcenter := quasiFreeSpectralCenteringDefect_nonneg
    v energy occupation lower upper
  have hcoherence := quasiFreeSpectralCoherenceDefect_nonneg
    v energy occupation hoccupation
  linarith

/-- **Noise-certified support-rank law.**  The first two cumulants impose a lower-bound inequality
on the support rank of any compatible nonnegative quasi-free occupation profile. -/
theorem quasiFreeSpectral_rank_witness
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    4 * (lower * upper * (∑ i, occupation i) -
        quasiFreeSpectralFanoMargin v energy occupation) ≤
      (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 := by
  have hlowerBound := quasiFreeSpectralFanoMargin_lower_bound
    v energy occupation hframe hoccupation lower upper hlower hupper
  nlinarith

/-- Near-saturation of the universal floor forces the occupation-compressed observable close to
the balancing scalar in the invariant Hilbert--Schmidt compression defect. -/
theorem quasiFreeSpectralCompressionDefect_le_fano_excess
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    quasiFreeSpectralCompressionDefect v energy occupation lower upper ≤
      quasiFreeSpectralFanoMargin v energy occupation -
        (lower * upper * (∑ i, occupation i) -
          (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4) := by
  have hedge := quasiFreeSpectralSecantDefect_nonneg
    v energy occupation hframe hoccupation lower upper hlower hupper
  rw [quasiFreeSpectralFanoMargin_two_defect v energy occupation lower upper]
  linarith

/-- Near-saturation also bounds the occupation-weighted leakage away from the two spectral
endpoints. -/
theorem quasiFreeSpectralSecantDefect_le_fano_excess
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hoccupation : ∀ i, 0 ≤ occupation i) (lower upper : ℝ) :
    quasiFreeSpectralSecantDefect v energy occupation lower upper ≤
      quasiFreeSpectralFanoMargin v energy occupation -
        (lower * upper * (∑ i, occupation i) -
          (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4) := by
  have hcompression := quasiFreeSpectralCompressionDefect_nonneg
    v energy occupation hoccupation lower upper
  rw [quasiFreeSpectralFanoMargin_two_defect v energy occupation lower upper]
  linarith

/-- The exact rank--filling threshold forces a nonnegative quasi-free Fano margin. -/
theorem quasiFreeSpectralFanoMargin_nonnegative_of_filling
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper)
    (hthreshold :
      (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 ≤
        4 * (lower * upper) * ∑ i, occupation i) :
    0 ≤ quasiFreeSpectralFanoMargin v energy occupation := by
  have hlowerBound := quasiFreeSpectralFanoMargin_lower_bound
    v energy occupation hframe hoccupation lower upper hlower hupper
  have hfloor : 0 ≤ lower * upper * (∑ i, occupation i) -
      (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4 := by
    nlinarith
  exact le_trans hfloor hlowerBound

/-- A negative quasi-free Fano margin necessarily lies below the exact rank--filling threshold. -/
theorem quasiFreeSpectralFanoMargin_negative_forces_filling_failure
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper)
    (hnegative : quasiFreeSpectralFanoMargin v energy occupation < 0) :
    4 * (lower * upper) * (∑ i, occupation i) <
      (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 := by
  by_contra hnot
  have hthreshold :
      (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 ≤
        4 * (lower * upper) * ∑ i, occupation i := le_of_not_gt hnot
  have hnonnegative := quasiFreeSpectralFanoMargin_nonnegative_of_filling
    v energy occupation hframe hoccupation lower upper hlower hupper hthreshold
  linarith

/-- Equality in the universal floor is equivalent to simultaneous vanishing of the intrinsic
endpoint and Hilbert--Schmidt compression defects. -/
theorem quasiFreeSpectralFanoMargin_eq_lower_bound_iff
    (v : ι → κ → ℝ) (energy : κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    quasiFreeSpectralFanoMargin v energy occupation =
        lower * upper * (∑ i, occupation i) -
          (Fintype.card ι : ℝ) * (lower + upper - 1) ^ 2 / 4 ↔
      quasiFreeSpectralSecantDefect v energy occupation lower upper = 0 ∧
        quasiFreeSpectralCompressionDefect v energy occupation lower upper = 0 := by
  have hedge := quasiFreeSpectralSecantDefect_nonneg
    v energy occupation hframe hoccupation lower upper hlower hupper
  have hcompression := quasiFreeSpectralCompressionDefect_nonneg
    v energy occupation hoccupation lower upper
  rw [quasiFreeSpectralFanoMargin_two_defect v energy occupation lower upper]
  constructor
  · intro h
    constructor <;> linarith
  · rintro ⟨hedge0, hcompression0⟩
    rw [hedge0, hcompression0]
    ring

/-- For positive integral degrees at most `maxDegree`, mean filling at least
`maxDegree / 4` guarantees a nonnegative quasi-free Fano margin. -/
theorem positiveBoundedDegree_quasiFreeSpectralFanoMargin_nonnegative
    (v : ι → κ → ℝ) (degree : κ → ℕ) (occupation : ι → ℝ)
    (maxDegree : ℕ)
    (hframe : IsOrthonormalCoordinateFrame v) (hoccupation : ∀ i, 0 ≤ occupation i)
    (hpositive : ∀ k, 1 ≤ degree k) (hbounded : ∀ k, degree k ≤ maxDegree)
    (hfilling : (Fintype.card ι : ℝ) * (maxDegree : ℝ) ≤
      4 * ∑ i, occupation i) :
    0 ≤ quasiFreeSpectralFanoMargin v (fun k => (degree k : ℝ)) occupation := by
  apply quasiFreeSpectralFanoMargin_nonnegative_of_filling
    v (fun k => (degree k : ℝ)) occupation hframe hoccupation 1 (maxDegree : ℝ)
  · intro k
    exact_mod_cast hpositive k
  · intro k
    exact_mod_cast hbounded k
  · have hscaled := mul_le_mul_of_nonneg_right hfilling
      (Nat.cast_nonneg maxDegree : (0 : ℝ) ≤ maxDegree)
    nlinarith

/-- In the degenerate one-level band, the quasi-free Fano margin is exactly the sum of squared
occupations and is therefore nonnegative at every filling. -/
theorem quasiFreeSpectralFanoMargin_unit_energy
    (v : ι → κ → ℝ) (occupation : ι → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v) :
    quasiFreeSpectralFanoMargin v (fun _ => 1) occupation =
      ∑ i, occupation i ^ 2 := by
  have hmean (i : ι) : orbitalSpectralMean v (fun _ => 1) i = 1 := by
    simpa [orbitalSpectralMean] using
      orthonormalCoordinateFrame_row_norm v hframe i
  have hsecond (i : ι) : orbitalSpectralSecondMoment v (fun _ => 1) i = 1 := by
    simpa [orbitalSpectralSecondMoment] using
      orthonormalCoordinateFrame_row_norm v hframe i
  have hcompression : quasiFreeCompressedSpectralEnergy v (fun _ => 1) occupation =
      ∑ i, occupation i ^ 2 := by
    unfold quasiFreeCompressedSpectralEnergy
    simp_rw [show ∀ i j, (∑ k, (1 : ℝ) * v i k * v j k) =
        if i = j then 1 else 0 by
      intro i j
      simpa using hframe i j]
    simp [pow_two]
  unfold quasiFreeSpectralFanoMargin quasiFreeSpectralMean quasiFreeSpectralVariance
  rw [hcompression]
  simp_rw [hmean, hsecond]
  ring

omit [DecidableEq ι] in
/-- Full occupation recovers the Slater endpoint-secant defect. -/
theorem quasiFreeSpectralSecantDefect_one
    (v : ι → κ → ℝ) (energy : κ → ℝ) (lower upper : ℝ) :
    quasiFreeSpectralSecantDefect v energy (fun _ => 1) lower upper =
      slaterSpectralSecantDefect v energy lower upper := by
  simp [quasiFreeSpectralSecantDefect, slaterSpectralSecantDefect]

omit [DecidableEq ι] in
/-- Full occupation recovers the Slater spectral-centering defect. -/
theorem quasiFreeSpectralCenteringDefect_one
    (v : ι → κ → ℝ) (energy : κ → ℝ) (lower upper : ℝ) :
    quasiFreeSpectralCenteringDefect v energy (fun _ => 1) lower upper =
      slaterSpectralCenteringDefect v energy lower upper := by
  simp [quasiFreeSpectralCenteringDefect, slaterSpectralCenteringDefect]

/-- Full occupation recovers the Slater occupied-coherence defect. -/
theorem quasiFreeSpectralCoherenceDefect_one
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    quasiFreeSpectralCoherenceDefect v energy (fun _ => 1) =
      slaterSpectralCoherenceDefect v energy := by
  simp [quasiFreeSpectralCoherenceDefect, slaterSpectralCoherenceDefect]

omit [DecidableEq ι] in
/-- Full occupation recovers the existing Slater mean. -/
theorem quasiFreeSpectralMean_one
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    quasiFreeSpectralMean v energy (fun _ => 1) = slaterSpectralMean v energy := by
  simp [quasiFreeSpectralMean, slaterSpectralMean]

omit [DecidableEq ι] in
/-- Full occupation recovers the existing Slater compression energy. -/
theorem quasiFreeCompressedSpectralEnergy_one
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    quasiFreeCompressedSpectralEnergy v energy (fun _ => 1) =
      slaterCompressedSpectralEnergy v energy := by
  simp [quasiFreeCompressedSpectralEnergy, slaterCompressedSpectralEnergy]

omit [DecidableEq ι] in
/-- Full occupation recovers the existing Slater variance. -/
theorem quasiFreeSpectralVariance_one
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    quasiFreeSpectralVariance v energy (fun _ => 1) =
      slaterSpectralVariance v energy := by
  rw [quasiFreeSpectralVariance, slaterSpectralVariance,
    quasiFreeCompressedSpectralEnergy_one]
  simp

omit [DecidableEq ι] in
/-- Full occupation recovers the existing Slater Fano margin literally. -/
theorem quasiFreeSpectralFanoMargin_one
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    quasiFreeSpectralFanoMargin v energy (fun _ => 1) =
      slaterSpectralFanoMargin v energy := by
  rw [quasiFreeSpectralFanoMargin, slaterSpectralFanoMargin,
    quasiFreeSpectralMean_one, quasiFreeSpectralVariance_one]

end

end GaloisForLFunctions.HilbertMetric
