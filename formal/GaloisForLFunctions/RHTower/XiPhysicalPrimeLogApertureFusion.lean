import GaloisForLFunctions.RHTower.CCMRectangularAutocorrelation
import GaloisForLFunctions.RHTower.PhysicalPrimeEndpointMeshCoercivity

/-!
# Physical prime-log aperture fusion

The true-aperture valuation metric is diagonal in the prime label.  The physical endpoint source
is not: all prime rays are fused into one common logarithmic aperture before the norm square.

This file defines that source-level fusion kernel.  It proves that its raw output is a moving
prime-log window, that the continuum log-density has constant window mass and is killed by
aperture centering, and that the bulk cross-prime Gram is the logarithmic triangular tent minus
the rank-one aperture mean.  It also separates the finite quadratic form into its harmless
diagonal and its genuinely off-diagonal cross-prime defect.

No Xi zero, RH assumption, numerical certificate, or conditional interface occurs here.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RHTower

noncomputable section

/-! ## The moving prime-log flux -/

/-- The aperture interval attached to the log-prime location `log p`, before clipping to the
physical aperture `(0,A]`. -/
def xiPhysicalPrimeLogWindowIndicator
    (m k : ℝ) (p : Nat.Primes) (u : ℝ) : ℝ :=
  rectangularIntervalIndicator
    (m - Real.log (p : ℝ)) (k - m) u

/-- The raw coherent prime flux through the moving logarithmic window. -/
def xiPhysicalPrimeLogWindowFlux
    (P : Finset Nat.Primes) (m k u : ℝ) : ℝ :=
  ∑ p ∈ P,
    physicalPrimeEndpointWeight p *
      xiPhysicalPrimeLogWindowIndicator m k p u

/-- A prime interval contains the aperture point `u` exactly when the prime log lies in the
translated physical window `(m-u,k-u]`. -/
theorem xiPhysicalPrimeLogWindowIndicator_eq_if
    (m k : ℝ) (p : Nat.Primes) (u : ℝ) :
    xiPhysicalPrimeLogWindowIndicator m k p u =
      if m - u < Real.log (p : ℝ) ∧
          Real.log (p : ℝ) ≤ k - u then 1 else 0 := by
  by_cases hwindow : m - u < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ k - u
  · have hmem : u ∈ Ioc
        (m - Real.log (p : ℝ))
        ((m - Real.log (p : ℝ)) + (k - m)) := by
      simp only [mem_Ioc]
      constructor <;> linarith [hwindow.1, hwindow.2]
    rw [xiPhysicalPrimeLogWindowIndicator,
      rectangularIntervalIndicator, Set.indicator_of_mem hmem,
      if_pos hwindow]
  · have hnotmem : u ∉ Ioc
        (m - Real.log (p : ℝ))
        ((m - Real.log (p : ℝ)) + (k - m)) := by
      intro hmem
      simp only [mem_Ioc] at hmem
      apply hwindow
      constructor <;> linarith [hmem.1, hmem.2]
    rw [xiPhysicalPrimeLogWindowIndicator,
      rectangularIntervalIndicator, Set.indicator_of_notMem hnotmem,
      if_neg hwindow]

/-- The common-aperture fusion is literally a weighted moving window in the prime-log
coordinate. -/
theorem xiPhysicalPrimeLogWindowFlux_eq_sum_filter
    (P : Finset Nat.Primes) (m k u : ℝ) :
    xiPhysicalPrimeLogWindowFlux P m k u =
      ∑ p ∈ P, if m - u < Real.log (p : ℝ) ∧
          Real.log (p : ℝ) ≤ k - u then
        physicalPrimeEndpointWeight p else 0 := by
  rw [xiPhysicalPrimeLogWindowFlux]
  apply Finset.sum_congr rfl
  intro p hp
  rw [xiPhysicalPrimeLogWindowIndicator_eq_if]
  split_ifs <;> ring

/-- Lebesgue measure is the exact continuum reference for the log-prime source: every translated
window has the same mass `k-m`. -/
def xiPhysicalLogWindowLebesgueMass (m k u : ℝ) : ℝ :=
  volume.real (Ioc (m - u) (k - u))

theorem xiPhysicalLogWindowLebesgueMass_eq
    {m k : ℝ} (hmk : m ≤ k) (u : ℝ) :
    xiPhysicalLogWindowLebesgueMass m k u = k - m := by
  rw [xiPhysicalLogWindowLebesgueMass, Measure.real, Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal]
  · ring
  · linarith

/-! ## Divisor-mode faithfulness -/

/-- Multiplier of an exponential log-source mode under one width-`c` physical moving-window
coboundary. -/
def xiPhysicalLogWindowModeMultiplier (c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((c : ℂ) * z) - 1

/-- The physical log-window multiplier is the sharp rectangular amplitude in the reversed
spectral coordinate, with its removable denominator restored. -/
theorem xiPhysicalLogWindowModeMultiplier_eq_mul_rectangularWindowAmplitude
    (c : ℝ) (z : ℂ) :
    xiPhysicalLogWindowModeMultiplier c z =
      z * rectangularWindowAmplitude c (-z) := by
  by_cases hz : z = 0
  · subst z
    simp [xiPhysicalLogWindowModeMultiplier]
  · rw [xiPhysicalLogWindowModeMultiplier,
      rectangularWindowAmplitude_eq_div (neg_ne_zero.mpr hz)]
    field_simp [hz]
    ring

/-- A positive-width physical window censors no exponential mode in the open left half-plane.
This is the divisor-facing half-plane containing every mode `z = rho - 1` from a nontrivial
zeta zero. -/
theorem xiPhysicalLogWindowModeMultiplier_ne_zero
    {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z.re < 0) :
    xiPhysicalLogWindowModeMultiplier c z ≠ 0 := by
  rw [xiPhysicalLogWindowModeMultiplier_eq_mul_rectangularWindowAmplitude]
  exact mul_ne_zero
    (fun hzero => by rw [hzero] at hz; simp at hz)
    (rectangularWindowAmplitude_ne_zero hc (by simpa using neg_pos.mpr hz))

/-! ## Prime-level bridge to the filtered Xi-shift source -/

/-- Prime weight of the one-unit-shifted filtered von Mangoldt source exposed by the completed
`+2` Xi logarithmic-derivative defect. -/
def xiShiftFilteredPrimeEndpointWeight (p : Nat.Primes) : ℝ :=
  physicalPrimeEndpointWeight p * (1 - 1 / (p : ℝ) ^ 2)

/-- Inverse-cubic correction from the shifted filtered Xi source to the physical endpoint
weight. -/
def xiShiftFilteredPrimeEndpointRemainder (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) / (p : ℝ) ^ 3

/-- The physical endpoint weight is exactly the one-unit-shifted filtered Xi-source weight plus
an inverse-cubic correction. -/
theorem physicalPrimeEndpointWeight_eq_shiftFiltered_add_remainder
    (p : Nat.Primes) :
    physicalPrimeEndpointWeight p =
      xiShiftFilteredPrimeEndpointWeight p +
        xiShiftFilteredPrimeEndpointRemainder p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  rw [physicalPrimeEndpointWeight, xiShiftFilteredPrimeEndpointWeight,
    xiShiftFilteredPrimeEndpointRemainder, physicalPrimeEndpointWeight]
  field_simp [hp0]
  ring

theorem xiShiftFilteredPrimeEndpointRemainder_pos
    (p : Nat.Primes) :
    0 < xiShiftFilteredPrimeEndpointRemainder p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  exact div_pos (Real.log_pos hp1) (by positivity)

/-- Exact symmetric-square correction from the one-unit-shifted filtered Xi source to the
physical ordinary-prime pair weight. -/
def xiShiftFilteredPrimePairWeightCorrection
    (p q : Nat.Primes) : ℝ :=
  2 * (xiShiftFilteredPrimeEndpointWeight p *
      xiShiftFilteredPrimeEndpointRemainder q +
    xiShiftFilteredPrimeEndpointRemainder p *
      xiShiftFilteredPrimeEndpointWeight q +
    xiShiftFilteredPrimeEndpointRemainder p *
      xiShiftFilteredPrimeEndpointRemainder q)

/-- Each physical prime-pair atom is exactly the symmetric-square atom of the shifted filtered
Xi source plus the displayed inverse-cubic correction. -/
theorem physicalPrimeEndpointPairWeight_eq_shiftFiltered_add_correction
    (p q : Nat.Primes) :
    2 * physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q =
      2 * xiShiftFilteredPrimeEndpointWeight p *
          xiShiftFilteredPrimeEndpointWeight q +
        xiShiftFilteredPrimePairWeightCorrection p q := by
  rw [physicalPrimeEndpointWeight_eq_shiftFiltered_add_remainder p,
    physicalPrimeEndpointWeight_eq_shiftFiltered_add_remainder q,
    xiShiftFilteredPrimePairWeightCorrection]
  ring

theorem physicalPrimeEndpointWeight_pos (p : Nat.Primes) :
    0 < physicalPrimeEndpointWeight p := by
  rw [physicalPrimeEndpointWeight]
  exact div_pos (Real.log_pos (by exact_mod_cast p.prop.one_lt))
    (by exact_mod_cast p.prop.pos)

/-! ## The clipped physical overlap kernel -/

/-- Left endpoint of the prime aperture interval after clipping at `0`. -/
def xiPhysicalPrimeLogApertureStart
    (m : ℝ) (p : Nat.Primes) : ℝ :=
  max 0 (m - Real.log (p : ℝ))

/-- Right endpoint of the prime aperture interval after clipping at `A`. -/
def xiPhysicalPrimeLogApertureEnd
    (A k : ℝ) (p : Nat.Primes) : ℝ :=
  min A (k - Real.log (p : ℝ))

/-- Length of the clipped physical aperture interval.  It is zero when the raw interval misses
the physical aperture. -/
def xiPhysicalPrimeLogApertureLength
    (A m k : ℝ) (p : Nat.Primes) : ℝ :=
  max 0 (xiPhysicalPrimeLogApertureEnd A k p -
    xiPhysicalPrimeLogApertureStart m p)

/-- Length of the overlap of two clipped physical prime intervals. -/
def xiPhysicalPrimeLogApertureOverlap
    (A m k : ℝ) (p q : Nat.Primes) : ℝ :=
  max 0 (min (xiPhysicalPrimeLogApertureEnd A k p)
      (xiPhysicalPrimeLogApertureEnd A k q) -
    max (xiPhysicalPrimeLogApertureStart m p)
      (xiPhysicalPrimeLogApertureStart m q))

/-- The centered physical fusion kernel.  The first term is literal cross-prime interval overlap;
the second is the rank-one aperture mean removed before squaring. -/
def xiPhysicalPrimeLogApertureFusionKernel
    (A m k : ℝ) (p q : Nat.Primes) : ℝ :=
  xiPhysicalPrimeLogApertureOverlap A m k p q -
    xiPhysicalPrimeLogApertureLength A m k p *
      xiPhysicalPrimeLogApertureLength A m k q / A

theorem xiPhysicalPrimeLogApertureStart_nonneg
    (m : ℝ) (p : Nat.Primes) :
    0 ≤ xiPhysicalPrimeLogApertureStart m p := by
  exact le_max_left _ _

theorem xiPhysicalPrimeLogApertureEnd_le
    (A k : ℝ) (p : Nat.Primes) :
    xiPhysicalPrimeLogApertureEnd A k p ≤ A := by
  exact min_le_left _ _

theorem xiPhysicalPrimeLogApertureLength_nonneg
    (A m k : ℝ) (p : Nat.Primes) :
    0 ≤ xiPhysicalPrimeLogApertureLength A m k p := by
  exact le_max_left _ _

theorem xiPhysicalPrimeLogApertureLength_le
    {A : ℝ} (hA : 0 ≤ A) (m k : ℝ) (p : Nat.Primes) :
    xiPhysicalPrimeLogApertureLength A m k p ≤ A := by
  rw [xiPhysicalPrimeLogApertureLength]
  apply max_le hA
  have hend := xiPhysicalPrimeLogApertureEnd_le A k p
  have hstart := xiPhysicalPrimeLogApertureStart_nonneg m p
  linarith

theorem xiPhysicalPrimeLogApertureOverlap_symm
    (A m k : ℝ) (p q : Nat.Primes) :
    xiPhysicalPrimeLogApertureOverlap A m k p q =
      xiPhysicalPrimeLogApertureOverlap A m k q p := by
  simp only [xiPhysicalPrimeLogApertureOverlap, min_comm, max_comm]

theorem xiPhysicalPrimeLogApertureOverlap_self
    (A m k : ℝ) (p : Nat.Primes) :
    xiPhysicalPrimeLogApertureOverlap A m k p p =
      xiPhysicalPrimeLogApertureLength A m k p := by
  simp [xiPhysicalPrimeLogApertureOverlap,
    xiPhysicalPrimeLogApertureLength]

theorem xiPhysicalPrimeLogApertureFusionKernel_symm
    (A m k : ℝ) (p q : Nat.Primes) :
    xiPhysicalPrimeLogApertureFusionKernel A m k p q =
      xiPhysicalPrimeLogApertureFusionKernel A m k q p := by
  rw [xiPhysicalPrimeLogApertureFusionKernel,
    xiPhysicalPrimeLogApertureFusionKernel,
    xiPhysicalPrimeLogApertureOverlap_symm]
  ring

theorem xiPhysicalPrimeLogApertureFusionKernel_diagonal
    (A m k : ℝ) (p : Nat.Primes) :
    xiPhysicalPrimeLogApertureFusionKernel A m k p p =
      xiPhysicalPrimeLogApertureLength A m k p -
        xiPhysicalPrimeLogApertureLength A m k p ^ 2 / A := by
  rw [xiPhysicalPrimeLogApertureFusionKernel,
    xiPhysicalPrimeLogApertureOverlap_self]
  ring

theorem xiPhysicalPrimeLogApertureFusionKernel_diagonal_nonneg
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p : Nat.Primes) :
    0 ≤ xiPhysicalPrimeLogApertureFusionKernel A m k p p := by
  rw [xiPhysicalPrimeLogApertureFusionKernel_diagonal]
  let L := xiPhysicalPrimeLogApertureLength A m k p
  have hL0 : 0 ≤ L := xiPhysicalPrimeLogApertureLength_nonneg A m k p
  have hLA : L ≤ A := xiPhysicalPrimeLogApertureLength_le hA.le m k p
  have hfactor : L - L ^ 2 / A = L * (A - L) / A := by
    field_simp [hA.ne']
  rw [hfactor]
  exact div_nonneg (mul_nonneg hL0 (sub_nonneg.mpr hLA)) hA.le

/-! ## Exact bulk logarithmic tent -/

theorem xiPhysicalPrimeLogApertureLength_eq_bulk
    {A m k : ℝ} (p : Nat.Primes)
    (hstart : 0 ≤ m - Real.log (p : ℝ))
    (hend : k - Real.log (p : ℝ) ≤ A)
    (hmk : m ≤ k) :
    xiPhysicalPrimeLogApertureLength A m k p = k - m := by
  rw [xiPhysicalPrimeLogApertureLength,
    xiPhysicalPrimeLogApertureStart,
    xiPhysicalPrimeLogApertureEnd,
    max_eq_right hstart, min_eq_right hend]
  rw [max_eq_right]
  · ring
  · linarith

theorem xiPhysicalPrimeLogApertureOverlap_eq_bulk_tent
    {A m k : ℝ} (p q : Nat.Primes)
    (hstartp : 0 ≤ m - Real.log (p : ℝ))
    (hendp : k - Real.log (p : ℝ) ≤ A)
    (hstartq : 0 ≤ m - Real.log (q : ℝ))
    (hendq : k - Real.log (q : ℝ) ≤ A) :
    xiPhysicalPrimeLogApertureOverlap A m k p q =
      max 0 ((k - m) -
        |Real.log (p : ℝ) - Real.log (q : ℝ)|) := by
  have hsp : xiPhysicalPrimeLogApertureStart m p =
      m - Real.log (p : ℝ) := by
    rw [xiPhysicalPrimeLogApertureStart, max_eq_right hstartp]
  have hep : xiPhysicalPrimeLogApertureEnd A k p =
      k - Real.log (p : ℝ) := by
    rw [xiPhysicalPrimeLogApertureEnd, min_eq_right hendp]
  have hsq : xiPhysicalPrimeLogApertureStart m q =
      m - Real.log (q : ℝ) := by
    rw [xiPhysicalPrimeLogApertureStart, max_eq_right hstartq]
  have heq : xiPhysicalPrimeLogApertureEnd A k q =
      k - Real.log (q : ℝ) := by
    rw [xiPhysicalPrimeLogApertureEnd, min_eq_right hendq]
  rw [xiPhysicalPrimeLogApertureOverlap, hsp, hep, hsq, heq]
  have hp : k - Real.log (p : ℝ) =
      (m - Real.log (p : ℝ)) + (k - m) := by ring
  have hq : k - Real.log (q : ℝ) =
      (m - Real.log (q : ℝ)) + (k - m) := by ring
  rw [hp, hq, min_add_add_right]
  congr 1
  rw [show min (m - Real.log (p : ℝ)) (m - Real.log (q : ℝ)) + (k - m) -
      max (m - Real.log (p : ℝ)) (m - Real.log (q : ℝ)) =
      (k - m) -
        (max (m - Real.log (p : ℝ)) (m - Real.log (q : ℝ)) -
          min (m - Real.log (p : ℝ)) (m - Real.log (q : ℝ))) by ring,
    max_sub_min_eq_abs]
  congr 2
  ring

/-- In the unclipped bulk, distinct primes interact through one logarithmic triangular tent minus
the rank-one aperture mean. -/
theorem xiPhysicalPrimeLogApertureFusionKernel_eq_bulk_tent
    {A m k : ℝ} (p q : Nat.Primes)
    (hstartp : 0 ≤ m - Real.log (p : ℝ))
    (hendp : k - Real.log (p : ℝ) ≤ A)
    (hstartq : 0 ≤ m - Real.log (q : ℝ))
    (hendq : k - Real.log (q : ℝ) ≤ A)
    (hmk : m ≤ k) :
    xiPhysicalPrimeLogApertureFusionKernel A m k p q =
      max 0 ((k - m) -
        |Real.log (p : ℝ) - Real.log (q : ℝ)|) -
      (k - m) ^ 2 / A := by
  rw [xiPhysicalPrimeLogApertureFusionKernel,
    xiPhysicalPrimeLogApertureOverlap_eq_bulk_tent p q
      hstartp hendp hstartq hendq,
    xiPhysicalPrimeLogApertureLength_eq_bulk p hstartp hendp hmk,
    xiPhysicalPrimeLogApertureLength_eq_bulk q hstartq hendq hmk]
  ring

/-! ## The genuinely off-diagonal RH object -/

/-- Finite quadratic form of the coherent physical fusion kernel. -/
def xiPhysicalPrimeLogApertureFusionEnergy
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      xiPhysicalPrimeLogApertureFusionKernel A m k p q

/-- The prime-diagonal contribution to the physical fusion energy. -/
def xiPhysicalPrimeLogApertureDiagonalEnergy
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, physicalPrimeEndpointWeight p ^ 2 *
    xiPhysicalPrimeLogApertureFusionKernel A m k p p

/-- The signed distinct-prime overlap defect.  This is the non-diagonal source object left after
the unconditional diagonal budget is removed. -/
def xiPhysicalPrimeLogApertureCrossDefect
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      xiPhysicalPrimeLogApertureFusionKernel A m k p q

theorem xiPhysicalPrimeLogApertureFusionEnergy_eq_diagonal_add_cross
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k =
      xiPhysicalPrimeLogApertureDiagonalEnergy P A m k +
        xiPhysicalPrimeLogApertureCrossDefect P A m k := by
  rw [xiPhysicalPrimeLogApertureFusionEnergy,
    xiPhysicalPrimeLogApertureDiagonalEnergy,
    xiPhysicalPrimeLogApertureCrossDefect,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hsplit := Finset.sum_erase_add P (fun q =>
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      xiPhysicalPrimeLogApertureFusionKernel A m k p q) hp
  calc
    (∑ q ∈ P, physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
        xiPhysicalPrimeLogApertureFusionKernel A m k p q) =
      (∑ q ∈ P.erase p,
        physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
          xiPhysicalPrimeLogApertureFusionKernel A m k p q) +
        physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight p *
          xiPhysicalPrimeLogApertureFusionKernel A m k p p := hsplit.symm
    _ = physicalPrimeEndpointWeight p ^ 2 *
          xiPhysicalPrimeLogApertureFusionKernel A m k p p +
        ∑ q ∈ P.erase p,
          physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
            xiPhysicalPrimeLogApertureFusionKernel A m k p q := by ring

theorem xiPhysicalPrimeLogApertureDiagonalEnergy_nonneg
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    0 ≤ xiPhysicalPrimeLogApertureDiagonalEnergy P A m k := by
  rw [xiPhysicalPrimeLogApertureDiagonalEnergy]
  exact Finset.sum_nonneg fun p hp =>
    mul_nonneg (sq_nonneg _)
      (xiPhysicalPrimeLogApertureFusionKernel_diagonal_nonneg hA m k p)

/-! ## The renormalized distinct-prime pair excess -/

/-- Literal weighted overlap mass of distinct prime aperture intervals. -/
def xiPhysicalPrimeLogApertureOverlapCrossMass
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      xiPhysicalPrimeLogApertureOverlap A m k p q

/-- Weighted total length of the physical prime aperture intervals. -/
def xiPhysicalPrimeLogApertureWeightedLengthMass
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, physicalPrimeEndpointWeight p *
    xiPhysicalPrimeLogApertureLength A m k p

/-- Self-pair contribution to the square of the weighted length mass. -/
def xiPhysicalPrimeLogApertureLengthDiagonalMass
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, (physicalPrimeEndpointWeight p *
    xiPhysicalPrimeLogApertureLength A m k p) ^ 2

private theorem sum_sq_eq_diagonal_add_offDiagonal
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ P, a i) ^ 2 =
      (∑ i ∈ P, (a i) ^ 2) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, a i * a j := by
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hsplit := Finset.sum_erase_add P (fun j => a i * a j) hi
  calc
    (∑ j ∈ P, a i * a j) =
        (∑ j ∈ P.erase i, a i * a j) + a i * a i := hsplit.symm
    _ = a i ^ 2 + ∑ j ∈ P.erase i, a i * a j := by ring

/-- The signed cross defect is exactly the local distinct-prime overlap mass minus the
continuum mean-field pair mass, with the self-pair mass removed. -/
theorem xiPhysicalPrimeLogApertureCrossDefect_eq_pairExcess
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalPrimeLogApertureCrossDefect P A m k =
      xiPhysicalPrimeLogApertureOverlapCrossMass P A m k -
        (xiPhysicalPrimeLogApertureWeightedLengthMass P A m k ^ 2 -
          xiPhysicalPrimeLogApertureLengthDiagonalMass P A m k) / A := by
  let a : Nat.Primes → ℝ := fun p =>
    physicalPrimeEndpointWeight p *
      xiPhysicalPrimeLogApertureLength A m k p
  have hsq := sum_sq_eq_diagonal_add_offDiagonal P a
  have hoff :
      (∑ p ∈ P, ∑ q ∈ P.erase p, a p * a q) =
        (∑ p ∈ P, a p) ^ 2 - ∑ p ∈ P, (a p) ^ 2 := by
    linarith
  calc
    xiPhysicalPrimeLogApertureCrossDefect P A m k =
        xiPhysicalPrimeLogApertureOverlapCrossMass P A m k -
          (∑ p ∈ P, ∑ q ∈ P.erase p, a p * a q) / A := by
      rw [xiPhysicalPrimeLogApertureCrossDefect,
        xiPhysicalPrimeLogApertureOverlapCrossMass]
      rw [Finset.sum_div]
      simp_rw [Finset.sum_div]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [xiPhysicalPrimeLogApertureFusionKernel, a]
      ring
    _ = xiPhysicalPrimeLogApertureOverlapCrossMass P A m k -
          ((∑ p ∈ P, a p) ^ 2 - ∑ p ∈ P, (a p) ^ 2) / A := by
      rw [hoff]
    _ = xiPhysicalPrimeLogApertureOverlapCrossMass P A m k -
        (xiPhysicalPrimeLogApertureWeightedLengthMass P A m k ^ 2 -
          xiPhysicalPrimeLogApertureLengthDiagonalMass P A m k) / A := by
      rfl

/-! ## Aperture-width curvature tomography -/

private theorem relu_secondDifference_eq_tent
    {x h : ℝ} (hh : 0 ≤ h) :
    max 0 (x + h) + max 0 (x - h) - 2 * max 0 x =
      max 0 (h - |x|) := by
  by_cases hx0 : x ≤ -h
  · have h1 : x + h ≤ 0 := by linarith
    have h2 : x - h ≤ 0 := by linarith
    have h3 : x ≤ 0 := hx0.trans (neg_nonpos.mpr hh)
    have hrhs : h - |x| ≤ 0 := by
      rw [abs_of_nonpos h3]
      linarith
    rw [max_eq_left h1, max_eq_left h2, max_eq_left h3,
      max_eq_left hrhs]
    norm_num
  · have hx0' : -h < x := lt_of_not_ge hx0
    by_cases hx : x ≤ 0
    · have h1 : 0 ≤ x + h := by linarith
      have h2 : x - h ≤ 0 := by linarith
      have hrhs : 0 ≤ h - |x| := by
        rw [abs_of_nonpos hx]
        linarith
      rw [max_eq_right h1, max_eq_left h2, max_eq_left hx,
        max_eq_right hrhs, abs_of_nonpos hx]
      ring
    · have hx' : 0 < x := lt_of_not_ge hx
      by_cases hx1 : x ≤ h
      · have h1 : 0 ≤ x + h := by linarith
        have h2 : x - h ≤ 0 := by linarith
        have h3 : 0 ≤ x := hx'.le
        have hrhs : 0 ≤ h - |x| := by
          rw [abs_of_nonneg h3]
          linarith
        rw [max_eq_right h1, max_eq_left h2, max_eq_right h3,
          max_eq_right hrhs, abs_of_nonneg h3]
        ring
      · have hx1' : h < x := lt_of_not_ge hx1
        have h1 : 0 ≤ x + h := by linarith
        have h2 : 0 ≤ x - h := by linarith
        have h3 : 0 ≤ x := hx'.le
        have hrhs : h - |x| ≤ 0 := by
          rw [abs_of_nonneg h3]
          linarith
        rw [max_eq_right h1, max_eq_right h2, max_eq_right h3,
          max_eq_left hrhs]
        ring

/-- One-sided increment of the ReLU.  The old active sites contribute the full step; sites to
the right contribute only their boundary ramp. -/
private theorem relu_forwardDifference_eq
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    max 0 (x + h) - max 0 x =
      if 0 ≤ x then h else max 0 (x + h) := by
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, max_eq_right hx, max_eq_right (by linarith)]
    ring
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [if_neg hx, max_eq_left hx'.le]
    ring

/-- Logarithmic distance between two prime locations. -/
def xiPhysicalPrimeLogBulkPairDistance (p q : Nat.Primes) : ℝ :=
  |Real.log (p : ℝ) - Real.log (q : ℝ)|

private theorem prime_real_ratio_eq_of_ne
    (p q r s : Nat.Primes) (hpq : p ≠ q)
    (hratio : (p : ℝ) / (q : ℝ) = (r : ℝ) / (s : ℝ)) :
    p = r ∧ q = s := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast s.prop.ne_zero
  have hreal : (p : ℝ) * s = (r : ℝ) * q :=
    (div_eq_div_iff hq0 hs0).mp hratio
  have hnat : (p : ℕ) * s = (r : ℕ) * q := by exact_mod_cast hreal
  have hpdiv : (p : ℕ) ∣ (r : ℕ) * q := ⟨s, hnat.symm⟩
  rcases p.prop.dvd_mul.mp hpdiv with hpr | hpqdiv
  · have hrp : r = p := by
      apply Subtype.ext
      exact (r.prop.dvd_iff_eq p.prop.ne_one).mp hpr
    subst r
    refine ⟨rfl, ?_⟩
    apply Subtype.ext
    exact Nat.eq_of_mul_eq_mul_left p.prop.pos hnat.symm
  · have hqp : q = p := by
      apply Subtype.ext
      exact (q.prop.dvd_iff_eq p.prop.ne_one).mp hpqdiv
    exact (hpq hqp.symm).elim

/-- Arithmetic simplicity of the bulk ratio spectrum: a logarithmic distance from one distinct
prime pair determines that unordered prime pair exactly. -/
theorem xiPhysicalPrimeLogBulkPairDistance_eq_iff
    (p q r s : Nat.Primes) (hpq : p ≠ q) :
    xiPhysicalPrimeLogBulkPairDistance p q =
        xiPhysicalPrimeLogBulkPairDistance r s ↔
      (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  constructor
  · intro hdist
    rw [xiPhysicalPrimeLogBulkPairDistance,
      xiPhysicalPrimeLogBulkPairDistance] at hdist
    rcases abs_eq_abs.mp hdist with hsame | hswap
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
      have hq0 : (0 : ℝ) < q := by exact_mod_cast q.prop.pos
      have hr0 : (0 : ℝ) < r := by exact_mod_cast r.prop.pos
      have hs0 : (0 : ℝ) < s := by exact_mod_cast s.prop.pos
      have hexp := congrArg Real.exp hsame
      have hratio : (p : ℝ) / q = (r : ℝ) / s := by
        simpa [Real.exp_sub, Real.exp_log hp0, Real.exp_log hq0,
          Real.exp_log hr0, Real.exp_log hs0] using hexp
      exact Or.inl (prime_real_ratio_eq_of_ne p q r s hpq hratio)
    · have hsame : Real.log (p : ℝ) - Real.log (q : ℝ) =
          Real.log (s : ℝ) - Real.log (r : ℝ) := by linarith
      have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
      have hq0 : (0 : ℝ) < q := by exact_mod_cast q.prop.pos
      have hr0 : (0 : ℝ) < r := by exact_mod_cast r.prop.pos
      have hs0 : (0 : ℝ) < s := by exact_mod_cast s.prop.pos
      have hexp := congrArg Real.exp hsame
      have hratio : (p : ℝ) / q = (s : ℝ) / r := by
        simpa [Real.exp_sub, Real.exp_log hp0, Real.exp_log hq0,
          Real.exp_log hr0, Real.exp_log hs0] using hexp
      exact Or.inr (prime_real_ratio_eq_of_ne p q s r hpq hratio)
  · rintro (h | h)
    · rw [h.1, h.2]
    · rw [h.1, h.2, xiPhysicalPrimeLogBulkPairDistance,
        xiPhysicalPrimeLogBulkPairDistance, abs_sub_comm]

/-- Centered fusion kernel for two untruncated prime intervals of common width `c`. -/
def xiPhysicalPrimeLogBulkFusionKernel
    (A c : ℝ) (p q : Nat.Primes) : ℝ :=
  max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q) - c ^ 2 / A

/-- The clipped physical kernel agrees with the width-only bulk kernel whenever neither prime
interval meets the aperture boundary. -/
theorem xiPhysicalPrimeLogApertureFusionKernel_eq_bulkKernel
    {A m k : ℝ} (p q : Nat.Primes)
    (hstartp : 0 ≤ m - Real.log (p : ℝ))
    (hendp : k - Real.log (p : ℝ) ≤ A)
    (hstartq : 0 ≤ m - Real.log (q : ℝ))
    (hendq : k - Real.log (q : ℝ) ≤ A)
    (hmk : m ≤ k) :
    xiPhysicalPrimeLogApertureFusionKernel A m k p q =
      xiPhysicalPrimeLogBulkFusionKernel A (k - m) p q := by
  rw [xiPhysicalPrimeLogApertureFusionKernel_eq_bulk_tent p q
    hstartp hendp hstartq hendq hmk]
  rfl

/-- Triangular ratio shell selected by a width second difference. -/
def xiPhysicalPrimeLogPairBandTent
    (c h : ℝ) (p q : Nat.Primes) : ℝ :=
  max 0 (h - |xiPhysicalPrimeLogBulkPairDistance p q - c|)

theorem xiPhysicalPrimeLogPairBandTent_pos_iff
    (c h : ℝ) (p q : Nat.Primes) :
    0 < xiPhysicalPrimeLogPairBandTent c h p q ↔
      |xiPhysicalPrimeLogBulkPairDistance p q - c| < h := by
  simp [xiPhysicalPrimeLogPairBandTent]

/-- Exact width curvature of one centered bulk prime-pair kernel.  Its singular positive part is
the triangular shell around the pair's logarithmic ratio; the continuum term contributes only a
constant negative background. -/
theorem xiPhysicalPrimeLogBulkFusionKernel_width_secondDifference
    (A c : ℝ) {h : ℝ} (hh : 0 ≤ h) (p q : Nat.Primes) :
    xiPhysicalPrimeLogBulkFusionKernel A (c + h) p q +
        xiPhysicalPrimeLogBulkFusionKernel A (c - h) p q -
        2 * xiPhysicalPrimeLogBulkFusionKernel A c p q =
      xiPhysicalPrimeLogPairBandTent c h p q - 2 * h ^ 2 / A := by
  rw [xiPhysicalPrimeLogBulkFusionKernel,
    xiPhysicalPrimeLogBulkFusionKernel,
    xiPhysicalPrimeLogBulkFusionKernel]
  have hre := relu_secondDifference_eq_tent
    (x := c - xiPhysicalPrimeLogBulkPairDistance p q) hh
  rw [show c + h - xiPhysicalPrimeLogBulkPairDistance p q =
      (c - xiPhysicalPrimeLogBulkPairDistance p q) + h by ring,
    show c - h - xiPhysicalPrimeLogBulkPairDistance p q =
      (c - xiPhysicalPrimeLogBulkPairDistance p q) - h by ring]
  calc
    max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q + h) - (c + h) ^ 2 / A +
          (max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q - h) -
            (c - h) ^ 2 / A) -
          2 * (max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q) - c ^ 2 / A) =
        (max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q + h) +
          max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q - h) -
          2 * max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q)) -
          2 * h ^ 2 / A := by ring
    _ = xiPhysicalPrimeLogPairBandTent c h p q - 2 * h ^ 2 / A := by
      rw [hre, xiPhysicalPrimeLogPairBandTent, abs_sub_comm]

/-- Exact one-sided width increment of one bulk pair kernel.  Previously active ratio sites
contribute `h`; a site to the right contributes its truncated boundary ramp. -/
theorem xiPhysicalPrimeLogBulkFusionKernel_width_forwardDifference
    (A c : ℝ) {h : ℝ} (hh : 0 ≤ h) (p q : Nat.Primes) :
    xiPhysicalPrimeLogBulkFusionKernel A (c + h) p q -
        xiPhysicalPrimeLogBulkFusionKernel A c p q =
      h * (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0) +
        (if c < xiPhysicalPrimeLogBulkPairDistance p q then
          max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q)
        else 0) -
        (2 * c * h + h ^ 2) / A := by
  rw [xiPhysicalPrimeLogBulkFusionKernel,
    xiPhysicalPrimeLogBulkFusionKernel]
  have hre := relu_forwardDifference_eq
    (x := c - xiPhysicalPrimeLogBulkPairDistance p q) hh
  calc
    max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q) - (c + h) ^ 2 / A -
          (max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q) - c ^ 2 / A) =
        (max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q + h) -
          max 0 (c - xiPhysicalPrimeLogBulkPairDistance p q)) -
          (2 * c * h + h ^ 2) / A := by
      rw [show c + h - xiPhysicalPrimeLogBulkPairDistance p q =
        c - xiPhysicalPrimeLogBulkPairDistance p q + h by ring]
      ring
    _ = h * (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0) +
          (if c < xiPhysicalPrimeLogBulkPairDistance p q then
            max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q)
          else 0) -
          (2 * c * h + h ^ 2) / A := by
      rw [hre]
      rw [show c + h - xiPhysicalPrimeLogBulkPairDistance p q =
        c - xiPhysicalPrimeLogBulkPairDistance p q + h by ring]
      by_cases hd : xiPhysicalPrimeLogBulkPairDistance p q ≤ c
      · have hx : 0 ≤ c - xiPhysicalPrimeLogBulkPairDistance p q := sub_nonneg.mpr hd
        rw [if_pos hx, if_pos hd, if_neg (not_lt_of_ge hd)]
        ring
      · have hdc : c < xiPhysicalPrimeLogBulkPairDistance p q := lt_of_not_ge hd
        have hx : ¬ 0 ≤ c - xiPhysicalPrimeLogBulkPairDistance p q := by linarith
        rw [if_neg hx, if_neg hd, if_pos hdc]
        ring

private theorem sum_secondDifference
    {ι : Type*} (P : Finset ι) (f g r : ι → ℝ) :
    (∑ i ∈ P, f i) + (∑ i ∈ P, g i) - 2 * (∑ i ∈ P, r i) =
      ∑ i ∈ P, (f i + g i - 2 * r i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]

private theorem sum_forwardDifference
    {ι : Type*} (P : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ P, f i) - (∑ i ∈ P, g i) =
      ∑ i ∈ P, (f i - g i) := by
  rw [Finset.sum_sub_distrib]

private theorem sum_affine
    {ι : Type*} (P : Finset ι) (a b : ℝ) (u v w : ι → ℝ) :
    (∑ i ∈ P, (a * u i + v i - b * w i)) =
      a * (∑ i ∈ P, u i) + (∑ i ∈ P, v i) -
        b * (∑ i ∈ P, w i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]

/-- Off-diagonal bulk fusion defect as a function of the physical log-window width. -/
def xiPhysicalPrimeLogBulkCrossDefect
    (P : Finset Nat.Primes) (A c : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      xiPhysicalPrimeLogBulkFusionKernel A c p q

/-- Positive triangular mass of prime ratios in the width shell centered at `c`. -/
def xiPhysicalPrimeLogPairBandCurvatureMass
    (P : Finset Nat.Primes) (c h : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      xiPhysicalPrimeLogPairBandTent c h p q

/-- Total ordered distinct-prime pair weight. -/
def xiPhysicalPrimeLogCrossWeightMass (P : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q

/-- Ordered weighted mass of distinct-prime ratio sites at logarithmic distance at most `c`. -/
def xiPhysicalPrimeLogPairCumulativeMass
    (P : Finset Nat.Primes) (c : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0

/-- Cumulative prime-ratio mass after subtracting the linear continuum background forced by
aperture centering. -/
def xiPhysicalPrimeLogPairCumulativeDiscrepancy
    (P : Finset Nat.Primes) (A c : ℝ) : ℝ :=
  xiPhysicalPrimeLogPairCumulativeMass P c -
    2 * c / A * xiPhysicalPrimeLogCrossWeightMass P

/-- Boundary ramp from ratio sites which enter during the forward width step from `c` to
`c + h`. -/
def xiPhysicalPrimeLogPairForwardBoundaryRampMass
    (P : Finset Nat.Primes) (c h : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      if c < xiPhysicalPrimeLogBulkPairDistance p q then
        max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q)
      else 0

/-- Weighted atom of the off-diagonal prime-ratio measure at logarithmic distance `c`. -/
def xiPhysicalPrimeLogPairDistanceFiberMass
    (P : Finset Nat.Primes) (c : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p,
    if xiPhysicalPrimeLogBulkPairDistance p q = c then
      physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q else 0

private theorem pairDistanceFiberInnerSum_eq
    (P : Finset Nat.Primes) (p q r : Nat.Primes)
    (hpq : p ≠ q) (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P) :
    (∑ s ∈ P.erase r,
      if xiPhysicalPrimeLogBulkPairDistance r s =
          xiPhysicalPrimeLogBulkPairDistance p q then
        physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight s else 0) =
      if r = p then
        physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight q
      else if r = q then
        physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight p
      else 0 := by
  by_cases hrp : r = p
  · subst r
    rw [if_pos rfl]
    calc
      (∑ s ∈ P.erase p,
        if xiPhysicalPrimeLogBulkPairDistance p s =
            xiPhysicalPrimeLogBulkPairDistance p q then
          physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight s else 0) =
          (if xiPhysicalPrimeLogBulkPairDistance p q =
              xiPhysicalPrimeLogBulkPairDistance p q then
            physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q else 0) := by
        apply Finset.sum_eq_single q
        · intro s hs hsq
          rw [if_neg]
          intro hdist
          have hps : p ≠ s := (Finset.mem_erase.mp hs).1.symm
          rcases (xiPhysicalPrimeLogBulkPairDistance_eq_iff p s p q hps).mp hdist with h | h
          · exact hsq h.2
          · exact hpq h.1
        · intro hqnot
          exact (hqnot (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩)).elim
      _ = physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q := by simp
  · rw [if_neg hrp]
    by_cases hrq : r = q
    · subst r
      rw [if_pos rfl]
      have hdqp : xiPhysicalPrimeLogBulkPairDistance q p =
          xiPhysicalPrimeLogBulkPairDistance p q := by
        rw [xiPhysicalPrimeLogBulkPairDistance,
          xiPhysicalPrimeLogBulkPairDistance, abs_sub_comm]
      calc
        (∑ s ∈ P.erase q,
          if xiPhysicalPrimeLogBulkPairDistance q s =
              xiPhysicalPrimeLogBulkPairDistance p q then
            physicalPrimeEndpointWeight q * physicalPrimeEndpointWeight s else 0) =
            (if xiPhysicalPrimeLogBulkPairDistance q p =
                xiPhysicalPrimeLogBulkPairDistance p q then
              physicalPrimeEndpointWeight q * physicalPrimeEndpointWeight p else 0) := by
          apply Finset.sum_eq_single p
          · intro s hs hsp
            rw [if_neg]
            intro hdist
            have hqs : q ≠ s := (Finset.mem_erase.mp hs).1.symm
            rcases (xiPhysicalPrimeLogBulkPairDistance_eq_iff q s p q hqs).mp hdist with h | h
            · exact hpq h.1.symm
            · exact hsp h.2
          · intro hpnot
            exact (hpnot (Finset.mem_erase.mpr ⟨hpq, hp⟩)).elim
        _ = physicalPrimeEndpointWeight q * physicalPrimeEndpointWeight p := by
          rw [if_pos hdqp]
    · rw [if_neg hrq]
      apply Finset.sum_eq_zero
      intro s hs
      rw [if_neg]
      intro hdist
      have hrs : r ≠ s := (Finset.mem_erase.mp hs).1.symm
      rcases (xiPhysicalPrimeLogBulkPairDistance_eq_iff r s p q hrs).mp hdist with h | h
      · exact hrp h.1
      · exact hrq h.1

/-- Each positive logarithmic prime-ratio atom has exactly the two ordered orientations.  Its
weight is therefore twice the product of the two physical endpoint weights. -/
theorem xiPhysicalPrimeLogPairDistanceFiberMass_at_pair
    (P : Finset Nat.Primes) (p q : Nat.Primes)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    xiPhysicalPrimeLogPairDistanceFiberMass P
        (xiPhysicalPrimeLogBulkPairDistance p q) =
      2 * physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q := by
  rw [xiPhysicalPrimeLogPairDistanceFiberMass]
  have hrewrite :
      (∑ r ∈ P, ∑ s ∈ P.erase r,
        if xiPhysicalPrimeLogBulkPairDistance r s =
            xiPhysicalPrimeLogBulkPairDistance p q then
          physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight s else 0) =
        ∑ r ∈ P,
          if r = p then
            physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight q
          else if r = q then
            physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight p
          else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    exact pairDistanceFiberInnerSum_eq P p q r hpq hp hq hr
  rw [hrewrite]
  have hsplitp := Finset.sum_erase_add P (fun r =>
    if r = p then physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight q
    else if r = q then physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight p
    else 0) hp
  rw [← hsplitp]
  have hqErase : q ∈ P.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  have hsplitq := Finset.sum_erase_add (P.erase p) (fun r =>
    if r = p then physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight q
    else if r = q then physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight p
    else 0) hqErase
  rw [← hsplitq]
  have hzero :
      (∑ r ∈ (P.erase p).erase q,
        if r = p then physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight q
        else if r = q then physicalPrimeEndpointWeight r * physicalPrimeEndpointWeight p
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
    have hrp : r ≠ p :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    rw [if_neg hrp, if_neg hrq]
  rw [hzero]
  simp [hpq.symm]
  ring

private theorem exists_pos_le_abs_sub_on_finset
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) (c : ℝ) :
    ∃ h : ℝ, 0 < h ∧ ∀ i ∈ S, f i ≠ c → h ≤ |f i - c| := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨1, one_pos, by simp⟩
  | @insert a S ha ih =>
      obtain ⟨h, hh, hsep⟩ := ih
      by_cases hac : f a = c
      · refine ⟨h, hh, ?_⟩
        intro i hi hne
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact (hne hac).elim
        · exact hsep i hi hne
      · have hgap : 0 < |f a - c| :=
          abs_pos.mpr (sub_ne_zero.mpr hac)
        refine ⟨min h |f a - c|, lt_min hh hgap, ?_⟩
        intro i hi hne
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hsep i hi hne)

private def xiPhysicalPrimeLogOffDiagonalPairs
    (P : Finset Nat.Primes) : Finset (Nat.Primes × Nat.Primes) :=
  (P ×ˢ P).filter fun z => z.1 ≠ z.2

/-- Once a triangular ratio shell is narrower than every nonzero distance from `c`, its mass is
exactly its width times the atom mass at `c`. -/
theorem xiPhysicalPrimeLogPairBandCurvatureMass_eq_mul_fiberMass_of_isolated
    (P : Finset Nat.Primes) (c : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hsep : ∀ p ∈ P, ∀ q ∈ P.erase p,
      xiPhysicalPrimeLogBulkPairDistance p q ≠ c →
        h ≤ |xiPhysicalPrimeLogBulkPairDistance p q - c|) :
    xiPhysicalPrimeLogPairBandCurvatureMass P c h =
      h * xiPhysicalPrimeLogPairDistanceFiberMass P c := by
  rw [xiPhysicalPrimeLogPairBandCurvatureMass,
    xiPhysicalPrimeLogPairDistanceFiberMass, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hd : xiPhysicalPrimeLogBulkPairDistance p q = c
  · rw [if_pos hd, xiPhysicalPrimeLogPairBandTent, hd, sub_self, abs_zero]
    rw [sub_zero, max_eq_right hh]
    ring
  · rw [if_neg hd, mul_zero, xiPhysicalPrimeLogPairBandTent]
    rw [max_eq_left]
    · ring
    · linarith [hsep p hp q hq hd]

/-- Every finite prime packet has a positive shell scale at which width curvature recovers exactly
the weighted prime-ratio atom at `c`. -/
theorem exists_xiPhysicalPrimeLogPairBandCurvatureMass_eq_mul_fiberMass
    (P : Finset Nat.Primes) (c : ℝ) :
    ∃ h : ℝ, 0 < h ∧
      xiPhysicalPrimeLogPairBandCurvatureMass P c h =
        h * xiPhysicalPrimeLogPairDistanceFiberMass P c := by
  classical
  obtain ⟨h, hh, hsep⟩ := exists_pos_le_abs_sub_on_finset
    (xiPhysicalPrimeLogOffDiagonalPairs P)
    (fun z => xiPhysicalPrimeLogBulkPairDistance z.1 z.2) c
  refine ⟨h, hh,
    xiPhysicalPrimeLogPairBandCurvatureMass_eq_mul_fiberMass_of_isolated
      P c hh.le ?_⟩
  intro p hp q hq hne
  apply hsep (p, q)
  · rw [xiPhysicalPrimeLogOffDiagonalPairs]
    simp only [Finset.mem_filter, Finset.mem_product, ne_eq]
    have hqe := Finset.mem_erase.mp hq
    exact ⟨⟨hp, hqe.2⟩, hqe.1.symm⟩
  · exact hne

/-- Exact aperture-width tomography: the second width difference of the bulk cross defect is the
positive prime-ratio shell mass minus the explicit uniform continuum background. -/
theorem xiPhysicalPrimeLogBulkCrossDefect_width_secondDifference
    (P : Finset Nat.Primes) (A c : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    xiPhysicalPrimeLogBulkCrossDefect P A (c + h) +
        xiPhysicalPrimeLogBulkCrossDefect P A (c - h) -
        2 * xiPhysicalPrimeLogBulkCrossDefect P A c =
      xiPhysicalPrimeLogPairBandCurvatureMass P c h -
        2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P := by
  calc
    xiPhysicalPrimeLogBulkCrossDefect P A (c + h) +
          xiPhysicalPrimeLogBulkCrossDefect P A (c - h) -
          2 * xiPhysicalPrimeLogBulkCrossDefect P A c =
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
            (xiPhysicalPrimeLogBulkFusionKernel A (c + h) p q +
              xiPhysicalPrimeLogBulkFusionKernel A (c - h) p q -
              2 * xiPhysicalPrimeLogBulkFusionKernel A c p q) := by
      rw [xiPhysicalPrimeLogBulkCrossDefect,
        xiPhysicalPrimeLogBulkCrossDefect,
        xiPhysicalPrimeLogBulkCrossDefect,
        sum_secondDifference]
      apply Finset.sum_congr rfl
      intro p hp
      rw [sum_secondDifference]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ p ∈ P, ∑ q ∈ P.erase p,
          physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
            (xiPhysicalPrimeLogPairBandTent c h p q - 2 * h ^ 2 / A) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [xiPhysicalPrimeLogBulkFusionKernel_width_secondDifference A c hh p q]
    _ = xiPhysicalPrimeLogPairBandCurvatureMass P c h -
          2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P := by
      rw [xiPhysicalPrimeLogPairBandCurvatureMass,
        xiPhysicalPrimeLogCrossWeightMass]
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Exact Green--discrepancy law for a forward aperture-width step.  The first difference of the
bulk cross defect is the cumulative signed ratio discrepancy plus only the nonnegative boundary
ramp from sites entering during this step. -/
theorem xiPhysicalPrimeLogBulkCrossDefect_width_forwardDifference
    (P : Finset Nat.Primes) (A c : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    xiPhysicalPrimeLogBulkCrossDefect P A (c + h) -
        xiPhysicalPrimeLogBulkCrossDefect P A c =
      h * xiPhysicalPrimeLogPairCumulativeDiscrepancy P A c +
        xiPhysicalPrimeLogPairForwardBoundaryRampMass P c h -
        h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P := by
  calc
    xiPhysicalPrimeLogBulkCrossDefect P A (c + h) -
          xiPhysicalPrimeLogBulkCrossDefect P A c =
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
            (xiPhysicalPrimeLogBulkFusionKernel A (c + h) p q -
              xiPhysicalPrimeLogBulkFusionKernel A c p q) := by
      rw [xiPhysicalPrimeLogBulkCrossDefect,
        xiPhysicalPrimeLogBulkCrossDefect,
        sum_forwardDifference]
      apply Finset.sum_congr rfl
      intro p hp
      rw [sum_forwardDifference]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ p ∈ P, ∑ q ∈ P.erase p,
          physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
            (h * (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0) +
              (if c < xiPhysicalPrimeLogBulkPairDistance p q then
                max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q)
              else 0) -
              (2 * c * h + h ^ 2) / A) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [xiPhysicalPrimeLogBulkFusionKernel_width_forwardDifference A c hh p q]
    _ = h * xiPhysicalPrimeLogPairCumulativeMass P c +
          xiPhysicalPrimeLogPairForwardBoundaryRampMass P c h -
          (2 * c * h + h ^ 2) / A *
            xiPhysicalPrimeLogCrossWeightMass P := by
      rw [xiPhysicalPrimeLogPairCumulativeMass,
        xiPhysicalPrimeLogPairForwardBoundaryRampMass,
        xiPhysicalPrimeLogCrossWeightMass]
      calc
        (∑ p ∈ P, ∑ q ∈ P.erase p,
          physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
            (h * (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0) +
              (if c < xiPhysicalPrimeLogBulkPairDistance p q then
                max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q)
              else 0) -
              (2 * c * h + h ^ 2) / A)) =
            ∑ p ∈ P, ∑ q ∈ P.erase p,
              (h * (physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
                  (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0)) +
                physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
                  (if c < xiPhysicalPrimeLogBulkPairDistance p q then
                    max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q)
                  else 0) -
                (2 * c * h + h ^ 2) / A *
                  (physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q)) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = ∑ p ∈ P,
              (h * (∑ q ∈ P.erase p,
                  physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
                    (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0)) +
                (∑ q ∈ P.erase p,
                  physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
                    (if c < xiPhysicalPrimeLogBulkPairDistance p q then
                      max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q)
                    else 0)) -
                (2 * c * h + h ^ 2) / A *
                  (∑ q ∈ P.erase p,
                    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact sum_affine (P.erase p) h ((2 * c * h + h ^ 2) / A)
            (fun q => physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
              (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0))
            (fun q => physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
              (if c < xiPhysicalPrimeLogBulkPairDistance p q then
                max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q) else 0))
            (fun q => physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q)
        _ = h * (∑ p ∈ P, ∑ q ∈ P.erase p,
                physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
                  (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0)) +
              (∑ p ∈ P, ∑ q ∈ P.erase p,
                physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
                  (if c < xiPhysicalPrimeLogBulkPairDistance p q then
                    max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q) else 0)) -
              (2 * c * h + h ^ 2) / A *
                (∑ p ∈ P, ∑ q ∈ P.erase p,
                  physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q) := by
          exact sum_affine P h ((2 * c * h + h ^ 2) / A)
            (fun p => ∑ q ∈ P.erase p,
              physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
                (if xiPhysicalPrimeLogBulkPairDistance p q ≤ c then 1 else 0))
            (fun p => ∑ q ∈ P.erase p,
              physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
                (if c < xiPhysicalPrimeLogBulkPairDistance p q then
                  max 0 (c + h - xiPhysicalPrimeLogBulkPairDistance p q) else 0))
            (fun p => ∑ q ∈ P.erase p,
              physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q)
    _ = h * xiPhysicalPrimeLogPairCumulativeDiscrepancy P A c +
          xiPhysicalPrimeLogPairForwardBoundaryRampMass P c h -
          h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P := by
      rw [xiPhysicalPrimeLogPairCumulativeDiscrepancy]
      ring

/-- Every finite ratio spectrum has a positive right neighborhood at `c` containing no new ratio
site.  Hence its forward boundary ramp vanishes simultaneously at every smaller nonnegative
step. -/
theorem exists_pos_forall_xiPhysicalPrimeLogPairForwardBoundaryRampMass_eq_zero
    (P : Finset Nat.Primes) (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 ≤ h → h ≤ ε →
      xiPhysicalPrimeLogPairForwardBoundaryRampMass P c h = 0 := by
  classical
  obtain ⟨ε, hε, hsep⟩ := exists_pos_le_abs_sub_on_finset
    (xiPhysicalPrimeLogOffDiagonalPairs P)
    (fun z => xiPhysicalPrimeLogBulkPairDistance z.1 z.2) c
  refine ⟨ε, hε, ?_⟩
  intro h hh hle
  rw [xiPhysicalPrimeLogPairForwardBoundaryRampMass]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hright : c < xiPhysicalPrimeLogBulkPairDistance p q
  · have hmem : (p, q) ∈ xiPhysicalPrimeLogOffDiagonalPairs P := by
      rw [xiPhysicalPrimeLogOffDiagonalPairs]
      simp only [Finset.mem_filter, Finset.mem_product, ne_eq]
      have hqe := Finset.mem_erase.mp hq
      exact ⟨⟨hp, hqe.2⟩, hqe.1.symm⟩
    have hgap := hsep (p, q) hmem (ne_of_gt hright)
    rw [abs_of_pos (sub_pos.mpr hright)] at hgap
    rw [if_pos hright, max_eq_left]
    · ring
    · linarith
  · rw [if_neg hright]
    ring

/-- On a ratio-free right neighborhood, the first width difference recovers exactly the signed
cumulative prime-ratio discrepancy.  This is the finite, limit-free right-germ form of the
Green--discrepancy law. -/
theorem exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_forward_recovers_cumulativeDiscrepancy
    (P : Finset Nat.Primes) (A c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h ≤ ε →
      xiPhysicalPrimeLogBulkCrossDefect P A (c + h) -
          xiPhysicalPrimeLogBulkCrossDefect P A c +
          h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P =
        h * xiPhysicalPrimeLogPairCumulativeDiscrepancy P A c := by
  obtain ⟨ε, hε, hramp⟩ :=
    exists_pos_forall_xiPhysicalPrimeLogPairForwardBoundaryRampMass_eq_zero P c
  refine ⟨ε, hε, ?_⟩
  intro h hh hle
  rw [xiPhysicalPrimeLogBulkCrossDefect_width_forwardDifference P A c hh.le,
    hramp h hh.le hle]
  ring

/-- Finite prime-ratio atom recovery from the physical aperture metric.  At a sufficiently narrow
positive width step, the compensated curvature is exactly the selected ratio atom, with the
uniform continuum background displayed separately. -/
theorem exists_xiPhysicalPrimeLogBulkCrossDefect_curvature_recovers_fiber
    (P : Finset Nat.Primes) (A c : ℝ) :
    ∃ h : ℝ, 0 < h ∧
      xiPhysicalPrimeLogBulkCrossDefect P A (c + h) +
          xiPhysicalPrimeLogBulkCrossDefect P A (c - h) -
          2 * xiPhysicalPrimeLogBulkCrossDefect P A c =
        h * xiPhysicalPrimeLogPairDistanceFiberMass P c -
          2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P := by
  obtain ⟨h, hh, hmass⟩ :=
    exists_xiPhysicalPrimeLogPairBandCurvatureMass_eq_mul_fiberMass P c
  refine ⟨h, hh, ?_⟩
  rw [xiPhysicalPrimeLogBulkCrossDefect_width_secondDifference P A c hh.le,
    hmass]

/-- Strong local atom recovery: one positive isolation radius works for every smaller
nonnegative width step, not merely for one selected step. -/
theorem exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_curvature_recovers_fiber
    (P : Finset Nat.Primes) (A c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 ≤ h → h ≤ ε →
      xiPhysicalPrimeLogBulkCrossDefect P A (c + h) +
          xiPhysicalPrimeLogBulkCrossDefect P A (c - h) -
          2 * xiPhysicalPrimeLogBulkCrossDefect P A c =
        h * xiPhysicalPrimeLogPairDistanceFiberMass P c -
          2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P := by
  classical
  obtain ⟨ε, hε, hsep⟩ := exists_pos_le_abs_sub_on_finset
    (xiPhysicalPrimeLogOffDiagonalPairs P)
    (fun z => xiPhysicalPrimeLogBulkPairDistance z.1 z.2) c
  refine ⟨ε, hε, ?_⟩
  intro h hh hle
  rw [xiPhysicalPrimeLogBulkCrossDefect_width_secondDifference P A c hh,
    xiPhysicalPrimeLogPairBandCurvatureMass_eq_mul_fiberMass_of_isolated
      P c hh]
  intro p hp q hq hne
  apply hle.trans
  apply hsep (p, q)
  · rw [xiPhysicalPrimeLogOffDiagonalPairs]
    simp only [Finset.mem_filter, Finset.mem_product, ne_eq]
    have hqe := Finset.mem_erase.mp hq
    exact ⟨⟨hp, hqe.2⟩, hqe.1.symm⟩
  · exact hne

/-- Arithmetic atom tomography.  For each distinct prime pair in the packet, a sufficiently fine
positive aperture-width curvature recovers exactly twice its weight product; no other prime pair
can occupy the same logarithmic ratio site. -/
theorem exists_xiPhysicalPrimeLogBulkCrossDefect_curvature_recovers_primePair
    (P : Finset Nat.Primes) (A : ℝ) (p q : Nat.Primes)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    ∃ h : ℝ, 0 < h ∧
      xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q + h) +
        xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q - h) -
        2 * xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q) =
      2 * h * physicalPrimeEndpointWeight p *
          physicalPrimeEndpointWeight q -
        2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P := by
  obtain ⟨h, hh, hcurv⟩ :=
    exists_xiPhysicalPrimeLogBulkCrossDefect_curvature_recovers_fiber
      P A (xiPhysicalPrimeLogBulkPairDistance p q)
  refine ⟨h, hh, ?_⟩
  rw [hcurv,
    xiPhysicalPrimeLogPairDistanceFiberMass_at_pair P p q hp hq hpq]
  ring

/-- Sharp prime-pair cusp law.  At every ordinary-prime ratio site, every sufficiently small
positive compensated width curvature is exactly linear in the step, with coefficient twice the
prime-pair weight.  In particular the compensated curvature is not locally quadratic-flat. -/
theorem exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature_eq_primePair
    (P : Finset Nat.Primes) (A : ℝ) (p q : Nat.Primes)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h ≤ ε →
      xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q + h) +
        xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q - h) -
        2 * xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q) +
        2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P =
      2 * h * physicalPrimeEndpointWeight p *
        physicalPrimeEndpointWeight q := by
  obtain ⟨ε, hε, hcurv⟩ :=
    exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_curvature_recovers_fiber
      P A (xiPhysicalPrimeLogBulkPairDistance p q)
  refine ⟨ε, hε, ?_⟩
  intro h hh hle
  rw [hcurv h hh.le hle,
    xiPhysicalPrimeLogPairDistanceFiberMass_at_pair P p q hp hq hpq]
  ring

/-- Pointwise quadratic-flatness no-go.  At an ordinary-prime ratio site there is no finite
constant which bounds the compensated width curvature by `K * h^2` throughout a punctured right
neighborhood: the exact prime-pair cusp is linear in `h`. -/
theorem not_exists_local_quadratic_bound_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature
    (P : Finset Nat.Primes) (A : ℝ) (p q : Nat.Primes)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    ¬ ∃ K ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h ≤ ε →
      xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q + h) +
        xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q - h) -
        2 * xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q) +
        2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P ≤
      K * h ^ 2 := by
  rintro ⟨K, ε, hε, hbound⟩
  obtain ⟨δ, hδ, hcusp⟩ :=
    exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature_eq_primePair
      P A p q hp hq hpq
  let w : ℝ := physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q
  have hw : 0 < w := mul_pos (physicalPrimeEndpointWeight_pos p)
    (physicalPrimeEndpointWeight_pos q)
  let η : ℝ := min ε δ
  have hη : 0 < η := lt_min hε hδ
  let h : ℝ := min (η / 2) (w / (|K| + 1))
  have hden : 0 < |K| + 1 := by positivity
  have hh : 0 < h := lt_min (half_pos hη) (div_pos hw hden)
  have hhη : h ≤ η := (min_le_left _ _).trans (half_le_self hη.le)
  have hhε : h ≤ ε := hhη.trans (min_le_left _ _)
  have hhδ : h ≤ δ := hhη.trans (min_le_right _ _)
  have hcurv := hcusp h hh hhδ
  have hub := hbound h hh hhε
  rw [hcurv] at hub
  have hhsmall : h ≤ w / (|K| + 1) := min_le_right _ _
  have hKle : K * h ≤ |K| * h :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hh.le
  have habsle : |K| * h ≤ |K| * (w / (|K| + 1)) :=
    mul_le_mul_of_nonneg_left hhsmall (abs_nonneg K)
  have hratio : |K| * (w / (|K| + 1)) < w := by
    have hcross : |K| * w < w * (|K| + 1) := by
      nlinarith
    have hdiv := (div_lt_iff₀ hden).2 hcross
    convert hdiv using 1
    · ring
  have hKlt : K * h < 2 * w := by
    nlinarith [hKle, habsle, hratio, hw]
  have hscaled := mul_lt_mul_of_pos_right hKlt hh
  dsimp [w] at hub hscaled
  nlinarith [hub, hscaled]

/-- The sharp aperture cusp reads the actual shifted filtered Xi-source symmetric-square atom,
with the complete inverse-cubic correction exposed rather than hidden in an asymptotic error. -/
theorem exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature_eq_shiftFilteredPair
    (P : Finset Nat.Primes) (A : ℝ) (p q : Nat.Primes)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h ≤ ε →
      xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q + h) +
        xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q - h) -
        2 * xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q) +
        2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P =
      h * (2 * xiShiftFilteredPrimeEndpointWeight p *
          xiShiftFilteredPrimeEndpointWeight q +
        xiShiftFilteredPrimePairWeightCorrection p q) := by
  obtain ⟨ε, hε, hcusp⟩ :=
    exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature_eq_primePair
      P A p q hp hq hpq
  refine ⟨ε, hε, ?_⟩
  intro h hh hle
  calc
    xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q + h) +
        xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q - h) -
        2 * xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q) +
        2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P =
        2 * h * physicalPrimeEndpointWeight p *
          physicalPrimeEndpointWeight q := hcusp h hh hle
    _ = h * (2 * physicalPrimeEndpointWeight p *
          physicalPrimeEndpointWeight q) := by ring
    _ = h * (2 * xiShiftFilteredPrimeEndpointWeight p *
          xiShiftFilteredPrimeEndpointWeight q +
        xiShiftFilteredPrimePairWeightCorrection p q) := by
      rw [physicalPrimeEndpointPairWeight_eq_shiftFiltered_add_correction]

/-- Exact finite spline classification of the physical aperture profile.  On a sufficiently
small right neighborhood of every width `c`, the bulk cross defect is the quadratic with linear
coefficient equal to the cumulative ratio discrepancy at `c`.  On the left, the linear
coefficient loses exactly the ratio-fiber mass at `c`.  Thus the only knots of the finite profile
are the prime-ratio atoms, and their slope jumps are exactly their positive fiber masses. -/
theorem exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticSplineGerms
    (P : Finset Nat.Primes) (A c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h ≤ ε →
      (xiPhysicalPrimeLogBulkCrossDefect P A (c + h) =
        xiPhysicalPrimeLogBulkCrossDefect P A c +
          h * xiPhysicalPrimeLogPairCumulativeDiscrepancy P A c -
          h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P) ∧
      (xiPhysicalPrimeLogBulkCrossDefect P A (c - h) =
        xiPhysicalPrimeLogBulkCrossDefect P A c -
          h * (xiPhysicalPrimeLogPairCumulativeDiscrepancy P A c -
            xiPhysicalPrimeLogPairDistanceFiberMass P c) -
          h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P) := by
  obtain ⟨εr, hεr, hright⟩ :=
    exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_forward_recovers_cumulativeDiscrepancy
      P A c
  obtain ⟨εs, hεs, hsecond⟩ :=
    exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_curvature_recovers_fiber
      P A c
  refine ⟨min εr εs, lt_min hεr hεs, ?_⟩
  intro h hh hle
  have hler : h ≤ εr := hle.trans (min_le_left _ _)
  have hles : h ≤ εs := hle.trans (min_le_right _ _)
  have hr := hright h hh hler
  have hs := hsecond h hh.le hles
  constructor
  · linear_combination hr
  · linear_combination hs - hr

/-- Away from a ratio atom, the two one-sided spline branches glue to one quadratic chamber:
there is no hidden finite-packet differential complexity between prime-ratio knots. -/
theorem exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticChamber_of_fiberMass_eq_zero
    (P : Finset Nat.Primes) (A c : ℝ)
    (hfiber : xiPhysicalPrimeLogPairDistanceFiberMass P c = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h ≤ ε →
      (xiPhysicalPrimeLogBulkCrossDefect P A (c + h) =
        xiPhysicalPrimeLogBulkCrossDefect P A c +
          h * xiPhysicalPrimeLogPairCumulativeDiscrepancy P A c -
          h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P) ∧
      (xiPhysicalPrimeLogBulkCrossDefect P A (c - h) =
        xiPhysicalPrimeLogBulkCrossDefect P A c -
          h * xiPhysicalPrimeLogPairCumulativeDiscrepancy P A c -
          h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P) := by
  obtain ⟨ε, hε, hspline⟩ :=
    exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticSplineGerms P A c
  refine ⟨ε, hε, ?_⟩
  intro h hh hle
  simpa [hfiber] using hspline h hh hle

/-- At an ordinary-prime ratio knot, the exact slope jump of the finite physical aperture spline
is twice the physical pair weight.  This is the lossless arithmetic singularity which survives
after the smooth continuum background is removed. -/
theorem exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticSplineGerms_at_primePair
    (P : Finset Nat.Primes) (A : ℝ) (p q : Nat.Primes)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h ≤ ε →
      (xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q + h) =
        xiPhysicalPrimeLogBulkCrossDefect P A
            (xiPhysicalPrimeLogBulkPairDistance p q) +
          h * xiPhysicalPrimeLogPairCumulativeDiscrepancy P A
            (xiPhysicalPrimeLogBulkPairDistance p q) -
          h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P) ∧
      (xiPhysicalPrimeLogBulkCrossDefect P A
          (xiPhysicalPrimeLogBulkPairDistance p q - h) =
        xiPhysicalPrimeLogBulkCrossDefect P A
            (xiPhysicalPrimeLogBulkPairDistance p q) -
          h * (xiPhysicalPrimeLogPairCumulativeDiscrepancy P A
              (xiPhysicalPrimeLogBulkPairDistance p q) -
            2 * physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q) -
          h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P) := by
  obtain ⟨ε, hε, hspline⟩ :=
    exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticSplineGerms
      P A (xiPhysicalPrimeLogBulkPairDistance p q)
  refine ⟨ε, hε, ?_⟩
  intro h hh hle
  simpa [xiPhysicalPrimeLogPairDistanceFiberMass_at_pair P p q hp hq hpq] using
    hspline h hh hle

theorem xiPhysicalPrimeLogPairBandCurvatureMass_nonneg
    (P : Finset Nat.Primes) (c h : ℝ) :
    0 ≤ xiPhysicalPrimeLogPairBandCurvatureMass P c h := by
  rw [xiPhysicalPrimeLogPairBandCurvatureMass]
  exact Finset.sum_nonneg fun p hp =>
    Finset.sum_nonneg fun q hq =>
      mul_nonneg
        (mul_nonneg (physicalPrimeEndpointWeight_pos p).le
          (physicalPrimeEndpointWeight_pos q).le)
        (le_max_left _ _)

theorem xiPhysicalPrimeLogCrossWeightMass_nonneg
    (P : Finset Nat.Primes) :
    0 ≤ xiPhysicalPrimeLogCrossWeightMass P := by
  rw [xiPhysicalPrimeLogCrossWeightMass]
  exact Finset.sum_nonneg fun p hp =>
    Finset.sum_nonneg fun q hq =>
      mul_nonneg (physicalPrimeEndpointWeight_pos p).le
        (physicalPrimeEndpointWeight_pos q).le

/-- Positive-survivor semiconvexity law.  After continuum compensation, the bulk cross defect can
have no negative width curvature beyond its explicit rank-one background. -/
theorem xiPhysicalPrimeLogBulkCrossDefect_width_semiconvex
    (P : Finset Nat.Primes) (A c : ℝ)
    {h : ℝ} (hh : 0 ≤ h) :
    -(2 * h ^ 2 / A * xiPhysicalPrimeLogCrossWeightMass P) ≤
      xiPhysicalPrimeLogBulkCrossDefect P A (c + h) +
        xiPhysicalPrimeLogBulkCrossDefect P A (c - h) -
        2 * xiPhysicalPrimeLogBulkCrossDefect P A c := by
  rw [xiPhysicalPrimeLogBulkCrossDefect_width_secondDifference P A c hh]
  linarith [xiPhysicalPrimeLogPairBandCurvatureMass_nonneg P c h]

end

end RHTower
