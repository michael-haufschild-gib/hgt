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

/-- Logarithmic distance between two prime locations. -/
def xiPhysicalPrimeLogBulkPairDistance (p q : Nat.Primes) : ℝ :=
  |Real.log (p : ℝ) - Real.log (q : ℝ)|

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

private theorem sum_secondDifference
    {ι : Type*} (P : Finset ι) (f g r : ι → ℝ) :
    (∑ i ∈ P, f i) + (∑ i ∈ P, g i) - 2 * (∑ i ∈ P, r i) =
      ∑ i ∈ P, (f i + g i - 2 * r i) := by
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

theorem physicalPrimeEndpointWeight_pos (p : Nat.Primes) :
    0 < physicalPrimeEndpointWeight p := by
  rw [physicalPrimeEndpointWeight]
  exact div_pos (Real.log_pos (by exact_mod_cast p.prop.one_lt))
    (by exact_mod_cast p.prop.pos)

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
