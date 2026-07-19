import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureFusion
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The true physical prime-log aperture Hilbert metric

The clipped aperture intervals are embedded as oriented centered indicators in real `L²`.
Their inherited distance is the true hard-aperture metric: it retains the sign lost by a
projective line metric and varies continuously under hard-cutoff motion, unlike a support-gap
metric.

This file identifies the previously explicit overlap kernel with the actual Hilbert Gram,
proves the exact quotient-distance formula, and realizes the complete coherent fusion energy as
a squared `L²` norm.  Thus the full kernel, not only its diagonal, is positive semidefinite.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The clipped interval carried by one physical prime endpoint. -/
def xiPhysicalPrimeLogApertureSet
    (A m k : ℝ) (p : Nat.Primes) : Set ℝ :=
  Ioc (xiPhysicalPrimeLogApertureStart m p)
    (xiPhysicalPrimeLogApertureEnd A k p)

/-- The ambient hard aperture. -/
def xiPhysicalLogApertureSet (A : ℝ) : Set ℝ := Ioc 0 A

theorem volume_real_xiPhysicalPrimeLogApertureSet
    (A m k : ℝ) (p : Nat.Primes) :
    volume.real (xiPhysicalPrimeLogApertureSet A m k p) =
      xiPhysicalPrimeLogApertureLength A m k p := by
  rw [xiPhysicalPrimeLogApertureSet, xiPhysicalPrimeLogApertureLength,
    Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal', max_comm]

theorem xiPhysicalPrimeLogApertureSet_inter
    (A m k : ℝ) (p q : Nat.Primes) :
    xiPhysicalPrimeLogApertureSet A m k p ∩
        xiPhysicalPrimeLogApertureSet A m k q =
      Ioc (max (xiPhysicalPrimeLogApertureStart m p)
          (xiPhysicalPrimeLogApertureStart m q))
        (min (xiPhysicalPrimeLogApertureEnd A k p)
          (xiPhysicalPrimeLogApertureEnd A k q)) := by
  ext u
  simp only [xiPhysicalPrimeLogApertureSet, mem_inter_iff, mem_Ioc]
  constructor
  · rintro ⟨⟨hsp, hep⟩, hsq, heq⟩
    exact ⟨max_lt hsp hsq, le_min hep heq⟩
  · rintro ⟨hs, he⟩
    exact ⟨⟨(max_lt_iff.mp hs).1, (le_min_iff.mp he).1⟩,
      (max_lt_iff.mp hs).2, (le_min_iff.mp he).2⟩

theorem volume_real_xiPhysicalPrimeLogApertureSet_inter
    (A m k : ℝ) (p q : Nat.Primes) :
    volume.real (xiPhysicalPrimeLogApertureSet A m k p ∩
        xiPhysicalPrimeLogApertureSet A m k q) =
      xiPhysicalPrimeLogApertureOverlap A m k p q := by
  rw [xiPhysicalPrimeLogApertureSet_inter,
    xiPhysicalPrimeLogApertureOverlap, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal', max_comm]

theorem xiPhysicalPrimeLogApertureSet_subset
    (A m k : ℝ) (p : Nat.Primes) :
    xiPhysicalPrimeLogApertureSet A m k p ⊆
      xiPhysicalLogApertureSet A := by
  intro u hu
  rw [xiPhysicalPrimeLogApertureSet, mem_Ioc] at hu
  rw [xiPhysicalLogApertureSet, mem_Ioc]
  exact ⟨lt_of_le_of_lt (xiPhysicalPrimeLogApertureStart_nonneg m p) hu.1,
    hu.2.trans (xiPhysicalPrimeLogApertureEnd_le A k p)⟩

theorem volume_real_xiPhysicalLogApertureSet
    {A : ℝ} (hA : 0 < A) :
    volume.real (xiPhysicalLogApertureSet A) = A := by
  rw [xiPhysicalLogApertureSet, Measure.real, Real.volume_Ioc, sub_zero]
  exact ENNReal.toReal_ofReal hA.le

/-- The real Hilbert space which carries oriented physical apertures. -/
abbrev XiPhysicalApertureL2 :=
  MeasureTheory.Lp ℝ 2 (volume : Measure ℝ)

theorem measure_xiPhysicalPrimeLogApertureSet_ne_top
    (A m k : ℝ) (p : Nat.Primes) :
    volume (xiPhysicalPrimeLogApertureSet A m k p) ≠ ⊤ := by
  rw [xiPhysicalPrimeLogApertureSet]
  exact ne_of_lt measure_Ioc_lt_top

theorem measure_xiPhysicalLogApertureSet_ne_top (A : ℝ) :
    volume (xiPhysicalLogApertureSet A) ≠ ⊤ := by
  rw [xiPhysicalLogApertureSet]
  exact ne_of_lt measure_Ioc_lt_top

/-- The uncentered indicator of one clipped prime aperture. -/
def xiPhysicalPrimeLogApertureIndicator
    (A m k : ℝ) (p : Nat.Primes) : XiPhysicalApertureL2 :=
  indicatorConstLp (μ := (volume : Measure ℝ)) 2
    (s := xiPhysicalPrimeLogApertureSet A m k p) measurableSet_Ioc
    (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p) (1 : ℝ)

/-- Constant-direction indicator of the whole physical aperture. -/
def xiPhysicalLogApertureIndicator
    (A : ℝ) : XiPhysicalApertureL2 :=
  indicatorConstLp (μ := (volume : Measure ℝ)) 2
    (s := xiPhysicalLogApertureSet A) measurableSet_Ioc
    (measure_xiPhysicalLogApertureSet_ne_top A) (1 : ℝ)

/-- The true oriented aperture carrier: the clipped interval indicator projected away from the
constant aperture direction. -/
def xiPhysicalPrimeLogCenteredApertureCarrier
    (A m k : ℝ) (p : Nat.Primes) : XiPhysicalApertureL2 :=
  xiPhysicalPrimeLogApertureIndicator A m k p -
    (xiPhysicalPrimeLogApertureLength A m k p / A) •
      xiPhysicalLogApertureIndicator A

theorem real_inner_xiPhysicalPrimeLogApertureIndicator
    (A m k : ℝ) (p q : Nat.Primes) :
    inner ℝ (xiPhysicalPrimeLogApertureIndicator A m k p)
        (xiPhysicalPrimeLogApertureIndicator A m k q) =
      xiPhysicalPrimeLogApertureOverlap A m k p q := by
  simpa only [xiPhysicalPrimeLogApertureIndicator,
      volume_real_xiPhysicalPrimeLogApertureSet_inter] using
    (MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := (volume : Measure ℝ))
      (s := xiPhysicalPrimeLogApertureSet A m k p)
      (t := xiPhysicalPrimeLogApertureSet A m k q)
      measurableSet_Ioc measurableSet_Ioc
      (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p)
      (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k q))

theorem real_inner_xiPhysicalPrimeLogApertureIndicator_aperture
    (A m k : ℝ) (p : Nat.Primes) :
    inner ℝ (xiPhysicalPrimeLogApertureIndicator A m k p)
        (xiPhysicalLogApertureIndicator A) =
      xiPhysicalPrimeLogApertureLength A m k p := by
  have hinter : xiPhysicalPrimeLogApertureSet A m k p ∩
      xiPhysicalLogApertureSet A =
      xiPhysicalPrimeLogApertureSet A m k p :=
    Set.inter_eq_left.mpr (xiPhysicalPrimeLogApertureSet_subset A m k p)
  simpa only [xiPhysicalPrimeLogApertureIndicator,
      xiPhysicalLogApertureIndicator, hinter,
      volume_real_xiPhysicalPrimeLogApertureSet] using
    (MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := (volume : Measure ℝ))
      (s := xiPhysicalPrimeLogApertureSet A m k p)
      (t := xiPhysicalLogApertureSet A)
      measurableSet_Ioc measurableSet_Ioc
      (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p)
      (measure_xiPhysicalLogApertureSet_ne_top A))

theorem real_inner_xiPhysicalLogApertureIndicator_prime
    (A m k : ℝ) (p : Nat.Primes) :
    inner ℝ (xiPhysicalLogApertureIndicator A)
        (xiPhysicalPrimeLogApertureIndicator A m k p) =
      xiPhysicalPrimeLogApertureLength A m k p := by
  rw [real_inner_comm]
  exact real_inner_xiPhysicalPrimeLogApertureIndicator_aperture A m k p

theorem real_inner_xiPhysicalLogApertureIndicator
    {A : ℝ} (hA : 0 < A) :
    inner ℝ (xiPhysicalLogApertureIndicator A)
        (xiPhysicalLogApertureIndicator A) = A := by
  simpa only [xiPhysicalLogApertureIndicator, inter_self,
      volume_real_xiPhysicalLogApertureSet hA] using
    (MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := (volume : Measure ℝ))
      (s := xiPhysicalLogApertureSet A) (t := xiPhysicalLogApertureSet A)
      measurableSet_Ioc measurableSet_Ioc
      (measure_xiPhysicalLogApertureSet_ne_top A)
      (measure_xiPhysicalLogApertureSet_ne_top A))

/-- Exact Gram realization of the concrete centered overlap kernel. -/
theorem real_inner_xiPhysicalPrimeLogCenteredApertureCarrier
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p q : Nat.Primes) :
    inner ℝ (xiPhysicalPrimeLogCenteredApertureCarrier A m k p)
        (xiPhysicalPrimeLogCenteredApertureCarrier A m k q) =
      xiPhysicalPrimeLogApertureFusionKernel A m k p q := by
  simp only [xiPhysicalPrimeLogCenteredApertureCarrier,
    inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_xiPhysicalPrimeLogApertureIndicator,
    real_inner_xiPhysicalPrimeLogApertureIndicator_aperture,
    real_inner_xiPhysicalLogApertureIndicator_prime,
    real_inner_xiPhysicalLogApertureIndicator hA,
    xiPhysicalPrimeLogApertureFusionKernel]
  field_simp [hA.ne']
  ring

/-- The true physical Hilbert distance between two oriented clipped prime apertures. -/
def xiPhysicalPrimeLogApertureHilbertDistance
    (A m k : ℝ) (p q : Nat.Primes) : ℝ :=
  dist (xiPhysicalPrimeLogCenteredApertureCarrier A m k p)
    (xiPhysicalPrimeLogCenteredApertureCarrier A m k q)

theorem xiPhysicalPrimeLogApertureHilbertDistance_nonneg
    (A m k : ℝ) (p q : Nat.Primes) :
    0 ≤ xiPhysicalPrimeLogApertureHilbertDistance A m k p q :=
  dist_nonneg

theorem xiPhysicalPrimeLogApertureHilbertDistance_self
    (A m k : ℝ) (p : Nat.Primes) :
    xiPhysicalPrimeLogApertureHilbertDistance A m k p p = 0 :=
  dist_self _

theorem xiPhysicalPrimeLogApertureHilbertDistance_symm
    (A m k : ℝ) (p q : Nat.Primes) :
    xiPhysicalPrimeLogApertureHilbertDistance A m k p q =
      xiPhysicalPrimeLogApertureHilbertDistance A m k q p :=
  dist_comm _ _

theorem xiPhysicalPrimeLogApertureHilbertDistance_triangle
    (A m k : ℝ) (p q r : Nat.Primes) :
    xiPhysicalPrimeLogApertureHilbertDistance A m k p r ≤
      xiPhysicalPrimeLogApertureHilbertDistance A m k p q +
        xiPhysicalPrimeLogApertureHilbertDistance A m k q r :=
  dist_triangle _ _ _

/-- Polarization identifies the square of the true aperture distance with the concrete fusion
kernel. -/
theorem xiPhysicalPrimeLogApertureHilbertDistance_sq_eq_kernel
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p q : Nat.Primes) :
    xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 =
      xiPhysicalPrimeLogApertureFusionKernel A m k p p +
        xiPhysicalPrimeLogApertureFusionKernel A m k q q -
        2 * xiPhysicalPrimeLogApertureFusionKernel A m k p q := by
  rw [xiPhysicalPrimeLogApertureHilbertDistance, dist_eq_norm,
    norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq,
    real_inner_xiPhysicalPrimeLogCenteredApertureCarrier hA,
    real_inner_xiPhysicalPrimeLogCenteredApertureCarrier hA,
    real_inner_xiPhysicalPrimeLogCenteredApertureCarrier hA]
  ring

/-- Exact quotient-distance formula for the clipped physical intervals. -/
theorem xiPhysicalPrimeLogApertureHilbertDistance_sq_eq
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p q : Nat.Primes) :
    xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 =
      xiPhysicalPrimeLogApertureLength A m k p +
        xiPhysicalPrimeLogApertureLength A m k q -
        2 * xiPhysicalPrimeLogApertureOverlap A m k p q -
        (xiPhysicalPrimeLogApertureLength A m k p -
          xiPhysicalPrimeLogApertureLength A m k q) ^ 2 / A := by
  rw [xiPhysicalPrimeLogApertureHilbertDistance_sq_eq_kernel hA,
    xiPhysicalPrimeLogApertureFusionKernel_diagonal,
    xiPhysicalPrimeLogApertureFusionKernel_diagonal,
    xiPhysicalPrimeLogApertureFusionKernel]
  ring

/-- Coherent weighted aperture carrier of a finite prime packet. -/
def xiPhysicalPrimeLogAggregateApertureCarrier
    (P : Finset Nat.Primes) (A m k : ℝ) : XiPhysicalApertureL2 :=
  ∑ p ∈ P, physicalPrimeEndpointWeight p •
    xiPhysicalPrimeLogCenteredApertureCarrier A m k p

/-- The complete physical fusion energy is literally the squared norm of the coherent centered
aperture carrier.  This upgrades the explicit overlap formula to an actual Hilbert Gram law. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k =
      ‖xiPhysicalPrimeLogAggregateApertureCarrier P A m k‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    xiPhysicalPrimeLogAggregateApertureCarrier, sum_inner,
    xiPhysicalPrimeLogApertureFusionEnergy]
  apply Finset.sum_congr rfl
  intro p hp
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [real_inner_smul_left, real_inner_smul_right,
    real_inner_xiPhysicalPrimeLogCenteredApertureCarrier hA]
  ring

theorem xiPhysicalPrimeLogApertureFusionEnergy_nonneg
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    0 ≤ xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  rw [xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA m k]
  positivity

/-- The exact positive survivor for the signed cross term: it can be negative, but never below
the negative diagonal energy because their sum is a squared Hilbert norm. -/
theorem neg_xiPhysicalPrimeLogApertureDiagonalEnergy_le_crossDefect
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    -xiPhysicalPrimeLogApertureDiagonalEnergy P A m k ≤
      xiPhysicalPrimeLogApertureCrossDefect P A m k := by
  have henergy := xiPhysicalPrimeLogApertureFusionEnergy_nonneg P hA m k
  rw [xiPhysicalPrimeLogApertureFusionEnergy_eq_diagonal_add_cross] at henergy
  linarith

end

end RHTower
