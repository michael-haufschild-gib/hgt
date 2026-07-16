import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Geometric CDD constraint

Finite truncations of the geometric Blaschke--CDD product already carry the exact static laws used
by the physical hypertranscendental scattering candidate: one-step `q` self-similarity, inversion
under reversal of the crossing coordinate, and rapidity crossing symmetry.

This file is the finite algebraic core only.  It does not claim convergence of the infinite
product, regular-strip boundedness, hypertranscendence, modular nuclearity, or construction of a
local quantum field theory.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- One squared geometric CDD factor.  Squaring records the reality-paired rapidity zeros which
have the same crossing-coordinate value. -/
def geometricCDDStep
    {K : Type*} [Field K] (q t : K) (k : ℕ) : K :=
  ((1 - q ^ k * t) / (1 + q ^ k * t)) ^ 2

/-- Finite geometric CDD product through scales `0,...,N-1`. -/
def geometricCDDTruncation
    {K : Type*} [Field K] (q t : K) (N : ℕ) : K :=
  ∏ k ∈ Finset.range N, geometricCDDStep q t k

@[simp]
theorem geometricCDDTruncation_zero
    {K : Type*} [Field K] (q t : K) :
    geometricCDDTruncation q t 0 = 1 := by
  simp [geometricCDDTruncation]

/-- Scaling the crossing coordinate shifts the geometric factor index by one. -/
theorem geometricCDDStep_succ_eq_scale
    {K : Type*} [Field K] (q t : K) (k : ℕ) :
    geometricCDDStep q t (k + 1) = geometricCDDStep q (q * t) k := by
  simp only [geometricCDDStep, pow_succ]
  congr 2 <;> ring

/-- Exact finite `q`-constraint.  The new scale-zero factor is the boundary term left by shifting
all older scales. -/
theorem geometricCDDTruncation_succ_constraint
    {K : Type*} [Field K] (q t : K) (N : ℕ) :
    geometricCDDTruncation q t (N + 1) =
      geometricCDDStep q t 0 * geometricCDDTruncation q (q * t) N := by
  rw [geometricCDDTruncation, Finset.prod_range_succ']
  simp_rw [geometricCDDStep_succ_eq_scale]
  rw [geometricCDDTruncation]
  ring

/-- One nonsingular CDD factor times its reversed-coordinate factor is one. -/
theorem geometricCDDStep_neg_mul
    {K : Type*} [Field K] (q t : K) (k : ℕ)
    (hminus : 1 - q ^ k * t ≠ 0) (hplus : 1 + q ^ k * t ≠ 0) :
    geometricCDDStep q (-t) k * geometricCDDStep q t k = 1 := by
  unfold geometricCDDStep
  have hnegmul : q ^ k * (-t) = -(q ^ k * t) := by ring
  rw [hnegmul]
  rw [sub_neg_eq_add, ← sub_eq_add_neg]
  let a := q ^ k * t
  change 1 - a ≠ 0 at hminus
  change 1 + a ≠ 0 at hplus
  change (((1 + a) / (1 - a)) ^ 2) * (((1 - a) / (1 + a)) ^ 2) = 1
  field_simp [hminus, hplus]

/-- Finite unitarity/inversion identity away from the finite zero and pole set. -/
theorem geometricCDDTruncation_neg_mul
    {K : Type*} [Field K] (q t : K) (N : ℕ)
    (hminus : ∀ k < N, 1 - q ^ k * t ≠ 0)
    (hplus : ∀ k < N, 1 + q ^ k * t ≠ 0) :
    geometricCDDTruncation q (-t) N * geometricCDDTruncation q t N = 1 := by
  rw [geometricCDDTruncation, geometricCDDTruncation,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k hk
  rw [Finset.mem_range] at hk
  exact geometricCDDStep_neg_mul q t k (hminus k hk) (hplus k hk)

/-- Canonical crossing coordinate for a rapidity variable. -/
noncomputable def geometricCDDCrossingCoordinate (C theta : ℂ) : ℂ :=
  -Complex.I * Complex.sinh theta / C

@[simp]
theorem geometricCDDCrossingCoordinate_neg (C theta : ℂ) :
    geometricCDDCrossingCoordinate C (-theta) =
      -geometricCDDCrossingCoordinate C theta := by
  simp [geometricCDDCrossingCoordinate, Complex.sinh_neg]
  ring

/-- A shift by the physical crossing period reverses the crossing coordinate. -/
theorem geometricCDDCrossingCoordinate_add_pi_mul_I (C theta : ℂ) :
    geometricCDDCrossingCoordinate C (theta + (Real.pi : ℂ) * Complex.I) =
      -geometricCDDCrossingCoordinate C theta := by
  have hsinh : Complex.sinh (theta + (Real.pi : ℂ) * Complex.I) =
      -Complex.sinh theta := by
    rw [Complex.sinh_add]
    rw [Complex.sinh_mul_I, Complex.cosh_mul_I]
    rw [← Complex.ofReal_sin, Real.sin_pi]
    rw [← Complex.ofReal_cos, Real.cos_pi]
    norm_num
  rw [geometricCDDCrossingCoordinate, hsinh,
    geometricCDDCrossingCoordinate]
  ring

/-- Every nonsingular finite geometric CDD truncation satisfies rapidity unitarity. -/
theorem geometricCDDTruncation_rapidity_neg_mul
    (q C theta : ℂ) (N : ℕ)
    (hminus : ∀ k < N,
      1 - q ^ k * geometricCDDCrossingCoordinate C theta ≠ 0)
    (hplus : ∀ k < N,
      1 + q ^ k * geometricCDDCrossingCoordinate C theta ≠ 0) :
    geometricCDDTruncation q (geometricCDDCrossingCoordinate C (-theta)) N *
        geometricCDDTruncation q (geometricCDDCrossingCoordinate C theta) N = 1 := by
  rw [geometricCDDCrossingCoordinate_neg]
  exact geometricCDDTruncation_neg_mul q _ N hminus hplus

/-- Every nonsingular finite geometric CDD truncation satisfies crossing-period inversion. -/
theorem geometricCDDTruncation_rapidity_crossing_mul
    (q C theta : ℂ) (N : ℕ)
    (hminus : ∀ k < N,
      1 - q ^ k * geometricCDDCrossingCoordinate C theta ≠ 0)
    (hplus : ∀ k < N,
      1 + q ^ k * geometricCDDCrossingCoordinate C theta ≠ 0) :
    geometricCDDTruncation q
        (geometricCDDCrossingCoordinate C
          (theta + (Real.pi : ℂ) * Complex.I)) N *
        geometricCDDTruncation q (geometricCDDCrossingCoordinate C theta) N = 1 := by
  rw [geometricCDDCrossingCoordinate_add_pi_mul_I]
  exact geometricCDDTruncation_neg_mul q _ N hminus hplus

/-- The continuous unwrapped real-axis scattering phase of a finite geometric CDD truncation.
The additive `pi` records the overall fermionic sign in `S=-P`. -/
noncomputable def geometricCDDTruncationPhase
    (q C theta : ℝ) (N : ℕ) : ℝ :=
  Real.pi + 4 * ∑ k ∈ Finset.range N,
    Real.arctan (q ^ k * Real.sinh theta / C)

/-- Exact rapidity slope of the finite unwrapped scattering phase. -/
noncomputable def geometricCDDTruncationPhaseSlope
    (q C theta : ℝ) (N : ℕ) : ℝ :=
  4 * ∑ k ∈ Finset.range N,
    (q ^ k * Real.cosh theta / C) /
      (1 + (q ^ k * Real.sinh theta / C) ^ 2)

/-- The displayed finite phase slope is the actual derivative of the unwrapped CDD phase. -/
theorem hasDerivAt_geometricCDDTruncationPhase
    (q C theta : ℝ) (N : ℕ) :
    HasDerivAt (fun u ↦ geometricCDDTruncationPhase q C u N)
      (geometricCDDTruncationPhaseSlope q C theta N) theta := by
  unfold geometricCDDTruncationPhase geometricCDDTruncationPhaseSlope
  have hterm : ∀ k ∈ Finset.range N,
      HasDerivAt
        (fun u : ℝ ↦ Real.arctan (q ^ k * Real.sinh u / C))
        ((q ^ k * Real.cosh theta / C) /
          (1 + (q ^ k * Real.sinh theta / C) ^ 2)) theta := by
    intro k hk
    convert (((Real.hasDerivAt_sinh theta).const_mul (q ^ k)).div_const C).arctan using 1
    all_goals ring
  have hsum := HasDerivAt.sum hterm
  simpa only [Pi.add_apply, Finset.sum_apply, zero_add] using
    (hasDerivAt_const theta Real.pi).add (hsum.const_mul 4)

/-- Every nonempty physical finite truncation has strictly increasing unwrapped phase. -/
theorem geometricCDDTruncationPhaseSlope_pos
    {q C : ℝ} (hq : 0 < q) (hC : 0 < C) (theta : ℝ) (N : ℕ) :
    0 < geometricCDDTruncationPhaseSlope q C theta (N + 1) := by
  unfold geometricCDDTruncationPhaseSlope
  apply mul_pos (by norm_num)
  apply Finset.sum_pos
  · intro k hk
    apply div_pos
    · exact div_pos (mul_pos (pow_pos hq k) (Real.cosh_pos theta)) hC
    · positivity
  · exact ⟨0, by simp⟩

/-- The real-axis phase derivative of every nonempty physical truncation is positive. -/
theorem deriv_geometricCDDTruncationPhase_pos
    {q C : ℝ} (hq : 0 < q) (hC : 0 < C) (theta : ℝ) (N : ℕ) :
    0 < deriv (fun u ↦ geometricCDDTruncationPhase q C u (N + 1)) theta := by
  rw [(hasDerivAt_geometricCDDTruncationPhase q C theta (N + 1)).deriv]
  exact geometricCDDTruncationPhaseSlope_pos hq hC theta N

end GaloisForLFunctions.HTGeometry
