import GaloisForLFunctions.RHTower.GammaCoPoissonIntervalFactorialBridge
import GaloisForLFunctions.HTGeometry.CompactIntervalL2Pairing

/-!
# Reflected Gamma/co-Poisson interval as a positive common-test source

Endpoint dressing and functional-equation reflection turn the raw local
Gamma/co-Poisson interval cell into an ordinary compact-interval `L²` Gram.
This is the local head fibre used by the primitive Euler source horizon.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

abbrev GammaCoPoissonIntervalL2 (L : ℝ) :=
  Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) L))

theorem memLp_two_gammaCoPoissonIntervalFeature
    (L : ℝ) (z : ℂ) :
    MemLp (fun t : ℝ => Complex.exp ((z - 1 / 2) * (t : ℂ))) 2
      (volume.restrict (Icc (0 : ℝ) L)) := by
  have hcontinuous :
      Continuous (fun t : ℝ => Complex.exp ((z - 1 / 2) * (t : ℂ))) := by
    fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun t : ℝ => Complex.exp ((z - 1 / 2) * (t : ℂ)))
    hcontinuous.continuousOn
  refine MemLp.of_bound hcontinuous.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

def gammaCoPoissonReflectedIntervalFeature
    (L : ℝ) (z : ℂ) : GammaCoPoissonIntervalL2 L :=
  (memLp_two_gammaCoPoissonIntervalFeature L z).toLp
    (fun t : ℝ => Complex.exp ((z - 1 / 2) * (t : ℂ)))

def gammaCoPoissonReflectedIntervalKernel
    (L : ℝ) (z w : ℂ) : ℂ :=
  inner ℂ
    (gammaCoPoissonReflectedIntervalFeature L w)
    (gammaCoPoissonReflectedIntervalFeature L z)

theorem gammaCoPoissonReflectedIntervalKernel_eq_integral
    {L : ℝ} (hL : 0 ≤ L) (z w : ℂ) :
    gammaCoPoissonReflectedIntervalKernel L z w =
      ∫ t in (0 : ℝ)..L,
        Complex.exp ((z + (starRingEnd ℂ) w - 1) * (t : ℂ)) := by
  rw [gammaCoPoissonReflectedIntervalKernel, MeasureTheory.L2.inner_def]
  calc
    (∫ t,
        inner ℂ
          (gammaCoPoissonReflectedIntervalFeature L w t)
          (gammaCoPoissonReflectedIntervalFeature L z t)
        ∂volume.restrict (Icc (0 : ℝ) L)) =
        ∫ t in Icc (0 : ℝ) L,
          Complex.exp ((z + (starRingEnd ℂ) w - 1) * (t : ℂ)) := by
      apply integral_congr_ae
      filter_upwards
        [(memLp_two_gammaCoPoissonIntervalFeature L w).coeFn_toLp,
          (memLp_two_gammaCoPoissonIntervalFeature L z).coeFn_toLp]
          with t hw hz
      rw [show gammaCoPoissonReflectedIntervalFeature L w t =
          Complex.exp ((w - 1 / 2) * (t : ℂ)) from hw,
        show gammaCoPoissonReflectedIntervalFeature L z t =
          Complex.exp ((z - 1 / 2) * (t : ℂ)) from hz]
      simp only [RCLike.inner_apply]
      rw [← Complex.exp_conj, map_mul, map_sub]
      simp only [Complex.conj_ofReal]
      rw [← Complex.exp_add]
      congr 1
      have hhalf :
          (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
        apply Complex.ext <;> norm_num
      rw [hhalf]
      ring
    _ = ∫ t in (0 : ℝ)..L,
          Complex.exp ((z + (starRingEnd ℂ) w - 1) * (t : ℂ)) := by
      rw [intervalIntegral.integral_of_le hL, integral_Icc_eq_integral_Ioc]

/-- Endpoint-dressed functional-equation reflection turns the local
Gamma/co-Poisson interval cell into an ordinary Hilbert Gram kernel. -/
theorem gammaCoPoissonReflectedIntervalKernel_eq_cell
    {L : ℝ} (hL : 0 ≤ L) (z w : ℂ) :
    gammaCoPoissonReflectedIntervalKernel L z w =
      Complex.exp (((starRingEnd ℂ) w - 1 / 2) * (L : ℂ)) *
        gammaCoPoissonIntervalCell (L : ℂ) z
          (1 - (starRingEnd ℂ) w) := by
  let A : ℂ := z + (starRingEnd ℂ) w - 1
  by_cases hA : A = 0
  · have hzw : z = 1 - (starRingEnd ℂ) w := by
      dsimp only [A] at hA
      linear_combination hA
    rw [gammaCoPoissonReflectedIntervalKernel_eq_integral hL]
    simp only [A, hA, zero_mul, Complex.exp_zero]
    rw [intervalIntegral.integral_const]
    rw [hzw, gammaCoPoissonIntervalCell_self]
    rw [← mul_assoc, ← Complex.exp_add]
    have hexponent :
        ((starRingEnd ℂ) w - 1 / 2) * (L : ℂ) +
            ((1 - (starRingEnd ℂ) w - 1 / 2) * (L : ℂ)) = 0 := by
      ring
    rw [hexponent, Complex.exp_zero, one_mul]
    simp
  · have hne : z ≠ 1 - (starRingEnd ℂ) w := by
      intro h
      apply hA
      dsimp only [A]
      rw [h]
      ring
    rw [gammaCoPoissonReflectedIntervalKernel_eq_integral hL,
      integral_exp_mul_complex hA,
      gammaCoPoissonIntervalCell_eq_dividedDifference _ _ _ hne]
    have hden :
        z - (1 - (starRingEnd ℂ) w) = A := by
      dsimp only [A]
      ring
    rw [hden]
    norm_num only [ofReal_zero, mul_zero, Complex.exp_zero]
    change
      (Complex.exp (A * (L : ℂ)) - 1) / A =
        Complex.exp (((starRingEnd ℂ) w - 1 / 2) * (L : ℂ)) *
          ((Complex.exp ((z - 1 / 2) * (L : ℂ)) -
            Complex.exp ((1 - (starRingEnd ℂ) w - 1 / 2) * (L : ℂ))) / A)
    field_simp [hA]
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · congr 1
      dsimp only [A]
      ring
    · rw [← Complex.exp_zero]
      congr 1
      ring

def gammaCoPoissonReflectedIntervalMatrix
    {n : ℕ} (L : ℝ) (node : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => gammaCoPoissonReflectedIntervalKernel L (node j) (node i)

theorem gammaCoPoissonReflectedIntervalMatrix_eq_gram
    {n : ℕ} (L : ℝ) (node : Fin n → ℂ) :
    gammaCoPoissonReflectedIntervalMatrix L node =
      Matrix.gram ℂ
        (fun i => gammaCoPoissonReflectedIntervalFeature L (node i)) := by
  ext i j
  rw [Matrix.gram_apply]
  rfl

/-- Every finite spectral packet sees a positive semidefinite reflected
interval cell.  Unlike the undressed cell, this statement holds for arbitrary
complex nodes, not only a real two-character slice. -/
theorem gammaCoPoissonReflectedIntervalMatrix_posSemidef
    {n : ℕ} (L : ℝ) (node : Fin n → ℂ) :
    (gammaCoPoissonReflectedIntervalMatrix L node).PosSemidef := by
  rw [gammaCoPoissonReflectedIntervalMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℂ _

theorem gammaCoPoissonReflectedIntervalMatrix_apply_eq_cell
    {n : ℕ} {L : ℝ} (hL : 0 ≤ L) (node : Fin n → ℂ)
    (i j : Fin n) :
    gammaCoPoissonReflectedIntervalMatrix L node i j =
      Complex.exp
          (((starRingEnd ℂ) (node i) - 1 / 2) * (L : ℂ)) *
        gammaCoPoissonIntervalCell (L : ℂ) (node j)
          (1 - (starRingEnd ℂ) (node i)) :=
  gammaCoPoissonReflectedIntervalKernel_eq_cell hL (node j) (node i)

/-- Finite label-sensitive direct sum of reflected interval cells. -/
def finiteGammaCoPoissonReflectedSourceMatrix
    {P : Type*} [Fintype P] {n : ℕ}
    (weight action : P → ℝ) (node : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ p : P, (weight p : ℂ) •
    gammaCoPoissonReflectedIntervalMatrix (action p) node

/-- Nonnegative primitive weights make every finite action-mixed reflected
source packet positive semidefinite. -/
theorem finiteGammaCoPoissonReflectedSourceMatrix_posSemidef
    {P : Type*} [Fintype P] {n : ℕ}
    (weight action : P → ℝ) (node : Fin n → ℂ)
    (hweight : ∀ p, 0 ≤ weight p) :
    (finiteGammaCoPoissonReflectedSourceMatrix
      weight action node).PosSemidef := by
  unfold finiteGammaCoPoissonReflectedSourceMatrix
  exact Finset.sum_induction _ _
    (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero
    (fun p _ => by
      apply Matrix.PosSemidef.smul
      · exact gammaCoPoissonReflectedIntervalMatrix_posSemidef (action p) node
      · exact Complex.nonneg_iff.mpr ⟨hweight p, by simp⟩)

theorem finiteGammaCoPoissonReflectedSourceMatrix_apply_eq_cell
    {P : Type*} [Fintype P] {n : ℕ}
    (weight action : P → ℝ) (node : Fin n → ℂ)
    (haction : ∀ p, 0 ≤ action p) (i j : Fin n) :
    finiteGammaCoPoissonReflectedSourceMatrix weight action node i j =
      ∑ p : P, (weight p : ℂ) *
        Complex.exp
          (((starRingEnd ℂ) (node i) - 1 / 2) * (action p : ℂ)) *
        gammaCoPoissonIntervalCell (action p : ℂ) (node j)
          (1 - (starRingEnd ℂ) (node i)) := by
  simp only [finiteGammaCoPoissonReflectedSourceMatrix,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [gammaCoPoissonReflectedIntervalMatrix_apply_eq_cell
    (haction p)]
  ring

end

end RHTower
