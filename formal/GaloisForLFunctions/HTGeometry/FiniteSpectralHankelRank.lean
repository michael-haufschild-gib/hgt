import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Instances.Matrix

/-!
# Finite spectral width forces finite Hankel rank

A clock observed through `d` spectral lines has moments

`m n = ∑ i : Fin d, mass i * node i ^ n`.

The polynomial whose roots are the observed nodes gives a nonzero kernel vector for the
`(d + 1) × (d + 1)` moment Hankel matrix.  Thus its determinant vanishes.  The same obstruction
survives pointwise limits and local finite-coordinate approximation when the width `d` is fixed.

This is the exact finite-dimensional boundary behind Prony reconstruction, finite-rate-of-
innovation models, finite quantum spectra, and finite sums of audio sinusoids.  It is deliberately
stated without positivity or distinctness assumptions: allowing signed masses and repeated nodes
makes the obstruction stronger.
-/

open Filter Polynomial Topology
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- The moment sequence of `d` spectral lines with arbitrary real masses and nodes. -/
def finiteSpectralMoment {d : ℕ} (mass node : Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ i, mass i * node i ^ n

/-- A sequence has spectral width at most `d`.  Zero masses permit padding, so an exact `Fin d`
presentation represents every smaller finite width as well. -/
def SpectralWidthAtMost (d : ℕ) (m : ℕ → ℝ) : Prop :=
  ∃ mass node : Fin d → ℝ, m = finiteSpectralMoment mass node

/-- Every finite coordinate block of `target` is arbitrarily approximable by spectral moment
sequences with one *fixed* width bound `d`. -/
def FixedSpectralWidthLocalClosure (d : ℕ) (target : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ mass node : Fin d → ℝ,
      ∀ n : ℕ, n < N → dist (finiteSpectralMoment mass node n) (target n) < ε

/-- The node polynomial annihilates every row of the first Hankel block beyond the spectral
width.  This is the algebraic core of the finite-rank obstruction. -/
theorem momentHankelMatrix_mulVec_nodePolynomial_eq_zero
    {d : ℕ} (mass node : Fin d → ℝ) :
    momentHankelMatrix (finiteSpectralMoment mass node) (d + 1) *ᵥ
        (fun j : Fin (d + 1) ↦
          (∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))).coeff (j : ℕ)) = 0 := by
  let p : Polynomial ℝ := ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))
  have hpmon : p.Monic := by
    exact Polynomial.monic_prod_of_monic _ _
      (fun i _ ↦ Polynomial.monic_X_sub_C (node i))
  have hpdeg : p.natDegree = d := by
    rw [show p = ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i)) by rfl,
      Polynomial.natDegree_prod_of_monic _ _
        (fun i _ ↦ Polynomial.monic_X_sub_C (node i))]
    simp
  have hroot : ∀ i : Fin d, p.eval (node i) = 0 := by
    intro i
    rw [show p = ∏ k : Fin d, (Polynomial.X - Polynomial.C (node k)) by rfl,
      Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  funext r
  simp only [Matrix.mulVec, momentHankelMatrix, Pi.zero_apply]
  change ∑ j : Fin (d + 1),
      finiteSpectralMoment mass node ((r : ℕ) + (j : ℕ)) * p.coeff (j : ℕ) = 0
  calc
    ∑ j : Fin (d + 1),
        finiteSpectralMoment mass node ((r : ℕ) + (j : ℕ)) * p.coeff (j : ℕ) =
        ∑ j : Fin (d + 1), ∑ i : Fin d,
          (mass i * node i ^ (r : ℕ)) * (p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [finiteSpectralMoment, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
      ring
    _ = ∑ i : Fin d, ∑ j : Fin (d + 1),
          (mass i * node i ^ (r : ℕ)) * (p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, (mass i * node i ^ (r : ℕ)) *
          (∑ j : Fin (d + 1), p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i : Fin d, (mass i * node i ^ (r : ℕ)) * p.eval (node i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < d + 1)]
      rw [Finset.sum_range fun j ↦ p.coeff j * node i ^ j]
    _ = 0 := by simp [hroot]

/-- **Finite spectral rank law.**  A moment sequence supported on at most `d` spectral lines has
zero leading Hankel determinant in size `d + 1`. -/
theorem det_momentHankelMatrix_finiteSpectralMoment_succ_eq_zero
    {d : ℕ} (mass node : Fin d → ℝ) :
    (momentHankelMatrix (finiteSpectralMoment mass node) (d + 1)).det = 0 := by
  let p : Polynomial ℝ := ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))
  have hpmon : p.Monic := by
    exact Polynomial.monic_prod_of_monic _ _
      (fun i _ ↦ Polynomial.monic_X_sub_C (node i))
  have hpdeg : p.natDegree = d := by
    rw [show p = ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i)) by rfl,
      Polynomial.natDegree_prod_of_monic _ _
        (fun i _ ↦ Polynomial.monic_X_sub_C (node i))]
    simp
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (momentHankelMatrix_mulVec_nodePolynomial_eq_zero mass node)
    (i := Fin.last d)
  have hp1 : p.coeff d = 1 := by
    rw [← hpdeg]
    exact hpmon.coeff_natDegree
  simpa [p, hp1]

/-- The determinant obstruction in representation form. -/
theorem det_momentHankelMatrix_succ_eq_zero_of_spectralWidthAtMost
    {d : ℕ} {m : ℕ → ℝ} (hm : SpectralWidthAtMost d m) :
    (momentHankelMatrix m (d + 1)).det = 0 := by
  obtain ⟨mass, node, rfl⟩ := hm
  exact det_momentHankelMatrix_finiteSpectralMoment_succ_eq_zero mass node

/-- Fixed spectral width is closed under pointwise convergence.  Only the determinant conclusion,
which is the useful invariant for the present corpus, is asserted: the individual nodes and masses
need not converge. -/
theorem det_momentHankelMatrix_succ_eq_zero_of_fixedSpectralWidth_tendsto
    {d : ℕ} {m : ℕ → ℕ → ℝ} {target : ℕ → ℝ}
    (hm : ∀ j, SpectralWidthAtMost d (m j))
    (hconv : Tendsto m atTop (nhds target)) :
    (momentHankelMatrix target (d + 1)).det = 0 := by
  have hmatrix : Tendsto
      (fun j ↦ momentHankelMatrix (m j) (d + 1)) atTop
      (nhds (momentHankelMatrix target (d + 1))) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro c
    simpa [momentHankelMatrix] using
      (tendsto_pi_nhds.mp hconv) ((r : ℕ) + (c : ℕ))
  have hdet : Tendsto
      (fun j ↦ (momentHankelMatrix (m j) (d + 1)).det) atTop
      (nhds (momentHankelMatrix target (d + 1)).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix
  have hzero : Tendsto
      (fun j ↦ (momentHankelMatrix (m j) (d + 1)).det) atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    exact Filter.Eventually.of_forall fun j ↦
      (det_momentHankelMatrix_succ_eq_zero_of_spectralWidthAtMost (hm j)).symm
  exact tendsto_nhds_unique hdet hzero

/-- Uniformly bounded spectral width remains impossible even when each requested finite moment
block may use a different clock. -/
theorem det_momentHankelMatrix_succ_eq_zero_of_fixedSpectralWidthLocalClosure
    {d : ℕ} {target : ℕ → ℝ}
    (h : FixedSpectralWidthLocalClosure d target) :
    (momentHankelMatrix target (d + 1)).det = 0 := by
  have happ : ∀ j : ℕ, ∃ mass node : Fin d → ℝ,
      ∀ n : ℕ, n < j + 1 →
        dist (finiteSpectralMoment mass node n) (target n) < 1 / ((j : ℝ) + 1) := by
    intro j
    exact h (j + 1) (1 / ((j : ℝ) + 1)) (by positivity)
  choose mass node happrox using happ
  let approx : ℕ → ℕ → ℝ := fun j ↦ finiteSpectralMoment (mass j) (node j)
  have hwidth : ∀ j, SpectralWidthAtMost d (approx j) := by
    intro j
    exact ⟨mass j, node j, rfl⟩
  have hconv : Tendsto approx atTop (nhds target) := by
    apply tendsto_pi_nhds.mpr
    intro n
    rw [Metric.tendsto_atTop]
    intro ε hε
    have herr : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε)
    obtain ⟨J, hJ⟩ := eventually_atTop.mp herr
    refine ⟨max J n, fun j hj ↦ ?_⟩
    exact (happrox j n (by omega)).trans
      (hJ j (le_trans (le_max_left _ _) hj))
  exact det_momentHankelMatrix_succ_eq_zero_of_fixedSpectralWidth_tendsto hwidth hconv

/-- A single nonzero Hankel determinant rules out fixed-width local spectral approximation. -/
theorem not_fixedSpectralWidthLocalClosure_of_det_ne_zero
    {d : ℕ} {target : ℕ → ℝ}
    (hdet : (momentHankelMatrix target (d + 1)).det ≠ 0) :
    ¬ FixedSpectralWidthLocalClosure d target := by
  intro h
  exact hdet (det_momentHankelMatrix_succ_eq_zero_of_fixedSpectralWidthLocalClosure h)

/-- Every infinite-support moment clock escapes every uniformly bounded finite spectral model. -/
theorem not_fixedSpectralWidthLocalClosure_of_infiniteSupport
    {d : ℕ} {target : ℕ → ℝ} {mu : MeasureTheory.Measure ℝ}
    (hs : ∀ k, target k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hint : ∀ k, MeasureTheory.Integrable (fun x : ℝ ↦ (x : ℝ) ^ k) mu)
    (hmuinf : ∀ F : Finset ℝ, 0 < mu {x : ℝ | x ∉ F}) :
    ¬ FixedSpectralWidthLocalClosure d target := by
  apply not_fixedSpectralWidthLocalClosure_of_det_ne_zero
  exact ne_of_gt (det_momentHankelMatrix_pos_of_infiniteSupport target hs hint hmuinf (d + 1))

end

end HTGeometry
