import GaloisForLFunctions.HTGeometry.UniversalSpectralSemigroupWallCrossingLaw
import GaloisForLFunctions.RHTower.SteinhausModel

/-!
# Regularized CGC correlators and Filon assembly from arXiv:2608.18589

This module transfers the exact algebraic and Fourier identities used by the paper's oscillatory
quadrature scheme.  Its removable `exprel` factor is identified with the corpus's already-certified
exponential divided difference.  Local monomial moments and the global node-weight contraction are
then formalized without approximation assumptions.
-/

noncomputable section

open MeasureTheory
open scoped Interval BigOperators

namespace GaloisForLFunctions.HTGeometry

/-! ## The removable CGC `exprel` factor -/

/-- The paper's `exprel(z) = (exp z - 1) / z`, continuously filled by `exprel(0) = 1`. -/
abbrev cgcExprel : ℂ → ℂ := forwardWindowKernel

@[simp] theorem cgcExprel_zero : cgcExprel 0 = 1 :=
  forwardWindowKernel_zero

theorem cgcExprel_of_ne (z : {z : ℂ // z ≠ 0}) :
    cgcExprel z = (Complex.exp z - 1) / z :=
  forwardWindowKernel_of_ne z.property

theorem continuous_cgcExprel : Continuous cgcExprel :=
  continuous_forwardWindowKernel

/-- Corpus application: `exprel` is exactly the normalized finite-time average of one exponential
spectral mode.  Thus the CGC pole regularization is also a semigroup observation kernel. -/
theorem cgcExprel_eq_forwardModeAverage (T : Set.Ioi (0 : ℝ)) (mode : ℂ) :
    cgcExprel (((T : ℝ) : ℂ) * mode) = forwardModeAverage T mode := by
  exact (forwardModeAverage_eq_kernel T mode (ne_of_gt T.property)).symm

/-- Regularized four-line correlator factor from equation (11), with spectator dipole factors. -/
def cgcRegularizedFourLine (N S S' D : ℂ) : ℂ :=
  -(N * S * S') * cgcExprel (-D)

/-- At the apparent pole `D = 0`, the correlator has the finite value `-N S S'`. -/
@[simp] theorem cgcRegularizedFourLine_zero (N S S' : ℂ) :
    cgcRegularizedFourLine N S S' 0 = -(N * S * S') := by
  simp [cgcRegularizedFourLine]

/-- Pole-cleared form of the regularized correlator, valid at and away from `D = 0`. -/
theorem cgcRegularizedFourLine_cleared (N S S' D : ℂ) :
    D * cgcRegularizedFourLine N S S' D =
      -(N * S * S') * (1 - Complex.exp (-D)) := by
  by_cases hD : D = 0
  · subst D
    simp
  · rw [cgcRegularizedFourLine, cgcExprel_of_ne ⟨-D, neg_ne_zero.mpr hD⟩]
    field_simp
    ring

/-- On the punctured plane, regularization agrees with the paper's quotient formula. -/
theorem cgcRegularizedFourLine_of_ne (N S S' : ℂ) (D : {D : ℂ // D ≠ 0}) :
    cgcRegularizedFourLine N S S' D =
      -(N * S * S') * (1 - Complex.exp (-D)) / D := by
  rw [cgcRegularizedFourLine, cgcExprel_of_ne ⟨-D, neg_ne_zero.mpr D.property⟩]
  field_simp [D.property]
  ring

/-! ## Exact angular selection -/

/-- Integral of one integer angular character over a full turn. -/
theorem cgcAngularCharacter_integral (k : ℤ) :
    (∫ theta : ℝ in 0..2 * Real.pi,
      Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))) =
        if k = 0 then (2 * Real.pi : ℝ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [if_neg hk, integral_exp_mul_complex]
    · have h1 : ((k : ℂ) * Complex.I) * (((2 * Real.pi : ℝ)) : ℂ) =
          (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
      have h0 : ((k : ℂ) * Complex.I) * (((0 : ℝ)) : ℂ) = 0 := by norm_num
      rw [h1, h0, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_zero, sub_self,
        zero_div]
      norm_num
    · exact mul_ne_zero (Int.cast_ne_zero.mpr hk) Complex.I_ne_zero

/-- The angular integral in equation (14) keeps precisely the coupled mode `m = -ell`. -/
theorem cgcAngularModeSelection (m ell : ℤ) :
    (∫ theta : ℝ in 0..2 * Real.pi,
      Complex.exp ((((m + ell : ℤ) : ℂ) * Complex.I) * (theta : ℂ))) =
        if m = -ell then (2 * Real.pi : ℝ) else 0 := by
  rw [cgcAngularCharacter_integral]
  by_cases h : m = -ell
  · simp [h]
  · have hsum : m + ell ≠ 0 := by omega
    simp [h, hsum]

/-- Pairing opposite integer Fourier modes gives the real cosine kernel used to halve the paper's
angular transform work. -/
theorem cgcOppositeAngularModes_eq_two_cos (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) + Complex.exp ((-x : ℂ) * Complex.I) =
      2 * (Real.cos x : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Finite paired-mode form of equation (16): after identifying opposite Fourier coefficients,
the complex angular sum is exactly a real cosine sum. -/
theorem cgcPairedAngularSum_eq_cosine
    (M : ℕ) (mode : ℕ → ℂ) (theta : ℝ) :
    mode 0 + ∑ m ∈ Finset.range M,
        (-1 : ℂ) ^ (m + 1) *
          (Complex.exp (((((m + 1 : ℕ) : ℝ) * theta : ℝ) : ℂ) * Complex.I) +
            Complex.exp ((-(((m + 1 : ℕ) : ℝ) * theta : ℝ) : ℂ) * Complex.I)) *
          mode (m + 1) =
      mode 0 + 2 * ∑ m ∈ Finset.range M,
        (-1 : ℂ) ^ (m + 1) * (Real.cos (((m + 1 : ℕ) : ℝ) * theta) : ℂ) *
          mode (m + 1) := by
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [cgcOppositeAngularModes_eq_two_cos]
  ring

/-! ## Filon local moments and global contraction -/

/-- Equation (18): exact nonoscillatory monomial moment on a local interval. -/
theorem filonLocalMonomialMoment (h : ℝ) (r : ℕ) :
    (∫ u : ℝ in 0..h, u ^ r) = h ^ (r + 1) / (r + 1) := by
  rw [integral_pow]
  simp

/-- Precomputed coefficient multiplying one global node value after all interval moments are
contracted, corresponding to equations (29)--(30). -/
def filonNodeWeight {I R J : Type*} [Fintype I] [Fintype R]
    (interpolationWeight : I → R → J → ℂ) (moment : I → R → ℂ) (j : J) : ℂ :=
  ∑ i, ∑ r, interpolationWeight i r j * moment i r

/-- Interval-first presentation of the same assembled Filon functional. -/
def filonIntervalAssembly {I R J : Type*} [Fintype I] [Fintype R] [Fintype J]
    (interpolationWeight : I → R → J → ℂ) (moment : I → R → ℂ)
    (sample : J → ℂ) : ℂ :=
  ∑ i, ∑ r, (∑ j, interpolationWeight i r j * sample j) * moment i r

/-- Exact regrouping behind precomputed Filon weights: every interval/local-polynomial contraction
can be performed once at the nodes, independently of later field samples. -/
theorem filonIntervalAssembly_eq_nodeContraction
    {I R J : Type*} [Fintype I] [Fintype R] [Fintype J]
    (interpolationWeight : I → R → J → ℂ) (moment : I → R → ℂ)
    (sample : J → ℂ) :
    filonIntervalAssembly interpolationWeight moment sample =
      ∑ j, filonNodeWeight interpolationWeight moment j * sample j := by
  rw [filonIntervalAssembly]
  simp_rw [Finset.sum_mul]
  calc
    (∑ i, ∑ r, ∑ j, interpolationWeight i r j * sample j * moment i r) =
        ∑ i, ∑ j, ∑ r, interpolationWeight i r j * sample j * moment i r := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, ∑ r, interpolationWeight i r j * sample j * moment i r := by
      rw [Finset.sum_comm]
    _ = ∑ j, filonNodeWeight interpolationWeight moment j * sample j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [filonNodeWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring

end GaloisForLFunctions.HTGeometry
