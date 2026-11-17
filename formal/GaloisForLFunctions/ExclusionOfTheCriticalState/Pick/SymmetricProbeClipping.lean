import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheConfinedPickMatricesCountTheZerosRightOfTheLine
import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingProjection
import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingInertia
import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingRestoration

/-!
# Optimal bounded approximations of the actual Weil probe matrices

Two-sided spectral clipping applies to every admissible finite probe family,
without positivity of the Weil form. The arithmetic kernel gives an explicit
square budget; higher spectral moments control the discarded tails. Among
Hermitian matrices with the same two-sided cap, the clipped probe matrix
minimizes Frobenius error.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HilbertMetric.SymmetricClipping
open HTGeometry
noncomputable section

private theorem admissibleProbe_hermitian {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    (probeGram fun i => (p i).val).IsHermitian :=
  probeGram_isHermitian fun i => by linarith only [(p i).property]

/-- Clip both tails of the actual arithmetic probe matrix. -/
def clippedWeilProbe {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) :
    Matrix (Fin N) (Fin N) ℂ := matrix (admissibleProbe_hermitian p) c

/-- Spectral coefficient change restoring the original Weil form after positive clipping. -/
def weilProbeRestorer {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) :
    Matrix (Fin N) (Fin N) ℂ := restoreMatrix (admissibleProbe_hermitian p) c

/-- The regularized Weil matrix obeys both spectral caps unconditionally. -/
theorem clippedWeilProbe_bounds {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) :
    (((c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - clippedWeilProbe p c).PosSemidef ∧
      (clippedWeilProbe p c - ((-(c : ℝ)) : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef :=
  matrix_bounds (admissibleProbe_hermitian p) c

/-- The actual arithmetic symbol computes the full probe square energy. -/
theorem weilProbe_frobSq_arithmetic {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    frobSq (probeGram fun i => (p i).val) =
      ∑ i, ∑ j, ((probeSymbol (p i).val + probeSymbol (p j).val) /
        ((p i).val + (p j).val)) ^ 2 := by
  rw [frobSq, (admissibleProbe_hermitian p).eq]
  change (trace ((probeGram fun i => (p i).val) *
    (probeGram fun i => (p i).val))).re = _
  rw [HilbertMetric.Clipped.trace_square (admissibleProbe_hermitian p)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [probeGram, bareMixedEnergy_probe (by linarith only [(p i).property])
    (by linarith only [(p j).property])]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, pow_two]

/-- Every higher moment of the actual probe matrix bounds its clipping error. -/
theorem clippedWeilProbe_error_moment {N : ℕ}
    (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) (n : ℕ) :
    (c : ℝ) ^ n * frobSq ((probeGram fun i => (p i).val) - clippedWeilProbe p c) ≤
      HilbertMetric.Clipped.spectralSum (fun x => |x| ^ (n + 2))
        (probeGram fun i => (p i).val) :=
  error_moment (admissibleProbe_hermitian p) c n

/-- The regularized probe matrix retains at most the explicit arithmetic square budget. -/
theorem clippedWeilProbe_arithmetic_budget {N : ℕ}
    (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) :
    frobSq (clippedWeilProbe p c) ≤
      ∑ i, ∑ j, ((probeSymbol (p i).val + probeSymbol (p j).val) /
        ((p i).val + (p j).val)) ^ 2 := by
  rw [← weilProbe_frobSq_arithmetic p]
  exact matrix_frobSq_le (admissibleProbe_hermitian p) c

/-- A competing bounded probe approximation pays its distance from the spectral clip. -/
theorem clippedWeilProbe_pythagorean {N : ℕ}
    (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) (B : Matrix (Fin N) (Fin N) ℂ)
    (hB : B.IsHermitian)
    (hupper : (((c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - B).PosSemidef)
    (hlower : (B - ((-(c : ℝ)) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) :
    frobSq ((probeGram fun i => (p i).val) - clippedWeilProbe p c) +
      frobSq (B - clippedWeilProbe p c) ≤ frobSq ((probeGram fun i => (p i).val) - B) :=
  matrix_pythagorean (admissibleProbe_hermitian p) hB c hupper hlower

/-- Clipping cannot amplify the matrix change caused by moving any probe nodes. -/
theorem clippedWeilProbe_stable {N : ℕ}
    (p q : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) :
    frobSq (clippedWeilProbe p c - clippedWeilProbe q c) ≤
      ∑ i, ∑ j,
        (((probeSymbol (p i).val + probeSymbol (p j).val) / ((p i).val + (p j).val)) -
          ((probeSymbol (q i).val + probeSymbol (q j).val) / ((q i).val + (q j).val))) ^ 2 := by
  have h := matrix_nonexpansive (admissibleProbe_hermitian p) (admissibleProbe_hermitian q) c
  refine h.trans_eq ?_
  rw [frobSq, ((admissibleProbe_hermitian p).sub (admissibleProbe_hermitian q)).eq]
  change (trace (((probeGram fun i => (p i).val) - (probeGram fun i => (q i).val)) *
    ((probeGram fun i => (p i).val) - (probeGram fun i => (q i).val)))).re = _
  rw [HilbertMetric.Clipped.trace_square
    ((admissibleProbe_hermitian p).sub (admissibleProbe_hermitian q))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply, probeGram]
  rw [bareMixedEnergy_probe (by linarith only [(p i).property])
    (by linarith only [(p j).property]),
    bareMixedEnergy_probe (by linarith only [(q i).property])
      (by linarith only [(q j).property]), ← Complex.ofReal_sub]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, pow_two]

/-- Bounded regularization preserves every negative Weil direction and every null mode. -/
theorem clippedWeilProbe_inertia {N : ℕ}
    (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) :
    hermPosIndex (clippedWeilProbe p (c + 1)) = hermPosIndex (probeGram fun i => (p i).val) ∧
      hermNegIndex (clippedWeilProbe p (c + 1)) = hermNegIndex (probeGram fun i => (p i).val) ∧
      hermNullIndex (clippedWeilProbe p (c + 1)) =
        hermNullIndex (probeGram fun i => (p i).val) :=
  matrix_inertia (admissibleProbe_hermitian p) (c + 1) (by positivity)

/-- Every exact arithmetic null vector survives bounded spectral regularization. -/
theorem clippedWeilProbe_kernel {N : ℕ}
    (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) :
    LinearMap.ker (clippedWeilProbe p (c + 1)).mulVecLin =
      LinearMap.ker (probeGram fun i => (p i).val).mulVecLin :=
  matrix_kernel (admissibleProbe_hermitian p) (c + 1) (by positivity)

/-- Explicit spectral rescaling recovers every original signed Weil quadratic value. -/
theorem clippedWeilProbe_quadratic_transport {N : ℕ}
    (p : Fin N → {x : ℝ // 1 ≤ x}) (c : ℝ≥0) (v : Fin N → ℂ) :
    hermQuad (clippedWeilProbe p (c + 1))
        (weilProbeRestorer p (c + 1) *ᵥ v) =
      hermQuad (probeGram fun i => (p i).val) v :=
  matrix_quadratic_transport (admissibleProbe_hermitian p) (c + 1) (by positivity) v

#print axioms clippedWeilProbe_bounds
#print axioms weilProbe_frobSq_arithmetic
#print axioms clippedWeilProbe_error_moment
#print axioms clippedWeilProbe_arithmetic_budget
#print axioms clippedWeilProbe_pythagorean
#print axioms clippedWeilProbe_stable
#print axioms clippedWeilProbe_inertia
#print axioms clippedWeilProbe_kernel
#print axioms clippedWeilProbe_quadratic_transport

end
end GaloisForLFunctions.ExclusionOfTheCriticalState
