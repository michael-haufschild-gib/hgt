import GaloisForLFunctions.RHTower.RestrictedProjectionCubicTrace
import GaloisForLFunctions.RHTower.HilbertSchmidtTraceObstruction
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace

/-!
# Minimality of the cubic Schatten grade

This module formalizes RUCRI-B.  A concrete harmonic diagonal proves that Hilbert--Schmidt
membership does not make the linear grade trace class.  The square is always trace class but is
even under orientation reversal.  The cube is always trace class, is odd, and a rank-one
projection pair gives cubic trace one.  Thus degree three is the first polynomial grade at the
critical `S₂` boundary that simultaneously supports an ordinary trace and orientation.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap InnerProductSpace

/-- Concrete critical Hilbert carrier for the non-nuclear linear-grade witness. -/
abbrev RUCRICriticalHilbert := lp (fun _ : ℕ => ℂ) 2

/-- Harmonic diagonal operator: Hilbert--Schmidt but not Schatten one. -/
def rucriHarmonicDiagonalOperator : RUCRICriticalHilbert →L[ℂ] RUCRICriticalHilbert :=
  HilbertSchmidt.toOperator harmonicDiagonalHSKernel_isHS

theorem rucriHarmonicDiagonalOperator_isHilbertSchmidt :
    rucriHarmonicDiagonalOperator.IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator harmonicDiagonalHSKernel_isHS

theorem rucriHarmonicDiagonalOperator_basis (n : ℕ) :
    rucriHarmonicDiagonalOperator (HilbertSchmidt.lpBasis ℕ n) =
      harmonicDiagonalHSKernel (n, n) • HilbertSchmidt.lpBasis ℕ n := by
  apply lp.ext
  funext j
  rw [rucriHarmonicDiagonalOperator, HilbertSchmidt.lpBasis_apply,
    HilbertSchmidt.toOperator_single harmonicDiagonalHSKernel_isHS]
  change harmonicDiagonalHSKernel (j, n) =
    harmonicDiagonalHSKernel (n, n) * (lp.single 2 n 1 : RUCRICriticalHilbert) j
  by_cases hj : j = n
  · subst j
    simp
  · simp [harmonicDiagonalHSKernel, hj]

theorem rucriHarmonicDiagonalOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 rucriHarmonicDiagonalOperator := by
  intro htrace
  have hdiag := htrace.one_summable_inner_diag_basis (HilbertSchmidt.lpBasis ℕ)
  have hcomplex : Summable (fun n : ℕ => harmonicDiagonalHSKernel (n, n)) := by
    apply hdiag.congr
    intro n
    rw [rucriHarmonicDiagonalOperator_basis, inner_smul_right]
    have hnorm := (HilbertSchmidt.lpBasis ℕ).orthonormal.1 n
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  exact not_summable_harmonicDiagonalHSKernel_diagonal hcomplex

/-- Closed conjunction expressing all three polynomial-grade tests in RUCRI-B. -/
def RestrictedProjectionCubicMinimalityStatement : Prop :=
  (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (A : H →L[ℂ] H),
      A.IsHilbertSchmidt ∧ ¬ MemSchattenClass 1 A) ∧
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      A.IsHilbertSchmidt → MemSchattenClass 1 (A ^ 2)) ∧
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      (-A) ^ 2 = A ^ 2) ∧
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      A.IsHilbertSchmidt → MemSchattenClass 1 (A ^ 3)) ∧
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      (-A) ^ 3 = -(A ^ 3)) ∧
  (∃ (R P : ℂ →L[ℂ] ℂ),
      R.IsHilbertSchmidt ∧ P.IsHilbertSchmidt ∧
      ContinuousLinearMap.opTrace (restrictedProjectionCubicDefect R P) = 1)

/-- RUCRI-B: cubic degree is minimal for nuclearity, oddness, and nonzero integral charge at the
Hilbert--Schmidt boundary. -/
theorem restrictedProjectionCubicMinimality_closed :
    RestrictedProjectionCubicMinimalityStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨RUCRICriticalHilbert, inferInstance, inferInstance,
      inferInstance, rucriHarmonicDiagonalOperator,
      rucriHarmonicDiagonalOperator_isHilbertSchmidt,
      rucriHarmonicDiagonalOperator_not_memSchattenClass_one⟩
  · intro H _ _ _ A hA
    have hrect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hA hA
    simpa [pow_two, ContinuousLinearMap.mul_def] using
      (memRectSchattenClass_iff_memSchattenClass 1 (A ∘L A)).mp hrect
  · intro H _ _ _ A
    noncomm_ring
  · intro H _ _ _ A hA
    have hsqRect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hA hA
    have hsq : MemSchattenClass 1 (A ∘L A) :=
      (memRectSchattenClass_iff_memSchattenClass 1 (A ∘L A)).mp hsqRect
    have hcube := memSchattenClass_one_comp_right hsq A
    simpa [pow_succ, ContinuousLinearMap.mul_def] using hcube
  · intro H _ _ _ A
    noncomm_ring
  · let R : ℂ →L[ℂ] ℂ := rankOne ℂ (1 : ℂ) (1 : ℂ)
    let P : ℂ →L[ℂ] ℂ := 0
    have hRHS : R.IsHilbertSchmidt := by
      simpa [R] using
        (GaloisForLFunctions.HTGeometry.isHilbertSchmidt_rankOne
          (1 : ℂ) (1 : ℂ))
    have hPHS : P.IsHilbertSchmidt := by
      simpa [P] using
        (ContinuousLinearMap.isHilbertSchmidt_zero (E := ℂ) (F := ℂ))
    refine ⟨R, P, hRHS, hPHS, ?_⟩
    have hRmul : R * R = R := by
      apply ContinuousLinearMap.ext
      intro z
      simp [R]
    have hcubic : restrictedProjectionCubicDefect R P = R := by
      simp [restrictedProjectionCubicDefect, restrictedProjectionDisplacement, P,
        pow_succ, hRmul]
    rw [hcubic]
    simpa [R] using
      (GaloisForLFunctions.HTGeometry.opTrace_rankOne (H := ℂ)
        (1 : ℂ) (1 : ℂ))

end RHTower
