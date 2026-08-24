import GaloisForLFunctions.RHTower.PositiveDiagonalCompletionCriticalBoundaryDichotomy
import GaloisForLFunctions.RHTower.PositiveDiagonalCompletionEdge

namespace RHTower

open Matrix Complex
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder

noncomputable section

/-- Positive-semidefinite kernel: every injectively indexed finite section is
positive semidefinite. -/
def PositiveSemidefiniteKernel (K : Matrix ℕ ℕ ℂ) : Prop :=
  ∀ (m : ℕ) (e : Fin m → ℕ), Function.Injective e →
    (K.submatrix e e).PosSemidef

/-- Diagonal completion of an infinite arithmetic kernel. -/
def positiveDiagonalCompletedKernel (W : Matrix ℕ ℕ ℂ) (d : ℕ → ℝ) :
    Matrix ℕ ℕ ℂ := W + Matrix.diagonal (fun n => (d n : ℂ))

/-- A nonzero coprime-supported Hermitian kernel together with a positive
diagonal repair and finite critical Dirichlet energy. -/
structure PositiveDiagonalCoprimeKernelRepair where
  W : Matrix ℕ ℕ ℂ
  d : ℕ → ℝ
  hermitian : W.IsHermitian
  coprimeSupport : ∀ a b : ℕ, W a b ≠ 0 →
    1 < a ∧ 1 < b ∧ Nat.Coprime a b
  nonzeroEdge : {p : ℕ × ℕ // W p.1 p.2 ≠ 0}
  completedPSD : PositiveSemidefiniteKernel (positiveDiagonalCompletedKernel W d)
  criticalSummable : Summable (gdTwistTerm
    (fun n : positiveDirichletCoordinate => d n.1)
    positiveDirichletLogFrequency 1 0)

namespace PositiveDiagonalCoprimeKernelRepair

variable (R : PositiveDiagonalCoprimeKernelRepair)

/-- Coprime support above one forces zero diagonal. -/
theorem diagonal_zero (n : ℕ) : R.W n n = 0 := by
  by_contra hne
  have hs := R.coprimeSupport n n hne
  have hn : n = 1 := (Nat.coprime_self n).mp hs.2.2
  omega

/-- Every correcting diagonal coefficient is nonnegative. -/
theorem d_nonneg (n : ℕ) : 0 ≤ R.d n := by
  let e : Fin 1 → ℕ := fun _ => n
  have he : Function.Injective e := fun _ _ _ => Subsingleton.elim _ _
  have hpsd := R.completedPSD 1 e he
  have hdiag := hpsd.diag_nonneg (i := (0 : Fin 1))
  have hdiagC : (0 : ℂ) ≤ (R.d n : ℂ) := by
    simpa [positiveDiagonalCompletedKernel, e, Matrix.diagonal_apply,
      R.diagonal_zero n] using hdiag
  exact (Complex.nonneg_iff.mp hdiagC).1

/-- The selected nonzero coprime edge forces a strictly positive correction
coefficient at an integer greater than one. -/
def positiveAtom : {n : ℕ // 1 < n ∧ 0 < R.d n} := by
  let a := R.nonzeroEdge.1.1
  let b := R.nonzeroEdge.1.2
  have hWab : R.W a b ≠ 0 := R.nonzeroEdge.2
  have hs := R.coprimeSupport a b hWab
  have hab : a ≠ b := by
    intro hab
    have hc : Nat.Coprime a a := by simpa [hab] using hs.2.2
    have haone : a = 1 := (Nat.coprime_self a).mp hc
    omega
  let e : Fin 2 → ℕ := ![a, b]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [e]
  let W2 : Matrix (Fin 2) (Fin 2) ℂ := R.W.submatrix e e
  let d2 : Fin 2 → ℝ := fun i => R.d (e i)
  have hW2 : W2.IsHermitian := R.hermitian.submatrix e
  have hpsd2 : (W2 + Matrix.diagonal (fun i => (d2 i : ℂ))).PosSemidef := by
    have hraw := R.completedPSD 2 e he
    have hmatrix :
        (positiveDiagonalCompletedKernel R.W R.d).submatrix e e =
          W2 + Matrix.diagonal (fun i => (d2 i : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [positiveDiagonalCompletedKernel, W2, d2]
      · have heij : e i ≠ e j := fun h => hij (he h)
        simp [positiveDiagonalCompletedKernel, W2, d2, hij, heij]
    rw [hmatrix] at hraw
    exact hraw
  have hstrict := positiveDiagonalCompletion_edge_strict W2 d2 hW2
    (0 : Fin 2) (1 : Fin 2) (by decide)
    (by simp [W2, e, R.diagonal_zero])
    (by simp [W2, e, R.diagonal_zero])
    (by simpa [W2, e] using hWab) hpsd2
  exact ⟨a, hs.1, by simpa [d2, e] using hstrict.1⟩

/-- Positive Dirichlet datum canonically forced by the repaired kernel. -/
def dirichletData : PositiveDiagonalCompletionDirichletData 1 where
  coeff := R.d
  coeff_nonneg := fun n _ => R.d_nonneg n
  summable_at := R.criticalSummable
  positiveAtom := R.positiveAtom

/-- Exact unconditional incompatibility: a finite-critical-energy positive
diagonal repair is either nonanalytic at the critical boundary, or all its
reflected critical even jets are the strictly positive logarithmic moments. -/
theorem criticalBoundary_dichotomy :
    (¬ AnalyticAt ℂ R.dirichletData.series (1 : ℂ)) ∨
      ((∀ k : ℕ, Summable (gdTwistTerm R.dirichletData.positiveCoeff
          positiveDirichletLogFrequency 1 k)) ∧
        ∀ (z : PositiveDiagonalCriticalLinePoint) (m : ℕ),
          mixedAddIteratedDeriv m m R.dirichletData.series z.1 (star z.1) =
              ((gdMoment R.dirichletData.positiveCoeff positiveDirichletLogFrequency
                1 (2 * m) : ℝ) : ℂ) ∧
            0 < (mixedAddIteratedDeriv m m R.dirichletData.series
              z.1 (star z.1)).re) :=
  positiveDiagonal_criticalBoundary_dichotomy R.dirichletData

end PositiveDiagonalCoprimeKernelRepair

end

end RHTower
