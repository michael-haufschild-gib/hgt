import GaloisForLFunctions.HTGeometry.FiniteMatrixCyclicReaderRigidity
import GaloisForLFunctions.RHTower.VonMangoldtBivariateMarginalTraceLock

/-!
# Von Mangoldt cyclic-reader opening-flux no-go

`SR-43` excludes ordinary coordinate partial trace as a bivariate prime--jet connector, but leaves
an apparent finite-level escape: replace ordinary trace by a weighted cyclic reader.

That escape does not exist on a finite full matrix source algebra.  Cyclic-reader rigidity forces
every such reader to be a scalar ordinary trace.  If consecutive jet readers agree on one
normalized matrix corner, their values on the actual Suzuki principal-relative jet current differ
by exactly the positive von-Mangoldt opening flux.

No positivity of matrices, RH premise, Xi zero, estimate, or computation is used.
-/

open scoped BigOperators Matrix

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- **Exact cyclic-reader opening law.**  Inclusion-compatible cyclic readers on consecutive full
jet matrix algebras must carry the actual positive Suzuki jet-opening flux. -/
theorem finiteVonMangoldtSuccessor_cyclicReader_opening_eq
    (M N : ℕ)
    (Φ0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ →ₗ[ℝ] ℝ)
    (Φ1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ →ₗ[ℝ] ℝ)
    (hcyc0 : HTGeometry.MatrixCyclicReader Φ0)
    (hcyc1 : HTGeometry.MatrixCyclicReader Φ1)
    (hcorner :
      Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) =
        Φ1 (Matrix.single (0 : Fin (N + 2)) 0 1)) :
    Φ1 (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 2)) -
        Φ0 (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) =
      Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) *
        finiteVonMangoldtSuccessorRelativeMoment M (2 * (N + 1) + 2) := by
  rw [HTGeometry.matrixCyclicReader_apply_eq_corner_mul_trace
      Φ0 hcyc0 (0 : Fin (N + 1)),
    HTGeometry.matrixCyclicReader_apply_eq_corner_mul_trace
      Φ1 hcyc1 (0 : Fin (N + 2)), ← hcorner]
  have htrace :
      Matrix.trace
          (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 2)) =
        Matrix.trace
            (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) +
          finiteVonMangoldtSuccessorRelativeMoment M (2 * (N + 1) + 2) := by
    simpa only [Nat.add_assoc] using
      trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_succ M (N + 1)
  rw [htrace]
  ring

/-- Positive normalization makes every consecutive cyclic-reader value strictly increase. -/
theorem finiteVonMangoldtSuccessor_cyclicReader_strictMono
    (M N : ℕ) (hM : 0 < M)
    (Φ0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ →ₗ[ℝ] ℝ)
    (Φ1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ →ₗ[ℝ] ℝ)
    (hcyc0 : HTGeometry.MatrixCyclicReader Φ0)
    (hcyc1 : HTGeometry.MatrixCyclicReader Φ1)
    (hpositive : 0 < Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1))
    (hcorner :
      Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) =
        Φ1 (Matrix.single (0 : Fin (N + 2)) 0 1)) :
    Φ0 (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) <
      Φ1 (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 2)) := by
  have hopen :=
    finiteVonMangoldtSuccessor_cyclicReader_opening_eq
      M N Φ0 Φ1 hcyc0 hcyc1 hcorner
  have hflux :
      0 < finiteVonMangoldtSuccessorRelativeMoment M (2 * (N + 1) + 2) :=
    finiteVonMangoldtSuccessorRelativeMoment_pos M _ hM (by omega)
  nlinarith [mul_pos hpositive hflux]

/-- **Weighted cyclic-reader no-go.**  No positively normalized, inclusion-compatible cyclic
reader family can assign one fixed source value to two consecutive actual Suzuki jet sections. -/
theorem not_exists_fixedValue_inclusionCompatible_cyclicReaders_finiteVonMangoldtSuccessor
    (M N : ℕ) (hM : 0 < M) :
    ¬ ∃ (Φ0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ →ₗ[ℝ] ℝ)
        (Φ1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ →ₗ[ℝ] ℝ),
      HTGeometry.MatrixCyclicReader Φ0 ∧
      HTGeometry.MatrixCyclicReader Φ1 ∧
      0 < Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) ∧
      Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) =
        Φ1 (Matrix.single (0 : Fin (N + 2)) 0 1) ∧
      Φ0 (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) =
        Φ1 (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 2)) := by
  rintro ⟨Φ0, Φ1, hcyc0, hcyc1, hpositive, hcorner, hfixed⟩
  have hlt :=
    finiteVonMangoldtSuccessor_cyclicReader_strictMono
      M N hM Φ0 Φ1 hcyc0 hcyc1 hpositive hcorner
  exact hlt.ne hfixed

end

end RHTower
