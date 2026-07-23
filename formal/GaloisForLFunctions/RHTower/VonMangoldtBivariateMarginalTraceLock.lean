import GaloisForLFunctions.HTGeometry.BivariateMarginalTraceLock
import GaloisForLFunctions.RHTower.GammaOddJacobiCoherentCapacity
import GaloisForLFunctions.RHTower.VonMangoldtSuccessorPrincipalRelativeHankel

/-!
# Von Mangoldt bivariate marginal trace-lock no-go

The standard bivariate realization of a prime--jet kernel takes coordinate partial traces to
recover its jet and prime marginals. The universal marginal trace lock forces those two marginals
to have equal trace.

For the actual finite von Mangoldt successor principal-relative current, adding one jet coordinate
strictly increases trace. Therefore no fixed prime marginal can coexist with consecutive jet
sections through ordinary coordinate partial traces. This excludes arbitrary real bivariate
kernels: positivity, Hermitian symmetry, finite Krein index, inclusion compatibility, and the
choice of mixed block are not assumptions.
-/

open scoped BigOperators Matrix

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Every positive-order successor logarithmic difference is nonnegative on the source range. -/
theorem vonMangoldtAdditiveLogJetDifference_nonneg
    (q n : ℕ) (hn : 1 ≤ n) :
    0 ≤ vonMangoldtAdditiveLogJetDifference q n := by
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  apply sub_nonneg.mpr
  have hlogle : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by positivity : (0 : ℝ) < n)
      (by positivity : (0 : ℝ) < n + 1)
      (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one] using
    pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hn)) hlogle q

/-- The actual edge `2 -> 3` has strictly positive logarithmic difference at every positive
order. -/
theorem vonMangoldtAdditiveLogJetDifference_two_pos
    (q : ℕ) (hq : 0 < q) :
    0 < vonMangoldtAdditiveLogJetDifference q 2 := by
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  apply sub_pos.mpr
  exact pow_lt_pow_left₀
    (Real.strictMonoOn_log
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (3 : ℝ) ∈ Set.Ioi 0)
      (by norm_num))
    (Real.log_pos (by norm_num)).le
    hq.ne'

/-- Every positive-order source-relative summand is nonnegative. -/
theorem vonMangoldtSuccessorRelativeMomentTerm_nonneg
    (q n : ℕ) (hn : 1 ≤ n) :
    0 ≤ vonMangoldtSuccessorRelativeMomentTerm q n := by
  exact mul_nonneg (finiteVonMangoldtRealWeight_nonneg n)
    (vonMangoldtAdditiveLogJetDifference_nonneg q n hn)

/-- The actual von Mangoldt atom `2` is a strict source-relative summand at every positive
order. -/
theorem vonMangoldtSuccessorRelativeMomentTerm_two_pos
    (q : ℕ) (hq : 0 < q) :
    0 < vonMangoldtSuccessorRelativeMomentTerm q 2 := by
  exact mul_pos finiteVonMangoldtRealWeight_two_pos
    (vonMangoldtAdditiveLogJetDifference_two_pos q hq)

/-- Every nonempty finite aperture has a strictly positive source-relative moment at every
positive order. -/
theorem finiteVonMangoldtSuccessorRelativeMoment_pos
    (M q : ℕ) (hM : 0 < M) (hq : 0 < q) :
    0 < finiteVonMangoldtSuccessorRelativeMoment M q := by
  unfold finiteVonMangoldtSuccessorRelativeMoment
  apply Finset.sum_pos'
  · intro p hp
    exact vonMangoldtSuccessorRelativeMomentTerm_nonneg q ((p : ℕ) + 2) (by omega)
  · let p0 : Fin M := ⟨0, hM⟩
    refine ⟨p0, Finset.mem_univ p0, ?_⟩
    simpa [p0] using vonMangoldtSuccessorRelativeMomentTerm_two_pos q hq

/-- Exact trace-flux law: adding jet coordinate `N` adds precisely the positive-order relative
moment `rho_M(2N+2)`. -/
theorem trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_succ
    (M N : ℕ) :
    Matrix.trace
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) =
      Matrix.trace
          (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N) +
        finiteVonMangoldtSuccessorRelativeMoment M (2 * N + 2) := by
  unfold Matrix.trace
  rw [Fin.sum_univ_castSucc]
  congr 1
  change finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)
      (Fin.last N) (Fin.last N) =
    finiteVonMangoldtSuccessorRelativeMoment M (2 * N + 2)
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply]
  congr 1
  simp only [Fin.val_last]
  omega

/-- The trace of the actual finite principal-relative current is strictly increasing in jet
aperture whenever the source aperture is nonempty. -/
theorem trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_strictMono
    (M N : ℕ) (hM : 0 < M) :
    Matrix.trace (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N) <
      Matrix.trace
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) := by
  rw [trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_succ]
  exact lt_add_of_pos_right _
    (finiteVonMangoldtSuccessorRelativeMoment_pos M (2 * N + 2) hM (by omega))

/-- **Von Mangoldt bivariate marginal trace-lock no-go.** At a nonempty source aperture, no fixed
finite source marginal can coexist with two consecutive principal-relative jet marginals through
ordinary coordinate partial traces.

The source marginal `B` is arbitrary. Hence this applies in particular to every fixed finite
restriction of the coherent odd Gamma--Jacobi residual. -/
theorem not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessor
    {P : Type*} [Fintype P]
    (M N : ℕ) (hM : 0 < M) (B : Matrix P P ℝ) :
    ¬ ((∃ C : Matrix (P × Fin N) (P × Fin N) ℝ,
          HTGeometry.bivariateJetMarginal C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N ∧
          HTGeometry.bivariateSourceMarginal C = B) ∧
        (∃ C : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ,
          HTGeometry.bivariateJetMarginal C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1) ∧
          HTGeometry.bivariateSourceMarginal C = B)) := by
  rintro ⟨⟨C0, hJ0, hP0⟩, ⟨C1, hJ1, hP1⟩⟩
  have htrace0 :=
    HTGeometry.trace_bivariateJetMarginal_eq_trace_bivariateSourceMarginal C0
  have htrace1 :=
    HTGeometry.trace_bivariateJetMarginal_eq_trace_bivariateSourceMarginal C1
  rw [hJ0, hP0] at htrace0
  rw [hJ1, hP1] at htrace1
  have hlt :=
    trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_strictMono M N hM
  linarith

/-- Finite pullback of the actual coherent odd Gamma--Jacobi residual to an arbitrary source
packet. -/
def finiteGammaOddJacobiCoherentResidualMatrix
    {P : Type*} [Fintype P] (prime : P → Nat.Primes) : Matrix P P ℝ :=
  fun p q => gammaOddJacobiPrimeCoherentResidualKernel (prime p) (prime q)

/-- **Exact `SR-40`/`SR-38` partial-trace incompatibility.** No two consecutive finite
principal-relative jet sections can share the actual coherent odd Gamma--Jacobi source marginal
through coordinate partial traces. -/
theorem not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessor_gammaOddJacobi
    {P : Type*} [Fintype P] (prime : P → Nat.Primes)
    (M N : ℕ) (hM : 0 < M) :
    ¬ ((∃ C : Matrix (P × Fin N) (P × Fin N) ℝ,
          HTGeometry.bivariateJetMarginal C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N ∧
          HTGeometry.bivariateSourceMarginal C =
            finiteGammaOddJacobiCoherentResidualMatrix prime) ∧
        (∃ C : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ,
          HTGeometry.bivariateJetMarginal C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1) ∧
          HTGeometry.bivariateSourceMarginal C =
            finiteGammaOddJacobiCoherentResidualMatrix prime)) :=
  not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessor M N hM
    (finiteGammaOddJacobiCoherentResidualMatrix prime)

end

end RHTower
