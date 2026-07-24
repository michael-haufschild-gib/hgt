import GaloisForLFunctions.HTGeometry.WeightedBivariateMarginalLock
import GaloisForLFunctions.RHTower.VonMangoldtBivariateMarginalTraceLock
import GaloisForLFunctions.RHTower.VonMangoldtSuccessorDiracKreinEdge

/-!
# Von Mangoldt weighted-marginal boundary anomaly

Ordinary coordinate partial trace is not the only finite marginal construction obstructed by the
strict Suzuki jet-opening flux.  Arbitrary diagonal densities on both tensor factors obey a
weighted marginal lock.  Consequently, if one fixed source marginal is retained through every
jet cutoff, every inclusion-compatible jet weight must vanish.

This excludes positive, signed, normalized, and unnormalized diagonal-density readers.  No
positivity of the bivariate kernels, cyclicity on a full matrix algebra, RH premise, estimate, or
computation is used.
-/

open scoped BigOperators
open Filter Topology

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Exact weighted opening law for the actual finite Suzuki principal-relative jet current. -/
theorem diagonalWeightedTrace_finiteVonMangoldtSuccessor_succ
    (M N : ℕ) (jetWeight : ℕ → ℝ) :
    HTGeometry.diagonalWeightedTrace
        (fun i : Fin (N + 1) => jetWeight i)
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) =
      HTGeometry.diagonalWeightedTrace
          (fun i : Fin N => jetWeight i)
          (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N) +
        jetWeight N *
          finiteVonMangoldtSuccessorRelativeMoment M (2 * N + 2) := by
  unfold HTGeometry.diagonalWeightedTrace
  rw [Fin.sum_univ_castSucc]
  congr 1
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply]
  simp only [Fin.val_last]
  congr 2
  omega

/-- Restriction of one inclusion-compatible infinite jet density to a finite jet section. -/
def finiteVonMangoldtJetDensity (density : ℕ → ℕ → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => density i j

/-- **Full-density opening law.**  A non-diagonal density can cancel the diagonal opening flux
only through its newly exposed symmetric boundary row. -/
theorem densityPair_finiteVonMangoldtSuccessor_succ
    (M N : ℕ) (density : ℕ → ℕ → ℝ) :
    HTGeometry.matrixDensityPair (finiteVonMangoldtJetDensity density (N + 1))
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) =
      HTGeometry.matrixDensityPair (finiteVonMangoldtJetDensity density N)
          (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N) +
        density N N *
          finiteVonMangoldtSuccessorRelativeMoment M (2 * N + 2) +
        ∑ i : Fin N, (density N i + density i N) *
          finiteVonMangoldtSuccessorRelativeMoment M (N + i + 2) := by
  unfold HTGeometry.matrixDensityPair finiteVonMangoldtJetDensity
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  simp_rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply]
  simp only [Fin.val_castSucc, Fin.val_last]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have hcross :
      (∑ i : Fin N, density N i *
          finiteVonMangoldtSuccessorRelativeMoment M (i + N + 2)) =
        ∑ i : Fin N, density N i *
          finiteVonMangoldtSuccessorRelativeMoment M (N + i + 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    omega
  rw [hcross]
  ring_nf

/-- Fixed consecutive source marginals force exact cancellation between diagonal opening flux and
the new symmetric boundary row of every non-diagonal jet density. -/
theorem fixedSourceDensityMarginals_force_boundaryCancellation
    {P : Type*} [Fintype P]
    (sourceDensity : Matrix P P ℝ) (jetDensity : ℕ → ℕ → ℝ)
    (B : Matrix P P ℝ) (M N : ℕ)
    (C0 : Matrix (P × Fin N) (P × Fin N) ℝ)
    (C1 : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ)
    (hJ0 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C0 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N)
    (hP0 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity N) C0 = B)
    (hJ1 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C1 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1))
    (hP1 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity (N + 1)) C1 = B) :
    jetDensity N N *
          finiteVonMangoldtSuccessorRelativeMoment M (2 * N + 2) +
        ∑ i : Fin N, (jetDensity N i + jetDensity i N) *
          finiteVonMangoldtSuccessorRelativeMoment M (N + i + 2) = 0 := by
  have hlock0 :=
    HTGeometry.matrixDensityPair_densityBivariateJetMarginal_eq
      sourceDensity (finiteVonMangoldtJetDensity jetDensity N) C0
  have hlock1 :=
    HTGeometry.matrixDensityPair_densityBivariateJetMarginal_eq
      sourceDensity (finiteVonMangoldtJetDensity jetDensity (N + 1)) C1
  rw [hJ0, hP0] at hlock0
  rw [hJ1, hP1] at hlock1
  have hopen :=
    densityPair_finiteVonMangoldtSuccessor_succ M N jetDensity
  linarith

/-- With positive new diagonal, a fixed-marginal full-density realization must introduce a
strictly negative symmetric boundary coefficient.  Purely nonnegative density kernels cannot
carry the opening anomaly. -/
theorem fixedSourceDensityMarginals_require_negativeBoundary
    {P : Type*} [Fintype P]
    (sourceDensity : Matrix P P ℝ) (jetDensity : ℕ → ℕ → ℝ)
    (B : Matrix P P ℝ) (M N : ℕ) (hM : 0 < M)
    (hdiag : 0 < jetDensity N N)
    (C0 : Matrix (P × Fin N) (P × Fin N) ℝ)
    (C1 : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ)
    (hJ0 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C0 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N)
    (hP0 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity N) C0 = B)
    (hJ1 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C1 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1))
    (hP1 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity (N + 1)) C1 = B) :
    ∃ i : Fin N, jetDensity N i + jetDensity i N < 0 := by
  have hcancel :=
    fixedSourceDensityMarginals_force_boundaryCancellation
      sourceDensity jetDensity B M N C0 C1 hJ0 hP0 hJ1 hP1
  by_contra hnegative
  push Not at hnegative
  have hsum :
      0 ≤ ∑ i : Fin N, (jetDensity N i + jetDensity i N) *
          finiteVonMangoldtSuccessorRelativeMoment M (N + i + 2) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hnegative i)
      (finiteVonMangoldtSuccessorRelativeMoment_pos
        M (N + i + 2) hM (by omega)).le
  have hopen :
      0 < jetDensity N N *
          finiteVonMangoldtSuccessorRelativeMoment M (2 * N + 2) :=
    mul_pos hdiag
      (finiteVonMangoldtSuccessorRelativeMoment_pos M (2 * N + 2) hM (by omega))
  linarith

/-- Cyclicity against the simple jet-degree clock kills every boundary coefficient that could
absorb opening flux.  A fixed source marginal then forces the newly opened diagonal density to
vanish. -/
theorem fixedSourceDensityMarginals_clockCyclic_force_openingDiagonal_zero
    {P : Type*} [Fintype P]
    (sourceDensity : Matrix P P ℝ) (jetDensity : ℕ → ℕ → ℝ)
    (B : Matrix P P ℝ) (M N : ℕ) (hM : 0 < M)
    (C0 : Matrix (P × Fin N) (P × Fin N) ℝ)
    (C1 : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ)
    (hJ0 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C0 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N)
    (hP0 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity N) C0 = B)
    (hJ1 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C1 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1))
    (hP1 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity (N + 1)) C1 = B)
    (hcyc :
      HTGeometry.MatrixDensityClockCyclic
        (finiteVonMangoldtJetDensity jetDensity (N + 1))
        (fun i : Fin (N + 1) => (i : ℝ))) :
    jetDensity N N = 0 := by
  have hclock :
      Function.Injective (fun i : Fin (N + 1) => (i : ℝ)) := by
    intro i j hij
    apply Fin.ext
    change ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) at hij
    exact_mod_cast hij
  have hcancel :=
    fixedSourceDensityMarginals_force_boundaryCancellation
      sourceDensity jetDensity B M N C0 C1 hJ0 hP0 hJ1 hP1
  have hcross :
      (∑ i : Fin N, (jetDensity N i + jetDensity i N) *
          finiteVonMangoldtSuccessorRelativeMoment M (N + i + 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hlast : (Fin.last N : Fin (N + 1)) ≠ i.castSucc := by
      intro h
      have := congrArg Fin.val h
      simp at this
      have hiLt := i.isLt
      omega
    have hNi :
        jetDensity N i = 0 := by
      change finiteVonMangoldtJetDensity jetDensity (N + 1)
          (Fin.last N) i.castSucc = 0
      exact HTGeometry.matrixDensityClockCyclic_offDiagonal_eq_zero
        _ _ hclock hcyc hlast
    have hiN :
        jetDensity i N = 0 := by
      change finiteVonMangoldtJetDensity jetDensity (N + 1)
          i.castSucc (Fin.last N) = 0
      exact HTGeometry.matrixDensityClockCyclic_offDiagonal_eq_zero
        _ _ hclock hcyc hlast.symm
    rw [hNi, hiN, zero_add, zero_mul]
  rw [hcross, add_zero] at hcancel
  exact (mul_eq_zero.mp hcancel).resolve_right
    (ne_of_gt
      (finiteVonMangoldtSuccessorRelativeMoment_pos M (2 * N + 2) hM (by omega)))

/-- Across all nonempty jet cutoffs, fixed source marginal plus cyclicity against the jet-degree
clock forces every diagonal density above degree zero to vanish. -/
theorem fixedSourceMarginal_clockCyclic_allPositiveJetSections_force_diagonalTail_zero
    {P : Type*} [Fintype P]
    (sourceDensity : Matrix P P ℝ) (jetDensity : ℕ → ℕ → ℝ)
    (B : Matrix P P ℝ) (M : ℕ) (hM : 0 < M)
    (hsections : ∀ N : ℕ,
      ∃ C : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ,
        HTGeometry.densityBivariateJetMarginal sourceDensity C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1) ∧
          HTGeometry.densityBivariateSourceMarginal
              (finiteVonMangoldtJetDensity jetDensity (N + 1)) C = B)
    (hcyc : ∀ N : ℕ,
      HTGeometry.MatrixDensityClockCyclic
        (finiteVonMangoldtJetDensity jetDensity (N + 1))
        (fun i : Fin (N + 1) => (i : ℝ))) :
    ∀ N : ℕ, jetDensity (N + 1) (N + 1) = 0 := by
  intro N
  obtain ⟨C0, hJ0, hP0⟩ := hsections N
  obtain ⟨C1, hJ1, hP1⟩ := hsections (N + 1)
  exact fixedSourceDensityMarginals_clockCyclic_force_openingDiagonal_zero
    sourceDensity jetDensity B M (N + 1) hM C0 C1 hJ0 hP0 hJ1 hP1 (hcyc (N + 1))

/-- Every positive-order cofinal source-relative moment is strictly positive. -/
theorem vonMangoldtSuccessorRelativeMoment_pos
    (q : ℕ) (hq : 0 < q) :
    0 < vonMangoldtSuccessorRelativeMoment q := by
  have hs : Summable (fun m : ℕ =>
      vonMangoldtSuccessorRelativeMomentTerm q (m + 2)) :=
    (summable_vonMangoldtSuccessorRelativeMomentTerm q).comp_injective
      (fun a b h => Nat.add_right_cancel h)
  unfold vonMangoldtSuccessorRelativeMoment
  exact hs.tsum_pos
    (fun m =>
      vonMangoldtSuccessorRelativeMomentTerm_nonneg q (m + 2) (by omega))
    0
    (by simpa using vonMangoldtSuccessorRelativeMomentTerm_two_pos q hq)

/-- Canonical symmetric Toeplitz density generated directly by the finite von Mangoldt successor
moments. -/
noncomputable def finiteVonMangoldtHankelToeplitzCounterDensity
    (M i j : ℕ) : ℝ :=
  HTGeometry.hankelToeplitzCounterDensity
    (finiteVonMangoldtSuccessorRelativeMoment M) i j

/-- Every source-defined Toeplitz boundary row cancels the actual next Suzuki opening flux. -/
theorem finiteVonMangoldtHankelToeplitzCounterDensity_opening_cancellation
    (M n : ℕ) (hM : 0 < M) :
    finiteVonMangoldtHankelToeplitzCounterDensity M (n + 1) (n + 1) *
          finiteVonMangoldtSuccessorRelativeMoment M (2 * (n + 1) + 2) +
        ∑ i : Fin (n + 1),
          (finiteVonMangoldtHankelToeplitzCounterDensity M (n + 1) i +
              finiteVonMangoldtHankelToeplitzCounterDensity M i (n + 1)) *
            finiteVonMangoldtSuccessorRelativeMoment M ((n + 1) + i + 2) = 0 := by
  exact HTGeometry.hankelToeplitzCounterDensity_opening_cancellation
    (finiteVonMangoldtSuccessorRelativeMoment M) n
      (ne_of_gt
        (finiteVonMangoldtSuccessorRelativeMoment_pos M (n + 3) hM (by omega)))

/-- Consecutive positive jet sections have identical value under the canonical Toeplitz
counterdensity. -/
theorem finiteVonMangoldtHankelToeplitzCounterDensity_pair_succ
    (M n : ℕ) (hM : 0 < M) :
    HTGeometry.matrixDensityPair
        (finiteVonMangoldtJetDensity
          (finiteVonMangoldtHankelToeplitzCounterDensity M) (n + 2))
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (n + 2)) =
      HTGeometry.matrixDensityPair
        (finiteVonMangoldtJetDensity
          (finiteVonMangoldtHankelToeplitzCounterDensity M) (n + 1))
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (n + 1)) := by
  have hopen :=
    densityPair_finiteVonMangoldtSuccessor_succ M (n + 1)
      (finiteVonMangoldtHankelToeplitzCounterDensity M)
  have hcancel :=
    finiteVonMangoldtHankelToeplitzCounterDensity_opening_cancellation M n hM
  linarith

/-- **Von Mangoldt Hankel--Toeplitz countertrace law.**  On every nonempty jet section, the
canonical source Toeplitz density reads exactly the first relative moment `rho_M(2)`, independent
of jet cutoff. -/
theorem finiteVonMangoldtHankelToeplitzCounterDensity_pair_constant
    (M N : ℕ) (hM : 0 < M) :
    HTGeometry.matrixDensityPair
        (finiteVonMangoldtJetDensity
          (finiteVonMangoldtHankelToeplitzCounterDensity M) (N + 1))
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) =
      finiteVonMangoldtSuccessorRelativeMoment M 2 := by
  induction N with
  | zero =>
      simp [HTGeometry.matrixDensityPair, finiteVonMangoldtJetDensity,
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply,
        finiteVonMangoldtHankelToeplitzCounterDensity,
        HTGeometry.hankelToeplitzCounterDensity_self]
  | succ N ih =>
      rw [finiteVonMangoldtHankelToeplitzCounterDensity_pair_succ M N hM]
      exact ih

/-- Exact weighted opening law for the cofinal Suzuki principal-relative jet current. -/
theorem densityPair_vonMangoldtSuccessorPrincipalRelativeHankel_succ
    (N : ℕ) (density : ℕ → ℕ → ℝ) :
    HTGeometry.matrixDensityPair (finiteVonMangoldtJetDensity density (N + 1))
        (vonMangoldtSuccessorPrincipalRelativeHankel (N + 1)) =
      HTGeometry.matrixDensityPair (finiteVonMangoldtJetDensity density N)
          (vonMangoldtSuccessorPrincipalRelativeHankel N) +
        density N N * vonMangoldtSuccessorRelativeMoment (2 * N + 2) +
        ∑ i : Fin N, (density N i + density i N) *
          vonMangoldtSuccessorRelativeMoment (N + i + 2) := by
  unfold HTGeometry.matrixDensityPair finiteVonMangoldtJetDensity
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  simp_rw [vonMangoldtSuccessorPrincipalRelativeHankel_apply]
  unfold vonMangoldtSuccessorPrincipalRelativeKernel
  simp only [Fin.val_castSucc, Fin.val_last]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have hcross :
      (∑ i : Fin N, density N i *
          vonMangoldtSuccessorRelativeMoment (i + N + 2)) =
        ∑ i : Fin N, density N i *
          vonMangoldtSuccessorRelativeMoment (N + i + 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    omega
  rw [hcross]
  ring_nf

/-- Canonical symmetric Toeplitz density generated by the cofinal von Mangoldt successor
moments. -/
noncomputable def vonMangoldtHankelToeplitzCounterDensity
    (i j : ℕ) : ℝ :=
  HTGeometry.hankelToeplitzCounterDensity
    vonMangoldtSuccessorRelativeMoment i j

/-- Every finite-aperture counterweight converges to the coefficient selected by the fully summed
von Mangoldt source. -/
theorem tendsto_finiteVonMangoldtHankelToeplitzCounterweight
    (n : ℕ) :
    Tendsto
      (fun M =>
        HTGeometry.hankelToeplitzCounterweight
          (finiteVonMangoldtSuccessorRelativeMoment M) n)
      atTop
      (nhds
        (HTGeometry.hankelToeplitzCounterweight
          vonMangoldtSuccessorRelativeMoment n)) := by
  exact HTGeometry.tendsto_hankelToeplitzCounterweight
    (fun M => finiteVonMangoldtSuccessorRelativeMoment M)
    vonMangoldtSuccessorRelativeMoment
    tendsto_finiteVonMangoldtSuccessorRelativeMoment
    (fun q =>
      ne_of_gt
        (vonMangoldtSuccessorRelativeMoment_pos (q + 3) (by omega)))
    n

/-- Pointwise source-aperture convergence of the canonical Toeplitz counterdensity. -/
theorem tendsto_finiteVonMangoldtHankelToeplitzCounterDensity_apply
    (i j : ℕ) :
    Tendsto
      (fun M => finiteVonMangoldtHankelToeplitzCounterDensity M i j)
      atTop
      (nhds (vonMangoldtHankelToeplitzCounterDensity i j)) := by
  unfold finiteVonMangoldtHankelToeplitzCounterDensity
    vonMangoldtHankelToeplitzCounterDensity
    HTGeometry.hankelToeplitzCounterDensity
  split
  · exact tendsto_finiteVonMangoldtHankelToeplitzCounterweight (j - i)
  · exact tendsto_finiteVonMangoldtHankelToeplitzCounterweight (i - j)

/-- Every fixed finite jet section of the source counterdensity is the matrix limit of its literal
finite-aperture predecessors. -/
theorem tendsto_finiteVonMangoldtHankelToeplitzCounterDensity_section
    (N : ℕ) :
    Tendsto
      (fun M =>
        finiteVonMangoldtJetDensity
          (finiteVonMangoldtHankelToeplitzCounterDensity M) N)
      atTop
      (nhds
        (finiteVonMangoldtJetDensity
          vonMangoldtHankelToeplitzCounterDensity N)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_finiteVonMangoldtHankelToeplitzCounterDensity_apply i j

/-- The source-defined cofinal Toeplitz boundary row cancels every Suzuki opening flux. -/
theorem vonMangoldtHankelToeplitzCounterDensity_opening_cancellation
    (n : ℕ) :
    vonMangoldtHankelToeplitzCounterDensity (n + 1) (n + 1) *
          vonMangoldtSuccessorRelativeMoment (2 * (n + 1) + 2) +
        ∑ i : Fin (n + 1),
          (vonMangoldtHankelToeplitzCounterDensity (n + 1) i +
              vonMangoldtHankelToeplitzCounterDensity i (n + 1)) *
            vonMangoldtSuccessorRelativeMoment ((n + 1) + i + 2) = 0 := by
  exact HTGeometry.hankelToeplitzCounterDensity_opening_cancellation
    vonMangoldtSuccessorRelativeMoment n
      (ne_of_gt
        (vonMangoldtSuccessorRelativeMoment_pos (n + 3) (by omega)))

/-- Consecutive cofinal jet sections have identical value under the canonical Toeplitz
counterdensity. -/
theorem vonMangoldtHankelToeplitzCounterDensity_pair_succ
    (n : ℕ) :
    HTGeometry.matrixDensityPair
        (finiteVonMangoldtJetDensity
          vonMangoldtHankelToeplitzCounterDensity (n + 2))
        (vonMangoldtSuccessorPrincipalRelativeHankel (n + 2)) =
      HTGeometry.matrixDensityPair
        (finiteVonMangoldtJetDensity
          vonMangoldtHankelToeplitzCounterDensity (n + 1))
        (vonMangoldtSuccessorPrincipalRelativeHankel (n + 1)) := by
  have hopen :=
    densityPair_vonMangoldtSuccessorPrincipalRelativeHankel_succ
      (n + 1) vonMangoldtHankelToeplitzCounterDensity
  have hcancel :=
    vonMangoldtHankelToeplitzCounterDensity_opening_cancellation n
  linarith

/-- **Cofinal von Mangoldt Hankel--Toeplitz countertrace law.**  The canonical normalized
source-recursive Toeplitz density reads every nonempty section of the fully summed relative
current as the same first moment. -/
theorem vonMangoldtHankelToeplitzCounterDensity_pair_constant
    (N : ℕ) :
    HTGeometry.matrixDensityPair
        (finiteVonMangoldtJetDensity
          vonMangoldtHankelToeplitzCounterDensity (N + 1))
        (vonMangoldtSuccessorPrincipalRelativeHankel (N + 1)) =
      vonMangoldtSuccessorRelativeMoment 2 := by
  induction N with
  | zero =>
      simp [HTGeometry.matrixDensityPair, finiteVonMangoldtJetDensity,
        vonMangoldtSuccessorPrincipalRelativeHankel_apply,
        vonMangoldtSuccessorPrincipalRelativeKernel,
        vonMangoldtHankelToeplitzCounterDensity,
        HTGeometry.hankelToeplitzCounterDensity_self]
  | succ N ih =>
      rw [vonMangoldtHankelToeplitzCounterDensity_pair_succ N]
      exact ih

/-- The finite countertrace law is carried by the actual source-edge Dirac--Krein realization, not
only by its contracted Hankel matrix. -/
theorem finiteVonMangoldtHankelToeplitzCounterDensity_diracKrein_pair_constant
    (M N : ℕ) (hM : 0 < M) :
    HTGeometry.matrixDensityPair
        (finiteVonMangoldtJetDensity
          (finiteVonMangoldtHankelToeplitzCounterDensity M) (N + 1))
        (finiteVonMangoldtSuccessorDiracKreinGram M (N + 1)) =
      finiteVonMangoldtSuccessorRelativeMoment M 2 := by
  rw [finiteVonMangoldtSuccessorDiracKreinGram_eq]
  exact finiteVonMangoldtHankelToeplitzCounterDensity_pair_constant M N hM

/-- The cofinal countertrace likewise evaluates the literal source-edge exchange Gram to the first
relative moment on every nonempty jet section. -/
theorem vonMangoldtHankelToeplitzCounterDensity_diracKrein_pair_constant
    (N : ℕ) :
    HTGeometry.matrixDensityPair
        (finiteVonMangoldtJetDensity
          vonMangoldtHankelToeplitzCounterDensity (N + 1))
        (fun i j : Fin (N + 1) =>
          vonMangoldtSuccessorDiracKreinGram i j) =
      vonMangoldtSuccessorRelativeMoment 2 := by
  have hmatrix :
      (fun i j : Fin (N + 1) =>
        vonMangoldtSuccessorDiracKreinGram i j) =
        vonMangoldtSuccessorPrincipalRelativeHankel (N + 1) := by
    ext i j
    rw [vonMangoldtSuccessorDiracKreinGram_eq,
      vonMangoldtSuccessorPrincipalRelativeHankel_apply]
  rw [hmatrix]
  exact vonMangoldtHankelToeplitzCounterDensity_pair_constant N

/-- Two consecutive weighted bivariate realizations with one fixed source marginal force the
weight of the newly opened jet coordinate to vanish. -/
theorem fixedSourceMarginals_force_openingJetWeight_zero
    {P : Type*} [Fintype P]
    (sourceWeight : P → ℝ) (jetWeight : ℕ → ℝ)
    (B : Matrix P P ℝ) (M N : ℕ) (hM : 0 < M)
    (C0 : Matrix (P × Fin N) (P × Fin N) ℝ)
    (C1 : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ)
    (hJ0 :
      HTGeometry.weightedBivariateJetMarginal sourceWeight C0 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N)
    (hP0 :
      HTGeometry.weightedBivariateSourceMarginal
          (fun i : Fin N => jetWeight i) C0 = B)
    (hJ1 :
      HTGeometry.weightedBivariateJetMarginal sourceWeight C1 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1))
    (hP1 :
      HTGeometry.weightedBivariateSourceMarginal
          (fun i : Fin (N + 1) => jetWeight i) C1 = B) :
    jetWeight N = 0 := by
  have hlock0 :=
    HTGeometry.diagonalWeightedTrace_weightedBivariateJetMarginal_eq
      sourceWeight (fun i : Fin N => jetWeight i) C0
  have hlock1 :=
    HTGeometry.diagonalWeightedTrace_weightedBivariateJetMarginal_eq
      sourceWeight (fun i : Fin (N + 1) => jetWeight i) C1
  rw [hJ0, hP0] at hlock0
  rw [hJ1, hP1] at hlock1
  have hopen :=
    diagonalWeightedTrace_finiteVonMangoldtSuccessor_succ M N jetWeight
  have hzero :
      jetWeight N *
          finiteVonMangoldtSuccessorRelativeMoment M (2 * N + 2) = 0 := by
    linarith
  exact (mul_eq_zero.mp hzero).resolve_right
    (ne_of_gt
      (finiteVonMangoldtSuccessorRelativeMoment_pos M (2 * N + 2) hM (by omega)))

/-- **All-cutoff diagonal-density classification.**  Any weighted bivariate family realizing all
actual Suzuki jet sections while retaining one fixed finite source marginal has identically zero
jet density. -/
theorem fixedSourceMarginal_allJetSections_force_jetWeight_zero
    {P : Type*} [Fintype P]
    (sourceWeight : P → ℝ) (jetWeight : ℕ → ℝ)
    (B : Matrix P P ℝ) (M : ℕ) (hM : 0 < M)
    (hsections : ∀ N : ℕ,
      ∃ C : Matrix (P × Fin N) (P × Fin N) ℝ,
        HTGeometry.weightedBivariateJetMarginal sourceWeight C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N ∧
          HTGeometry.weightedBivariateSourceMarginal
              (fun i : Fin N => jetWeight i) C = B) :
    jetWeight = 0 := by
  funext N
  obtain ⟨C0, hJ0, hP0⟩ := hsections N
  obtain ⟨C1, hJ1, hP1⟩ := hsections (N + 1)
  exact fixedSourceMarginals_force_openingJetWeight_zero
    sourceWeight jetWeight B M N hM C0 C1 hJ0 hP0 hJ1 hP1

/-- For the nonempty jet tower, a fixed source marginal forces every diagonal density weight above
the initial jet coordinate to vanish.  The only diagonal survivor is a rank-one degree-zero
reader. -/
theorem fixedSourceMarginal_allPositiveJetSections_force_jetWeight_tail_zero
    {P : Type*} [Fintype P]
    (sourceWeight : P → ℝ) (jetWeight : ℕ → ℝ)
    (B : Matrix P P ℝ) (M : ℕ) (hM : 0 < M)
    (hsections : ∀ N : ℕ,
      ∃ C : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ,
        HTGeometry.weightedBivariateJetMarginal sourceWeight C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1) ∧
          HTGeometry.weightedBivariateSourceMarginal
              (fun i : Fin (N + 1) => jetWeight i) C = B) :
    ∀ N : ℕ, jetWeight (N + 1) = 0 := by
  intro N
  obtain ⟨C0, hJ0, hP0⟩ := hsections N
  obtain ⟨C1, hJ1, hP1⟩ := hsections (N + 1)
  exact fixedSourceMarginals_force_openingJetWeight_zero
    sourceWeight jetWeight B M (N + 1) hM C0 C1 hJ0 hP0 hJ1 hP1

/-- No nonzero inclusion-compatible diagonal jet density can realize all Suzuki jet sections with
one fixed source marginal. -/
theorem not_allJetSections_fixedSourceMarginal_of_jetWeight_ne_zero
    {P : Type*} [Fintype P]
    (sourceWeight : P → ℝ) (jetWeight : ℕ → ℝ)
    (B : Matrix P P ℝ) (M : ℕ) (hM : 0 < M)
    (hweight : jetWeight ≠ 0) :
    ¬ ∀ N : ℕ,
      ∃ C : Matrix (P × Fin N) (P × Fin N) ℝ,
        HTGeometry.weightedBivariateJetMarginal sourceWeight C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N ∧
          HTGeometry.weightedBivariateSourceMarginal
              (fun i : Fin N => jetWeight i) C = B := by
  intro hsections
  exact hweight
    (fixedSourceMarginal_allJetSections_force_jetWeight_zero
      sourceWeight jetWeight B M hM hsections)

/-- A nonzero higher-jet diagonal weight rules out a fixed-marginal realization of every nonempty
Suzuki jet section. -/
theorem not_allPositiveJetSections_fixedSourceMarginal_of_tailWeight_ne_zero
    {P : Type*} [Fintype P]
    (sourceWeight : P → ℝ) (jetWeight : ℕ → ℝ)
    (B : Matrix P P ℝ) (M K : ℕ) (hM : 0 < M)
    (hweight : jetWeight (K + 1) ≠ 0) :
    ¬ ∀ N : ℕ,
      ∃ C : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ,
        HTGeometry.weightedBivariateJetMarginal sourceWeight C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1) ∧
          HTGeometry.weightedBivariateSourceMarginal
              (fun i : Fin (N + 1) => jetWeight i) C = B := by
  intro hsections
  exact hweight
    (fixedSourceMarginal_allPositiveJetSections_force_jetWeight_tail_zero
      sourceWeight jetWeight B M hM hsections K)

/-- The all-cutoff classification applies directly when the fixed source marginal is the actual
coherent odd Gamma--Jacobi residual on a finite prime packet. -/
theorem gammaOddJacobi_fixedSourceMarginal_allJetSections_force_jetWeight_zero
    {P : Type*} [Fintype P] (prime : P → Nat.Primes)
    (sourceWeight : P → ℝ) (jetWeight : ℕ → ℝ)
    (M : ℕ) (hM : 0 < M)
    (hsections : ∀ N : ℕ,
      ∃ C : Matrix (P × Fin N) (P × Fin N) ℝ,
        HTGeometry.weightedBivariateJetMarginal sourceWeight C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N ∧
          HTGeometry.weightedBivariateSourceMarginal
              (fun i : Fin N => jetWeight i) C =
            finiteGammaOddJacobiCoherentResidualMatrix prime) :
    jetWeight = 0 :=
  fixedSourceMarginal_allJetSections_force_jetWeight_zero
    sourceWeight jetWeight
      (finiteGammaOddJacobiCoherentResidualMatrix prime) M hM hsections

/-- On the actual coherent odd Gamma--Jacobi marginal, every nonempty diagonal-density tower
collapses to its degree-zero reader. -/
theorem gammaOddJacobi_fixedSourceMarginal_allPositiveJetSections_force_tail_zero
    {P : Type*} [Fintype P] (prime : P → Nat.Primes)
    (sourceWeight : P → ℝ) (jetWeight : ℕ → ℝ)
    (M : ℕ) (hM : 0 < M)
    (hsections : ∀ N : ℕ,
      ∃ C : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ,
        HTGeometry.weightedBivariateJetMarginal sourceWeight C =
            finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1) ∧
          HTGeometry.weightedBivariateSourceMarginal
              (fun i : Fin (N + 1) => jetWeight i) C =
            finiteGammaOddJacobiCoherentResidualMatrix prime) :
    ∀ N : ℕ, jetWeight (N + 1) = 0 :=
  fixedSourceMarginal_allPositiveJetSections_force_jetWeight_tail_zero
    sourceWeight jetWeight
      (finiteGammaOddJacobiCoherentResidualMatrix prime) M hM hsections

end

end RHTower
