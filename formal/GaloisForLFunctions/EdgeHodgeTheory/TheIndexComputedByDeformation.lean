import GaloisForLFunctions.EdgeHodgeTheory.IntegersAlongPaths
import GaloisForLFunctions.EdgeHodgeTheory.TheHorizonFlowAtFixedWidth
import GaloisForLFunctions.HeckeKreinToeplitz.ShrinkingAtomsCarryTheWholeIndex

/-!
# The index computed by deformation

Can the Hodge defect be computed by deforming the form, through nondegenerate forms, to a model
of known index? Along such a path the index is constant (`IntegersAlongPaths`), so the answer is
fixed by the endpoint.

* **Regularized deformation** (`forall_exists_crossingFree_path_add_iff`): for a Hermitian `A`, a
  crossing-free path from `A + ε·1` to the identity exists for every `ε > 0` iff `A` has no negative
  square. The shift moves each eigenvalue by `ε`, and the straight path is crossing-free exactly
  when all shifted eigenvalues are positive.
* **The spline horizon families** (`riemannHypothesis_iff_spline_regularized_deformation`): at any
  width `w > 0`, RH holds iff at every horizon the regularized Weil Gram matrix of the spline atoms
  `B_w(· − log n)` deforms to the identity without crossing.
* **Every deformation crosses without RH** (`eventually_not_exists_crossingFree_path_of_not_rh`):
  if RH fails, from some horizon on no crossing-free path joins the spline horizon family to the
  identity.

An index computed by deformation to a positive model is the sign itself: a structural reason that
keeps a path nondegenerate is a proof of positivity at its starting point.
-/

open Matrix Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.EdgeHodgeTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem isHermitian_add_smul_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (ε : ℝ) :
    (A + ((ε : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_add, conjTranspose_smul, hA.eq, conjTranspose_one]
  simp [Complex.conj_ofReal]

/-- In the eigenbasis of `A`, the shift `A + ε·1` is diagonal with entries `λᵢ + ε`. -/
theorem conjTranspose_mul_add_smul_one_mul {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (ε : ℝ) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (A + ((ε : ℝ) : ℂ) • 1) *
        (hA.eigenvectorUnitary : Matrix ι ι ℂ) =
      diagonal fun i => ((hA.eigenvalues i + ε : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    conjTranspose_mul_mul_eigenvectorUnitary hA, hU]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

/-- **Regularized deformation.** For every `ε > 0` a crossing-free path joins `A + ε·1` to the
identity iff `A` has no negative square. -/
theorem forall_exists_crossingFree_path_add_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (∀ ε : ℝ, 0 < ε → ∃ H : ℝ → Matrix ι ι ℂ, ContinuousOn H (Set.Icc 0 1) ∧
      H 0 = A + ((ε : ℝ) : ℂ) • 1 ∧ H 1 = 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (H t).IsHermitian ∧ hermNullIndex (H t) = 0) ↔
      hermNegIndex A = 0 := by
  have key : ∀ ε : ℝ, hermNegIndex (A + ((ε : ℝ) : ℂ) • 1) = 0 ∧
      hermNullIndex (A + ((ε : ℝ) : ℂ) • 1) = 0 ↔ ∀ i, 0 < hA.eigenvalues i + ε := by
    intro ε
    have hU := isUnit_eigenvectorUnitary hA
    rw [← negIndex_conjugate _ hU, ← nullIndex_conjugate _ hU,
      conjTranspose_mul_add_smul_one_mul hA, negIndex_diagonal, nullIndex_diagonal,
      Finset.card_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.filter_eq_empty_iff]
    constructor
    · rintro ⟨h₁, h₂⟩ i
      exact lt_of_le_of_ne (not_lt.mp (h₁ (Finset.mem_univ i))) (Ne.symm (h₂ (Finset.mem_univ i)))
    · intro h
      exact ⟨fun i _ => not_lt.mpr (h i).le, fun i _ => (h i).ne'⟩
  rw [negIndex_eq_card_neg_eigenvalues hA, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro H i _ hneg
    have hε : 0 < -hA.eigenvalues i / 2 := by linarith
    have h := (key _).mp ((exists_crossingFree_path_to_one_iff (isHermitian_add_smul_one hA _)).mp
      (H _ hε)) i
    linarith
  · intro H ε hε
    refine (exists_crossingFree_path_to_one_iff (isHermitian_add_smul_one hA ε)).mpr ((key ε).mpr ?_)
    intro i
    have := not_lt.mp (H (Finset.mem_univ i))
    linarith

/-! ### The spline horizon families -/

open HeckeKreinToeplitz (shrinkGram negIndex_zetaKernel_eq_iSup_shrinkGram hermNegIndex_shrinkGram_mono
  riemannHypothesis_iff_negIndex_zetaKernel_eq_zero)

theorem shrinkGram_isHermitian (w : ℝ) (N : ℕ) : (shrinkGram w N).IsHermitian :=
  ArithmeticCastelnuovoSeveri.weilGram_isHermitian _ _

/-- RH holds iff the spline horizon family of width `w` has no negative square at any horizon. -/
theorem riemannHypothesis_iff_forall_shrinkGram {w : ℝ} (hw : 0 < w) :
    RiemannHypothesis ↔ ∀ N, hermNegIndex (shrinkGram w N) = 0 := by
  rw [riemannHypothesis_iff_negIndex_zetaKernel_eq_zero, negIndex_zetaKernel_eq_iSup_shrinkGram hw,
    ENat.iSup_eq_zero]
  simp only [Nat.cast_eq_zero]

/-- **Deformation of the spline horizon family reads RH.** -/
theorem riemannHypothesis_iff_spline_regularized_deformation {w : ℝ} (hw : 0 < w) :
    RiemannHypothesis ↔ ∀ (N : ℕ) (ε : ℝ), 0 < ε → ∃ H : ℝ → Matrix (Fin N) (Fin N) ℂ,
      ContinuousOn H (Set.Icc 0 1) ∧ H 0 = shrinkGram w N + ((ε : ℝ) : ℂ) • 1 ∧ H 1 = 1 ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, (H t).IsHermitian ∧ hermNullIndex (H t) = 0 := by
  rw [riemannHypothesis_iff_forall_shrinkGram hw]
  exact forall_congr' fun N =>
    (forall_exists_crossingFree_path_add_iff (shrinkGram_isHermitian w N)).symm

/-- **Every deformation crosses without RH.** If RH fails, then at every width, from some horizon
on, no crossing-free path joins the spline horizon family to the identity. -/
theorem eventually_not_exists_crossingFree_path_of_not_rh (hRH : ¬ RiemannHypothesis) {w : ℝ}
    (hw : 0 < w) :
    ∀ᶠ N : ℕ in atTop, ¬ ∃ H : ℝ → Matrix (Fin N) (Fin N) ℂ, ContinuousOn H (Set.Icc 0 1) ∧
      H 0 = shrinkGram w N ∧ H 1 = 1 ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, (H t).IsHermitian ∧ hermNullIndex (H t) = 0 := by
  rw [riemannHypothesis_iff_forall_shrinkGram hw] at hRH
  push Not at hRH
  obtain ⟨N₀, hN₀⟩ := hRH
  filter_upwards [eventually_ge_atTop N₀] with N hN hpath
  have h0 := ((exists_crossingFree_path_to_one_iff (shrinkGram_isHermitian w N)).mp hpath).1
  exact hN₀ (Nat.eq_zero_of_le_zero (h0 ▸ hermNegIndex_shrinkGram_mono w hN))

end GaloisForLFunctions.EdgeHodgeTheory
