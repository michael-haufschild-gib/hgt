import GaloisForLFunctions.HTGeometry.EuclideanPackingPigeonhole
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The spectral response vector and its size

Hellmann–Feynman says that the motion of a simple eigenvalue under a family `A₀ + t·∑_a u_a P_a` is
the expectation `∑_a u_a ⟪e, P_a e⟫` of the family's motion in the eigenstate.  So the gradient of
that eigenvalue in coefficient space is the *response vector* whose `a`-th coordinate is
`⟪e, P_a e⟫`.

Each coordinate is bounded by the operator norm of the corresponding generator, so a family of `m`
generators of norm at most one produces response vectors of Euclidean norm at most `√m` — and the
same bound survives orthogonal projection onto any subspace, in particular onto the tangent space
of a coefficient sphere.  Feeding that bound into the volume packing law bounds the observed
crowding of replica actions built from these gradients.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section ResponseVector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The expectation of an operator in a unit state is bounded by its operator norm. -/
theorem abs_inner_apply_le_opNorm (A : E →L[ℝ] E) {e : E} (he : ‖e‖ ≤ 1) :
    |(inner ℝ e (A e) : ℝ)| ≤ ‖A‖ := by
  calc |(inner ℝ e (A e) : ℝ)| ≤ ‖e‖ * ‖A e‖ := by
        simpa using abs_real_inner_le_norm e (A e)
    _ ≤ ‖e‖ * (‖A‖ * ‖e‖) := by
        refine mul_le_mul_of_nonneg_left (A.le_opNorm e) (norm_nonneg e)
    _ ≤ 1 * (‖A‖ * 1) := by
        refine mul_le_mul he ?_ (by positivity) zero_le_one
        exact mul_le_mul_of_nonneg_left he (norm_nonneg A)
    _ = ‖A‖ := by ring

/-- The response vector of a state against a finite family of generators: its `a`-th coordinate is
the expectation of the `a`-th generator. -/
def spectralResponseVector {m : ℕ} (P : Fin m → (E →L[ℝ] E)) (e : E) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun a => (inner ℝ e (P a e) : ℝ)

theorem spectralResponseVector_apply {m : ℕ} (P : Fin m → (E →L[ℝ] E)) (e : E) (a : Fin m) :
    spectralResponseVector P e a = (inner ℝ e (P a e) : ℝ) := rfl

/-- **Hellmann–Feynman in coefficient space.**  The expectation of a coefficient combination of the
generators is the inner product of the coefficient vector with the response vector, so the response
vector is exactly the coefficient-space gradient supplied by Hellmann–Feynman. -/
theorem inner_spectralResponseVector {m : ℕ} (P : Fin m → (E →L[ℝ] E)) (e : E)
    (u : EuclideanSpace ℝ (Fin m)) :
    (inner ℝ u (spectralResponseVector P e) : ℝ) = (inner ℝ e ((∑ a, u a • P a) e) : ℝ) := by
  classical
  rw [show ((∑ a, u a • P a) e) = ∑ a, u a • P a e by simp, inner_sum]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [real_inner_smul_right, spectralResponseVector_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- A vector all of whose coordinates are bounded by one has norm at most `√m`. -/
theorem norm_le_sqrt_card_of_forall_abs_le {m : ℕ} (w : EuclideanSpace ℝ (Fin m))
    (hw : ∀ a, |w a| ≤ 1) : ‖w‖ ≤ Real.sqrt m := by
  classical
  have hsq : ‖w‖ ^ (2 : ℕ) ≤ (m : ℝ) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    calc ∑ i : Fin m, ‖w i‖ ^ (2 : ℕ) ≤ ∑ _i : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hw i
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (w i)]
      _ = (m : ℝ) := by simp
  have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (m : ℝ)),
    Real.sqrt_nonneg ((m : ℝ)), hsq, hnn]

/-- **Equation (4): the response vector of a unit state against `m` generators of norm at most one
has Euclidean norm at most `√m`.** -/
theorem norm_spectralResponseVector_le {m : ℕ} (P : Fin m → (E →L[ℝ] E))
    (hP : ∀ a, ‖P a‖ ≤ 1) {e : E} (he : ‖e‖ ≤ 1) :
    ‖spectralResponseVector P e‖ ≤ Real.sqrt m := by
  refine norm_le_sqrt_card_of_forall_abs_le _ fun a => ?_
  rw [spectralResponseVector_apply]
  exact le_trans (abs_inner_apply_le_opNorm (P a) he) (hP a)

/-- The same bound survives orthogonal projection onto any subspace, in particular onto the tangent
space of the coefficient sphere. -/
theorem norm_starProjection_spectralResponseVector_le {m : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin m))) [S.HasOrthogonalProjection]
    (P : Fin m → (E →L[ℝ] E)) (hP : ∀ a, ‖P a‖ ≤ 1) {e : E} (he : ‖e‖ ≤ 1) :
    ‖S.starProjection (spectralResponseVector P e)‖ ≤ Real.sqrt m :=
  le_trans (S.norm_starProjection_apply_le _) (norm_spectralResponseVector_le P hP he)

end ResponseVector

/-- **Corollary A1, equation (5).**  With observer vectors given by spectral response vectors of
unit states against `m` generators of norm at most one, two distinct replica multiplicity vectors of
order `r` have observed actions within `2 r √m / (N^{1/d} − 1)` of one another, where `N` is the
number of multiplicity vectors and `d` the dimension of the observer space. -/
theorem exists_pair_replicaObservedAction_response_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
    [FiniteDimensional ℝ W] [Nontrivial W] (μ : Measure W) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (P : Fin m → (E →L[ℝ] E)) (hP : ∀ a, ‖P a‖ ≤ 1)
    (state : I → E) (hstate : ∀ j, ‖state j‖ ≤ 1)
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] W) (hT : ‖T‖ ≤ 1) (r : ℕ)
    (hcard : 1 < (Finset.univ.piAntidiag r : Finset (I → ℕ)).card) :
    ∃ p ∈ (Finset.univ.piAntidiag r : Finset (I → ℕ)),
      ∃ q ∈ (Finset.univ.piAntidiag r : Finset (I → ℕ)), p ≠ q ∧
        (((Finset.univ.piAntidiag r : Finset (I → ℕ)).card : ℝ) ^
              ((Module.finrank ℝ W : ℝ)⁻¹) - 1) *
            ‖replicaObservedAction (fun j => T (spectralResponseVector P (state j))) p -
              replicaObservedAction (fun j => T (spectralResponseVector P (state j))) q‖ ≤
          2 * (r * Real.sqrt m) := by
  refine exists_pair_replicaObservedAction_mul_le μ
    (fun j => T (spectralResponseVector P (state j))) (Real.sqrt m) (Real.sqrt_nonneg _)
    (fun j => ?_) r hcard
  calc ‖T (spectralResponseVector P (state j))‖ ≤ ‖T‖ * ‖spectralResponseVector P (state j)‖ :=
        T.le_opNorm _
    _ ≤ 1 * Real.sqrt m := by
        refine mul_le_mul hT (norm_spectralResponseVector_le P hP (hstate j)) (norm_nonneg _)
          zero_le_one
    _ = Real.sqrt m := one_mul _

end GaloisForLFunctions.HTGeometry
