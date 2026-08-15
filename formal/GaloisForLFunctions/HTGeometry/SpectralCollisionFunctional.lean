import GaloisForLFunctions.HTGeometry.PureStateReplicaProjectiveGramLaw

/-!
# A polynomial regularization of the spectral collision

The spectral collision of a state in the eigenbasis of a Hermitian matrix is not a continuous
function of the matrix, because an eigenbasis is not.  Its regularization by a symmetric weight of
the spectral gaps is: expanding the weight binomially expresses it through the state moments
`⟨ψ, Hʳψ⟩`, which are polynomials in the matrix entries.  The regularization dominates the
collision at every regularization order and decreases to the collision of the diagonal spectral
classes, so it is exactly the collision whenever the spectrum is simple.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

section Inner

theorem finiteComplexInner_sum_right {ι : Type*} (u : α → ℂ) (s : Finset ι) (v : ι → α → ℂ) :
    finiteComplexInner u (∑ i ∈ s, v i) = ∑ i ∈ s, finiteComplexInner u (v i) := by
  classical
  simp only [finiteComplexInner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_apply, Finset.mul_sum]

theorem finiteComplexInner_smul_right (u v : α → ℂ) (c : ℂ) :
    finiteComplexInner u (c • v) = c * finiteComplexInner u v := by
  simp only [finiteComplexInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end Inner

section EigenBasis

/-- An orthonormal eigenbasis of a matrix, with its real eigenvalues. -/
structure IsOrthoEigenBasis (H : Matrix α α ℂ) (e : α → α → ℂ) (lam : α → ℝ) : Prop where
  orth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0
  eigen : ∀ j, H *ᵥ e j = ((lam j : ℝ) : ℂ) • e j
  complete : ∀ ψ : α → ℂ, ∑ j, finiteComplexInner (e j) ψ • e j = ψ

/-- The spectral weight of a state on one eigenvector. -/
def eigenWeight (e : α → α → ℂ) (ψ : α → ℂ) (j : α) : ℝ :=
  ‖finiteComplexInner (e j) ψ‖ ^ 2

theorem eigenWeight_nonneg (e : α → α → ℂ) (ψ : α → ℂ) (j : α) : 0 ≤ eigenWeight e ψ j :=
  sq_nonneg _

/-- The `r`-th moment of a state under a matrix. -/
def stateMoment (H : Matrix α α ℂ) (ψ : α → ℂ) (r : ℕ) : ℂ :=
  finiteComplexInner ψ ((H ^ r) *ᵥ ψ)

theorem pow_mulVec_eigen {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (j : α) (r : ℕ) :
    (H ^ r) *ᵥ e j = (((lam j : ℝ) : ℂ) ^ r) • e j := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hb.eigen j, smul_smul,
        ← pow_succ]

theorem stateMoment_eq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) (r : ℕ) :
    stateMoment H ψ r = ∑ j, ((eigenWeight e ψ j : ℝ) : ℂ) * (((lam j : ℝ) : ℂ)) ^ r := by
  classical
  have hexp : (H ^ r) *ᵥ ψ =
      ∑ j, (finiteComplexInner (e j) ψ * ((lam j : ℝ) : ℂ) ^ r) • e j := by
    conv_lhs => rw [← hb.complete ψ]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, pow_mulVec_eigen hb j r, smul_smul]
  rw [stateMoment, hexp, finiteComplexInner_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finiteComplexInner_smul_right, eigenWeight]
  have hconj : finiteComplexInner ψ (e j) = (starRingEnd ℂ) (finiteComplexInner (e j) ψ) :=
    finiteComplexInner_conj_symm _ _
  rw [hconj]
  have hnorm : ((‖finiteComplexInner (e j) ψ‖ ^ 2 : ℝ) : ℂ) =
      finiteComplexInner (e j) ψ * (starRingEnd ℂ) (finiteComplexInner (e j) ψ) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [hnorm]
  ring

end EigenBasis

section Regularization

/-- The binomially expanded gap regularization of the collision. -/
def regCollisionC (c : ℝ) (m : ℕ) (H : Matrix α α ℂ) (ψ : α → ℂ) : ℂ :=
  ∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * (-(1 : ℂ) / (c : ℂ)) ^ l *
    ∑ i ∈ Finset.range (2 * l + 1), (((2 * l).choose i : ℕ) : ℂ) * (-1 : ℂ) ^ i *
      (stateMoment H ψ (2 * l - i) * stateMoment H ψ i)

theorem sum_gap_pow {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) (l : ℕ) :
    (∑ i ∈ Finset.range (2 * l + 1), (((2 * l).choose i : ℕ) : ℂ) * (-1 : ℂ) ^ i *
        (stateMoment H ψ (2 * l - i) * stateMoment H ψ i)) =
      ∑ j, ∑ k, ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
        (((lam j - lam k : ℝ) : ℂ)) ^ (2 * l) := by
  classical
  have hL : (∑ i ∈ Finset.range (2 * l + 1), (((2 * l).choose i : ℕ) : ℂ) * (-1 : ℂ) ^ i *
        (stateMoment H ψ (2 * l - i) * stateMoment H ψ i)) =
      ∑ i ∈ Finset.range (2 * l + 1), ∑ j, ∑ k,
        ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
          ((-(((lam k : ℝ) : ℂ))) ^ i * (((lam j : ℝ) : ℂ)) ^ (2 * l - i) *
            (((2 * l).choose i : ℕ) : ℂ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stateMoment_eq hb ψ (2 * l - i), stateMoment_eq hb ψ i, Finset.sum_mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  have hR : (∑ j, ∑ k, ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
        (((lam j - lam k : ℝ) : ℂ)) ^ (2 * l)) =
      ∑ j, ∑ k, ∑ i ∈ Finset.range (2 * l + 1),
        ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
          ((-(((lam k : ℝ) : ℂ))) ^ i * (((lam j : ℝ) : ℂ)) ^ (2 * l - i) *
            (((2 * l).choose i : ℕ) : ℂ)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hbin : (((lam j - lam k : ℝ) : ℂ)) ^ (2 * l) =
        ∑ i ∈ Finset.range (2 * l + 1),
          (-(((lam k : ℝ) : ℂ))) ^ i * (((lam j : ℝ) : ℂ)) ^ (2 * l - i) *
            (((2 * l).choose i : ℕ) : ℂ) := by
      rw [show (((lam j - lam k : ℝ) : ℂ)) = -(((lam k : ℝ) : ℂ)) + (((lam j : ℝ) : ℂ)) by
        push_cast; ring]
      exact add_pow _ _ _
    rw [hbin, Finset.mul_sum]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- **The regularization is a spectral gap weight.** -/
theorem regCollisionC_eq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) (c : ℝ) (m : ℕ) :
    regCollisionC c m H ψ =
      ∑ j, ∑ k, ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
        (((1 - (lam j - lam k) ^ 2 / c : ℝ) : ℂ)) ^ m := by
  classical
  rw [regCollisionC]
  have hL : (∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * (-(1 : ℂ) / (c : ℂ)) ^ l *
        ∑ i ∈ Finset.range (2 * l + 1), (((2 * l).choose i : ℕ) : ℂ) * (-1 : ℂ) ^ i *
          (stateMoment H ψ (2 * l - i) * stateMoment H ψ i)) =
      ∑ l ∈ Finset.range (m + 1), ∑ j, ∑ k,
        ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
          ((-((((lam j - lam k) ^ 2 / c : ℝ) : ℂ))) ^ l * (1 : ℂ) ^ (m - l) *
            ((m.choose l : ℕ) : ℂ)) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_gap_pow hb ψ l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hpow : (((lam j - lam k : ℝ) : ℂ)) ^ (2 * l) =
        ((((lam j - lam k) ^ 2 : ℝ) : ℂ)) ^ l := by
      push_cast
      exact pow_mul _ 2 l
    rw [hpow, one_pow, Complex.ofReal_div,
      show (-(((((lam j - lam k) ^ 2 : ℝ) : ℂ)) / (c : ℂ))) =
        (-(1 : ℂ) / (c : ℂ)) * ((((lam j - lam k) ^ 2 : ℝ) : ℂ)) from by ring,
      mul_pow]
    ring
  have hR : (∑ j, ∑ k, ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
        (((1 - (lam j - lam k) ^ 2 / c : ℝ) : ℂ)) ^ m) =
      ∑ j, ∑ k, ∑ l ∈ Finset.range (m + 1),
        ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
          ((-((((lam j - lam k) ^ 2 / c : ℝ) : ℂ))) ^ l * (1 : ℂ) ^ (m - l) *
            ((m.choose l : ℕ) : ℂ)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hbin : (((1 - (lam j - lam k) ^ 2 / c : ℝ) : ℂ)) ^ m =
        ∑ l ∈ Finset.range (m + 1),
          (-((((lam j - lam k) ^ 2 / c : ℝ) : ℂ))) ^ l * (1 : ℂ) ^ (m - l) *
            ((m.choose l : ℕ) : ℂ) := by
      rw [show (((1 - (lam j - lam k) ^ 2 / c : ℝ) : ℂ)) =
          -((((lam j - lam k) ^ 2 / c : ℝ) : ℂ)) + 1 by push_cast; ring]
      exact add_pow _ _ _
    rw [hbin, Finset.mul_sum]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

end Regularization

end GaloisForLFunctions.HTGeometry
