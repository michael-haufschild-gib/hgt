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

/-- The orthonormal eigenbasis of a Hermitian matrix, as plain coordinate vectors. -/
def hermitianEigenBasis (H : Matrix α α ℂ) (hH : H.IsHermitian) : α → α → ℂ :=
  fun j => (hH.eigenvectorBasis j).ofLp

/-- **Every Hermitian matrix carries an orthonormal eigenbasis.**  The eigenbasis hypothesis of
this file is therefore never a restriction. -/
theorem isOrthoEigenBasis_hermitian (H : Matrix α α ℂ) (hH : H.IsHermitian) :
    IsOrthoEigenBasis H (hermitianEigenBasis H hH) hH.eigenvalues := by
  classical
  have hbridge : ∀ j : α, ∀ v : α → ℂ,
      finiteComplexInner ((hH.eigenvectorBasis j).ofLp) v =
        inner ℂ (hH.eigenvectorBasis j) (WithLp.toLp 2 v) := by
    intro j v
    rw [EuclideanSpace.inner_eq_star_dotProduct, finiteComplexInner, dotProduct]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Pi.star_apply]
    ring
  show IsOrthoEigenBasis H (fun j => (hH.eigenvectorBasis j).ofLp) hH.eigenvalues
  refine ⟨?_, ?_, ?_⟩
  · intro j k
    have h0 := hH.eigenvectorBasis.orthonormal
    rw [orthonormal_iff_ite] at h0
    rw [hbridge j ((hH.eigenvectorBasis k).ofLp)]
    exact h0 j k
  · intro j
    rw [hH.mulVec_eigenvectorBasis j]
    funext i
    simp [Complex.real_smul]
  · intro ψ
    simp only [hbridge]
    have h := hH.eigenvectorBasis.sum_repr' (WithLp.toLp 2 ψ)
    calc (∑ j, inner ℂ (hH.eigenvectorBasis j) (WithLp.toLp 2 ψ) • ((hH.eigenvectorBasis j).ofLp))
        = (∑ j, inner ℂ (hH.eigenvectorBasis j) (WithLp.toLp 2 ψ) •
            hH.eigenvectorBasis j).ofLp := by simp
      _ = (WithLp.toLp 2 ψ).ofLp := by rw [h]
      _ = ψ := rfl

theorem exists_isOrthoEigenBasis (H : Matrix α α ℂ) (hH : H.IsHermitian) :
    ∃ (e : α → α → ℂ) (lam : α → ℝ), IsOrthoEigenBasis H e lam :=
  ⟨hermitianEigenBasis H hH, hH.eigenvalues, isOrthoEigenBasis_hermitian H hH⟩

/-- The spectral weight of a state on one eigenvector. -/
def eigenWeight (e : α → α → ℂ) (ψ : α → ℂ) (j : α) : ℝ :=
  ‖finiteComplexInner (e j) ψ‖ ^ (2 : ℕ)

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
  have hnorm : ((‖finiteComplexInner (e j) ψ‖ ^ (2 : ℕ) : ℝ) : ℂ) =
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
        (((1 - (lam j - lam k) ^ (2 : ℕ) / c : ℝ) : ℂ)) ^ m := by
  classical
  rw [regCollisionC]
  have hL : (∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * (-(1 : ℂ) / (c : ℂ)) ^ l *
        ∑ i ∈ Finset.range (2 * l + 1), (((2 * l).choose i : ℕ) : ℂ) * (-1 : ℂ) ^ i *
          (stateMoment H ψ (2 * l - i) * stateMoment H ψ i)) =
      ∑ l ∈ Finset.range (m + 1), ∑ j, ∑ k,
        ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
          ((-((((lam j - lam k) ^ (2 : ℕ) / c : ℝ) : ℂ))) ^ l * (1 : ℂ) ^ (m - l) *
            ((m.choose l : ℕ) : ℂ)) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_gap_pow hb ψ l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hpow : (((lam j - lam k : ℝ) : ℂ)) ^ (2 * l) =
        ((((lam j - lam k) ^ (2 : ℕ) : ℝ) : ℂ)) ^ l := by
      push_cast
      exact pow_mul _ 2 l
    rw [hpow, one_pow, Complex.ofReal_div,
      show (-(((((lam j - lam k) ^ (2 : ℕ) : ℝ) : ℂ)) / (c : ℂ))) =
        (-(1 : ℂ) / (c : ℂ)) * ((((lam j - lam k) ^ (2 : ℕ) : ℝ) : ℂ)) from by ring,
      mul_pow]
    ring
  have hR : (∑ j, ∑ k, ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
        (((1 - (lam j - lam k) ^ (2 : ℕ) / c : ℝ) : ℂ)) ^ m) =
      ∑ j, ∑ k, ∑ l ∈ Finset.range (m + 1),
        ((eigenWeight e ψ j * eigenWeight e ψ k : ℝ) : ℂ) *
          ((-((((lam j - lam k) ^ (2 : ℕ) / c : ℝ) : ℂ))) ^ l * (1 : ℂ) ^ (m - l) *
            ((m.choose l : ℕ) : ℂ)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hbin : (((1 - (lam j - lam k) ^ (2 : ℕ) / c : ℝ) : ℂ)) ^ m =
        ∑ l ∈ Finset.range (m + 1),
          (-((((lam j - lam k) ^ (2 : ℕ) / c : ℝ) : ℂ))) ^ l * (1 : ℂ) ^ (m - l) *
            ((m.choose l : ℕ) : ℂ) := by
      rw [show (((1 - (lam j - lam k) ^ (2 : ℕ) / c : ℝ) : ℂ)) =
          -((((lam j - lam k) ^ (2 : ℕ) / c : ℝ) : ℂ)) + 1 by push_cast; ring]
      exact add_pow _ _ _
    rw [hbin, Finset.mul_sum]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- The gap kernel of the regularization. -/
def collisionKernel (lam : α → ℝ) (c : ℝ) (m : ℕ) (j k : α) : ℝ :=
  (1 - (lam j - lam k) ^ (2 : ℕ) / c) ^ m

/-- The real gap-regularized collision. -/
def regCollision (c : ℝ) (m : ℕ) (H : Matrix α α ℂ) (ψ : α → ℂ) : ℝ :=
  (regCollisionC c m H ψ).re

theorem regCollision_eq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) (c : ℝ) (m : ℕ) :
    regCollision c m H ψ =
      ∑ j, ∑ k, eigenWeight e ψ j * eigenWeight e ψ k * collisionKernel lam c m j k := by
  rw [regCollision, regCollisionC_eq hb ψ c m, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [collisionKernel, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem collisionKernel_diag (lam : α → ℝ) (c : ℝ) (m : ℕ) (j : α) :
    collisionKernel lam c m j j = 1 := by
  rw [collisionKernel]
  norm_num

theorem collisionKernel_nonneg {lam : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hle : ∀ j k, (lam j - lam k) ^ (2 : ℕ) ≤ c) (m : ℕ) (j k : α) :
    0 ≤ collisionKernel lam c m j k := by
  refine pow_nonneg ?_ m
  rw [sub_nonneg, div_le_one hc]
  exact hle j k

theorem collisionKernel_le_one {lam : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hle : ∀ j k, (lam j - lam k) ^ (2 : ℕ) ≤ c) (m : ℕ) (j k : α) :
    collisionKernel lam c m j k ≤ 1 := by
  refine pow_le_one₀ ?_ ?_
  · rw [sub_nonneg, div_le_one hc]
    exact hle j k
  · have : (0 : ℝ) ≤ (lam j - lam k) ^ (2 : ℕ) / c := by positivity
    linarith

/-- **The regularization dominates the collision.** -/
theorem sum_eigenWeight_sq_le_regCollision {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) {c : ℝ} (hc : 0 < c)
    (hle : ∀ j k, (lam j - lam k) ^ (2 : ℕ) ≤ c) (m : ℕ) :
    (∑ j, eigenWeight e ψ j ^ (2 : ℕ)) ≤ regCollision c m H ψ := by
  rw [regCollision_eq hb ψ c m]
  refine Finset.sum_le_sum fun j _ => ?_
  have hdiag : eigenWeight e ψ j ^ (2 : ℕ) =
      eigenWeight e ψ j * eigenWeight e ψ j * collisionKernel lam c m j j := by
    rw [collisionKernel_diag, mul_one, sq]
  rw [hdiag]
  refine Finset.single_le_sum
    (f := fun k => eigenWeight e ψ j * eigenWeight e ψ k * collisionKernel lam c m j k)
    (fun k _ => ?_) (Finset.mem_univ j)
  exact mul_nonneg (mul_nonneg (eigenWeight_nonneg e ψ j) (eigenWeight_nonneg e ψ k))
    (collisionKernel_nonneg hc hle m j k)

theorem regCollision_le_sq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) {c : ℝ} (hc : 0 < c)
    (hle : ∀ j k, (lam j - lam k) ^ (2 : ℕ) ≤ c) (m : ℕ) :
    regCollision c m H ψ ≤ (∑ j, eigenWeight e ψ j) ^ (2 : ℕ) := by
  rw [regCollision_eq hb ψ c m, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
  calc eigenWeight e ψ j * eigenWeight e ψ k * collisionKernel lam c m j k
      ≤ eigenWeight e ψ j * eigenWeight e ψ k * 1 :=
        mul_le_mul_of_nonneg_left (collisionKernel_le_one hc hle m j k)
          (mul_nonneg (eigenWeight_nonneg e ψ j) (eigenWeight_nonneg e ψ k))
    _ = eigenWeight e ψ j * eigenWeight e ψ k := mul_one _

/-- **The regularization converges to the collision at a simple spectrum.** -/
theorem tendsto_regCollision {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) {c : ℝ} (hc : 0 < c)
    (hlt : ∀ j k, j ≠ k → (lam j - lam k) ^ (2 : ℕ) < c) (hinj : Function.Injective lam) :
    Filter.Tendsto (fun m => regCollision c m H ψ) Filter.atTop
      (nhds (∑ j, eigenWeight e ψ j ^ (2 : ℕ))) := by
  classical
  have hrw : (fun m => regCollision c m H ψ) =
      fun m => ∑ j, ∑ k, eigenWeight e ψ j * eigenWeight e ψ k * collisionKernel lam c m j k :=
    funext fun m => regCollision_eq hb ψ c m
  rw [hrw]
  have htarget : (∑ j, eigenWeight e ψ j ^ (2 : ℕ)) =
      ∑ j, ∑ k, (if j = k then eigenWeight e ψ j * eigenWeight e ψ k else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq (Finset.univ : Finset α) j
      (fun k => eigenWeight e ψ j * eigenWeight e ψ k), if_pos (Finset.mem_univ j), sq]
  rw [htarget]
  refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => ?_
  by_cases hjk : j = k
  · subst hjk
    have hconst : (fun m => eigenWeight e ψ j * eigenWeight e ψ j *
        collisionKernel lam c m j j) = fun _ => eigenWeight e ψ j * eigenWeight e ψ j := by
      funext m
      rw [collisionKernel_diag, mul_one]
    rw [hconst, if_pos rfl]
    exact tendsto_const_nhds
  · have hgap : 0 < (lam j - lam k) ^ (2 : ℕ) := by
      have hne : lam j - lam k ≠ 0 := sub_ne_zero.mpr fun hcon => hjk (hinj hcon)
      positivity
    have hbase : |1 - (lam j - lam k) ^ (2 : ℕ) / c| < 1 := by
      have h1 : 0 < (lam j - lam k) ^ (2 : ℕ) / c := div_pos hgap hc
      have h2 : (lam j - lam k) ^ (2 : ℕ) / c < 1 := (div_lt_one hc).mpr (hlt j k hjk)
      rw [abs_lt]
      constructor <;> linarith
    have hzero : Filter.Tendsto (fun m => collisionKernel lam c m j k) Filter.atTop (nhds 0) := by
      simpa [collisionKernel] using tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbase
    rw [if_neg hjk]
    simpa using (tendsto_const_nhds (x := eigenWeight e ψ j * eigenWeight e ψ k)
      (f := Filter.atTop (α := ℕ))).mul hzero

end Regularization

section Continuity

theorem continuous_matrixPow_entry (r : ℕ) (x y : α) :
    Continuous fun H : Matrix α α ℂ => (H ^ r) x y := by
  classical
  induction r generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      exact continuous_const.if_const _ continuous_const
  | succ r ih =>
      have hrw : ∀ H : Matrix α α ℂ, (H ^ (r + 1)) x y = ∑ z, H x z * (H ^ r) z y := by
        intro H
        rw [pow_succ']
        rfl
      simp only [hrw]
      refine continuous_finsetSum _ fun z _ => ?_
      refine Continuous.mul ?_ (ih z y)
      exact (continuous_apply z).comp (continuous_apply x)

theorem continuous_stateMoment (ψ : α → ℂ) (r : ℕ) :
    Continuous fun H : Matrix α α ℂ => stateMoment H ψ r := by
  classical
  have hrw : ∀ H : Matrix α α ℂ, stateMoment H ψ r =
      ∑ x, (starRingEnd ℂ) (ψ x) * ∑ y, (H ^ r) x y * ψ y := by
    intro H
    rw [stateMoment, finiteComplexInner]
    exact Finset.sum_congr rfl fun x _ => rfl
  simp only [hrw]
  refine continuous_finsetSum _ fun x _ => continuous_const.mul ?_
  exact continuous_finsetSum _ fun y _ => (continuous_matrixPow_entry r x y).mul continuous_const

/-- The squared Frobenius size of a matrix. -/
def frobSq (H : Matrix α α ℂ) : ℝ := ∑ a, ∑ b, ‖H a b‖ ^ (2 : ℕ)

theorem frobSq_nonneg (H : Matrix α α ℂ) : 0 ≤ frobSq H :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_frobSq : Continuous (frobSq (α := α)) := by
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (((continuous_apply b).comp (continuous_apply a)).norm).pow 2

/-- A gap cap that dominates every squared spectral gap. -/
def capC (H : Matrix α α ℂ) : ℝ := 1 + 4 * frobSq H

theorem capC_pos (H : Matrix α α ℂ) : 0 < capC H := by
  have := frobSq_nonneg H
  rw [capC]
  linarith

theorem continuous_capC : Continuous (capC (α := α)) :=
  continuous_const.add (continuous_const.mul continuous_frobSq)

theorem sum_normSq_eigenvector {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (j : α) : (∑ b, ‖e j b‖ ^ (2 : ℕ)) = 1 := by
  have h := hb.orth j j
  rw [if_pos rfl, finiteComplexInner] at h
  have hre : (∑ b, ((‖e j b‖ ^ (2 : ℕ) : ℝ) : ℂ)) = (1 : ℂ) := by
    rw [← h]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.sq_norm, ← Complex.mul_conj]
    ring
  rw [← Complex.ofReal_sum] at hre
  exact_mod_cast hre

theorem sq_lam_le_frobSq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (j : α) : (lam j) ^ (2 : ℕ) ≤ frobSq H := by
  classical
  have hunit := sum_normSq_eigenvector hb j
  have hrow : ∀ a : α, ‖(H *ᵥ e j) a‖ ^ (2 : ℕ) ≤ ∑ b, ‖H a b‖ ^ (2 : ℕ) := by
    intro a
    have hcs : (∑ b, ‖H a b‖ * ‖e j b‖) ^ (2 : ℕ) ≤
        (∑ b, ‖H a b‖ ^ (2 : ℕ)) * ∑ b, ‖e j b‖ ^ (2 : ℕ) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [hunit, mul_one] at hcs
    have hbound : ‖(H *ᵥ e j) a‖ ≤ ∑ b, ‖H a b‖ * ‖e j b‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hbound 2) hcs
  have heig : ∀ a : α, ‖(H *ᵥ e j) a‖ ^ (2 : ℕ) = (lam j) ^ (2 : ℕ) * ‖e j a‖ ^ (2 : ℕ) := by
    intro a
    rw [hb.eigen j]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
  have hsum : (lam j) ^ (2 : ℕ) = ∑ a, ‖(H *ᵥ e j) a‖ ^ (2 : ℕ) := by
    rw [Finset.sum_congr rfl fun a _ => heig a, ← Finset.mul_sum, hunit, mul_one]
  rw [hsum, frobSq]
  exact Finset.sum_le_sum fun a _ => hrow a

theorem sq_gap_lt_capC {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (j k : α) : (lam j - lam k) ^ (2 : ℕ) < capC H := by
  have hj := sq_lam_le_frobSq hb j
  have hk := sq_lam_le_frobSq hb k
  have hexp : (lam j - lam k) ^ (2 : ℕ) ≤ 2 * (lam j) ^ (2 : ℕ) + 2 * (lam k) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (lam j + lam k)]
  rw [capC]
  linarith

theorem sq_gap_le_capC {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (j k : α) : (lam j - lam k) ^ (2 : ℕ) ≤ capC H :=
  le_of_lt (sq_gap_lt_capC hb j k)

/-- The gap-capped regularization of the collision: a continuous function of the matrix. -/
def cappedRegCollision (m : ℕ) (H : Matrix α α ℂ) (ψ : α → ℂ) : ℝ :=
  regCollision (capC H) m H ψ

theorem continuous_cappedRegCollision (m : ℕ) (ψ : α → ℂ) :
    Continuous fun H : Matrix α α ℂ => cappedRegCollision m H ψ := by
  classical
  have hden : Continuous fun H : Matrix α α ℂ => (((capC H : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_capC
  have hne : ∀ H : Matrix α α ℂ, (((capC H : ℝ)) : ℂ) ≠ 0 := by
    intro H
    exact_mod_cast ne_of_gt (capC_pos H)
  have hC : Continuous fun H : Matrix α α ℂ => regCollisionC (capC H) m H ψ := by
    refine continuous_finsetSum _ fun l _ => ?_
    refine Continuous.mul (continuous_const.mul ((continuous_const.div hden hne).pow l)) ?_
    refine continuous_finsetSum _ fun i _ => ?_
    exact continuous_const.mul
      ((continuous_stateMoment ψ (2 * l - i)).mul (continuous_stateMoment ψ i))
  exact Complex.continuous_re.comp hC

/-- **The capped regularization dominates the collision.** -/
theorem sum_eigenWeight_sq_le_cappedRegCollision {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) (m : ℕ) :
    (∑ j, eigenWeight e ψ j ^ (2 : ℕ)) ≤ cappedRegCollision m H ψ :=
  sum_eigenWeight_sq_le_regCollision hb ψ (capC_pos H) (fun j k => sq_gap_le_capC hb j k) m

theorem cappedRegCollision_le_sq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) (m : ℕ) :
    cappedRegCollision m H ψ ≤ (∑ j, eigenWeight e ψ j) ^ (2 : ℕ) :=
  regCollision_le_sq hb ψ (capC_pos H) (fun j k => sq_gap_le_capC hb j k) m

/-- **The capped regularization converges to the collision at a simple spectrum.** -/
theorem tendsto_cappedRegCollision {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) (hinj : Function.Injective lam) :
    Filter.Tendsto (fun m => cappedRegCollision m H ψ) Filter.atTop
      (nhds (∑ j, eigenWeight e ψ j ^ (2 : ℕ))) :=
  tendsto_regCollision hb ψ (capC_pos H) (fun j k _ => sq_gap_lt_capC hb j k) hinj

end Continuity

end GaloisForLFunctions.HTGeometry
