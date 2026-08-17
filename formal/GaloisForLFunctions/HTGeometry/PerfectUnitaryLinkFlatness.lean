import GaloisForLFunctions.HTGeometry.ContextOrderRobustHilbertization

/-!
# Perfect unitary links force flat holonomy

A normalized positive block kernel has a common Gram realization by orthonormal context frames. If
one cross-Gram block is unitary, equality in Bessel's inequality forces exact reconstruction of the
target frame from the source frame. Therefore a network whose every link is unitary obeys the exact
cocycle law, and every triangular Wilson loop is the identity.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

variable {A E : Type*} [Fintype A] [DecidableEq A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Cross-Gram matrix between two finite Hilbert-space frames. -/
def crossInnerMatrix (v w : A → E) : Matrix A A ℂ :=
  fun a b => inner ℂ (v a) (w b)

/-- **Bessel saturation.** A unitary cross-Gram matrix between orthonormal frames reconstructs the
second frame exactly from the first. -/
theorem orthonormal_reconstruct_of_crossInnerMatrix_unitary
    {v w : A → E} (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (hU : crossInnerMatrix v w ∈ Matrix.unitaryGroup A ℂ) (b : A) :
    w b = ∑ a, crossInnerMatrix v w a b • v a := by
  let p : E := ∑ a, crossInnerMatrix v w a b • v a
  have hcol : ∑ a, star (crossInnerMatrix v w a b) * crossInnerMatrix v w a b = 1 := by
    have hunit := Matrix.mem_unitaryGroup_iff'.mp hU
    have hab := congrFun (congrFun hunit b) b
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using hab
  have hww : inner ℂ (w b) (w b) = 1 := by
    simpa using (orthonormal_iff_ite.mp hw b b)
  have hwp : inner ℂ (w b) p = 1 := by
    rw [show p = ∑ a, crossInnerMatrix v w a b • v a from rfl]
    simp_rw [inner_sum, inner_smul_right]
    calc
      ∑ x, crossInnerMatrix v w x b * inner ℂ (w b) (v x) =
          ∑ x, crossInnerMatrix v w x b * star (crossInnerMatrix v w x b) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [crossInnerMatrix]
            congr 1
            exact (inner_conj_symm (𝕜 := ℂ) (w b) (v x)).symm
      _ = 1 := by simpa only [mul_comm] using hcol
  have hpw : inner ℂ p (w b) = 1 := by
    calc
      inner ℂ p (w b) = star (inner ℂ (w b) p) :=
        (inner_conj_symm (𝕜 := ℂ) p (w b)).symm
      _ = 1 := by rw [hwp]; simp
  have hpp : inner ℂ p p = 1 := by
    change inner ℂ (∑ a ∈ Finset.univ, crossInnerMatrix v w a b • v a)
      (∑ a ∈ Finset.univ, crossInnerMatrix v w a b • v a) = 1
    rw [hv.inner_sum (fun a => crossInnerMatrix v w a b)
      (fun a => crossInnerMatrix v w a b) Finset.univ]
    simpa using hcol
  have hz : w b - p = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp <| by
    calc
      inner ℂ (w b - p) (w b - p) =
        inner ℂ (w b) (w b) - inner ℂ p (w b) -
          (inner ℂ (w b) p - inner ℂ p p) := by
            simp only [inner_sub_left, inner_sub_right]
      _ = 0 := by rw [hww, hwp, hpw, hpp]; ring
  change w b = p
  exact sub_eq_zero.mp hz

/-- Cross-context block of a normalized kernel. -/
def NormalizedBlockKernel.link {I A : Type*} [DecidableEq A]
    (K : NormalizedBlockKernel I A) (i j : I) : Matrix A A ℂ :=
  fun a b => K.matrix (i, a) (j, b)

/-- Normalized PSD kernel all of whose cross-context blocks are unitary. -/
structure PerfectUnitaryLinkKernel (I A : Type*) [Fintype A] [DecidableEq A]
    extends NormalizedBlockKernel I A where
  posSemidef : matrix.PosSemidef
  link_unitary : ∀ i j, toNormalizedBlockKernel.link i j ∈ Matrix.unitaryGroup A ℂ

/-- A normalized link from a context to itself is the identity. -/
theorem PerfectUnitaryLinkKernel.link_self
    {I A : Type*} [Fintype A] [DecidableEq A]
    (K : PerfectUnitaryLinkKernel I A) (i : I) :
    K.toNormalizedBlockKernel.link i i = 1 := by
  ext a b
  exact K.diagonalBlock i a b

/-- **Perfect-link cocycle law.** Positivity and unitary cross-links force exact composition. -/
theorem PerfectUnitaryLinkKernel.link_cocycle
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]
    (K : PerfectUnitaryLinkKernel I A) (i j k : I) :
    K.toNormalizedBlockKernel.link i j * K.toNormalizedBlockKernel.link j k =
      K.toNormalizedBlockKernel.link i k := by
  classical
  obtain ⟨v, hvK, hv⟩ :=
    (normalizedBlockKernel_posSemidef_iff_exists_orthonormal_frames
      K.toNormalizedBlockKernel).mp K.posSemidef
  have hlink (x y : I) :
      K.toNormalizedBlockKernel.link x y =
        crossInnerMatrix (fun a => v (x, a)) (fun b => v (y, b)) := by
    ext a b
    rw [NormalizedBlockKernel.link, hvK, innerGramMatrix_apply]
    rfl
  have hreconstruct (x y : I) (b : A) :
      v (y, b) = ∑ a, K.toNormalizedBlockKernel.link x y a b • v (x, a) := by
    rw [hlink]
    exact orthonormal_reconstruct_of_crossInnerMatrix_unitary
      (hv x) (hv y) (by simpa only [hlink] using K.link_unitary x y) b
  ext a c
  rw [Matrix.mul_apply]
  calc
    ∑ b, K.toNormalizedBlockKernel.link i j a b *
          K.toNormalizedBlockKernel.link j k b c =
        inner ℂ (v (i, a))
          (∑ b, K.toNormalizedBlockKernel.link j k b c • v (j, b)) := by
            simp_rw [inner_sum, inner_smul_right]
            apply Finset.sum_congr rfl
            intro b _
            rw [hlink i j, crossInnerMatrix]
            ring
    _ = inner ℂ (v (i, a)) (v (k, c)) := by rw [← hreconstruct j k c]
    _ = K.toNormalizedBlockKernel.link i k a c := by rw [hlink]; rfl

/-- **Flat triangular holonomy.** Every perfect-link Wilson triangle is the identity. -/
theorem PerfectUnitaryLinkKernel.triangle_holonomy
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]
    (K : PerfectUnitaryLinkKernel I A) (i j k : I) :
    K.toNormalizedBlockKernel.link i j * K.toNormalizedBlockKernel.link j k *
        K.toNormalizedBlockKernel.link k i = 1 := by
  rw [K.link_cocycle i j k, K.link_cocycle i k i, K.link_self i]

end

end GaloisForLFunctions.HTGeometry
