import GaloisForLFunctions.HTGeometry.MomentInnerProduct

/-!
# Null-root division as a spectral law

For a symmetric bilinear form, division of one radical vector by distinct spectral roots does not
create independent scalar constraints.  Self-adjointness of the coordinate operator forces the
root-deleted descendants to be pairwise orthogonal.  A repeated division is isotropic; in a
positive-semidefinite form it therefore lies in the radical.

This is the exact algebra behind root-division Cauchy equations at a hard spectral edge.  It
classifies what those equations can detect: distinct roots produce orthogonal descendants, while
multiple roots enlarge the nullspace.
-/

namespace HTGeometry

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- A coordinate operator is self-adjoint for a bilinear form when it can be moved between the
two slots without changing the pairing. -/
def BilinSelfAdjoint (B : LinearMap.BilinForm ℝ M) (T : M →ₗ[ℝ] M) : Prop :=
  ∀ x y, B (T x) y = B x (T y)

/-- **Distinct root deletions are orthogonal.**  If `f` is radical and both `q` and `p` map to
`f` under distinct shifted coordinate operators, their pairing vanishes. -/
theorem rootDeletion_orthogonal
    (B : LinearMap.BilinForm ℝ M) (T : M →ₗ[ℝ] M)
    (hB : B.IsSymm) (hT : BilinSelfAdjoint B T)
    {f q p : M} {r s : ℝ}
    (hf : ∀ v, B f v = 0)
    (hq : T q - r • q = f) (hp : T p - s • p = f)
    (hrs : r ≠ s) :
    B q p = 0 := by
  have hr : B (T q - r • q) p = 0 := by
    rw [hq]
    exact hf p
  have hs : B q (T p - s • p) = 0 := by
    rw [hp, ← hB.eq f q, hf q]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at hr hs
  rw [hT q p] at hr
  have hzero : (s - r) * B q p = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hrs.symm)

/-- Family form of root-deletion orthogonality.  An injectively labelled shifted-coordinate
factorization of one radical vector is pairwise orthogonal. -/
theorem rootDeletion_pairwise_orthogonal
    {ι : Type*} (B : LinearMap.BilinForm ℝ M) (T : M →ₗ[ℝ] M)
    (hB : B.IsSymm) (hT : BilinSelfAdjoint B T)
    {f : M} (root : ι → ℝ) (deleted : ι → M)
    (hf : ∀ v, B f v = 0)
    (hdeleted : ∀ i, T (deleted i) - root i • deleted i = f)
    (hroot : Function.Injective root) :
    ∀ i j, i ≠ j → B (deleted i) (deleted j) = 0 := by
  intro i j hij
  exact rootDeletion_orthogonal B T hB hT hf (hdeleted i) (hdeleted j)
    (hroot.ne hij)

/-- **A repeated root deletion is isotropic.**  A two-step Jordan chain ending at a radical
vector has zero middle energy for every self-adjoint coordinate operator. -/
theorem repeatedRootDeletion_isotropic
    (B : LinearMap.BilinForm ℝ M) (T : M →ₗ[ℝ] M)
    (hT : BilinSelfAdjoint B T)
    {f h q : M} {r : ℝ}
    (hf : ∀ v, B f v = 0)
    (hh : T h - r • h = f) (hq : T q - r • q = h) :
    B h h = 0 := by
  calc
    B h h = B h (T q - r • q) := by rw [hq]
    _ = B (T h - r • h) q := by
      simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      rw [hT h q]
    _ = B f q := by rw [hh]
    _ = 0 := hf q

/-- In a positive-semidefinite form, the isotropic middle vector produced by a repeated root
deletion belongs to the full radical.  Thus repeated roots force kernel enlargement. -/
theorem repeatedRootDeletion_mem_ker
    (B : LinearMap.BilinForm ℝ M) (T : M →ₗ[ℝ] M)
    (hB : B.IsPosSemidef) (hT : BilinSelfAdjoint B T)
    {f h q : M} {r : ℝ}
    (hf : ∀ v, B f v = 0)
    (hh : T h - r • h = f) (hq : T q - r • q = h) :
    h ∈ LinearMap.ker B := by
  apply (B.apply_apply_same_eq_zero_iff hB.isNonneg.nonneg
    (LinearMap.BilinForm.isSymm_iff.mp hB.isSymm)).mp
  exact repeatedRootDeletion_isotropic B T hT hf hh hq

/-! ## Literal moment-form specialization -/

open Polynomial

/-- Expanding one shifted coordinate factor in the literal polynomial moment form. -/
theorem momentInner_X_sub_C_mul
    (moments : ℕ → ℝ) (q p : Polynomial ℝ) (r : ℝ) :
    momentInner moments ((X - C r) * q) p =
      momentInner moments (X * q) p - r * momentInner moments q p := by
  rw [sub_mul, sub_eq_add_neg, momentInner_add_left]
  have hneg : -(C r * q) = (-r) • q := by
    rw [Polynomial.smul_eq_C_mul, C_neg]
    ring
  rw [hneg, momentInner_smul_left]
  ring

/-- The polynomial moment form is self-adjoint for every shifted coordinate operator. -/
theorem momentInner_X_sub_C_mul_selfAdjoint
    (moments : ℕ → ℝ) (q p : Polynomial ℝ) (r : ℝ) :
    momentInner moments ((X - C r) * q) p =
      momentInner moments q ((X - C r) * p) := by
  rw [momentInner_X_sub_C_mul,
    momentInner_comm moments q ((X - C r) * p), momentInner_X_sub_C_mul,
    momentInner_comm moments (X * q) p, momentInner_X_mul moments p q,
    momentInner_comm moments q p]

/-- **Literal moment root divisions are orthogonal.**  Two distinct polynomial root deletions of
one moment-radical polynomial have zero mixed moment. -/
theorem momentInner_rootDivisions_orthogonal
    {moments : ℕ → ℝ} {f q p : Polynomial ℝ} {r s : ℝ}
    (hf : ∀ v, momentInner moments f v = 0)
    (hq : (X - C r) * q = f) (hp : (X - C s) * p = f)
    (hrs : r ≠ s) :
    momentInner moments q p = 0 := by
  have hr : momentInner moments ((X - C r) * q) p = 0 := by
    rw [hq]
    exact hf p
  have hs : momentInner moments q ((X - C s) * p) = 0 := by
    rw [hp, momentInner_comm, hf q]
  rw [momentInner_X_sub_C_mul] at hr
  rw [momentInner_comm, momentInner_X_sub_C_mul,
    momentInner_comm moments (X * p) q, momentInner_comm moments p q] at hs
  rw [momentInner_X_mul] at hr
  have hzero : (s - r) * momentInner moments q p = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hrs.symm)

/-- A repeated polynomial root deletion has zero middle moment energy. -/
theorem momentInner_repeatedRootDeletion_isotropic
    {moments : ℕ → ℝ} {f h q : Polynomial ℝ} {r : ℝ}
    (hf : ∀ v, momentInner moments f v = 0)
    (hh : (X - C r) * h = f) (hq : (X - C r) * q = h) :
    momentInner moments h h = 0 := by
  calc
    momentInner moments h h =
        momentInner moments h ((X - C r) * q) := by rw [hq]
    _ = momentInner moments ((X - C r) * h) q := by
      rw [momentInner_X_sub_C_mul_selfAdjoint]
    _ = momentInner moments f q := by rw [hh]
    _ = 0 := hf q

/-- Strict positive moment admission excludes a nonzero repeated root-deletion chain ending in a
radical polynomial. -/
theorem no_repeatedRootDeletion_of_positiveMomentForm
    {moments : ℕ → ℝ} (hpos : PositiveMomentForm moments)
    {f h q : Polynomial ℝ} {r : ℝ}
    (hf : ∀ v, momentInner moments f v = 0)
    (hh : (X - C r) * h = f) (hq : (X - C r) * q = h)
    (hne : h ≠ 0) : False := by
  exact hne (hpos.eq_zero_of_self_eq_zero
    (momentInner_repeatedRootDeletion_isotropic hf hh hq))

end HTGeometry
