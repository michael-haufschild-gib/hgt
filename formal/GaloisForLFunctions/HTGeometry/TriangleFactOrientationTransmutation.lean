import Mathlib

/-!
# Triangle fact-to-orientation transmutation

The oriented boundary cycle of an empty triangle reverses under a transposition of two vertices.
Consequently no nonzero scalar multiple of that cycle is natural under every relabeling of the
unlabeled source.

This is the exact finite no-selection core of the paper theorem that the empty triangle's
rank-one disagreement transforms as an orientation/sign line.  The present module deliberately
proves only the explicit source-symmetry statement; it gives no physical interpretation to the
matrix, its relabelings, or its residual coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The antisymmetric oriented boundary cycle
`0 → 1 → 2 → 0` of the empty triangle. -/
def triangleOrientationCycle (R : Type*) [Ring R] :
    Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, -1;
     -1, 0, 1;
     1, -1, 0]

/-- The source automorphism interchanging the first two triangle vertices. -/
def triangleSwap01 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1

/-- Relabel an oriented edge field by a permutation of its source vertices. -/
def triangleRelabel {R : Type*} (σ : Equiv.Perm (Fin 3))
    (c : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  fun i j => c (σ.symm i) (σ.symm j)

/-- Swapping two vertices reverses the triangle's oriented boundary cycle. -/
theorem triangleRelabel_swap01_orientationCycle (R : Type*) [Ring R] :
    triangleRelabel triangleSwap01 (triangleOrientationCycle R) =
      -triangleOrientationCycle R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleRelabel, triangleSwap01, triangleOrientationCycle,
      Equiv.swap_apply_def]

/-- Relabeling commutes with scalar multiplication of an edge field. -/
theorem triangleRelabel_smul {R : Type*} [Semiring R]
    (σ : Equiv.Perm (Fin 3)) (a : R)
    (c : Matrix (Fin 3) (Fin 3) R) :
    triangleRelabel σ (a • c) = a • triangleRelabel σ c := by
  rfl

/-- A complex coefficient on the rank-one oriented triangle residual. -/
def triangleOrientationResidual (a : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  a • triangleOrientationCycle ℂ

/-- The source transposition sends a residual coefficient to its negative. -/
theorem triangleRelabel_swap01_orientationResidual (a : ℂ) :
    triangleRelabel triangleSwap01 (triangleOrientationResidual a) =
      triangleOrientationResidual (-a) := by
  rw [triangleOrientationResidual, triangleRelabel_smul,
    triangleRelabel_swap01_orientationCycle, triangleOrientationResidual]
  ext i j
  simp

/-- Source-natural edge data are fixed under every vertex relabeling. -/
def TriangleSourceNatural {R : Type*}
    (c : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3), triangleRelabel σ c = c

/-- The oriented residual parameterization has trivial kernel. -/
theorem triangleOrientationResidual_eq_zero_iff (a : ℂ) :
    triangleOrientationResidual a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h (0 : Fin 3)) (1 : Fin 3)
    simpa [triangleOrientationResidual, triangleOrientationCycle] using h01
  · rintro rfl
    ext i j
    simp [triangleOrientationResidual]

/-- A residual is invariant under the single orientation-reversing source automorphism exactly
when it is zero. -/
theorem triangleOrientationResidual_swap01_invariant_iff (a : ℂ) :
    triangleRelabel triangleSwap01 (triangleOrientationResidual a) =
      triangleOrientationResidual a ↔ a = 0 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h (0 : Fin 3)) (1 : Fin 3)
    simp [triangleRelabel, triangleSwap01, triangleOrientationResidual,
      triangleOrientationCycle] at h01
    have hsum : a + a = 0 := by
      nth_rewrite 2 [← h01]
      exact add_neg_cancel a
    have htwo : (2 : ℂ) * a = 0 := by
      simpa [two_mul] using hsum
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  · rintro rfl
    ext i j
    simp [triangleRelabel, triangleOrientationResidual]

/-- **Static self-witness no-selection theorem.** No nonzero multiple of the triangle orientation
cycle is natural under every automorphism of the unlabeled three-vertex source. -/
theorem triangleOrientationResidual_sourceNatural_iff (a : ℂ) :
    TriangleSourceNatural (triangleOrientationResidual a) ↔ a = 0 := by
  constructor
  · intro h
    exact (triangleOrientationResidual_swap01_invariant_iff a).mp
      (h triangleSwap01)
  · rintro rfl σ
    ext i j
    simp [triangleRelabel, triangleOrientationResidual]

/-! ### Explicit augmented triangle exactness -/

/-- The oriented boundary of a scalar triangle filler in edge coordinates `(01, 02, 12)`. -/
def triangleFillerBoundary (R : Type*) [Ring R] (a : R) : Fin 3 → R :=
  ![a, -a, a]

/-- The oriented boundary from edge coordinates `(01, 02, 12)` to the three vertices. -/
def triangleEdgeBoundary {R : Type*} [Ring R] (x : Fin 3 → R) : Fin 3 → R :=
  ![-x 0 - x 1, x 0 - x 2, x 1 + x 2]

/-- Augmentation of the three vertex coefficients. -/
def triangleVertexAugmentation {R : Type*} [Ring R] (v : Fin 3 → R) : R :=
  v 0 + v 1 + v 2

/-- A filler boundary has no vertex boundary. -/
theorem triangleEdgeBoundary_fillerBoundary
    (R : Type*) [Ring R] (a : R) :
    triangleEdgeBoundary (triangleFillerBoundary R a) = 0 := by
  ext i
  fin_cases i <;>
    simp [triangleEdgeBoundary, triangleFillerBoundary]

/-- Every edge boundary has zero augmentation. -/
theorem triangleVertexAugmentation_edgeBoundary
    {R : Type*} [Ring R] (x : Fin 3 → R) :
    triangleVertexAugmentation (triangleEdgeBoundary x) = 0 := by
  simp [triangleVertexAugmentation, triangleEdgeBoundary]
  noncomm_ring

/-- The triangle filler boundary is injective over every ring. -/
theorem triangleFillerBoundary_injective
    (R : Type*) [Ring R] :
    Function.Injective (triangleFillerBoundary R) := by
  intro a b h
  have h0 := congrFun h (0 : Fin 3)
  simpa [triangleFillerBoundary] using h0

/-- Exactness at the three-dimensional oriented edge layer: every loop is the boundary of one
unique scalar filler. -/
theorem triangleEdgeBoundary_eq_zero_iff
    {R : Type*} [Ring R] (x : Fin 3 → R) :
    triangleEdgeBoundary x = 0 ↔
      ∃ a : R, x = triangleFillerBoundary R a := by
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 3)
    have h1 := congrFun h (1 : Fin 3)
    simp [triangleEdgeBoundary] at h0 h1
    have hx1 : x 1 = -x 0 := by
      have h0' : -x 0 = x 1 := calc
        -x 0 = (-x 0 - x 1) + x 1 := (sub_add_cancel (-x 0) (x 1)).symm
        _ = 0 + x 1 := by rw [h0]
        _ = x 1 := zero_add _
      exact h0'.symm
    have hx2 : x 2 = x 0 := by
      have h1' : x 0 = x 2 := calc
        x 0 = (x 0 - x 2) + x 2 := (sub_add_cancel (x 0) (x 2)).symm
        _ = 0 + x 2 := by rw [h1]
        _ = x 2 := zero_add _
      exact h1'.symm
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i <;>
      simp [triangleFillerBoundary, hx1, hx2]
  · rintro ⟨a, rfl⟩
    exact triangleEdgeBoundary_fillerBoundary R a

/-- Exactness at the three-dimensional vertex layer: every zero-sum vertex field is an edge
boundary. -/
theorem triangleVertexAugmentation_eq_zero_iff
    {R : Type*} [Ring R] (v : Fin 3 → R) :
    triangleVertexAugmentation v = 0 ↔
      ∃ x : Fin 3 → R, triangleEdgeBoundary x = v := by
  constructor
  · intro h
    refine ⟨![v 1, v 2, 0], ?_⟩
    ext i
    fin_cases i
    · change -v 1 - v 2 = v 0
      have hv0 : v 0 = -(v 1 + v 2) :=
        eq_neg_of_add_eq_zero_left (by
          simpa [triangleVertexAugmentation, add_assoc] using h)
      rw [hv0]
      abel
    · change v 1 - 0 = v 1
      simp
    · change v 2 + 0 = v 2
      simp
  · rintro ⟨x, rfl⟩
    exact triangleVertexAugmentation_edgeBoundary x

end GaloisForLFunctions.HTGeometry
