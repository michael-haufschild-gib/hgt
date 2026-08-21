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

/-! ### Full `S₃`-equivariance of the orientation line

Relabeling is a group action, so the sign law for the whole symmetric group follows from the
single-transposition law by the standard generation-by-transpositions induction.  No enumeration
of the six permutations is used.
-/

theorem triangleRelabel_one {R : Type*} (c : Matrix (Fin 3) (Fin 3) R) :
    triangleRelabel 1 c = c := rfl

theorem triangleRelabel_mul {R : Type*} (σ τ : Equiv.Perm (Fin 3))
    (c : Matrix (Fin 3) (Fin 3) R) :
    triangleRelabel (σ * τ) c = triangleRelabel σ (triangleRelabel τ c) := rfl

theorem triangleRelabel_zsmul {R : Type*} [Ring R] (σ : Equiv.Perm (Fin 3)) (m : ℤ)
    (c : Matrix (Fin 3) (Fin 3) R) :
    triangleRelabel σ (m • c) = m • triangleRelabel σ c := rfl

/-- Every vertex transposition reverses the oriented boundary cycle. -/
theorem triangleRelabel_swap_orientationCycle (R : Type*) [Ring R] {a b : Fin 3} (hab : a ≠ b) :
    triangleRelabel (Equiv.swap a b) (triangleOrientationCycle R) =
      -triangleOrientationCycle R := by
  have hpair : ∀ p q : Fin 3, p ≠ q →
      triangleRelabel (Equiv.swap p q) (triangleOrientationCycle R)
        = -triangleOrientationCycle R := by
    have h01 : triangleRelabel (Equiv.swap (0 : Fin 3) 1) (triangleOrientationCycle R)
        = -triangleOrientationCycle R := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [triangleRelabel, triangleOrientationCycle, Equiv.swap_apply_def]
    have h02 : triangleRelabel (Equiv.swap (0 : Fin 3) 2) (triangleOrientationCycle R)
        = -triangleOrientationCycle R := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [triangleRelabel, triangleOrientationCycle, Equiv.swap_apply_def]
    have h12 : triangleRelabel (Equiv.swap (1 : Fin 3) 2) (triangleOrientationCycle R)
        = -triangleOrientationCycle R := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [triangleRelabel, triangleOrientationCycle, Equiv.swap_apply_def]
    have h10 : triangleRelabel (Equiv.swap (1 : Fin 3) 0) (triangleOrientationCycle R)
        = -triangleOrientationCycle R := by rw [Equiv.swap_comm]; exact h01
    have h20 : triangleRelabel (Equiv.swap (2 : Fin 3) 0) (triangleOrientationCycle R)
        = -triangleOrientationCycle R := by rw [Equiv.swap_comm]; exact h02
    have h21 : triangleRelabel (Equiv.swap (2 : Fin 3) 1) (triangleOrientationCycle R)
        = -triangleOrientationCycle R := by rw [Equiv.swap_comm]; exact h12
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all
  exact hpair a b hab

/-- **Full `S₃`-equivariance.**  The orientation line carries the sign representation: every
vertex relabeling acts on the oriented boundary cycle by the sign of the permutation. -/
theorem triangleRelabel_orientationCycle (R : Type*) [Ring R] (σ : Equiv.Perm (Fin 3)) :
    triangleRelabel σ (triangleOrientationCycle R) =
      ((Equiv.Perm.sign σ : ℤ)) • triangleOrientationCycle R := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · simp [triangleRelabel_one]
  · intro f x y hxy hf
    rw [triangleRelabel_mul, hf, triangleRelabel_zsmul,
      triangleRelabel_swap_orientationCycle R hxy, map_mul, Equiv.Perm.sign_swap hxy,
      smul_neg, ← neg_smul]
    congr 1
    simp

/-- The sign action on the residual coefficient, for every permutation. -/
theorem triangleRelabel_orientationResidual (σ : Equiv.Perm (Fin 3)) (a : ℂ) :
    triangleRelabel σ (triangleOrientationResidual a) =
      triangleOrientationResidual (((Equiv.Perm.sign σ : ℤ) : ℂ) * a) := by
  rw [triangleOrientationResidual, triangleRelabel_smul, triangleRelabel_orientationCycle,
    triangleOrientationResidual]
  ext i j
  simp only [Matrix.smul_apply]
  simp only [smul_eq_mul, zsmul_eq_mul]
  ring

/-! ### The invariant subspace of the antisymmetric edge module vanishes -/

/-- Antisymmetric edge fields. -/
def TriangleAntisymm {R : Type*} [Ring R] (c : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ i j, c i j = -c j i

theorem triangleAntisymm_orientationCycle (R : Type*) [Ring R] :
    TriangleAntisymm (triangleOrientationCycle R) := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [triangleOrientationCycle]

/-- **Equation `(4)` for the whole exterior square.**  Over a ring without `2`-torsion, the only
relabeling-invariant antisymmetric edge field is zero; in particular the exterior square has no
trivial summand, so neither `Std` nor `Sgn` contributes an invariant vector. -/
theorem triangleAntisymm_sourceNatural_eq_zero {R : Type*} [Ring R] [NoZeroDivisors R]
    [CharZero R] {c : Matrix (Fin 3) (Fin 3) R} (hanti : TriangleAntisymm c)
    (hnat : TriangleSourceNatural c) : c = 0 := by
  ext i j
  rcases eq_or_ne i j with hij | hij
  · subst hij
    have h := hanti i i
    have h2 : (2 : R) * c i i = 0 := by
      have hsum : c i i + c i i = 0 := by
        nth_rewrite 2 [h]
        exact add_neg_cancel _
      rw [two_mul]
      exact hsum
    have := (mul_eq_zero.mp h2).resolve_left (two_ne_zero)
    simpa using this
  · have hswap := congrFun (congrFun (hnat (Equiv.swap i j)) i) j
    have hval : c j i = c i j := by
      have hi : (Equiv.swap i j).symm i = j := by simp [Equiv.swap_apply_left]
      have hj : (Equiv.swap i j).symm j = i := by simp [Equiv.swap_apply_right]
      rw [triangleRelabel, hi, hj] at hswap
      exact hswap
    have h := hanti i j
    rw [hval] at h
    have h2 : (2 : R) * c i j = 0 := by
      have hsum : c i j + c i j = 0 := by
        nth_rewrite 2 [h]
        exact add_neg_cancel _
      rw [two_mul]
      exact hsum
    have := (mul_eq_zero.mp h2).resolve_left (two_ne_zero)
    simpa using this

/-! ### The kernel of the edge boundary is the orientation line -/

/-- The antisymmetric matrix attached to edge coordinates `(01, 02, 12)`. -/
def triangleEdgeMatrix {R : Type*} [Ring R] (x : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, x 0, x 1;
     -x 0, 0, x 2;
     -x 1, -x 2, 0]

theorem triangleEdgeMatrix_fillerBoundary (R : Type*) [Ring R] (a : R) :
    triangleEdgeMatrix (triangleFillerBoundary R a) = a • triangleOrientationCycle R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleEdgeMatrix, triangleFillerBoundary, triangleOrientationCycle,
      Matrix.smul_apply]

/-- **Equation `(3)`, matrix form.**  The kernel of the edge boundary is exactly the orientation
line, on which `S₃` acts by the sign character. -/
theorem triangleEdgeBoundary_eq_zero_iff_orientationLine {R : Type*} [Ring R]
    (x : Fin 3 → R) :
    triangleEdgeBoundary x = 0 ↔
      ∃ a : R, triangleEdgeMatrix x = a • triangleOrientationCycle R := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (triangleEdgeBoundary_eq_zero_iff x).mp h
    exact ⟨a, by rw [ha, triangleEdgeMatrix_fillerBoundary]⟩
  · rintro ⟨a, ha⟩
    have hx : x = triangleFillerBoundary R a := by
      have h0 := congrFun (congrFun ha (0 : Fin 3)) (1 : Fin 3)
      have h1 := congrFun (congrFun ha (0 : Fin 3)) (2 : Fin 3)
      have h2 := congrFun (congrFun ha (1 : Fin 3)) (2 : Fin 3)
      simp [triangleEdgeMatrix, triangleOrientationCycle, Matrix.smul_apply] at h0 h1 h2
      ext i
      fin_cases i <;> simp [triangleFillerBoundary, h0, h1, h2]
    rw [hx]
    exact triangleEdgeBoundary_fillerBoundary R a


end GaloisForLFunctions.HTGeometry
