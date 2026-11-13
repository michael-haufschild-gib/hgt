import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TwoCoupledWindowsAreBracketedByLoweredAndRaisedPotentialsAndGluedThroughResponseMatrices
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheStepPacketMatricesOfARatioAreDecidedOnCoarseBlocks
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks
import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia

/-!
# A window glues its two overlapping parts through its dyadic middle

Write the window `W = (R, 2D + b]`, `D = R + a`, as a left end `(R, D]` of `a` blocks, the dyadic
middle `M = (D, 2D]` and a right end `(2D, 2D + b]` of `b` blocks. Its two **parts**
`A = (R, 2D]` and `A' = (D, 2D + b]` overlap in `M`, and both contain a dyadic window.

The middle is invertible and holds exactly one bound state (`isUnit_neutralWindow_dyadic`). The
Schur complement of the neutral part of `W` over `M` is a two-block matrix: its diagonal blocks
are the **conditional energies** `S₁`, `S₃` of the two ends given the middle, its off-diagonal
block the **conditional coupling** `X = K − P₁ᵀ M⁻¹ P₂` of the two ends through the middle.
Haynsworth's inertia additivity gives the **overlap gluing law**
(`hermNegIndex_neutralWindow_overlap_eq_one_iff`):

  `W` has one bound state iff `A` and `A'` have one bound state each and
  `(uᵀ X v)² ≤ (uᵀ S₁ u)(vᵀ S₃ v)` for all `u`, `v`,

that is, iff the parts are one-bound-state windows and the conditional coupling is a contraction
between their conditional energies. The inequality is a forward Cauchy–Schwarz inequality on the
whole space, with nonnegative forms on both sides; the reverse inequality on the positive cone of
the two-well law is replaced by it. The contacts of `W` between its two ends, and every jet
between them, enter only `X`.

Both parts are shorter than `W`. By induction on the length, starting from the windows of ratio
at most `103/50`, the Riemann hypothesis holds iff every conditional coupling is a contraction
(`riemannHypothesis_iff_forall_overlap_contraction`): a recursion on windows whose step has full
rank. The induction uses that refinement does not lower the index of the neutral part
(`hermNegIndex_neutralWindow_le_refined`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### Inertia of real block matrices -/

section Blocks

variable {μ κ α β : Type*} [Fintype μ] [Fintype κ] [Fintype α] [Fintype β]
  [DecidableEq μ] [DecidableEq κ] [DecidableEq α] [DecidableEq β]

/-- **Haynsworth's inertia additivity for real symmetric block matrices.** -/
theorem hermNegIndex_fromBlocks_transpose {A : Matrix μ μ ℝ} (hA : ∀ i j, A i j = A j i)
    (hAu : IsUnit A) (B : Matrix μ κ ℝ) {C : Matrix κ κ ℝ} (hC : ∀ i j, C i j = C j i) :
    hermNegIndex ((fromBlocks A B Bᵀ C).map (↑) : Matrix (μ ⊕ κ) (μ ⊕ κ) ℂ) =
      hermNegIndex (A.map (↑) : Matrix μ μ ℂ) +
        hermNegIndex ((C - Bᵀ * A⁻¹ * B).map (↑) : Matrix κ κ ℂ) := by
  have hBt : ((Bᵀ).map (↑) : Matrix κ μ ℂ) = (B.map (↑) : Matrix μ κ ℂ)ᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [Matrix.fromBlocks_map, hBt,
    haynsworth_negIndex (AbsoluteGeometryOfSpecZ.isUnit_map_ofReal hAu)
      (AbsoluteGeometryOfSpecZ.isHermitian_map_ofReal hA) _
      (AbsoluteGeometryOfSpecZ.isHermitian_map_ofReal hC),
    ← AbsoluteGeometryOfSpecZ.map_ofReal_nonsing_inv hAu]
  congr 2
  ext i j
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul,
    RCLike.star_def, Complex.conj_ofReal]

omit [DecidableEq κ] in
/-- A real matrix has no negative square iff its quadratic form is nonnegative. -/
theorem hermNegIndex_eq_zero_iff_forall {S : Matrix κ κ ℝ} :
    hermNegIndex (S.map (↑) : Matrix κ κ ℂ) = 0 ↔ ∀ x : κ → ℝ, 0 ≤ x ⬝ᵥ (S *ᵥ x) := by
  constructor
  · intro h x
    have := ArithmeticCastelnuovoSeveri.hermQuad_nonneg_of_negIndex_eq_zero h
      (fun i => ((x i : ℝ) : ℂ))
    rwa [HeckeKreinToeplitz.hermQuad_map_ofReal_real] at this
  · intro h
    have h0 := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
      (S.map (↑) : Matrix κ κ ℂ) (fun e : Empty => e.elim) fun z _ => by
        rw [HeckeKreinToeplitz.hermQuad_map_ofReal]
        exact add_nonneg (h _) (h _)
    simpa using h0

omit [DecidableEq α] [DecidableEq β] in
/-- The quadratic form of a symmetric two-block matrix. -/
theorem dotProduct_fromBlocks_mulVec (S₁ : Matrix α α ℝ) (X : Matrix α β ℝ)
    (S₃ : Matrix β β ℝ) (u : α → ℝ) (v : β → ℝ) :
    Sum.elim u v ⬝ᵥ (fromBlocks S₁ X Xᵀ S₃ *ᵥ Sum.elim u v) =
      u ⬝ᵥ (S₁ *ᵥ u) + 2 * (u ⬝ᵥ (X *ᵥ v)) + v ⬝ᵥ (S₃ *ᵥ v) := by
  rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add]
  rw [show v ⬝ᵥ (Xᵀ *ᵥ u) = u ⬝ᵥ (X *ᵥ v) by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]]
  ring

/-- **A two-block form with nonnegative diagonal blocks is nonnegative iff its off-diagonal
block is a contraction between them.** -/
theorem forall_fromBlocks_nonneg_iff {S₁ : Matrix α α ℝ} {X : Matrix α β ℝ}
    {S₃ : Matrix β β ℝ} (h₁ : ∀ u, 0 ≤ u ⬝ᵥ (S₁ *ᵥ u)) (h₃ : ∀ v, 0 ≤ v ⬝ᵥ (S₃ *ᵥ v)) :
    (∀ z : α ⊕ β → ℝ, 0 ≤ z ⬝ᵥ (fromBlocks S₁ X Xᵀ S₃ *ᵥ z)) ↔
      ∀ u v, (u ⬝ᵥ (X *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (S₁ *ᵥ u)) * (v ⬝ᵥ (S₃ *ᵥ v)) := by
  constructor
  · intro h u v
    have hq : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ (S₃ *ᵥ v)) * (t * t) + 2 * (u ⬝ᵥ (X *ᵥ v)) * t +
        u ⬝ᵥ (S₁ *ᵥ u) := by
      intro t
      have := h (Sum.elim u (t • v))
      rw [dotProduct_fromBlocks_mulVec] at this
      simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
      nlinarith [this]
    have hd := discrim_le_zero hq
    unfold discrim at hd
    nlinarith [hd]
  · intro h z
    rw [← Sum.elim_comp_inl_inr z, dotProduct_fromBlocks_mulVec]
    have hb := h (z ∘ Sum.inl) (z ∘ Sum.inr)
    have ha := h₁ (z ∘ Sum.inl)
    have hc := h₃ (z ∘ Sum.inr)
    set A := (z ∘ Sum.inl) ⬝ᵥ (S₁ *ᵥ (z ∘ Sum.inl))
    set B := (z ∘ Sum.inl) ⬝ᵥ (X *ᵥ (z ∘ Sum.inr))
    set C := (z ∘ Sum.inr) ⬝ᵥ (S₃ *ᵥ (z ∘ Sum.inr))
    by_contra hneg
    rw [not_le] at hneg
    have h1 : (A + C) ^ 2 < (2 * B) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (A - C)]

/-- The columns of the two couplings of the middle, side by side. -/
def joinColumns (P₁ : Matrix μ α ℝ) (P₂ : Matrix μ β ℝ) : Matrix μ (α ⊕ β) ℝ :=
  Matrix.of fun m x => Sum.elim (P₁ m) (P₂ m) x

omit [Fintype α] [Fintype β] [DecidableEq μ] [DecidableEq α] [DecidableEq β] in
theorem joinColumns_transpose_mul_mul (P₁ : Matrix μ α ℝ) (P₂ : Matrix μ β ℝ)
    (M : Matrix μ μ ℝ) :
    (joinColumns P₁ P₂)ᵀ * M * joinColumns P₁ P₂ =
      fromBlocks (P₁ᵀ * M * P₁) (P₁ᵀ * M * P₂) (P₂ᵀ * M * P₁) (P₂ᵀ * M * P₂) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    simp [joinColumns, Matrix.mul_apply]

/-- The window built from a middle `M`, its couplings `P₁`, `P₂` to the two ends, the ends `N₁`,
`N₂` and their direct coupling `K`. -/
def overlapWhole (M : Matrix μ μ ℝ) (P₁ : Matrix μ α ℝ) (P₂ : Matrix μ β ℝ)
    (N₁ : Matrix α α ℝ) (K : Matrix α β ℝ) (N₂ : Matrix β β ℝ) :
    Matrix (μ ⊕ (α ⊕ β)) (μ ⊕ (α ⊕ β)) ℝ :=
  fromBlocks M (joinColumns P₁ P₂) (joinColumns P₁ P₂)ᵀ (fromBlocks N₁ K Kᵀ N₂)

/-- The Schur complement over the middle is the two conditional energies and the conditional
coupling. -/
theorem fromBlocks_sub_joinColumns {M : Matrix μ μ ℝ} (hM : ∀ i j, M i j = M j i)
    (P₁ : Matrix μ α ℝ) (P₂ : Matrix μ β ℝ) (N₁ : Matrix α α ℝ) (K : Matrix α β ℝ)
    (N₂ : Matrix β β ℝ) :
    fromBlocks N₁ K Kᵀ N₂ - (joinColumns P₁ P₂)ᵀ * M⁻¹ * joinColumns P₁ P₂ =
      fromBlocks (N₁ - P₁ᵀ * M⁻¹ * P₁) (K - P₁ᵀ * M⁻¹ * P₂) (K - P₁ᵀ * M⁻¹ * P₂)ᵀ
        (N₂ - P₂ᵀ * M⁻¹ * P₂) := by
  have hMt : Mᵀ = M := Matrix.ext fun i j => hM j i
  have hMinv : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMt]
  have hT : P₂ᵀ * M⁻¹ * P₁ = (P₁ᵀ * M⁻¹ * P₂)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hMinv,
      Matrix.mul_assoc]
  rw [joinColumns_transpose_mul_mul, hT]
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    simp [Matrix.sub_apply, Matrix.transpose_apply]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
theorem fromBlocks_symm {N₁ : Matrix α α ℝ} (h₁ : ∀ i j, N₁ i j = N₁ j i) (K : Matrix α β ℝ)
    {N₂ : Matrix β β ℝ} (h₂ : ∀ i j, N₂ i j = N₂ j i) (x y : α ⊕ β) :
    fromBlocks N₁ K Kᵀ N₂ x y = fromBlocks N₁ K Kᵀ N₂ y x := by
  rcases x with i | i <;> rcases y with j | j
  · exact h₁ i j
  · rfl
  · rfl
  · exact h₂ i j

/-- **The overlap gluing law.** If the middle is invertible, the whole holds as many negative
squares as the middle iff each part does and the conditional coupling is a contraction between
the conditional energies. -/
theorem hermNegIndex_overlapWhole_eq_iff {M : Matrix μ μ ℝ} (hM : ∀ i j, M i j = M j i)
    (hMu : IsUnit M) (P₁ : Matrix μ α ℝ) (P₂ : Matrix μ β ℝ) {N₁ : Matrix α α ℝ}
    (hN₁ : ∀ i j, N₁ i j = N₁ j i) (K : Matrix α β ℝ) {N₂ : Matrix β β ℝ}
    (hN₂ : ∀ i j, N₂ i j = N₂ j i) :
    hermNegIndex ((overlapWhole M P₁ P₂ N₁ K N₂).map (↑) :
        Matrix (μ ⊕ (α ⊕ β)) (μ ⊕ (α ⊕ β)) ℂ) = hermNegIndex (M.map (↑) : Matrix μ μ ℂ) ↔
      hermNegIndex ((fromBlocks M P₁ P₁ᵀ N₁).map (↑) : Matrix (μ ⊕ α) (μ ⊕ α) ℂ) =
          hermNegIndex (M.map (↑) : Matrix μ μ ℂ) ∧
        hermNegIndex ((fromBlocks M P₂ P₂ᵀ N₂).map (↑) : Matrix (μ ⊕ β) (μ ⊕ β) ℂ) =
          hermNegIndex (M.map (↑) : Matrix μ μ ℂ) ∧
        ∀ u v, (u ⬝ᵥ ((K - P₁ᵀ * M⁻¹ * P₂) *ᵥ v)) ^ 2 ≤
          (u ⬝ᵥ ((N₁ - P₁ᵀ * M⁻¹ * P₁) *ᵥ u)) * (v ⬝ᵥ ((N₂ - P₂ᵀ * M⁻¹ * P₂) *ᵥ v)) := by
  unfold overlapWhole
  rw [hermNegIndex_fromBlocks_transpose hM hMu _ (fromBlocks_symm hN₁ K hN₂),
    hermNegIndex_fromBlocks_transpose hM hMu P₁ hN₁,
    hermNegIndex_fromBlocks_transpose hM hMu P₂ hN₂, fromBlocks_sub_joinColumns hM,
    add_eq_left, add_eq_left, add_eq_left, hermNegIndex_eq_zero_iff_forall,
    hermNegIndex_eq_zero_iff_forall, hermNegIndex_eq_zero_iff_forall]
  constructor
  · intro h
    have h₁ : ∀ u, 0 ≤ u ⬝ᵥ ((N₁ - P₁ᵀ * M⁻¹ * P₁) *ᵥ u) := fun u => by
      have := h (Sum.elim u 0)
      rw [dotProduct_fromBlocks_mulVec] at this
      simpa using this
    have h₃ : ∀ v, 0 ≤ v ⬝ᵥ ((N₂ - P₂ᵀ * M⁻¹ * P₂) *ᵥ v) := fun v => by
      have := h (Sum.elim 0 v)
      rw [dotProduct_fromBlocks_mulVec] at this
      simpa using this
    exact ⟨h₁, h₃, (forall_fromBlocks_nonneg_iff h₁ h₃).mp h⟩
  · rintro ⟨h₁, h₃, hcs⟩
    exact (forall_fromBlocks_nonneg_iff h₁ h₃).mpr hcs

end Blocks

/-! ### Matrices of blocks at given positions -/

section Positions

variable {κ κ₁ κ₂ : Type*}

/-- The matrix of a kernel between two families of blocks given by their positions. -/
def posMatrix (K : ℕ → ℕ → ℝ) (p : κ₁ → ℕ) (q : κ₂ → ℕ) : Matrix κ₁ κ₂ ℝ :=
  Matrix.of fun x y => K (p x) (q y)

theorem posMatrix_transpose {K : ℕ → ℕ → ℝ} (hK : ∀ a b, K a b = K b a) (p : κ₁ → ℕ)
    (q : κ₂ → ℕ) : (posMatrix K p q)ᵀ = posMatrix K q p :=
  Matrix.ext fun _ _ => hK _ _

theorem posMatrix_symm {K : ℕ → ℕ → ℝ} (hK : ∀ a b, K a b = K b a) (p : κ → ℕ) (x y : κ) :
    posMatrix K p p x y = posMatrix K p p y x := hK _ _

theorem posMatrix_sumElim {K : ℕ → ℕ → ℝ} (hK : ∀ a b, K a b = K b a) (p₁ : κ₁ → ℕ)
    (p₂ : κ₂ → ℕ) :
    posMatrix K (Sum.elim p₁ p₂) (Sum.elim p₁ p₂) =
      fromBlocks (posMatrix K p₁ p₁) (posMatrix K p₁ p₂) (posMatrix K p₁ p₂)ᵀ
        (posMatrix K p₂ p₂) := by
  rw [posMatrix_transpose hK]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> rfl

theorem posMatrix_sumElim_right (K : ℕ → ℕ → ℝ) {μ : Type*} (p : μ → ℕ) (p₁ : κ₁ → ℕ)
    (p₂ : κ₂ → ℕ) :
    posMatrix K p (Sum.elim p₁ p₂) = joinColumns (posMatrix K p p₁) (posMatrix K p p₂) := by
  ext m x
  rcases x with x | x <;> rfl

end Positions

/-! ### The overlap of a window -/

section Overlap

/-- The positions of the middle `(R + a, 2(R + a)]` of `(R, 2(R + a) + b]`. -/
def middlePos (R a : ℕ) (m : Fin (R + a)) : ℕ := R + a + m

/-- The positions of the left end `(R, R + a]`. -/
def leftPos (R a : ℕ) (i : Fin a) : ℕ := R + i

/-- The positions of the right end `(2(R + a), 2(R + a) + b]`. -/
def rightPos (R a b : ℕ) (j : Fin b) : ℕ := 2 * (R + a) + j

/-- The conditional energy of the left end given the middle. -/
def overlapLeftEnergy (Q R a : ℕ) : Matrix (Fin a) (Fin a) ℝ :=
  posMatrix (neutralBlock Q) (leftPos R a) (leftPos R a) -
    (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))ᵀ * (neutralWindow Q (R + a) (R + a))⁻¹ *
      posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a)

/-- The conditional energy of the right end given the middle. -/
def overlapRightEnergy (Q R a b : ℕ) : Matrix (Fin b) (Fin b) ℝ :=
  posMatrix (neutralBlock Q) (rightPos R a b) (rightPos R a b) -
    (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))ᵀ *
      (neutralWindow Q (R + a) (R + a))⁻¹ *
      posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b)

/-- The conditional coupling of the two ends through the middle. -/
def overlapCoupling (Q R a b : ℕ) : Matrix (Fin a) (Fin b) ℝ :=
  posMatrix (neutralBlock Q) (leftPos R a) (rightPos R a b) -
    (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))ᵀ *
      (neutralWindow Q (R + a) (R + a))⁻¹ *
      posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b)

/-- The blocks of the whole window as middle, left end and right end. -/
def overlapEquiv (a D b : ℕ) : Fin D ⊕ (Fin a ⊕ Fin b) ≃ Fin (a + D + b) :=
  (Equiv.sumAssoc (Fin D) (Fin a) (Fin b)).symm.trans
    ((Equiv.sumCongr (Equiv.sumComm (Fin D) (Fin a)) (Equiv.refl (Fin b))).trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin b))).trans finSumFinEquiv))

/-- The blocks of the left part as middle and left end. -/
def leftPartEquiv (a D : ℕ) : Fin D ⊕ Fin a ≃ Fin (a + D) :=
  (Equiv.sumComm (Fin D) (Fin a)).trans finSumFinEquiv

theorem neutralBlock_symm (Q : ℕ) (x y : ℕ) : neutralBlock Q x y = neutralBlock Q y x :=
  neutralBlock_comm Q x y

/-- The whole window, reindexed, is the overlap matrix of its middle and its two ends. -/
theorem neutralWindow_submatrix_overlapEquiv (Q R a b : ℕ) :
    (neutralWindow Q R (a + (R + a) + b)).submatrix (overlapEquiv a (R + a) b)
        (overlapEquiv a (R + a) b) =
      overlapWhole (neutralWindow Q (R + a) (R + a))
        (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))
        (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))
        (posMatrix (neutralBlock Q) (leftPos R a) (leftPos R a))
        (posMatrix (neutralBlock Q) (leftPos R a) (rightPos R a b))
        (posMatrix (neutralBlock Q) (rightPos R a b) (rightPos R a b)) := by
  have hpos : ∀ x, R + (overlapEquiv a (R + a) b x : ℕ) =
      Sum.elim (middlePos R a) (Sum.elim (leftPos R a) (rightPos R a b)) x := by
    rintro (m | i | j) <;>
      simp [overlapEquiv, middlePos, leftPos, rightPos] <;> omega
  have hW : (neutralWindow Q R (a + (R + a) + b)).submatrix (overlapEquiv a (R + a) b)
      (overlapEquiv a (R + a) b) =
      posMatrix (neutralBlock Q)
        (Sum.elim (middlePos R a) (Sum.elim (leftPos R a) (rightPos R a b)))
        (Sum.elim (middlePos R a) (Sum.elim (leftPos R a) (rightPos R a b))) := by
    ext x y
    simp only [Matrix.submatrix_apply, neutralWindow, windowMatrix, Matrix.of_apply, posMatrix,
      hpos]
  rw [hW, posMatrix_sumElim (neutralBlock_symm Q), posMatrix_sumElim_right,
    posMatrix_sumElim (neutralBlock_symm Q), overlapWhole, posMatrix_transpose (neutralBlock_symm Q)]
  rfl

/-- The left part, reindexed. -/
theorem neutralWindow_submatrix_leftPartEquiv (Q R a : ℕ) :
    (neutralWindow Q R (a + (R + a))).submatrix (leftPartEquiv a (R + a))
        (leftPartEquiv a (R + a)) =
      fromBlocks (neutralWindow Q (R + a) (R + a))
        (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))
        (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))ᵀ
        (posMatrix (neutralBlock Q) (leftPos R a) (leftPos R a)) := by
  have hpos : ∀ x, R + (leftPartEquiv a (R + a) x : ℕ) =
      Sum.elim (middlePos R a) (leftPos R a) x := by
    rintro (m | i) <;> simp [leftPartEquiv, middlePos, leftPos] <;> omega
  have hW : (neutralWindow Q R (a + (R + a))).submatrix (leftPartEquiv a (R + a))
      (leftPartEquiv a (R + a)) =
      posMatrix (neutralBlock Q) (Sum.elim (middlePos R a) (leftPos R a))
        (Sum.elim (middlePos R a) (leftPos R a)) := by
    ext x y
    simp only [Matrix.submatrix_apply, neutralWindow, windowMatrix, Matrix.of_apply, posMatrix,
      hpos]
  rw [hW, posMatrix_sumElim (neutralBlock_symm Q)]
  rfl

/-- The right part, reindexed. -/
theorem neutralWindow_submatrix_rightPart (Q R a b : ℕ) :
    (neutralWindow Q (R + a) ((R + a) + b)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (neutralWindow Q (R + a) (R + a))
        (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))
        (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))ᵀ
        (posMatrix (neutralBlock Q) (rightPos R a b) (rightPos R a b)) := by
  have hpos : ∀ x : Fin (R + a) ⊕ Fin b, R + a + (finSumFinEquiv x : ℕ) =
      Sum.elim (middlePos R a) (rightPos R a b) x := by
    rintro (m | j) <;> simp [middlePos, rightPos] <;> omega
  have hW : (neutralWindow Q (R + a) ((R + a) + b)).submatrix finSumFinEquiv finSumFinEquiv =
      posMatrix (neutralBlock Q) (Sum.elim (middlePos R a) (rightPos R a b))
        (Sum.elim (middlePos R a) (rightPos R a b)) := by
    ext x y
    simp only [Matrix.submatrix_apply, neutralWindow, windowMatrix, Matrix.of_apply, posMatrix,
      hpos]
  rw [hW, posMatrix_sumElim (neutralBlock_symm Q)]
  rfl

theorem hermNegIndex_map_submatrix {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (A : Matrix ι ι ℝ) (e : ι' ≃ ι) :
    hermNegIndex ((A.submatrix e e).map (↑) : Matrix ι' ι' ℂ) =
      hermNegIndex (A.map (↑) : Matrix ι ι ℂ) :=
  hermNegIndex_submatrix_equiv (A.map (↑) : Matrix ι ι ℂ) e

/-! ### The dyadic middle -/

/-- **The neutral part of a dyadic window is invertible**: it is positive where the first
charge vanishes and negative on the constant packet. -/
theorem isUnit_neutralWindow_dyadic {Q D : ℕ} (hD : 1 ≤ D) (hQ : 2 ≤ Q) :
    IsUnit (neutralWindow Q D D) := by
  set N := neutralWindow Q D D with hN
  have hsymm : ∀ i j, N i j = N j i := neutralWindow_symm Q D D
  have hNt : Nᵀ = N := Matrix.ext fun i j => hsymm j i
  have hsym : ∀ x y : Fin D → ℝ, x ⬝ᵥ (N *ᵥ y) = y ⬝ᵥ (N *ᵥ x) := fun x y => by
    rw [Matrix.dotProduct_mulVec, ← hNt, Matrix.vecMul_transpose, hNt, dotProduct_comm]
  set one : Fin D → ℝ := fun _ => 1 with hone_def
  have hone : one ⬝ᵥ (N *ᵥ one) < 0 := by
    rw [AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, hN, neutralWindow]
    have h := sum_neutralBlock_dyadic_neg Q hD
    have hc := sum_fin_windowMatrix_coe (neutralBlock Q) D D (fun _ => 1)
    simp only [one_mul] at hc
    simpa only [hone_def, one_mul, hc] using h
  have hpos : ∀ z : Fin D → ℝ, ∑ i, z i = 0 → 1 / 5000 * ∑ i, z i ^ 2 ≤ z ⬝ᵥ (N *ᵥ z) := by
    intro z hz
    rw [AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, hN, neutralWindow,
      sum_fin_windowMatrix_eq,
      show ∑ i, z i ^ 2 = ∑ j ∈ range D, extendFin (fun i => z i ^ 2) j from
        sum_fin_eq_sum_range_extendFin _]
    have h := sum_neutralBlock_ge_of_short (R := D) (J := D) hD (by omega) hQ
      (σ := extendFin z) (Or.inl ((sum_fin_eq_sum_range_extendFin z).symm.trans hz))
    refine le_trans (le_of_eq ?_) h
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [extendFin, extendFin, dif_pos (Finset.mem_range.mp hj), dif_pos (Finset.mem_range.mp hj)]
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hw0 : N *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  suffices hwz : x - y = 0 from sub_eq_zero.mp hwz
  generalize x - y = w at hw0 ⊢
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (∑ i, w i) / D := ⟨_, rfl⟩
  have hz0 : ∑ i, (w - t • one) i = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, hone_def, smul_eq_mul, mul_one,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ht]
    field_simp
    ring
  have hw1 : w ⬝ᵥ (N *ᵥ one) = 0 := by rw [hsym, hw0, dotProduct_zero]
  have hzz : (w - t • one) ⬝ᵥ (N *ᵥ (w - t • one)) = t ^ 2 * (one ⬝ᵥ (N *ᵥ one)) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hw0, sub_dotProduct,
      dotProduct_neg, dotProduct_smul, smul_dotProduct, hw1, smul_eq_mul, zero_sub]
    ring
  have h1 := hpos (w - t • one) hz0
  rw [hzz] at h1
  have hsq : 0 ≤ ∑ i, (w - t • one) i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht2 : t ^ 2 = 0 := by
    by_contra hne
    have hpos2 : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) (Ne.symm hne)
    have := mul_neg_of_pos_of_neg hpos2 hone
    nlinarith
  have hs : ∑ i, (w - t • one) i ^ 2 = 0 := by
    rw [ht2, zero_mul] at h1
    linarith
  have ht0 : t = 0 := (pow_eq_zero_iff two_ne_zero).mp ht2
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ((w - t • one) i)).mp hs i
    (Finset.mem_univ i)
  have := pow_eq_zero_iff two_ne_zero |>.mp hi
  simpa [ht0] using this

/-- The middle holds exactly one bound state. -/
theorem hermNegIndex_neutralWindow_dyadic {Q D : ℕ} (hD : 1 ≤ D) (hQ : 2 ≤ Q) :
    hermNegIndex ((neutralWindow Q D D).map (↑) : Matrix (Fin D) (Fin D) ℂ) = 1 :=
  hermNegIndex_neutralWindow_eq_one hD le_rfl (by omega) hQ

/-! ### The gluing law on windows -/

/-- **The overlap gluing law.** The window `(R, 2(R + a) + b]` holds one bound state iff its
parts `(R, 2(R + a)]` and `(R + a, 2(R + a) + b]` hold one each and the conditional coupling of
its ends through the dyadic middle is a contraction between their conditional energies. -/
theorem hermNegIndex_neutralWindow_overlap_eq_one_iff {Q R : ℕ} (a b : ℕ) (hR : 1 ≤ R)
    (hQ : 2 ≤ Q) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
        Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 ↔
      hermNegIndex ((neutralWindow Q R (a + (R + a))).map (↑) :
          Matrix (Fin (a + (R + a))) (Fin (a + (R + a))) ℂ) = 1 ∧
        hermNegIndex ((neutralWindow Q (R + a) ((R + a) + b)).map (↑) :
          Matrix (Fin ((R + a) + b)) (Fin ((R + a) + b)) ℂ) = 1 ∧
        ∀ u v, (u ⬝ᵥ (overlapCoupling Q R a b *ᵥ v)) ^ 2 ≤
          (u ⬝ᵥ (overlapLeftEnergy Q R a *ᵥ u)) * (v ⬝ᵥ (overlapRightEnergy Q R a b *ᵥ v)) := by
  have hD : 1 ≤ R + a := by omega
  have hM := hermNegIndex_neutralWindow_dyadic (Q := Q) hD hQ
  have hlaw := hermNegIndex_overlapWhole_eq_iff (neutralWindow_symm Q (R + a) (R + a))
    (isUnit_neutralWindow_dyadic hD hQ)
    (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))
    (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))
    (posMatrix_symm (neutralBlock_symm Q) (leftPos R a))
    (posMatrix (neutralBlock Q) (leftPos R a) (rightPos R a b))
    (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b))
  rw [hM, ← neutralWindow_submatrix_overlapEquiv, ← neutralWindow_submatrix_leftPartEquiv,
    ← neutralWindow_submatrix_rightPart Q R a b, hermNegIndex_map_submatrix,
    hermNegIndex_map_submatrix, hermNegIndex_map_submatrix] at hlaw
  exact hlaw

/-! ### Refinement and the recursion -/

/-- The refinement of the block values of a complex vector, read through a real-linear
coordinate. -/
theorem sum_neutralBlock_complexRefine {R m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (Q J : ℕ)
    (g : ℂ → ℝ) (hg0 : g 0 = 0) (hdiv : ∀ z : ℂ, g (z / (Real.sqrt m : ℂ)) = g z / Real.sqrt m)
    (c : Fin J → ℂ) :
    ∑ n ∈ range (m * J), ∑ l ∈ range (m * J),
        extendFin (fun i : Fin (m * J) => g (complexRefine m J c i)) n *
          extendFin (fun i : Fin (m * J) => g (complexRefine m J c i)) l *
            neutralBlock Q (m * R + n) (m * R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, extendFin (fun i : Fin J => g (c i)) j *
        extendFin (fun i : Fin J => g (c i)) l * neutralBlock Q (R + j) (R + l) := by
  have hpt : ∀ n ∈ range (m * J), extendFin (fun i : Fin (m * J) => g (complexRefine m J c i)) n =
      refineStep m (extendFin fun i : Fin J => g (c i)) n := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [extendFin, dif_pos hn', refineStep]
    simp only [complexRefine, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hdiv]
    congr 1
    simp only [complexExtend, LinearMap.coe_mk, AddHom.coe_mk, extendFin]
    split_ifs <;> simp [hg0]
  rw [← sum_neutralBlock_refine hR hm Q J]
  exact Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun l hl => by
    rw [hpt n hn, hpt l hl]

/-- **Refinement does not lower the index of the neutral part.** -/
theorem hermNegIndex_neutralWindow_le_refined {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m)
    (Q J : ℕ) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      hermNegIndex ((neutralWindow Q (m * R) (m * J)).map (↑) :
        Matrix (Fin (m * J)) (Fin (m * J)) ℂ) := by
  refine HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_eq _ _ (complexRefine m J) fun c => ?_
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, HeckeKreinToeplitz.hermQuad_map_ofReal,
    AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    neutralWindow, neutralWindow, sum_fin_windowMatrix_eq,
    sum_fin_windowMatrix_eq, sum_fin_windowMatrix_eq, sum_fin_windowMatrix_eq,
    sum_neutralBlock_complexRefine hR hm Q J Complex.re (by simp)
      (fun z => Complex.div_ofReal_re z _),
    sum_neutralBlock_complexRefine hR hm Q J Complex.im (by simp)
      (fun z => Complex.div_ofReal_im z _)]

/-- **The Riemann hypothesis is the contraction of every conditional coupling.** It holds iff
for every window `(R, 2(R + a) + b]` with `R ≥ 34` and ends `a, b ≥ 1` the conditional coupling
of the two ends through the dyadic middle is a contraction between their conditional energies. -/
theorem riemannHypothesis_iff_forall_overlap_contraction :
    RiemannHypothesis ↔ ∀ Q R a b : ℕ, 34 ≤ R → 1 ≤ a → 1 ≤ b →
      R + (a + (R + a) + b) ≤ Q * R →
        ∀ u v, (u ⬝ᵥ (overlapCoupling Q R a b *ᵥ v)) ^ 2 ≤
          (u ⬝ᵥ (overlapLeftEnergy Q R a *ᵥ u)) * (v ⬝ᵥ (overlapRightEnergy Q R a b *ᵥ v)) := by
  rw [riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one]
  constructor
  · intro h Q R a b hR _ _ hQ
    have hQ2 : 2 ≤ Q := by
      by_contra hlt
      have : Q * R ≤ 1 * R := Nat.mul_le_mul_right R (by omega)
      omega
    exact ((hermNegIndex_neutralWindow_overlap_eq_one_iff a b (by omega) hQ2).mp
      (h Q R _ (by omega) (by omega) hQ)).2.2
  · intro h
    -- every window with `R ≥ 34` holds one bound state, by induction on its length
    have key : ∀ J Q R : ℕ, 34 ≤ R → R ≤ J → R + J ≤ Q * R →
        hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 := by
      intro J
      induction J using Nat.strong_induction_on with
      | _ J ih =>
        intro Q R hR hRJ hQ
        have hQ2 : 2 ≤ Q := by
          by_contra hlt
          have : Q * R ≤ 1 * R := Nat.mul_le_mul_right R (by omega)
          omega
        rcases Nat.lt_or_ge J (R + 3) with hJ | hJ
        · exact hermNegIndex_neutralWindow_eq_one (by omega) hRJ (by omega) hQ2
        · obtain ⟨c, rfl⟩ : ∃ c, J = 1 + (R + 1) + (c + 1) := ⟨J - R - 3, by omega⟩
          refine (hermNegIndex_neutralWindow_overlap_eq_one_iff 1 (c + 1) (by omega) hQ2).mpr
            ⟨ih _ (by omega) Q R hR (by omega) (by omega),
              ih _ (by omega) Q (R + 1) (by omega) (by omega)
                (le_trans (by omega) (Nat.mul_le_mul_left Q (Nat.le_succ R))),
              h Q R 1 (c + 1) hR le_rfl (by omega) hQ⟩
    intro Q R J hR hRJ hQ
    have hle := hermNegIndex_neutralWindow_le_refined hR (m := 34) (by norm_num) Q J
    have h34 := key (34 * J) Q (34 * R) (by omega) (by omega)
      (by nlinarith [hQ])
    exact le_antisymm (hle.trans h34.le) (one_le_hermNegIndex_neutralWindow Q hR hRJ)

end Overlap

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
