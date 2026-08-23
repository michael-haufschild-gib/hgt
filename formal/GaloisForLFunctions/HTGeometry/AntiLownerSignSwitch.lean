import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Anti-Löwner one-coordinate sign switch

`[LEAN-PROVED] [LITERATURE-FORMALIZATION] [NOVELTY UNVERIFIED]`

Formalizes the Schur-complement core of Audenaert's anti-Löwner sign-switch argument.  Flipping
one signed positive node preserves positive semidefiniteness of the finite anti-Löwner matrix.
Unlike the published principal-minor proof, the formal proof exposes an exact diagonal congruence
between the two Schur complements.
-/

open scoped Matrix MatrixOrder

namespace RHTower

noncomputable section

def signedAntiLownerMatrix {ι : Type*} (x g s : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (s i * g i + s j * g j) / (s i * x i + s j * x j)

theorem signedAntiLownerMatrix_comm {ι : Type*} (x g s : ι → ℝ) (i j : ι) :
    signedAntiLownerMatrix x g s i j = signedAntiLownerMatrix x g s j i := by
  simp only [signedAntiLownerMatrix]
  rw [add_comm (s i * g i), add_comm (s i * x i)]

def flipHeadSign {ι : Type*} (s : Unit ⊕ ι → ℝ) : Unit ⊕ ι → ℝ
  | Sum.inl u => -s (Sum.inl u)
  | Sum.inr i => s (Sum.inr i)

def flipSignAt {ι : Type*} [DecidableEq ι] (s : ι → ℝ) (k : ι) : ι → ℝ :=
  Function.update s k (-s k)

theorem signedAntiLownerMatrix_submatrix_equiv
    {ι κ : Type*} (x g s : ι → ℝ) (e : κ ≃ ι) :
    (signedAntiLownerMatrix x g s).submatrix e e =
      signedAntiLownerMatrix (x ∘ e) (g ∘ e) (s ∘ e) := by
  rfl

theorem flipSignAt_comp_equiv_head
    {ι κ : Type*} [DecidableEq ι]
    (s : ι → ℝ) (e : Unit ⊕ κ ≃ ι) :
    flipSignAt s (e (Sum.inl ())) ∘ e = flipHeadSign (s ∘ e) := by
  funext i
  rcases i with (_ | i)
  · simp [flipSignAt, flipHeadSign]
  · have hne : e (Sum.inr i) ≠ e (Sum.inl ()) := e.injective.ne (by simp)
    simp [flipSignAt, flipHeadSign, hne]

def headComplementEquiv {ι : Type*} [DecidableEq ι] (k : ι) :
    Unit ⊕ {j : ι // j ≠ k} ≃ ι where
  toFun
    | Sum.inl _ => k
    | Sum.inr j => j
  invFun j := if h : j = k then Sum.inl () else Sum.inr ⟨j, h⟩
  left_inv z := by
    rcases z with (_ | ⟨j, hj⟩)
    · simp
    · simp [hj]
  right_inv j := by
    by_cases h : j = k
    · subst j
      simp
    · simp [h]

def antiLownerTailSchur {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g s : Unit ⊕ ι → ℝ) : Matrix ι ι ℝ :=
  fun i j =>
    signedAntiLownerMatrix x g s (Sum.inr i) (Sum.inr j) -
      signedAntiLownerMatrix x g s (Sum.inr i) (Sum.inl ()) *
        (x (Sum.inl ()) / g (Sum.inl ())) *
      signedAntiLownerMatrix x g s (Sum.inl ()) (Sum.inr j)

def antiLownerHeadFlipCongruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x s : Unit ⊕ ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i =>
    (s (Sum.inl ()) * x (Sum.inl ()) + s (Sum.inr i) * x (Sum.inr i)) /
      (-s (Sum.inl ()) * x (Sum.inl ()) + s (Sum.inr i) * x (Sum.inr i))

private def antiLownerHead {ι : Type*} (x g : Unit ⊕ ι → ℝ) :
    Matrix Unit Unit ℝ :=
  Matrix.diagonal fun _ => g (Sum.inl ()) / x (Sum.inl ())

private def antiLownerHeadTail {ι : Type*} (x g s : Unit ⊕ ι → ℝ) :
    Matrix Unit ι ℝ :=
  fun _ j => signedAntiLownerMatrix x g s (Sum.inl ()) (Sum.inr j)

private def antiLownerTail {ι : Type*} (x g s : Unit ⊕ ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => signedAntiLownerMatrix x g s (Sum.inr i) (Sum.inr j)

private theorem antiLownerHead_inv {ι : Type*} (x g : Unit ⊕ ι → ℝ)
    (hx0 : x (Sum.inl ()) ≠ 0) (hg0 : g (Sum.inl ()) ≠ 0) :
    (antiLownerHead x g)⁻¹ =
      Matrix.diagonal (fun _ : Unit => x (Sum.inl ()) / g (Sum.inl ())) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  simp only [Subsingleton.elim (α := Unit) i (), Subsingleton.elim (α := Unit) j ()]
  simp [antiLownerHead]
  field_simp [hx0, hg0]

theorem signedAntiLownerMatrix_eq_fromBlocks
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g s : Unit ⊕ ι → ℝ) (hs0 : s (Sum.inl ()) ≠ 0)
    (hx0 : x (Sum.inl ()) ≠ 0) :
    signedAntiLownerMatrix x g s =
      Matrix.fromBlocks (antiLownerHead x g) (antiLownerHeadTail x g s)
        (antiLownerHeadTail x g s)ᴴ (antiLownerTail x g s) := by
  ext i j
  rcases i with (_ | i) <;> rcases j with (_ | j)
  · simp only [Subsingleton.elim (α := Unit) _ ()]
    simp only [signedAntiLownerMatrix, antiLownerHead, Matrix.fromBlocks_apply₁₁,
      Matrix.diagonal_apply_eq]
    field_simp [hs0, hx0]
  · rfl
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, star_id_of_comm,
      antiLownerHeadTail, signedAntiLownerMatrix]
    rw [add_comm (s (Sum.inr i) * g (Sum.inr i)),
      add_comm (s (Sum.inr i) * x (Sum.inr i))]
  · rfl

theorem antiLowner_schur_eq_tailSchur
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g s : Unit ⊕ ι → ℝ) (hx0 : x (Sum.inl ()) ≠ 0)
    (hg0 : g (Sum.inl ()) ≠ 0) :
    antiLownerTail x g s -
        (antiLownerHeadTail x g s)ᴴ * (antiLownerHead x g)⁻¹ *
          antiLownerHeadTail x g s =
      antiLownerTailSchur x g s := by
  ext i j
  simp only [Matrix.sub_apply, antiLownerTail, antiLownerHeadTail,
    antiLownerTailSchur, Matrix.mul_apply, Matrix.conjTranspose_apply, star_id_of_comm]
  rw [antiLownerHead_inv x g hx0 hg0]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  simp only [Matrix.diagonal_apply_eq]
  rw [signedAntiLownerMatrix_comm x g s (Sum.inl ()) (Sum.inr i)]

theorem scalar_antiLownerSchur_flip
    {x0 xi xj g0 gi gj s0 si sj : ℝ}
    (hs0 : s0 ^ 2 = 1) (hsi : si ^ 2 = 1) (hsj : sj ^ 2 = 1)
    (hg0 : g0 ≠ 0)
    (htail : si * xi + sj * xj ≠ 0)
    (hpi : s0 * x0 + si * xi ≠ 0) (hpj : s0 * x0 + sj * xj ≠ 0)
    (hmi : -s0 * x0 + si * xi ≠ 0) (hmj : -s0 * x0 + sj * xj ≠ 0) :
    (si * gi + sj * gj) / (si * xi + sj * xj) -
        (-s0 * g0 + si * gi) / (-s0 * x0 + si * xi) * (x0 / g0) *
          (-s0 * g0 + sj * gj) / (-s0 * x0 + sj * xj) =
      ((s0 * x0 + si * xi) / (-s0 * x0 + si * xi)) *
        ((si * gi + sj * gj) / (si * xi + sj * xj) -
          (s0 * g0 + si * gi) / (s0 * x0 + si * xi) * (x0 / g0) *
            (s0 * g0 + sj * gj) / (s0 * x0 + sj * xj)) *
          ((s0 * x0 + sj * xj) / (-s0 * x0 + sj * xj)) := by
  rcases sq_eq_one_iff.mp hs0 with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hsi with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hsj with rfl | rfl <;>
    norm_num at htail hpi hpj hmi hmj ⊢ <;>
    field_simp [hg0, htail, hpi, hpj, hmi, hmj] <;>
    ring

theorem antiLownerTailSchur_flipHead_eq_congruence
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g s : Unit ⊕ ι → ℝ)
    (hsq : ∀ k, s k ^ 2 = 1)
    (hg0 : g (Sum.inl ()) ≠ 0)
    (htail : ∀ i j,
      s (Sum.inr i) * x (Sum.inr i) + s (Sum.inr j) * x (Sum.inr j) ≠ 0)
    (hcross : ∀ i,
      s (Sum.inl ()) * x (Sum.inl ()) + s (Sum.inr i) * x (Sum.inr i) ≠ 0)
    (hflip : ∀ i,
      -s (Sum.inl ()) * x (Sum.inl ()) + s (Sum.inr i) * x (Sum.inr i) ≠ 0) :
    antiLownerTailSchur x g (flipHeadSign s) =
      antiLownerHeadFlipCongruence x s * antiLownerTailSchur x g s *
        (antiLownerHeadFlipCongruence x s)ᴴ := by
  ext i j
  simp only [antiLownerHeadFlipCongruence, Matrix.diagonal_conjTranspose,
    star_id_of_comm]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold antiLownerTailSchur signedAntiLownerMatrix flipHeadSign
  simp only [neg_mul]
  convert (scalar_antiLownerSchur_flip
      (x0 := x (Sum.inl ())) (xi := x (Sum.inr i)) (xj := x (Sum.inr j))
      (g0 := g (Sum.inl ())) (gi := g (Sum.inr i)) (gj := g (Sum.inr j))
      (s0 := s (Sum.inl ())) (si := s (Sum.inr i)) (sj := s (Sum.inr j))
      (hsq (Sum.inl ())) (hsq (Sum.inr i)) (hsq (Sum.inr j)) hg0
      (htail i j) (hcross i) (hcross j) (hflip i) (hflip j)) using 1 <;>
    ring

theorem antiLownerHeadFlipCongruence_isUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x s : Unit ⊕ ι → ℝ)
    (hcross : ∀ i,
      s (Sum.inl ()) * x (Sum.inl ()) + s (Sum.inr i) * x (Sum.inr i) ≠ 0)
    (hflip : ∀ i,
      -s (Sum.inl ()) * x (Sum.inl ()) + s (Sum.inr i) * x (Sum.inr i) ≠ 0) :
    IsUnit (antiLownerHeadFlipCongruence x s) := by
  rw [antiLownerHeadFlipCongruence, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  rw [isUnit_iff_ne_zero]
  exact div_ne_zero (hcross i) (hflip i)

/-- Audenaert's one-node sign switch: anti-Löwner positivity is invariant under flipping one
signed node.  The proof is by a scalar Schur complement and diagonal congruence. -/
theorem signedAntiLownerMatrix_flipHead_posSemidef_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g s : Unit ⊕ ι → ℝ)
    (hsq : ∀ k, s k ^ 2 = 1)
    (hx0 : 0 < x (Sum.inl ()))
    (hg0 : 0 < g (Sum.inl ()))
    (htail : ∀ i j,
      s (Sum.inr i) * x (Sum.inr i) + s (Sum.inr j) * x (Sum.inr j) ≠ 0)
    (hcross : ∀ i,
      s (Sum.inl ()) * x (Sum.inl ()) + s (Sum.inr i) * x (Sum.inr i) ≠ 0)
    (hflip : ∀ i,
      -s (Sum.inl ()) * x (Sum.inl ()) + s (Sum.inr i) * x (Sum.inr i) ≠ 0) :
    (signedAntiLownerMatrix x g (flipHeadSign s)).PosSemidef ↔
      (signedAntiLownerMatrix x g s).PosSemidef := by
  have hs0 : s (Sum.inl ()) ≠ 0 := by
    intro hs
    simpa [hs] using hsq (Sum.inl ())
  have hhead : (antiLownerHead x g).PosDef := by
    apply Matrix.PosDef.diagonal
    intro _
    exact div_pos hg0 hx0
  letI : Invertible (antiLownerHead x g) := hhead.isUnit.nonempty_invertible.some
  have hflipBlock :
      signedAntiLownerMatrix x g (flipHeadSign s) =
        Matrix.fromBlocks (antiLownerHead x g) (antiLownerHeadTail x g (flipHeadSign s))
          (antiLownerHeadTail x g (flipHeadSign s))ᴴ
          (antiLownerTail x g (flipHeadSign s)) := by
    apply signedAntiLownerMatrix_eq_fromBlocks
    · simpa [flipHeadSign] using neg_ne_zero.mpr hs0
    · exact ne_of_gt hx0
  have hbaseBlock :
      signedAntiLownerMatrix x g s =
        Matrix.fromBlocks (antiLownerHead x g) (antiLownerHeadTail x g s)
          (antiLownerHeadTail x g s)ᴴ (antiLownerTail x g s) :=
    signedAntiLownerMatrix_eq_fromBlocks x g s hs0 (ne_of_gt hx0)
  have hflipSchur :
      antiLownerTail x g (flipHeadSign s) -
          (antiLownerHeadTail x g (flipHeadSign s))ᴴ *
            (antiLownerHead x g)⁻¹ * antiLownerHeadTail x g (flipHeadSign s) =
        antiLownerTailSchur x g (flipHeadSign s) :=
    antiLowner_schur_eq_tailSchur x g (flipHeadSign s) (ne_of_gt hx0) (ne_of_gt hg0)
  have hbaseSchur :
      antiLownerTail x g s - (antiLownerHeadTail x g s)ᴴ *
          (antiLownerHead x g)⁻¹ * antiLownerHeadTail x g s =
        antiLownerTailSchur x g s :=
    antiLowner_schur_eq_tailSchur x g s (ne_of_gt hx0) (ne_of_gt hg0)
  have hcong := antiLownerTailSchur_flipHead_eq_congruence
    x g s hsq (ne_of_gt hg0) htail hcross hflip
  have hunit := antiLownerHeadFlipCongruence_isUnit x s hcross hflip
  rw [hflipBlock, Matrix.PosDef.fromBlocks₁₁
    (antiLownerHeadTail x g (flipHeadSign s)) (antiLownerTail x g (flipHeadSign s)) hhead,
    hflipSchur, hcong]
  rw [show
    (antiLownerHeadFlipCongruence x s * antiLownerTailSchur x g s *
        (antiLownerHeadFlipCongruence x s)ᴴ).PosSemidef ↔
      (antiLownerTailSchur x g s).PosSemidef by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hunit
        (x := antiLownerTailSchur x g s))]
  rw [hbaseBlock, Matrix.PosDef.fromBlocks₁₁
    (antiLownerHeadTail x g s) (antiLownerTail x g s) hhead, hbaseSchur]

/-- Coordinate-free form of the one-node sign switch, parameterized by a decomposition that moves
the selected coordinate to the head. -/
theorem signedAntiLownerMatrix_flipSignAt_posSemidef_iff
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (x g s : ι → ℝ) (e : Unit ⊕ κ ≃ ι)
    (hsq : ∀ k, s k ^ 2 = 1)
    (hx : ∀ k, 0 < x k)
    (hg : ∀ k, 0 < g k)
    (hbase : ∀ i j, s i * x i + s j * x j ≠ 0)
    (hflip : ∀ j : κ,
      -s (e (Sum.inl ())) * x (e (Sum.inl ())) +
          s (e (Sum.inr j)) * x (e (Sum.inr j)) ≠ 0) :
    (signedAntiLownerMatrix x g (flipSignAt s (e (Sum.inl ())))).PosSemidef ↔
      (signedAntiLownerMatrix x g s).PosSemidef := by
  have hhead := signedAntiLownerMatrix_flipHead_posSemidef_iff
    (x ∘ e) (g ∘ e) (s ∘ e)
    (fun k ↦ hsq (e k)) (hx (e (Sum.inl ()))) (hg (e (Sum.inl ())))
    (fun i j ↦ hbase (e (Sum.inr i)) (e (Sum.inr j)))
    (fun i ↦ hbase (e (Sum.inl ())) (e (Sum.inr i))) hflip
  rw [← Matrix.posSemidef_submatrix_equiv e,
    signedAntiLownerMatrix_submatrix_equiv]
  rw [flipSignAt_comp_equiv_head]
  rw [hhead]
  rw [← signedAntiLownerMatrix_submatrix_equiv,
    Matrix.posSemidef_submatrix_equiv e]

theorem signedAntiLownerMatrix_flipSignAt_posSemidef_iff_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g s : ι → ℝ) (k : ι)
    (hsq : ∀ i, s i ^ 2 = 1)
    (hx : ∀ i, 0 < x i)
    (hg : ∀ i, 0 < g i)
    (hbase : ∀ i j, s i * x i + s j * x j ≠ 0)
    (hflip : ∀ j, j ≠ k → -s k * x k + s j * x j ≠ 0) :
    (signedAntiLownerMatrix x g (flipSignAt s k)).PosSemidef ↔
      (signedAntiLownerMatrix x g s).PosSemidef := by
  simpa [headComplementEquiv] using
    (signedAntiLownerMatrix_flipSignAt_posSemidef_iff
      x g s (headComplementEquiv k) hsq hx hg hbase
      (fun j ↦ hflip j.1 j.2))

theorem signedNodeSum_ne_zero_of_pos_injective
    {ι : Type*} (x s : ι → ℝ)
    (hsq : ∀ i, s i ^ 2 = 1)
    (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) :
    ∀ i j, s i * x i + s j * x j ≠ 0 := by
  intro i j hzero
  have hprod : s i * x i = -(s j * x j) := by linarith
  have hxsq : (x i) ^ 2 = (x j) ^ 2 := by
    calc
      (x i) ^ 2 = (s i * x i) ^ 2 := by rw [mul_pow, hsq i, one_mul]
      _ = (-(s j * x j)) ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) hprod
      _ = (x j) ^ 2 := by rw [neg_sq, mul_pow, hsq j, one_mul]
  have hxij : x i = x j := by nlinarith [hx i, hx j]
  have hij : i = j := hinj hxij
  subst j
  have hsi : s i ≠ 0 := by
    intro h
    simpa [h] using hsq i
  exact (mul_ne_zero hsi (ne_of_gt (hx i))) (by linarith)

theorem flipSignAt_sq
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) (k : ι)
    (hsq : ∀ i, s i ^ 2 = 1) :
    ∀ i, (flipSignAt s k i) ^ 2 = 1 := by
  intro i
  by_cases h : i = k
  · subst i
    rw [flipSignAt, Function.update_self, neg_sq, hsq k]
  · rw [flipSignAt, Function.update_of_ne h, hsq i]

theorem signedAntiLownerMatrix_flipSignAt_posSemidef_iff_of_pos_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g s : ι → ℝ) (k : ι)
    (hsq : ∀ i, s i ^ 2 = 1)
    (hx : ∀ i, 0 < x i)
    (hg : ∀ i, 0 < g i)
    (hinj : Function.Injective x) :
    (signedAntiLownerMatrix x g (flipSignAt s k)).PosSemidef ↔
      (signedAntiLownerMatrix x g s).PosSemidef := by
  apply signedAntiLownerMatrix_flipSignAt_posSemidef_iff_of_ne x g s k hsq hx hg
  · exact signedNodeSum_ne_zero_of_pos_injective x s hsq hx hinj
  · intro j hj
    have hnonzero := signedNodeSum_ne_zero_of_pos_injective
      x (flipSignAt s k) (flipSignAt_sq s k hsq) hx hinj k j
    simpa [flipSignAt, hj] using hnonzero

def finsetSign {ι : Type*} [DecidableEq ι] (S : Finset ι) : ι → ℝ :=
  fun i => if i ∈ S then -1 else 1

theorem finsetSign_sq
    {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    ∀ i, (finsetSign S i) ^ 2 = 1 := by
  intro i
  simp [finsetSign]

theorem finsetSign_insert
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι) (hk : k ∉ S) :
    finsetSign (insert k S) = flipSignAt (finsetSign S) k := by
  funext i
  by_cases hik : i = k
  · subst i
    simp [finsetSign, flipSignAt, hk]
  · simp [finsetSign, flipSignAt, hik]

theorem signedAntiLownerMatrix_finsetSign_posSemidef_iff_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g : ι → ℝ) (S : Finset ι)
    (hx : ∀ i, 0 < x i)
    (hg : ∀ i, 0 < g i)
    (hinj : Function.Injective x) :
    (signedAntiLownerMatrix x g (finsetSign S)).PosSemidef ↔
      (signedAntiLownerMatrix x g (fun _ ↦ 1)).PosSemidef := by
  induction S using Finset.induction_on with
  | empty => exact Iff.rfl
  | @insert k S hk ih =>
      rw [finsetSign_insert S k hk]
      exact (signedAntiLownerMatrix_flipSignAt_posSemidef_iff_of_pos_injective
        x g (finsetSign S) k (finsetSign_sq S) hx hg hinj).trans ih

/-- Finite anti-Löwner sign-switch theorem.  On positive pairwise-distinct nodes, every `±1`
sign pattern has the same positive-semidefinite status as the all-positive anti-Löwner matrix. -/
theorem signedAntiLownerMatrix_posSemidef_iff_allPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x g s : ι → ℝ)
    (hsq : ∀ i, s i ^ 2 = 1)
    (hx : ∀ i, 0 < x i)
    (hg : ∀ i, 0 < g i)
    (hinj : Function.Injective x) :
    (signedAntiLownerMatrix x g s).PosSemidef ↔
      (signedAntiLownerMatrix x g (fun _ ↦ 1)).PosSemidef := by
  let S := Finset.univ.filter fun i => s i = -1
  have hs : s = finsetSign S := by
    funext i
    rcases sq_eq_one_iff.mp (hsq i) with hi | hi
    · simp [S, finsetSign, hi]
    · simp [S, finsetSign, hi]
  rw [hs]
  exact signedAntiLownerMatrix_finsetSign_posSemidef_iff_one x g S hx hg hinj

end

end RHTower
