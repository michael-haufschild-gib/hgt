import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Right-flip transport for two-particle scattering

The adjacent-braid input and the physical quantum matrix differ by right multiplication by the
two-particle tensor flip.  This file isolates the algebraic transport laws that use only the
flip's three exact properties: it is self-adjoint, unitary, and involutive.

The statements are first proved in an arbitrary star monoid and then specialized to the literal
permutation matrix on `κ × κ`.  No analytic, Yang--Baxter, or reconstruction hypothesis is hidden
in the interface.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv Matrix

/-- Right-flip conversion from an adjacent-braid operator to its physical quantum operator. -/
def rightFlip {A : Type*} [Mul A] (B F : A) : A :=
  B * F

section StarMonoid

variable {A : Type*} [Monoid A] [StarMul A]

/-- Right multiplication by a unitary flip preserves and reflects unitarity. -/
theorem rightFlip_mem_unitary_iff
    {B F : A} (hF : F ∈ unitary A) :
    rightFlip B F ∈ unitary A ↔ B ∈ unitary A := by
  constructor
  · intro hBF
    have hcancel := (unitary A).mul_mem hBF (Unitary.star_mem hF)
    simpa [rightFlip, mul_assoc, Unitary.mul_star_self_of_mem hF] using hcancel
  · intro hB
    exact (unitary A).mul_mem hB hF

/-- Hermitian analyticity is transported by right flip to conjugation by the flip. -/
theorem rightFlip_star_conjugation_iff
    {Bminus B F : A} (hF : F ∈ unitary A) :
    rightFlip Bminus F = F * star (rightFlip B F) * F ↔
      Bminus = star B := by
  let U : unitary A := ⟨F, hF⟩
  have hrhs : F * star (rightFlip B F) * F = star B * F := by
    calc
      F * star (rightFlip B F) * F =
          F * (star F * star B) * F := by rw [rightFlip, star_mul]
      _ = (F * star F) * star B * F := by simp only [mul_assoc]
      _ = star B * F := by rw [Unitary.mul_star_self_of_mem hF, one_mul]
  rw [rightFlip, hrhs]
  exact Unitary.mul_left_inj U

/-- Function-level form of hermitian-analyticity transport. -/
theorem rightFlip_hermitianAnalytic_iff
    {Θ : Type*} (neg : Θ → Θ) (B : Θ → A) {F : A}
    (hF : F ∈ unitary A) :
    (∀ θ, rightFlip (B (neg θ)) F = F * star (rightFlip (B θ) F) * F) ↔
      ∀ θ, B (neg θ) = star (B θ) := by
  constructor <;> intro h θ
  · exact (rightFlip_star_conjugation_iff hF).mp (h θ)
  · exact (rightFlip_star_conjugation_iff hF).mpr (h θ)

end StarMonoid

section Ring

variable {A : Type*} [Ring A]

/-- The adjacent fermionic identity anchor is exactly the physical negative-flip anchor. -/
theorem rightFlip_eq_neg_flip_iff
    {B F : A} (hF2 : F * F = 1) :
    rightFlip B F = -F ↔ B = -1 := by
  constructor
  · intro h
    have hmul := congrArg (fun X : A => X * F) h
    simpa [rightFlip, mul_assoc, hF2] using hmul
  · rintro rfl
    simp [rightFlip]

/-- Function-level anchor transport at a distinguished spectral parameter. -/
theorem rightFlip_fermionicAnchor_iff
    {Θ : Type*} (B : Θ → A) (θ₀ : Θ) {F : A} (hF2 : F * F = 1) :
    rightFlip (B θ₀) F = -F ↔ B θ₀ = -1 :=
  rightFlip_eq_neg_flip_iff hF2

end Ring

section AbstractBraidTransport

variable {P T : Type*} [Monoid P] [Monoid T]

/-- The non-adjacent `13` leg obtained by conjugating the adjacent `23` leg with the
`12` flip. -/
def conjugatedMiddleLeg (leg12 leg23 : P →* T) (F A : P) : T :=
  leg12 F * leg23 A * leg12 F

/-- Purely algebraic right-flip transport from the adjacent braid equation to the quantum
Yang--Baxter equation.  The hypotheses are precisely the Coxeter and covariance laws of the
two adjacent leg embeddings; the concrete finite-matrix theorem below proves every one of them. -/
theorem rightFlip_adjacentBraid_iff_quantumYangBaxter
    (leg12 leg23 : P →* T) (F : P)
    (hF2 : F * F = 1)
    (hflipBraid :
      leg12 F * leg23 F * leg12 F = leg23 F * leg12 F * leg23 F)
    (hmove23 : ∀ A, (leg23 F * leg12 F) * leg23 A =
      leg12 A * (leg23 F * leg12 F))
    (hmove12 : ∀ A, (leg12 F * leg23 F) * leg12 A =
      leg23 A * (leg12 F * leg23 F))
    (Bx Bxy By : P) :
    leg12 Bx * leg23 Bxy * leg12 By =
        leg23 By * leg12 Bxy * leg23 Bx ↔
      leg12 (rightFlip Bx F) *
          conjugatedMiddleLeg leg12 leg23 F (rightFlip Bxy F) *
          leg23 (rightFlip By F) =
        leg23 (rightFlip By F) *
          conjugatedMiddleLeg leg12 leg23 F (rightFlip Bxy F) *
          leg12 (rightFlip Bx F) := by
  let F12 : T := leg12 F
  let F23 : T := leg23 F
  have hF12sq : F12 * F12 = 1 := by
    change leg12 F * leg12 F = 1
    rw [← map_mul, hF2, map_one]
  have hF23sq : F23 * F23 = 1 := by
    change leg23 F * leg23 F = 1
    rw [← map_mul, hF2, map_one]
  have hleft :
      leg12 (rightFlip Bx F) *
          conjugatedMiddleLeg leg12 leg23 F (rightFlip Bxy F) *
          leg23 (rightFlip By F) =
        (leg12 Bx * leg23 Bxy * leg12 By) * (F12 * F23 * F12) := by
    simp only [rightFlip, map_mul, conjugatedMiddleLeg]
    change
      (leg12 Bx * F12) * (F12 * (leg23 Bxy * F23) * F12) *
          (leg23 By * F23) =
        (leg12 Bx * leg23 Bxy * leg12 By) * (F12 * F23 * F12)
    calc
      _ = leg12 Bx * (F12 * F12) * leg23 Bxy *
          ((F23 * F12) * leg23 By) * F23 := by
        simp only [mul_assoc]
      _ = leg12 Bx * leg23 Bxy * ((F23 * F12) * leg23 By) * F23 := by
        rw [hF12sq]
        simp only [mul_one]
      _ = leg12 Bx * leg23 Bxy *
          (leg12 By * (F23 * F12)) * F23 := by
        rw [hmove23]
      _ = (leg12 Bx * leg23 Bxy * leg12 By) * (F23 * F12 * F23) := by
        simp only [mul_assoc]
      _ = (leg12 Bx * leg23 Bxy * leg12 By) * (F12 * F23 * F12) := by
        rw [hflipBraid]
  have hright :
      leg23 (rightFlip By F) *
          conjugatedMiddleLeg leg12 leg23 F (rightFlip Bxy F) *
          leg12 (rightFlip Bx F) =
        (leg23 By * leg12 Bxy * leg23 Bx) * (F12 * F23 * F12) := by
    simp only [rightFlip, map_mul, conjugatedMiddleLeg]
    change
      (leg23 By * F23) * (F12 * (leg23 Bxy * F23) * F12) *
          (leg12 Bx * F12) =
        (leg23 By * leg12 Bxy * leg23 Bx) * (F12 * F23 * F12)
    calc
      _ = leg23 By * ((F23 * F12) * leg23 Bxy) * F23 * F12 *
          leg12 Bx * F12 := by
        simp only [mul_assoc]
      _ = leg23 By * (leg12 Bxy * (F23 * F12)) * F23 * F12 *
          leg12 Bx * F12 := by
        rw [hmove23]
      _ = leg23 By * leg12 Bxy * ((F23 * F12 * F23) * F12) *
          leg12 Bx * F12 := by
        simp only [mul_assoc]
      _ = leg23 By * leg12 Bxy * ((F12 * F23 * F12) * F12) *
          leg12 Bx * F12 := by
        rw [hflipBraid]
      _ = leg23 By * leg12 Bxy * ((F12 * F23) * leg12 Bx) * F12 := by
        simp only [mul_assoc, hF12sq, mul_one]
      _ = leg23 By * leg12 Bxy *
          (leg23 Bx * (F12 * F23)) * F12 := by
        rw [hmove12]
      _ = (leg23 By * leg12 Bxy * leg23 Bx) * (F12 * F23 * F12) := by
        simp only [mul_assoc]
  have hlongestSq :
      (F12 * F23 * F12) * (F12 * F23 * F12) = 1 := by
    calc
      (F12 * F23 * F12) * (F12 * F23 * F12) =
          F12 * F23 * (F12 * F12) * F23 * F12 := by
        simp only [mul_assoc]
      _ = F12 * (F23 * F23) * F12 := by
        rw [hF12sq]
        simp only [mul_one, mul_assoc]
      _ = F12 * F12 := by rw [hF23sq]; simp
      _ = 1 := hF12sq
  rw [hleft, hright]
  constructor
  · intro h
    rw [h]
  · intro h
    calc
      leg12 Bx * leg23 Bxy * leg12 By =
          (leg12 Bx * leg23 Bxy * leg12 By) * 1 := by rw [mul_one]
      _ = (leg12 Bx * leg23 Bxy * leg12 By) *
          ((F12 * F23 * F12) * (F12 * F23 * F12)) := by
        rw [hlongestSq]
      _ = ((leg12 Bx * leg23 Bxy * leg12 By) * (F12 * F23 * F12)) *
            (F12 * F23 * F12) :=
        (mul_assoc (leg12 Bx * leg23 Bxy * leg12 By)
          (F12 * F23 * F12) (F12 * F23 * F12)).symm
      _ = ((leg23 By * leg12 Bxy * leg23 Bx) * (F12 * F23 * F12)) *
            (F12 * F23 * F12) := congrArg (fun A : T ↦ A * (F12 * F23 * F12)) h
      _ = (leg23 By * leg12 Bxy * leg23 Bx) *
          ((F12 * F23 * F12) * (F12 * F23 * F12)) :=
        mul_assoc (leg23 By * leg12 Bxy * leg23 Bx)
          (F12 * F23 * F12) (F12 * F23 * F12)
      _ = (leg23 By * leg12 Bxy * leg23 Bx) * 1 := by rw [hlongestSq]
      _ = leg23 By * leg12 Bxy * leg23 Bx := by rw [mul_one]

end AbstractBraidTransport

section TensorFlip

variable (κ : Type*) [DecidableEq κ]

/-- The literal tensor flip on a finite one-particle basis, represented as a permutation matrix. -/
noncomputable def twoParticleFlipMatrix : Matrix (κ × κ) (κ × κ) ℂ :=
  (show Equiv.Perm (κ × κ) from Equiv.prodComm κ κ).permMatrix ℂ

/-- The two-particle flip is self-adjoint. -/
@[simp]
theorem star_twoParticleFlipMatrix :
    star (twoParticleFlipMatrix κ) = twoParticleFlipMatrix κ := by
  let σ : Equiv.Perm (κ × κ) := Equiv.prodComm κ κ
  have hσ : σ⁻¹ = σ := by
    simp [σ, Equiv.Perm.inv_def, Equiv.prodComm_symm]
  change (σ.permMatrix ℂ).conjTranspose = σ.permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix, hσ]

variable [Fintype κ]

/-- Right-associated basis indices for a three-particle tensor product. -/
abbrev ThreeParticleIndex := κ × (κ × κ)

/-- A two-particle matrix acting on the adjacent `23` tensor factors. -/
noncomputable def threeParticleLeg23 :
    Matrix (κ × κ) (κ × κ) ℂ →*
      Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ where
  toFun A := Matrix.kronecker (1 : Matrix κ κ ℂ) A
  map_one' := by simp
  map_mul' A B := by
    simpa using
      (Matrix.mul_kronecker_mul
        (1 : Matrix κ κ ℂ) (1 : Matrix κ κ ℂ) A B)

/-- A two-particle matrix acting on the adjacent `12` tensor factors, reindexed onto the same
right-associated three-particle basis as `threeParticleLeg23`. -/
noncomputable def threeParticleLeg12 :
    Matrix (κ × κ) (κ × κ) ℂ →*
      Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ where
  toFun A :=
    Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc κ κ κ)
      (Matrix.kronecker A (1 : Matrix κ κ ℂ))
  map_one' := by simp
  map_mul' A B := by
    rw [← Matrix.reindexAlgEquiv_mul]
    congr 1
    simpa using
      (Matrix.mul_kronecker_mul A B
        (1 : Matrix κ κ ℂ) (1 : Matrix κ κ ℂ))

@[simp]
theorem threeParticleLeg23_apply
    (A : Matrix (κ × κ) (κ × κ) ℂ)
    (i j : ThreeParticleIndex κ) :
    threeParticleLeg23 κ A i j =
      (1 : Matrix κ κ ℂ) i.1 j.1 * A i.2 j.2 :=
  rfl

@[simp]
theorem threeParticleLeg12_apply
    (A : Matrix (κ × κ) (κ × κ) ℂ)
    (i j : ThreeParticleIndex κ) :
    threeParticleLeg12 κ A i j =
      A (i.1, i.2.1) (j.1, j.2.1) *
        (1 : Matrix κ κ ℂ) i.2.2 j.2.2 :=
  rfl

/-- The permutation of three tensor factors exchanging positions `1` and `2`. -/
def tripleFlip12Permutation : Equiv.Perm (ThreeParticleIndex κ) where
  toFun i := (i.2.1, (i.1, i.2.2))
  invFun i := (i.2.1, (i.1, i.2.2))
  left_inv i := by rcases i with ⟨i₁, i₂, i₃⟩; rfl
  right_inv i := by rcases i with ⟨i₁, i₂, i₃⟩; rfl

/-- The permutation of three tensor factors exchanging positions `2` and `3`. -/
def tripleFlip23Permutation : Equiv.Perm (ThreeParticleIndex κ) where
  toFun i := (i.1, (i.2.2, i.2.1))
  invFun i := (i.1, (i.2.2, i.2.1))
  left_inv i := by rcases i with ⟨i₁, i₂, i₃⟩; rfl
  right_inv i := by rcases i with ⟨i₁, i₂, i₃⟩; rfl

/-- The literal `12` tensor flip on the three-particle basis. -/
noncomputable def threeParticleFlip12Matrix :
    Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ :=
  (tripleFlip12Permutation κ).permMatrix ℂ

/-- The literal `23` tensor flip on the three-particle basis. -/
noncomputable def threeParticleFlip23Matrix :
    Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ :=
  (tripleFlip23Permutation κ).permMatrix ℂ

/-- Conjugation by the `12` flip places a two-particle matrix on tensor factors `1` and `3`. -/
noncomputable def threeParticleLeg13
    (A : Matrix (κ × κ) (κ × κ) ℂ) :
    Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ :=
  threeParticleFlip12Matrix κ * threeParticleLeg23 κ A *
    threeParticleFlip12Matrix κ

/-- Embedding the two-particle flip in leg `12` gives the literal three-particle `12` flip. -/
@[simp]
theorem threeParticleLeg12_twoParticleFlipMatrix :
    threeParticleLeg12 κ (twoParticleFlipMatrix κ) =
      threeParticleFlip12Matrix κ := by
  ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩
  simp [threeParticleLeg12, twoParticleFlipMatrix, threeParticleFlip12Matrix,
    tripleFlip12Permutation, Matrix.one_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp_all

/-- Embedding the two-particle flip in leg `23` gives the literal three-particle `23` flip. -/
@[simp]
theorem threeParticleLeg23_twoParticleFlipMatrix :
    threeParticleLeg23 κ (twoParticleFlipMatrix κ) =
      threeParticleFlip23Matrix κ := by
  ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩
  simp [threeParticleLeg23, twoParticleFlipMatrix, threeParticleFlip23Matrix,
    tripleFlip23Permutation, Matrix.one_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp_all

/-- The two adjacent three-particle flips obey the braid relation. -/
theorem threeParticleFlip_braid :
    threeParticleFlip12Matrix κ * threeParticleFlip23Matrix κ *
        threeParticleFlip12Matrix κ =
      threeParticleFlip23Matrix κ * threeParticleFlip12Matrix κ *
        threeParticleFlip23Matrix κ := by
  let σ₁₂ := tripleFlip12Permutation κ
  let σ₂₃ := tripleFlip23Permutation κ
  have hperm : σ₁₂ * (σ₂₃ * σ₁₂) = σ₂₃ * (σ₁₂ * σ₂₃) := by
    apply Equiv.ext
    intro i
    rcases i with ⟨i₁, i₂, i₃⟩
    rfl
  change σ₁₂.permMatrix ℂ * σ₂₃.permMatrix ℂ * σ₁₂.permMatrix ℂ =
    σ₂₃.permMatrix ℂ * σ₁₂.permMatrix ℂ * σ₂₃.permMatrix ℂ
  calc
    σ₁₂.permMatrix ℂ * σ₂₃.permMatrix ℂ * σ₁₂.permMatrix ℂ =
        (σ₁₂ * (σ₂₃ * σ₁₂)).permMatrix ℂ := by
      rw [Matrix.permMatrix_mul, Matrix.permMatrix_mul]
    _ = (σ₂₃ * (σ₁₂ * σ₂₃)).permMatrix ℂ := by rw [hperm]
    _ = σ₂₃.permMatrix ℂ * σ₁₂.permMatrix ℂ *
        σ₂₃.permMatrix ℂ := by
      rw [Matrix.permMatrix_mul, Matrix.permMatrix_mul]

/-- Moving a `23` operator through the `23,12` flip word relabels it as a `12` operator. -/
theorem threeParticleFlip_move23
    (A : Matrix (κ × κ) (κ × κ) ℂ) :
    (threeParticleFlip23Matrix κ * threeParticleFlip12Matrix κ) *
        threeParticleLeg23 κ A =
      threeParticleLeg12 κ A *
        (threeParticleFlip23Matrix κ * threeParticleFlip12Matrix κ) := by
  let σ₁₂ := tripleFlip12Permutation κ
  let σ₂₃ := tripleFlip23Permutation κ
  have hsymm : (σ₁₂ * σ₂₃).symm = σ₂₃ * σ₁₂ := by
    apply Equiv.ext
    intro i
    rcases i with ⟨i₁, i₂, i₃⟩
    rfl
  change (σ₂₃.permMatrix ℂ * σ₁₂.permMatrix ℂ) *
      threeParticleLeg23 κ A =
    threeParticleLeg12 κ A *
      (σ₂₃.permMatrix ℂ * σ₁₂.permMatrix ℂ)
  calc
    (σ₂₃.permMatrix ℂ * σ₁₂.permMatrix ℂ) *
        threeParticleLeg23 κ A =
      (σ₁₂ * σ₂₃).permMatrix ℂ * threeParticleLeg23 κ A := by
        rw [Matrix.permMatrix_mul]
    _ = (threeParticleLeg23 κ A).submatrix (σ₁₂ * σ₂₃) id := by
      rw [PEquiv.toMatrix_toPEquiv_mul]
    _ = (threeParticleLeg12 κ A).submatrix id (σ₁₂ * σ₂₃).symm := by
      ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩
      rw [hsymm]
      simp [σ₁₂, σ₂₃, tripleFlip12Permutation, tripleFlip23Permutation,
        Matrix.one_apply]
    _ = threeParticleLeg12 κ A * (σ₁₂ * σ₂₃).permMatrix ℂ := by
      rw [PEquiv.mul_toMatrix_toPEquiv]
    _ = threeParticleLeg12 κ A *
        (σ₂₃.permMatrix ℂ * σ₁₂.permMatrix ℂ) := by
      rw [Matrix.permMatrix_mul]

/-- Moving a `12` operator through the `12,23` flip word relabels it as a `23` operator. -/
theorem threeParticleFlip_move12
    (A : Matrix (κ × κ) (κ × κ) ℂ) :
    (threeParticleFlip12Matrix κ * threeParticleFlip23Matrix κ) *
        threeParticleLeg12 κ A =
      threeParticleLeg23 κ A *
        (threeParticleFlip12Matrix κ * threeParticleFlip23Matrix κ) := by
  let σ₁₂ := tripleFlip12Permutation κ
  let σ₂₃ := tripleFlip23Permutation κ
  have hsymm : (σ₂₃ * σ₁₂).symm = σ₁₂ * σ₂₃ := by
    apply Equiv.ext
    intro i
    rcases i with ⟨i₁, i₂, i₃⟩
    rfl
  change (σ₁₂.permMatrix ℂ * σ₂₃.permMatrix ℂ) *
      threeParticleLeg12 κ A =
    threeParticleLeg23 κ A *
      (σ₁₂.permMatrix ℂ * σ₂₃.permMatrix ℂ)
  calc
    (σ₁₂.permMatrix ℂ * σ₂₃.permMatrix ℂ) *
        threeParticleLeg12 κ A =
      (σ₂₃ * σ₁₂).permMatrix ℂ * threeParticleLeg12 κ A := by
        rw [Matrix.permMatrix_mul]
    _ = (threeParticleLeg12 κ A).submatrix (σ₂₃ * σ₁₂) id := by
      rw [PEquiv.toMatrix_toPEquiv_mul]
    _ = (threeParticleLeg23 κ A).submatrix id (σ₂₃ * σ₁₂).symm := by
      ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩
      rw [hsymm]
      simp [σ₁₂, σ₂₃, tripleFlip12Permutation, tripleFlip23Permutation,
        Matrix.one_apply]
    _ = threeParticleLeg23 κ A * (σ₂₃ * σ₁₂).permMatrix ℂ := by
      rw [PEquiv.mul_toMatrix_toPEquiv]
    _ = threeParticleLeg23 κ A *
        (σ₁₂.permMatrix ℂ * σ₂₃.permMatrix ℂ) := by
      rw [Matrix.permMatrix_mul]

/-- Coordinate vector of a pure two-particle tensor. -/
def pureTensorVector (v w : κ → ℂ) : κ × κ → ℂ :=
  fun ij => v ij.1 * w ij.2

/-- Standard matrix element on the finite tensor-coordinate Hilbert space. -/
noncomputable def standardMatrixElement
    (bra : κ × κ → ℂ) (A : Matrix (κ × κ) (κ × κ) ℂ)
    (ket : κ × κ → ℂ) : ℂ :=
  (fun i => star (bra i)) ⬝ᵥ (A *ᵥ ket)

/-- Right multiplication by the tensor flip is exactly reversal of the two incoming matrix
indices.  This is the component identity used by the ordered-chamber scattering formula. -/
@[simp]
theorem matrix_rightFlip_apply
    (B : Matrix (κ × κ) (κ × κ) ℂ) (a b : κ × κ) :
    rightFlip B (twoParticleFlipMatrix κ) a b = B a (b.2, b.1) := by
  rw [rightFlip, twoParticleFlipMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The permutation matrix acts as the literal tensor flip on every pure tensor. -/
@[simp]
theorem twoParticleFlipMatrix_mulVec_pureTensor
    (v w : κ → ℂ) :
    twoParticleFlipMatrix κ *ᵥ pureTensorVector κ v w = pureTensorVector κ w v := by
  change (show Equiv.Perm (κ × κ) from Equiv.prodComm κ κ).permMatrix ℂ *ᵥ
      pureTensorVector κ v w = pureTensorVector κ w v
  rw [Matrix.permMatrix_mulVec]
  funext ij
  simp [pureTensorVector, mul_comm]

/-- Acting by the physical right-flip matrix is acting by the adjacent matrix after swapping the
two incoming pure-tensor factors. -/
@[simp]
theorem matrix_rightFlip_mulVec_pureTensor
    (B : Matrix (κ × κ) (κ × κ) ℂ) (v w : κ → ℂ) :
    rightFlip B (twoParticleFlipMatrix κ) *ᵥ pureTensorVector κ v w =
      B *ᵥ pureTensorVector κ w v := by
  rw [rightFlip, ← Matrix.mulVec_mulVec, twoParticleFlipMatrix_mulVec_pureTensor]

/-- Crossing pairings in the adjacent convention are exactly the corresponding physical
right-flip pairings.  The two charge-conjugated vectors are supplied explicitly, so no analytic or
antiunitary hypothesis is encoded in this algebraic transport theorem. -/
theorem rightFlip_crossingPairing_iff
    (Bplus Bminus : Matrix (κ × κ) (κ × κ) ℂ)
    (v₁ v₂ v₃ v₄ Jv₂ Jv₄ : κ → ℂ) :
    standardMatrixElement κ (pureTensorVector κ v₂ v₁) Bplus
          (pureTensorVector κ v₄ v₃) =
        standardMatrixElement κ (pureTensorVector κ v₁ Jv₄) Bminus
          (pureTensorVector κ v₃ Jv₂) ↔
      standardMatrixElement κ (pureTensorVector κ v₂ v₁)
          (rightFlip Bplus (twoParticleFlipMatrix κ)) (pureTensorVector κ v₃ v₄) =
        standardMatrixElement κ (pureTensorVector κ v₁ Jv₄)
          (rightFlip Bminus (twoParticleFlipMatrix κ)) (pureTensorVector κ Jv₂ v₃) := by
  simp only [standardMatrixElement, matrix_rightFlip_mulVec_pureTensor]

/-- The two-particle flip is an involution. -/
@[simp]
theorem twoParticleFlipMatrix_sq :
    twoParticleFlipMatrix κ * twoParticleFlipMatrix κ = 1 := by
  let σ : Equiv.Perm (κ × κ) := Equiv.prodComm κ κ
  have hσ2 : σ * σ = 1 := by
    apply Equiv.ext
    intro x
    simp [Equiv.Perm.mul_apply, σ]
  change σ.permMatrix ℂ * σ.permMatrix ℂ = 1
  rw [← Matrix.permMatrix_mul, hσ2, Matrix.permMatrix_one]

/-- The two-particle flip is unitary. -/
theorem twoParticleFlipMatrix_mem_unitary :
    twoParticleFlipMatrix κ ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ) := by
  constructor <;> simp

/-- Concrete finite-dimensional unitarity transport for the physical right-flip matrix. -/
theorem matrix_rightFlip_mem_unitary_iff
    (B : Matrix (κ × κ) (κ × κ) ℂ) :
    rightFlip B (twoParticleFlipMatrix κ) ∈
        unitary (Matrix (κ × κ) (κ × κ) ℂ) ↔
      B ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ) :=
  rightFlip_mem_unitary_iff (twoParticleFlipMatrix_mem_unitary κ)

/-- Concrete finite-dimensional fermionic-anchor transport. -/
theorem matrix_rightFlip_eq_neg_flip_iff
    (B : Matrix (κ × κ) (κ × κ) ℂ) :
    rightFlip B (twoParticleFlipMatrix κ) = -twoParticleFlipMatrix κ ↔
      B = -1 :=
  rightFlip_eq_neg_flip_iff (twoParticleFlipMatrix_sq κ)

/-- Concrete function-level fermionic-anchor transport. -/
theorem matrix_rightFlip_fermionicAnchor_iff
    {Θ : Type*} (B : Θ → Matrix (κ × κ) (κ × κ) ℂ) (θ₀ : Θ) :
    rightFlip (B θ₀) (twoParticleFlipMatrix κ) = -twoParticleFlipMatrix κ ↔
      B θ₀ = -1 :=
  rightFlip_fermionicAnchor_iff B θ₀ (twoParticleFlipMatrix_sq κ)

/-- Concrete finite-dimensional hermitian-analyticity transport. -/
theorem matrix_rightFlip_star_conjugation_iff
    (Bminus B : Matrix (κ × κ) (κ × κ) ℂ) :
    rightFlip Bminus (twoParticleFlipMatrix κ) =
        twoParticleFlipMatrix κ * star (rightFlip B (twoParticleFlipMatrix κ)) *
          twoParticleFlipMatrix κ ↔
      Bminus = star B :=
  rightFlip_star_conjugation_iff
    (twoParticleFlipMatrix_mem_unitary κ)

/-- Concrete function-level hermitian-analyticity transport. -/
theorem matrix_rightFlip_hermitianAnalytic_iff
    {Θ : Type*} (neg : Θ → Θ) (B : Θ → Matrix (κ × κ) (κ × κ) ℂ) :
    (∀ θ, rightFlip (B (neg θ)) (twoParticleFlipMatrix κ) =
        twoParticleFlipMatrix κ *
          star (rightFlip (B θ) (twoParticleFlipMatrix κ)) *
            twoParticleFlipMatrix κ) ↔
      ∀ θ, B (neg θ) = star (B θ) :=
  rightFlip_hermitianAnalytic_iff neg B (twoParticleFlipMatrix_mem_unitary κ)

/-- For arbitrary spectral parameters, right multiplication by the tensor flip converts the
adjacent spectral braid equation exactly into the quantum spectral Yang--Baxter equation on
the `12`, `13`, and `23` legs.  No regularity, invertibility, or analytic hypothesis on `B` is
needed for this algebraic equivalence. -/
theorem matrix_rightFlip_adjacentBraid_iff_quantumYangBaxter
    {Θ : Type*} [Add Θ]
    (B : Θ → Matrix (κ × κ) (κ × κ) ℂ) :
    (∀ x y,
      threeParticleLeg12 κ (B x) * threeParticleLeg23 κ (B (x + y)) *
          threeParticleLeg12 κ (B y) =
        threeParticleLeg23 κ (B y) * threeParticleLeg12 κ (B (x + y)) *
          threeParticleLeg23 κ (B x)) ↔
      ∀ x y,
        threeParticleLeg12 κ (rightFlip (B x) (twoParticleFlipMatrix κ)) *
            threeParticleLeg13 κ
              (rightFlip (B (x + y)) (twoParticleFlipMatrix κ)) *
            threeParticleLeg23 κ (rightFlip (B y) (twoParticleFlipMatrix κ)) =
          threeParticleLeg23 κ (rightFlip (B y) (twoParticleFlipMatrix κ)) *
            threeParticleLeg13 κ
              (rightFlip (B (x + y)) (twoParticleFlipMatrix κ)) *
            threeParticleLeg12 κ (rightFlip (B x) (twoParticleFlipMatrix κ)) := by
  have hflipBraid :
      threeParticleLeg12 κ (twoParticleFlipMatrix κ) *
            threeParticleLeg23 κ (twoParticleFlipMatrix κ) *
            threeParticleLeg12 κ (twoParticleFlipMatrix κ) =
        threeParticleLeg23 κ (twoParticleFlipMatrix κ) *
            threeParticleLeg12 κ (twoParticleFlipMatrix κ) *
            threeParticleLeg23 κ (twoParticleFlipMatrix κ) := by
    simpa using threeParticleFlip_braid κ
  have hmove23 : ∀ A : Matrix (κ × κ) (κ × κ) ℂ,
      (threeParticleLeg23 κ (twoParticleFlipMatrix κ) *
          threeParticleLeg12 κ (twoParticleFlipMatrix κ)) *
          threeParticleLeg23 κ A =
        threeParticleLeg12 κ A *
          (threeParticleLeg23 κ (twoParticleFlipMatrix κ) *
            threeParticleLeg12 κ (twoParticleFlipMatrix κ)) := by
    intro A
    simpa using threeParticleFlip_move23 κ A
  have hmove12 : ∀ A : Matrix (κ × κ) (κ × κ) ℂ,
      (threeParticleLeg12 κ (twoParticleFlipMatrix κ) *
          threeParticleLeg23 κ (twoParticleFlipMatrix κ)) *
          threeParticleLeg12 κ A =
        threeParticleLeg23 κ A *
          (threeParticleLeg12 κ (twoParticleFlipMatrix κ) *
            threeParticleLeg23 κ (twoParticleFlipMatrix κ)) := by
    intro A
    simpa using threeParticleFlip_move12 κ A
  constructor
  · intro h x y
    have hxy := (rightFlip_adjacentBraid_iff_quantumYangBaxter
      (threeParticleLeg12 κ) (threeParticleLeg23 κ) (twoParticleFlipMatrix κ)
      (twoParticleFlipMatrix_sq κ) hflipBraid hmove23 hmove12
      (B x) (B (x + y)) (B y)).mp (h x y)
    simpa [conjugatedMiddleLeg, threeParticleLeg13] using hxy
  · intro h x y
    apply (rightFlip_adjacentBraid_iff_quantumYangBaxter
      (threeParticleLeg12 κ) (threeParticleLeg23 κ) (twoParticleFlipMatrix κ)
      (twoParticleFlipMatrix_sq κ) hflipBraid hmove23 hmove12
      (B x) (B (x + y)) (B y)).mpr
    simpa [conjugatedMiddleLeg, threeParticleLeg13] using h x y

end TensorFlip

end GaloisForLFunctions.HTGeometry
