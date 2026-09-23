import GaloisForLFunctions.RHTower.PinnedAffineWeldBoundaryNoGo

/-!
# The universal quotient by pinned affine defects

`PinnedAffineWeldBoundaryNoGo` proves that commutators corrected by arbitrary target factors, source
factors, and local-divisor multiples have zero Fitting boundary.  This file turns that no-go family
into a mathematical object.

For a fixed torsion presentation `A`, all pinned affine defects form an additive subgroup of the
matrix defect group.  The **pinned-affine defect quotient** divides by exactly this subgroup.  It is
universal for additive detectors which ignore pinned affine realizations.  The Fitting boundary
vanishes on the subgroup and therefore descends to the quotient.

Every nonzero Fitting boundary class has nonzero quotient class, and the existing one-slot
presentation `A=X^(2 : ℕ)`, `Delta=1` proves the quotient is genuinely nontrivial.  This is the precise,
carrier-free local meaning of an intrinsically non-affine defect.  It does not attach the completed
zeta datum; it supplies the universal recipient in which such an attachment would have to land.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The additive subgroup consisting of every pinned commutator-plus-two-sided-factor defect. -/
def pinnedAffineDefects (m : ℕ) (A : Matrix n n (Polynomial R)) :
    AddSubgroup (Matrix n n (Polynomial R)) where
  carrier := fun Delta =>
    ∃ σ Hright Kright Hleft Kleft : Matrix n n (Polynomial R),
      Delta = pinnedAffineWeldDefect m A σ Hright Kright Hleft Kleft
  zero_mem' := by
    refine ⟨0, 0, 0, 0, 0, ?_⟩
    simp [pinnedAffineWeldDefect, commutatorDefect]
  add_mem' := by
    rintro Delta E ⟨σ, Hr, Kr, Hl, Kl, rfl⟩ ⟨τ, Hr', Kr', Hl', Kl', rfl⟩
    refine ⟨σ + τ, Hr + Hr', Kr + Kr', Hl + Hl', Kl + Kl', ?_⟩
    simp [pinnedAffineWeldDefect, commutatorDefect, Matrix.add_mul, Matrix.mul_add, smul_add]
    abel
  neg_mem' := by
    rintro Delta ⟨σ, Hr, Kr, Hl, Kl, rfl⟩
    refine ⟨-σ, -Hr, -Kr, -Hl, -Kl, ?_⟩
    simp [pinnedAffineWeldDefect, commutatorDefect]
    abel

/-- Defects modulo all pinned affine realizations. -/
abbrev PinnedAffineDefectQuotient (m : ℕ) (A : Matrix n n (Polynomial R)) :=
  Matrix n n (Polynomial R) ⧸ pinnedAffineDefects m A

/-- Universal lift of an additive detector which vanishes on every pinned affine defect. -/
def pinnedAffineBlindLift {B : Type*} [AddCommGroup B]
    (m : ℕ) (A : Matrix n n (Polynomial R))
    (detector : Matrix n n (Polynomial R) →+ B)
    (blind : pinnedAffineDefects m A ≤ AddMonoidHom.ker detector) :
    PinnedAffineDefectQuotient m A →+ B :=
  QuotientAddGroup.lift _ detector blind

@[simp]
theorem pinnedAffineBlindLift_mk {B : Type*} [AddCommGroup B]
    (m : ℕ) (A Delta : Matrix n n (Polynomial R))
    (detector : Matrix n n (Polynomial R) →+ B)
    (blind : pinnedAffineDefects m A ≤ AddMonoidHom.ker detector) :
    pinnedAffineBlindLift m A detector blind
      (QuotientAddGroup.mk Delta : PinnedAffineDefectQuotient m A) = detector Delta := rfl

/-- The Fitting boundary as a bundled additive homomorphism in the defect variable. -/
def fittingBoundaryClassHom (m : ℕ) (A : Matrix n n (Polynomial R)) :
    Matrix n n (Polynomial R) →+ LocalDivisorJet R m where
  toFun := fittingBoundaryClass m A
  map_zero' := by
    simp [fittingBoundaryClass, fittingBoundaryTrace, jetClass]
  map_add' := fittingBoundaryClass_add m A

/-- The Fitting boundary kills the entire pinned affine subgroup. -/
theorem pinnedAffineDefects_le_ker_fittingBoundaryClassHom (m : ℕ)
    (A : Matrix n n (Polynomial R)) (hdet : A.det = (X : Polynomial R) ^ m) :
    pinnedAffineDefects m A ≤ AddMonoidHom.ker (fittingBoundaryClassHom m A) := by
  intro Delta hDelta
  rcases hDelta with ⟨σ, Hr, Kr, Hl, Kl, rfl⟩
  change fittingBoundaryClass m A (pinnedAffineWeldDefect m A σ Hr Kr Hl Kl) = 0
  exact fittingBoundaryClass_pinnedAffineWeldDefect_eq_zero m A σ Hr Kr Hl Kl hdet

/-- The Fitting boundary descended to defects modulo all pinned affine realizations. -/
def pinnedAffineBoundaryHom (m : ℕ) (A : Matrix n n (Polynomial R))
    (hdet : A.det = (X : Polynomial R) ^ m) :
    PinnedAffineDefectQuotient m A →+ LocalDivisorJet R m :=
  pinnedAffineBlindLift m A (fittingBoundaryClassHom m A)
    (pinnedAffineDefects_le_ker_fittingBoundaryClassHom m A hdet)

@[simp]
theorem pinnedAffineBoundaryHom_mk (m : ℕ) (A Delta : Matrix n n (Polynomial R))
    (hdet : A.det = (X : Polynomial R) ^ m) :
    pinnedAffineBoundaryHom m A hdet
      (QuotientAddGroup.mk Delta : PinnedAffineDefectQuotient m A) =
      fittingBoundaryClass m A Delta := rfl

/-- **Live Fitting boundary survives the universal quotient.** -/
theorem pinnedAffineClass_ne_zero_of_fittingBoundaryClass_ne_zero (m : ℕ)
    (A Delta : Matrix n n (Polynomial R)) (hdet : A.det = (X : Polynomial R) ^ m)
    (hclass : fittingBoundaryClass m A Delta ≠ 0) :
    (QuotientAddGroup.mk Delta : PinnedAffineDefectQuotient m A) ≠ 0 := by
  intro hzero
  apply hclass
  have hmap := congrArg (fun q => pinnedAffineBoundaryHom m A hdet q) hzero
  simpa using hmap

/-- **The quotient is nontrivial.**  The explicit one-slot nonfake boundary gives a nonzero class
modulo every pinned affine realization. -/
theorem exists_nonzero_pinnedAffineDefectQuotientClass :
    ∃ (A Delta : Matrix (Fin 1) (Fin 1) (Polynomial ℚ)),
      A.det = (X : Polynomial ℚ) ^ (2 : ℕ) ∧
        (QuotientAddGroup.mk Delta : PinnedAffineDefectQuotient 2 A) ≠ 0 := by
  obtain ⟨A, Delta, hdet, hclass⟩ := exists_nonfake_fittingBoundary
  exact ⟨A, Delta, hdet,
    pinnedAffineClass_ne_zero_of_fittingBoundaryClass_ne_zero 2 A Delta hdet hclass⟩

end RHTower

