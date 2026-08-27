import GaloisForLFunctions.HTGeometry.MilnorKTwoDiagonalExtension
import GaloisForLFunctions.HTGeometry.MilnorKUnitRankOne
import GaloisForLFunctions.HTGeometry.SteinbergTWTWeylKernel
import GaloisForLFunctions.HTGeometry.SteinbergFinFourWeylTorusTransport
import GaloisForLFunctions.HTGeometry.SteinbergWeylRootAction
import GaloisForLFunctions.HTGeometry.SteinbergWeylWordNormalForm
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Weyl action on the rank-four Milnor diagonal extension

This file builds the permutation and diagonal automorphisms in Milnor's Lemma 12.3.  The
non-strict triangular cocycle is not permutation invariant: an adjacent transposition changes it
by the coboundary of one Milnor symbol.  Correcting by that symbol gives exact lifted Coxeter
generators.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

namespace MilnorDiagonalExtension

open scoped commutatorElement

@[simp]
theorem neg_milnorSym2_self_eq_self (u : Fˣ) :
    -milnorSym2 F u u = milnorSym2 F u u := by
  have h := milnorSym2_two_nsmul_self F u
  simp only [two_nsmul] at h
  exact (eq_neg_of_add_eq_zero_left h).symm

@[simp]
theorem milnorSym2_self_add_self (u : Fˣ) :
    milnorSym2 F u u + milnorSym2 F u u = 0 := by
  simpa only [two_nsmul] using milnorSym2_two_nsmul_self F u

theorem milnorSym2_negOne_left_eq_neg (u : Fˣ) :
    milnorSym2 F (-1) u = -milnorSym2 F (-1) u := by
  calc
    milnorSym2 F (-1) u = milnorSym2 F u u := (milnorSym2_self u).symm
    _ = -milnorSym2 F u u := (neg_milnorSym2_self_eq_self u).symm
    _ = -milnorSym2 F (-1) u := congrArg Neg.neg (milnorSym2_self u)

theorem milnorSym2_negOne_left_add_self (u : Fˣ) :
    milnorSym2 F (-1) u + milnorSym2 F (-1) u = 0 := by
  rw [← milnorSym2_self]
  exact milnorSym2_self_add_self u

theorem neg_milnorSym2_negOne_left_add_self (u : Fˣ) :
    -milnorSym2 F (-1) u + -milnorSym2 F (-1) u = 0 := by
  rw [← neg_add_rev, milnorSym2_negOne_left_add_self, neg_zero]

/-- Relabel determinant-one diagonal coordinates by a permutation. -/
def fin4PermuteDiagonal (π : Equiv.Perm (Fin 4)) :
    detOneDiagonalUnits F 4 ≃* detOneDiagonalUnits F 4 where
  toFun u := ⟨fun i => u.1 (π.symm i), by
    change (∏ i : Fin 4, u.1 (π.symm i)) = 1
    rw [Equiv.prod_comp (show Fin 4 ≃ Fin 4 from π.symm) u.1]
    exact u.property⟩
  invFun u := ⟨fun i => u.1 (π i), by
    change (∏ i : Fin 4, u.1 (π i)) = 1
    rw [Equiv.prod_comp (show Fin 4 ≃ Fin 4 from π) u.1]
    exact u.property⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    simp
  right_inv u := by
    apply Subtype.ext
    funext i
    simp
  map_mul' u v := by
    apply Subtype.ext
    funext i
    rfl

@[simp]
theorem fin4PermuteDiagonal_apply (π : Equiv.Perm (Fin 4))
    (u : detOneDiagonalUnits F 4) (i : Fin 4) :
    (fin4PermuteDiagonal (F := F) π u).1 i = u.1 (π.symm i) := rfl

/-- Lift an automorphism of the diagonal group whose cocycle discrepancy is a coboundary. -/
def cochainLift (e : detOneDiagonalUnits F 4 ≃* detOneDiagonalUnits F 4)
    (b : detOneDiagonalUnits F 4 → MilnorKDeg F 2)
    (htransport : ∀ u v,
      milnorDiagonalCocycle (e u) (e v)
        = milnorDiagonalCocycle u v + b (u * v) - b u - b v) :
    MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 where
  toFun x := ⟨e x.diag, x.central + b x.diag⟩
  invFun x := ⟨e.symm x.diag, x.central - b (e.symm x.diag)⟩
  left_inv x := by
    ext
    · simp
    · simp
  right_inv x := by
    ext
    · simp
    · simp
  map_mul' x y := by
    apply MilnorDiagonalExtension.ext
    · exact e.map_mul x.diag y.diag
    · simp only [central_mul, diag_mul]
      rw [htransport]
      abel

def fin4Swap01Correction (u : detOneDiagonalUnits F 4) : MilnorKDeg F 2 :=
  milnorSym2 F (u.1 0) (u.1 1)

def fin4Swap12Correction (u : detOneDiagonalUnits F 4) : MilnorKDeg F 2 :=
  milnorSym2 F (u.1 1) (u.1 2)

def fin4Swap23Correction (u : detOneDiagonalUnits F 4) : MilnorKDeg F 2 :=
  milnorSym2 F (u.1 2) (u.1 3)

theorem milnorDiagonalCocycle_swap01 (u v : detOneDiagonalUnits F 4) :
    milnorDiagonalCocycle
        (fin4PermuteDiagonal (F := F) (Equiv.swap (0 : Fin 4) 1) u)
        (fin4PermuteDiagonal (F := F) (Equiv.swap (0 : Fin 4) 1) v)
      = milnorDiagonalCocycle u v
        + fin4Swap01Correction (F := F) (u * v)
        - fin4Swap01Correction (F := F) u
        - fin4Swap01Correction (F := F) v := by
  simp [milnorDiagonalCocycle, fin4PermuteDiagonal, fin4Swap01Correction,
    Fin.sum_univ_four, Equiv.swap_apply_def, milnorSym2_mul_left, milnorSym2_mul_right]
  rw [milnorSym2_antisymm (v.1 0) (u.1 1)]
  abel

theorem milnorDiagonalCocycle_swap12 (u v : detOneDiagonalUnits F 4) :
    milnorDiagonalCocycle
        (fin4PermuteDiagonal (F := F) (Equiv.swap (1 : Fin 4) 2) u)
        (fin4PermuteDiagonal (F := F) (Equiv.swap (1 : Fin 4) 2) v)
      = milnorDiagonalCocycle u v
        + fin4Swap12Correction (F := F) (u * v)
        - fin4Swap12Correction (F := F) u
        - fin4Swap12Correction (F := F) v := by
  simp [milnorDiagonalCocycle, fin4PermuteDiagonal, fin4Swap12Correction,
    Fin.sum_univ_four, Equiv.swap_apply_def, milnorSym2_mul_left, milnorSym2_mul_right]
  rw [milnorSym2_antisymm (v.1 1) (u.1 2)]
  abel

theorem milnorDiagonalCocycle_swap23 (u v : detOneDiagonalUnits F 4) :
    milnorDiagonalCocycle
        (fin4PermuteDiagonal (F := F) (Equiv.swap (2 : Fin 4) 3) u)
        (fin4PermuteDiagonal (F := F) (Equiv.swap (2 : Fin 4) 3) v)
      = milnorDiagonalCocycle u v
        + fin4Swap23Correction (F := F) (u * v)
        - fin4Swap23Correction (F := F) u
        - fin4Swap23Correction (F := F) v := by
  simp [milnorDiagonalCocycle, fin4PermuteDiagonal, fin4Swap23Correction,
    Fin.sum_univ_four, Equiv.swap_apply_def, milnorSym2_mul_left, milnorSym2_mul_right]
  rw [milnorSym2_antisymm (v.1 2) (u.1 3)]
  abel

/-- Lifted adjacent transposition `(0,1)`. -/
def fin4Swap01 : MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 :=
  cochainLift
    (fin4PermuteDiagonal (F := F) (Equiv.swap (0 : Fin 4) 1))
    (fin4Swap01Correction (F := F))
    (milnorDiagonalCocycle_swap01 (F := F))

/-- Lifted adjacent transposition `(1,2)`. -/
def fin4Swap12 : MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 :=
  cochainLift
    (fin4PermuteDiagonal (F := F) (Equiv.swap (1 : Fin 4) 2))
    (fin4Swap12Correction (F := F))
    (milnorDiagonalCocycle_swap12 (F := F))

/-- Lifted adjacent transposition `(2,3)`. -/
def fin4Swap23 : MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 :=
  cochainLift
    (fin4PermuteDiagonal (F := F) (Equiv.swap (2 : Fin 4) 3))
    (fin4Swap23Correction (F := F))
    (milnorDiagonalCocycle_swap23 (F := F))

@[simp] theorem fin4Swap01_diag (x : MilnorDiagonalExtension F 4) :
    (fin4Swap01 (F := F) x).diag =
      fin4PermuteDiagonal (F := F) (Equiv.swap (0 : Fin 4) 1) x.diag := rfl

@[simp] theorem fin4Swap12_diag (x : MilnorDiagonalExtension F 4) :
    (fin4Swap12 (F := F) x).diag =
      fin4PermuteDiagonal (F := F) (Equiv.swap (1 : Fin 4) 2) x.diag := rfl

@[simp] theorem fin4Swap23_diag (x : MilnorDiagonalExtension F 4) :
    (fin4Swap23 (F := F) x).diag =
      fin4PermuteDiagonal (F := F) (Equiv.swap (2 : Fin 4) 3) x.diag := rfl

@[simp] theorem fin4Swap01_central (x : MilnorDiagonalExtension F 4) :
    (fin4Swap01 (F := F) x).central = x.central + fin4Swap01Correction (F := F) x.diag := rfl

@[simp] theorem fin4Swap12_central (x : MilnorDiagonalExtension F 4) :
    (fin4Swap12 (F := F) x).central = x.central + fin4Swap12Correction (F := F) x.diag := rfl


@[simp] theorem fin4Swap23_central (x : MilnorDiagonalExtension F 4) :
    (fin4Swap23 (F := F) x).central = x.central + fin4Swap23Correction (F := F) x.diag := rfl

theorem fin4Swap01_sq (x : MilnorDiagonalExtension F 4) :
    fin4Swap01 (F := F) (fin4Swap01 (F := F) x) = x := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap01Correction, fin4PermuteDiagonal, Equiv.swap_apply_def]
    rw [milnorSym2_antisymm (x.diag.1 1) (x.diag.1 0)]
    abel

theorem fin4Swap12_sq (x : MilnorDiagonalExtension F 4) :
    fin4Swap12 (F := F) (fin4Swap12 (F := F) x) = x := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap12Correction, fin4PermuteDiagonal, Equiv.swap_apply_def]
    rw [milnorSym2_antisymm (x.diag.1 2) (x.diag.1 1)]
    abel

theorem fin4Swap23_sq (x : MilnorDiagonalExtension F 4) :
    fin4Swap23 (F := F) (fin4Swap23 (F := F) x) = x := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap23Correction, fin4PermuteDiagonal, Equiv.swap_apply_def]
    rw [milnorSym2_antisymm (x.diag.1 3) (x.diag.1 2)]
    abel

theorem fin4Swap01_swap23 (x : MilnorDiagonalExtension F 4) :
    fin4Swap01 (F := F) (fin4Swap23 (F := F) x)
      = fin4Swap23 (F := F) (fin4Swap01 (F := F) x) := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap01Correction, fin4Swap23Correction, fin4PermuteDiagonal,
      Equiv.swap_apply_def]
    abel

theorem fin4Swap01_swap12_swap01 (x : MilnorDiagonalExtension F 4) :
    fin4Swap01 (F := F) (fin4Swap12 (F := F) (fin4Swap01 (F := F) x))
      = fin4Swap12 (F := F) (fin4Swap01 (F := F) (fin4Swap12 (F := F) x)) := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap01Correction, fin4Swap12Correction, fin4PermuteDiagonal,
      Equiv.swap_apply_def]
    abel

theorem fin4Swap12_swap23_swap12 (x : MilnorDiagonalExtension F 4) :
    fin4Swap12 (F := F) (fin4Swap23 (F := F) (fin4Swap12 (F := F) x))
      = fin4Swap23 (F := F) (fin4Swap12 (F := F) (fin4Swap23 (F := F) x)) := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap12Correction, fin4Swap23Correction, fin4PermuteDiagonal,
      Equiv.swap_apply_def]
    abel

/-- Character by which an arbitrary ambient diagonal tuple acts on the determinant-one
diagonal extension.  The ambient tuple itself need not have determinant one. -/
def fin4DiagonalCharacter (a : Fin 4 → Fˣ) (u : detOneDiagonalUnits F 4) :
    MilnorKDeg F 2 :=
  ∑ i : Fin 4, milnorSym2 F (a i) (u.1 i)

@[simp]
theorem fin4DiagonalCharacter_one (a : Fin 4 → Fˣ) :
    fin4DiagonalCharacter (F := F) a 1 = 0 := by
  simp [fin4DiagonalCharacter, milnorSym2_one_right]

@[simp]
theorem fin4DiagonalCharacter_mul (a : Fin 4 → Fˣ)
    (u v : detOneDiagonalUnits F 4) :
    fin4DiagonalCharacter (F := F) a (u * v)
      = fin4DiagonalCharacter (F := F) a u + fin4DiagonalCharacter (F := F) a v := by
  simp [fin4DiagonalCharacter, milnorSym2_mul_right, Finset.sum_add_distrib]

theorem fin4DiagonalCharacter_mul_left (a b : Fin 4 → Fˣ)
    (u : detOneDiagonalUnits F 4) :
    fin4DiagonalCharacter (F := F) (a * b) u
      = fin4DiagonalCharacter (F := F) a u + fin4DiagonalCharacter (F := F) b u := by
  simp [fin4DiagonalCharacter, milnorSym2_mul_left, Finset.sum_add_distrib]

/-- Milnor's automorphism `beta(a)` for an arbitrary diagonal tuple `a`. -/
def fin4DiagonalAction (a : Fin 4 → Fˣ) :
    MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 where
  toFun x := ⟨x.diag, x.central + fin4DiagonalCharacter (F := F) a x.diag⟩
  invFun x := ⟨x.diag, x.central - fin4DiagonalCharacter (F := F) a x.diag⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by
    apply MilnorDiagonalExtension.ext
    · rfl
    · simp only [central_mul, diag_mul, fin4DiagonalCharacter_mul]
      abel

@[simp] theorem fin4DiagonalAction_diag (a : Fin 4 → Fˣ)
    (x : MilnorDiagonalExtension F 4) :
    (fin4DiagonalAction (F := F) a x).diag = x.diag := rfl

@[simp] theorem fin4DiagonalAction_central (a : Fin 4 → Fˣ)
    (x : MilnorDiagonalExtension F 4) :
    (fin4DiagonalAction (F := F) a x).central
      = x.central + fin4DiagonalCharacter (F := F) a x.diag := rfl

theorem fin4DiagonalAction_mul (a b : Fin 4 → Fˣ)
    (x : MilnorDiagonalExtension F 4) :
    fin4DiagonalAction (F := F) a (fin4DiagonalAction (F := F) b x)
      = fin4DiagonalAction (F := F) (a * b) x := by
  apply MilnorDiagonalExtension.ext
  · rfl
  · simp [fin4DiagonalCharacter_mul_left]
    abel

/-- If the ambient diagonal has determinant one, `beta(a)` is conjugation by every lift of it. -/
theorem fin4DiagonalAction_eq_conj (a : detOneDiagonalUnits F 4)
    (y x : MilnorDiagonalExtension F 4) (hy : y.diag = a) :
    fin4DiagonalAction (F := F) a.1 x = y * x * y⁻¹ := by
  calc
    fin4DiagonalAction (F := F) a.1 x
        = centralIncl (F := F) (n := 4)
            (Multiplicative.ofAdd (milnorDiagonalSymbolSum a x.diag)) * x := by
              apply MilnorDiagonalExtension.ext
              · simp
              · simp [fin4DiagonalCharacter, milnorDiagonalSymbolSum]
                abel
    _ = ⁅y, x⁆ * x := by
      rw [commutatorElement_eq_diagonalSymbolSum, hy]
    _ = y * x * y⁻¹ := by
      rw [commutatorElement_def]
      group

set_option maxHeartbeats 800000

/-- Pure permutation part of Milnor Lemma 12.3 for the first adjacent transposition. -/
theorem fin4Swap01_matsumotoDiagonalLift {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4Swap01 (F := F) (fin4MatsumotoDiagonalLift hij u)
      = fin4MatsumotoDiagonalLift
          (equiv_swap_ne (0 : Fin 4) 1 i j hij) u := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [fin4Swap01, cochainLift, fin4PermuteDiagonal,
        fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal, Equiv.swap_apply_def]
  · fin_cases i <;> fin_cases j <;>
      simp_all [fin4Swap01, cochainLift, fin4Swap01Correction,
        fin4PermuteDiagonal, fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal,
        Equiv.swap_apply_def, milnorSym2_one_left, milnorSym2_one_right,
        milnorSym2_inv_left, milnorSym2_inv_right]

/-- Pure permutation part of Milnor Lemma 12.3 for the middle adjacent transposition. -/
theorem fin4Swap12_matsumotoDiagonalLift {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4Swap12 (F := F) (fin4MatsumotoDiagonalLift hij u)
      = fin4MatsumotoDiagonalLift
          (equiv_swap_ne (1 : Fin 4) 2 i j hij) u := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [fin4Swap12, cochainLift, fin4PermuteDiagonal,
        fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal, Equiv.swap_apply_def]
  · fin_cases i <;> fin_cases j <;>
      simp_all [fin4Swap12, cochainLift, fin4Swap12Correction,
        fin4PermuteDiagonal, fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal,
        Equiv.swap_apply_def, milnorSym2_one_left, milnorSym2_one_right,
        milnorSym2_inv_left, milnorSym2_inv_right]

/-- Pure permutation part of Milnor Lemma 12.3 for the last adjacent transposition. -/
theorem fin4Swap23_matsumotoDiagonalLift {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4Swap23 (F := F) (fin4MatsumotoDiagonalLift hij u)
      = fin4MatsumotoDiagonalLift
          (equiv_swap_ne (2 : Fin 4) 3 i j hij) u := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [fin4Swap23, cochainLift, fin4PermuteDiagonal,
        fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal, Equiv.swap_apply_def]
  · fin_cases i <;> fin_cases j <;>
      simp_all [fin4Swap23, cochainLift, fin4Swap23Correction,
        fin4PermuteDiagonal, fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal,
        Equiv.swap_apply_def, milnorSym2_one_left, milnorSym2_one_right,
        milnorSym2_inv_left, milnorSym2_inv_right]

set_option maxHeartbeats 200000

theorem fin4DiagonalCharacter_matsumotoDiagonal (a : Fin 4 → Fˣ)
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4DiagonalCharacter (F := F) a (fin4MatsumotoDiagonal i j u)
      = milnorSym2 F (a i * (a j)⁻¹) u := by
  fin_cases i <;> fin_cases j <;>
    simp_all [fin4DiagonalCharacter, fin4MatsumotoDiagonal, Fin.sum_univ_four,
      milnorSym2_one_right, milnorSym2_mul_left, milnorSym2_inv_left,
      milnorSym2_inv_right] <;> abel

/-- Diagonal part of Milnor Lemma 12.3 on every canonical lift. -/
theorem fin4DiagonalAction_matsumotoDiagonalLift (a : Fin 4 → Fˣ)
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4DiagonalAction (F := F) a (fin4MatsumotoDiagonalLift hij u)
      = centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F (a i * (a j)⁻¹) u))
        * fin4MatsumotoDiagonalLift hij u := by
  apply MilnorDiagonalExtension.ext
  · simp
  · simp [fin4DiagonalAction, fin4MatsumotoDiagonalLift,
      fin4DiagonalCharacter_matsumotoDiagonal a hij u]
    abel

theorem fin4Swap01_centralIncl (z : Multiplicative (MilnorKDeg F 2)) :
    fin4Swap01 (F := F) (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    rfl
  · simp [fin4Swap01, cochainLift, fin4Swap01Correction, milnorSym2_one_left]

theorem fin4Swap12_centralIncl (z : Multiplicative (MilnorKDeg F 2)) :
    fin4Swap12 (F := F) (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    rfl
  · simp [fin4Swap12, cochainLift, fin4Swap12Correction, milnorSym2_one_left]

theorem fin4Swap23_centralIncl (z : Multiplicative (MilnorKDeg F 2)) :
    fin4Swap23 (F := F) (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    rfl
  · simp [fin4Swap23, cochainLift, fin4Swap23Correction, milnorSym2_one_left]

/-- Diagonal scale in the signed monomial matrix of `w₀₁(1)`. -/
def fin4Weyl01Scale : Fin 4 → Fˣ :=
  steinbergWeylRootScale (i := (0 : Fin 4)) (j := 1) (1 : Fˣ)

/-- Diagonal scale in the signed monomial matrix of `w₁₂(1)`. -/
def fin4Weyl12Scale : Fin 4 → Fˣ :=
  steinbergWeylRootScale (i := (1 : Fin 4)) (j := 2) (1 : Fˣ)

/-- Diagonal scale in the signed monomial matrix of `w₂₃(1)`. -/
def fin4Weyl23Scale : Fin 4 → Fˣ :=
  steinbergWeylRootScale (i := (2 : Fin 4)) (j := 3) (1 : Fˣ)

/-- Action of Milnor's signed Weyl generator `w₀₁(1)`. -/
def fin4SignedWeyl01Action :
    MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 :=
  (fin4DiagonalAction (F := F) (fin4Weyl01Scale (F := F))).trans
    (fin4Swap01 (F := F))

/-- Action of Milnor's signed Weyl generator `w₁₂(1)`. -/
def fin4SignedWeyl12Action :
    MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 :=
  (fin4DiagonalAction (F := F) (fin4Weyl12Scale (F := F))).trans
    (fin4Swap12 (F := F))

/-- Action of Milnor's signed Weyl generator `w₂₃(1)`. -/
def fin4SignedWeyl23Action :
    MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 :=
  (fin4DiagonalAction (F := F) (fin4Weyl23Scale (F := F))).trans
    (fin4Swap23 (F := F))

/-- **Milnor Lemma 12.3 for `w₀₁(1)`.** -/
theorem fin4SignedWeyl01Action_matsumotoDiagonalLift {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) :
    fin4SignedWeyl01Action (F := F) (fin4MatsumotoDiagonalLift hij u)
      = centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F
            (fin4Weyl01Scale (F := F) i * (fin4Weyl01Scale (F := F) j)⁻¹) u))
        * fin4MatsumotoDiagonalLift
            (equiv_swap_ne (0 : Fin 4) 1 i j hij) u := by
  change fin4Swap01 (F := F)
      (fin4DiagonalAction (F := F) (fin4Weyl01Scale (F := F))
        (fin4MatsumotoDiagonalLift hij u)) = _
  rw [fin4DiagonalAction_matsumotoDiagonalLift, map_mul,
    fin4Swap01_centralIncl, fin4Swap01_matsumotoDiagonalLift]

/-- **Milnor Lemma 12.3 for `w₁₂(1)`.** -/
theorem fin4SignedWeyl12Action_matsumotoDiagonalLift {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) :
    fin4SignedWeyl12Action (F := F) (fin4MatsumotoDiagonalLift hij u)
      = centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F
            (fin4Weyl12Scale (F := F) i * (fin4Weyl12Scale (F := F) j)⁻¹) u))
        * fin4MatsumotoDiagonalLift
            (equiv_swap_ne (1 : Fin 4) 2 i j hij) u := by
  change fin4Swap12 (F := F)
      (fin4DiagonalAction (F := F) (fin4Weyl12Scale (F := F))
        (fin4MatsumotoDiagonalLift hij u)) = _
  rw [fin4DiagonalAction_matsumotoDiagonalLift, map_mul,
    fin4Swap12_centralIncl, fin4Swap12_matsumotoDiagonalLift]

/-- **Milnor Lemma 12.3 for `w₂₃(1)`.** -/
theorem fin4SignedWeyl23Action_matsumotoDiagonalLift {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) :
    fin4SignedWeyl23Action (F := F) (fin4MatsumotoDiagonalLift hij u)
      = centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F
            (fin4Weyl23Scale (F := F) i * (fin4Weyl23Scale (F := F) j)⁻¹) u))
        * fin4MatsumotoDiagonalLift
            (equiv_swap_ne (2 : Fin 4) 3 i j hij) u := by
  change fin4Swap23 (F := F)
      (fin4DiagonalAction (F := F) (fin4Weyl23Scale (F := F))
        (fin4MatsumotoDiagonalLift hij u)) = _
  rw [fin4DiagonalAction_matsumotoDiagonalLift, map_mul,
    fin4Swap23_centralIncl, fin4Swap23_matsumotoDiagonalLift]

@[simp]
theorem fin4SignedWeyl01Action_diag (x : MilnorDiagonalExtension F 4) :
    (fin4SignedWeyl01Action (F := F) x).diag =
      fin4PermuteDiagonal (F := F) (Equiv.swap (0 : Fin 4) 1) x.diag := rfl

@[simp]
theorem fin4SignedWeyl12Action_diag (x : MilnorDiagonalExtension F 4) :
    (fin4SignedWeyl12Action (F := F) x).diag =
      fin4PermuteDiagonal (F := F) (Equiv.swap (1 : Fin 4) 2) x.diag := rfl

@[simp]
theorem fin4SignedWeyl23Action_diag (x : MilnorDiagonalExtension F 4) :
    (fin4SignedWeyl23Action (F := F) x).diag =
      fin4PermuteDiagonal (F := F) (Equiv.swap (2 : Fin 4) 3) x.diag := rfl

theorem fin4DiagonalCharacter_weyl01Scale (u : detOneDiagonalUnits F 4) :
    fin4DiagonalCharacter (F := F) (fin4Weyl01Scale (F := F)) u
      = milnorSym2 F (-1 : Fˣ) (u.1 0) := by
  simp [fin4DiagonalCharacter, fin4Weyl01Scale, steinbergWeylRootScale,
    Fin.sum_univ_four, milnorSym2_one_left]

theorem fin4DiagonalCharacter_weyl12Scale (u : detOneDiagonalUnits F 4) :
    fin4DiagonalCharacter (F := F) (fin4Weyl12Scale (F := F)) u
      = milnorSym2 F (-1 : Fˣ) (u.1 1) := by
  simp [fin4DiagonalCharacter, fin4Weyl12Scale, steinbergWeylRootScale,
    Fin.sum_univ_four, milnorSym2_one_left]

theorem fin4DiagonalCharacter_weyl23Scale (u : detOneDiagonalUnits F 4) :
    fin4DiagonalCharacter (F := F) (fin4Weyl23Scale (F := F)) u
      = milnorSym2 F (-1 : Fˣ) (u.1 2) := by
  simp [fin4DiagonalCharacter, fin4Weyl23Scale, steinbergWeylRootScale,
    Fin.sum_univ_four, milnorSym2_one_left]

@[simp]
theorem fin4SignedWeyl01Action_central (x : MilnorDiagonalExtension F 4) :
    (fin4SignedWeyl01Action (F := F) x).central
      = x.central + milnorSym2 F (-1 : Fˣ) (x.diag.1 0)
        + fin4Swap01Correction (F := F) x.diag := by
  simp [fin4SignedWeyl01Action, fin4DiagonalAction, fin4Swap01, cochainLift,
    fin4DiagonalCharacter_weyl01Scale]

@[simp]
theorem fin4SignedWeyl12Action_central (x : MilnorDiagonalExtension F 4) :
    (fin4SignedWeyl12Action (F := F) x).central
      = x.central + milnorSym2 F (-1 : Fˣ) (x.diag.1 1)
        + fin4Swap12Correction (F := F) x.diag := by
  simp [fin4SignedWeyl12Action, fin4DiagonalAction, fin4Swap12, cochainLift,
    fin4DiagonalCharacter_weyl12Scale]

@[simp]
theorem fin4SignedWeyl23Action_central (x : MilnorDiagonalExtension F 4) :
    (fin4SignedWeyl23Action (F := F) x).central
      = x.central + milnorSym2 F (-1 : Fˣ) (x.diag.1 2)
        + fin4Swap23Correction (F := F) x.diag := by
  simp [fin4SignedWeyl23Action, fin4DiagonalAction, fin4Swap23, cochainLift,
    fin4DiagonalCharacter_weyl23Scale]

/-- Distant signed Weyl generators commute as automorphisms of `H`. -/
theorem fin4SignedWeyl01Action_signedWeyl23Action
    (x : MilnorDiagonalExtension F 4) :
    fin4SignedWeyl01Action (F := F) (fin4SignedWeyl23Action (F := F) x)
      = fin4SignedWeyl23Action (F := F) (fin4SignedWeyl01Action (F := F) x) := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap01Correction, fin4Swap23Correction, fin4PermuteDiagonal,
      Equiv.swap_apply_def]
    abel

/-- First signed type-A braid relation. -/
theorem fin4SignedWeyl01Action_signedWeyl12Action_signedWeyl01Action
    (x : MilnorDiagonalExtension F 4) :
    fin4SignedWeyl01Action (F := F)
        (fin4SignedWeyl12Action (F := F) (fin4SignedWeyl01Action (F := F) x))
      = fin4SignedWeyl12Action (F := F)
          (fin4SignedWeyl01Action (F := F) (fin4SignedWeyl12Action (F := F) x)) := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap01Correction, fin4Swap12Correction, fin4PermuteDiagonal,
      Equiv.swap_apply_def]
    abel

/-- Second signed type-A braid relation. -/
theorem fin4SignedWeyl12Action_signedWeyl23Action_signedWeyl12Action
    (x : MilnorDiagonalExtension F 4) :
    fin4SignedWeyl12Action (F := F)
        (fin4SignedWeyl23Action (F := F) (fin4SignedWeyl12Action (F := F) x))
      = fin4SignedWeyl23Action (F := F)
          (fin4SignedWeyl12Action (F := F) (fin4SignedWeyl23Action (F := F) x)) := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap12Correction, fin4Swap23Correction, fin4PermuteDiagonal,
      Equiv.swap_apply_def]
    abel

/-- Square of signed generator `w₀₁(1)` is the diagonal action of `h₀₁(-1)`. -/
theorem fin4SignedWeyl01Action_sq (x : MilnorDiagonalExtension F 4) :
    fin4SignedWeyl01Action (F := F) (fin4SignedWeyl01Action (F := F) x)
      = fin4DiagonalAction (F := F)
          (fin4MatsumotoDiagonal (F := F) (0 : Fin 4) 1 (-1 : Fˣ)).1 x := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap01Correction, fin4PermuteDiagonal, fin4DiagonalAction,
      fin4DiagonalCharacter, fin4MatsumotoDiagonal, Fin.sum_univ_four,
      Equiv.swap_apply_def, milnorSym2_one_left]
    rw [milnorSym2_antisymm (x.diag.1 1) (x.diag.1 0)]
    abel

/-- Square of signed generator `w₁₂(1)` is the diagonal action of `h₁₂(-1)`. -/
theorem fin4SignedWeyl12Action_sq (x : MilnorDiagonalExtension F 4) :
    fin4SignedWeyl12Action (F := F) (fin4SignedWeyl12Action (F := F) x)
      = fin4DiagonalAction (F := F)
          (fin4MatsumotoDiagonal (F := F) (1 : Fin 4) 2 (-1 : Fˣ)).1 x := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap12Correction, fin4PermuteDiagonal, fin4DiagonalAction,
      fin4DiagonalCharacter, fin4MatsumotoDiagonal, Fin.sum_univ_four,
      Equiv.swap_apply_def, milnorSym2_one_left]
    rw [milnorSym2_antisymm (x.diag.1 2) (x.diag.1 1)]
    abel

/-- Square of signed generator `w₂₃(1)` is the diagonal action of `h₂₃(-1)`. -/
theorem fin4SignedWeyl23Action_sq (x : MilnorDiagonalExtension F 4) :
    fin4SignedWeyl23Action (F := F) (fin4SignedWeyl23Action (F := F) x)
      = fin4DiagonalAction (F := F)
          (fin4MatsumotoDiagonal (F := F) (2 : Fin 4) 3 (-1 : Fˣ)).1 x := by
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · simp [fin4Swap23Correction, fin4PermuteDiagonal, fin4DiagonalAction,
      fin4DiagonalCharacter, fin4MatsumotoDiagonal, Fin.sum_univ_four,
      Equiv.swap_apply_def, milnorSym2_one_left]
    rw [milnorSym2_antisymm (x.diag.1 3) (x.diag.1 2)]
    abel

/-- Three adjacent transpositions of four coordinates. -/
def fin4AdjacentPerm : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap (0 : Fin 4) 1, Equiv.swap (1 : Fin 4) 2,
    Equiv.swap (2 : Fin 4) 3]

/-- Corrected lifts of the three adjacent transpositions. -/
def fin4AdjacentAction : Fin 3 →
    (MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4) :=
  ![fin4Swap01 (F := F), fin4Swap12 (F := F), fin4Swap23 (F := F)]

theorem fin4AdjacentAction_matsumotoDiagonalLift (r : Fin 3)
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4AdjacentAction (F := F) r (fin4MatsumotoDiagonalLift hij u)
      = fin4MatsumotoDiagonalLift
          ((fin4AdjacentPerm r).injective.ne_iff.mpr hij) u := by
  fin_cases r
  · exact fin4Swap01_matsumotoDiagonalLift hij u
  · exact fin4Swap12_matsumotoDiagonalLift hij u
  · exact fin4Swap23_matsumotoDiagonalLift hij u

theorem fin4AdjacentAction_centralIncl (r : Fin 3)
    (z : Multiplicative (MilnorKDeg F 2)) :
    fin4AdjacentAction (F := F) r (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z := by
  fin_cases r
  · exact fin4Swap01_centralIncl z
  · exact fin4Swap12_centralIncl z
  · exact fin4Swap23_centralIncl z

/-- A word in adjacent transpositions, evaluated in both the permutation group and the corrected
automorphism group. -/
inductive Fin4AdjacentWord where
  | one
  | snoc (word : Fin4AdjacentWord) (r : Fin 3)

namespace Fin4AdjacentWord

def perm : Fin4AdjacentWord → Equiv.Perm (Fin 4)
  | .one => 1
  | .snoc word r => (fin4AdjacentPerm r).trans word.perm

def action : Fin4AdjacentWord →
    (MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4)
  | .one => MulEquiv.refl _
  | .snoc word r => (fin4AdjacentAction (F := F) r).trans word.action

def ofList : List (Fin 3) → Fin4AdjacentWord
  | [] => .one
  | r :: rs => .snoc (ofList rs) r

theorem action_matsumotoDiagonalLift (word : Fin4AdjacentWord)
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    word.action (F := F) (fin4MatsumotoDiagonalLift hij u)
      = fin4MatsumotoDiagonalLift (word.perm.injective.ne_iff.mpr hij) u := by
  induction word generalizing i j with
  | one => rfl
  | snoc word r ih =>
      change word.action (F := F)
        (fin4AdjacentAction (F := F) r (fin4MatsumotoDiagonalLift hij u)) = _
      rw [fin4AdjacentAction_matsumotoDiagonalLift, ih]
      rfl

theorem action_centralIncl (word : Fin4AdjacentWord)
    (z : Multiplicative (MilnorKDeg F 2)) :
    word.action (F := F) (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z := by
  induction word with
  | one => rfl
  | snoc word r ih =>
      change word.action (F := F)
        (fin4AdjacentAction (F := F) r (centralIncl (F := F) (n := 4) z)) = _
      rw [fin4AdjacentAction_centralIncl, ih]

end Fin4AdjacentWord

/-- Canonical adjacent-transposition word for each transposition of four coordinates. -/
def fin4SwapAdjacentWord (i j : Fin 4) : Fin4AdjacentWord :=
  Fin4AdjacentWord.ofList (![![[], [0], [0, 1, 0], [0, 1, 2, 1, 0]],
    ![[0], [], [1], [1, 2, 1]],
    ![[0, 1, 0], [1], [], [2]],
    ![[0, 1, 2, 1, 0], [1, 2, 1], [2], []]] i j)

theorem fin4SwapAdjacentWord_perm (i j : Fin 4) :
    (fin4SwapAdjacentWord i j).perm = Equiv.swap i j := by
  ext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

/-- Corrected lift of an arbitrary transposition of four coordinates. -/
def fin4SwapAction (i j : Fin 4) :
    MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 :=
  (fin4SwapAdjacentWord i j).action (F := F)

theorem fin4SwapAction_matsumotoDiagonalLift (p q : Fin 4)
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4SwapAction (F := F) p q (fin4MatsumotoDiagonalLift hij u)
      = fin4MatsumotoDiagonalLift
          (equiv_swap_ne p q i j hij) u := by
  rw [fin4SwapAction, Fin4AdjacentWord.action_matsumotoDiagonalLift]
  rw [fin4SwapAdjacentWord_perm]

theorem fin4SwapAction_centralIncl (p q : Fin 4)
    (z : Multiplicative (MilnorKDeg F 2)) :
    fin4SwapAction (F := F) p q (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z :=
  Fin4AdjacentWord.action_centralIncl _ z

/-- Milnor action of an arbitrary rank-four Weyl generator `wᵢⱼ(u)`. -/
def fin4WeylGeneratorAction {i j : Fin 4} (_hij : i ≠ j) (u : Fˣ) :
    MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4 :=
  (fin4DiagonalAction (F := F)
      (steinbergWeylRootScale (i := i) (j := j) u)).trans
    (fin4SwapAction (F := F) i j)

/-- Milnor Lemma 12.3 for every rank-four Weyl generator. -/
theorem fin4WeylGeneratorAction_matsumotoDiagonalLift {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) {p q : Fin 4} (hpq : p ≠ q) (v : Fˣ) :
    fin4WeylGeneratorAction (F := F) hij u (fin4MatsumotoDiagonalLift hpq v)
      = centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F
            (steinbergWeylRootScale (i := i) (j := j) u p
              * (steinbergWeylRootScale (i := i) (j := j) u q)⁻¹) v))
        * fin4MatsumotoDiagonalLift (equiv_swap_ne i j p q hpq) v := by
  change fin4SwapAction (F := F) i j
      (fin4DiagonalAction (F := F) (steinbergWeylRootScale (i := i) (j := j) u)
        (fin4MatsumotoDiagonalLift hpq v)) = _
  rw [fin4DiagonalAction_matsumotoDiagonalLift, map_mul,
    fin4SwapAction_centralIncl, fin4SwapAction_matsumotoDiagonalLift]

theorem fin4WeylGeneratorAction_centralIncl {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) (z : Multiplicative (MilnorKDeg F 2)) :
    fin4WeylGeneratorAction (F := F) hij u (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z := by
  change fin4SwapAction (F := F) i j
      (fin4DiagonalAction (F := F) (steinbergWeylRootScale (i := i) (j := j) u)
        (centralIncl (F := F) (n := 4) z)) = _
  rw [show fin4DiagonalAction (F := F) (steinbergWeylRootScale (i := i) (j := j) u)
      (centralIncl (F := F) (n := 4) z) = centralIncl (F := F) (n := 4) z by
        apply MilnorDiagonalExtension.ext
        · rfl
        · simp [fin4DiagonalAction],
    fin4SwapAction_centralIncl]

namespace SteinbergWeylWord

/-- Action on Milnor's diagonal extension obtained by evaluating a rank-four Weyl word. -/
def fin4MilnorAction : SteinbergWeylWord F (Fin 4) →
    (MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4)
  | .one => MulEquiv.refl _
  | .snoc word _ _ hij u =>
      (fin4WeylGeneratorAction (F := F) hij u).trans (fin4MilnorAction word)

theorem fin4MilnorAction_centralIncl (word : SteinbergWeylWord F (Fin 4))
    (z : Multiplicative (MilnorKDeg F 2)) :
    fin4MilnorAction word (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z := by
  induction word with
  | one => rfl
  | snoc word i j hij u ih =>
      change fin4MilnorAction word
        (fin4WeylGeneratorAction (F := F) hij u
          (centralIncl (F := F) (n := 4) z)) = _
      rw [fin4WeylGeneratorAction_centralIncl, ih]

/-- **Milnor Lemma 12.3 for an arbitrary signed Weyl word.** The action depends only on its
accumulated signed monomial permutation and scale data. -/
theorem fin4MilnorAction_matsumotoDiagonalLift (word : SteinbergWeylWord F (Fin 4))
    {p q : Fin 4} (hpq : p ≠ q) (v : Fˣ) :
    fin4MilnorAction word (fin4MatsumotoDiagonalLift hpq v)
      = centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd
            (milnorSym2 F (word.scale p * (word.scale q)⁻¹) v))
        * fin4MatsumotoDiagonalLift (word.perm.injective.ne_iff.mpr hpq) v := by
  induction word generalizing p q with
  | one =>
      apply MilnorDiagonalExtension.ext
      · simp [fin4MilnorAction, SteinbergWeylWord.scale, SteinbergWeylWord.perm,
          milnorSym2_one_left]
      · simp [fin4MilnorAction, SteinbergWeylWord.scale, SteinbergWeylWord.perm,
          milnorSym2_one_left]
  | snoc word i j hij u ih =>
      change fin4MilnorAction word
        (fin4WeylGeneratorAction (F := F) hij u
          (fin4MatsumotoDiagonalLift hpq v)) = _
      rw [fin4WeylGeneratorAction_matsumotoDiagonalLift, map_mul,
        fin4MilnorAction_centralIncl, ih]
      apply MilnorDiagonalExtension.ext
      · simp only [diag_mul, centralIncl_diag, one_mul]
        apply Subtype.ext
        rfl
      · simp only [central_mul, centralIncl_central, centralIncl_diag,
          milnorDiagonalCocycle_one_left]
        simp only [SteinbergWeylWord.scale, mul_inv_rev, milnorSym2_mul_left,
          milnorSym2_inv_left, toAdd_ofAdd]
        abel

end SteinbergWeylWord

/-- Three canonical root-diagonal lifts recovering the diagonal projection of any element of `H`. -/
def fin4DiagonalLiftProduct (x : MilnorDiagonalExtension F 4) :
    MilnorDiagonalExtension F 4 :=
  fin4MatsumotoDiagonalLift (by decide : (0 : Fin 4) ≠ 3) (x.diag.1 0)
    * fin4MatsumotoDiagonalLift (by decide : (1 : Fin 4) ≠ 3) (x.diag.1 1)
    * fin4MatsumotoDiagonalLift (by decide : (2 : Fin 4) ≠ 3) (x.diag.1 2)

theorem fin4DiagonalLiftProduct_diag (x : MilnorDiagonalExtension F 4) :
    (fin4DiagonalLiftProduct x).diag = x.diag := by
  apply Subtype.ext
  funext k
  have hprod : x.diag.1 0 * x.diag.1 1 * x.diag.1 2 * x.diag.1 3 = 1 := by
    have h := x.diag.property
    change (∏ i : Fin 4, x.diag.1 i) = 1 at h
    rw [Fin.prod_univ_four] at h
    exact h
  fin_cases k
  · simp [fin4DiagonalLiftProduct, fin4MatsumotoDiagonalLift,
      fin4MatsumotoDiagonal]
  · simp [fin4DiagonalLiftProduct, fin4MatsumotoDiagonalLift,
      fin4MatsumotoDiagonal]
  · simp [fin4DiagonalLiftProduct, fin4MatsumotoDiagonalLift,
      fin4MatsumotoDiagonal]
  · simp [fin4DiagonalLiftProduct, fin4MatsumotoDiagonalLift,
      fin4MatsumotoDiagonal]
    rw [show (x.diag.1 0)⁻¹ * (x.diag.1 1)⁻¹ * (x.diag.1 2)⁻¹
        = (x.diag.1 0 * x.diag.1 1 * x.diag.1 2)⁻¹ by
          simp only [mul_inv_rev]
          ac_rfl]
    exact (eq_inv_of_mul_eq_one_right hprod).symm

/-- Every element of `H` is a central element times three canonical diagonal lifts. -/
theorem exists_central_mul_fin4DiagonalLiftProduct (x : MilnorDiagonalExtension F 4) :
    ∃ z : Multiplicative (MilnorKDeg F 2),
      x = centralIncl (F := F) (n := 4) z * fin4DiagonalLiftProduct x := by
  let y := fin4DiagonalLiftProduct x
  let z : Multiplicative (MilnorKDeg F 2) := Multiplicative.ofAdd ((x * y⁻¹).central)
  refine ⟨z, ?_⟩
  have hcentral : centralIncl (F := F) (n := 4) z = x * y⁻¹ := by
    apply MilnorDiagonalExtension.ext
    · simp [z, y, fin4DiagonalLiftProduct_diag]
    · rfl
  rw [hcentral]
  change x = (x * y⁻¹) * y
  group

private def fin4RootRatio (x : MilnorDiagonalExtension F 4) (p q : Fin 4) : Fˣ :=
  x.diag.1 p * (x.diag.1 q)⁻¹

private def Fin4WeylDeltaProperty {p q : Fin 4} (hpq : p ≠ q)
    (x : MilnorDiagonalExtension F 4) : Prop :=
  x * fin4WeylGeneratorAction (F := F) hpq 1 x⁻¹ =
    fin4MatsumotoDiagonalLift hpq (fin4RootRatio x p q)

private theorem fin4RootRatio_mul (x y : MilnorDiagonalExtension F 4) (p q : Fin 4) :
    fin4RootRatio (x * y) p q = fin4RootRatio x p q * fin4RootRatio y p q := by
  rw [fin4RootRatio, diag_mul]
  change (x.diag.1 p * y.diag.1 p) * (x.diag.1 q * y.diag.1 q)⁻¹ = _
  simp only [fin4RootRatio, mul_inv_rev]
  ac_rfl

private theorem fin4WeylDeltaProperty_mul {p q : Fin 4} (hpq : p ≠ q)
    (x y : MilnorDiagonalExtension F 4)
    (hx : Fin4WeylDeltaProperty hpq x) (hy : Fin4WeylDeltaProperty hpq y) :
    Fin4WeylDeltaProperty hpq (x * y) := by
  let rx := fin4RootRatio x p q
  let ry := fin4RootRatio y p q
  unfold Fin4WeylDeltaProperty at hx hy ⊢
  rw [fin4RootRatio_mul]
  change (x * y) * fin4WeylGeneratorAction (F := F) hpq 1 (x * y)⁻¹ =
    fin4MatsumotoDiagonalLift hpq (rx * ry)
  rw [map_inv, map_mul, mul_inv_rev, ← map_inv, ← map_inv]
  calc
    (x * y) *
          (fin4WeylGeneratorAction (F := F) hpq 1 y⁻¹ *
            fin4WeylGeneratorAction (F := F) hpq 1 x⁻¹) =
        (x * (y * fin4WeylGeneratorAction (F := F) hpq 1 y⁻¹) * x⁻¹) *
          (x * fin4WeylGeneratorAction (F := F) hpq 1 x⁻¹) := by group
    _ = (x * fin4MatsumotoDiagonalLift hpq ry * x⁻¹) *
          fin4MatsumotoDiagonalLift hpq rx := by rw [hy, hx]
    _ = fin4DiagonalAction (F := F) x.diag.1
          (fin4MatsumotoDiagonalLift hpq ry) *
          fin4MatsumotoDiagonalLift hpq rx := by
      rw [fin4DiagonalAction_eq_conj x.diag x _ rfl]
    _ = fin4MatsumotoDiagonalLift hpq (rx * ry) := by
      rw [fin4DiagonalAction_matsumotoDiagonalLift]
      change centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F rx ry)) *
          fin4MatsumotoDiagonalLift hpq ry *
          fin4MatsumotoDiagonalLift hpq rx = _
      rw [mul_assoc, fin4MatsumotoDiagonalLift_mul]
      rw [mul_comm ry rx]
      apply MilnorDiagonalExtension.ext
      · simp [rx, ry, mul_comm]
      · simp only [central_mul, centralIncl_central, centralIncl_diag,
          diag_mul, milnorDiagonalCocycle_one_left, toAdd_ofAdd]
        rw [milnorSym2_antisymm]
        abel

private theorem fin4WeylDeltaProperty_central {p q : Fin 4} (hpq : p ≠ q)
    (z : Multiplicative (MilnorKDeg F 2)) :
    Fin4WeylDeltaProperty hpq (centralIncl (F := F) (n := 4) z) := by
  unfold Fin4WeylDeltaProperty fin4RootRatio
  rw [map_inv, fin4WeylGeneratorAction_centralIncl]
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext k
    simp [fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal]
  · simp [fin4MatsumotoDiagonalLift, milnorSym2_one_left]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
private theorem fin4WeylDeltaProperty_canonical {p q : Fin 4} (hpq : p ≠ q)
    (a : Fin 3) (u : Fˣ) :
    Fin4WeylDeltaProperty hpq
      (fin4MatsumotoDiagonalLift (Fin.ne_of_lt a.castSucc_lt_last) u) := by
  unfold Fin4WeylDeltaProperty fin4RootRatio
  rw [map_inv, fin4WeylGeneratorAction_matsumotoDiagonalLift]
  apply MilnorDiagonalExtension.ext
  · apply Subtype.ext
    funext s
    fin_cases a <;> fin_cases p <;> fin_cases q
    all_goals try { exact (hpq rfl).elim }
    all_goals fin_cases s <;>
      simp [fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal,
        Equiv.swap_apply_def, steinbergWeylRootScale]
  · fin_cases a <;> fin_cases p <;> fin_cases q
    all_goals try { exact (hpq rfl).elim }
    all_goals simp [central_mul, central_inv, diag_mul, diag_inv,
      centralIncl_central, centralIncl_diag,
      fin4MatsumotoDiagonalLift, fin4MatsumotoDiagonal,
      milnorDiagonalCocycle, steinbergWeylRootScale,
      Fin.sum_univ_four, Equiv.swap_apply_def,
      milnorSym2_one_left, milnorSym2_one_right,
      milnorSym2_self, milnorSym2_mul_left, milnorSym2_mul_right,
      milnorSym2_inv_left, milnorSym2_inv_right]
    all_goals have ht := milnorSym2_negOne_left_eq_neg (F := F) u
    all_goals try exact ht
    all_goals try exact ht.symm
    all_goals exact (neg_milnorSym2_negOne_left_add_self (F := F) u).symm

private theorem fin4WeylDeltaProperty_all {p q : Fin 4} (hpq : p ≠ q)
    (x : MilnorDiagonalExtension F 4) :
    Fin4WeylDeltaProperty hpq x := by
  obtain ⟨z, hx⟩ := exists_central_mul_fin4DiagonalLiftProduct x
  rw [hx]
  apply fin4WeylDeltaProperty_mul hpq
  · exact fin4WeylDeltaProperty_central hpq z
  · unfold fin4DiagonalLiftProduct
    apply fin4WeylDeltaProperty_mul hpq
    · apply fin4WeylDeltaProperty_mul hpq
      · simpa using fin4WeylDeltaProperty_canonical hpq (0 : Fin 3) (x.diag.1 0)
      · simpa using fin4WeylDeltaProperty_canonical hpq (1 : Fin 3) (x.diag.1 1)
    · simpa using fin4WeylDeltaProperty_canonical hpq (2 : Fin 3) (x.diag.1 2)

/-- Diagonal half of Milnor Lemma 12.5's second identity.  Conjugating the normalized Weyl
generator by any element of `H` gives the canonical lift of its root character. -/
theorem fin4Diagonal_conj_weylGeneratorAction (x : MilnorDiagonalExtension F 4)
    {p q : Fin 4} (hpq : p ≠ q) :
    x * fin4WeylGeneratorAction (F := F) hpq 1 x⁻¹ =
      fin4MatsumotoDiagonalLift hpq (x.diag.1 p * (x.diag.1 q)⁻¹) :=
  fin4WeylDeltaProperty_all hpq x

/-- Automorphisms of `H` agree when they fix the center and agree on every canonical `hᵢⱼ(u)`. -/
theorem mulEquiv_eq_of_centralIncl_and_matsumotoDiagonalLift
    (f g : MilnorDiagonalExtension F 4 ≃* MilnorDiagonalExtension F 4)
    (hcentral : ∀ z : Multiplicative (MilnorKDeg F 2),
      f (centralIncl (F := F) (n := 4) z) = g (centralIncl (F := F) (n := 4) z))
    (hlift : ∀ {i j : Fin 4} (hij : i ≠ j) (u : Fˣ),
      f (fin4MatsumotoDiagonalLift hij u) = g (fin4MatsumotoDiagonalLift hij u)) :
    f = g := by
  apply MulEquiv.ext
  intro x
  obtain ⟨z, hx⟩ := exists_central_mul_fin4DiagonalLiftProduct x
  rw [hx, map_mul, map_mul, hcentral]
  simp only [fin4DiagonalLiftProduct, map_mul]
  rw [hlift, hlift, hlift]

/-- Signed monomial matrix data are unique. -/
theorem signedMonomialMatrix_data_injective {σ τ : Equiv.Perm (Fin 4)}
    {c d : Fin 4 → Fˣ}
    (h : signedMonomialMatrix σ c = signedMonomialMatrix τ d) :
    σ = τ ∧ c = d := by
  have hperm_apply : ∀ p : Fin 4, σ p = τ p := by
    intro p
    by_contra hne
    have hentry := congrFun (congrFun h (σ p)) p
    simp [signedMonomialMatrix, hne] at hentry
  have hperm : σ = τ := Equiv.ext hperm_apply
  have hscale : c = d := by
    funext p
    apply Units.ext
    have hentry := congrFun (congrFun h (σ p)) p
    simpa [signedMonomialMatrix, ← hperm] using hentry
  exact ⟨hperm, hscale⟩

theorem steinbergWeylWord_perm_scale_eq_of_eval_eq
    (w₁ w₂ : SteinbergWeylWord F (Fin 4)) (h : w₁.eval = w₂.eval) :
    w₁.perm = w₂.perm ∧ w₁.scale = w₂.scale := by
  apply signedMonomialMatrix_data_injective
  rw [← steinbergWeylWord_matrix w₁, ← steinbergWeylWord_matrix w₂, h]

namespace SteinbergWeylWord

theorem fin4MilnorAction_eq_of_perm_scale_eq (w₁ w₂ : SteinbergWeylWord F (Fin 4))
    (hperm : w₁.perm = w₂.perm) (hscale : w₁.scale = w₂.scale) :
    fin4MilnorAction w₁ = fin4MilnorAction w₂ := by
  apply mulEquiv_eq_of_centralIncl_and_matsumotoDiagonalLift
  · intro z
    rw [fin4MilnorAction_centralIncl, fin4MilnorAction_centralIncl]
  · intro i j hij u
    rw [fin4MilnorAction_matsumotoDiagonalLift,
      fin4MilnorAction_matsumotoDiagonalLift, hperm, hscale]

/-- Weyl-word action descends through word evaluation: equal Steinberg elements act identically. -/
theorem fin4MilnorAction_eq_of_eval_eq (w₁ w₂ : SteinbergWeylWord F (Fin 4))
    (h : w₁.eval = w₂.eval) :
    fin4MilnorAction w₁ = fin4MilnorAction w₂ := by
  obtain ⟨hperm, hscale⟩ := steinbergWeylWord_perm_scale_eq_of_eval_eq w₁ w₂ h
  exact fin4MilnorAction_eq_of_perm_scale_eq w₁ w₂ hperm hscale

theorem fin4MilnorAction_append (w₁ w₂ : SteinbergWeylWord F (Fin 4)) :
    fin4MilnorAction
        (GaloisForLFunctions.HTGeometry.SteinbergWeylWord.append w₁ w₂)
      = fin4MilnorAction w₁ * fin4MilnorAction w₂ := by
  induction w₂ generalizing w₁ with
  | one => rfl
  | snoc w₂ i j hij u ih =>
      change (fin4WeylGeneratorAction (F := F) hij u).trans
          (fin4MilnorAction
            (GaloisForLFunctions.HTGeometry.SteinbergWeylWord.append w₁ w₂))
        = fin4MilnorAction w₁ *
          ((fin4WeylGeneratorAction (F := F) hij u).trans (fin4MilnorAction w₂))
      rw [ih]
      rfl

end SteinbergWeylWord

noncomputable def fin4WeylSubgroupChosenWord
    (x : steinbergWeylWordSubgroup (F := F) (n := Fin 4)) :
    SteinbergWeylWord F (Fin 4) :=
  Classical.choose (SteinbergWeylWord.exists_of_mem_subgroup x.property)

theorem fin4WeylSubgroupChosenWord_eval
    (x : steinbergWeylWordSubgroup (F := F) (n := Fin 4)) :
    (fin4WeylSubgroupChosenWord x).eval = x.1 :=
  Classical.choose_spec (SteinbergWeylWord.exists_of_mem_subgroup x.property)

/-- **Descended Milnor action of the rank-four Weyl-word subgroup.** -/
noncomputable def fin4WeylSubgroupActionHom :
    steinbergWeylWordSubgroup (F := F) (n := Fin 4) →*
      MulAut (MilnorDiagonalExtension F 4) where
  toFun x := SteinbergWeylWord.fin4MilnorAction (fin4WeylSubgroupChosenWord x)
  map_one' := by
    calc
      SteinbergWeylWord.fin4MilnorAction (fin4WeylSubgroupChosenWord 1)
          = SteinbergWeylWord.fin4MilnorAction (.one : SteinbergWeylWord F (Fin 4)) := by
              apply SteinbergWeylWord.fin4MilnorAction_eq_of_eval_eq
              rw [fin4WeylSubgroupChosenWord_eval]
              rfl
      _ = 1 := rfl
  map_mul' x y := by
    let wx := fin4WeylSubgroupChosenWord x
    let wy := fin4WeylSubgroupChosenWord y
    calc
      SteinbergWeylWord.fin4MilnorAction (fin4WeylSubgroupChosenWord (x * y))
          = SteinbergWeylWord.fin4MilnorAction
              (GaloisForLFunctions.HTGeometry.SteinbergWeylWord.append wx wy) := by
              apply SteinbergWeylWord.fin4MilnorAction_eq_of_eval_eq
              rw [fin4WeylSubgroupChosenWord_eval,
                GaloisForLFunctions.HTGeometry.SteinbergWeylWord.eval_append,
                fin4WeylSubgroupChosenWord_eval, fin4WeylSubgroupChosenWord_eval]
              rfl
      _ = SteinbergWeylWord.fin4MilnorAction wx
          * SteinbergWeylWord.fin4MilnorAction wy :=
        SteinbergWeylWord.fin4MilnorAction_append wx wy

theorem fin4WeylSubgroupActionHom_centralIncl
    (x : steinbergWeylWordSubgroup (F := F) (n := Fin 4))
    (z : Multiplicative (MilnorKDeg F 2)) :
    fin4WeylSubgroupActionHom x (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z :=
  SteinbergWeylWord.fin4MilnorAction_centralIncl _ z

theorem fin4SimpleWeylSubgroup_le_weylWord :
    fin4SimpleWeylSubgroup (F := F)
      ≤ steinbergWeylWordSubgroup (F := F) (n := Fin 4) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, j, hij, rfl⟩
  exact Subgroup.subset_closure ⟨i, j, hij, (1 : Fˣ), rfl⟩

def fin4SimpleWeylToWeylWord :
    fin4SimpleWeylSubgroup (F := F) →*
      steinbergWeylWordSubgroup (F := F) (n := Fin 4) :=
  Subgroup.inclusion fin4SimpleWeylSubgroup_le_weylWord

/-- Milnor Lemma 12.3 as an action of the simple signed-Weyl subgroup `W₀`. -/
noncomputable def fin4SimpleWeylActionHom :
    fin4SimpleWeylSubgroup (F := F) →* MulAut (MilnorDiagonalExtension F 4) :=
  fin4WeylSubgroupActionHom.comp fin4SimpleWeylToWeylWord

theorem fin4SimpleWeylActionHom_centralIncl
    (x : fin4SimpleWeylSubgroup (F := F))
    (z : Multiplicative (MilnorKDeg F 2)) :
    fin4SimpleWeylActionHom x (centralIncl (F := F) (n := 4) z)
      = centralIncl (F := F) (n := 4) z :=
  fin4WeylSubgroupActionHom_centralIncl _ z

/-- Semidirect precursor `H ⋊ W₀` to Milnor's amalgamated monomial extension. -/
abbrev MilnorWPre (F : Type*) [Field F] :=
  MilnorDiagonalExtension F 4 ⋊[fin4SimpleWeylActionHom (F := F)]
    fin4SimpleWeylSubgroup (F := F)

def milnorWPreCentralIncl :
    Multiplicative (MilnorKDeg F 2) →* MilnorWPre F :=
  SemidirectProduct.inl.comp centralIncl

theorem milnorWPreCentralIncl_injective :
    Function.Injective (milnorWPreCentralIncl (F := F)) :=
  SemidirectProduct.inl_injective.comp centralIncl_injective

theorem milnorWPreCentralIncl_mem_center (z : Multiplicative (MilnorKDeg F 2)) :
    milnorWPreCentralIncl (F := F) z ∈ Subgroup.center (MilnorWPre F) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply SemidirectProduct.ext
  · simp only [milnorWPreCentralIncl, MonoidHom.comp_apply,
      SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rw [fin4SimpleWeylActionHom_centralIncl]
    exact ((centralIncl_mem_center z).comm x.left).symm
  · change x.right * 1 = 1 * x.right
    simp

end MilnorDiagonalExtension

end GaloisForLFunctions.HTGeometry
