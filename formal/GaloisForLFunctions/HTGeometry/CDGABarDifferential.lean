import GaloisForLFunctions.HTGeometry.CDGABarHead
import Mathlib.Algebra.DirectSum.Module

/-!
# The bar differential

The bar differential of a tensor power of the shifted augmentation ideal multiplies one adjacent
pair of factors, so it lowers the number of factors by one and raises the total degree by one.
Written recursively on the number of factors it is the head — multiplying the first two — plus the
bar differential of the tail tensored with the identity, which carries the Koszul sign of the degree
of the first factor.  On one factor there is no adjacent pair, so it is zero.

* `HTGeometry.barD` : the bar differential.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

/-- **The bar differential**: on `k + 1` factors it multiplies the first two and adds the bar
differential of the last `k`, with the Koszul sign of the first factor. -/
noncomputable def barD : ∀ (k n : ℕ),
    (barPower ε (k + 1)).carrier n →ₗ[R] (barPower ε k).carrier (n + 1)
  | 0, _ => 0
  | (k + 1), n =>
      barHeadₗ ε (barPower ε k).carrier n
        + tensorRightDegOneₗ (M := barShiftFamily ε)
          (N := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
          (N' := (barPower ε k).carrier) (fun b => barD k b) n

theorem barD_zero (n : ℕ) : barD ε 0 n = 0 := rfl

/-- **On two factors the bar differential is the head alone**, since there is no tail to
differentiate. -/
theorem barD_one (n : ℕ) (F : (barPower ε 2).carrier n) :
    barD ε 1 n F = barHeadₗ ε (barPower ε 0).carrier n F := by
  show barHeadₗ ε (barPower ε 0).carrier n F
      + tensorRightDegOneₗ (M := barShiftFamily ε) (fun b => barD ε 0 b) n F = _
  show barHeadₗ ε (barPower ε 0).carrier n F
      + tensorRightDegOne (M := barShiftFamily ε) (fun b => barD ε 0 b) n F = _
  rw [show (fun b => barD ε 0 b) = (fun b => (0 : (barPower ε 1).carrier b →ₗ[R]
      (barPower ε 0).carrier (b + 1))) from funext fun b => barD_zero ε b,
    tensorRightDegOne_zero_map, add_zero]

theorem barD_one_eq (n : ℕ) : barD ε 1 n = barHeadₗ ε (barPower ε 0).carrier n :=
  LinearMap.ext fun F => barD_one ε n F

/-- **The bar differential of two factors is killed by the next one**, which has nothing left to
multiply. -/
theorem barD_comp_zero (n : ℕ) (F : (barPower ε 2).carrier n) :
    barD ε 0 (n + 1) (barD ε 1 n F) = 0 := by
  rw [barD_zero]
  rfl

theorem barD_succ (k n : ℕ) :
    barD ε (k + 1) n
      = barHeadₗ ε (barPower ε k).carrier n
        + tensorRightDegOneₗ (M := barShiftFamily ε)
          (N := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
          (N' := (barPower ε k).carrier) (fun b => barD ε k b) n := rfl

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open DirectSum

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

/-- **The bar construction**: in each degree, the direct sum over the number of factors of the
tensor powers of the shifted augmentation ideal. -/
abbrev BarCarrier (n : ℕ) : Type u := DirectSum ℕ fun k => (barPower ε k).carrier n

/-- The component of the total differential on the `k`-fold tensor power: the internal differential,
which keeps the number of factors, plus the bar differential, which lowers it by one. -/
noncomputable def barTotalComponent : ∀ (k n : ℕ),
    (barPower ε k).carrier n →ₗ[R] BarCarrier ε (n + 1)
  | 0, n => (DirectSum.lof R ℕ (fun k => (barPower ε k).carrier (n + 1)) 0).comp
      ((barPower ε 0).d n)
  | (k + 1), n =>
      (DirectSum.lof R ℕ (fun j => (barPower ε j).carrier (n + 1)) (k + 1)).comp
          ((barPower ε (k + 1)).d n)
        + (DirectSum.lof R ℕ (fun j => (barPower ε j).carrier (n + 1)) k).comp (barD ε k n)

/-- **The total differential of the bar construction.** -/
noncomputable def barTotalD (n : ℕ) : BarCarrier ε n →ₗ[R] BarCarrier ε (n + 1) :=
  DirectSum.toModule R ℕ _ fun k => barTotalComponent ε k n

theorem barTotalD_of (k n : ℕ) (x : (barPower ε k).carrier n) :
    barTotalD ε n (DirectSum.lof R ℕ (fun j => (barPower ε j).carrier n) k x)
      = barTotalComponent ε k n x := by
  show DirectSum.toModule R ℕ _ (fun j => barTotalComponent ε j n)
    (DirectSum.lof R ℕ (fun j => (barPower ε j).carrier n) k x) = _
  rw [DirectSum.toModule_lof]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open DirectSum

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

/-- **The counit of the bar construction**: the component with no factors. -/
noncomputable def barCounit (n : ℕ) :
    BarCarrier ε n →ₗ[R] (barPower ε 0).carrier n :=
  DirectSum.component R ℕ (fun k => (barPower ε k).carrier n) 0

/-- **The counit is a morphism of complexes.**  The ground stage has no differential, and nothing can
be multiplied down into it, so every contribution to the component with no factors vanishes. -/
theorem barCounit_totalD (n : ℕ) (k : ℕ) (y : (barPower ε k).carrier n) :
    barCounit ε (n + 1)
        (barTotalD ε n (DirectSum.lof R ℕ (fun j => (barPower ε j).carrier n) k y)) = 0 := by
  rw [barTotalD_of]
  cases k with
  | zero =>
      show DirectSum.component R ℕ (fun j => (barPower ε j).carrier (n + 1)) 0
        ((DirectSum.lof R ℕ (fun j => (barPower ε j).carrier (n + 1)) 0)
          ((barPower ε 0).d n y)) = 0
      rw [DirectSum.component.lof_self]
      rfl
  | succ k' =>
      show DirectSum.component R ℕ (fun j => (barPower ε j).carrier (n + 1)) 0
        ((DirectSum.lof R ℕ (fun j => (barPower ε j).carrier (n + 1)) (k' + 1))
            ((barPower ε (k' + 1)).d n y)
          + (DirectSum.lof R ℕ (fun j => (barPower ε j).carrier (n + 1)) k')
            (barD ε k' n y)) = 0
      rw [map_add, DirectSum.component.of, DirectSum.component.of, dif_neg (by omega)]
      cases k' with
      | zero =>
          simp only [barD_zero, dif_pos]
          rw [LinearMap.zero_apply, add_zero]
      | succ k'' => rw [dif_neg (by omega), add_zero]

end GaloisForLFunctions.HTGeometry
