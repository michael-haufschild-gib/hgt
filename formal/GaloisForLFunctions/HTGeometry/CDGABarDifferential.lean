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
      (show (barPower ε (k + 1 + 1)).carrier n →ₗ[R] (barPower ε (k + 1)).carrier (n + 1) from
        barHeadₗ ε (barPower ε k).carrier n)
        + (show (barPower ε (k + 1 + 1)).carrier n →ₗ[R] (barPower ε (k + 1)).carrier (n + 1) from
          tensorRightDegOneₗ (M := barShiftFamily ε) (fun b => barD k b) n)

theorem barD_zero (n : ℕ) : barD ε 0 n = 0 := rfl

theorem barD_succ (k n : ℕ) :
    barD ε (k + 1) n
      = (show (barPower ε (k + 1 + 1)).carrier n →ₗ[R] (barPower ε (k + 1)).carrier (n + 1) from
          barHeadₗ ε (barPower ε k).carrier n)
        + (show (barPower ε (k + 1 + 1)).carrier n →ₗ[R] (barPower ε (k + 1)).carrier (n + 1) from
          tensorRightDegOneₗ (M := barShiftFamily ε) (fun b => barD ε k b) n) := rfl

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
