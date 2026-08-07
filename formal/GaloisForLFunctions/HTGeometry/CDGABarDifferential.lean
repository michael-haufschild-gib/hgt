import GaloisForLFunctions.HTGeometry.CDGABarHead

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
