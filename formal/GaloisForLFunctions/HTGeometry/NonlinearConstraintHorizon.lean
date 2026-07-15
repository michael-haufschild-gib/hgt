import GaloisForLFunctions.HTGeometry.ProjectiveHorizonComplementarity
import Mathlib.Tactic

/-!
# Nonlinear constraints rigidify derivative horizons

For the nonlinear observation surface `z = x * y`, the first derivatives of its three
coordinates determine the hidden coordinates `x` and `y` as soon as the derivative-frame
Wronskian is nonzero.  This is the exact algebraic core of the statement that a nonlinear
constraint removes the additive integration gauge retained by an affine observation channel.

No flow or carrier is introduced: the reconstruction uses only a static algebraic constraint
and its differentiated consequences.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The derivative-frame determinant for the bilinear constraint `z = x * y`. -/
def bilinearHorizonWronskian
    {K : Type*} [CommRing K] [Differential K] (x y : K) : K :=
  x′ * y′′ - x′′ * y′

/-- The second differentiated consequence of the static bilinear constraint. -/
theorem secondDeriv_mul_eq
    {K : Type*} [CommRing K] [Differential K] (x y : K) :
    (x * y)′′ = x′′ * y + 2 * x′ * y′ + x * y′′ := by
  rw [Derivation.leibniz, map_add]
  simp only [smul_eq_mul]
  rw [Derivation.leibniz, Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- A bilinear constraint reconstructs its left coordinate from first and second horizon data. -/
theorem bilinearConstraint_reconstruct_left
    {K : Type*} [Field K] [Differential K]
    (x y : K) (hW : bilinearHorizonWronskian x y ≠ 0) :
    x =
      (x′ * ((x * y)′′ - 2 * x′ * y′) - x′′ * (x * y)′) /
        bilinearHorizonWronskian x y := by
  unfold bilinearHorizonWronskian
  rw [secondDeriv_mul_eq, Derivation.leibniz]
  simp only [smul_eq_mul]
  apply (eq_div_iff hW).2
  simp only [bilinearHorizonWronskian]
  ring

/-- A bilinear constraint reconstructs its right coordinate from first and second horizon data. -/
theorem bilinearConstraint_reconstruct_right
    {K : Type*} [Field K] [Differential K]
    (x y : K) (hW : bilinearHorizonWronskian x y ≠ 0) :
    y =
      (y′′ * (x * y)′ - y′ * ((x * y)′′ - 2 * x′ * y′)) /
        bilinearHorizonWronskian x y := by
  unfold bilinearHorizonWronskian
  rw [secondDeriv_mul_eq, Derivation.leibniz]
  simp only [smul_eq_mul]
  apply (eq_div_iff hW).2
  simp only [bilinearHorizonWronskian]
  ring

/-- **Bilinear horizon rigidity.**  A derivation-closed field containing the first derivative
of each coordinate on `z = x * y` contains the hidden coordinate `x` when the derivative frame
is nondegenerate. -/
theorem bilinearConstraint_left_mem_of_firstJets_mem
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x y : K) (hW : bilinearHorizonWronskian x y ≠ 0)
    (hx : x′ ∈ L) (hy : y′ ∈ L) (hxy : (x * y)′ ∈ L) :
    x ∈ L := by
  have hx2 : x′′ ∈ L := hL hx
  have hy2 : y′′ ∈ L := hL hy
  have hxy2 : (x * y)′′ ∈ L := hL hxy
  have hWmem : bilinearHorizonWronskian x y ∈ L :=
    sub_mem (mul_mem hx hy2) (mul_mem hx2 hy)
  have hnum :
      x′ * ((x * y)′′ - 2 * x′ * y′) - x′′ * (x * y)′ ∈ L := by
    exact sub_mem
      (mul_mem hx (sub_mem hxy2 (mul_mem (mul_mem (natCast_mem L 2) hx) hy)))
      (mul_mem hx2 hxy)
  rw [bilinearConstraint_reconstruct_left x y hW]
  exact div_mem hnum hWmem

/-- **Bilinear horizon rigidity.**  Under the same static constraint, the first derivative
horizon also contains the hidden coordinate `y`. -/
theorem bilinearConstraint_right_mem_of_firstJets_mem
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x y : K) (hW : bilinearHorizonWronskian x y ≠ 0)
    (hx : x′ ∈ L) (hy : y′ ∈ L) (hxy : (x * y)′ ∈ L) :
    y ∈ L := by
  have hx2 : x′′ ∈ L := hL hx
  have hy2 : y′′ ∈ L := hL hy
  have hxy2 : (x * y)′′ ∈ L := hL hxy
  have hWmem : bilinearHorizonWronskian x y ∈ L :=
    sub_mem (mul_mem hx hy2) (mul_mem hx2 hy)
  have hnum :
      y′′ * (x * y)′ - y′ * ((x * y)′′ - 2 * x′ * y′) ∈ L := by
    exact sub_mem (mul_mem hy2 hxy)
      (mul_mem hy (sub_mem hxy2 (mul_mem (mul_mem (natCast_mem L 2) hx) hy)))
  rw [bilinearConstraint_reconstruct_right x y hW]
  exact div_mem hnum hWmem

/-- The first derivative horizon of the nonlinear surface `z = x * y` contains both hidden
coordinates whenever its derivative-frame determinant is nonzero. -/
theorem bilinearConstraint_pair_mem_of_firstJets_mem
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x y : K) (hW : bilinearHorizonWronskian x y ≠ 0)
    (hx : x′ ∈ L) (hy : y′ ∈ L) (hxy : (x * y)′ ∈ L) :
    x ∈ L ∧ y ∈ L :=
  ⟨bilinearConstraint_left_mem_of_firstJets_mem L hL x y hW hx hy hxy,
    bilinearConstraint_right_mem_of_firstJets_mem L hL x y hW hx hy hxy⟩

end

end GaloisForLFunctions
