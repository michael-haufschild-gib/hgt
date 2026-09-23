import GaloisForLFunctions.HTGeometry.NonlinearConstraintHorizon
import Mathlib.Tactic

/-!
# A two-chart core for the projective horizon building

Two distinct affine charts of a differential-generic projective curve have complementary
positive-jet horizons.  This file formalizes the coordinate reconstruction at the first
higher-rank case: inversion recovers the chart denominator, and a projective ratio then recovers
every transverse coordinate.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- Once a projective chart denominator `x` is visible, the derivative of the transverse ratio
`y / x` reconstructs `y` from first-order data. -/
theorem projectiveRatio_reconstruct_transverse
    {K : Type*} [Field K] [Differential K]
    (x y : K) (hx : x ≠ 0) (hdx : x′ ≠ 0) :
    y = (y′ * x - (y / x)′ * x ^ (2 : ℕ)) / x′ := by
  rw [(Differential.deriv : Derivation ℤ K K).leibniz_div]
  simp only [smul_eq_mul]
  apply (eq_div_iff hdx).2
  field_simp [hx]
  ring

/-- Opposite affine-chart horizons reconstruct the projective denominator inside any
derivation-closed intermediate field. -/
theorem projectiveTwoChart_denominator_mem
    {F K : Type*} [Field F] [Field K] [CharZero K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x : K) (hx : x ≠ 0) (hdx : x′ ≠ 0)
    (hx1 : x′ ∈ L) (hinv1 : (x⁻¹)′ ∈ L) :
    x ∈ L := by
  have hx2 : x′′ ∈ L := hL hx1
  have hinv2 : (x⁻¹)′′ ∈ L := hL hinv1
  have hden : x′′ / x′ - (x⁻¹)′′ / (x⁻¹)′ ∈ L :=
    sub_mem (div_mem hx2 hx1) (div_mem hinv2 hinv1)
  have hrec : x = 2 * x′ / (x′′ / x′ - (x⁻¹)′′ / (x⁻¹)′) :=
    projectiveInversion_twoJet_reconstruction x hx hdx
  rw [hrec]
  exact div_mem (mul_mem (natCast_mem L 2) hx1) hden

/-- After the denominator has been reconstructed, the second chart reconstructs a transverse
coordinate from the derivative of its projective ratio. -/
theorem projectiveTwoChart_transverse_mem
    {F K : Type*} [Field F] [Field K] [CharZero K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x y : K) (hx : x ≠ 0) (hdx : x′ ≠ 0)
    (hx1 : x′ ∈ L) (hy1 : y′ ∈ L)
    (hinv1 : (x⁻¹)′ ∈ L) (hratio1 : (y / x)′ ∈ L) :
    y ∈ L := by
  have hxmem : x ∈ L :=
    projectiveTwoChart_denominator_mem L hL x hx hdx hx1 hinv1
  have hnum : y′ * x - (y / x)′ * x ^ (2 : ℕ) ∈ L :=
    sub_mem (mul_mem hy1 hxmem) (mul_mem hratio1 (pow_mem hxmem 2))
  rw [projectiveRatio_reconstruct_transverse x y hx hdx]
  exact div_mem hnum hx1

/-- **Two-chart projective complementarity.**  Positive-jet data in two distinct standard
projective charts reconstruct both the denominator and one arbitrary transverse coordinate. -/
theorem projectiveTwoChart_pair_mem
    {F K : Type*} [Field F] [Field K] [CharZero K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x y : K) (hx : x ≠ 0) (hdx : x′ ≠ 0)
    (hx1 : x′ ∈ L) (hy1 : y′ ∈ L)
    (hinv1 : (x⁻¹)′ ∈ L) (hratio1 : (y / x)′ ∈ L) :
    x ∈ L ∧ y ∈ L :=
  ⟨projectiveTwoChart_denominator_mem L hL x hx hdx hx1 hinv1,
    projectiveTwoChart_transverse_mem L hL x y hx hdx hx1 hy1 hinv1 hratio1⟩

/-- **Arbitrary-dimensional two-chart complementarity.**  The positive jets of two distinct
standard projective charts reconstruct the common denominator and every transverse coordinate.
The index type is unrestricted; finite-dimensional projective space is the principal case. -/
theorem projectiveTwoChart_family_mem
    {F K ι : Type*} [Field F] [Field K] [CharZero K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x : K) (y : ι → K) (hx : x ≠ 0) (hdx : x′ ≠ 0)
    (hx1 : x′ ∈ L) (hy1 : ∀ i, (y i)′ ∈ L)
    (hinv1 : (x⁻¹)′ ∈ L) (hratio1 : ∀ i, (y i / x)′ ∈ L) :
    x ∈ L ∧ ∀ i, y i ∈ L := by
  refine ⟨projectiveTwoChart_denominator_mem L hL x hx hdx hx1 hinv1, ?_⟩
  intro i
  exact projectiveTwoChart_transverse_mem
    L hL x (y i) hx hdx hx1 (hy1 i) hinv1 (hratio1 i)

end

end GaloisForLFunctions
