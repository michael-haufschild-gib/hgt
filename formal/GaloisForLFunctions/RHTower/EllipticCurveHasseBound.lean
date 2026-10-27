import GaloisForLFunctions.RHTower.HyperellipticDescent
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction

/-!
# Hasse's theorem for elliptic curves over finite fields of odd characteristic

For a Weierstrass curve `W` over a finite field `F` of odd characteristic, completing the square
turns the equation into `(2y + a₁x + a₃)² = g(x)` with the 2-torsion polynomial
`g = 4X³ + b₂X² + 2b₄X + b₆` (`equation_iff_sq_eq`). Its discriminant is `16Δ`, so `g` is
squarefree when `W` is elliptic (`squarefree_twoTorsionPolynomial`). The affine points are the
solutions of `y'² = g(x)` (`card_equation_eq`) and the point at infinity is one more; the
odd-degree hyperelliptic Hasse–Weil bound gives (`abs_natCard_point_sub_le`)

  `|#W(F) − (q + 1)| ≤ 2√q`.

At a place of good reduction with odd residue characteristic this bounds the trace of mathlib's
local polynomial `1 − aT + qT²` of the L-function (`abs_localTrace_le`). The proof is by counting: Stepanov's auxiliary section, the Gauss-sum modulus, and descent from the
splitting field of `g`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.EllipticHasse

open Hyperelliptic

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F)

/-- The 2-torsion polynomial `4X³ + b₂X² + 2b₄X + b₆`. -/
noncomputable def twoTorsionPoly : F[X] := W.twoTorsionPolynomial.toPoly

omit [Fintype F] in
theorem twoTorsionPoly_eval (x : F) :
    (twoTorsionPoly W).eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [twoTorsionPoly, Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial]

omit [Fintype F] in
/-- **Completing the square**: `W(x, y) = 0 ⇔ (2y + a₁x + a₃)² = g(x)` in odd characteristic. -/
theorem equation_iff_sq_eq (hF : ringChar F ≠ 2) (x y : F) :
    W.toAffine.Equation x y ↔ (2 * y + W.a₁ * x + W.a₃) ^ 2 = (twoTorsionPoly W).eval x := by
  have h4 : (4 : F) ≠ 0 := by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [WeierstrassCurve.Affine.equation_iff', twoTorsionPoly_eval]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  constructor
  · intro h; linear_combination 4 * h
  · intro h
    have : (4 : F) * (y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h4

omit [Fintype F] in
theorem natDegree_twoTorsionPoly (hF : ringChar F ≠ 2) : (twoTorsionPoly W).natDegree = 3 := by
  have h4 : (4 : F) ≠ 0 := by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  exact Cubic.natDegree_of_a_ne_zero (P := W.twoTorsionPolynomial) h4

omit [Fintype F] in
/-- **The 2-torsion polynomial of an elliptic curve is squarefree** in odd characteristic: its
discriminant is `16Δ ≠ 0`, so its roots in a splitting field are distinct. -/
theorem squarefree_twoTorsionPoly (hF : ringChar F ≠ 2) [W.IsElliptic] :
    Squarefree (twoTorsionPoly W) := by
  have h2 : IsUnit (2 : F) := (Ring.two_ne_zero hF).isUnit
  have h4 : W.twoTorsionPolynomial.a ≠ 0 := by
    change (4 : F) ≠ 0
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2.ne_zero h2.ne_zero
  set K := (twoTorsionPoly W).SplittingField
  have hsplit : ((twoTorsionPoly W).map (algebraMap F K)).Splits := SplittingField.splits _
  have hdisc := W.twoTorsionPolynomial_discr_ne_zero h2 W.isUnit_Δ
  have hnodup := (Cubic.discr_ne_zero_iff_roots_nodup (φ := algebraMap F K) h4 hsplit).mp hdisc
  have hne : (twoTorsionPoly W).map (algebraMap F K) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap F K).injective]
    intro h
    have := natDegree_twoTorsionPoly W hF
    rw [h, natDegree_zero] at this
    exact absurd this (by norm_num)
  have hsep : ((twoTorsionPoly W).map (algebraMap F K)).Separable := by
    rw [← nodup_roots_iff_of_splits hne hsplit]
    rwa [Cubic.roots, Cubic.map_toPoly] at hnodup
  exact ((separable_map (algebraMap F K)).mp hsep).squarefree

/-- **The affine points are the points of `y'² = g(x)`**, by `y' = 2y + a₁x + a₃`. -/
theorem card_equation_eq (hF : ringChar F ≠ 2) :
    Fintype.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} =
      (univ.filter fun q : F × F => q.2 ^ 2 = (twoTorsionPoly W).eval q.1).card := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [Fintype.card_subtype]
  refine Finset.card_nbij' (fun q => (q.1, 2 * q.2 + W.a₁ * q.1 + W.a₃))
    (fun q => (q.1, (q.2 - W.a₁ * q.1 - W.a₃) / 2)) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hq ⊢
    exact (equation_iff_sq_eq W hF q.1 q.2).mp hq
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hq ⊢
    rw [equation_iff_sq_eq W hF]
    convert hq using 2
    field_simp
    ring
  · intro q _
    ext
    · rfl
    · simp only
      field_simp
      ring
  · intro q _
    ext
    · rfl
    · simp only
      field_simp
      ring

/-- **Hasse's theorem**: an elliptic curve over a finite field `F` of odd characteristic,
`q = |F|`, has `|#W(F) − (q + 1)| ≤ 2√q` points (the affine points and the point at infinity). -/
theorem abs_natCard_point_sub_le (hF : ringChar F ≠ 2) [W.IsElliptic] :
    |(Nat.card W.toAffine.Point : ℝ) - (Fintype.card F + 1)| ≤ 2 * Real.sqrt (Fintype.card F) := by
  have hcard : Nat.card W.toAffine.Point =
      Fintype.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
    rw [Nat.card_congr (WeierstrassCurve.Affine.pointEquiv W.toAffine), WithZero,
      Finite.card_option, Nat.card_eq_fintype_card]
  have hodd : Odd (twoTorsionPoly W).natDegree := by
    rw [natDegree_twoTorsionPoly W hF]; decide
  have hHW := abs_card_points_sub_le_oddHyperelliptic hF (squarefree_twoTorsionPoly W hF) hodd F
  simp only [Algebra.algebraMap_self, aeval_def, eval₂_id, natDegree_twoTorsionPoly W hF] at hHW
  rw [hcard, card_equation_eq W hF]
  push_cast
  convert hHW using 1
  · ring_nf
  · norm_num

/-- **Hasse's theorem at a place of good reduction**: for a Weierstrass curve over the fraction field
of a discrete valuation ring with finite residue field `κ` of odd characteristic, if the minimal
model has good reduction then the trace `a = |κ| + 1 − #W̃(κ)` of the local polynomial
`1 − aT + |κ|T²` satisfies `|a| ≤ 2√|κ|`. -/
theorem abs_localTrace_le (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (V : WeierstrassCurve K)
    [Finite (IsLocalRing.ResidueField R)] (h2 : ringChar (IsLocalRing.ResidueField R) ≠ 2)
    [hgood : (V.minimal R).HasGoodReduction R] :
    |((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
        Nat.card ((V.minimal R).reduction R).toAffine.Point : ℝ)| ≤
      2 * Real.sqrt (Nat.card (IsLocalRing.ResidueField R)) := by
  letI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  haveI : ((V.minimal R).reduction R).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp hgood
  have h := abs_natCard_point_sub_le ((V.minimal R).reduction R) h2
  rw [Nat.card_eq_fintype_card (α := IsLocalRing.ResidueField R)]
  rw [abs_sub_comm] at h
  push_cast
  convert h using 2

end GaloisForLFunctions.RHTower.EllipticHasse
