/-
# The σ-saturated dyadic tower inside the graded Mahler carrier

The dyadic layers `ℂ(t^{2⁻ⁿ})(ℓ)` form an increasing tower of subfields of the graded
Mahler carrier.  Their union is stable under the graded Mahler automorphism `σ` in both
directions — pulling one layer deeper inverts the exponent doubling — and under the
untwisted derivation `δ = ℓ·θ`.  This module builds that saturated subfield, restricts
`σ` to an automorphism and `δ` to a derivation of it, and applies the automorphism-family
Ostrowski criterion: the normalized velocity `A·ℓ⁻¹` is an additive `σ`-primitive whose
telescoper obstruction holds on every layer, so `A` is differentially transcendental over
`ℂ(t)` with respect to the Euler derivation.
-/
import Mathlib
import GaloisForLFunctions.U0.MahlerLayerEmbedding
import GaloisForLFunctions.AutomorphismFamilyOstrowski

namespace GaloisForLFunctions

open Polynomial HahnSeries
open scoped Differential

noncomputable section

/-! ## Derivation calculus on the carrier -/

theorem eulerDeriv_single (s : ℚ) (c : RatFunc ℂ) :
    eulerDeriv (HahnSeries.single s c) =
      HahnSeries.single s (algebraMap ℚ (RatFunc ℂ) s * c) := by
  ext q
  rw [eulerDeriv_coeff]
  rcases eq_or_ne q s with rfl | hq
  · rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne hq, HahnSeries.coeff_single_of_ne hq, mul_zero]

theorem mahlerDeriv_single (s : ℚ) (c : RatFunc ℂ) :
    mahlerDeriv (HahnSeries.single s c) =
      HahnSeries.single 0 (algebraMap ℚ (RatFunc ℂ) s) * mahlerEll *
        HahnSeries.single s c := by
  have hrhs : HahnSeries.single (0 : ℚ) (algebraMap ℚ (RatFunc ℂ) s) * mahlerEll *
      HahnSeries.single s c =
      HahnSeries.single s (algebraMap ℚ (RatFunc ℂ) s * RatFunc.X * c) := by
    rw [mahlerEll, HahnSeries.single_mul_single, HahnSeries.single_mul_single, zero_add,
      zero_add]
  rw [hrhs]
  ext q
  rcases eq_or_ne q s with rfl | hq
  · rw [mahlerDeriv_coeff, HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
    ring
  · rw [mahlerDeriv_coeff, HahnSeries.coeff_single_of_ne hq,
      HahnSeries.coeff_single_of_ne hq, mul_zero, mul_zero]

theorem eulerDeriv_one : eulerDeriv (1 : HahnSeries ℚ (RatFunc ℂ)) = 0 := by
  ext q
  rw [eulerDeriv_coeff, HahnSeries.coeff_one]
  rcases eq_or_ne q 0 with rfl | hq
  · rw [if_pos rfl, map_zero, zero_mul]
    rfl
  · rw [if_neg hq, mul_zero]
    rfl

theorem mahlerDeriv_one : mahlerDeriv (1 : HahnSeries ℚ (RatFunc ℂ)) = 0 := by
  rw [mahlerDeriv, eulerDeriv_one, mul_zero]

theorem mahlerDeriv_mahlerEll : mahlerDeriv mahlerEll = 0 := by
  rw [mahlerEll, mahlerDeriv_single, map_zero]
  rw [HahnSeries.single_eq_zero_iff.mpr rfl, zero_mul, zero_mul]

theorem mahlerDeriv_mahlerT : mahlerDeriv mahlerT = mahlerEll * mahlerT := by
  rw [mahlerT, mahlerDeriv_single, map_one]
  rw [show HahnSeries.single (0 : ℚ) (1 : RatFunc ℂ) = 1 from rfl, one_mul]

theorem mahlerDeriv_two : mahlerDeriv (2 : HahnSeries ℚ (RatFunc ℂ)) = 0 := by
  rw [show (2 : HahnSeries ℚ (RatFunc ℂ)) = 1 + 1 from by norm_num, mahlerDeriv_add,
    mahlerDeriv_one, add_zero]

theorem mahlerDeriv_pow_eq_zero {x : HahnSeries ℚ (RatFunc ℂ)} (hx : mahlerDeriv x = 0)
    (n : ℕ) : mahlerDeriv (x ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero, mahlerDeriv_one]
  | succ n ih => rw [pow_succ, mahlerDeriv_mul, ih, hx, zero_mul, mul_zero, add_zero]

theorem mahlerDeriv_inv {x : HahnSeries ℚ (RatFunc ℂ)} (hx : x ≠ 0) :
    mahlerDeriv x⁻¹ = -(x⁻¹ * x⁻¹ * mahlerDeriv x) := by
  have hxx : x * x⁻¹ = (1 : HahnSeries ℚ (RatFunc ℂ)) :=
    mul_inv_cancel₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) hx
  have hxx' : x⁻¹ * x = (1 : HahnSeries ℚ (RatFunc ℂ)) :=
    inv_mul_cancel₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) hx
  have h1 : mahlerDeriv (x * x⁻¹) = 0 := by
    rw [hxx, mahlerDeriv_one]
  rw [mahlerDeriv_mul] at h1
  have h2 : x * mahlerDeriv x⁻¹ = -(mahlerDeriv x * x⁻¹) := by linear_combination h1
  have h3 : x⁻¹ * (x * mahlerDeriv x⁻¹) = x⁻¹ * -(mahlerDeriv x * x⁻¹) := by rw [h2]
  rw [← mul_assoc, hxx', one_mul] at h3
  rw [h3]
  ring

theorem mahlerDeriv_inv_eq_zero {x : HahnSeries ℚ (RatFunc ℂ)}
    (hx : mahlerDeriv x = 0) : mahlerDeriv x⁻¹ = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [inv_zero (G₀ := HahnSeries ℚ (RatFunc ℂ)), hx]
  · rw [mahlerDeriv_inv hx0, hx, mul_zero, neg_zero]

theorem mahlerDeriv_zpow_eq_zero {x : HahnSeries ℚ (RatFunc ℂ)}
    (hx : mahlerDeriv x = 0) (z : ℤ) : mahlerDeriv (x ^ z) = 0 := by
  rcases z with n | n
  · simpa using mahlerDeriv_pow_eq_zero hx n
  · rw [zpow_negSucc]
    exact mahlerDeriv_inv_eq_zero (mahlerDeriv_pow_eq_zero hx (n + 1))

/-- Quotient rule for the untwisted Mahler derivation. -/
theorem mahlerDeriv_div (P S : HahnSeries ℚ (RatFunc ℂ)) (hS : S ≠ 0) :
    mahlerDeriv (P / S) = (mahlerDeriv P * S - P * mahlerDeriv S) / (S * S) := by
  have hPS : P / S * S = P := div_mul_cancel₀ P hS
  have h1 : mahlerDeriv P = mahlerDeriv (P / S) * S + P / S * mahlerDeriv S := by
    conv_lhs => rw [← hPS, mahlerDeriv_mul]
  have hSS : (S * S) ≠ 0 := mul_ne_zero hS hS
  have key : mahlerDeriv (P / S) * (S * S) =
      mahlerDeriv P * S - P * mahlerDeriv S := by
    calc mahlerDeriv (P / S) * (S * S)
        = (mahlerDeriv (P / S) * S + P / S * mahlerDeriv S - P / S * mahlerDeriv S) * S := by
          ring
      _ = (mahlerDeriv P - P / S * mahlerDeriv S) * S := by rw [← h1]
      _ = mahlerDeriv P * S - P / S * S * mahlerDeriv S := by ring
      _ = mahlerDeriv P * S - P * mahlerDeriv S := by rw [hPS]
  calc mahlerDeriv (P / S)
      = mahlerDeriv (P / S) * (S * S) * (S * S)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) hSS, mul_one]
    _ = (mahlerDeriv P * S - P * mahlerDeriv S) * (S * S)⁻¹ := by rw [key]
    _ = (mahlerDeriv P * S - P * mahlerDeriv S) / (S * S) := (div_eq_mul_inv _ _).symm

/-! ## Halving: each layer sits inside the next -/

theorem coeffSquare_cond : nonZeroDivisors (Polynomial MahlerBase) ≤
    Submonoid.comap (Polynomial.mapRingHom (MahlerPolynomial.mahlerHom 0).toRingHom)
      (nonZeroDivisors (Polynomial MahlerBase)) := by
  intro q hq
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h0
  apply hq
  apply Polynomial.map_injective _ (MahlerPolynomial.mahlerHom 0).toRingHom.injective
  rw [Polynomial.map_zero]
  exact h0

/-- The dyadic coefficient substitution `u ↦ u²` on two-variable rational functions,
acting through the coefficient field and fixing the eigenvariable. -/
def coeffSquare : RatFunc MahlerBase →+* RatFunc MahlerBase :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (MahlerPolynomial.mahlerHom 0).toRingHom)
    coeffSquare_cond

theorem coeffSquare_apply_div (p q : Polynomial MahlerBase) :
    coeffSquare (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
          (p.map (MahlerPolynomial.mahlerHom 0).toRingHom) /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
          (q.map (MahlerPolynomial.mahlerHom 0).toRingHom) := by
  have hcoe : coeffSquare (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      RatFunc.map (Polynomial.mapRingHom (MahlerPolynomial.mahlerHom 0).toRingHom)
        coeffSquare_cond
        (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
          algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) :=
    congrFun (RatFunc.coe_mapRingHom_eq_coe_map _ _) _
  rw [hcoe, RatFunc.map_apply_div]
  rfl

/-- Halving the monomial exponent is the dyadic substitution on the coefficient field. -/
theorem monoRatEval_halving (q₀ : ℚ) (hq₀ : 0 < q₀) (f : RatFunc ℂ) :
    monoRatEval (q₀ / 2) (by positivity) (MahlerPolynomial.mahlerHom 0 f) =
      monoRatEval q₀ hq₀ f := by
  induction f using RatFunc.induction_on with
  | _ p s hs =>
    have hφdiv : MahlerPolynomial.mahlerHom 0
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p / algebraMap (Polynomial ℂ) (RatFunc ℂ) s) =
        MahlerPolynomial.mahlerHom 0 (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) /
          MahlerPolynomial.mahlerHom 0 (algebraMap (Polynomial ℂ) (RatFunc ℂ) s) :=
      map_div₀ _ _ _
    rw [hφdiv, MahlerPolynomial.mahlerHom_algebraMap, MahlerPolynomial.mahlerHom_algebraMap]
    have hcomp : ∀ w : Polynomial ℂ, w.comp (Polynomial.X ^ 2 + Polynomial.C 0) =
        Polynomial.expand ℂ 2 w := by
      intro w
      rw [map_zero, add_zero, ← Polynomial.expand_eq_comp_X_pow]
    rw [hcomp, hcomp]
    have hmono : ∀ w : Polynomial ℂ,
        monoRatEval (q₀ / 2) (by positivity)
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.expand ℂ 2 w)) =
        monoRatEval q₀ hq₀ (algebraMap (Polynomial ℂ) (RatFunc ℂ) w) := by
      intro w
      show hahnBaseChange (monoRatEvalC (q₀ / 2) (by positivity)
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.expand ℂ 2 w))) =
        hahnBaseChange (monoRatEvalC q₀ hq₀ (algebraMap (Polynomial ℂ) (RatFunc ℂ) w))
      rw [monoRatEvalC_algebraMap, monoRatEvalC_algebraMap]
      congr 1
      show Polynomial.eval₂ HahnSeries.C (HahnSeries.single (q₀ / 2) 1)
          (Polynomial.expand ℂ 2 w) =
        Polynomial.eval₂ HahnSeries.C (HahnSeries.single q₀ 1) w
      rw [Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp]
      congr 1
      rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, sq, HahnSeries.single_mul_single,
        mul_one]
      congr 1
      ring_nf
    have hMdiv : ∀ (g₁ g₂ : RatFunc ℂ),
        monoRatEval (q₀ / 2) (by positivity) (g₁ / g₂) =
          monoRatEval (q₀ / 2) (by positivity) g₁ / monoRatEval (q₀ / 2) (by positivity) g₂ :=
      fun g₁ g₂ => map_div₀ (f := monoRatEval (q₀ / 2) (by positivity)) (a := g₁) (b := g₂)
    have hNdiv : ∀ (g₁ g₂ : RatFunc ℂ),
        monoRatEval q₀ hq₀ (g₁ / g₂) =
          monoRatEval q₀ hq₀ g₁ / monoRatEval q₀ hq₀ g₂ :=
      fun g₁ g₂ => map_div₀ (f := monoRatEval q₀ hq₀) (a := g₁) (b := g₂)
    rw [hMdiv, hNdiv, hmono, hmono]

/-- Halving at the polynomial layer: the coefficientwise dyadic substitution absorbs an
exponent halving of the base monomial. -/
theorem layerPolyEval_halving (q₀ : ℚ) (hq₀ : 0 < q₀) (p : Polynomial MahlerBase) :
    layerPolyEval (q₀ / 2) (by positivity)
        (p.map (MahlerPolynomial.mahlerHom 0).toRingHom) =
      layerPolyEval q₀ hq₀ p := by
  have hhom : (layerPolyEval (q₀ / 2) (by positivity)).comp
      (Polynomial.mapRingHom (MahlerPolynomial.mahlerHom 0).toRingHom) =
      layerPolyEval q₀ hq₀ := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply]
      rw [show Polynomial.mapRingHom (MahlerPolynomial.mahlerHom 0).toRingHom
          (Polynomial.C a) = Polynomial.C (MahlerPolynomial.mahlerHom 0 a) from
        Polynomial.map_C _]
      rw [layerPolyEval_C, layerPolyEval_C]
      exact monoRatEval_halving q₀ hq₀ a
    · rw [RingHom.comp_apply]
      rw [show Polynomial.mapRingHom (MahlerPolynomial.mahlerHom 0).toRingHom
          Polynomial.X = Polynomial.X from Polynomial.map_X _]
      rw [layerPolyEval_X, layerPolyEval_X]
  have := congrFun (congrArg (fun (g : Polynomial MahlerBase →+*
      HahnSeries ℚ (RatFunc ℂ)) => (g : Polynomial MahlerBase →
      HahnSeries ℚ (RatFunc ℂ))) hhom) p
  simpa using this

/-- Halving at the field layer: each dyadic layer embedding factors through the next. -/
theorem layerEmbed_halving (q₀ : ℚ) (hq₀ : 0 < q₀) (f : RatFunc MahlerBase) :
    layerEmbed (q₀ / 2) (by positivity) (coeffSquare f) = layerEmbed q₀ hq₀ f := by
  induction f using RatFunc.induction_on with
  | _ p s hs =>
    rw [coeffSquare_apply_div, layerEmbed_apply_div, layerEmbed_apply_div,
      layerPolyEval_halving, layerPolyEval_halving]

/-! ## The eigenvariable doubling on two-variable rational functions -/

/-- The eigenvariable dilation `ℓ ↦ 2ℓ` as a polynomial algebra equivalence over the
coefficient field. -/
def satEllPolyScale : Polynomial MahlerBase ≃ₐ[MahlerBase] Polynomial MahlerBase :=
  letI : Invertible (2 : MahlerBase) := invertibleOfNonzero two_ne_zero
  algEquivCMulXAddC 2 0

theorem satEllPolyScale_ne_zero {p : Polynomial MahlerBase} (hp : p ≠ 0) :
    satEllPolyScale p ≠ 0 := by
  intro h
  apply hp
  have := congrArg satEllPolyScale.symm h
  simpa using this

theorem satEllPolyScale_symm_ne_zero {p : Polynomial MahlerBase} (hp : p ≠ 0) :
    satEllPolyScale.symm p ≠ 0 := by
  intro h
  apply hp
  have := congrArg satEllPolyScale h
  simpa using this

theorem satEllScale_cond : nonZeroDivisors (Polynomial MahlerBase) ≤
    Submonoid.comap satEllPolyScale.toAlgHom.toRingHom
      (nonZeroDivisors (Polynomial MahlerBase)) := by
  intro q hq
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  exact satEllPolyScale_ne_zero hq

theorem satEllScaleInv_cond : nonZeroDivisors (Polynomial MahlerBase) ≤
    Submonoid.comap satEllPolyScale.symm.toAlgHom.toRingHom
      (nonZeroDivisors (Polynomial MahlerBase)) := by
  intro q hq
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  exact satEllPolyScale_symm_ne_zero hq

/-- Forward eigenvariable dilation `ℓ ↦ 2ℓ` on two-variable rational functions. -/
def satEllScaleHom : RatFunc MahlerBase →+* RatFunc MahlerBase :=
  RatFunc.mapRingHom satEllPolyScale.toAlgHom.toRingHom satEllScale_cond

/-- Backward eigenvariable dilation `ℓ ↦ ℓ/2` on two-variable rational functions. -/
def satEllScaleInvHom : RatFunc MahlerBase →+* RatFunc MahlerBase :=
  RatFunc.mapRingHom satEllPolyScale.symm.toAlgHom.toRingHom satEllScaleInv_cond

theorem satEllScaleHom_apply_div (p q : Polynomial MahlerBase) :
    satEllScaleHom (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (satEllPolyScale p) /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (satEllPolyScale q) := by
  have hcoe : satEllScaleHom (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      RatFunc.map satEllPolyScale.toAlgHom.toRingHom satEllScale_cond
        (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
          algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) :=
    congrFun (RatFunc.coe_mapRingHom_eq_coe_map _ _) _
  rw [hcoe, RatFunc.map_apply_div]
  rfl

theorem satEllScaleInvHom_apply_div (p q : Polynomial MahlerBase) :
    satEllScaleInvHom (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (satEllPolyScale.symm p) /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase)
          (satEllPolyScale.symm q) := by
  have hcoe : satEllScaleInvHom (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      RatFunc.map satEllPolyScale.symm.toAlgHom.toRingHom satEllScaleInv_cond
        (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
          algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) :=
    congrFun (RatFunc.coe_mapRingHom_eq_coe_map _ _) _
  rw [hcoe, RatFunc.map_apply_div]
  rfl

theorem satEllScaleHom_symm_apply (f : RatFunc MahlerBase) :
    satEllScaleHom (satEllScaleInvHom f) = f := by
  induction f using RatFunc.induction_on with
  | _ p s hs =>
    rw [satEllScaleInvHom_apply_div, satEllScaleHom_apply_div,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- The polynomial two-variable Mahler transform is the coefficient substitution composed
with the eigenvariable dilation, in either order. -/
theorem twoVarPolyHom_eq_map_scale (p : Polynomial MahlerBase) :
    twoVarPolyHom p =
      (satEllPolyScale p).map (MahlerPolynomial.mahlerHom 0).toRingHom := by
  have hhom : (twoVarPolyHom : Polynomial MahlerBase →+* Polynomial MahlerBase) =
      (Polynomial.mapRingHom (MahlerPolynomial.mahlerHom 0).toRingHom).comp
        satEllPolyScale.toAlgHom.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [twoVarPolyHom_C, RingHom.comp_apply]
      rw [show satEllPolyScale.toAlgHom.toRingHom (Polynomial.C a) = Polynomial.C a from by
        show satEllPolyScale (Polynomial.C a) = Polynomial.C a
        rw [satEllPolyScale]
        letI : Invertible (2 : MahlerBase) := invertibleOfNonzero two_ne_zero
        rw [algEquivCMulXAddC_apply, Polynomial.aeval_C, Polynomial.algebraMap_eq]]
      exact (Polynomial.map_C _).symm
    · rw [twoVarPolyHom_X, RingHom.comp_apply]
      rw [show satEllPolyScale.toAlgHom.toRingHom Polynomial.X =
          Polynomial.C 2 * Polynomial.X + Polynomial.C 0 from by
        show satEllPolyScale Polynomial.X = _
        rw [satEllPolyScale]
        letI : Invertible (2 : MahlerBase) := invertibleOfNonzero two_ne_zero
        rw [algEquivCMulXAddC_apply, Polynomial.aeval_X]]
      rw [map_zero, add_zero, Polynomial.coe_mapRingHom, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, map_ofNat, map_ofNat, map_ofNat]
  exact congrFun (congrArg (fun (g : Polynomial MahlerBase →+* Polynomial MahlerBase) =>
    (g : Polynomial MahlerBase → Polynomial MahlerBase)) hhom) p

/-- The two-variable Mahler transform factors as coefficient substitution after
eigenvariable dilation. -/
theorem twoVarMahler_eq_coeffSquare_scale (f : RatFunc MahlerBase) :
    twoVarMahler f = coeffSquare (satEllScaleHom f) := by
  induction f using RatFunc.induction_on with
  | _ p s hs =>
    rw [twoVarMahler_apply_div, satEllScaleHom_apply_div, coeffSquare_apply_div,
      twoVarPolyHom_eq_map_scale, twoVarPolyHom_eq_map_scale]


/-! ## The dyadic layer tower -/

/-- The base-monomial exponent of the `n`-th dyadic layer. -/
def layerQ (n : ℕ) : ℚ := ((2 : ℚ) ^ n)⁻¹

theorem layerQ_pos (n : ℕ) : 0 < layerQ n := by
  rw [layerQ]
  positivity

theorem layerQ_half (n : ℕ) : layerQ n / 2 = layerQ (n + 1) := by
  rw [layerQ, layerQ, pow_succ, mul_inv, div_eq_mul_inv]

/-- The `n`-th dyadic layer subfield `ℂ(t^{2⁻ⁿ})(ℓ)` of the carrier. -/
def layerField (n : ℕ) : Subfield (HahnSeries ℚ (RatFunc ℂ)) :=
  RingHom.fieldRange (K := RatFunc MahlerBase) (L := HahnSeries ℚ (RatFunc ℂ))
    (layerEmbed (layerQ n) (layerQ_pos n))

theorem mem_layerField_iff {n : ℕ} {z : HahnSeries ℚ (RatFunc ℂ)} :
    z ∈ layerField n ↔ ∃ f, layerEmbed (layerQ n) (layerQ_pos n) f = z :=
  RingHom.mem_fieldRange (K := RatFunc MahlerBase) (L := HahnSeries ℚ (RatFunc ℂ))

theorem layerEmbed_mem_layerField (n : ℕ) (f : RatFunc MahlerBase) :
    layerEmbed (layerQ n) (layerQ_pos n) f ∈ layerField n :=
  mem_layerField_iff.mpr ⟨f, rfl⟩

theorem layerEmbed_congr {q₁ q₂ : ℚ} (h : q₁ = q₂) (h₁ : 0 < q₁) (f : RatFunc MahlerBase) :
    layerEmbed q₁ h₁ f = layerEmbed q₂ (h ▸ h₁) f := by
  subst h
  rfl

/-- The halving identity, indexed along the dyadic tower. -/
theorem layerEmbed_succ_coeffSquare (n : ℕ) (f : RatFunc MahlerBase) :
    layerEmbed (layerQ (n + 1)) (layerQ_pos (n + 1)) (coeffSquare f) =
      layerEmbed (layerQ n) (layerQ_pos n) f := by
  rw [layerEmbed_congr ((layerQ_half n).symm : layerQ (n + 1) = layerQ n / 2)
    (layerQ_pos (n + 1)) (coeffSquare f)]
  exact layerEmbed_halving (layerQ n) (layerQ_pos n) f

theorem layerField_mono (n : ℕ) : layerField n ≤ layerField (n + 1) := by
  intro z hz
  obtain ⟨f, rfl⟩ := mem_layerField_iff.mp hz
  exact mem_layerField_iff.mpr ⟨coeffSquare f, layerEmbed_succ_coeffSquare n f⟩

theorem layerField_le {m n : ℕ} (h : m ≤ n) : layerField m ≤ layerField n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (layerField_mono _)

/-- The saturated dyadic tower field: the union of all dyadic layers. -/
def mahlerSat : Subfield (HahnSeries ℚ (RatFunc ℂ)) := ⨆ n, layerField n

theorem layerField_le_mahlerSat (n : ℕ) : layerField n ≤ mahlerSat :=
  le_iSup layerField n

theorem mem_mahlerSat_iff {z : HahnSeries ℚ (RatFunc ℂ)} :
    z ∈ mahlerSat ↔ ∃ n, z ∈ layerField n :=
  Subfield.mem_iSup_of_directed
    ((monotone_nat_of_le_succ layerField_mono).directed_le)

/-! ## Stability of the tower under the graded Mahler automorphism -/

theorem mahlerSigma_layerField_mem {n : ℕ} {z : HahnSeries ℚ (RatFunc ℂ)}
    (hz : z ∈ layerField n) : mahlerSigma z ∈ layerField n := by
  obtain ⟨f, rfl⟩ := mem_layerField_iff.mp hz
  rw [mahlerSigma_layerEmbed]
  exact layerEmbed_mem_layerField n (twoVarMahler f)

/-- Every layer element is the `σ`-image of an element one layer deeper: the eigenvariable
dilation is inverted there and the coefficient substitution is absorbed by halving. -/
theorem exists_sigma_eq_of_mem_layerField {n : ℕ} {z : HahnSeries ℚ (RatFunc ℂ)}
    (hz : z ∈ layerField n) : ∃ w ∈ layerField (n + 1), mahlerSigma w = z := by
  obtain ⟨f, rfl⟩ := mem_layerField_iff.mp hz
  refine ⟨layerEmbed (layerQ (n + 1)) (layerQ_pos (n + 1)) (satEllScaleInvHom f),
    layerEmbed_mem_layerField (n + 1) _, ?_⟩
  rw [mahlerSigma_layerEmbed, twoVarMahler_eq_coeffSquare_scale, satEllScaleHom_symm_apply]
  exact layerEmbed_succ_coeffSquare n f

theorem mahlerSigma_mahlerSat_mem {z : HahnSeries ℚ (RatFunc ℂ)}
    (hz : z ∈ mahlerSat) : mahlerSigma z ∈ mahlerSat := by
  obtain ⟨n, hn⟩ := mem_mahlerSat_iff.mp hz
  exact layerField_le_mahlerSat n (mahlerSigma_layerField_mem hn)

theorem mahlerSigma_symm_mahlerSat_mem {z : HahnSeries ℚ (RatFunc ℂ)}
    (hz : z ∈ mahlerSat) : mahlerSigma.symm z ∈ mahlerSat := by
  obtain ⟨n, hn⟩ := mem_mahlerSat_iff.mp hz
  obtain ⟨w, hw, hws⟩ := exists_sigma_eq_of_mem_layerField hn
  have hsymm : mahlerSigma.symm z = w := by
    rw [← hws, RingEquiv.symm_apply_apply]
  rw [hsymm]
  exact layerField_le_mahlerSat (n + 1) hw

/-- The graded Mahler automorphism restricted to the saturated tower field. -/
def mahlerSatTau : mahlerSat ≃+* mahlerSat where
  toFun z := ⟨mahlerSigma z.val, mahlerSigma_mahlerSat_mem z.prop⟩
  invFun z := ⟨mahlerSigma.symm z.val, mahlerSigma_symm_mahlerSat_mem z.prop⟩
  left_inv z := Subtype.ext (RingEquiv.symm_apply_apply mahlerSigma z.val)
  right_inv z := Subtype.ext (RingEquiv.apply_symm_apply mahlerSigma z.val)
  map_mul' x y := Subtype.ext (map_mul mahlerSigma x.val y.val)
  map_add' x y := Subtype.ext (map_add mahlerSigma x.val y.val)

theorem mahlerSatTau_val (z : mahlerSat) :
    (mahlerSatTau z).val = mahlerSigma z.val := rfl

/-! ## Stability of the tower under the untwisted derivation -/

theorem layerEmbed_ratFuncC (n : ℕ) (e : MahlerBase) :
    layerEmbed (layerQ n) (layerQ_pos n) (RatFunc.C e) =
      monoRatEval (layerQ n) (layerQ_pos n) e := by
  rw [show (RatFunc.C e : RatFunc MahlerBase) =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (Polynomial.C e) from
    (RatFunc.algebraMap_C e).symm]
  rw [layerEmbed_algebraMap, layerPolyEval_C]

theorem monoRatEval_mem_layerField (n : ℕ) (e : MahlerBase) :
    monoRatEval (layerQ n) (layerQ_pos n) e ∈ layerField n := by
  rw [← layerEmbed_ratFuncC]
  exact layerEmbed_mem_layerField n _

theorem mahlerEll_mem_layerField (n : ℕ) : mahlerEll ∈ layerField n := by
  have h : layerEmbed (layerQ n) (layerQ_pos n)
      (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) Polynomial.X) = mahlerEll := by
    rw [layerEmbed_algebraMap, layerPolyEval_X]
  rw [← h]
  exact layerEmbed_mem_layerField n _

theorem layerPolyEval_mem_layerField (n : ℕ) (p : Polynomial MahlerBase) :
    layerPolyEval (layerQ n) (layerQ_pos n) p ∈ layerField n := by
  rw [← layerEmbed_algebraMap]
  exact layerEmbed_mem_layerField n _

/-- A rational constant of the coefficient field lies on every layer. -/
theorem hahn_ratCast_const_mem_layerField (n : ℕ) (r : ℚ) :
    HahnSeries.single (0 : ℚ) (algebraMap ℚ (RatFunc ℂ) r) ∈ layerField n := by
  have hcast : algebraMap ℚ (RatFunc ℂ) r = algebraMap ℂ (RatFunc ℂ) ((r : ℂ)) := by
    rw [eq_ratCast (algebraMap ℚ (RatFunc ℂ)) r, map_ratCast]
  rw [hcast, ← monoRatEval_ratFuncC (layerQ n) (layerQ_pos n)]
  exact monoRatEval_mem_layerField n _

theorem mahlerDeriv_monoRatEval_poly_mem (n : ℕ) (p : Polynomial ℂ) :
    mahlerDeriv (monoRatEval (layerQ n) (layerQ_pos n)
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)) ∈ layerField n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, mahlerDeriv_add]
    exact Subfield.add_mem _ hp hq
  | monomial j c =>
    have hmono : monoRatEval (layerQ n) (layerQ_pos n)
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.monomial j c)) =
        HahnSeries.single ((j : ℚ) * layerQ n) (algebraMap ℂ (RatFunc ℂ) c) := by
      rw [show (Polynomial.monomial j c : Polynomial ℂ) =
          Polynomial.C c * Polynomial.X ^ j from by
        rw [Polynomial.C_mul_X_pow_eq_monomial]]
      rw [map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        monoRatEval_ratFuncC, monoRatEval_X, HahnSeries.single_pow, one_pow,
        HahnSeries.single_mul_single, zero_add, mul_one]
      congr 1
    rw [hmono, mahlerDeriv_single]
    refine Subfield.mul_mem _ (Subfield.mul_mem _ ?_ (mahlerEll_mem_layerField n)) ?_
    · exact hahn_ratCast_const_mem_layerField n _
    · rw [← hmono]
      exact monoRatEval_mem_layerField n _

theorem mahlerDeriv_monoRatEval_mem (n : ℕ) (f : RatFunc ℂ) :
    mahlerDeriv (monoRatEval (layerQ n) (layerQ_pos n) f) ∈ layerField n := by
  induction f using RatFunc.induction_on with
  | _ p s hs =>
    have hdiv : monoRatEval (layerQ n) (layerQ_pos n)
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p / algebraMap (Polynomial ℂ) (RatFunc ℂ) s) =
        monoRatEval (layerQ n) (layerQ_pos n) (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) /
          monoRatEval (layerQ n) (layerQ_pos n) (algebraMap (Polynomial ℂ) (RatFunc ℂ) s) :=
      map_div₀ (f := monoRatEval (layerQ n) (layerQ_pos n)) (a := _) (b := _)
    have hs0 : algebraMap (Polynomial ℂ) (RatFunc ℂ) s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))).mpr hs
    have hS0 : monoRatEval (layerQ n) (layerQ_pos n)
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) s) ≠ 0 :=
      (map_ne_zero_iff _ (monoRatEval (layerQ n) (layerQ_pos n)).injective).mpr hs0
    rw [hdiv, mahlerDeriv_div _ _ hS0]
    have hpmem : ∀ w : Polynomial ℂ, monoRatEval (layerQ n) (layerQ_pos n)
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) w) ∈ layerField n :=
      fun w => monoRatEval_mem_layerField n _
    exact Subfield.div_mem _
      (Subfield.sub_mem _
        (Subfield.mul_mem _ (mahlerDeriv_monoRatEval_poly_mem n p) (hpmem s))
        (Subfield.mul_mem _ (hpmem p) (mahlerDeriv_monoRatEval_poly_mem n s)))
      (Subfield.mul_mem _ (hpmem s) (hpmem s))

theorem mahlerDeriv_layerPolyEval_mem (n : ℕ) (p : Polynomial MahlerBase) :
    mahlerDeriv (layerPolyEval (layerQ n) (layerQ_pos n) p) ∈ layerField n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, mahlerDeriv_add]
    exact Subfield.add_mem _ hp hq
  | monomial i e =>
    rw [show (Polynomial.monomial i e : Polynomial MahlerBase) =
        Polynomial.C e * Polynomial.X ^ i from by
      rw [Polynomial.C_mul_X_pow_eq_monomial]]
    rw [map_mul, map_pow, layerPolyEval_C, layerPolyEval_X, mahlerDeriv_mul,
      mahlerDeriv_pow_eq_zero mahlerDeriv_mahlerEll i, mul_zero, add_zero]
    exact Subfield.mul_mem _ (mahlerDeriv_monoRatEval_mem n e)
      (Subfield.pow_mem _ (mahlerEll_mem_layerField n) i)

theorem mahlerDeriv_layerField_mem {n : ℕ} {z : HahnSeries ℚ (RatFunc ℂ)}
    (hz : z ∈ layerField n) : mahlerDeriv z ∈ layerField n := by
  obtain ⟨f, rfl⟩ := mem_layerField_iff.mp hz
  induction f using RatFunc.induction_on with
  | _ p s hs =>
    have hS0 : layerPolyEval (layerQ n) (layerQ_pos n) s ≠ 0 :=
      layerPolyEval_ne_zero (layerQ_pos n) hs
    rw [layerEmbed_apply_div, mahlerDeriv_div _ _ hS0]
    exact Subfield.div_mem _
      (Subfield.sub_mem _
        (Subfield.mul_mem _ (mahlerDeriv_layerPolyEval_mem n p)
          (layerPolyEval_mem_layerField n s))
        (Subfield.mul_mem _ (layerPolyEval_mem_layerField n p)
          (mahlerDeriv_layerPolyEval_mem n s)))
      (Subfield.mul_mem _ (layerPolyEval_mem_layerField n s)
        (layerPolyEval_mem_layerField n s))

theorem mahlerDeriv_mahlerSat_mem {z : HahnSeries ℚ (RatFunc ℂ)}
    (hz : z ∈ mahlerSat) : mahlerDeriv z ∈ mahlerSat := by
  obtain ⟨n, hn⟩ := mem_mahlerSat_iff.mp hz
  exact layerField_le_mahlerSat n (mahlerDeriv_layerField_mem hn)


/-! ## The carrier and the tower as differential fields -/

theorem mahlerDeriv_zero : mahlerDeriv (0 : HahnSeries ℚ (RatFunc ℂ)) = 0 := by
  ext q
  rw [mahlerDeriv_coeff]
  rw [show (0 : HahnSeries ℚ (RatFunc ℂ)).coeff q = 0 from rfl, mul_zero, mul_zero]

theorem mahlerDeriv_neg (x : HahnSeries ℚ (RatFunc ℂ)) :
    mahlerDeriv (-x) = -(mahlerDeriv x) := by
  have h : mahlerDeriv (x + (-x)) = 0 := by
    rw [add_neg_cancel, mahlerDeriv_zero]
  rw [mahlerDeriv_add] at h
  linear_combination h

/-- The carrier as a differential field under `δ = ℓ·θ`. -/
noncomputable instance mahlerCarrierDifferential :
    Differential (HahnSeries ℚ (RatFunc ℂ)) := by
  letI : Algebra ℤ (HahnSeries ℚ (RatFunc ℂ)) := Ring.toIntAlgebra _
  exact ⟨Derivation.mk'
    (AddMonoidHom.toIntLinearMap
      { toFun := mahlerDeriv
        map_zero' := mahlerDeriv_zero
        map_add' := mahlerDeriv_add })
    (fun a b => by
      show mahlerDeriv (a * b) = a • mahlerDeriv b + b • mahlerDeriv a
      rw [smul_eq_mul, smul_eq_mul, mahlerDeriv_mul]
      ring)⟩

theorem carrier_deriv_eq (x : HahnSeries ℚ (RatFunc ℂ)) : x′ = mahlerDeriv x := rfl

/-- The saturated tower as a differential field, by restriction. -/
noncomputable instance mahlerSatDifferential : Differential ↥mahlerSat := by
  letI : Algebra ℤ ↥mahlerSat := Ring.toIntAlgebra _
  exact ⟨Derivation.mk'
    (AddMonoidHom.toIntLinearMap
      { toFun := fun z => ⟨mahlerDeriv z.val, mahlerDeriv_mahlerSat_mem z.prop⟩
        map_zero' := Subtype.ext mahlerDeriv_zero
        map_add' := fun a b => Subtype.ext (mahlerDeriv_add a.val b.val) })
    (fun a b => by
      apply Subtype.ext
      show mahlerDeriv (a.val * b.val) =
        (a • (⟨mahlerDeriv b.val, mahlerDeriv_mahlerSat_mem b.prop⟩ : ↥mahlerSat) +
          b • ⟨mahlerDeriv a.val, mahlerDeriv_mahlerSat_mem a.prop⟩ : ↥mahlerSat).val
      rw [show (a • (⟨mahlerDeriv b.val, mahlerDeriv_mahlerSat_mem b.prop⟩ : ↥mahlerSat) +
          b • (⟨mahlerDeriv a.val, mahlerDeriv_mahlerSat_mem a.prop⟩ : ↥mahlerSat) :
          ↥mahlerSat).val =
        a.val * mahlerDeriv b.val + b.val * mahlerDeriv a.val from rfl]
      rw [mahlerDeriv_mul]
      ring)⟩

theorem mahlerSat_deriv_val (z : ↥mahlerSat) : (z′).val = mahlerDeriv z.val := rfl

/-- The tower inclusion is a differential-algebra morphism. -/
instance : DifferentialAlgebra ↥mahlerSat (HahnSeries ℚ (RatFunc ℂ)) :=
  ⟨fun _ => rfl⟩

theorem differentialJet_mahlerSat_val (m : ℕ) (x : ↥mahlerSat) :
    (differentialJet m x).val = mahlerDeriv^[m] x.val := by
  induction m with
  | zero => rw [differentialJet_zero, Function.iterate_zero_apply]
  | succ m ih =>
    rw [differentialJet_succ, Function.iterate_succ_apply', ← ih]
    rfl

/-! ## The generators of the base layer and the shift element -/

theorem monoRatEval_X_pow_two_pow (n : ℕ) :
    monoRatEval (layerQ n) (layerQ_pos n) ((RatFunc.X : RatFunc ℂ) ^ (2 ^ n)) = mahlerT := by
  rw [map_pow, monoRatEval_X, HahnSeries.single_pow, one_pow, mahlerT]
  congr 1
  rw [nsmul_eq_mul, layerQ]
  push_cast
  field_simp

theorem mahlerT_mem_layerField (n : ℕ) : mahlerT ∈ layerField n := by
  rw [← monoRatEval_X_pow_two_pow n]
  exact monoRatEval_mem_layerField n _

theorem two_mem_layerField (n : ℕ) : (2 : HahnSeries ℚ (RatFunc ℂ)) ∈ layerField n := by
  rw [show (2 : HahnSeries ℚ (RatFunc ℂ)) = 1 + 1 from by norm_num]
  exact Subfield.add_mem _ (Subfield.one_mem _) (Subfield.one_mem _)

/-- The additive increment of the normalized velocity under `σ`: `−t²·(2ℓ)⁻¹`. -/
def mahlerShift : HahnSeries ℚ (RatFunc ℂ) :=
  -(mahlerT * mahlerT * (2 * mahlerEll)⁻¹)

theorem two_mul_mahlerEll_ne_zero : (2 * mahlerEll : HahnSeries ℚ (RatFunc ℂ)) ≠ 0 :=
  mul_ne_zero hahn_two_ne_zero mahlerEll_ne_zero

theorem mahlerShift_mem_layerField (n : ℕ) : mahlerShift ∈ layerField n :=
  Subfield.neg_mem _ (Subfield.mul_mem _
    (Subfield.mul_mem _ (mahlerT_mem_layerField n) (mahlerT_mem_layerField n))
    (Subfield.inv_mem _
      (Subfield.mul_mem _ (two_mem_layerField n) (mahlerEll_mem_layerField n))))

theorem mahlerDeriv_two_mul_mahlerEll :
    mahlerDeriv (2 * mahlerEll : HahnSeries ℚ (RatFunc ℂ)) = 0 := by
  rw [mahlerDeriv_mul, mahlerDeriv_two, mahlerDeriv_mahlerEll, mul_zero, zero_mul, add_zero]

theorem mahlerDeriv_mahlerT_sq :
    mahlerDeriv (mahlerT * mahlerT) = 2 * mahlerEll * (mahlerT * mahlerT) := by
  rw [mahlerDeriv_mul, mahlerDeriv_mahlerT]
  ring

/-- The jets of the shift element: one derivation removes the eigenvariable denominator,
each further derivation multiplies by `2ℓ`. -/
theorem mahlerDeriv_iterate_shift_succ (n : ℕ) :
    mahlerDeriv^[n + 1] mahlerShift =
      -((2 : HahnSeries ℚ (RatFunc ℂ)) ^ n * mahlerEll ^ n * (mahlerT * mahlerT)) := by
  induction n with
  | zero =>
    rw [Function.iterate_one, mahlerShift, mahlerDeriv_neg, mahlerDeriv_mul,
      mahlerDeriv_inv_eq_zero mahlerDeriv_two_mul_mahlerEll, mul_zero, add_zero,
      mahlerDeriv_mahlerT_sq, pow_zero, pow_zero]
    have h2l : (2 * mahlerEll) * (2 * mahlerEll)⁻¹ = (1 : HahnSeries ℚ (RatFunc ℂ)) :=
      mul_inv_cancel₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) two_mul_mahlerEll_ne_zero
    have hred : 2 * mahlerEll * (mahlerT * mahlerT) * (2 * mahlerEll)⁻¹ =
        mahlerT * mahlerT := by
      calc 2 * mahlerEll * (mahlerT * mahlerT) * (2 * mahlerEll)⁻¹
          = (mahlerT * mahlerT) * ((2 * mahlerEll) * (2 * mahlerEll)⁻¹) := by ring
        _ = mahlerT * mahlerT := by rw [h2l, mul_one]
    rw [hred, one_mul, one_mul]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, mahlerDeriv_neg]
    have hconst : mahlerDeriv ((2 : HahnSeries ℚ (RatFunc ℂ)) ^ n * mahlerEll ^ n) = 0 := by
      rw [mahlerDeriv_mul, mahlerDeriv_pow_eq_zero mahlerDeriv_two n,
        mahlerDeriv_pow_eq_zero mahlerDeriv_mahlerEll n, zero_mul, mul_zero, add_zero]
    rw [mahlerDeriv_mul, hconst, zero_mul, zero_add, mahlerDeriv_mahlerT_sq, pow_succ,
      pow_succ]
    ring


/-! ## The layer embeddings are injective -/

theorem layerPolyEval_injective (q₀ : ℚ) (hq₀ : 0 < q₀) :
    Function.Injective (layerPolyEval q₀ hq₀) := by
  intro a b hab
  by_contra hne
  exact layerPolyEval_ne_zero hq₀ (sub_ne_zero.mpr hne) (by rw [map_sub, hab, sub_self])

theorem layerEmbed_ne_zero (q₀ : ℚ) (hq₀ : 0 < q₀) {f : RatFunc MahlerBase}
    (hf : f ≠ 0) : layerEmbed q₀ hq₀ f ≠ 0 := by
  intro h0
  have hone : layerEmbed q₀ hq₀ (f * f⁻¹) = 1 := by
    rw [mul_inv_cancel₀ (G₀ := RatFunc MahlerBase) hf, map_one]
  rw [map_mul, h0, zero_mul] at hone
  exact zero_ne_one hone

theorem layerEmbed_injective (q₀ : ℚ) (hq₀ : 0 < q₀) :
    Function.Injective (layerEmbed q₀ hq₀) := by
  intro a b hab
  by_contra hne
  exact layerEmbed_ne_zero q₀ hq₀ (sub_ne_zero.mpr hne) (by rw [map_sub, hab, sub_self])

/-! ## The constant field inside the tower -/

/-- The complex constants inside the carrier. -/
def hahnConstHom : ℂ →+* HahnSeries ℚ (RatFunc ℂ) :=
  (monoRatEval 1 one_pos).comp (RatFunc.C : ℂ →+* RatFunc ℂ)

theorem hahnConstHom_apply (c : ℂ) :
    hahnConstHom c = HahnSeries.single 0 (algebraMap ℂ (RatFunc ℂ) c) :=
  monoRatEval_ratFuncC 1 one_pos c

theorem hahnConstHom_mem_layerField (n : ℕ) (c : ℂ) : hahnConstHom c ∈ layerField n := by
  rw [hahnConstHom_apply, ← monoRatEval_ratFuncC (layerQ n) (layerQ_pos n)]
  exact monoRatEval_mem_layerField n _

theorem hahnConstHom_mem_mahlerSat (c : ℂ) : hahnConstHom c ∈ mahlerSat :=
  layerField_le_mahlerSat 0 (hahnConstHom_mem_layerField 0 c)

/-- The complex constants inside the saturated tower. -/
def satConstHom : ℂ →+* ↥mahlerSat where
  toFun c := ⟨hahnConstHom c, hahnConstHom_mem_mahlerSat c⟩
  map_one' := Subtype.ext (map_one hahnConstHom)
  map_mul' a b := Subtype.ext (map_mul hahnConstHom a b)
  map_zero' := Subtype.ext (map_zero hahnConstHom)
  map_add' a b := Subtype.ext (map_add hahnConstHom a b)

theorem satConstHom_injective : Function.Injective satConstHom :=
  fun _ _ h => hahnConstHom.injective (congrArg Subtype.val h)

theorem mahlerSigma_hahnConstHom (c : ℂ) :
    mahlerSigma (hahnConstHom c) = hahnConstHom c := by
  rw [hahnConstHom_apply, mahlerSigma_single, mul_zero, ellScale_algebraMap_C]

theorem mahlerSigma_fixed_constHom {z : HahnSeries ℚ (RatFunc ℂ)}
    (h : mahlerSigma z = z) : ∃ c : ℂ, hahnConstHom c = z := by
  obtain ⟨c, rfl⟩ := mahlerSigma_fixed_iff.mp h
  exact ⟨c, hahnConstHom_apply c⟩

/-! ## The normalized velocity and its additive shift -/

/-- The normalized velocity `A·ℓ⁻¹`, an additive `σ`-primitive over the tower. -/
def velocityHat : HahnSeries ℚ (RatFunc ℂ) := toMahlerCarrier velocityJet * mahlerEll⁻¹

/-- The shift element as an element of the saturated tower. -/
def satShift : ↥mahlerSat :=
  ⟨mahlerShift, layerField_le_mahlerSat 0 (mahlerShift_mem_layerField 0)⟩

theorem mahlerSigma_velocityHat_shift :
    mahlerSigma velocityHat =
      velocityHat + algebraMap ↥mahlerSat (HahnSeries ℚ (RatFunc ℂ)) satShift := by
  show mahlerSigma velocityHat = velocityHat + mahlerShift
  rw [velocityHat, mahlerSigma_velocityHat, mahlerShift, sub_eq_add_neg]

/-! ## The jet combination as a layer telescoper right side -/

/-- The uniform closed form of the shift jets: every jet is a constant multiple of
`t²·ℓ^{j}·ℓ⁻¹`. -/
theorem mahlerDeriv_iterate_shift (j : ℕ) :
    mahlerDeriv^[j] mahlerShift =
      -((2 : HahnSeries ℚ (RatFunc ℂ)) ^ j * (2 : HahnSeries ℚ (RatFunc ℂ))⁻¹ *
        mahlerEll ^ j * mahlerEll⁻¹ * (mahlerT * mahlerT)) := by
  cases j with
  | zero =>
    rw [Function.iterate_zero_apply, mahlerShift, pow_zero, pow_zero]
    have hinv : ((2 : HahnSeries ℚ (RatFunc ℂ)) * mahlerEll)⁻¹ =
        (2 : HahnSeries ℚ (RatFunc ℂ))⁻¹ * mahlerEll⁻¹ :=
      mul_inv (α := HahnSeries ℚ (RatFunc ℂ)) 2 mahlerEll
    rw [hinv]
    ring
  | succ n =>
    rw [mahlerDeriv_iterate_shift_succ n]
    have h2 : (2 : HahnSeries ℚ (RatFunc ℂ)) ^ (n + 1) *
        (2 : HahnSeries ℚ (RatFunc ℂ))⁻¹ = 2 ^ n := by
      rw [pow_succ, mul_assoc,
        mul_inv_cancel₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) hahn_two_ne_zero, mul_one]
    have hl : mahlerEll ^ (n + 1) * mahlerEll⁻¹ = mahlerEll ^ n := by
      rw [pow_succ, mul_assoc,
        mul_inv_cancel₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) mahlerEll_ne_zero, mul_one]
    have hprod : (2 : HahnSeries ℚ (RatFunc ℂ)) ^ (n + 1) *
        (2 : HahnSeries ℚ (RatFunc ℂ))⁻¹ * mahlerEll ^ (n + 1) * mahlerEll⁻¹ *
        (mahlerT * mahlerT) =
        2 ^ n * mahlerEll ^ n * (mahlerT * mahlerT) := by
      calc (2 : HahnSeries ℚ (RatFunc ℂ)) ^ (n + 1) * (2 : HahnSeries ℚ (RatFunc ℂ))⁻¹ *
          mahlerEll ^ (n + 1) * mahlerEll⁻¹ * (mahlerT * mahlerT)
          = ((2 : HahnSeries ℚ (RatFunc ℂ)) ^ (n + 1) * (2 : HahnSeries ℚ (RatFunc ℂ))⁻¹) *
            (mahlerEll ^ (n + 1) * mahlerEll⁻¹) * (mahlerT * mahlerT) := by ring
        _ = 2 ^ n * mahlerEll ^ n * (mahlerT * mahlerT) := by rw [h2, hl]
    rw [hprod]

/-- The base monomial squared, read on layer `m`. -/
theorem layerEmbed_TT (m : ℕ) :
    layerEmbed (layerQ m) (layerQ_pos m)
      (RatFunc.C ((RatFunc.X : RatFunc ℂ) ^ (2 * 2 ^ m))) = mahlerT * mahlerT := by
  rw [layerEmbed_ratFuncC, show 2 * 2 ^ m = 2 ^ m * 2 from mul_comm 2 (2 ^ m), pow_mul,
    map_pow, monoRatEval_X_pow_two_pow, sq]

set_option maxHeartbeats 1000000 in
/-- One constant-multiple jet as a base-layer product: the Hahn-level form. -/
theorem hahnConst_mul_shift_jet' (m : ℕ) (a : ℂ) (j : ℕ) :
    hahnConstHom a * mahlerDeriv^[j] mahlerShift =
      (mahlerT * mahlerT) *
        (layerPolyEval (layerQ m) (layerQ_pos m)
            (Polynomial.monomial j (RatFunc.C (-((2 : ℂ) ^ j * a) / 2))) * mahlerEll⁻¹) := by
  rw [show (Polynomial.monomial j (RatFunc.C (-((2 : ℂ) ^ j * a) / 2)) :
      Polynomial MahlerBase) =
    Polynomial.C (RatFunc.C (-((2 : ℂ) ^ j * a) / 2)) * Polynomial.X ^ j from by
    rw [Polynomial.C_mul_X_pow_eq_monomial]]
  rw [map_mul, map_pow, layerPolyEval_C, layerPolyEval_X]
  rw [show monoRatEval (layerQ m) (layerQ_pos m) (RatFunc.C (-((2 : ℂ) ^ j * a) / 2)) =
    hahnConstHom (-((2 : ℂ) ^ j * a) / 2) from
    (monoRatEval_ratFuncC (layerQ m) (layerQ_pos m) _).trans
      (hahnConstHom_apply _).symm]
  have hconst : hahnConstHom (-((2 : ℂ) ^ j * a) / 2) =
      -(((2 : HahnSeries ℚ (RatFunc ℂ)) ^ j * hahnConstHom a) *
        (2 : HahnSeries ℚ (RatFunc ℂ))⁻¹) := by
    have hdiv2 : hahnConstHom (-((2 : ℂ) ^ j * a) / 2) =
        hahnConstHom (-((2 : ℂ) ^ j * a)) / hahnConstHom 2 :=
      map_div₀ (f := hahnConstHom) (a := -((2 : ℂ) ^ j * a)) (b := 2)
    rw [hdiv2, map_neg, map_mul, map_pow, map_ofNat, div_eq_mul_inv]
    exact neg_mul ((2 : HahnSeries ℚ (RatFunc ℂ)) ^ j * hahnConstHom a)
      ((2 : HahnSeries ℚ (RatFunc ℂ))⁻¹)
  rw [hconst, mahlerDeriv_iterate_shift]
  ring

/-- The eigenvariable numerator polynomial of a constant-coefficient jet combination. -/
def shiftComboPoly (c : (Unit × ℕ) →₀ ℂ) : Polynomial MahlerBase :=
  c.sum fun p a => Polynomial.monomial p.2 (RatFunc.C (-((2 : ℂ) ^ p.2 * a) / 2))

theorem shiftComboPoly_coeff (c : (Unit × ℕ) →₀ ℂ) (j : ℕ) :
    (shiftComboPoly c).coeff j = RatFunc.C (-((2 : ℂ) ^ j * c ((), j)) / 2) := by
  classical
  rw [shiftComboPoly, Finsupp.sum, Polynomial.finsetSum_coeff]
  have hterm : ∀ p ∈ c.support,
      (Polynomial.monomial p.2 (RatFunc.C (-((2 : ℂ) ^ p.2 * c p) / 2))).coeff j =
      if p = ((), j) then RatFunc.C (-((2 : ℂ) ^ j * c ((), j)) / 2) else 0 := by
    intro p _
    rw [Polynomial.coeff_monomial]
    rcases eq_or_ne p ((), j) with rfl | hne
    · rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hne (Prod.ext (Subsingleton.elim _ _) h)), if_neg hne]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' c.support ((), j)]
  by_cases hmem : ((), j) ∈ c.support
  · rw [if_pos hmem]
  · rw [if_neg hmem, Finsupp.notMem_support_iff.mp hmem, mul_zero, neg_zero, zero_div,
      map_zero]

theorem shiftComboPoly_ne_zero {c : (Unit × ℕ) →₀ ℂ} (hc : c ≠ 0) :
    shiftComboPoly c ≠ 0 := by
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (Finsupp.ext h)
  intro h0
  have hco : (shiftComboPoly c).coeff p.2 = 0 := by rw [h0, Polynomial.coeff_zero]
  rw [shiftComboPoly_coeff] at hco
  have hcp : c ((), p.2) ≠ 0 := by
    rw [show (((), p.2) : Unit × ℕ) = p from Prod.ext (Subsingleton.elim _ _) rfl]
    exact hp
  have hγ : (-((2 : ℂ) ^ p.2 * c ((), p.2)) / 2 : ℂ) = 0 :=
    RatFunc.C_injective (by rw [hco, map_zero])
  rw [div_eq_zero_iff, neg_eq_zero, mul_eq_zero] at hγ
  rcases hγ with (h2 | hc0) | h20
  · exact pow_ne_zero p.2 two_ne_zero h2
  · exact hcp hc0
  · exact two_ne_zero h20

/-- A constant-coefficient combination of shift jets is the layer image of the exact
telescoper right side refuted by the two-variable obstruction. -/
theorem shift_combo_layerEmbed (m : ℕ) (c : (Unit × ℕ) →₀ ℂ) :
    (c.sum fun p a => hahnConstHom a * mahlerDeriv^[p.2] mahlerShift) =
      layerEmbed (layerQ m) (layerQ_pos m)
        (RatFunc.C ((RatFunc.X : RatFunc ℂ) ^ (2 * 2 ^ m)) *
          (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (shiftComboPoly c) /
            algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) Polynomial.X)) := by
  classical
  rw [map_mul, layerEmbed_TT, layerEmbed_apply_div, layerPolyEval_X, shiftComboPoly,
    Finsupp.sum, Finsupp.sum,
    map_sum (layerPolyEval (layerQ m) (layerQ_pos m))
      (fun p => Polynomial.monomial p.2 (RatFunc.C (-((2 : ℂ) ^ p.2 * c p) / 2)))
      c.support,
    div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => hahnConst_mul_shift_jet' m (c p) p.2

/-- No nonzero constant-coefficient combination of shift jets telescopes on the saturated
tower: transported through the layer embedding this is exactly the two-variable rational
telescoper obstruction. -/
theorem mahlerSat_no_shift_combination (c : (Unit × ℕ) →₀ ℂ) (hc : c ≠ 0)
    (k : ↥mahlerSat)
    (heq : (mahlerSatTau k - k : ↥mahlerSat).val =
      c.sum fun p a => hahnConstHom a * mahlerDeriv^[p.2] mahlerShift) : False := by
  obtain ⟨m, hm⟩ := mem_mahlerSat_iff.mp k.prop
  obtain ⟨κ, hκ⟩ := mem_layerField_iff.mp hm
  have hL : (mahlerSatTau k - k : ↥mahlerSat).val =
      layerEmbed (layerQ m) (layerQ_pos m) (twoVarMahler κ - κ) := by
    rw [show (mahlerSatTau k - k : ↥mahlerSat).val = mahlerSigma k.val - k.val from rfl]
    rw [← hκ, map_sub, mahlerSigma_layerEmbed]
  rw [hL, shift_combo_layerEmbed m c] at heq
  exact no_twoVarMahler_telescoper (N := 2 ^ m) (Nat.two_pow_pos m)
    (shiftComboPoly_ne_zero hc) (fun i => ⟨_, shiftComboPoly_coeff c i⟩) κ
    (layerEmbed_injective (layerQ m) (layerQ_pos m) heq)

/-- The native coefficientwise `ℂ`-action on the carrier is multiplication by the
corresponding constant. -/
theorem hahn_smul_eq (c : ℂ) (x : HahnSeries ℚ (RatFunc ℂ)) :
    c • x = hahnConstHom c * x := by
  rw [hahnConstHom_apply]
  ext q
  rw [HahnSeries.coeff_single_zero_mul]
  rw [show (c • x).coeff q = c • x.coeff q from rfl]
  rw [Algebra.smul_def]

theorem zero_smul_jet (p : Unit × ℕ) :
    (0 : ↥mahlerSat) • differentialJet p.2 satShift = 0 :=
  zero_smul _ _

/-! ## The Ostrowski application -/

/-- **The normalized velocity is differentially transcendental over the saturated dyadic
tower.**  The graded Mahler automorphism family (a single automorphism) has constant fixed
field, commutes exactly with the untwisted derivation, and shifts the normalized velocity
by a tower element whose jets admit no rational telescoper on any layer. -/
theorem velocityHat_differentialIndependent :
    DifferentialIndependent ↥mahlerSat (fun _ : Unit => velocityHat) := by
  letI : Algebra ℂ (HahnSeries ℚ (RatFunc ℂ)) :=
    { smul := fun c x => c • x
      algebraMap := hahnConstHom
      commutes' := fun _ _ => mul_comm _ _
      smul_def' := hahn_smul_eq }
  letI : Algebra ℂ ↥mahlerSat := satConstHom.toAlgebra
  haveI : IsScalarTower ℂ ↥mahlerSat (HahnSeries ℚ (RatFunc ℂ)) :=
    ⟨fun c k l => by
      rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul,
        Algebra.smul_def c k, hahn_smul_eq]
      rw [show ((algebraMap ℂ ↥mahlerSat c * k : ↥mahlerSat) :
          HahnSeries ℚ (RatFunc ℂ)) =
        hahnConstHom c * (k : HahnSeries ℚ (RatFunc ℂ)) from rfl, mul_assoc]⟩
  haveI : CharZero ↥mahlerSat := charZero_of_injective_algebraMap satConstHom_injective
  refine automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    (I := Unit) (C := ℂ)
    (fun _ => mahlerSatTau) (fun _ => mahlerSigma)
    (fun _ _ => rfl)
    (fun _ x => by rw [carrier_deriv_eq, carrier_deriv_eq, mahlerSigma_mahlerDeriv])
    (fun _ c => mahlerSigma_hahnConstHom c)
    (fun z hz => mahlerSigma_fixed_constHom (hz ()))
    (fun _ => velocityHat) (fun _ _ => satShift)
    (fun _ _ => mahlerSigma_velocityHat_shift)
    ?_
  intro c hc k
  refine ⟨(), fun heq => ?_⟩
  apply mahlerSat_no_shift_combination c hc k
  have hval := congrArg Subtype.val heq
  rw [hval, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index zero_smul_jet]
  show (Subfield.subtype mahlerSat)
      (c.sum fun p a => algebraMap ℂ ↥mahlerSat a • differentialJet p.2 satShift) = _
  rw [map_finsuppSum (Subfield.subtype mahlerSat)]
  apply Finsupp.sum_congr
  intro p _
  show (algebraMap ℂ ↥mahlerSat (c p) • differentialJet p.2 satShift : ↥mahlerSat).val = _
  rw [show (algebraMap ℂ ↥mahlerSat (c p) • differentialJet p.2 satShift :
      ↥mahlerSat).val = hahnConstHom (c p) * (differentialJet p.2 satShift).val from rfl]
  rw [differentialJet_mahlerSat_val]
  rfl

/-! ## Transport: hypertranscendence of the velocity jet over the base field -/

theorem layerQ_zero : layerQ 0 = 1 := by
  rw [layerQ, pow_zero, inv_one]

theorem monoRatEval_congr {q₁ q₂ : ℚ} (h : q₁ = q₂) (h₁ : 0 < q₁) (f : RatFunc ℂ) :
    monoRatEval q₁ h₁ f = monoRatEval q₂ (h ▸ h₁) f := by
  subst h
  rfl

theorem monoRatEval_one_mem_mahlerSat (f : RatFunc ℂ) :
    monoRatEval 1 one_pos f ∈ mahlerSat := by
  have h := monoRatEval_mem_layerField 0 f
  rw [monoRatEval_congr layerQ_zero (layerQ_pos 0) f] at h
  exact layerField_le_mahlerSat 0 h

/-- The base rational-function field `ℂ(t)` inside the saturated tower. -/
def satBaseHom : RatFunc ℂ →+* ↥mahlerSat where
  toFun f := ⟨monoRatEval 1 one_pos f, monoRatEval_one_mem_mahlerSat f⟩
  map_one' := Subtype.ext (map_one (monoRatEval 1 one_pos))
  map_mul' a b := Subtype.ext (map_mul (monoRatEval 1 one_pos) a b)
  map_zero' := Subtype.ext (map_zero (monoRatEval 1 one_pos))
  map_add' a b := Subtype.ext (map_add (monoRatEval 1 one_pos) a b)

theorem satBaseHom_injective : Function.Injective satBaseHom :=
  fun _ _ h => (monoRatEval 1 one_pos).injective (congrArg Subtype.val h)

theorem algebraMap_comp_satBaseHom :
    (algebraMap ↥mahlerSat (HahnSeries ℚ (RatFunc ℂ))).comp satBaseHom =
      monoRatEval 1 one_pos :=
  RingHom.ext fun _ => rfl

/-- The eigenvariable as an element of the saturated tower. -/
def satEll : ↥mahlerSat :=
  ⟨mahlerEll, layerField_le_mahlerSat 0 (mahlerEll_mem_layerField 0)⟩

theorem satEll_ne_zero : satEll ≠ 0 :=
  fun h => mahlerEll_ne_zero (congrArg Subtype.val h)

/-- The jets of the normalized velocity untwist to eigenvariable powers of the Euler jets
of the velocity itself. -/
theorem mahlerDeriv_iterate_velocityHat (n : ℕ) :
    mahlerDeriv^[n] velocityHat =
      mahlerEll ^ ((n : ℤ) - 1) * eulerDeriv^[n] (toMahlerCarrier velocityJet) := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply, velocityHat]
    rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by norm_num, zpow_neg_one]
    exact mul_comm _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, mahlerDeriv_mul,
      mahlerDeriv_zpow_eq_zero mahlerDeriv_mahlerEll, zero_mul, zero_add]
    rw [show mahlerDeriv (eulerDeriv^[n] (toMahlerCarrier velocityJet)) =
      mahlerEll * eulerDeriv^[n + 1] (toMahlerCarrier velocityJet) from by
      rw [Function.iterate_succ_apply']
      rfl]
    rw [show ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℤ) - 1) + 1 from by push_cast; ring]
    rw [zpow_add_one₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) mahlerEll_ne_zero]
    ring

/-- Scaling each jet variable by an eigenvariable power, as an algebra substitution. -/
def jetScale (z : Unit × ℕ → ℤ) :
    MvPolynomial (Unit × ℕ) ↥mahlerSat →ₐ[↥mahlerSat] MvPolynomial (Unit × ℕ) ↥mahlerSat :=
  MvPolynomial.aeval (fun p => MvPolynomial.C (satEll ^ z p) * MvPolynomial.X p)

theorem jetScale_injective (z : Unit × ℕ → ℤ) : Function.Injective (jetScale z) := by
  have hcomp : (jetScale (fun p => -(z p))).comp (jetScale z) =
      AlgHom.id ↥mahlerSat (MvPolynomial (Unit × ℕ) ↥mahlerSat) := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.id_apply, jetScale, jetScale, MvPolynomial.aeval_X,
      map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    rw [show algebraMap ↥mahlerSat (MvPolynomial (Unit × ℕ) ↥mahlerSat) (satEll ^ z p) =
      MvPolynomial.C (satEll ^ z p) from rfl]
    rw [← mul_assoc, ← map_mul, ← zpow_add₀ satEll_ne_zero]
    rw [show z p + -(z p) = 0 from by ring, zpow_zero, map_one, one_mul]
  intro a b hab
  have hid := congrArg (jetScale (fun p => -(z p))) hab
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp, AlgHom.id_apply,
    AlgHom.id_apply] at hid
  exact hid

/-- **Hypertranscendence of the Böttcher velocity jet over the base field, in the graded
carrier.**  No nonzero polynomial with `ℂ(t)`-coefficients vanishes on the Euler jets of
the lacunary velocity `A`: the normalized velocity is an additive Mahler primitive over
the saturated dyadic tower, its jets rescale to the Euler jets by eigenvariable powers,
and the tower-level differential independence descends. -/
theorem velocity_theta_hypertranscendental (m : ℕ)
    (P : MvPolynomial (Fin (m + 1)) (RatFunc ℂ)) (hP : P ≠ 0) :
    MvPolynomial.eval₂ (monoRatEval 1 one_pos)
      (fun i : Fin (m + 1) => eulerDeriv^[(i : ℕ)] (toMahlerCarrier velocityJet)) P ≠ 0 := by
  intro heval
  have hAI : AlgebraicIndependent ↥mahlerSat
      (fun p : Unit × ℕ => differentialJet p.2 velocityHat) :=
    velocityHat_differentialIndependent
  have hjet : ∀ p : Unit × ℕ,
      differentialJet p.2 velocityHat = mahlerDeriv^[p.2] velocityHat := fun _ => rfl
  set P₁ : MvPolynomial (Fin (m + 1)) ↥mahlerSat := MvPolynomial.map satBaseHom P with hP₁
  set P₂ : MvPolynomial (Unit × ℕ) ↥mahlerSat :=
    MvPolynomial.rename (fun i : Fin (m + 1) => (((), (i : ℕ)) : Unit × ℕ)) P₁ with hP₂
  set P₃ : MvPolynomial (Unit × ℕ) ↥mahlerSat :=
    jetScale (fun p => 1 - (p.2 : ℤ)) P₂ with hP₃
  have hsub : ∀ p : Unit × ℕ,
      MvPolynomial.aeval (fun p : Unit × ℕ => differentialJet p.2 velocityHat)
        (MvPolynomial.C (satEll ^ (1 - (p.2 : ℤ))) * MvPolynomial.X p) =
      eulerDeriv^[p.2] (toMahlerCarrier velocityJet) := by
    intro p
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hjet,
      mahlerDeriv_iterate_velocityHat]
    rw [show algebraMap ↥mahlerSat (HahnSeries ℚ (RatFunc ℂ))
        (satEll ^ (1 - (p.2 : ℤ))) = mahlerEll ^ (1 - (p.2 : ℤ)) from
      map_zpow₀ (algebraMap ↥mahlerSat (HahnSeries ℚ (RatFunc ℂ))) satEll _]
    rw [← mul_assoc, ← zpow_add₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) mahlerEll_ne_zero]
    rw [show (1 - (p.2 : ℤ)) + ((p.2 : ℤ) - 1) = 0 from by ring, zpow_zero, one_mul]
  have hzero : MvPolynomial.aeval
      (fun p : Unit × ℕ => differentialJet p.2 velocityHat) P₃ = 0 := by
    have hcompose := DFunLike.congr_fun
      (MvPolynomial.comp_aeval
        (fun p : Unit × ℕ => MvPolynomial.C (satEll ^ (1 - (p.2 : ℤ))) * MvPolynomial.X p)
        (MvPolynomial.aeval (fun p : Unit × ℕ => differentialJet p.2 velocityHat))) P₂
    rw [AlgHom.comp_apply] at hcompose
    rw [hP₃, jetScale, hcompose]
    rw [show (fun p : Unit × ℕ => MvPolynomial.aeval
        (fun q : Unit × ℕ => differentialJet q.2 velocityHat)
        (MvPolynomial.C (satEll ^ (1 - (p.2 : ℤ))) * MvPolynomial.X p)) =
      (fun p : Unit × ℕ => eulerDeriv^[p.2] (toMahlerCarrier velocityJet)) from
      funext hsub]
    rw [hP₂, MvPolynomial.aeval_rename, hP₁]
    rw [show ((fun p : Unit × ℕ => eulerDeriv^[p.2] (toMahlerCarrier velocityJet)) ∘
        (fun i : Fin (m + 1) => (((), (i : ℕ)) : Unit × ℕ))) =
      (fun i : Fin (m + 1) => eulerDeriv^[(i : ℕ)] (toMahlerCarrier velocityJet)) from
      rfl]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, algebraMap_comp_satBaseHom]
    exact heval
  have hP₃0 : P₃ = 0 := hAI (by rw [hzero, map_zero])
  have hP₂0 : P₂ = 0 := jetScale_injective _ (by rw [← hP₃, hP₃0, map_zero])
  have hP₁0 : P₁ = 0 := MvPolynomial.rename_injective _
    (fun a b hab => Fin.val_injective (congrArg Prod.snd hab))
    (by rw [← hP₂, hP₂0, map_zero])
  exact hP (MvPolynomial.map_injective satBaseHom satBaseHom_injective
    (by rw [← hP₁, hP₁0, map_zero]))
end

end GaloisForLFunctions
