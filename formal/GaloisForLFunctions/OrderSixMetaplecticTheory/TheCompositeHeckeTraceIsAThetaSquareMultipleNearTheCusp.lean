import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeHeckeTraceIsFiveBlocks

/-!
# The composite Hecke trace near the cusp

For `m = pq` and the source theta `θ_s = cv^{2/3} + O(v^{−3})`, the composite trace exceeds
`N(m)(2 + 2(p/q)₃)θ_s²` by `O(v^{−7/3})` on the standard strip (`PrimaryPair.norm_remainder_strip`):

* every Hecke point has height `ρv`, `v/ρ`, `(ρ_p/ρ_q)v` or `(ρ_q/ρ_p)v` (`ρ = |m|`), between `v/ρ` and `ρv`;
* the dilate pairs `(ρv, v/ρ)` and `((ρ_p/ρ_q)v, (ρ_q/ρ_p)v)` have height product `v²`, so their constant parts are
  `c²v^{4/3}`: the `N(m)` pairs of each of the two blocks `Θ^{hh}ΣΘ^{ll}` and `(ΣΘ^{hl})(ΣΘ^{lh})` give
  `2N(m)c²v^{4/3}` and `2(p/q)₃N(m)c²v^{4/3}`;
* in the twisted blocks the constant parts do not depend on the character variable and the characters
  `(3y/q)₃`, `(3y/p)₃`, `(3y/m)₃` have mean zero.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPair

variable (R : PrimaryPair)

/-- `N(m)(2 + 2(p/q)₃)`: the number of theta squares in the composite trace. -/
def growth : ℂ :=
  (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ) * (2 + 2 * ringComplex (symbol R.P.p R.Q.p))

/-- The composite trace of the source theta. -/
def sourceTrace (w : HyperbolicSpace) : ℂ := R.heckeTrace sourceTheta w

/-- `G'_m = Tr_mθ_s − N(m)(2 + 2(p/q)₃)θ_s²`. -/
def remainder (w : HyperbolicSpace) : ℂ := R.sourceTrace w - R.growth * sourceTheta w ^ 2

/-! ### The Hecke points of a point of the upper half-space -/

theorem hh_point (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.hh sourceTheta (upperPoint z v hv) = sourceTheta (upperPoint (ringComplex R.P.p * (ringComplex R.Q.p * z))
      (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v)) (mul_pos R.P.norm_pos (mul_pos R.Q.norm_pos hv))) := by
  rw [hh, dilation, mul_smul, R.Q.dilation_upperPoint, R.P.dilation_upperPoint]

theorem ll_point (t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.ll sourceTheta t (upperPoint z v hv) = sourceTheta (upperPoint
      ((z + 3 * ringComplex t) / ringComplex R.Q.p / ringComplex R.P.p)
      (v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) (div_pos (div_pos hv R.Q.norm_pos) R.P.norm_pos)) := by
  rw [ll, contraction, transThree_smul_upperPoint, mul_smul, R.Q.contraction_upperPoint, R.P.contraction_upperPoint]

theorem hl_point (t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.hl sourceTheta t (upperPoint z v hv) = sourceTheta (upperPoint
      ((ringComplex R.P.p * z + 3 * ringComplex t) / ringComplex R.Q.p)
      (‖ringComplex R.P.p‖ * v / ‖ringComplex R.Q.p‖) (div_pos (mul_pos R.P.norm_pos hv) R.Q.norm_pos)) := by
  rw [hl, R.P.dilation_upperPoint, transThree_smul_upperPoint, R.Q.contraction_upperPoint]

theorem lh_point (t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.lh sourceTheta t (upperPoint z v hv) = sourceTheta (upperPoint
      ((ringComplex R.Q.p * z + 3 * ringComplex t) / ringComplex R.P.p)
      (‖ringComplex R.Q.p‖ * v / ‖ringComplex R.P.p‖) (div_pos (mul_pos R.Q.norm_pos hv) R.P.norm_pos)) := by
  rw [lh, R.Q.dilation_upperPoint, transThree_smul_upperPoint, R.P.contraction_upperPoint]

/-! ### Mean-zero characters -/

theorem sum_ul_symbol : ∑ y : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.yUL y) R.Q.p) = 0 := by
  have h := R.Q.sum_symbol_eq_zero
  have hp := R.pInv_ne_zero
  let e : {y : R.Q.Res // y ≠ 0} ≃ {y : R.Q.Res // y ≠ 0} :=
    ⟨fun y => ⟨y.1 * R.pInv, mul_ne_zero y.2 hp⟩, fun y => ⟨y.1 * R.pInv⁻¹, mul_ne_zero y.2 (inv_ne_zero hp)⟩,
      fun y => by ext; simp [hp], fun y => by ext; simp [hp]⟩
  rw [← h, ← Equiv.sum_comp e]
  rfl

theorem sum_lu_symbol : ∑ y : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y) R.P.p) = 0 := by
  have h := R.P.sum_symbol_eq_zero
  have hq := R.qInv_ne_zero
  let e : {y : R.P.Res // y ≠ 0} ≃ {y : R.P.Res // y ≠ 0} :=
    ⟨fun y => ⟨y.1 * R.qInv, mul_ne_zero y.2 hq⟩, fun y => ⟨y.1 * R.qInv⁻¹, mul_ne_zero y.2 (inv_ne_zero hq)⟩,
      fun y => by ext; simp [hq], fun y => by ext; simp [hq]⟩
  rw [← h, ← Equiv.sum_comp e]
  rfl

theorem sum_ll_symbol :
    ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
      ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) = 0 := by
  have e : ∀ (y₁ : {y : R.P.Res // y ≠ 0}) (y₂ : {y : R.Q.Res // y ≠ 0}),
      ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) =
        ringComplex (symbol (3 * R.P.lift y₁.1) R.P.p) * ringComplex (symbol (3 * R.Q.lift y₂.1) R.Q.p) := by
    intro y₁ y₂
    rw [symbol_mul_denominator, map_mul,
      symbol_congr (show R.P.p ∣ 3 * R.crt y₁.1 y₂.1 - 3 * R.P.lift y₁.1 by
        rw [← R.P.res_eq_zero_iff]; simp),
      symbol_congr (show R.Q.p ∣ 3 * R.crt y₁.1 y₂.1 - 3 * R.Q.lift y₂.1 by
        rw [← R.Q.res_eq_zero_iff]; simp)]
  simp_rw [e, ← Finset.mul_sum, R.Q.sum_symbol_eq_zero, mul_zero, Finset.sum_const_zero]

theorem norm_symbol_le' (x n : O) (hn : lambda ^ 2 ∣ n - 1) : ‖ringComplex (symbol x n)‖ ≤ 1 :=
  norm_symbol_le x n hn

theorem primary_m : lambda ^ 2 ∣ R.P.p * R.Q.p - 1 := primary_mul R.P.primary R.Q.primary

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
