import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeHeckeTraceIsFiveBlocks
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsTwiceNormThetaSquaresUpToABoundedRemainder
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheLongColumnsAreLayersOfTwistedThetaSquares

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
  calc ∑ y : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.yUL y) R.Q.p)
      = ∑ y : {y : R.Q.Res // y ≠ 0}, (fun y : {y : R.Q.Res // y ≠ 0} =>
          ringComplex (symbol (3 * R.Q.lift y.1) R.Q.p)) (e y) := rfl
    _ = 0 := by rw [Equiv.sum_comp e (fun y : {y : R.Q.Res // y ≠ 0} => ringComplex (symbol (3 * R.Q.lift y.1) R.Q.p)), h]

theorem sum_lu_symbol : ∑ y : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y) R.P.p) = 0 := by
  have h := R.P.sum_symbol_eq_zero
  have hq := R.qInv_ne_zero
  let e : {y : R.P.Res // y ≠ 0} ≃ {y : R.P.Res // y ≠ 0} :=
    ⟨fun y => ⟨y.1 * R.qInv, mul_ne_zero y.2 hq⟩, fun y => ⟨y.1 * R.qInv⁻¹, mul_ne_zero y.2 (inv_ne_zero hq)⟩,
      fun y => by ext; simp [hq], fun y => by ext; simp [hq]⟩
  calc ∑ y : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y) R.P.p)
      = ∑ y : {y : R.P.Res // y ≠ 0}, (fun y : {y : R.P.Res // y ≠ 0} =>
          ringComplex (symbol (3 * R.P.lift y.1) R.P.p)) (e y) := rfl
    _ = 0 := by rw [Equiv.sum_comp e (fun y : {y : R.P.Res // y ≠ 0} => ringComplex (symbol (3 * R.P.lift y.1) R.P.p)), h]

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

/-! ### The strip -/

theorem norm_mul_sub_le_two {X Y A B U V : ℂ} {E : ℝ} (h1 : ‖X * Y - A * B‖ ≤ E) (h2 : ‖U * V - A * B‖ ≤ E) :
    ‖X * Y - U * V‖ ≤ 2 * E := by
  have := norm_sub_le (X * Y - A * B) (U * V - A * B)
  rw [show X * Y - A * B - (U * V - A * B) = X * Y - U * V by ring] at this
  linarith

theorem norm_sum_le_card {ι : Type*} [Fintype ι] (f : ι → ℂ) {E : ℝ} (h : ∀ i, ‖f i‖ ≤ E) :
    ‖∑ i, f i‖ ≤ (Fintype.card ι : ℝ) * E := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖f i‖ ≤ ∑ _i : ι, E := Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card ι : ℝ) * E := by simp

theorem card_units_le (F : Type) [Field F] [Fintype F] : (Fintype.card {y : F // y ≠ 0} : ℝ) ≤ Fintype.card F := by
  exact_mod_cast Fintype.card_subtype_le _

/-- A twisted sum whose character has mean zero is a sum of approximation errors. -/
theorem sum_char_sub {ι : Type*} [Fintype ι] (χ f : ι → ℂ) (hχ : ∑ i, χ i = 0) (A : ℂ) :
    ∑ i, χ i * f i = ∑ i, χ i * (f i - A) := by
  rw [show (∑ i, χ i * (f i - A)) = (∑ i, χ i * f i) - (∑ i, χ i) * A by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring, hχ, zero_mul,
    sub_zero]

section Blocks

variable (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) {M D : ℝ}

theorem norm_block_dil_le {A₁ A₂ A0 : ℂ} (h0 : ‖Θ w - A0‖ ≤ D) (hm0 : ‖A0‖ ≤ M) (h1 : ‖R.hh Θ w - A₁‖ ≤ D)
    (h2 : ∀ t, ‖R.ll Θ t w - A₂‖ ≤ D) (hm1 : ‖A₁‖ ≤ M) (hm2 : ‖A₂‖ ≤ M) (hA : A₁ * A₂ = A0 * A0) :
    ‖R.hh Θ w * R.llSum Θ w - (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ) * (Θ w * Θ w)‖ ≤
      (Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) * (2 * (2 * M * D + D ^ 2))) := by
  have e00 : ‖Θ w * Θ w - A0 * A0‖ ≤ 2 * M * D + D ^ 2 := norm_mul_sub_mul_le hm0 hm0 h0 h0
  have hB : R.hh Θ w * R.llSum Θ w - (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ) * (Θ w * Θ w) =
      ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res, (R.hh Θ w * R.ll Θ (R.crt x₁ x₂) w - Θ w * Θ w) := by
    simp only [llSum, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hB]
  exact norm_sum_le_card _ fun x₁ => norm_sum_le_card _ fun x₂ =>
    norm_mul_sub_le_two (norm_mul_sub_mul_le hm1 hm2 h1 (h2 _)) (by rw [hA]; exact e00)

theorem norm_block_ratio_le {A₁ A₂ A0 : ℂ} (h0 : ‖Θ w - A0‖ ≤ D) (hm0 : ‖A0‖ ≤ M)
    (h1 : ∀ t, ‖R.hl Θ t w - A₁‖ ≤ D) (h2 : ∀ t, ‖R.lh Θ t w - A₂‖ ≤ D) (hm1 : ‖A₁‖ ≤ M) (hm2 : ‖A₂‖ ≤ M)
    (hA : A₁ * A₂ = A0 * A0) :
    ‖R.hlSum Θ w * R.lhSum Θ w - (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ) * (Θ w * Θ w)‖ ≤
      (Fintype.card R.Q.Res : ℝ) * ((Fintype.card R.P.Res : ℝ) * (2 * (2 * M * D + D ^ 2))) := by
  have e00 : ‖Θ w * Θ w - A0 * A0‖ ≤ 2 * M * D + D ^ 2 := norm_mul_sub_mul_le hm0 hm0 h0 h0
  have hB : R.hlSum Θ w * R.lhSum Θ w - (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ) * (Θ w * Θ w) =
      ∑ u : R.Q.Res, ∑ u' : R.P.Res, (R.hl Θ (R.Q.lift u) w * R.lh Θ (R.P.lift u') w - Θ w * Θ w) := by
    rw [hlSum, lhSum, Finset.sum_mul_sum]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hB]
  exact norm_sum_le_card _ fun u => norm_sum_le_card _ fun u' =>
    norm_mul_sub_le_two (norm_mul_sub_mul_le hm1 hm2 (h1 _) (h2 _)) (by rw [hA]; exact e00)

theorem norm_ulBlock_le {A₁ A₂ : ℂ} (h1 : ∀ t, ‖R.hl Θ t w - A₁‖ ≤ D) (h2 : ∀ t, ‖R.ll Θ t w - A₂‖ ≤ D)
    (hm1 : ‖A₁‖ ≤ M) (hm2 : ‖A₂‖ ≤ M) (hE : 0 ≤ 2 * M * D + D ^ 2) :
    ‖R.ulBlock Θ w‖ ≤ (Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) *
      ((Fintype.card R.Q.Res : ℝ) * (2 * M * D + D ^ 2))) := by
  have key : ∀ x₁ x₂, ‖∑ y₂ : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.yUL y₂) R.Q.p) *
      R.hl Θ (R.P.p * R.crt x₁ x₂ - R.Q.lowBeta (R.yUL y₂)) w * R.ll Θ (R.crt x₁ x₂) w‖ ≤
      (Fintype.card R.Q.Res : ℝ) * (2 * M * D + D ^ 2) := by
    intro x₁ x₂
    rw [Finset.sum_congr rfl fun y _ => mul_assoc (ringComplex (symbol (3 * R.yUL y) R.Q.p)) _ _,
      sum_char_sub _ _ R.sum_ul_symbol (A₁ * A₂)]
    refine (norm_sum_le_card _ fun y => ?_).trans (mul_le_mul_of_nonneg_right (card_units_le _) hE)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_symbol_le _ _ R.Q.primary)).trans
      (norm_mul_sub_mul_le hm1 hm2 (h1 _) (h2 _))
  rw [ulBlock]
  exact norm_sum_le_card _ fun x₁ => norm_sum_le_card _ fun x₂ => key x₁ x₂

theorem norm_luBlock_le {A₁ A₂ : ℂ} (h1 : ∀ t, ‖R.lh Θ t w - A₁‖ ≤ D) (h2 : ∀ t, ‖R.ll Θ t w - A₂‖ ≤ D)
    (hm1 : ‖A₁‖ ≤ M) (hm2 : ‖A₂‖ ≤ M) (hE : 0 ≤ 2 * M * D + D ^ 2) :
    ‖R.luBlock Θ w‖ ≤ (Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) *
      ((Fintype.card R.P.Res : ℝ) * (2 * M * D + D ^ 2))) := by
  have key : ∀ x₁ x₂, ‖∑ y₁ : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y₁) R.P.p) *
      R.lh Θ (R.Q.p * R.crt x₁ x₂ - R.P.lowBeta (R.yLU y₁)) w * R.ll Θ (R.crt x₁ x₂) w‖ ≤
      (Fintype.card R.P.Res : ℝ) * (2 * M * D + D ^ 2) := by
    intro x₁ x₂
    rw [Finset.sum_congr rfl fun y _ => mul_assoc (ringComplex (symbol (3 * R.yLU y) R.P.p)) _ _,
      sum_char_sub _ _ R.sum_lu_symbol (A₁ * A₂)]
    refine (norm_sum_le_card _ fun y => ?_).trans (mul_le_mul_of_nonneg_right (card_units_le _) hE)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_symbol_le _ _ R.P.primary)).trans
      (norm_mul_sub_mul_le hm1 hm2 (h1 _) (h2 _))
  rw [luBlock]
  refine norm_sum_le_card _ fun x₁ => ?_
  rw [Finset.sum_comm]
  exact norm_sum_le_card _ fun x₂ => key x₁ x₂

theorem norm_llBlock_le {A₂ : ℂ} (h2 : ∀ t, ‖R.ll Θ t w - A₂‖ ≤ D) (hm2 : ‖A₂‖ ≤ M)
    (hE : 0 ≤ 2 * M * D + D ^ 2) :
    ‖R.llBlock Θ w‖ ≤ (Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) *
      ((Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) * (2 * M * D + D ^ 2)))) := by
  set F : R.P.Res → R.Q.Res → {y : R.P.Res // y ≠ 0} → {y : R.Q.Res // y ≠ 0} → ℂ :=
    fun (x₁ : R.P.Res) (x₂ : R.Q.Res) (y₁ : {y : R.P.Res // y ≠ 0}) (y₂ : {y : R.Q.Res // y ≠ 0}) =>
    ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
      (R.ll Θ (R.crt x₁ x₂ - R.mLowBeta (R.crt y₁.1 y₂.1)) w * R.ll Θ (R.crt x₁ x₂) w) with hF
  have hB : R.llBlock Θ w = ∑ x₁, ∑ x₂, ∑ y₁, ∑ y₂, F x₁ x₂ y₁ y₂ := by
    rw [llBlock]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x₂ _ => Finset.sum_congr rfl fun y₁ _ =>
      Finset.sum_congr rfl fun y₂ _ => by rw [hF]; ring
  have key : ∀ x₁ x₂, ‖∑ y₁, ∑ y₂, F x₁ x₂ y₁ y₂‖ ≤
      (Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) * (2 * M * D + D ^ 2)) := by
    intro x₁ x₂
    have hχ : ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
        ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) = 0 := R.sum_ll_symbol
    have e : ∑ y₁, ∑ y₂, F x₁ x₂ y₁ y₂ = ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
        ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
          (R.ll Θ (R.crt x₁ x₂ - R.mLowBeta (R.crt y₁.1 y₂.1)) w * R.ll Θ (R.crt x₁ x₂) w - A₂ * A₂) := by
      rw [show (∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
          ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
            (R.ll Θ (R.crt x₁ x₂ - R.mLowBeta (R.crt y₁.1 y₂.1)) w * R.ll Θ (R.crt x₁ x₂) w - A₂ * A₂)) =
          (∑ y₁, ∑ y₂, F x₁ x₂ y₁ y₂) - (∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
            ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p))) * (A₂ * A₂) by
        simp only [hF, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ => by ring, hχ, zero_mul, sub_zero]
    rw [e]
    refine (norm_sum_le_card _ fun y₁ => (norm_sum_le_card _ fun y₂ => ?_).trans
      (mul_le_mul_of_nonneg_right (card_units_le _) hE)).trans
      (mul_le_mul_of_nonneg_right (card_units_le _) (by positivity))
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_symbol_le _ _ R.primary_m)).trans
      (norm_mul_sub_mul_le hm2 hm2 (h2 _) (h2 _))
  rw [hB]
  exact norm_sum_le_card _ fun x₁ => norm_sum_le_card _ fun x₂ => key x₁ x₂

end Blocks

/-- The remainder is a sum of approximation errors at the Hecke points. -/
theorem norm_remainder_le (w : HyperbolicSpace) {M D : ℝ} {A0 A₁ A₂ A₃ A₄ : ℂ}
    (h0 : ‖sourceTheta w - A0‖ ≤ D) (hm0 : ‖A0‖ ≤ M) (h1 : ‖R.hh sourceTheta w - A₁‖ ≤ D)
    (h2 : ∀ t, ‖R.ll sourceTheta t w - A₂‖ ≤ D) (h3 : ∀ t, ‖R.hl sourceTheta t w - A₃‖ ≤ D)
    (h4 : ∀ t, ‖R.lh sourceTheta t w - A₄‖ ≤ D) (hm1 : ‖A₁‖ ≤ M) (hm2 : ‖A₂‖ ≤ M) (hm3 : ‖A₃‖ ≤ M)
    (hm4 : ‖A₄‖ ≤ M) (hA12 : A₁ * A₂ = A0 * A0) (hA34 : A₃ * A₄ = A0 * A0) (hE : 0 ≤ 2 * M * D + D ^ 2) :
    ‖R.remainder w‖ ≤ (Fintype.card R.P.Res : ℝ) * (Fintype.card R.Q.Res : ℝ) *
      (8 + 2 * (Fintype.card R.Q.Res : ℝ) + 2 * (Fintype.card R.P.Res : ℝ) +
        (Fintype.card R.P.Res : ℝ) * (Fintype.card R.Q.Res : ℝ)) * (2 * M * D + D ^ 2) := by
  have b1 := R.norm_block_dil_le sourceTheta w h0 hm0 h1 h2 hm1 hm2 hA12
  have b2 := R.norm_block_ratio_le sourceTheta w h0 hm0 h3 h4 hm3 hm4 hA34
  have b3 := R.norm_ulBlock_le sourceTheta w h3 h2 hm3 hm2 hE
  have b4 := R.norm_luBlock_le sourceTheta w h4 h2 hm4 hm2 hE
  have b5 := R.norm_llBlock_le sourceTheta w h2 hm2 hE
  set s := ringComplex (symbol R.P.p R.Q.p)
  have hs1 : ‖s‖ ≤ 1 := norm_symbol_le _ _ R.Q.primary
  set X1 := R.hh sourceTheta w * R.llSum sourceTheta w -
    (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ) * (sourceTheta w * sourceTheta w)
  set X2 := R.hlSum sourceTheta w * R.lhSum sourceTheta w -
    (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ) * (sourceTheta w * sourceTheta w)
  have hrem : R.remainder w = 2 * X1 + 2 * s * X2 + 2 * R.ulBlock sourceTheta w + 2 * R.luBlock sourceTheta w +
      R.llBlock sourceTheta w := by
    rw [remainder, sourceTrace, R.heckeTrace_eq_blocks sourceTheta sourceTheta_automorphy w, growth]
    ring
  have n2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have t1 : ‖2 * X1‖ ≤ 2 * ((Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) * (2 * (2 * M * D + D ^ 2)))) := by
    rw [norm_mul, n2]; exact mul_le_mul_of_nonneg_left b1 (by norm_num)
  have t2 : ‖2 * s * X2‖ ≤ 2 * ((Fintype.card R.Q.Res : ℝ) * ((Fintype.card R.P.Res : ℝ) * (2 * (2 * M * D + D ^ 2)))) := by
    rw [norm_mul, norm_mul, n2, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (norm_nonneg _) hs1).trans b2) (by norm_num)
  have t3 : ‖2 * R.ulBlock sourceTheta w‖ ≤ 2 * ((Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) *
      ((Fintype.card R.Q.Res : ℝ) * (2 * M * D + D ^ 2)))) := by
    rw [norm_mul, n2]; exact mul_le_mul_of_nonneg_left b3 (by norm_num)
  have t4 : ‖2 * R.luBlock sourceTheta w‖ ≤ 2 * ((Fintype.card R.P.Res : ℝ) * ((Fintype.card R.Q.Res : ℝ) *
      ((Fintype.card R.P.Res : ℝ) * (2 * M * D + D ^ 2)))) := by
    rw [norm_mul, n2]; exact mul_le_mul_of_nonneg_left b4 (by norm_num)
  rw [hrem]
  have tot := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) b5)
  refine tot.trans (le_of_eq ?_)
  ring

/-- The power of `v` in the strip bound. -/
theorem strip_rpow {a v κ C ρ : ℝ} (ha : 0 < a) (hv : 0 < v) (hav : a ≤ v) (hρ : 0 < ρ) (K : ℝ) (hK : 0 ≤ K) :
    K * (2 * (κ * ρ ^ ((2 : ℝ) / 3) * v ^ ((2 : ℝ) / 3)) * (C * ρ ^ 3 / v ^ 3) + (C * ρ ^ 3 / v ^ 3) ^ 2) ≤
      K * (2 * κ * ρ ^ ((2 : ℝ) / 3) * (C * ρ ^ 3) + (C * ρ ^ 3) ^ 2 * a ^ (-(11 : ℝ) / 3)) *
        v ^ (-(7 : ℝ) / 3) := by
  have hv3 : v ^ ((2 : ℝ) / 3) / v ^ 3 = v ^ (-(7 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hv]
    norm_num
  have hv6 : 1 / v ^ 6 ≤ a ^ (-(11 : ℝ) / 3) * v ^ (-(7 : ℝ) / 3) := by
    have hsplit : 1 / v ^ 6 = v ^ (-(11 : ℝ) / 3) * v ^ (-(7 : ℝ) / 3) := by
      rw [← Real.rpow_add hv, one_div, ← Real.rpow_natCast, ← Real.rpow_neg hv.le]
      norm_num
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hav (by norm_num)) (by positivity)
  have hEbv : 2 * (κ * ρ ^ ((2 : ℝ) / 3) * v ^ ((2 : ℝ) / 3)) * (C * ρ ^ 3 / v ^ 3) + (C * ρ ^ 3 / v ^ 3) ^ 2 =
      2 * κ * ρ ^ ((2 : ℝ) / 3) * (C * ρ ^ 3) * (v ^ ((2 : ℝ) / 3) / v ^ 3) + (C * ρ ^ 3) ^ 2 * (1 / v ^ 6) := by
    field_simp
  rw [hEbv, hv3]
  have h6 := mul_le_mul_of_nonneg_left hv6 (by positivity : (0 : ℝ) ≤ (C * ρ ^ 3) ^ 2)
  nlinarith [mul_le_mul_of_nonneg_left h6 hK, Real.rpow_nonneg hv.le (-(7 : ℝ) / 3),
    Real.rpow_nonneg hρ.le ((2 : ℝ) / 3)]

/-- **`G'_m = O(v^{−7/3})` on the standard strip above any fixed height.** -/
theorem norm_remainder_strip (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖R.remainder (upperPoint z v hv)‖ ≤ K * v ^ (-(7 : ℝ) / 3) := by
  have hp1 := R.P.one_le_norm
  have hq1 := R.Q.one_le_norm
  have hp0 := R.P.norm_pos
  have hq0 := R.Q.norm_pos
  set ρp := ‖ringComplex R.P.p‖ with hρp
  set ρq := ‖ringComplex R.Q.p‖ with hρq
  set ρ := ρp * ρq with hρdef
  have hρ1 : 1 ≤ ρ := by nlinarith
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height (a / ρ) (div_pos ha hρ0)
  set c : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue with hcdef
  set Kc : ℝ := (Fintype.card R.P.Res : ℝ) * (Fintype.card R.Q.Res : ℝ) *
      (8 + 2 * (Fintype.card R.Q.Res : ℝ) + 2 * (Fintype.card R.P.Res : ℝ) +
        (Fintype.card R.P.Res : ℝ) * (Fintype.card R.Q.Res : ℝ)) with hKc
  have hK0 : 0 ≤ Kc := by positivity
  refine ⟨Kc * (2 * ‖c‖ * ρ ^ ((2 : ℝ) / 3) * (C₁ * ρ ^ 3) + (C₁ * ρ ^ 3) ^ 2 * a ^ (-(11 : ℝ) / 3)),
    by positivity, fun z v hv hav => ?_⟩
  set A : ℝ → ℂ := fun h => c * (h : ℂ) ^ (2 / 3 : ℂ) with hAdef
  set M := ‖c‖ * ρ ^ ((2 : ℝ) / 3) * v ^ ((2 : ℝ) / 3) with hMdef
  set D := C₁ * ρ ^ 3 / v ^ 3 with hDdef
  have hcube : ∀ (ζ : ℂ) (h : ℝ) (hh : 0 < h), v / ρ ≤ h → ‖sourceTheta (upperPoint ζ h hh) - A h‖ ≤ D := by
    intro ζ h hh hle
    have hd := hdec h hh (le_trans (div_le_div_of_nonneg_right hav hρ0.le) hle) ζ
    refine hd.trans ?_
    rw [hDdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (v / ρ) ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ (div_pos hv hρ0).le hle 3
    have e : (v / ρ) ^ 3 * ρ ^ 3 = v ^ 3 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ C₁ * ρ ^ 3)]
  have hAM : ∀ h : ℝ, 0 < h → h ≤ ρ * v → ‖A h‖ ≤ M := by
    intro h hh hle
    rw [hAdef, norm_mul, norm_cpow_two_thirds hh, hMdef, mul_assoc, ← Real.mul_rpow hρ0.le hv.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh.le hle (by norm_num)) (norm_nonneg _)
  have hAA : ∀ x y : ℝ, 0 < x → 0 < y → x * y = v * v → A x * A y = A v * A v := by
    intro x y hx hy hxy
    simp only [hAdef]
    rw [show c * (x : ℂ) ^ (2 / 3 : ℂ) * (c * (y : ℂ) ^ (2 / 3 : ℂ)) =
        c ^ 2 * ((x : ℂ) ^ (2 / 3 : ℂ) * (y : ℂ) ^ (2 / 3 : ℂ)) by ring,
      show c * (v : ℂ) ^ (2 / 3 : ℂ) * (c * (v : ℂ) ^ (2 / 3 : ℂ)) =
        c ^ 2 * ((v : ℂ) ^ (2 / 3 : ℂ) * (v : ℂ) ^ (2 / 3 : ℂ)) by ring,
      ← Complex.mul_cpow_ofReal_nonneg hx.le hy.le, ← Complex.mul_cpow_ofReal_nonneg hv.le hv.le]
    rw [show (x : ℂ) * y = v * v by exact_mod_cast hxy]
  have hHhh : 0 < ρp * (ρq * v) := by positivity
  have hHll : 0 < v / ρq / ρp := by positivity
  have hHhl : 0 < ρp * v / ρq := by positivity
  have hHlh : 0 < ρq * v / ρp := by positivity
  have lo_hh : v / ρ ≤ ρp * (ρq * v) := by
    rw [div_le_iff₀ hρ0, hρdef]; nlinarith [mul_le_mul hp1 hq1 zero_le_one hp0.le, mul_pos hp0 hq0]
  have lo_ll : v / ρ ≤ v / ρq / ρp := by rw [hρdef, div_div, mul_comm]
  have lo_hl : v / ρ ≤ ρp * v / ρq := by
    rw [hρdef, div_le_div_iff₀ (by positivity) hq0]; nlinarith [mul_le_mul hp1 hp1 zero_le_one hp0.le]
  have lo_lh : v / ρ ≤ ρq * v / ρp := by
    rw [hρdef, div_le_div_iff₀ (by positivity) hp0]; nlinarith [mul_le_mul hq1 hq1 zero_le_one hq0.le]
  have lo_0 : v / ρ ≤ v := div_le_self hv.le hρ1
  have up_0 : v ≤ ρ * v := le_mul_of_one_le_left hv.le hρ1
  have up_hh : ρp * (ρq * v) ≤ ρ * v := by rw [hρdef, mul_assoc]
  have up_ll : v / ρq / ρp ≤ ρ * v := by
    have : v / ρq / ρp ≤ v := by
      rw [div_div]; exact div_le_self hv.le (by nlinarith)
    exact this.trans up_0
  have up_hl : ρp * v / ρq ≤ ρ * v := by
    rw [div_le_iff₀ hq0, hρdef]; nlinarith [mul_le_mul hq1 hq1 zero_le_one hq0.le, mul_pos hp0 hv]
  have up_lh : ρq * v / ρp ≤ ρ * v := by
    rw [div_le_iff₀ hp0, hρdef]; nlinarith [mul_le_mul hp1 hp1 zero_le_one hp0.le, mul_pos hq0 hv]
  have hprod1 : ρp * (ρq * v) * (v / ρq / ρp) = v * v := by field_simp
  have hprod2 : ρp * v / ρq * (ρq * v / ρp) = v * v := by field_simp
  have hE : 0 ≤ 2 * M * D + D ^ 2 := by positivity
  have key := R.norm_remainder_le (upperPoint z v hv) (hcube _ _ hv lo_0) (hAM _ hv up_0)
    (by rw [R.hh_point]; exact hcube _ _ _ lo_hh) (fun t => by rw [R.ll_point]; exact hcube _ _ _ lo_ll)
    (fun t => by rw [R.hl_point]; exact hcube _ _ _ lo_hl) (fun t => by rw [R.lh_point]; exact hcube _ _ _ lo_lh)
    (hAM _ hHhh up_hh) (hAM _ hHll up_ll) (hAM _ hHhl up_hl) (hAM _ hHlh up_lh)
    (hAA _ _ hHhh hHll hprod1) (hAA _ _ hHhl hHlh hprod2) hE
  refine key.trans ?_
  rw [hMdef, hDdef]
  exact strip_rpow ha hv hav hρ0 Kc hK0

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
