import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeHeckeTraceIsNineBlocksOfHeckePoints

/-!
# The `W`-types of the composite trace fold onto the `U`-types

The Hecke points depend only on residues: `Θ^{ll}_t` on `t` mod `m`, `Θ^{hl}_t` on `t` mod `q`, `Θ^{lh}_t` on `t` mod `p`
(`ll_congr`, `hl_congr`, `lh_congr`). Hence the blocks reduce by translations of the residue fields:

* `(W, W) = (U, U) = Θ^{hh}·Σ_xΘ^{ll}_x`;
* `(U, W) = (W, U) = (p/q)₃·(Σ_uΘ^{hl}_u)(Σ_uΘ^{lh}_u)`: the `p`-adic nebentypus at the `q`-Hecke point is
  `κ(W'_q)^{−2}κ(A_pM'A_p⁻¹) = (p/q)₃` (`phase_UW`), and `(q/p)₃ = (p/q)₃` by reciprocity;

so the dilate blocks carry `2 + 2(p/q)₃` copies of the theta square, not `4`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPair

variable (R : PrimaryPair)

theorem contraction_transThree_mul (s : O) :
    R.contraction * complexMatrix (transThree (R.P.p * (R.Q.p * s))) = complexMatrix (transThree s) * R.contraction := by
  rw [contraction, mul_assoc, show R.P.p * (R.Q.p * s) = R.Q.p * (R.P.p * s) by ring,
    R.Q.contraction_transThree_mul, ← mul_assoc, R.P.contraction_transThree_mul, mul_assoc]

theorem m_dvd_of_dvd {t : O} (hp : R.P.p ∣ t) (hq : R.Q.p ∣ t) : R.P.p * R.Q.p ∣ t := R.coprime.mul_dvd hp hq

/-! ### Residue fields: translations and dilations permute the sums -/

theorem sum_add_right {F : Type*} [AddGroup F] [Fintype F] (f : F → ℂ) (c : F) :
    ∑ x : F, f (x + c) = ∑ x : F, f x := Equiv.sum_comp (Equiv.addRight c) f

theorem sum_mul_add {F : Type*} [Field F] [Fintype F] (f : F → ℂ) (a c : F) (ha : a ≠ 0) :
    ∑ x : F, f (a * x + c) = ∑ x : F, f x := by
  rw [Fintype.sum_bijective (fun x => a * x) ⟨fun x y h => mul_left_cancel₀ ha h, fun y => ⟨a⁻¹ * y, by simp [ha]⟩⟩ (fun x => f (a * x + c))
    (fun y => f (y + c)) (fun x => rfl)]
  exact sum_add_right f c

theorem sum_neg_units {F : Type*} [Field F] [Fintype F] (f : {y : F // y ≠ 0} → ℂ) :
    ∑ y : {y : F // y ≠ 0}, f ⟨-y.1, neg_ne_zero.mpr y.2⟩ = ∑ y, f y := by
  let e : {y : F // y ≠ 0} ≃ {y : F // y ≠ 0} :=
    ⟨fun y => ⟨-y.1, neg_ne_zero.mpr y.2⟩, fun y => ⟨-y.1, neg_ne_zero.mpr y.2⟩,
      fun y => by simp, fun y => by simp⟩
  exact Equiv.sum_comp e f

variable {R}

section Congr

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
include hΘ

theorem ll_congr {t t' : O} (h1 : R.P.res t = R.P.res t') (h2 : R.Q.res t = R.Q.res t') (w : HyperbolicSpace) :
    R.ll Θ t w = R.ll Θ t' w := by
  have hp : R.P.p ∣ t' - t := by rw [← R.P.res_eq_zero_iff, map_sub, h1, sub_self]
  have hq : R.Q.p ∣ t' - t := by rw [← R.Q.res_eq_zero_iff, map_sub, h2, sub_self]
  obtain ⟨s, hs⟩ := R.m_dvd_of_dvd hp hq
  have ht : t' = R.P.p * (R.Q.p * s) + t := by linear_combination hs
  have e : R.contraction • (complexMatrix (transThree t') • w) =
      complexMatrix (transThree s) • (R.contraction • (complexMatrix (transThree t) • w)) := by
    rw [ht, ← PrimaryPrime.transThree_mul, map_mul, mul_smul,
      ← mul_smul R.contraction (complexMatrix (transThree (R.P.p * (R.Q.p * s)))), R.contraction_transThree_mul,
      mul_smul]
  unfold ll
  rw [e, theta_trans Θ hΘ]

theorem hl_congr {t t' : O} (h : R.Q.res t = R.Q.res t') (w : HyperbolicSpace) :
    R.hl Θ t w = R.hl Θ t' w := by
  have hq : R.Q.p ∣ t' - t := by rw [← R.Q.res_eq_zero_iff, map_sub, h, sub_self]
  obtain ⟨s, hs⟩ := hq
  have ht : t' = R.Q.p * s + t := by linear_combination hs
  have e : R.Q.contraction • (complexMatrix (transThree t') • (R.P.dilation • w)) =
      complexMatrix (transThree s) • (R.Q.contraction • (complexMatrix (transThree t) • (R.P.dilation • w))) := by
    rw [ht, ← PrimaryPrime.transThree_mul, map_mul, mul_smul,
      ← mul_smul R.Q.contraction (complexMatrix (transThree (R.Q.p * s))), R.Q.contraction_transThree_mul, mul_smul]
  unfold hl
  rw [e, theta_trans Θ hΘ]

theorem lh_congr {t t' : O} (h : R.P.res t = R.P.res t') (w : HyperbolicSpace) :
    R.lh Θ t w = R.lh Θ t' w := by
  have hp : R.P.p ∣ t' - t := by rw [← R.P.res_eq_zero_iff, map_sub, h, sub_self]
  obtain ⟨s, hs⟩ := hp
  have ht : t' = R.P.p * s + t := by linear_combination hs
  have e : R.P.contraction • (complexMatrix (transThree t') • (R.Q.dilation • w)) =
      complexMatrix (transThree s) • (R.P.contraction • (complexMatrix (transThree t) • (R.Q.dilation • w))) := by
    rw [ht, ← PrimaryPrime.transThree_mul, map_mul, mul_smul,
      ← mul_smul R.P.contraction (complexMatrix (transThree (R.P.p * s))), R.P.contraction_transThree_mul, mul_smul]
  unfold lh
  rw [e, theta_trans Θ hΘ]

end Congr

variable (R)

/-! ### The phases of the ratio types -/

theorem isCoprime_three_qK : IsCoprime (3 * R.qK) R.Q.p := ⟨-(3 * R.P.p), R.qDelta, by linear_combination R.q_det⟩

theorem isCoprime_three_pK : IsCoprime (3 * R.pK) R.P.p := ⟨-(3 * R.Q.p), R.pDelta, by linear_combination R.p_det⟩

theorem complexCharacter_ne_zero (M : levelThree) : complexCharacter M ≠ 0 := by
  intro h
  have := norm_complexCharacter M
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **The `p`-adic nebentypus at the `q`-Hecke point**: `κ(W'_q)^{−2}κ(A_pM'A_p⁻¹) = (p/q)₃`. -/
theorem phase_UW :
    (complexCharacter R.wQ ^ 2)⁻¹ * complexCharacter R.qHighUp = ringComplex (symbol R.P.p R.Q.p) := by
  have h1 : complexCharacter R.wQ = ringComplex (symbol R.P.p R.Q.p) * ringComplex (symbol (3 * R.qK) R.Q.p) := by
    rw [complexCharacter_eq_symbol, show ((R.wQ : levelThree) : SL(2, O)) 1 0 = R.P.p * (3 * R.qK) by
      simp [wQ]; ring, show ((R.wQ : levelThree) : SL(2, O)) 0 0 = R.Q.p from rfl, symbol_mul_numerator, map_mul]
  have h2 : complexCharacter R.qHighUp = ringComplex (symbol (3 * R.qK) R.Q.p) ^ 2 := by
    rw [complexCharacter_eq_symbol, show ((R.qHighUp : levelThree) : SL(2, O)) 1 0 = 3 * R.qK from rfl,
      show ((R.qHighUp : levelThree) : SL(2, O)) 0 0 = R.Q.p ^ 2 from rfl, symbol_pow_denominator, map_pow]
  have hk : ringComplex (symbol (3 * R.qK) R.Q.p) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ ringComplex_injective]
    exact symbol_ne_zero_of_isCoprime _ _ R.Q.primary R.isCoprime_three_qK
  have hc : ringComplex (symbol R.P.p R.Q.p) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime _ _ R.Q.primary R.coprime, map_one]
  have hs : ringComplex (symbol R.P.p R.Q.p) ≠ 0 := by
    intro h; rw [h] at hc; norm_num at hc
  rw [h1, h2]
  field_simp
  linear_combination (-1 : ℂ) * hc

/-- `κ(W'_p)^{−2}κ(A_qM''A_q⁻¹) = (q/p)₃ = (p/q)₃`. -/
theorem phase_WU :
    (complexCharacter R.wP ^ 2)⁻¹ * complexCharacter R.pHighUp = ringComplex (symbol R.P.p R.Q.p) := by
  have h1 : complexCharacter R.wP = ringComplex (symbol R.Q.p R.P.p) * ringComplex (symbol (3 * R.pK) R.P.p) := by
    rw [complexCharacter_eq_symbol, show ((R.wP : levelThree) : SL(2, O)) 1 0 = R.Q.p * (3 * R.pK) by
      simp [wP]; ring, show ((R.wP : levelThree) : SL(2, O)) 0 0 = R.P.p from rfl, symbol_mul_numerator, map_mul]
  have h2 : complexCharacter R.pHighUp = ringComplex (symbol (3 * R.pK) R.P.p) ^ 2 := by
    rw [complexCharacter_eq_symbol, show ((R.pHighUp : levelThree) : SL(2, O)) 1 0 = 3 * R.pK from rfl,
      show ((R.pHighUp : levelThree) : SL(2, O)) 0 0 = R.P.p ^ 2 from rfl, symbol_pow_denominator, map_pow]
  have hk : ringComplex (symbol (3 * R.pK) R.P.p) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ ringComplex_injective]
    exact symbol_ne_zero_of_isCoprime _ _ R.P.primary R.isCoprime_three_pK
  have hc : ringComplex (symbol R.Q.p R.P.p) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime _ _ R.P.primary R.coprime.symm, map_one]
  have hs : ringComplex (symbol R.Q.p R.P.p) ≠ 0 := by
    intro h; rw [h] at hc; norm_num at hc
  rw [h1, h2, symbol_reciprocity R.P.p R.Q.p R.P.primary R.Q.primary]
  field_simp
  linear_combination (-1 : ℂ) * hc

/-! ### The blocks -/

/-- `Σ_{x mod m} Θ^{ll}_x`. -/
def llSum (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res, R.ll Θ (R.crt x₁ x₂) w

/-- `Σ_{u mod q} Θ^{hl}_u`. -/
def hlSum (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ := ∑ u : R.Q.Res, R.hl Θ (R.Q.lift u) w

/-- `Σ_{u mod p} Θ^{lh}_u`. -/
def lhSum (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ := ∑ u : R.P.Res, R.lh Θ (R.P.lift u) w

/-- The `(U, L)` block. -/
def ulBlock (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
    ringComplex (symbol (3 * R.yUL y₂) R.Q.p) *
      R.hl Θ (R.P.p * R.crt x₁ x₂ - R.Q.lowBeta (R.yUL y₂)) w * R.ll Θ (R.crt x₁ x₂) w

/-- The `(L, U)` block. -/
def luBlock (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑ x₁ : R.P.Res, ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ x₂ : R.Q.Res,
    ringComplex (symbol (3 * R.yLU y₁) R.P.p) *
      R.lh Θ (R.Q.p * R.crt x₁ x₂ - R.P.lowBeta (R.yLU y₁)) w * R.ll Θ (R.crt x₁ x₂) w

/-- The `(L, L)` block. -/
def llBlock (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑ x₁ : R.P.Res, ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ x₂ : R.Q.Res, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
    ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
      R.ll Θ (R.crt x₁ x₂ - R.mLowBeta (R.crt y₁.1 y₂.1)) w * R.ll Θ (R.crt x₁ x₂) w

/-! ### Residues of the Bezout data -/

theorem Q_res_pDelta : R.Q.res R.pDelta = R.pInv := by
  have h := congrArg R.Q.res R.p_det
  simp only [map_sub, map_mul, map_one, R.Q.res_nine, R.Q.res_p, zero_mul, mul_zero, sub_zero] at h
  rw [pInv]
  exact eq_inv_of_mul_eq_one_right h

theorem P_res_qDelta : R.P.res R.qDelta = R.qInv := by
  have h := congrArg R.P.res R.q_det
  simp only [map_sub, map_mul, map_one, R.P.res_nine, R.P.res_p, zero_mul, mul_zero, sub_zero] at h
  rw [qInv]
  exact eq_inv_of_mul_eq_one_right h

theorem Q_res_wlBeta (y : O) (hy : ¬ R.Q.p ∣ y) :
    R.Q.res (R.wlBeta y) * (9 * R.Q.res (R.wlC y)) = -1 := by
  have h := congrArg R.Q.res (R.wl_det y hy)
  simp only [map_sub, map_mul, map_one, map_pow, R.Q.res_nine, R.Q.res_p, zero_mul, mul_zero, zero_sub] at h
  linear_combination -h

theorem P_res_lwBeta (y : O) (hy : ¬ R.P.p ∣ y) :
    R.P.res (R.lwBeta y) * (9 * R.P.res (R.lwC y)) = -1 := by
  have h := congrArg R.P.res (R.lw_det y hy)
  simp only [map_sub, map_mul, map_one, map_pow, R.P.res_nine, R.P.res_p, zero_mul, mul_zero, zero_sub] at h
  linear_combination -h

theorem Q_res_lowBeta (y : O) (hy : ¬ R.Q.p ∣ y) : R.Q.res (R.Q.lowBeta y) * (9 * R.Q.res y) = -1 := by
  have h := congrArg R.Q.res (R.Q.low_det y hy)
  simp only [map_sub, map_mul, map_one, R.Q.res_nine, R.Q.res_p, zero_mul, zero_sub] at h
  linear_combination -h

theorem P_res_lowBeta (y : O) (hy : ¬ R.P.p ∣ y) : R.P.res (R.P.lowBeta y) * (9 * R.P.res y) = -1 := by
  have h := congrArg R.P.res (R.P.low_det y hy)
  simp only [map_sub, map_mul, map_one, R.P.res_nine, R.P.res_p, zero_mul, zero_sub] at h
  linear_combination -h

theorem Q_p_ne : R.Q.res R.P.p ≠ 0 := R.Q_res_p_ne_zero
theorem P_q_ne : R.P.res R.Q.p ≠ 0 := R.P_res_q_ne_zero

theorem Q_res_yUL (y : {y : R.Q.Res // y ≠ 0}) : R.Q.res (R.yUL y) = y.1 * R.pInv := by
  rw [yUL, R.Q.res_lift]

theorem P_res_yLU (y : {y : R.P.Res // y ≠ 0}) : R.P.res (R.yLU y) = y.1 * R.qInv := by
  rw [yLU, R.P.res_lift]

theorem Q_res_wlC (y : {y : R.Q.Res // y ≠ 0}) : R.Q.res (R.wlC (R.yWL y)) = y.1 * R.pInv := by
  rw [wlC, yWL, map_add, map_mul, map_mul, map_pow, R.Q.res_lift, R.Q.res_p, zero_mul, add_zero, R.Q_res_pDelta]
  have hp := R.Q_p_mul_pInv
  linear_combination y.1 * R.pInv * (R.Q.res R.P.p * R.pInv + 1) * hp

theorem P_res_lwC (y : {y : R.P.Res // y ≠ 0}) : R.P.res (R.lwC (R.yLW y)) = y.1 * R.qInv := by
  rw [lwC, yLW, map_add, map_mul, map_mul, map_pow, R.P.res_lift, R.P.res_p, zero_mul, add_zero, R.P_res_qDelta]
  have hq := R.P_q_mul_qInv
  linear_combination y.1 * R.qInv * (R.P.res R.Q.p * R.qInv + 1) * hq

theorem Q_res_wlShift (y : {y : R.Q.Res // y ≠ 0}) :
    R.Q.res (R.wlShift (R.yWL y)) = R.pInv + (9 * y.1)⁻¹ := by
  have hb := R.Q_res_wlBeta (R.yWL y) (R.not_dvd_yWL y)
  rw [R.Q_res_wlC] at hb
  have hy := y.2
  have hp := R.Q_p_ne
  have h9 := R.Q.nine_ne_zero'
  have hβ : R.Q.res (R.wlBeta (R.yWL y)) = -(9 * (y.1 * R.pInv))⁻¹ := by
    rw [pInv] at hb ⊢
    field_simp
    linear_combination hb
  rw [wlShift, map_sub, map_mul, map_mul, map_mul, map_add, map_mul, map_mul, R.Q.res_p, R.Q.res_nine, hβ,
    R.Q_res_pDelta, yWL, R.Q.res_lift, R.Q_res_pDelta]
  rw [pInv]
  field_simp
  ring

theorem P_res_lwShift (y : {y : R.P.Res // y ≠ 0}) :
    R.P.res (R.lwShift (R.yLW y)) = R.qInv + (9 * y.1)⁻¹ := by
  have hb := R.P_res_lwBeta (R.yLW y) (R.not_dvd_yLW y)
  rw [R.P_res_lwC] at hb
  have hy := y.2
  have hq := R.P_q_ne
  have h9 := R.P.nine_ne_zero'
  have hβ : R.P.res (R.lwBeta (R.yLW y)) = -(9 * (y.1 * R.qInv))⁻¹ := by
    rw [qInv] at hb ⊢
    field_simp
    linear_combination hb
  rw [lwShift, map_sub, map_mul, map_mul, map_mul, map_add, map_mul, map_mul, R.P.res_p, R.P.res_nine, hβ,
    R.P_res_qDelta, yLW, R.P.res_lift, R.P_res_qDelta]
  rw [qInv]
  field_simp
  ring

theorem Q_res_lowBeta_yUL (y : {y : R.Q.Res // y ≠ 0}) :
    R.Q.res (R.Q.lowBeta (R.yUL y)) = -(9 * (y.1 * R.pInv))⁻¹ := by
  have hb := R.Q_res_lowBeta (R.yUL y) (R.not_dvd_yUL y)
  rw [R.Q_res_yUL] at hb
  have hy := y.2
  have hp := R.pInv_ne_zero
  have h9 := R.Q.nine_ne_zero'
  field_simp
  linear_combination hb

theorem P_res_lowBeta_yLU (y : {y : R.P.Res // y ≠ 0}) :
    R.P.res (R.P.lowBeta (R.yLU y)) = -(9 * (y.1 * R.qInv))⁻¹ := by
  have hb := R.P_res_lowBeta (R.yLU y) (R.not_dvd_yLU y)
  rw [R.P_res_yLU] at hb
  have hy := y.2
  have hq := R.qInv_ne_zero
  have h9 := R.P.nine_ne_zero'
  field_simp
  linear_combination hb

/-- `y ↦ −y` on the units of a residue field. -/
def negY {F : Type*} [Field F] (y : {y : F // y ≠ 0}) : {y : F // y ≠ 0} := ⟨-y.1, neg_ne_zero.mpr y.2⟩

/-- **The `(W, L)` phase is a `(U, L)` phase**: `κ(W'_p)^{−2}κ(M_y) = (3c/q)₃ = (3y'/q)₃`. -/
theorem phase_WL (y : {y : R.Q.Res // y ≠ 0}) :
    (complexCharacter R.wP ^ 2)⁻¹ * complexCharacter (R.wlMat (R.yWL y) (R.not_dvd_yWL y)) =
      ringComplex (symbol (3 * R.yUL (negY y)) R.Q.p) := by
  set c := R.wlC (R.yWL y)
  have hW : complexCharacter (R.wlMat (R.yWL y) (R.not_dvd_yWL y)) =
      complexCharacter R.wP ^ 2 * ringComplex (symbol (3 * c) R.Q.p) := by
    rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol,
      show ((R.wlMat (R.yWL y) (R.not_dvd_yWL y) : levelThree) : SL(2, O)) 1 0 = 3 * c from rfl,
      show ((R.wlMat (R.yWL y) (R.not_dvd_yWL y) : levelThree) : SL(2, O)) 0 0 = R.P.p ^ 2 * R.Q.p from rfl,
      show ((R.wP : levelThree) : SL(2, O)) 1 0 = 3 * (R.Q.p * R.pK) from rfl,
      show ((R.wP : levelThree) : SL(2, O)) 0 0 = R.P.p from rfl, symbol_mul_denominator, symbol_pow_denominator,
      symbol_congr (show R.P.p ∣ 3 * c - 3 * (R.Q.p * R.pK) from
        ⟨3 * R.P.p * R.yWL y, by simp only [c, wlC]; ring⟩)]
    simp only [map_mul, map_pow]
  have hc : R.Q.p ∣ 3 * c - -(3 * R.yUL (negY y)) := by
    rw [← R.Q.res_eq_zero_iff, map_sub, map_neg, map_mul, map_mul, R.Q.res_three, R.Q_res_wlC, R.Q_res_yUL]
    simp [negY]
  rw [hW, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (R.complexCharacter_ne_zero R.wP)), one_mul,
    symbol_congr hc, symbol_neg_numerator _ _ R.Q.primary]

/-- **The `(L, W)` phase is an `(L, U)` phase.** -/
theorem phase_LW (y : {y : R.P.Res // y ≠ 0}) :
    (complexCharacter R.wQ ^ 2)⁻¹ * complexCharacter (R.lwMat (R.yLW y) (R.not_dvd_yLW y)) =
      ringComplex (symbol (3 * R.yLU (negY y)) R.P.p) := by
  set c := R.lwC (R.yLW y)
  have hW : complexCharacter (R.lwMat (R.yLW y) (R.not_dvd_yLW y)) =
      complexCharacter R.wQ ^ 2 * ringComplex (symbol (3 * c) R.P.p) := by
    rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol,
      show ((R.lwMat (R.yLW y) (R.not_dvd_yLW y) : levelThree) : SL(2, O)) 1 0 = 3 * c from rfl,
      show ((R.lwMat (R.yLW y) (R.not_dvd_yLW y) : levelThree) : SL(2, O)) 0 0 = R.Q.p ^ 2 * R.P.p from rfl,
      show ((R.wQ : levelThree) : SL(2, O)) 1 0 = 3 * (R.P.p * R.qK) from rfl,
      show ((R.wQ : levelThree) : SL(2, O)) 0 0 = R.Q.p from rfl, symbol_mul_denominator, symbol_pow_denominator,
      symbol_congr (show R.Q.p ∣ 3 * c - 3 * (R.P.p * R.qK) from
        ⟨3 * R.Q.p * R.yLW y, by simp only [c, lwC]; ring⟩)]
    simp only [map_mul, map_pow]
  have hc : R.P.p ∣ 3 * c - -(3 * R.yLU (negY y)) := by
    rw [← R.P.res_eq_zero_iff, map_sub, map_neg, map_mul, map_mul, R.P.res_three, R.P_res_lwC, R.P_res_yLU]
    simp [negY]
  rw [hW, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (R.complexCharacter_ne_zero R.wQ)), one_mul,
    symbol_congr hc, symbol_neg_numerator _ _ R.P.primary]

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
