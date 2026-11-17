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

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
