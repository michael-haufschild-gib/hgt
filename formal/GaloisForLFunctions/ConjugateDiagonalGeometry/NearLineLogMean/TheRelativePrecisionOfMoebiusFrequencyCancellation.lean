import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheBalanceOfPrimitiveMoebiusWindowFrequencies
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheExactLengthOrderOfUnsignedMoebiusFrequencies

/-!
# Relative imbalance of the signed primitive Möbius frequencies

Across polynomial lengths the unsigned cost has logarithmic order θ,
whereas the diagonal has one fixed polynomial height bound. Thus the
second-moment criterion becomes a precision requirement on the
difference of the positive and negative integrated frequency masses.
-/
noncomputable section
open Finset Filter Topology MeasureTheory Complex
open _root_.RHTower _root_.RHTower.Sieve
open GaloisForLFunctions.MultiscaleMollifiedZetaField
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

/-- Absolute signed excess as a fraction of the variation of the
individual integrated frequency coefficients. -/
def relativeMoebiusImbalance (N : ℕ) (T : ℝ) :=
  |∑ q ∈ primitiveRatioPairs N,integratedRatio N T q| / absoluteMoebiusOffDiagonal N T

private def energy (N : ℕ) (T : ℝ) := ∫ t in (1:ℝ)..T, ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2

private def diagonal (N : ℕ) (T : ℝ) := (T-1)*(∑ n ∈ Icc 1 N,mobiusRealCoefficient n^2/n)

private theorem energy_balance (N : ℕ) (T : ℝ) (hA : 0 < absoluteMoebiusOffDiagonal N T) :
    relativeMoebiusImbalance N T*absoluteMoebiusOffDiagonal N T=|energy N T-diagonal N T| := by
  rw [relativeMoebiusImbalance,div_mul_cancel₀ _ hA.ne',signed_primitive_window_excess]
  rfl

private theorem window_comparisons {θ : ℝ} (hθ : 1 < θ) :
    ∀ᶠ T : ℝ in atTop, let N := ⌊T^θ⌋₊
      1 ≤ T ∧ T^(θ-1) ≤ absoluteMoebiusOffDiagonal N T ∧
      absoluteMoebiusOffDiagonal N T ≤ T^(θ+1) ∧
      0 ≤ diagonal N T ∧ diagonal N T ≤ (1+θ)*T^2 ∧ 0 ≤ energy N T := by
  have hθ0 := zero_lt_one.trans hθ
  have hl := unsigned_cost_polynomial_order hθ
  filter_upwards [eventually_gt_atTop (1:ℝ),
    every_polynomial_height_cost_fails_unsigned hθ (by linarith only [] : θ-1<θ) 1,
    hl.eventually_lt_const (by linarith only [] : θ<θ+1)] with T ht hL hU
  let N := ⌊T^θ⌋₊
  have hp := zero_lt_one.trans ht
  have hN : 1 ≤ N := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow ht.le hθ0.le)
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hLow : T^(θ-1) ≤ absoluteMoebiusOffDiagonal N T := by simpa only [one_mul] using hL.le
  have ha := (Real.rpow_pos_of_pos hp _).trans_le hLow
  have hupper : absoluteMoebiusOffDiagonal N T ≤ T^(θ+1) := by
    apply (Real.log_le_log_iff ha (Real.rpow_pos_of_pos hp _)).mp
    rw [Real.log_rpow hp]
    exact ((div_lt_iff₀ (Real.log_pos ht)).mp hU).le
  have hmass : (∑ n ∈ Icc 1 N,mobiusRealCoefficient n^2/n) ≤ 1+Real.log N := by
    refine (sum_le_sum (fun n _ => ?_)).trans (sum_Icc_one_div_le_one_add_log N)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hb : |mobiusRealCoefficient n| ≤ 1 := by
      unfold mobiusRealCoefficient; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hlN := Real.log_le_log hn (Nat.floor_le (Real.rpow_nonneg hp.le θ))
  rw [Real.log_rpow hp] at hlN
  have hlogT := Real.log_le_sub_one_of_pos hp
  have hmass0 : 0 ≤ ∑ n ∈ Icc 1 N,mobiusRealCoefficient n^2/n :=
    sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hcharge : ∑ n ∈ Icc 1 N,mobiusRealCoefficient n^2/n ≤ (1+θ)*T := by
    linarith only [hmass,hlN,mul_le_mul_of_nonneg_left hlogT hθ0.le,ht,hθ0]
  refine ⟨ht.le,hLow,hupper,mul_nonneg (sub_nonneg.mpr ht.le) hmass0,?_,
    intervalIntegral.integral_nonneg ht.le (fun _ _ => sq_nonneg _)⟩
  exact (mul_le_mul (sub_le_self T zero_le_one) hcharge hmass0 hp.le).trans_eq (by ring)

/-- RH is equivalent to a fixed additive allowance in the exponent
of relative frequency imbalance, for cofinal lengths and unbounded
heights. -/
theorem rh_iff_relative_primitive_moebius_balance :
    RiemannHypothesis ↔
      ∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ T : ℝ in atTop,
          relativeMoebiusImbalance ⌊T^θ⌋₊ T ≤ C*T^(K-θ) := by
  rw [riemannHypothesis_iff_cofinal_pure_moebius_moment]
  simp_rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
  constructor
  · rintro ⟨K,hK,hh⟩
    refine ⟨K+3,by linarith only [hK],fun θ₀ _ => ?_⟩
    obtain ⟨θ,hθ,C,hC,hE⟩ := hh (max θ₀ 2) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    have hθ' : 1 < θ := (by norm_num : (1:ℝ)<2).trans_le ((le_max_right _ _).trans hθ)
    refine ⟨θ,(le_max_left _ _).trans hθ,C+1+θ,by linarith only [hC,hθ'],?_⟩
    refine (hE.and_eventually (window_comparisons hθ')).mono ?_
    rintro T ⟨henergy,hT,hlo,_,hd0,hd,he0⟩
    let N := ⌊T^θ⌋₊
    have hp := zero_lt_one.trans_le hT
    have hA := (Real.rpow_pos_of_pos hp _).trans_le hlo
    have hx : energy N T ≤ C*T^K := henergy
    have hE' := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT
      (by linarith only [] : K ≤ K+2)) hC
    have hD' := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT
      (by linarith only [hK] : (2:ℝ) ≤ K+2)) (by linarith only [hθ'] : 0 ≤ 1+θ)
    rw [Real.rpow_two] at hD'
    have hdiff : |energy N T-diagonal N T| ≤ (C+1+θ)*T^(K+2) := by
      rw [abs_le]; constructor <;> linarith only [hx,hd,hd0,he0,hE',hD']
    have hfact : (C+1+θ)*T^(K+2) =
        ((C+1+θ)*T^((K+3)-θ))*T^(θ-1) := by
      rw [mul_assoc,←Real.rpow_add hp,show K+3-θ+(θ-1)=K+2 by ring]
    rw [hfact] at hdiff
    have hw := mul_le_mul_of_nonneg_left hlo (mul_nonneg
      (by linarith only [hC,hθ'] : 0 ≤ C+1+θ) (Real.rpow_nonneg hp.le (K + 3 - θ)))
    exact le_of_mul_le_mul_right (((energy_balance N T hA).le.trans hdiff).trans hw) hA
  · rintro ⟨K,hK,hh⟩
    refine ⟨K+2,by linarith only [hK],fun θ₀ _ => ?_⟩
    obtain ⟨θ,hθ,C,hC,hB⟩ := hh (max θ₀ 2) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    have hθ' : 1 < θ := (by norm_num : (1:ℝ)<2).trans_le ((le_max_right _ _).trans hθ)
    refine ⟨θ,(le_max_left _ _).trans hθ,C+1+θ,by linarith only [hC,hθ'],?_⟩
    refine (hB.and_eventually (window_comparisons hθ')).mono ?_
    rintro T ⟨hrel,hT,hlo,hup,hd0,hd,he0⟩
    let N := ⌊T^θ⌋₊
    have hp := zero_lt_one.trans_le hT
    have hA := (Real.rpow_pos_of_pos hp _).trans_le hlo
    have hab := mul_le_mul hrel hup hA.le (mul_nonneg hC (Real.rpow_nonneg hp.le _))
    rw [energy_balance N T hA,mul_assoc,←Real.rpow_add hp,
      show K-θ+(θ+1)=K+1 by ring] at hab
    have hE' := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT
      (by linarith only [] : K+1 ≤ K+2)) hC
    have hD' := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT
      (by linarith only [hK] : (2:ℝ) ≤ K+2)) (by linarith only [hθ'] : 0 ≤ 1+θ)
    rw [Real.rpow_two] at hD'
    change energy N T ≤ _
    linarith only [(abs_le.mp hab).2,hd,hE',hD']

#print axioms rh_iff_relative_primitive_moebius_balance
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
