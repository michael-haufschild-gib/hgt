import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheZeroFreeRegionSavingOnShortMoebiusWindows
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheUnsignedCostOfTheMoebiusSecondMoment
import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicMertensBound

/-!
# Balance of positive and negative Möbius frequencies on short windows

Reduce each directed ratio before assigning a sign to its integrated
coefficient. The triangle inequality is exact inside each ratio, so the
linear absolute mass survives reduction. On short growing time windows
the signed energy and the diagonal are both sublinear in the cutoff.
Each sign therefore carries asymptotically half the total variation.
-/
noncomputable section
open Finset Filter MeasureTheory Topology
open _root_.RHTower _root_.RHTower.Sieve _root_.RHTower.CubicGamma
open GaloisForLFunctions.MultiscaleMollifiedZetaField
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

def integratedRatio (N : ℕ) (T : ℝ) (q : ℕ × ℕ) :=
  atom N q.1 q.2*cosInt (Real.log q.1-Real.log q.2) 1 (T-1)

/-- Total variation commutes with reduction by the common divisor for
every real spectral multiplier, even one that changes sign. -/
theorem absolute_primitive_spectrum (N : ℕ) (K : ℝ → ℝ) :
    (∑ m ∈ Icc 1 N,∑ n ∈ (Icc 1 N).erase m,
      |coeff m*coeff n*K (Real.log m-Real.log n)|) =
    ∑ q ∈ primitiveRatioPairs N,|atom N q.1 q.2*K (Real.log q.1-Real.log q.2)| := by
  let f := fun m n : ℕ => |coeff m*coeff n*K (Real.log m-Real.log n)|
  rw [←sum_offDiagPairs_eq_double N f,sum_offDiagPairs_eq_sum_ratio]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨ha,hb⟩ := mem_product.mp (mem_filter.mp hq).1
  have ha0 : (q.1:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp ha).1)
  have hb0 : (q.2:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hb).1)
  rw [abs_mul,←absolute_scale_correlation,Finset.sum_mul]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hd).1).1)
  simp only [f,Nat.cast_mul,Real.log_mul hd0 ha0,Real.log_mul hd0 hb0,
    add_sub_add_left_eq_sub,abs_mul]

/-- After integration the signed sum is precisely the excess above
the squarefree diagonal. -/
theorem signed_primitive_window_excess (N : ℕ) (T : ℝ) :
    ∑ q ∈ primitiveRatioPairs N,integratedRatio N T q =
      (∫ t in (1:ℝ)..T, ‖moebiusPoly N (linePoint t)‖^2) -
        (T-1)*(∑ n ∈ Icc 1 N,mobiusRealCoefficient n^2/n) := by
  rw [sharp_interval_spectrum,add_sub_cancel_left]
  refine sum_congr rfl fun q _ => congrArg (fun v : ℝ => atom N q.1 q.2*v) ?_
  simpa only [show (1:ℝ)+(T-1)=T by ring] using
    (integral_cos_lin_eq (Real.log q.1-Real.log q.2) 1 (T-1)).symm

private theorem diagonal_bound (N : ℕ) :
    ∑ n ∈ Icc 1 N,mobiusRealCoefficient n^2/n ≤ 2*(N:ℝ)^((1:ℝ)/2) := by
  have hm (n : ℕ) : |mobiusRealCoefficient n| ≤ 1 := by
    unfold mobiusRealCoefficient
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have row (n : ℕ) (hn : n ∈ Icc 1 N) :
      mobiusRealCoefficient n^2/n ≤ (n:ℝ)^(-(1/2:ℝ)) := by
    have hx : (1:ℝ) ≤ n := Nat.one_le_cast.mpr (mem_Icc.mp hn).1
    have hsq := pow_le_pow_left₀ (abs_nonneg _) (hm n) 2
    rw [sq_abs,one_pow] at hsq
    refine (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg n)).trans ?_
    rw [one_div,←Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hb := _root_.RHTower.sum_range_rpow_neg_le (1/2) (by norm_num) (by norm_num) N
  have h' : (∑ n ∈ Icc 1 N,mobiusRealCoefficient n^2/n) ≤
      ∑ i ∈ range N,((i:ℝ)+1)^(-(1/2:ℝ)) := by
    calc _ ≤ ∑ n ∈ Icc 1 N,(n:ℝ)^(-(1/2:ℝ)) := sum_le_sum row
         _ = _ := by rw [_root_.RHTower.sum_Icc_eq_sum_range_shift]; simp only [Nat.cast_succ]
  exact h'.trans (hb.trans_eq (by norm_num <;> ring))

private theorem window_le_small_root {a : ℝ} (ha : a ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Real.exp (a*(Real.log N)^((1:ℝ)/3)/108) ≤
      δ*(N:ℝ)^((1:ℝ)/2) := by
  obtain ⟨K,hK,hge⟩ := mertensSaving_ge (η:=1/4) (by norm_num)
  have hg := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (K/δ)
  filter_upwards [hg,eventually_ge_atTop 1] with N hn hN
  have hr : (1:ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have xp := zero_lt_one.trans_le hr
  let u := (Real.log N)^((1:ℝ)/3)/108
  have hu : 0 ≤ u := div_nonneg (Real.rpow_nonneg (Real.log_nonneg hr) _) (by norm_num)
  have hx : 0 < (N:ℝ)^((1:ℝ)/4) := Real.rpow_pos_of_pos xp _
  have hl := hge N hr
  change K⁻¹ * (N:ℝ)^(-(1/4:ℝ)) ≤ Real.exp (-u) at hl
  rw [Real.rpow_neg xp.le,Real.exp_neg,←mul_inv] at hl
  have hk := (one_div_le_one_div_of_le (by positivity : 0 < (K*(N:ℝ)^((1:ℝ)/4))⁻¹) hl)
  simp only [one_div,inv_inv] at hk
  have hδk := (div_le_iff₀ hδ).mp hn
  have hδk' := mul_le_mul_of_nonneg_right hδk hx.le
  calc Real.exp (a*(Real.log N)^((1:ℝ)/3)/108) = Real.exp (a*u) := by rw [mul_div_assoc]
       _ ≤ Real.exp u := Real.exp_le_exp.mpr (mul_le_of_le_one_left hu ha)
       _ ≤ K*(N:ℝ)^((1:ℝ)/4) := hk
       _ ≤ δ*((N:ℝ)^((1:ℝ)/4)*(N:ℝ)^((1:ℝ)/4)) := hδk'.trans_eq (by ring)
       _ = _ := by rw [←Real.rpow_add xp]; norm_num

/-- Across distinct reduced ratios the excess of either sign is an
arbitrarily small fraction of the total absolute mass. The estimate
holds simultaneously at every height in the indicated window. -/
theorem primitive_window_sign_balance {a : ℝ} (ha : a < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, 2 ≤ T →
      T ≤ Real.exp (a*(Real.log N)^((1:ℝ)/3)/108) →
      |∑ q ∈ primitiveRatioPairs N,integratedRatio N T q| ≤
        ε*(∑ q ∈ primitiveRatioPairs N,|integratedRatio N T q|) := by
  let δ := min (1/576:ℝ) (ε/331776)
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  have hd1 : δ ≤ 1/576 := min_le_left _ _
  have hd2 : δ ≤ ε/331776 := min_le_right _ _
  filter_upwards [eventually_ge_atTop 1,window_le_small_root ha.le δ hd,
    signed_moebius_sublinear_on_growing_windows ha (ε/165888) (by positivity)] with N hN hroot hmoment T hT ht
  have hr : (1:ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have xp := zero_lt_one.trans_le hr
  let R := (N:ℝ)^((1:ℝ)/2)
  have hrp : 0 ≤ R := (Real.rpow_pos_of_pos xp _).le
  have hr2 : R*R=(N:ℝ) := by
    dsimp only [R]; rw [←Real.rpow_add xp,show (1/2:ℝ)+1/2=1 by norm_num,Real.rpow_one]
  have hrn : R ≤ N := (Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1/2:ℝ)≤1)).trans_eq (Real.rpow_one _)
  have h1 : 1 ≤ T := by linarith only [hT]
  have htr : T ≤ δ*R := ht.trans hroot
  have hfit : 288*(T+1) ≤ N := by linarith only [hT,htr,mul_le_mul_of_nonneg_right hd1 hrp,hrn]
  have hvar := linear_unsigned_moebius_window_cost hT hfit
  have he : absoluteMoebiusOffDiagonal N T =
      ∑ q ∈ primitiveRatioPairs N,|integratedRatio N T q| :=
    absolute_primitive_spectrum N (fun x => cosInt x 1 (T-1))
  rw [he] at hvar
  have hp := mul_le_mul_of_nonneg_left hvar hε.le
  have hn := hmoment T h1 ht
  have diag := diagonal_bound N
  have diag0 : 0 ≤ ∑ n ∈ Icc 1 N,mobiusRealCoefficient n^2/n :=
    sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hcharge := mul_le_mul (sub_le_self T zero_le_one) diag diag0 (zero_le_one.trans h1)
  have hc := mul_le_mul_of_nonneg_right htr (show 0 ≤ 2*R by positivity)
  have hdN := mul_le_mul_of_nonneg_right hd2 (Nat.cast_nonneg (α:=ℝ) N)
  have hid : δ*R*(2*R)=2*δ*N := by rw [show δ*R*(2*R)=2*δ*(R*R) by ring,hr2]
  rw [hid] at hc
  have hi := intervalIntegral.integral_nonneg h1 (fun t _ => sq_nonneg ‖moebiusPoly N (linePoint t)‖)
  have hdn := mul_nonneg (sub_nonneg.mpr h1) diag0
  rw [signed_primitive_window_excess,abs_le]
  constructor <;> linarith only [hp,hn,hcharge,hc,hdN,hi,hdn]

#print axioms absolute_primitive_spectrum
#print axioms signed_primitive_window_excess
#print axioms primitive_window_sign_balance
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
