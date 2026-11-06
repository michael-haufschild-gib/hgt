import GaloisForLFunctions.ArithmeticCompensationTheory.WoldResidualVinogradovKorobov
import GaloisForLFunctions.RHTower.PaperWoldDirectedCovarianceRH

/-!
# A uniform band of bounded theta endpoint energies

The literal power-weighted endpoint energy is uniformly bounded when its exponent
is at most `κ vkScale(N+2)/(96 log(N+2))`. Monotonicity of the VK scale divided by
the logarithm pays the weights at every earlier index. The remaining squared
residual has an integrable logarithmic tail, with one bound for the entire band.
-/

open Filter Topology Finset
open scoped BigOperators
open RHTower RHTower.Sieve
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

local notation "R" => xiHeatCassiniWoldNatResidualLogDiscrepancy

private theorem exists_weighted_residual_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T m : ℕ) (t : ℝ), 1 ≤ m → m ≤ T →
      0 ≤ t → t ≤ 1/2 → t ≤ vkKappa*vkScale T/(96*Real.log T) →
      (m:ℝ)^(2*t)*R m^2 ≤ C*Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log m)) := by
  obtain ⟨B, hB, hrate⟩ := exists_abs_woldResidual_vk_rate
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hrate.and
    ((tendsto_natCast_atTop_atTop :
      Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop).eventually
      ((eventually_vk_conditions one_pos 0).and
        (eventually_ge_atTop (Real.exp (Real.exp 1))))))
  let head := ∑ m ∈ range A,
    (m:ℝ)*R m^2*Real.exp ((1/24:ℝ)*Real.sqrt (Real.log m))
  have hhead : 0 ≤ head := sum_nonneg fun m _ => by positivity
  refine ⟨head+B^2, add_nonneg hhead (sq_nonneg _), ?_⟩
  intro T m t hm1 hmT ht0 ht1 hband
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  rcases lt_or_ge m A with hsmall | hlarge
  · have hp : (m:ℝ)^(2*t) ≤ m := by
      have h := Real.rpow_le_rpow_of_exponent_le hmR (show 2*t ≤ 1 by linarith)
      simpa only [Real.rpow_one] using h
    have hs : (m:ℝ)*R m^2*Real.exp ((1/24:ℝ)*Real.sqrt (Real.log m)) ≤ head :=
      single_le_sum (fun n (_ : n ∈ range A) =>
        show (0 : ℝ) ≤ (n:ℝ)*R n^2*Real.exp ((1/24:ℝ)*Real.sqrt (Real.log n))
          from by positivity) (mem_range.mpr hsmall)
    have hmul := mul_le_mul_of_nonneg_right hs
      (Real.exp_pos (-(1/24:ℝ)*Real.sqrt (Real.log m))).le
    have he : Real.exp ((1/24:ℝ)*Real.sqrt (Real.log m))*
        Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log m)) = 1 := by
      rw [← Real.exp_add, show (1/24:ℝ)*Real.sqrt (Real.log m) +
        -(1/24:ℝ)*Real.sqrt (Real.log m) = 0 by ring, Real.exp_zero]
    rw [mul_assoc, he, mul_one] at hmul
    exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans
      (hmul.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg B))
        (Real.exp_pos _).le))
  · obtain ⟨hr, hvk, hexp⟩ := hA m hlarge
    have hmT' : (m:ℝ) ≤ T := by exact_mod_cast hmT
    have hL0 : 0 < Real.log (m:ℝ) := by linarith only [hvk.2.1]
    have hκ := vkKappa_pos
    have hratio := vkScale_div_log_le hexp hmT'
    have hpaid : 2*t*Real.log m ≤ vkKappa*vkScale m/48 := by
      have hb : 2*t ≤ vkKappa*(vkScale T/Real.log T)/48 := by
        have he : vkKappa*vkScale T/(96*Real.log T) =
            vkKappa*(vkScale T/Real.log T)/96 := by ring
        rw [he] at hband
        linarith only [hband]
      calc 2*t*Real.log m ≤ (vkKappa*(vkScale T/Real.log T)/48)*Real.log m :=
          mul_le_mul_of_nonneg_right hb hL0.le
        _ ≤ (vkKappa*(vkScale m/Real.log m)/48)*Real.log m := by
          gcongr
        _ = vkKappa*vkScale m/48 := by field_simp
    have hs := hvk.2.2.2.2.1
    rw [log_vkHeight] at hs
    have hr2 : R m^2 ≤ (B*Real.exp (-(vkKappa*vkScale m/48)))^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hr 2
    have heq : (m:ℝ)^(2*t)*(B*Real.exp (-(vkKappa*vkScale m/48)))^2 =
        B^2*Real.exp (2*t*Real.log m-vkKappa*vkScale m/24) := by
      rw [Real.rpow_def_of_pos hm0, mul_pow, ← Real.exp_nat_mul]
      rw [show Real.exp (Real.log m*(2*t)) *
          (B^2*Real.exp ((2:ℕ)* (-(vkKappa*vkScale m/48)))) =
        B^2*(Real.exp (Real.log m*(2*t))*
          Real.exp ((2:ℕ)* (-(vkKappa*vkScale m/48)))) by ring, ← Real.exp_add]
      congr 2
      push_cast
      ring
    calc (m:ℝ)^(2*t)*R m^2
        ≤ (m:ℝ)^(2*t)*(B*Real.exp (-(vkKappa*vkScale m/48)))^2 :=
          mul_le_mul_of_nonneg_left hr2 (Real.rpow_pos_of_pos hm0 _).le
      _ = B^2*Real.exp (2*t*Real.log m-vkKappa*vkScale m/24) := heq
      _ ≤ B^2*Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log m)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hpaid, hs]))
          (sq_nonneg B)
      _ ≤ (head+B^2)*Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log m)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hhead) (Real.exp_pos _).le

private theorem weight_increment_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) (n : ℕ) :
    woldPowerWeight t (n+1)-woldPowerWeight t n ≤
      2*((n:ℝ)+2)^(2*t)/((n:ℝ)+2) := by
  rcases eq_or_lt_of_le ht0 with he | ht
  · rw [← he]
    simp only [woldPowerWeight, mul_zero, Real.rpow_zero, sub_self]
    positivity
  have h := woldPowerWeight_succ_sub_le ht ht1 n
  rw [Real.rpow_sub_one (by positivity : (n:ℝ)+1 ≠ 0)] at h
  have hp : ((n:ℝ)+1)^(2*t) ≤ ((n:ℝ)+2)^(2*t) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  calc _ ≤ 2*t*(((n:ℝ)+1)^(2*t)/((n:ℝ)+1)) := h
    _ ≤ ((n:ℝ)+1)^(2*t)/((n:ℝ)+1) :=
      mul_le_of_le_one_left (by positivity) (by linarith)
    _ ≤ ((n:ℝ)+2)^(2*t)/((n:ℝ)+1) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ ≤ 2*((n:ℝ)+2)^(2*t)/((n:ℝ)+2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n:ℝ)+2) (2*t))
        (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]

/-- One bound controls every literal theta endpoint energy in the shrinking VK band. -/
theorem exists_thetaEndpointEnergy_le_on_vinogradovKorobovBand :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (N : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1/2 →
      t ≤ vkKappa*vkScale (N+2)/(96*Real.log (N+2)) →
        endpointEnergy (woldPowerWeight t) woldShiftedResidual N ≤ E := by
  obtain ⟨C, hC, hpoint⟩ := exists_weighted_residual_bound
  have hs := GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
    (by norm_num : (0 : ℝ) < 1 / 24)
  have hshift : Summable (fun n:ℕ =>
      Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log ((n+2:ℕ):ℝ)))/((n+2:ℕ):ℝ)) := by
    simpa only [neg_mul] using (summable_nat_add_iff 2).mpr hs
  let S := ∑' n:ℕ, Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log ((n+2:ℕ):ℝ)))/((n+2:ℕ):ℝ)
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  refine ⟨2*R 1^2+2*C+4*C*S, by positivity, ?_⟩
  intro N t ht0 ht1 hband
  have hb := hpoint (N+2) (N+1) t (by omega) (by omega) ht0 ht1
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hband)
  have hboundary : woldPowerWeight t N*woldShiftedResidual N^2 ≤ C := by
    have he : Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log ((N+1:ℕ):ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (by norm_num) (Real.sqrt_nonneg _))
    have h := hb.trans (mul_le_of_le_one_right hC he)
    simpa only [woldPowerWeight, woldShiftedResidual, Nat.cast_add, Nat.cast_one] using h
  have hsum : ∑ n ∈ range N, (woldPowerWeight t (n+1)-woldPowerWeight t n)*
      woldShiftedResidual (n+1)^2 ≤ 2*C*S := by
    have hterm : ∀ n ∈ range N,
        (woldPowerWeight t (n+1)-woldPowerWeight t n)*woldShiftedResidual (n+1)^2 ≤
        2*C*(Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log ((n+2:ℕ):ℝ)))/((n+2:ℕ):ℝ)) := by
      intro n hn
      have hp := hpoint (N+2) (n+2) t (by omega)
        (by have := mem_range.mp hn; omega) ht0 ht1
        (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hband)
      have hd := mul_le_mul_of_nonneg_right (weight_increment_le ht0 ht1 n)
        (sq_nonneg (woldShiftedResidual (n+1)))
      simp only [woldShiftedResidual] at hd ⊢
      have hcast : ((n+2:ℕ):ℝ) = (n:ℝ)+2 := by push_cast; rfl
      rw [hcast] at hp ⊢
      calc _ ≤ (2*((n:ℝ)+2)^(2*t)/((n:ℝ)+2))*R (n+1+1)^2 := hd
        _ = (2/((n:ℝ)+2))*(((n:ℝ)+2)^(2*t)*R (n+2)^2) := by ring
        _ ≤ (2/((n:ℝ)+2))*(C*Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log ((n:ℝ)+2)))) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = 2*C*(Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log ((n:ℝ)+2)))/((n:ℝ)+2)) := by ring
    calc _ ≤ ∑ n ∈ range N,
        2*C*(Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log ((n+2:ℕ):ℝ)))/((n+2:ℕ):ℝ)) :=
          sum_le_sum hterm
      _ = 2*C*∑ n ∈ range N,
        Real.exp (-(1/24:ℝ)*Real.sqrt (Real.log ((n+2:ℕ):ℝ)))/((n+2:ℕ):ℝ) := by rw [mul_sum]
      _ ≤ 2*C*S := mul_le_mul_of_nonneg_left
        (hshift.sum_le_tsum _ fun _ _ => by positivity) (by positivity)
  have he := endpointEnergy_le (monotone_woldPowerWeight ht0)
    (by simp only [woldPowerWeight, Nat.cast_zero, zero_add, Real.one_rpow]; norm_num)
    (r:=woldShiftedResidual) N
  have hz : woldPowerWeight t 0 = 1 := by simp only [woldPowerWeight, Nat.cast_zero, zero_add, Real.one_rpow]
  rw [hz, mul_one] at he
  change endpointEnergy (woldPowerWeight t) woldShiftedResidual N ≤ _
  have hr0 : woldShiftedResidual 0 = R 1 := rfl
  rw [hr0] at he
  linarith only [he, hboundary, hsum]

#print axioms exists_thetaEndpointEnergy_le_on_vinogradovKorobovBand

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
