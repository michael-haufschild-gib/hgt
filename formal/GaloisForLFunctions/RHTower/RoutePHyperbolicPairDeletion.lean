import GaloisForLFunctions.RHTower.RoutePFixedHyperbolicStrips
import GaloisForLFunctions.RHTower.RoutePUnsignedProfilePowerSaving
import GaloisForLFunctions.RHTower.RoutePMobiusHyperbolaCancellation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

/-!
# Critical deletion of the full hyperbolic signed-channel sector

The actual clipped unsigned profile has a uniform positive-power remainder.
Symmetry turns its quadratic error into centered quotient-prefix rows. Each
fixed row vanishes, and a summable inverse-power bound controls all rows at
once. Tannery's theorem and the literal Möbius convolution limit therefore
pay the entire d*e<=M sector at M^2 normalization. The exact partition leaves
every complementary pair, including its diagonal and common-divisor classes.
No estimate for that remaining sector or either native RP square debt is assumed.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private def profileMean : ℝ :=
  Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4
private def channelProfile (M d : ℕ) : ℝ :=
  divisorUnsignedDilationChannel M d/Real.sqrt M
private def centeredPairRow (M e : ℕ) : ℝ :=
  (ArithmeticFunction.moebius e:ℝ)*(channelProfile M e+profileMean)*
    ((∑ d ∈ Icc 1 (M/e), (ArithmeticFunction.moebius d:ℝ)*
      (channelProfile M d-profileMean))/(M:ℝ))

private lemma profile_abs_le (M d : ℕ) : |channelProfile M d| ≤ (3/5:ℝ) := by
  by_cases hM : M=0
  · norm_num [channelProfile,hM]
  have hm : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hs := Real.sqrt_pos.mpr hm
  rw [channelProfile,abs_of_nonneg (div_nonneg
    (divisorUnsignedDilationChannel_nonneg M d) hs.le),div_le_iff₀ hs]
  exact divisorUnsignedDilationChannel_le_three_fifths_sqrt M d

private lemma moebius_abs_le (d : ℕ) : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)

/-- Uniform profile error on every positive product pair, including small quotients. -/
theorem routeP_unsigned_profile_product_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M d e : ℕ, 0<d → 0<e → d*e≤M →
      |divisorUnsignedDilationChannel M d/Real.sqrt M-
        (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4)|
        ≤ C/(e:ℝ)^((1:ℝ)/40) := by
  change ∃ C : ℝ, 0 ≤ C ∧ ∀ M d e : ℕ, 0<d → 0<e → d*e≤M →
    |channelProfile M d-profileMean| ≤ C/(e:ℝ)^((1:ℝ)/40)
  obtain ⟨C,hC,T,hT,hbound⟩ := routeP_unsigned_channels_uniform_power_saving
  let B : ℝ := 3/5+|profileMean|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let D : ℝ := C+B*(T:ℝ)^((1:ℝ)/40)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro M d e hd he hde
  have heq : e ≤ M/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hde)
  have hep : (0:ℝ)<e := by exact_mod_cast he
  have het : 0<(e:ℝ)^((1:ℝ)/40) := Real.rpow_pos_of_pos hep _
  by_cases ht : T≤M/d
  · have h := hbound M d hd ht
    change |channelProfile M d-profileMean| ≤ _ at h
    apply h.trans
    apply (div_le_div_of_nonneg_left hC het
      (Real.rpow_le_rpow hep.le (by exact_mod_cast heq) (by norm_num))).trans
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg T) _))) het.le
  · have heT : e ≤ T := by omega
    have hsmall : |channelProfile M d-profileMean| ≤ B :=
      (abs_sub _ _).trans (add_le_add (profile_abs_le M d) (le_refl |profileMean|))
    apply hsmall.trans
    rw [le_div_iff₀ het]
    calc
      _ ≤ B*(T:ℝ)^((1:ℝ)/40) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hep.le (by exact_mod_cast heT) (by norm_num)) hB
      _ ≤ D := by dsimp [D]; linarith only [hC]

private lemma moebius_Icc_eq (N : ℕ) :
    (∑ d ∈ Icc 1 N, (ArithmeticFunction.moebius d:ℝ)) = Sieve.mertensM N := by
  rw [Sieve.mertensM,sum_range_succ',← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
  simp [add_comm]

private lemma quotient_moebius_tendsto (e : ℕ) :
    Tendsto (fun M : ℕ => (∑ d ∈ Icc 1 (M/e), (ArithmeticFunction.moebius d:ℝ))/(M:ℝ))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ Sieve.tendsto_mertensSup_div
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hm,moebius_Icc_eq]
  exact div_le_div_of_nonneg_right
    (Sieve.abs_mertensM_le_mertensSup (Nat.div_le_self M e)) hm.le

private lemma centered_prefix_identity (M e : ℕ) :
    (∑ d ∈ Icc 1 (M/e), (ArithmeticFunction.moebius d:ℝ)*
      (channelProfile M d-profileMean))/(M:ℝ) =
    (∑ d ∈ Icc 1 (M/e), mobiusDivisorDilationChannel M d)/((M:ℝ)*Real.sqrt M)-
      profileMean*((∑ d ∈ Icc 1 (M/e), (ArithmeticFunction.moebius d:ℝ))/(M:ℝ)) := by
  rw [sum_div, sum_div, sum_div, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned]
  dsimp [channelProfile]
  ring

private lemma centered_prefix_tendsto (e : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ d ∈ Icc 1 (M/e), (ArithmeticFunction.moebius d:ℝ)*
        (channelProfile M d-profileMean))/(M:ℝ)) atTop (𝓝 0) := by
  cases e with
  | zero => simp
  | succ e =>
    have h := (routeP_fixed_quotient_prefix_tendsto e).sub
      ((quotient_moebius_tendsto (e+1)).const_mul profileMean)
    simpa only [mul_zero,sub_zero,← centered_prefix_identity] using h

private lemma row_coefficient_abs_le (M e : ℕ) :
    |(ArithmeticFunction.moebius e:ℝ)*(channelProfile M e+profileMean)| ≤
      3/5+|profileMean| := by
  rw [abs_mul]
  calc
    _ ≤ 1*|channelProfile M e+profileMean| :=
      mul_le_mul_of_nonneg_right (moebius_abs_le e) (abs_nonneg _)
    _ ≤ _ := by
      simpa only [one_mul] using (abs_add_le _ _).trans
        (add_le_add (profile_abs_le M e) (le_refl |profileMean|))

private lemma centered_row_tendsto (e : ℕ) :
    Tendsto (fun M : ℕ => centeredPairRow M e) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa only [norm_zero,mul_zero] using
      (centered_prefix_tendsto e).norm.const_mul (3/5+|profileMean|))
  apply Eventually.of_forall
  intro M
  rw [centeredPairRow,norm_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (row_coefficient_abs_le M e)
    (norm_nonneg ((∑ d ∈ Icc 1 (M/e), (ArithmeticFunction.moebius d:ℝ)*
      (channelProfile M d-profileMean))/(M:ℝ)))

private lemma centered_row_bound {C : ℝ} (hC : 0 ≤ C)
    (herror : ∀ M d e : ℕ, 0<d → 0<e → d*e≤M →
      |channelProfile M d-profileMean| ≤ C/(e:ℝ)^((1:ℝ)/40))
    (M e : ℕ) (hM : 0<M) (he : 0<e) :
    |centeredPairRow M e| ≤ (3/5+|profileMean|)*C/(e:ℝ)^((41:ℝ)/40) := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hep : (0:ℝ)<e := by exact_mod_cast he
  have het : 0<(e:ℝ)^((1:ℝ)/40) := Real.rpow_pos_of_pos hep _
  have hprefix : |∑ d ∈ Icc 1 (M/e), (ArithmeticFunction.moebius d:ℝ)*
      (channelProfile M d-profileMean)| ≤ (M/e:ℕ)*(C/(e:ℝ)^((1:ℝ)/40)) := by
    calc
      _ ≤ ∑ d ∈ Icc 1 (M/e), |(ArithmeticFunction.moebius d:ℝ)*
        (channelProfile M d-profileMean)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Icc 1 (M/e), C/(e:ℝ)^((1:ℝ)/40) := by
        apply sum_le_sum
        intro d hd
        rw [abs_mul]
        calc
          _ ≤ 1*|channelProfile M d-profileMean| :=
            mul_le_mul_of_nonneg_right (moebius_abs_le d) (abs_nonneg _)
          _ ≤ _ := by
            simpa only [one_mul] using herror M d e (mem_Icc.mp hd).1 he
              ((Nat.le_div_iff_mul_le he).mp (mem_Icc.mp hd).2)
      _ = _ := by simp
  have hcount : ((M/e:ℕ):ℝ) ≤ (M:ℝ)/(e:ℝ) := by
    apply (le_div_iff₀ hep).mpr
    exact_mod_cast Nat.div_mul_le_self M e
  have hpow : (e:ℝ)^((41:ℝ)/40) = (e:ℝ)*(e:ℝ)^((1:ℝ)/40) := by
    rw [show (41:ℝ)/40=1+(1:ℝ)/40 by norm_num,Real.rpow_add hep,Real.rpow_one]
  rw [centeredPairRow,abs_mul,abs_div,abs_of_pos hm]
  calc
    _ ≤ (3/5+|profileMean|)*
        (((M/e:ℕ):ℝ)*(C/(e:ℝ)^((1:ℝ)/40))/(M:ℝ)) :=
      mul_le_mul (row_coefficient_abs_le M e)
        (div_le_div_of_nonneg_right hprefix hm.le) (by positivity) (by positivity)
    _ ≤ (3/5+|profileMean|)*
        (((M:ℝ)/(e:ℝ))*(C/(e:ℝ)^((1:ℝ)/40))/(M:ℝ)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcount (div_nonneg hC het.le)) hm.le) (by positivity)
    _ = _ := by rw [hpow]; field_simp

private lemma centered_rows_tsum_tendsto :
    Tendsto (fun M : ℕ => ∑' e : ℕ, centeredPairRow M e) atTop (𝓝 0) := by
  obtain ⟨C,hC,herror⟩ := routeP_unsigned_profile_product_error
  have hsum : Summable (fun e : ℕ => (3/5+|profileMean|)*C/(e:ℝ)^((41:ℝ)/40)) := by
    simpa only [one_div,mul_assoc,div_eq_mul_inv,one_mul] using
      (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1:ℝ)<41/40)).mul_left
        ((3/5+|profileMean|)*C)
  have h := tendsto_tsum_of_dominated_convergence hsum centered_row_tendsto
    (show ∀ᶠ M : ℕ in atTop, ∀ e : ℕ, ‖centeredPairRow M e‖ ≤
      (3/5+|profileMean|)*C/(e:ℝ)^((41:ℝ)/40) from by
      filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM e
      cases e with
      | zero => simp [centeredPairRow]
      | succ e =>
        rw [Real.norm_eq_abs]
        exact centered_row_bound hC herror M (e+1) (by omega) (by omega))
  simpa only [tsum_zero] using h

private lemma centered_rows_tsum_eq_sum (M : ℕ) :
    (∑' e : ℕ, centeredPairRow M e) = ∑ e ∈ Icc 1 M, centeredPairRow M e := by
  apply tsum_eq_sum
  intro e he
  by_cases he0 : e=0
  · simp [centeredPairRow,he0]
  · have hMe : M<e := by simp only [mem_Icc] at he; omega
    simp [centeredPairRow,Nat.div_eq_of_lt hMe]

private lemma hyperbolic_profile_identity (M : ℕ) (u v : ℕ → ℝ) (c : ℝ) :
    (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
      if d*e≤M then u e*(v e+c)*(u d*(v d-c)) else 0) =
    (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
      if d*e≤M then (u d*v d)*(u e*v e) else 0)-
      c^2*(∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if d*e≤M then u d*u e else 0) := by
  let F := fun d e => if d*e≤M then u e*(v e+c)*(u d*(v d-c)) else 0
  have hpoint (d e : ℕ) : F d e+F e d =
      2*(if d*e≤M then (u d*v d)*(u e*v e) else 0)-
      2*c^2*(if d*e≤M then u d*u e else 0) := by
    by_cases hde : d*e≤M
    · simp only [F,hde,show e*d≤M by simpa [Nat.mul_comm] using hde,if_true]
      ring
    · simp [F,hde,Nat.mul_comm]
  have hsum := congrArg (fun f : ℕ → ℕ → ℝ => ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, f d e)
    (funext fun d => funext fun e => hpoint d e)
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum] at hsum
  have hswap : (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, F e d) =
      ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, F d e := sum_comm
  rw [hswap] at hsum
  change (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, F d e) = _
  linarith only [hsum]

private lemma centered_rows_identity (M : ℕ) (hM : 0<M) :
    (∑' e : ℕ, centeredPairRow M e) =
      (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if d*e≤M then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0)/
          (M:ℝ)^2-profileMean^2*(routePMobiusHyperbolaCoefficient M/(M:ℝ)) := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hs := Real.sqrt_pos.mpr hm
  have hsq := Real.sq_sqrt hm.le
  have hrow (e : ℕ) (he : e ∈ Icc 1 M) :
      (∑ d ∈ Icc 1 M, if d*e≤M then
        (ArithmeticFunction.moebius e:ℝ)*(channelProfile M e+profileMean)*
          ((ArithmeticFunction.moebius d:ℝ)*(channelProfile M d-profileMean)) else 0) =
      (ArithmeticFunction.moebius e:ℝ)*(channelProfile M e+profileMean)*
        (∑ d ∈ Icc 1 (M/e), (ArithmeticFunction.moebius d:ℝ)*
          (channelProfile M d-profileMean)) := by
    rw [← sum_filter]
    have hset : {d ∈ Icc 1 M | d*e≤M} = Icc 1 (M/e) := by
      ext d
      simp only [mem_filter,mem_Icc]
      have hd : d≤M/e ↔ d*e≤M := Nat.le_div_iff_mul_le (mem_Icc.mp he).1
      have hh := Nat.div_le_self M e
      omega
    rw [hset,mul_sum]
  have hprofile (d e : ℕ) :
      ((ArithmeticFunction.moebius d:ℝ)*channelProfile M d)*
        ((ArithmeticFunction.moebius e:ℝ)*channelProfile M e) =
      mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e/(M:ℝ) := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      mobiusDivisorDilationChannel_eq_moebius_unsigned]
    dsimp [channelProfile]
    calc
      _ = ((ArithmeticFunction.moebius d:ℝ)*divisorUnsignedDilationChannel M d)*
        ((ArithmeticFunction.moebius e:ℝ)*divisorUnsignedDilationChannel M e)/(Real.sqrt M)^2 := by ring
      _ = _ := by rw [hsq]
  have hquadratic :
      (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if d*e≤M then ((ArithmeticFunction.moebius d:ℝ)*channelProfile M d)*
          ((ArithmeticFunction.moebius e:ℝ)*channelProfile M e) else 0) =
      (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if d*e≤M then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0)/(M:ℝ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro d _
    rw [sum_div]
    apply sum_congr rfl
    intro e _
    by_cases hde : d*e≤M <;> simp only [hde,if_true,if_false,zero_div,hprofile]
  rw [centered_rows_tsum_eq_sum]
  have hrows : (∑ e ∈ Icc 1 M, centeredPairRow M e) =
      (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, if d*e≤M then
        (ArithmeticFunction.moebius e:ℝ)*(channelProfile M e+profileMean)*
          ((ArithmeticFunction.moebius d:ℝ)*(channelProfile M d-profileMean)) else 0)/(M:ℝ) := by
    rw [sum_comm, sum_div]
    apply sum_congr rfl
    intro e he
    rw [hrow e he]
    dsimp [centeredPairRow]
    ring
  rw [hrows,hyperbolic_profile_identity,hquadratic]
  change _ = _-profileMean^2*((∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
    if d*e≤M then (ArithmeticFunction.moebius d:ℝ)*(ArithmeticFunction.moebius e:ℝ) else 0)/(M:ℝ))
  ring

/-- The entire literal hyperbolic signed-channel sector vanishes at critical
pair normalization. Every common-divisor pair and the diagonal are retained. -/
theorem routeP_hyperbolic_pair_sector_tendsto_zero :
    Tendsto (fun M : ℕ =>
      (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if d*e≤M then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0)/
          (M:ℝ)^2) atTop (𝓝 0) := by
  have h := centered_rows_tsum_tendsto.add
    (routeP_mobius_hyperbola_div_tendsto_zero.const_mul (profileMean^2))
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  rw [centered_rows_identity M (by omega)]
  ring

/-- Exact partition of the complete signed-channel square, including every
common-divisor pair and both parts of the diagonal. -/
theorem routeP_hyperbolic_pair_partition (M : ℕ) :
    (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)^2 =
    (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
      if d*e≤M then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0)+
    (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
      if M<d*e then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0) := by
  rw [pow_two,sum_mul]
  simp_rw [mul_sum]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases hde : d*e≤M
  · rw [if_pos hde,if_neg (by omega),add_zero]
  · rw [if_neg hde,if_pos (by omega),zero_add]

/-- After critical normalization, deleting the hyperbolic sector leaves the
literal complementary pairs, with no discarded diagonal or gcd class. -/
theorem routeP_complementary_pair_remainder_tendsto_zero :
    Tendsto (fun M : ℕ =>
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)^2/(M:ℝ)^2-
      (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if M<d*e then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0)/
          (M:ℝ)^2) atTop (𝓝 0) := by
  apply routeP_hyperbolic_pair_sector_tendsto_zero.congr
  intro M
  rw [routeP_hyperbolic_pair_partition,add_div]
  ring

end RHTower
