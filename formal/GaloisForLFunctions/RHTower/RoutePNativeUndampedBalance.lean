import GaloisForLFunctions.RHTower.RoutePNativeNegativeCoprimeWork
import GaloisForLFunctions.RHTower.MobiusDivisorUniformLocalRegularity
import GaloisForLFunctions.RHTower.DeningerMobiusHarmonicZero
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Absolute admission of the complete native balance at zero damping

Finite Abel summation combines the actual Möbius coefficients before
integration. Unit-head regularity pays each dilation difference against
the unconditional inverse-square Mertens sum. This admits the complete
balance, not its endpoint square or signed coprime work separately.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower
namespace NativeUndampedBalance

private abbrev W := routePCoprimeSquareWeight
private abbrev U := divisorContinuousUnitHead

private theorem unit_le_sqrt (x : ℝ) : U x ≤ Real.sqrt x := by
  have h := divisorContinuousUnitHead_le_sqrt x
  nlinarith [Real.sqrt_nonneg x]

private theorem weight_le_one (y : ℝ) : W y ≤ 1 :=
  (routePCoprimeSquareWeight_le y).trans (by norm_num)

private theorem dilation_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y => W (r*y)) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_mul_left_iff W 0 hr).mpr
  simpa only [mul_zero] using integrableOn_routePCoprimeSquareWeight

private theorem weight_dilation_bound {r y : ℝ} (hr : 1 ≤ r) (hy : 0 < y) :
    |W y - W (r*y)| ≤ (r-1)*(1+24/Real.sqrt y) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hry : 0 < r*y := mul_pos hr0 hy
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hiy : (r*y)⁻¹ ≤ y⁻¹ :=
    inv_le_inv₀ hry hy |>.2 (by nlinarith)
  have hu : U y⁻¹ ≤ 1/Real.sqrt y := by
    simpa only [Real.sqrt_inv, one_div] using unit_le_sqrt y⁻¹
  have hv : U (r*y)⁻¹ ≤ 1/Real.sqrt y := by
    apply (unit_le_sqrt _).trans
    simpa only [Real.sqrt_inv, one_div] using Real.sqrt_le_sqrt hiy
  have hu0 := divisorContinuousUnitHead_nonneg y⁻¹
  have hv0 := divisorContinuousUnitHead_nonneg (r*y)⁻¹
  have hsum : |U y⁻¹+U (r*y)⁻¹| ≤ 2/Real.sqrt y := by
    rw [abs_of_nonneg (add_nonneg hu0 hv0)]
    exact (add_le_add hu hv).trans_eq (by ring)
  have hinv : |y⁻¹-(r*y)⁻¹| ≤ (r-1)/y := by
    rw [abs_of_nonneg (sub_nonneg.mpr hiy)]
    apply (le_div_iff₀ hy).mpr
    field_simp
    nlinarith [sq_nonneg (r-1)]
  have hdiff : |U y⁻¹-U (r*y)⁻¹| ≤ 12*((r-1)/y) :=
    (abs_divisorContinuousUnitHead_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left hinv (by norm_num))
  have hv2 : y*U (r*y)⁻¹^2 ≤ 1 := by
    have hw := weight_le_one (r*y)
    change (r*y)*U (r*y)⁻¹^2 ≤ 1 at hw
    nlinarith [mul_nonneg hy.le (sq_nonneg (U (r*y)⁻¹))]
  have he : W y-W (r*y) =
      y*(U y⁻¹-U (r*y)⁻¹)*(U y⁻¹+U (r*y)⁻¹)-(r-1)*y*U (r*y)⁻¹^2 := by
    change y*U y⁻¹^2-(r*y)*U (r*y)⁻¹^2 = _
    ring
  rw [he]
  calc
    _ ≤ |y*(U y⁻¹-U (r*y)⁻¹)*(U y⁻¹+U (r*y)⁻¹)|+
        |(r-1)*y*U (r*y)⁻¹^2| := abs_sub _ _
    _ = y * |U y⁻¹-U (r*y)⁻¹| * |U y⁻¹+U (r*y)⁻¹| +
        (r-1)*(y*U (r*y)⁻¹^2) := by
      rw [abs_mul, abs_mul, abs_of_pos hy,
        abs_of_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hr) hy.le) (sq_nonneg _))]
      ring
    _ ≤ y*(12*((r-1)/y))*(2/Real.sqrt y)+(r-1)*1 := by
      gcongr
    _ = _ := by field_simp; ring

private theorem inv_sqrt_eq_rpow {y : ℝ} (hy : 0 < y) :
    1/Real.sqrt y = y^(-(1/2:ℝ)) := by
  rw [Real.rpow_neg hy.le, Real.sqrt_eq_rpow, one_div]

private theorem dilation_difference_mass {r : ℝ} (hr : 1 ≤ r) :
    (∫ y in Ioi (0 : ℝ), |W y-W (r*y)|) ≤ 49*(r-1) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hcut : (∫ y in Ioi (0 : ℝ), |W y-W (r*y)|) =
      ∫ y in Ioc (0 : ℝ) 1, |W y-W (r*y)| := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro y hy
    have hy1 : 1 ≤ y := le_of_not_gt (fun h => hy.2 ⟨hy.1,h.le⟩)
    have hry1 : 1 ≤ r*y := by nlinarith
    simp [routePCoprimeSquareWeight_eq_zero_of_one_le hy1,
      routePCoprimeSquareWeight_eq_zero_of_one_le hry1]
  have hp : IntervalIntegrable (fun y : ℝ => y^(-(1/2:ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hm := ((intervalIntegrable_const (c := (1:ℝ))).add (hp.const_mul 24)).const_mul (r-1)
  have hi : IntegrableOn (fun y => |W y-W (r*y)|) (Ioi 0) :=
    (integrableOn_routePCoprimeSquareWeight.sub (dilation_integrable hr0)).norm
  rw [hcut]
  calc
    _ ≤ ∫ y in Ioc (0 : ℝ) 1, (r-1)*(1+24*y^(-(1/2:ℝ))) := by
      apply integral_mono_ae (hi.mono_set Ioc_subset_Ioi_self) hm.1
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      calc
        _ ≤ (r-1)*(1+24/Real.sqrt y) := weight_dilation_bound hr hy.1
        _ = _ := by rw [← inv_sqrt_eq_rpow hy.1]; ring
    _ = 49*(r-1) := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const (hp.const_mul 24),
        intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ)))]
      norm_num
      ring

private theorem adjacent_mass {n : ℕ} (hn : 0 < n) :
    (∫ y in Ioi (0 : ℝ), |W ((n:ℝ)*y)-W (((n:ℝ)+1)*y)|) ≤ 49/(n:ℝ)^2 := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let r : ℝ := ((n:ℝ)+1)/n
  have hr : 1≤r := (le_div_iff₀ hn0).mpr (by linarith)
  have he (y : ℝ) : r*((n:ℝ)*y)=((n:ℝ)+1)*y := by dsimp [r]; field_simp
  have hi := integral_comp_mul_left_Ioi (fun y => |W y-W (r*y)|) 0 hn0
  simp only [he, mul_zero, smul_eq_mul] at hi
  rw [hi]
  calc
    _ ≤ (n:ℝ)⁻¹*(49*(r-1)) := mul_le_mul_of_nonneg_left
      (dilation_difference_mass hr) (inv_nonneg.mpr hn0.le)
    _ = _ := by dsimp [r]; field_simp; ring


private def atom (n : ℕ) (y : ℝ) : ℂ :=
  (Sieve.mertensM n : ℂ) * ((W ((n:ℝ)*y)-W (((n:ℝ)+1)*y) : ℝ) : ℂ)

private theorem atom_zero : atom 0 = 0 := by
  funext y
  simp [atom, Sieve.mertensM]

private theorem atom_integrable (n : ℕ) : IntegrableOn (atom n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [atom_zero]; exact integrable_zero ℝ ℂ _
  · have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    exact ((dilation_integrable hn0).sub
      (dilation_integrable (show 0<(n:ℝ)+1 by positivity))).ofReal.const_mul _

private theorem atom_mass (n : ℕ) :
    (∫ y in Ioi (0 : ℝ), ‖atom n y‖) ≤ 49*(|Sieve.mertensM n|/(n:ℝ)^2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [atom_zero]
  · simp only [atom, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_const_mul]
    calc
      _ ≤ |Sieve.mertensM n| * (49/(n:ℝ)^2) :=
        mul_le_mul_of_nonneg_left (adjacent_mass hn) (abs_nonneg _)
      _ = _ := by ring

private theorem atom_masses_summable :
    Summable (fun n : ℕ => ∫ y in Ioi (0 : ℝ), ‖atom n y‖) :=
  (deningerMertensM_invSq_summable.mul_left 49).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _) atom_mass

private theorem weight_late {y : ℝ} (hy : 0<y) {n : ℕ} (hn : ⌊y⁻¹⌋₊<n) :
    W ((n:ℝ)*y)=0 :=
  routePCoprimeSquareWeight_eq_zero_of_one_le
    (((inv_lt_iff_one_lt_mul₀ hy).mp (Nat.lt_of_floor_lt hn)).le)

private theorem atom_summable {y : ℝ} (hy : 0<y) : Summable (fun n => atom n y) := by
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.range (⌊y⁻¹⌋₊+1)) ?_).summable
  intro n hn
  have hn' : ⌊y⁻¹⌋₊<n := by simp only [Finset.mem_range, not_lt] at hn; omega
  have hn1 : ⌊y⁻¹⌋₊<n+1 := by omega
  have hz0 := weight_late hy hn'
  have hz1 := weight_late hy hn1
  simp only [Nat.cast_add, Nat.cast_one] at hz1
  simp [atom, hz0, hz1]

private theorem source_terms_summable {y : ℝ} (hy : 0<y) :
    Summable (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)*(W ((n:ℝ)*y) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.range (⌊y⁻¹⌋₊+1)) ?_).summable
  intro n hn
  have hn' : ⌊y⁻¹⌋₊<n := by simp only [Finset.mem_range, not_lt] at hn; omega
  simp [weight_late hy hn']

private theorem finite_abel (N : ℕ) (y : ℝ) :
    (∑ n ∈ Finset.range N, atom n y) =
      (∑ n ∈ Finset.range (N+1), ((ArithmeticFunction.moebius n : ℤ) : ℂ)*
        (W ((n:ℝ)*y) : ℂ))-(W ((N:ℝ)*y) : ℂ)*(Sieve.mertensM N : ℂ) := by
  classical
  let F : ℕ → ℂ := fun n => (W ((n:ℝ)*y) : ℂ)
  let G : ℕ → ℂ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  have hsum (n : ℕ) : (∑ j ∈ Finset.range (n+1), G j)=(Sieve.mertensM n : ℂ) := by
    simp only [Sieve.mertensM, G, Complex.ofReal_sum, Complex.ofReal_intCast]
  have hparts := Finset.sum_range_by_parts F G (N+1)
  simp only [Nat.add_sub_cancel, smul_eq_mul, hsum] at hparts
  have hd : (∑ n ∈ Finset.range N, (F (n+1)-F n)*(Sieve.mertensM n : ℂ)) =
      -(∑ n ∈ Finset.range N, atom n y) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [F, atom, Nat.cast_add, Nat.cast_one, Complex.ofReal_sub]
    ring
  have hm : (∑ n ∈ Finset.range (N+1), F n*G n)=
      ∑ n ∈ Finset.range (N+1), ((ArithmeticFunction.moebius n : ℤ) : ℂ)*
        (W ((n:ℝ)*y) : ℂ) :=
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [hd,hm] at hparts
  dsimp only [F] at hparts
  linear_combination -hparts

private theorem source_eq_abel {y : ℝ} (hy : 0<y) :
    routePCoprimeSquareSource y = ∑' n, atom n y := by
  have hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N+1),
      ((ArithmeticFunction.moebius n : ℤ) : ℂ)*(W ((n:ℝ)*y) : ℂ))
      atTop (𝓝 (routePCoprimeSquareSource y)) :=
    (source_terms_summable hy).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun N : ℕ => (W ((N:ℝ)*y) : ℂ)*(Sieve.mertensM N : ℂ))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop ⌊y⁻¹⌋₊] with N hN
    simp [weight_late hy hN]
  have hlim := hpartial.sub hzero
  simp only [sub_zero] at hlim
  have hlim' : Tendsto (fun N => ∑ n ∈ Finset.range N, atom n y)
      atTop (𝓝 (routePCoprimeSquareSource y)) :=
    hlim.congr fun N => (finite_abel N y).symm
  exact tendsto_nhds_unique hlim' (atom_summable hy).hasSum.tendsto_sum_nat

private theorem atom_integral (n : ℕ) :
    (∫ y in Ioi (0 : ℝ), atom n y) =
      ((Sieve.mertensM n/((n:ℝ)*((n:ℝ)+1)) : ℝ) : ℂ)*
        (routePCoprimeSquareMass : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [atom_zero, Sieve.mertensM]
  · have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hn1 : 0<(n:ℝ)+1 := by positivity
    have hnC : (n:ℂ)≠0 := by exact_mod_cast hn0.ne'
    have hn1C : (n:ℂ)+1≠0 := by exact_mod_cast hn1.ne'
    change (∫ y in Ioi (0:ℝ), (Sieve.mertensM n : ℂ)*
      ((W ((n:ℝ)*y)-W (((n:ℝ)+1)*y) : ℝ) : ℂ)) = _
    rw [integral_const_mul, integral_complex_ofReal,
      integral_sub (dilation_integrable hn0) (dilation_integrable hn1),
      integral_comp_mul_left_Ioi W 0 hn0, integral_comp_mul_left_Ioi W 0 hn1]
    simp only [mul_zero, smul_eq_mul]
    change (Sieve.mertensM n : ℂ)*
      (((n:ℝ)⁻¹*routePCoprimeSquareMass-((n:ℝ)+1)⁻¹*routePCoprimeSquareMass : ℝ) : ℂ)=_
    push_cast
    field_simp [hnC, hn1C]
    ring

end NativeUndampedBalance

/-- The complete native square source is absolutely admitted at its undamped boundary. -/
theorem integrableOn_routePCoprimeSquareSource :
    IntegrableOn routePCoprimeSquareSource (Ioi 0) := by
  have hi := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    NativeUndampedBalance.atom_integrable NativeUndampedBalance.atom_masses_summable
  exact IntegrableOn.congr_fun hi
    (fun y hy => (NativeUndampedBalance.source_eq_abel hy).symm) measurableSet_Ioi

/-- Signed Abel assembly preserves the exact zero Mobius harmonic mass. -/
theorem integral_routePCoprimeSquareSource_eq_zero :
    (∫ y in Ioi (0 : ℝ), routePCoprimeSquareSource y)=0 := by
  have he : (∫ y in Ioi (0 : ℝ), routePCoprimeSquareSource y)=
      ∫ y in Ioi (0 : ℝ), ∑' n, NativeUndampedBalance.atom n y :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => NativeUndampedBalance.source_eq_abel hy
  rw [he, ← integral_tsum_of_summable_integral_norm
    NativeUndampedBalance.atom_integrable NativeUndampedBalance.atom_masses_summable]
  simp_rw [NativeUndampedBalance.atom_integral]
  rw [tsum_mul_right]
  have hc := Complex.ofRealCLM.map_tsum deningerMertensHarmonic_summable
  change ((∑' n : ℕ, Sieve.mertensM n/((n:ℝ)*((n:ℝ)+1)) : ℝ) : ℂ)=
    ∑' n : ℕ, ((Sieve.mertensM n/((n:ℝ)*((n:ℝ)+1)) : ℝ) : ℂ) at hc
  rw [← hc]
  change (deningerHarmonicLimit : ℂ)*(routePCoprimeSquareMass : ℂ)=0
  rw [deningerHarmonicLimit_eq_zero, Complex.ofReal_zero, zero_mul]

namespace NativeUndampedBalance

private def balance (t : ℝ) : ℝ :=
  routePNativeCriticalProfile t^2+routePNativeCriticalCoprimeWork t

private theorem source_zero {y : ℝ} (hy : 1≤y) : routePCoprimeSquareSource y=0 := by
  rw [routePCoprimeSquareSource_eq_sum (zero_lt_one.trans_le hy)]
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hny : 1≤(n:ℝ)*y := by nlinarith
  simp [routePCoprimeSquareWeight_eq_zero_of_one_le hny]

private theorem balance_admitted_zero :
    IntegrableOn balance (Ioi 0) ∧ (∫ t in Ioi (0:ℝ), balance t)=0 := by
  let f : ℝ → ℝ := fun y => (routePCoprimeSquareSource y).re
  have hf : IntegrableOn f (Ioi 0) := integrableOn_routePCoprimeSquareSource.re
  have hf0 : (∫ y in Ioi (0:ℝ), f y)=0 := by
    have h := integral_re integrableOn_routePCoprimeSquareSource
    simpa only [RCLike.re_eq_complex_re, integral_routePCoprimeSquareSource_eq_zero,
      Complex.zero_re] using h
  have himg : (fun t : ℝ => Real.exp (-t)) '' Ioi 0=Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      have ht : 0<t := ht
      exact ⟨Real.exp_pos _, by simpa using Real.exp_lt_exp.mpr (show -t<0 by linarith)⟩
    · rintro ⟨hy0,hy1⟩
      exact ⟨-Real.log y,neg_pos.mpr (Real.log_neg hy0 hy1),by simp [Real.exp_log hy0]⟩
  have hd (t : ℝ) (_ : t ∈ Ioi (0:ℝ)) :
      HasDerivWithinAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) (Ioi 0) t := by
    simpa using ((hasDerivAt_id t).neg.exp).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    fun _ _ _ _ h => neg_injective (Real.exp_injective h)
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj f
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj f
  rw [himg] at hi hj
  simp only [abs_neg,abs_of_pos (Real.exp_pos _),smul_eq_mul] at hi hj
  have hcut : (∫ y in Ioi (0:ℝ), f y)=(∫ y in Ioo (0:ℝ) 1, f y) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
    intro y hy
    have hy1 : 1≤y := le_of_not_gt (fun h => hy.2 ⟨hy.1,h⟩)
    simp [f,source_zero hy1]
  have he (t : ℝ) (ht : t∈Ioi (0:ℝ)) : Real.exp (-t)*f (Real.exp (-t))=balance t := by
    have ht0 : 0≤t := le_of_lt ht
    change Real.exp (-t)*(routePCoprimeSquareSource (Real.exp (-t))).re=balance t
    rw [routePCoprimeSquareSource_eq_nativeSquare_add_cross ht0,Complex.ofReal_re,
      balance,routePNativeCriticalProfile,routePNativeCriticalCoprimeWork]
    ring
  refine ⟨IntegrableOn.congr_fun (hi.mp (hf.mono_set Ioo_subset_Ioi_self)) he measurableSet_Ioi,?_⟩
  calc
    _ = ∫ t in Ioi (0:ℝ), Real.exp (-t)*f (Real.exp (-t)) :=
      (setIntegral_congr_fun measurableSet_Ioi he).symm
    _ = ∫ y in Ioo (0:ℝ) 1, f y := hj.symm
    _ = 0 := hcut.symm.trans hf0

private theorem partial_balance {T : ℝ} (hT : 0≤T) :
    (∫ t in (0:ℝ)..T, routePNativeCriticalCoprimeWork t)+
      (∫ t in (0:ℝ)..T, routePNativeCriticalProfile t^2)=∫ t in (0:ℝ)..T, balance t := by
  have hE : IntervalIntegrable (fun t => routePNativeCriticalProfile t^2) volume 0 T :=
    ⟨integrableOn_routePNativeCriticalProfile_sq_Ioc T,by simp [Ioc_eq_empty_of_le hT]⟩
  have hB : IntervalIntegrable balance volume 0 T :=
    ⟨balance_admitted_zero.1.mono_set Ioc_subset_Ioi_self,by simp [Ioc_eq_empty_of_le hT]⟩
  have hC : IntervalIntegrable routePNativeCriticalCoprimeWork volume 0 T := by
    convert hB.sub hE using 1
    ext t
    simp [balance]
  rw [add_comm,← intervalIntegral.integral_add hE hC]
  rfl

private theorem balance_partial_limit :
    Tendsto (fun T : ℝ => ∫ t in (0:ℝ)..T, balance t) atTop (𝓝 0) := by
  simpa only [balance_admitted_zero.2,id_eq] using
    intervalIntegral_tendsto_integral_Ioi 0 balance_admitted_zero.1 tendsto_id

end NativeUndampedBalance

/-- The complete signed balance has zero total mass at zero damping. -/
theorem routePNativeCriticalBalance_integrable_zero :
    IntegrableOn (fun t => routePNativeCriticalProfile t^2+routePNativeCriticalCoprimeWork t)
      (Ioi 0) ∧
    (∫ t in Ioi (0:ℝ), routePNativeCriticalProfile t^2+routePNativeCriticalCoprimeWork t)=0 :=
  NativeUndampedBalance.balance_admitted_zero

/-- All positive native coprime work is paid already at zero damping. -/
theorem integrableOn_routePNativePositiveCoprimeWork :
    IntegrableOn (fun t => max (routePNativeCriticalCoprimeWork t) 0) (Ioi 0) := by
  have hE : AEStronglyMeasurable (fun t => routePNativeCriticalProfile t^2)
      (volume.restrict (Ioi 0)) :=
    (((Real.measurable_exp.comp measurable_id.neg).mul
      (measurable_mobiusDivisorFullHead.comp Real.measurable_exp)).pow_const 2).aestronglyMeasurable
  have hC : AEStronglyMeasurable routePNativeCriticalCoprimeWork
      (volume.restrict (Ioi 0)) := by
    have h := NativeUndampedBalance.balance_admitted_zero.1.aestronglyMeasurable.sub hE
    apply h.congr
    filter_upwards with t
    change routePNativeCriticalProfile t^2+routePNativeCriticalCoprimeWork t-
      routePNativeCriticalProfile t^2=routePNativeCriticalCoprimeWork t
    ring
  have hB : IntegrableOn (fun t => |NativeUndampedBalance.balance t|) (Ioi 0) :=
    NativeUndampedBalance.balance_admitted_zero.1.norm
  apply hB.mono' (hC.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  apply max_le
  · exact (le_add_of_nonneg_left (sq_nonneg (routePNativeCriticalProfile t))).trans
      (le_abs_self (NativeUndampedBalance.balance t))
  · exact abs_nonneg _

/-- Complete native cross work compensates square energy up to a remainder tending to zero. -/
theorem routePNativeSignedCoprimeWork_compensated_limit :
    Tendsto (fun T : ℝ =>
      (∫ t in (0:ℝ)..T, routePNativeCriticalCoprimeWork t)+
      (∫ t in (0:ℝ)..T, routePNativeCriticalProfile t^2)) atTop (𝓝 0) := by
  apply NativeUndampedBalance.balance_partial_limit.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  exact (NativeUndampedBalance.partial_balance hT).symm

/-- The full signed native coprime-work integral tends to minus infinity. -/
theorem routePNativeSignedCoprimeWork_tendsto_atBot :
    Tendsto (fun T : ℝ => ∫ t in (0:ℝ)..T, routePNativeCriticalCoprimeWork t) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro b
  obtain ⟨V,hV,hbig⟩ := routePNativeCritical_square_energy_cofinally_unbounded (1-b) 0
  have hevent := NativeUndampedBalance.balance_partial_limit.eventually
    (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨T,hT⟩ := eventually_atTop.mp hevent
  refine ⟨max V T,fun x hx => ?_⟩
  have hxV : V≤x := (le_max_left V T).trans hx
  have hxT : T≤x := (le_max_right V T).trans hx
  have hx0 : 0≤x := hV.trans hxV
  have hmono : (∫ t in (0:ℝ)..V, routePNativeCriticalProfile t^2) ≤
      ∫ t in (0:ℝ)..x, routePNativeCriticalProfile t^2 := by
    rw [intervalIntegral.integral_of_le hV,intervalIntegral.integral_of_le hx0]
    apply setIntegral_mono_set (integrableOn_routePNativeCriticalProfile_sq_Ioc x)
      (Eventually.of_forall fun t => sq_nonneg _) ?_
    exact Eventually.of_forall fun t ht => ⟨ht.1,ht.2.trans hxV⟩
  have hp := NativeUndampedBalance.partial_balance hx0
  have hb : (∫ t in (0:ℝ)..x, NativeUndampedBalance.balance t)<1 := hT x hxT
  linarith

end RHTower
