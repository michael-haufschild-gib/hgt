import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheTimeAveragedDyadicMaximumOfAPrimeTwist
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheShortRatioEnergyOfLongMoebiusPolynomials
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# One height exponent for almost every prime twist

At depth K the mean dyadic maximal cost for the critical Möbius
coefficients is O((K+1)³) per unit height. Markov's inequality with a
square-summable tail gives all polynomial lengths at once on a common
Haar-full set. Monotonicity of the time integral fills the dyadic gaps.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
open Filter Topology Finset MeasureTheory Complex
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.MultiscaleMollifiedZetaField (moebiusPoly)
open _root_.RHTower hiding linePoint
noncomputable section

private abbrev amplitude (n : ℕ) : ℂ := MoebiusGram.coeff n

private theorem energy_le (M : ℕ) :
    ∑ n ∈ Ioc 0 M, ‖amplitude n‖^2 ≤ 1+Real.log M := by
  have hs (n : ℕ) (hn : n ∈ Ioc 0 M) : ‖amplitude n‖^2 ≤ (n:ℝ)⁻¹ := by
    have hp : 0 < (n:ℝ) := Nat.cast_pos.mpr (mem_Ioc.mp hn).1
    have hm : |mobiusRealCoefficient n| ≤ 1 := by
      unfold mobiusRealCoefficient
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    simp only [amplitude,MoebiusGram.coeff,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,Real.sq_sqrt hp.le]
    rw [←one_div]
    exact div_le_div_of_nonneg_right ((sq_le_one_iff_abs_le_one _).mpr hm) hp.le
  refine (sum_le_sum hs).trans ?_
  have h := harmonic_le_one_add_log M
  have hi : Ioc 0 M = Icc 1 M := by
    ext n
    simp only [mem_Ioc,mem_Icc]
    omega
  simpa only [hi,_root_.RHTower.harmonic_eq_sum_Icc,one_div] using h

private abbrev times (T : ℝ) := volume.restrict (Set.Ioc (1:ℝ) T)

/-- The sharp critical-line Möbius polynomial with the prime twist x,
integrated in squared modulus from height one to T. -/
def criticalTwistedMoment (x : GaugeTorus) (N : ℕ) (T : ℝ) :=
  moment (times T) amplitude (Ioc 0 N) x

/-- At the trivial twist, the vertical Fourier section is exactly the
critical-line Möbius polynomial in squared modulus. -/
theorem power_at_trivial_twist (N : ℕ) (t : ℝ) :
    power (fun n => (MoebiusGram.coeff n:ℂ)) (Ioc 0 N) 0 t =
      ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2 := by
  let c := 2*Real.pi
  have hc : c ≠ 0 := (mul_pos (by norm_num) Real.pi_pos).ne'
  let w := t/(-c)
  have ht : -(2*Real.pi)*w=t := by
    dsimp only [w,c]
    field_simp [Real.pi_ne_zero] <;> ring
  have h := MoebiusGram.critical_moebius_logPoly N w
  rw [ht] at h
  rw [h]
  have hi : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  change ‖orthoSum _ _ (Ioc 0 N) 0‖^2=_
  apply congrArg (fun z : ℂ => ‖z‖^2)
  rw [orthoSum,_root_.RHTower.Sieve.logPoly,hi]
  apply sum_congr rfl
  intro n _
  have hphase : 2*Real.pi*(w*Real.log n) = -t*Real.log n := by
    change c*(t/(-c)*Real.log n) = _
    field_simp [hc]
    <;> ring
  simp only [twist_zero,mul_one,verticalCoeff,hphase]

/-- The trivial twist gives the original unmollified critical-line moment. -/
theorem critical_twisted_moment_zero (N : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    criticalTwistedMoment 0 N T =
      ∫ t in (1:ℝ)..T, ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2 := by
  rw [intervalIntegral.integral_of_le hT]
  exact integral_congr_ae (.of_forall (power_at_trivial_twist N))

private def depthCost (r k : ℕ) : ℝ := 2*((r:ℝ)+1)^3*((k:ℝ)+1)^3*(2:ℝ)^k

private def envelope (r k : ℕ) := maximalEnvelope (times ((2:ℝ)^k)) amplitude (r*k)

private theorem envelope_mean_le (r k : ℕ) : ∫ x, envelope r k x ∂gaugeHaar ≤ depthCost r k := by
  have hk : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hm := energy_le (2^(r*k+1))
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hm
  have hlog : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hdep : ((r*k+1:ℕ):ℝ) ≤ ((r:ℝ)+1)*((k:ℝ)+1) := by
    push_cast
    nlinarith only [Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) k]
  let L := ((r:ℝ)+1)*((k:ℝ)+1)
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_left (Nat.cast_nonneg r)) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have henergy : ∑ n ∈ Ioc 0 (2^(r*k+1)), ‖amplitude n‖^2 ≤ 2*L := by
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (r*k+1) (α:=ℝ))
    change ((r*k+1:ℕ):ℝ) ≤ L at hdep
    linarith only [hm,h,hdep,hL]
  rw [envelope,integral_maximalEnvelope,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hk]
  have hd : ((r*k:ℕ):ℝ)+1 ≤ L := by simpa only [Nat.cast_succ] using hdep
  calc
    _ ≤ L^2*(2:ℝ)^k*(2*L) := mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ (by positivity) hd 2) (sub_le_self _ zero_le_one)
        (sub_nonneg.mpr hk) (sq_nonneg L)) henergy (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = depthCost r k := by dsimp only [depthCost,L]; ring

private def bad (r k : ℕ) :=
  {x : GaugeTorus | depthCost r k*((k:ℝ)+1)^2 ≤ envelope r k x}

private theorem bad_mass (r k : ℕ) : gaugeHaar.real (bad r k) ≤ 1/((k:ℝ)+1)^2 := by
  have hn : ∀ x, 0 ≤ envelope r k x := fun x => mul_nonneg (by positivity)
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => moment_nonneg _ _ _ x)
  have h := mul_meas_ge_le_integral_of_nonneg (.of_forall hn)
    (integrable_maximalEnvelope (times ((2:ℝ)^k)) amplitude (r*k)) (depthCost r k*((k:ℝ)+1)^2)
  have hh : depthCost r k*((k:ℝ)+1)^2*gaugeHaar.real (bad r k) ≤ depthCost r k :=
    h.trans (envelope_mean_le r k)
  have hd : 0 < depthCost r k := by unfold depthCost; positivity
  rw [le_div_iff₀ (by positivity)]
  exact le_of_mul_le_mul_left (a:=depthCost r k) (by
    calc
      _ = depthCost r k*((k:ℝ)+1)^2*gaugeHaar.real (bad r k) := by ring
      _ ≤ _ := hh.trans_eq (mul_one _).symm) hd

private theorem ae_eventually_good (r : ℕ) :
    ∀ᵐ x ∂gaugeHaar, ∀ᶠ k : ℕ in atTop, envelope r k x ≤ depthCost r k*((k:ℝ)+1)^2 := by
  have hsum : Summable fun k : ℕ => 1/((k:ℝ)+1)^2 := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hfinite : ∑' k, gaugeHaar (bad r k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r:=∑' k : ℕ, 1/((k:ℝ)+1)^2)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum]
    apply ENNReal.tsum_le_tsum
    intro k
    rw [←ENNReal.ofReal_toReal (measure_ne_top gaugeHaar (bad r k)),←measureReal_def]
    exact ENNReal.ofReal_le_ofReal (bad_mass r k)
  filter_upwards [ae_eventually_notMem hfinite] with x hx
  filter_upwards [hx] with k hk
  exact (not_le.mp hk).le

/-- At almost every prime twist, eventually every section of length at most
T^r obeys the same T(log T)^5 height law, for every integer r simultaneously. -/
theorem ae_all_polynomial_lengths :
    ∀ᵐ x ∂gaugeHaar, ∀ r : ℕ, ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, (N:ℝ) ≤ T^r →
      criticalTwistedMoment x N T ≤ 128*((r:ℝ)+1)^3*T*(1+Real.log T)^5 := by
  have hall := ae_all_iff.mpr ae_eventually_good
  filter_upwards [hall] with x hx r
  obtain ⟨k₀,hk₀⟩ := eventually_atTop.mp (hx r)
  filter_upwards [eventually_ge_atTop ((2:ℝ)^k₀)] with T hT N hN
  have hT₁ : 1 ≤ T := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hT
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hT₁ (by norm_num : (1:ℝ) < 2)
  have hk : k₀ ≤ k+1 := by
    by_contra! h
    exact hhi.not_ge ((pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h.le).trans hT)
  have hmid : N < 2^(r*(k+1)+1) := by
    have hh := hN.trans (pow_le_pow_left₀ (zero_le_one.trans hT₁) hhi.le r)
    have hpow : ((2:ℝ)^(k+1))^r = (2:ℝ)^(r*(k+1)) := by rw [←pow_mul,Nat.mul_comm]
    rw [hpow] at hh
    have : (N:ℝ) < (2:ℝ)^(r*(k+1)+1) := by rw [pow_succ]; linarith only [hh,pow_pos (by norm_num : (0:ℝ)<2) (r*(k+1))]
    exact_mod_cast this
  have hmono : moment (times T) amplitude (Ioc 0 N) x ≤ moment (times ((2:ℝ)^(k+1))) amplitude (Ioc 0 N) x :=
    setIntegral_mono_set (integrable_power_at _ _ _ _) (.of_forall fun _ => sq_nonneg _)
      (.of_forall fun _ h => ⟨h.1,h.2.trans hhi.le⟩)
  have hB := (hmono.trans (moment_le_maximalEnvelope _ _ hmid x)).trans (hk₀ (k+1) hk)
  have hl := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) k) hlo
  rw [Real.log_pow] at hl
  have hlg : (k:ℝ)+2 ≤ 2*(1+Real.log T) := by
    have hhalf : (1/2:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
    linarith only [hl,mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg k (α:=ℝ))]
  have ht : (2:ℝ)^(k+1) ≤ 2*T := by rw [pow_succ,mul_comm]; exact mul_le_mul_of_nonneg_left hlo (by norm_num)
  refine hB.trans ?_
  simp only [depthCost,Nat.cast_succ]
  calc
    _ = 2*((r:ℝ)+1)^3*((2:ℝ)^(k+1))*((k:ℝ)+2)^5 := by ring
    _ ≤ 2*((r:ℝ)+1)^3*(2*T)*(2*(1+Real.log T))^5 := mul_le_mul
      (mul_le_mul_of_nonneg_left ht (by positivity)) (pow_le_pow_left₀ (by positivity) hlg 5)
      (by positivity) (by positivity)
    _ = _ := by ring

/-- The height exponent can be chosen arbitrarily close to one,
simultaneously for every polynomial length, at Haar-almost every twist. -/
theorem ae_common_height_exponent :
    ∀ᵐ x ∂gaugeHaar, ∀ ε : ℝ, 0 < ε → ∀ r : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, (N:ℝ) ≤ T^r →
        criticalTwistedMoment x N T ≤ C*T^(1+ε) := by
  filter_upwards [ae_all_polynomial_lengths] with x hx ε hε r
  let c := 1+5/ε
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨128*((r:ℝ)+1)^3*c^5,by positivity,?_⟩
  filter_upwards [hx r,eventually_ge_atTop (1:ℝ)] with T ht hT N hN
  let δ := ε/5
  have hδ : 0 < δ := div_pos hε (by norm_num)
  have hpow := Real.one_le_rpow hT hδ.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hT) hδ
  have he : T^δ/δ=(5/ε)*T^δ := by dsimp only [δ]; field_simp [hε.ne']
  rw [he] at hl
  have hb : 1+Real.log T ≤ c*T^δ := by
    dsimp only [c]
    rw [add_mul,one_mul]
    exact add_le_add hpow hl
  have hs := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_nonneg hT)) hb 5
  have hpow5 : (T^δ)^5=T^ε := by
    rw [←Real.rpow_natCast (T^δ),←Real.rpow_mul (zero_le_one.trans hT)]
    congr 1
    norm_num [δ] <;> ring
  rw [mul_pow,hpow5] at hs
  refine (ht N hN).trans ((mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 128*((r:ℝ)+1)^3*T)).trans_eq ?_)
  rw [Real.rpow_add (zero_lt_one.trans_le hT),Real.rpow_one]
  ring

#print axioms ae_common_height_exponent
#print axioms ae_all_polynomial_lengths
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
