import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.FiniteWave
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.MovingEuler
import GaloisForLFunctions.RHTower.ChiRamanujanMovingCofactorLimit

/-! # The logarithmic critical window of the binary vacuum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window

open Filter Topology _root_.RHTower _root_.RHTower.BAGTrace

/-- Complex displacement from inverse temperature one, measured in units of 1/log N. -/
def windowTemperature (N : ℕ) (u : ℂ) : ℂ := 1-u/(Real.log N:ℂ)

def profile (u : ℂ) : ℂ := ∫ t in (0:ℝ)..1, criticalEulerProfile u t

theorem continuous_profile : Continuous profile := by
  have hd : Continuous (dslope Complex.exp 0) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    by_cases hz : w = 0
    · subst w
      exact continuousAt_dslope_same.mpr (Complex.differentiable_exp 0)
    · exact (continuousAt_dslope_of_ne hz).mpr Complex.continuous_exp.continuousAt
  have h : Continuous (Function.uncurry criticalEulerProfile) :=
    continuous_fst.mul (hd.comp (continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd)))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1

def criticalConstant : ℂ := (Real.exp (-Real.eulerMascheroniConstant):ℂ)*riemannZeta 2

theorem criticalConstant_ne : criticalConstant ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))

theorem windowTemperature_tendsto (u : ℂ) : Tendsto (fun N => windowTemperature N u) atTop (𝓝 1) := by
  have h := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp
    (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have H := (tendsto_const_nhds (x := (1:ℂ))).sub ((tendsto_const_nhds (x := u)).mul h)
  simpa only [windowTemperature,div_eq_mul_inv,Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero,mul_zero,sub_zero] using H

private theorem mertens_eq (N : ℕ) :
    (mertensPrimeProduct N:ℂ) = ∏ p ∈ N.primesLE, (1-(p:ℂ)⁻¹) := by
  have h : mertensPrimeProduct N = ∏ p ∈ N.primesLE, (1-(p:ℝ)⁻¹) := by
    rw [mertensPrimeProduct,← Finset.prod_filter]
    congr 1
    ext p
    simp [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primesLE]
  rw [h]
  push_cast
  rfl

private theorem nome_lt_one {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    ‖(p:ℂ)^(-s)‖ < 1 := by
  rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hp.pos)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr hs)

private theorem inverse_binary_factor {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    (1+(p:ℂ)^(-s))⁻¹ =
      (1-(p:ℂ)⁻¹)*((1-(p:ℂ)^(-s))/(1-(p:ℂ)⁻¹))*(1-(p:ℂ)^(-(2*s)))⁻¹ := by
  let q := (p:ℂ)^(-s)
  have hq : ‖q‖ < 1 := nome_lt_one hs hp
  have h₁ : 1-q ≠ 0 := by
    intro he
    rw [← sub_eq_zero.mp he,norm_one] at hq
    exact lt_irrefl _ hq
  have h₂ : 1+q ≠ 0 := by
    intro he
    have hn : q = -1 := by linear_combination he
    rw [hn,norm_neg,norm_one] at hq
    exact lt_irrefl _ hq
  have h₀ : 1-(p:ℂ)⁻¹ ≠ 0 := by
    have hr : 0 < 1-(p:ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
    simpa only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_inv,Complex.ofReal_natCast]
      using (Complex.ofReal_ne_zero.mpr hr.ne')
  have hsq : (p:ℂ)^(-(2*s)) = q^2 := by
    rw [show -(2*s) = (2:ℂ)*(-s) by ring]
    exact Complex.cpow_nat_mul _ 2 _
  change (1+q)⁻¹ = (1-(p:ℂ)⁻¹)*((1-q)/(1-(p:ℂ)⁻¹))*(1-(p:ℂ)^(-(2*s)))⁻¹
  rw [mul_comm (1-(p:ℂ)⁻¹) ((1-q)/(1-(p:ℂ)⁻¹)),div_mul_cancel₀ _ h₀,hsq,
    show 1-q^2 = (1-q)*(1+q) by ring]
  field_simp

/-- Exact separation of the singular Mertens product and the absolutely convergent doubled modes. -/
private theorem inverse_split (N : ℕ) (u : ℂ) (hs : 0 < (windowTemperature N u).re) :
    (partition N (windowTemperature N u))⁻¹ =
      (mertensPrimeProduct N:ℂ)*criticalMovingEulerRatio u N*
        ∏ p ∈ N.primesLE, (1-(p:ℂ)^(-(2*windowTemperature N u)))⁻¹ := by
  rw [partition,← Finset.prod_inv_distrib,mertens_eq,criticalMovingEulerRatio,
    ← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun _ hp => inverse_binary_factor hs (Nat.prime_of_mem_primesLE hp))

/-- Complex critical-window response of the reciprocal squarefree partition. -/
theorem inverse_partition_window (u : ℂ) :
    Tendsto (fun N : ℕ => (Real.log N:ℂ)/partition N (windowTemperature N u)) atTop
      (𝓝 (criticalConstant*Complex.exp (-profile u))) := by
  have ht := windowTemperature_tendsto u
  have hd : Tendsto (fun N => (2:ℂ)*windowTemperature N u) atTop (𝓝 2) := by
    simpa only [mul_one] using (tendsto_const_nhds (x := (2:ℂ))).mul ht
  have he := moving_euler_product (show 1 < (2:ℂ).re by norm_num) hd
  have hm := (Complex.continuous_ofReal.tendsto _).comp tendsto_mertensPrimeProduct_mul_log
  have H := (hm.mul (criticalMovingEulerRatio_tendsto u)).mul he
  rw [show (Real.exp (-Real.eulerMascheroniConstant):ℂ)*Complex.exp (-(∫ t in (0:ℝ)..1,criticalEulerProfile u t))*riemannZeta 2 =
    criticalConstant*Complex.exp (-profile u) by unfold criticalConstant profile; ring] at H
  apply H.congr'
  have hr := (Complex.continuous_re.tendsto _).comp ht
  filter_upwards [hr.eventually_const_lt (by norm_num : (0:ℝ) < (1:ℂ).re)] with N hN
  dsimp only [Function.comp_apply]
  rw [Complex.ofReal_mul,div_eq_mul_inv,inverse_split N u hN]
  ring

/-- The exponent at real displacement is the ordinary real integral, including its sign. -/
theorem negative_profile_real (a : ℝ) : -profile (-2*(a:ℂ)) =
    ((∫ t in (0:ℝ)..1, (1-Real.exp (-2*a*t))/t : ℝ):ℂ) := by
  rw [profile,← intervalIntegral.integral_neg,← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t ht
  rw [Set.uIoc_of_le zero_le_one] at ht
  have hn : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have he := criticalEulerProfile_mul (-2*(a:ℂ)) t
  push_cast
  apply (eq_div_iff hn).mpr
  rw [neg_mul,mul_comm (criticalEulerProfile _ _),he]
  ring_nf

/-- The probability of observing no marked prime in the physical binary wave. -/
theorem vacuum_critical_window (a : ℝ) :
    Tendsto (fun N : ℕ => Real.log N*vacuumProbability N (1/2+a/Real.log N)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant)*(riemannZeta 2).re*
        Real.exp (∫ t in (0:ℝ)..1, (1-Real.exp (-2*a*t))/t))) := by
  have H := inverse_partition_window (-2*(a:ℂ))
  rw [negative_profile_real,← Complex.ofReal_exp] at H
  have hr := (Complex.continuous_re.tendsto _).comp H
  simp only [criticalConstant,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero] at hr
  apply hr.congr
  intro N
  have ha : windowTemperature N (-2*(a:ℂ)) = 2*((1/2+a/Real.log N:ℝ):ℂ) := by
    unfold windowTemperature
    push_cast
    ring
  rw [Function.comp_apply,ha,div_eq_mul_inv,← vacuumProbability_eq,← Complex.ofReal_mul,Complex.ofReal_re]

#print axioms continuous_profile
#print axioms criticalConstant_ne
#print axioms windowTemperature_tendsto
#print axioms inverse_partition_window
#print axioms negative_profile_real
#print axioms vacuum_critical_window

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window
