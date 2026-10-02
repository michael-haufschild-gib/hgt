import GaloisForLFunctions.RHTower.RoutePTerminalModularPowerSaving

/-!
# Uniform power remainder for the actual unsigned divisor profile

The exact square-birth, terminal modular, and smooth-channel decomposition
transfers the terminal power saving to the complete unsigned unit profile.
Exact square-root interpolation retains the clipped endpoint and makes the
remainder uniform over all positive dilation indices on one quotient tail.
This pays the profile-rate obligation in the Route RP hyperbolic pair-sector
candidate; it does not itself estimate that signed sector.
-/

noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower

private lemma terminal_boundary_bound (M : ℕ) (hM : 1 ≤ M) (T : ℝ) :
    |halfOrderAbelStep 0 M*T/Real.sqrt M| ≤ |T/(M:ℝ)| := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hs : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  let w := halfOrderAbelStep 0 M
  have hw : 0 ≤ w := halfOrderAbelStep_nonneg _ _
  have hs2 := Real.sq_sqrt hm.le
  have hsu := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) (M+1))
  have hc : 2*Real.sqrt M*w+w^2 = 1 := by
    dsimp [w,halfOrderAbelStep]
    push_cast at hsu ⊢
    simp only [zero_add]
    nlinarith only [hs2,hsu]
  have hb : w*Real.sqrt M ≤ 1 := by nlinarith only [hc,sq_nonneg w]
  have he : w*T/Real.sqrt M = (w*Real.sqrt M)*(T/(M:ℝ)) := by
    field_simp
    nlinarith only [congrArg (fun x : ℝ => w*T*x) hs2]
  change |w*T/Real.sqrt M| ≤ _
  rw [he,abs_mul,abs_of_nonneg (mul_nonneg hw hs.le)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (abs_nonneg (T/(M:ℝ)))

private lemma centered_profile_bound (M : ℕ) (hM : 1 ≤ M) :
    |centeredDivisorHyperbolaAbel M/Real.sqrt M+1/24| ≤
      ((5/48:ℝ)*((harmonic (Nat.sqrt M):ℚ):ℝ)+1/24)/Real.sqrt M+
      |(∑ d ∈ Icc 1 (Nat.sqrt M),
        (centeredModularMeanMagnitude d+centeredModularPrimitive d M))/(M:ℝ)| := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hs : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  let T : ℝ := ∑ d ∈ Icc 1 (Nat.sqrt M),
    (centeredModularMeanMagnitude d+centeredModularPrimitive d M)
  have hc := div_le_div_of_nonneg_right (centeredDivisorHyperbolaAbel_mean_error M) hs.le
  have habsdiv (x : ℝ) : |x|/Real.sqrt M = |x/Real.sqrt M| := by
    rw [abs_div,abs_of_pos hs]
  rw [habsdiv] at hc
  change |(centeredDivisorHyperbolaAbel M+(Nat.sqrt M:ℝ)/24-
    halfOrderAbelStep 0 M*T)/Real.sqrt M| ≤ _ at hc
  have hc' : |centeredDivisorHyperbolaAbel M/Real.sqrt M+(Nat.sqrt M:ℝ)/Real.sqrt M/24-
      halfOrderAbelStep 0 M*T/Real.sqrt M| ≤
      ((5/48:ℝ)*((harmonic (Nat.sqrt M):ℚ):ℝ))/Real.sqrt M := by
    convert hc using 1
    congr 1
    ring
  have hn : 0 ≤ 1-(Nat.sqrt M:ℝ)/Real.sqrt M := by
    rw [sub_nonneg,div_le_one hs]
    exact Real.nat_sqrt_le_real_sqrt
  have hn' : 1-(Nat.sqrt M:ℝ)/Real.sqrt M ≤ 1/Real.sqrt M := by
    rw [le_div_iff₀ hs]
    have h := Real.real_sqrt_le_nat_sqrt_succ (a:=M)
    have he : (1-(Nat.sqrt M:ℝ)/Real.sqrt M)*Real.sqrt M =
        Real.sqrt M-(Nat.sqrt M:ℝ) := by field_simp
    rw [he]
    linarith only [h]
  have ht := abs_le.mp (terminal_boundary_bound M hM T)
  have he := abs_le.mp hc'
  apply abs_le.mpr
  change -(_+|T/(M:ℝ)|) ≤ _ ∧ _ ≤ _+|T/(M:ℝ)|
  have hsinv : 0 ≤ (Real.sqrt (M:ℝ))⁻¹ := by positivity
  ring_nf at ht he hn hn' ⊢
  constructor <;> linarith only [ht.1,ht.2,he.1,he.2,hn,hn',hsinv]

/-- Full unit profile estimate: square births, signed terminal primitive, and
the smooth part all remain in the exact channel. -/
theorem routeP_unit_profile_remainder_bound (M : ℕ) (hM : 1 ≤ M) :
    |divisorUnsignedDilationChannel M 1/Real.sqrt M-
      (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4)| ≤
    (9*Real.log ((M:ℝ)+1)+25+|divisorHyperbolaSmoothMean|+
      (5/24:ℝ)*((harmonic (Nat.sqrt M):ℚ):ℝ)+1/12)/Real.sqrt M+
      2*|(∑ d ∈ Icc 1 (Nat.sqrt M),
        (centeredModularMeanMagnitude d+centeredModularPrimitive d M))/(M:ℝ)| := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hs : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  have hc := centered_profile_bound M hM
  have hb := div_le_div_of_nonneg_right (divisorHyperbolaSmoothAbel_mean_error M) hs.le
  have habsdiv (x : ℝ) : |x|/Real.sqrt M = |x/Real.sqrt M| := by
    rw [abs_div,abs_of_pos hs]
  rw [habsdiv] at hb
  have hb' : |divisorHyperbolaSmoothAbel M/Real.sqrt M-divisorHyperbolaSmoothMean| ≤
      (9*Real.log ((M:ℝ)+1)+25+|divisorHyperbolaSmoothMean|)/Real.sqrt M := by
    convert hb using 1
    congr 1
    field_simp
  have hid := mobiusDivisorDilationChannel_one_eq_hyperbola M
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at hid
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at hid
  rw [hid]
  have hcI := abs_le.mp hc
  have hbI := abs_le.mp hb'
  unfold divisorHyperbolaSmoothMean at hbI ⊢
  apply abs_le.mpr
  ring_nf at hcI hbI ⊢
  constructor <;> linarith only [hcI.1,hcI.2,hbI.1,hbI.2]

/-- The complete unsigned unit profile approaches its exact coefficient with
a positive-power remainder, without a cancellation hypothesis. -/
theorem routeP_unit_profile_power_saving :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ M : ℕ in atTop,
      |divisorUnsignedDilationChannel M 1/Real.sqrt M-
        (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4)| ≤
        C/(M:ℝ)^((1:ℝ)/40) := by
  have hlog : ∀ᶠ x : ℝ in atTop, |Real.log x| ≤ x^((19:ℝ)/40) := by
    filter_upwards [(isLittleO_log_rpow_atTop (r:=(19:ℝ)/40) (by norm_num)).bound
      (by norm_num : (0:ℝ)<1), eventually_ge_atTop (0:ℝ)] with x hx hx0
    simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx0 _)] using hx
  refine ⟨108+|divisorHyperbolaSmoothMean|,by positivity,?_⟩
  filter_upwards [routeP_terminal_modular_mean_power_saving,
    tendsto_natCast_atTop_atTop.eventually hlog, eventually_ge_atTop (1:ℕ)] with M hT hlog hM
  have hm1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hm : (0:ℝ) < M := by positivity
  have hs : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  have ht : 0 < (M:ℝ)^((1:ℝ)/40) := Real.rpow_pos_of_pos hm _
  have hp1 : 1 ≤ (M:ℝ)^((19:ℝ)/40) := Real.one_le_rpow hm1 (by norm_num)
  have hlog0 : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg hm1
  have hlog' : Real.log ((M:ℝ)+1) ≤ Real.log M+1 := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<M+1)
      (show (M:ℝ)+1 ≤ 2*(M:ℝ) by linarith only [hm1])
    rw [Real.log_mul (by norm_num) hm.ne'] at h
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h2
    linarith only [h,h2]
  have hn : (0:ℝ) < Nat.sqrt M := by
    exact_mod_cast (Nat.le_sqrt.mpr (by simpa using hM) : 1 ≤ Nat.sqrt M)
  have hH : ((harmonic (Nat.sqrt M):ℚ):ℝ) ≤ 1+Real.log M := by
    have h := Real.log_le_log hn
      (show (Nat.sqrt M:ℝ) ≤ M by exact_mod_cast Nat.sqrt_le_self M)
    linarith only [h,harmonic_le_one_add_log (Nat.sqrt M)]
  have hnum : 9*Real.log ((M:ℝ)+1)+25+|divisorHyperbolaSmoothMean|+
      (5/24:ℝ)*((harmonic (Nat.sqrt M):ℚ):ℝ)+1/12 ≤
      (50+|divisorHyperbolaSmoothMean|)*(M:ℝ)^((19:ℝ)/40) := by
    have hconst := mul_le_mul_of_nonneg_left hp1
      (show 0 ≤ 40+|divisorHyperbolaSmoothMean| by positivity)
    rw [abs_of_nonneg hlog0] at hlog
    nlinarith only [hconst,hlog,hlog',hH,hlog0,hp1]
  have hprod : (M:ℝ)^((19:ℝ)/40)*(M:ℝ)^((1:ℝ)/40) = Real.sqrt M := by
    rw [← Real.rpow_add hm,Real.sqrt_eq_rpow]
    norm_num
  have herr : (9*Real.log ((M:ℝ)+1)+25+|divisorHyperbolaSmoothMean|+
      (5/24:ℝ)*((harmonic (Nat.sqrt M):ℚ):ℝ)+1/12)/Real.sqrt M ≤
      (50+|divisorHyperbolaSmoothMean|)/(M:ℝ)^((1:ℝ)/40) := by
    rw [div_le_div_iff₀ hs ht]
    calc
      _ ≤ ((50+|divisorHyperbolaSmoothMean|)*(M:ℝ)^((19:ℝ)/40))*
          (M:ℝ)^((1:ℝ)/40) := mul_le_mul_of_nonneg_right hnum ht.le
      _ = _ := by rw [mul_assoc,hprod]
  apply (routeP_unit_profile_remainder_bound M hM).trans
  calc
    _ ≤ (50+|divisorHyperbolaSmoothMean|)/(M:ℝ)^((1:ℝ)/40)+
        2*(29/(M:ℝ)^((1:ℝ)/40)) := add_le_add herr
          (mul_le_mul_of_nonneg_left hT (by norm_num))
    _ = _ := by ring

/-- The power remainder is uniform in every positive dilation index once its
quotient is on one common tail. Exact clipping retains both adjacent cells. -/
theorem routeP_unsigned_channels_uniform_power_saving :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ M d : ℕ, 0 < d → T ≤ M/d →
      |divisorUnsignedDilationChannel M d/Real.sqrt M-
        (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4)| ≤
        C / ((M/d:ℕ):ℝ)^((1:ℝ)/40) := by
  obtain ⟨C,hC,hbound⟩ := routeP_unit_profile_power_saving
  obtain ⟨T,hT⟩ := eventually_atTop.mp hbound
  let c := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4
  refine ⟨C,hC,max T 1,le_max_right _ _,?_⟩
  intro M d hd hMd
  have hN : T ≤ M/d := (le_max_left _ _).trans hMd
  have hN1 : 1 ≤ M/d := (le_max_right _ _).trans hMd
  have hM : 1 ≤ M := hN1.trans (Nat.div_le_self M d)
  have hs : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
  let ε : ℝ := C / ((M/d:ℕ):ℝ)^((1:ℝ)/40)
  have hunit (N : ℕ) (hNT : T ≤ N) (hNN : M/d ≤ N) :
      (c-ε)*Real.sqrt N ≤ divisorUnsignedDilationChannel N 1 ∧
      divisorUnsignedDilationChannel N 1 ≤ (c+ε)*Real.sqrt N := by
    have hn1 : 1 ≤ N := hN1.trans hNN
    have hn : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
    have he : C/(N:ℝ)^((1:ℝ)/40) ≤ ε := by
      apply div_le_div_of_nonneg_left hC
      · exact Real.rpow_pos_of_pos (by exact_mod_cast hN1) _
      · exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hNN) (by norm_num)
    have h := (hT N hNT).trans he
    change |divisorUnsignedDilationChannel N 1/Real.sqrt N-c| ≤ ε at h
    obtain ⟨hl,hu⟩ := abs_le.mp h
    constructor
    · apply (le_div_iff₀ hn).mp
      linarith only [hl]
    · apply (div_le_iff₀ hn).mp
      linarith only [hu]
  have hA := hunit (M/d) hN le_rfl
  have hB := hunit (M/d+1) (by omega) (by omega)
  have hw0 := divisorPrimeClipWeight_nonneg M d hd
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M d := by
    have h := divisorPrimeClipWeight_lt_one M d hd
    linarith only [h]
  have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd
  simp only [Nat.mul_one] at hc
  have hclock := divisorPrimeClipWeight_mul_step M d hd
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hclock
  have hclock' : Real.sqrt (d:ℝ)*
      ((1-divisorPrimeClipWeight M d)*Real.sqrt (M/d:ℕ)+
        divisorPrimeClipWeight M d*Real.sqrt (M/d+1:ℕ)) = Real.sqrt M := by
    push_cast
    nlinarith only [hclock]
  have hl := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hA.1 hw1) (mul_le_mul_of_nonneg_left hB.1 hw0))
    (Real.sqrt_nonneg (d:ℝ))
  have hu := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hA.2 hw1) (mul_le_mul_of_nonneg_left hB.2 hw0))
    (Real.sqrt_nonneg (d:ℝ))
  have hLc := congrArg (fun x : ℝ => (c-ε)*x) hclock'
  have hUc := congrArg (fun x : ℝ => (c+ε)*x) hclock'
  have hscaled : (c-ε)*Real.sqrt M ≤ divisorUnsignedDilationChannel M d ∧
      divisorUnsignedDilationChannel M d ≤ (c+ε)*Real.sqrt M := by
    rw [hc]
    constructor <;> nlinarith only [hl,hu,hLc,hUc]
  apply abs_le.mpr
  have hl' := (le_div_iff₀ hs).mpr hscaled.1
  have hu' := (div_le_iff₀ hs).mpr hscaled.2
  change -ε ≤ _-c ∧ _-c ≤ ε
  constructor <;> linarith only [hl',hu']

end RHTower
