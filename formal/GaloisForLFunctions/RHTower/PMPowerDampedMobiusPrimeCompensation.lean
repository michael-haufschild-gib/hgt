import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeEnergyBalance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Leading compensation of the actual signed prime current

The complete physical source energy is negligible at the scale of the
proved negative mixed current. The exact common-horizon balance therefore
forces leading positive compensation for every sufficiently small positive
damping parameter. The bounded signed remainder required for canonical
L2 admission is not claimed.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private def pmqe_density (ε x : ℝ) : ℝ :=
  ‖pmPowerDampedFermiSource ε (1/x)‖^2/x^2

private theorem pmqe_reciprocal (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    pmPowerDampedFermiTruncatedEnergy ε N = ∫ x in Ioo (0 : ℝ) (N : ℝ), pmqe_density ε x ∧
      IntegrableOn (pmqe_density ε) (Ioo (0 : ℝ) (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have himage : (fun x : ℝ => x⁻¹) '' Ioo (0 : ℝ) (N : ℝ) = Ioi (1/(N : ℝ)) := by
    rw [image_inv_eq_inv,inv_Ioo_0_left hN0,one_div]
  have hd : ∀ x ∈ Ioo (0 : ℝ) (N : ℝ),
      HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(x^2)⁻¹) (Ioo (0 : ℝ) (N : ℝ)) x :=
    fun x hx => (hasDerivAt_inv hx.1.ne').hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => x⁻¹) (Ioo (0 : ℝ) (N : ℝ)) := inv_injective.injOn
  have heq : (fun x : ℝ => |-(x^2)⁻¹| • ‖pmPowerDampedFermiSource ε x⁻¹‖^2) =
      pmqe_density ε := by
    funext x
    simp only [pmqe_density,one_div,abs_neg,abs_inv,abs_of_nonneg (sq_nonneg x),smul_eq_mul]
    ring
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun t => ‖pmPowerDampedFermiSource ε t‖^2)
  rw [himage,heq] at hi
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun t => ‖pmPowerDampedFermiSource ε t‖^2)
  rw [himage,heq] at hj
  exact ⟨hi,hj.mp (integrableOn_pmPowerDampedFermiSource_truncated_sq ε hN)⟩

private theorem pmqe_density_log_eight {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      pmqe_density ε x ≤ C*x^(-2*ε)/Real.log x^8 := by
  obtain ⟨C,hC,he⟩ := pmPowerDampedFermiSource_reciprocal_eventually_log_four hε hεhalf
  refine ⟨C^2,sq_nonneg _,?_⟩
  filter_upwards [he,eventually_gt_atTop (1 : ℝ)] with x hb hx
  have hx0 : 0 < x := by linarith only [hx]
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hp : (x^(1-ε))^2 = x^2*x^(-2*ε) := by
    rw [← Real.rpow_mul_natCast hx0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (1-ε)*2 = (2 : ℝ)+(-2*ε) by ring,Real.rpow_add hx0,Real.rpow_two]
  calc
    _ ≤ (C*x^(1-ε)/Real.log x^4)^2/x^2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb 2) (sq_nonneg x)
    _ = _ := by rw [div_pow,mul_pow,hp]; field_simp

private theorem pmqe_power_integral_bound {ε R Y : ℝ} (hε : ε < 1/2)
    (hR : 0 ≤ R) (hRY : R ≤ Y) :
    (∫ x in Ioc R Y, x^(-2*ε)) ≤ Y^(1-2*ε)/(1-2*ε) := by
  rw [← intervalIntegral.integral_of_le hRY,
    integral_rpow (Or.inl (by linarith only [hε] : -1 < -2*ε)),
    show -2*ε+1 = 1-2*ε by ring]
  exact div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg hR _)) (by linarith only [hε])

private theorem pmqe_energy_split {ε C : ℝ} (hε : ε < 1/2) (hC : 0 ≤ C)
    {R N : ℕ} (hR : 1 ≤ R) (hN : 2 ≤ N) (hlogR : 1 ≤ Real.log (R : ℝ))
    (hRN : (R : ℝ)^2 ≤ (N : ℝ))
    (hb : ∀ x : ℝ, (R : ℝ) ≤ x → pmqe_density ε x ≤ C*x^(-2*ε)/Real.log x^8) :
    pmPowerDampedFermiTruncatedEnergy ε N ≤ pmPowerDampedFermiTruncatedEnergy ε R+
      (C/(1-2*ε))*(N : ℝ)^((1-2*ε)/2)+
      (256*C/(1-2*ε))*(N : ℝ)^(1-2*ε)/Real.log (N : ℝ)^8 := by
  let Y : ℝ := Real.sqrt N
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hNr]
  have hRY : (R : ℝ) ≤ Y := Real.le_sqrt_of_sq_le hRN
  have hY0 : 0 < Y := hR0.trans_le hRY
  have hYN : Y ≤ (N : ℝ) := Real.sqrt_le_iff.mpr ⟨hN0.le,by nlinarith only [hNr]⟩
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith only [hNr])
  have ha : 0 < 1-2*ε := by linarith only [hε]
  have hiN : IntegrableOn (pmqe_density ε) (Ioc (0 : ℝ) (N : ℝ)) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr (pmqe_reciprocal ε (by omega)).2
  have hiR : IntegrableOn (pmqe_density ε) (Ioc (0 : ℝ) (R : ℝ)) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr (pmqe_reciprocal ε hR).2
  have hiRY : IntegrableOn (pmqe_density ε) (Ioc (R : ℝ) Y) :=
    hiN.mono_set fun x hx => ⟨hR0.trans hx.1,hx.2.trans hYN⟩
  have hiYN : IntegrableOn (pmqe_density ε) (Ioc Y (N : ℝ)) :=
    hiN.mono_set fun x hx => ⟨hY0.trans hx.1,hx.2⟩
  have hir : IntervalIntegrable (pmqe_density ε) volume 0 (R : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le).mpr hiR
  have hiry : IntervalIntegrable (pmqe_density ε) volume (R : ℝ) Y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hRY).mpr hiRY
  have hiyn : IntervalIntegrable (pmqe_density ε) volume Y (N : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hYN).mpr hiYN
  have hsplit : pmPowerDampedFermiTruncatedEnergy ε N =
      pmPowerDampedFermiTruncatedEnergy ε R+
        (∫ x in Ioc (R : ℝ) Y,pmqe_density ε x)+(∫ x in Ioc Y (N : ℝ),pmqe_density ε x) := by
    rw [(pmqe_reciprocal ε (by omega : 1 ≤ N)).1,(pmqe_reciprocal ε hR).1,
      ← integral_Ioc_eq_integral_Ioo,← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hN0.le,← intervalIntegral.integral_of_le hR0.le,
      ← intervalIntegral.integral_of_le hRY,← intervalIntegral.integral_of_le hYN,
      intervalIntegral.integral_add_adjacent_intervals hir hiry,
      intervalIntegral.integral_add_adjacent_intervals (hir.trans hiry) hiyn]
  have hpowint (a b : ℝ) (hab : a ≤ b) : IntegrableOn (fun x : ℝ => x^(-2*ε)) (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith only [hε] : -1 < -2*ε))
  have hhead : (∫ x in Ioc (R : ℝ) Y,pmqe_density ε x) ≤ (C/(1-2*ε))*(N : ℝ)^((1-2*ε)/2) := by
    have hh := setIntegral_mono_on hiRY ((hpowint _ _ hRY).const_mul C) measurableSet_Ioc
      (fun x hx => by
        have hx0 : 0 < x := hR0.trans hx.1
        have hlx : 1 ≤ Real.log x := hlogR.trans (Real.log_le_log hR0 hx.1.le)
        have hd : 1 ≤ Real.log x^8 := by
          simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlx 8
        exact (hb x hx.1.le).trans (div_le_self (by positivity) hd))
    rw [integral_const_mul] at hh
    have hYpow : Y^(1-2*ε) = (N : ℝ)^((1-2*ε)/2) := by
      dsimp only [Y]
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hN0.le]
      congr 1
      ring
    calc
      _ ≤ C*(∫ x in Ioc (R : ℝ) Y,x^(-2*ε)) := hh
      _ ≤ C*(Y^(1-2*ε)/(1-2*ε)) := mul_le_mul_of_nonneg_left
        (pmqe_power_integral_bound hε hR0.le hRY) hC
      _ = _ := by rw [hYpow]; ring
  have htail : (∫ x in Ioc Y (N : ℝ),pmqe_density ε x) ≤
      (256*C/(1-2*ε))*(N : ℝ)^(1-2*ε)/Real.log (N : ℝ)^8 := by
    have hK : 0 ≤ 256*C/Real.log (N : ℝ)^8 := by positivity
    have hh := setIntegral_mono_on hiYN
      ((hpowint _ _ hYN).const_mul (256*C/Real.log (N : ℝ)^8)) measurableSet_Ioc
      (fun x hx => by
        have hx0 : 0 < x := hY0.trans hx.1
        have hlog : Real.log (N : ℝ)/2 ≤ Real.log x := by
          have hh := Real.log_le_log hY0 hx.1.le
          change Real.log (Real.sqrt (N : ℝ)) ≤ Real.log x at hh
          rwa [Real.log_sqrt hN0.le] at hh
        have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.log (N : ℝ)/2) hlog 8
        have hquot : C/Real.log x^8 ≤ 256*C/Real.log (N : ℝ)^8 := by
          have hh := div_le_div_of_nonneg_left hC (by positivity : 0 < (Real.log (N : ℝ)/2)^8) hpow
          exact hh.trans_eq (by field_simp; norm_num)
        calc
          _ ≤ C*x^(-2*ε)/Real.log x^8 := hb x (hRY.trans hx.1.le)
          _ = (C/Real.log x^8)*x^(-2*ε) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hquot (Real.rpow_nonneg hx0.le _))
    rw [integral_const_mul] at hh
    calc
      _ ≤ (256*C/Real.log (N : ℝ)^8)*(∫ x in Ioc Y (N : ℝ),x^(-2*ε)) := hh
      _ ≤ (256*C/Real.log (N : ℝ)^8)*((N : ℝ)^(1-2*ε)/(1-2*ε)) :=
        mul_le_mul_of_nonneg_left (pmqe_power_integral_bound hε hY0.le hYN) hK
      _ = _ := by ring
  rw [hsplit]
  exact add_le_add (add_le_add le_rfl hhead) htail

/-- The actual physical source energy is negligible at the scale forced by
the negative mixed current, without canonical L2 admission. -/
theorem pmPowerDampedFermiTruncatedEnergy_log_four_negligible {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun N : ℕ => pmPowerDampedFermiTruncatedEnergy ε N*
      Real.log (N : ℝ)^4/(N : ℝ)^(1-2*ε)) atTop (𝓝 0) := by
  obtain ⟨C,hC,he⟩ := pmqe_density_log_eight hε hεhalf
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp he
  obtain ⟨R,hR⟩ := exists_nat_ge (max R₀ (Real.exp 1))
  have hRe : Real.exp 1 ≤ (R : ℝ) := (le_max_right _ _).trans hR
  have hRR : R₀ ≤ (R : ℝ) := (le_max_left _ _).trans hR
  have hR0 : (0 : ℝ) < R := (Real.exp_pos 1).trans_le hRe
  have hR1 : 1 ≤ R := by
    have hh : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    exact_mod_cast hh.trans hRe
  have hlogR : 1 ≤ Real.log (R : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hRe
    rwa [Real.log_exp] at hh
  let a : ℝ := 1-2*ε
  have ha : 0 < a := by dsimp only [a]; linarith only [hεhalf]
  let A := pmPowerDampedFermiTruncatedEnergy ε R
  let B := C/a
  let D := 256*C/a
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpowlim (b : ℝ) (hb : 0 < b) :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)^4/(N : ℝ)^b) atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop (4 : ℝ) hb).tendsto_div_nhds_zero).comp hnat
    simpa only [Function.comp_def,
      show ∀ x : ℝ,x^(4 : ℝ) = x^(4 : ℕ) from fun x => Real.rpow_natCast x 4] using h
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)^4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp (Real.tendsto_log_atTop.comp hnat)
  have hinv : Tendsto (fun N : ℕ => 1/Real.log (N : ℝ)^4) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp hlogtop
  have hlim : Tendsto (fun N : ℕ => A*(Real.log (N : ℝ)^4/(N : ℝ)^a)+
      B*(Real.log (N : ℝ)^4/(N : ℝ)^(a/2))+D*(1/Real.log (N : ℝ)^4)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using
      (((hpowlim a ha).const_mul A).add ((hpowlim (a/2) (by positivity)).const_mul B)).add (hinv.const_mul D)
  apply squeeze_zero' (Eventually.of_forall fun N => by
    have hE : 0 ≤ pmPowerDampedFermiTruncatedEnergy ε N := integral_nonneg fun _ => sq_nonneg _
    exact div_nonneg (mul_nonneg hE (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)) ?_ hlim
  filter_upwards [hnat.eventually_ge_atTop ((R : ℝ)^2),eventually_ge_atTop (2 : ℕ)] with N hRN hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hNr]
  have hlN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by linarith only [hNr])).ne'
  have hpN : (N : ℝ)^(a/2) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hb := pmqe_energy_split hεhalf hC hR1 hN hlogR hRN (fun x hx => hR₀ x (hRR.trans hx))
  change pmPowerDampedFermiTruncatedEnergy ε N ≤ A+B*(N : ℝ)^(a/2)+D*(N : ℝ)^a/Real.log (N : ℝ)^8 at hb
  have hp : (N : ℝ)^a = ((N : ℝ)^(a/2))^2 := by
    rw [← Real.rpow_mul_natCast hN0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  calc
    _ = pmPowerDampedFermiTruncatedEnergy ε N*(Real.log (N : ℝ)^4/(N : ℝ)^a) := by dsimp only [a]; ring
    _ ≤ (A+B*(N : ℝ)^(a/2)+D*(N : ℝ)^a/Real.log (N : ℝ)^8)*
        (Real.log (N : ℝ)^4/(N : ℝ)^a) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by rw [hp]; field_simp

private theorem pmqe_relative_energy_at {ε c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    {P : ℕ} (hP : 2 ≤ P)
    (hm : c*(2*(P : ℝ))^(2-4*ε)/Real.log (2*(P : ℝ))^4 ≤
      pmPrimeUpdateNegativeMixedCurrent ε (8*P^2))
    (hs : pmPowerDampedFermiTruncatedEnergy ε (8*P^2)*Real.log ((8*P^2 : ℕ) : ℝ)^4/
      ((8*P^2 : ℕ) : ℝ)^(1-2*ε) < 2*δ*c/(2 : ℝ)^(1-2*ε)) :
    pmPowerDampedFermiTruncatedEnergy ε (8*P^2) ≤
      2*δ*pmPrimeUpdateNegativeMixedCurrent ε (8*P^2) := by
  let a : ℝ := 1-2*ε
  let N : ℕ := 8*P^2
  let Y : ℝ := 2*(P : ℝ)
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith only [hPr]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hY1 : 1 < Y := by dsimp [Y]; linarith only [hPr]
  have hlY : 0 < Real.log Y := Real.log_pos hY1
  have hN1 : 1 ≤ N := by dsimp [N]; nlinarith only [hP]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNeq : (N : ℝ) = 2*Y^2 := by dsimp [N,Y]; push_cast; ring
  have hYN : Y ≤ (N : ℝ) := by rw [hNeq]; nlinarith only [hY1]
  have hlog := pow_le_pow_left₀ hlY.le (Real.log_le_log hY hYN) 4
  have hpow : (N : ℝ)^a = (2 : ℝ)^a*Y^(2-4*ε) := by
    rw [hNeq,Real.mul_rpow (by norm_num) (sq_nonneg Y),← Real.rpow_natCast_mul hY.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    congr 1
    dsimp only [a]
    ring
  have hE0 : 0 ≤ pmPowerDampedFermiTruncatedEnergy ε N := integral_nonneg fun _ => sq_nonneg _
  change pmPowerDampedFermiTruncatedEnergy ε N*Real.log (N : ℝ)^4/(N : ℝ)^a < 2*δ*c/(2 : ℝ)^a at hs
  have hb := (div_lt_iff₀ (Real.rpow_pos_of_pos hN0 a)).mp hs
  have hrhs : (2*δ*c/(2 : ℝ)^a)*(N : ℝ)^a = 2*δ*c*Y^(2-4*ε) := by
    rw [hpow]
    field_simp
  rw [hrhs] at hb
  change c*Y^(2-4*ε)/Real.log Y^4 ≤ pmPrimeUpdateNegativeMixedCurrent ε N at hm
  have hm' := (div_le_iff₀ (pow_pos hlY 4)).mp hm
  have hh : pmPowerDampedFermiTruncatedEnergy ε N*Real.log Y^4 ≤
      (2*δ*pmPrimeUpdateNegativeMixedCurrent ε N)*Real.log Y^4 := by
    calc
      _ ≤ pmPowerDampedFermiTruncatedEnergy ε N*Real.log (N : ℝ)^4 :=
        mul_le_mul_of_nonneg_left hlog hE0
      _ ≤ 2*δ*c*Y^(2-4*ε) := hb.le
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hm' (by positivity : 0 ≤ 2*δ)]
  exact (mul_le_mul_iff_left₀ (pow_pos hlY 4)).mp hh

private theorem pmqe_relative_energy_eventually {ε c : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) (hc : 0 < c)
    (he : ∀ᶠ P : ℕ in atTop, c*(2*(P : ℝ))^(2-4*ε)/Real.log (2*(P : ℝ))^4 ≤
      pmPrimeUpdateNegativeMixedCurrent ε (8*P^2)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ P : ℕ in atTop, pmPowerDampedFermiTruncatedEnergy ε (8*P^2) ≤
      2*δ*pmPrimeUpdateNegativeMixedCurrent ε (8*P^2) := by
  have htop2 : Tendsto (fun P : ℕ => P^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have htop : Tendsto (fun P : ℕ => 8*P^2) atTop atTop :=
    htop2.const_mul_atTop' (by norm_num : 0 < (8 : ℕ))
  have hlim := (pmPowerDampedFermiTruncatedEnergy_log_four_negligible hε hεhalf).comp htop
  have hsmall := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 2*δ*c/(2 : ℝ)^(1-2*ε)))
  filter_upwards [he,hsmall,eventually_ge_atTop (2 : ℕ)] with P hm hs hP
  exact pmqe_relative_energy_at hc hδ hP hm hs

/-- The actual positive mixed current compensates the proved negative mass
to leading order. The bounded signed remainder required for RH is not asserted. -/
theorem pmPrimeUpdatePositiveMixedCurrent_leading_compensation :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ δ > 0, ∀ᶠ P : ℕ in atTop,
      (1-δ)*pmPrimeUpdateNegativeMixedCurrent ε (8*P^2) ≤
        pmPrimeUpdatePositiveMixedCurrent ε (8*P^2) := by
  filter_upwards [pmPrimeUpdateNegativeMixedCurrent_eventually_lower,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with ε he hε
  obtain ⟨c,hc,he⟩ := he
  intro δ hδ
  filter_upwards [pmqe_relative_energy_eventually hε.1 hε.2 hc he hδ,
    eventually_ge_atTop (2 : ℕ)] with P hrelative hP
  have hN1 : 1 ≤ 8*P^2 := by nlinarith only [hP]
  have hbalance := pmPowerDampedFermiTruncatedEnergy_signed_balance ε hN1
  have hseed : 0 ≤ ∫ t in Ioi (1/((8*P^2 : ℕ) : ℝ)), ‖fermiNymanGen 1 t‖^2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hQ := pmPrimeUpdateQuadraticCurrent_nonneg ε (8*P^2)
  linarith only [hrelative,hbalance,hseed,hQ]

end RHTower
