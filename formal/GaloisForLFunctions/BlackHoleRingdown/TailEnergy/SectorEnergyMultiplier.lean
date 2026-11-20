import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.PrimePowerReturnsForceSignedCancellation
import GaloisForLFunctions.BlackHoleRingdown.CuspEscapeAndMixedPulseInterference
import GaloisForLFunctions.RHTower.SoninSemilocalPoissonExpansion

/-!
# Energy of a prime-sector receiver

The normalized Jackson series of Arushi, Goswami, Das and Santra
(arXiv:2611.23023, §2) becomes a geometric multiplier in the physical
frequency. Plancherel gives the complete energy response of the actual
prime sector. Disjoint input translates can still interfere after
selection of the prime returns.
-/
noncomputable section
open Complex MeasureTheory Set Filter Topology Finset
open scoped FourierTransform ComplexConjugate
namespace GaloisForLFunctions.BlackHoleRingdown.ReturnCancellation

/-- Plancherel for an arbitrary contractive measurable receiver symbol. -/
theorem contractive_receiver_plancherel (h : CompactPulse) {J : ℝ → ℂ} (hJ : Measurable J)
    (hj : ∀ ξ : ℝ, ‖J ξ‖ ≤ 1) :
    Integrable (fun t : ℝ => ‖unitaryReflected J h t‖^2) ∧
      (∫ t : ℝ, ‖unitaryReflected J h t‖^2) = 2*Real.pi*(∫ ξ : ℝ, ‖pulseAmplitude h (ξ:ℂ)*J ξ‖^2) := by
  let F := fun ξ : ℝ => pulseAmplitude h (ξ:ℂ)*J ξ
  have hm : Measurable F := (h.differentiable_amplitude.continuous.measurable.comp Complex.measurable_ofReal).mul hJ
  have hn (ξ : ℝ) : ‖F ξ‖ ≤ ‖pulseAmplitude h (ξ:ℂ)‖ := by
    show ‖pulseAmplitude h (ξ:ℂ)*J ξ‖ ≤ _
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hj ξ)
  have ha : Integrable (fun ξ : ℝ => pulseAmplitude h (ξ:ℂ)) := by simpa using h.integrable_amplitude_line 0
  have hi := ha.norm.mono' hm.aestronglyMeasurable (.of_forall hn)
  have hF₂ : MemLp F 2 volume := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    ((integrable_norm_sq_pulseAmplitude h).mono' (hm.norm.pow_const 2).aestronglyMeasurable
      (.of_forall fun ξ => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hn ξ) 2))
  let k := -(2*Real.pi)⁻¹
  have hπ : (2*Real.pi:ℝ) ≠ 0 := by positivity
  have hk : k ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hπ)
  have htransform (t : ℝ) : unitaryReflected J h t = 𝓕 F (k*t) := by
    rw [unitaryReflected,Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    refine .of_forall fun ξ => ?_
    have he : (((-2*Real.pi*ξ*(k*t):ℝ):ℂ)*I) = I*(ξ:ℂ)*t := by
      have htime : -2*Real.pi*ξ*(k*t) = ξ*t := by dsimp only [k]; field_simp [hπ]
      rw [htime]; push_cast;ring
    beta_reduce
    rw [he,smul_eq_mul,mul_comm]
  have hcomp := ((_root_.GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hi hF₂).comp_mul_left' hk)
  constructor
  · exact hcomp.congr (.of_forall fun t => by beta_reduce; rw [htransform])
  simp_rw [htransform]
  rw [Measure.integral_comp_mul_left (fun ξ : ℝ => ‖𝓕 F ξ‖^2),smul_eq_mul,
    _root_.GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hi hF₂]
  simp [k,abs_of_pos Real.pi_pos,F,norm_mul]

/-- Geometric ratio of successive returns from p. -/
def sectorRatio (p : ℕ) : ℝ := (p:ℝ)⁻¹
private theorem scale_mem {p : ℕ} (hp : p.Prime) : sectorRatio p ∈ Set.Ioo 0 1 :=
  ⟨inv_pos.mpr (Nat.cast_pos.mpr hp.pos),inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)⟩

private def osc (d ξ : ℝ) := cexp (-(I*(ξ:ℂ)*d))
private theorem norm_osc (d ξ : ℝ) : ‖osc d ξ‖=1 := by
  simp [osc,Complex.exp_neg,norm_exp_I_mul]

/-- Multiplier on the reflected channel after selection of a single prime. -/
def sectorMultiplier (p : ℕ) (ξ : ℝ) : ℂ :=
  ((1-sectorRatio p:ℝ):ℂ)/(1-(sectorRatio p:ℂ)*osc (echoDelay p) ξ)

private theorem denom_pos {p : ℕ} (hp : p.Prime) (ξ : ℝ) :
    1-sectorRatio p ≤ ‖1-(sectorRatio p:ℂ)*osc (echoDelay p) ξ‖ := by
  have h := norm_sub_norm_le (1:ℂ) ((sectorRatio p:ℂ)*osc (echoDelay p) ξ)
  simpa only [norm_one,norm_mul,norm_osc,mul_one,Complex.norm_real,Real.norm_of_nonneg (scale_mem hp).1.le] using h

/-- Pointwise energy amplitude lies between the alternating and the stationary phase gains. -/
theorem sector_multiplier_bounds {p : ℕ} (hp : p.Prime) (ξ : ℝ) :
    (1-sectorRatio p)/(1+sectorRatio p) ≤ ‖sectorMultiplier p ξ‖ ∧ ‖sectorMultiplier p ξ‖ ≤ 1 := by
  have hs := scale_mem hp
  have hd := denom_pos hp ξ
  have hden := (sub_pos.mpr hs.2).trans_le hd
  rw [sectorMultiplier,norm_div,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr hs.2.le)]
  constructor
  · apply div_le_div_of_nonneg_left (sub_nonneg.mpr hs.2.le) hden
    have hh := norm_sub_le (1:ℂ) ((sectorRatio p:ℂ)*osc (echoDelay p) ξ)
    simpa only [norm_one,norm_mul,norm_osc,mul_one,Complex.norm_real,Real.norm_of_nonneg hs.1.le] using hh
  · exact (div_le_one hden).mpr hd

private theorem measurable_sector (p : ℕ) : Measurable (sectorMultiplier p) := by
  unfold sectorMultiplier osc
  fun_prop

/-- Physical scattering symbol with its prime receiver included. -/
def sectorScatteringSymbol (p : ℕ) (ξ : ℝ) := scatteringPhase ((ξ:ℂ)*I)*sectorMultiplier p ξ
private theorem measurable_symbol (p : ℕ) : Measurable (sectorScatteringSymbol p) :=
  continuous_scatteringPhase_line.measurable.mul (measurable_sector p)
private theorem norm_symbol (p : ℕ) (ξ : ℝ) : ‖sectorScatteringSymbol p ξ‖=‖sectorMultiplier p ξ‖ := by
  simp [sectorScatteringSymbol,norm_mul,norm_scatteringPhase_line]

/-- Fourier representation of the centered prime sector at every physical time. -/
theorem centered_sector_fourier (h : CompactPulse) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    centeredPrimeSector h p t = unitaryReflected (sectorScatteringSymbol p) h t := by
  let A := unitaryReflected (sectorScatteringSymbol p) h
  let q := (sectorRatio p:ℂ)
  have hq : q=1/(p:ℂ) := by simp [q,sectorRatio]
  have hsym (ξ : ℝ) : ‖sectorScatteringSymbol p ξ‖ ≤ 1 := (norm_symbol p ξ).le.trans (sector_multiplier_bounds hp ξ).2
  have hA (u : ℝ) : ‖A u‖ ≤ ∫ ξ : ℝ, ‖pulseAmplitude h (ξ:ℂ)‖ := by
    have hi := h.integrable_amplitude_mul (measurable_symbol p) hsym u
    have ha := (h.integrable_amplitude_line 0).norm
    have hint : Integrable (fun ξ : ℝ => ‖pulseAmplitude h (ξ:ℂ)‖) := by simpa using ha
    refine (norm_integral_le_integral_norm _).trans (integral_mono hi.norm hint fun ξ => ?_)
    rw [norm_mul,norm_exp_I_mul,mul_one,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hsym ξ)
  have hdiff (u : ℝ) : A u = (1-q)*pulseReflected h u+q*A (u-echoDelay p) := by
    have hmain := h.integrable_amplitude_mul continuous_scatteringPhase_line.measurable
      (fun ξ => (norm_scatteringPhase_line ξ).le) u
    have htail := h.integrable_amplitude_mul (measurable_symbol p) hsym (u-echoDelay p)
    dsimp only [A,unitaryReflected,pulseReflected]
    rw [←integral_const_mul,←integral_const_mul,←integral_add (hmain.const_mul _) (htail.const_mul _)]
    apply integral_congr_ae
    refine .of_forall fun ξ => ?_
    have hosc : cexp (I*(ξ:ℂ)*(u-echoDelay p:ℝ)) = osc (echoDelay p) ξ*cexp (I*(ξ:ℂ)*u) := by
      rw [osc,←Complex.exp_add]; congr 1;push_cast;ring
    beta_reduce
    rw [hosc]
    have hden : 1-q*osc (echoDelay p) ξ ≠ 0 :=
      norm_ne_zero_iff.mp ((sub_pos.mpr (scale_mem hp).2).trans_le (denom_pos hp ξ)).ne'
    have hfactor : sectorMultiplier p ξ*(1-q*osc (echoDelay p) ξ)=1-q := by
      unfold sectorMultiplier
      rw [div_mul_cancel₀ _ hden, Complex.ofReal_sub,Complex.ofReal_one]
    dsimp only [sectorScatteringSymbol]
    linear_combination pulseAmplitude h (ξ:ℂ)*scatteringPhase ((ξ:ℂ)*I)*cexp (I*(ξ:ℂ)*u)*hfactor
  have hres := sector_residual_bound h hp A (ε:=0) hA (fun u => by
    rw [←hq,hdiff u,add_sub_cancel_left,sub_self,norm_zero]) t
  rw [zero_div] at hres
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hres (norm_nonneg _)))).symm

/-- Literal total energy, with the local Euler multiplier retained inside the spectral integral. -/
theorem prime_sector_energy_spectrum (h : CompactPulse) {p : ℕ} (hp : p.Prime) :
    Integrable (fun t : ℝ => ‖centeredPrimeSector h p t‖^2) ∧
    (∫ t : ℝ, ‖centeredPrimeSector h p t‖^2) =
      2*Real.pi*(∫ ξ : ℝ, ‖pulseAmplitude h (ξ:ℂ)‖^2*‖sectorMultiplier p ξ‖^2) := by
  simp_rw [centered_sector_fourier h hp]
  simpa only [norm_mul,mul_pow,norm_symbol] using contractive_receiver_plancherel h (measurable_symbol p)
    (fun ξ => (norm_symbol p ξ).le.trans (sector_multiplier_bounds hp ξ).2)

private theorem integrable_spectral_energy (h : CompactPulse) {p : ℕ} (hp : p.Prime) :
    Integrable (fun ξ : ℝ => ‖pulseAmplitude h (ξ:ℂ)‖^2*‖sectorMultiplier p ξ‖^2) := by
  have hmeas := (h.differentiable_amplitude.continuous.measurable.comp Complex.measurable_ofReal).norm.pow_const 2
  refine (integrable_norm_sq_pulseAmplitude h).mono' (hmeas.mul ((measurable_sector p).norm.pow_const 2)).aestronglyMeasurable
    (.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  apply mul_le_of_le_one_right (sq_nonneg _)
  simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (sector_multiplier_bounds hp ξ).2 2

/-- Every prime receiver has a uniform lower and upper energy gain. -/
theorem prime_sector_energy_bounds (h : CompactPulse) {p : ℕ} (hp : p.Prime) :
    ((1-sectorRatio p)/(1+sectorRatio p))^2*(∫ t : ℝ, ‖h t‖^2) ≤ (∫ t : ℝ, ‖centeredPrimeSector h p t‖^2) ∧
    (∫ t : ℝ, ‖centeredPrimeSector h p t‖^2) ≤ ∫ t : ℝ, ‖h t‖^2 := by
  let r := (1-sectorRatio p)/(1+sectorRatio p)
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr (scale_mem hp).2.le) (by linarith [(scale_mem hp).1])
  have ht := integrable_spectral_energy h hp
  have ha := integrable_norm_sq_pulseAmplitude h
  have hpi : 0 ≤ 2*Real.pi := by positivity
  rw [(prime_sector_energy_spectrum h hp).2,←integral_norm_sq_pulseAmplitude]
  constructor
  · rw [show r^2*(2*Real.pi*(∫ ξ : ℝ, ‖pulseAmplitude h (ξ:ℂ)‖^2)) =
      (2*Real.pi)*(r^2*(∫ ξ : ℝ, ‖pulseAmplitude h (ξ:ℂ)‖^2)) by ring,←integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_mono (ha.const_mul _) ht (fun ξ => by
      rw [mul_comm (r^2)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr (sector_multiplier_bounds hp ξ).1 2) (sq_nonneg _))) hpi
  · apply mul_le_mul_of_nonneg_left _ hpi
    apply integral_mono ht ha
    intro ξ
    apply mul_le_of_le_one_right (sq_nonneg _)
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (sector_multiplier_bounds hp ξ).2 2

/-- Complex autocorrelation of the compact input at a physical delay. -/
def inputCorrelation (h : CompactPulse) (v : ℝ) :=
  ∫ s : ℝ, h (s-v)*conj (h s)

private theorem multiplier_poisson {p : ℕ} (hp : p.Prime) (ξ : ℝ) :
    ((‖sectorMultiplier p ξ‖^2:ℝ):ℂ) =
      (((1-sectorRatio p)/(1+sectorRatio p):ℝ):ℂ)*
        ∑' m : ℤ, _root_.RHTower.semilocalBilateralPoissonTerm (sectorRatio p) (osc (echoDelay p) ξ) m := by
  let r := sectorRatio p
  let z := osc (echoDelay p) ξ
  have hr := scale_mem hp
  have hgeo := _root_.RHTower.semilocalOnePrimePoissonExpansion hr.1.le hr.2 (norm_osc (echoDelay p) ξ)
  change ((Complex.normSq (1-(r:ℂ)*z):ℂ))⁻¹ = (1-(r:ℂ)^2)⁻¹*_ at hgeo
  have hrp : 1+(r:ℂ)≠0 := by exact_mod_cast (show (1:ℝ)+r≠0 from (by linarith [hr.1] : (0:ℝ) < 1+r).ne')
  have hrm : 1-(r:ℂ)≠0 := by exact_mod_cast (sub_pos.mpr hr.2).ne'
  have hfac : 1-(r:ℂ)^2=(1-r)*(1+r) := by ring
  rw [sectorMultiplier,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    ←Complex.normSq_eq_norm_sq,Complex.ofReal_div,div_eq_mul_inv,hgeo]
  push_cast
  rw [hfac,mul_inv_rev]
  dsimp only [r] at hrp hrm ⊢
  field_simp [hrp,hrm]
  <;> ring

private theorem osc_integer_delay (d ξ : ℝ) (m : ℤ) :
    (osc d ξ)^m=osc ((m:ℝ)*d) ξ := by
  rw [osc,osc,←Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- The entire energy is the Abel-weighted sum of input autocorrelations
on the two-sided physical delay lattice. Compactness makes this sum finite. -/
theorem prime_sector_energy_by_input_correlations (h : CompactPulse) {p : ℕ} (hp : p.Prime) :
    ((∫ t : ℝ, ‖centeredPrimeSector h p t‖^2:ℝ):ℂ) =
      (((1-sectorRatio p)/(1+sectorRatio p):ℝ):ℂ)*
        ∑' m : ℤ, ((sectorRatio p:ℂ)^m.natAbs)*inputCorrelation h (m*echoDelay p) := by
  let q := sectorRatio p
  let d := echoDelay p
  let B := ((1-q)/(1+q):ℝ)
  let H := fun ξ : ℝ => ‖pulseAmplitude h (ξ:ℂ)‖^2
  let F := fun (m : ℤ) (ξ : ℝ) => (q:ℂ)^m.natAbs*((H ξ:ℂ)*osc ((m:ℝ)*d) ξ)
  have hq := scale_mem hp
  have hH : Integrable H := integrable_norm_sq_pulseAmplitude h
  have hm (m : ℤ) : Measurable (F m) := by
    have hA : Measurable (fun ξ : ℝ => pulseAmplitude h (ξ:ℂ)) :=
      h.differentiable_amplitude.continuous.measurable.comp Complex.measurable_ofReal
    unfold F H osc
    fun_prop
  have hnorm (m : ℤ) (ξ : ℝ) : ‖F m ξ‖ = q^m.natAbs*H ξ := by
    simp only [F,norm_mul,norm_pow,Complex.norm_real,norm_osc,mul_one]
    rw [Real.norm_of_nonneg (show (0:ℝ) ≤ q from hq.1.le),
      Real.norm_of_nonneg (show (0:ℝ) ≤ H ξ from sq_nonneg _)]
  have hint (m : ℤ) : Integrable (F m) :=
    (hH.const_mul (q^m.natAbs)).mono' (hm m).aestronglyMeasurable (.of_forall fun ξ => (hnorm m ξ).le)
  have hsum := (_root_.RHTower.summable_int_pow_natAbs hq.1.le hq.2).mul_right (∫ ξ : ℝ,H ξ)
  have habs : Summable (fun m : ℤ => ∫ ξ : ℝ, ‖F m ξ‖) := by
    simpa only [hnorm,integral_const_mul] using hsum
  have hswitch := (hasSum_integral_of_summable_integral_norm hint habs).tsum_eq
  have hpoint (ξ : ℝ) : ((H ξ*‖sectorMultiplier p ξ‖^2:ℝ):ℂ) = (B:ℂ)*∑' m : ℤ, F m ξ := by
    rw [Complex.ofReal_mul,multiplier_poisson hp ξ]
    change (H ξ:ℂ)*((B:ℂ)*_)=(B:ℂ)*_
    rw [mul_left_comm,←tsum_mul_left]
    congr 1
    refine tsum_congr fun m => ?_
    rw [_root_.RHTower.semilocalBilateralPoissonTerm,osc_integer_delay]
    dsimp only [F]
    ring
  have hrow (m : ℤ) : (2*(Real.pi:ℂ))*(∫ ξ : ℝ, F m ξ) =
      (q:ℂ)^m.natAbs*inputCorrelation h (m*d) := by
    simp only [F,integral_const_mul]
    rw [mul_left_comm]
    exact congrArg (fun x => (q:ℂ)^m.natAbs*x) (integral_norm_sq_pulseAmplitude_mul_cexp h (m*d))
  rw [(prime_sector_energy_spectrum h hp).2,Complex.ofReal_mul,←integral_complex_ofReal]
  change ((2*Real.pi:ℝ):ℂ)*(∫ ξ : ℝ, ((H ξ*‖sectorMultiplier p ξ‖^2:ℝ):ℂ))=_
  simp_rw [hpoint]
  rw [integral_const_mul,←hswitch,mul_left_comm,←tsum_mul_left]
  push_cast
  rw [tsum_congr hrow]
  simp only [B,q,d,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_one]

private theorem correlation_zero_of_gap (h : CompactPulse) {A B v : ℝ}
    (hs : ∀ t ∉ Icc A B, h t=0) (hv : B-A < |v|) : inputCorrelation h v=0 := by
  unfold inputCorrelation
  apply integral_eq_zero_of_ae
  refine .of_forall fun t => ?_
  show h (t-v) * conj (h t) = 0
  by_cases ht : t∈Icc A B
  · have hout : t-v ∉ Icc A B := by
      intro hh
      have hb := abs_le.mpr (show -(B-A) ≤ v ∧ v ≤ B-A by
        constructor <;> linarith only [ht.1,ht.2,hh.1,hh.2])
      exact hv.not_ge hb
    rw [hs _ hout,zero_mul]
  · simp [hs t ht]

theorem sector_energy_finite_autocorrelations (h : CompactPulse) {p : ℕ} (hp : p.Prime) {A B : ℝ}
    (hs : ∀ t ∉ Icc A B, h t=0) {M : ℕ} (hM : B-A < (M+1)*echoDelay p) :
    ((∫ t : ℝ, ‖centeredPrimeSector h p t‖^2:ℝ):ℂ) =
      (((1-sectorRatio p)/(1+sectorRatio p):ℝ):ℂ)*
        ∑ m ∈ Finset.Icc (-(M:ℤ)) M, (sectorRatio p:ℂ)^m.natAbs*inputCorrelation h (m*echoDelay p) := by
  rw [prime_sector_energy_by_input_correlations h hp]
  congr 1
  apply tsum_eq_sum
  intro m hm
  have hfar : M+1 ≤ |m| := by simp only [Finset.mem_Icc] at hm; rw [le_abs]; omega
  have hd : 0 < echoDelay p := mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hp.one_lt))
  have hgap : B-A < |(m:ℝ)*echoDelay p| := by
    rw [abs_mul,abs_of_pos hd]
    exact hM.trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hfar) hd.le)
  rw [correlation_zero_of_gap h hs hgap,mul_zero]

/-- For a pulse shorter than the first prime delay, the measured energy has
the universal fraction (p−1)/(p+1), regardless of the pulse shape or placement. -/
theorem short_pulse_prime_energy (h : CompactPulse) {p : ℕ} (hp : p.Prime) {A B : ℝ}
    (hs : ∀ t ∉ Icc A B,h t=0) (hwidth : B-A < echoDelay p) :
    (∫ t : ℝ, ‖centeredPrimeSector h p t‖^2) =
      ((p:ℝ)-1)/((p:ℝ)+1)*(∫ t : ℝ, ‖h t‖^2) := by
  have hf := sector_energy_finite_autocorrelations h hp hs (M:=0) (by simpa using hwidth)
  have hz : inputCorrelation h 0 = ((∫ t : ℝ, ‖h t‖^2:ℝ):ℂ) := by
    simp only [inputCorrelation,sub_zero,Complex.mul_conj,Complex.normSq_eq_norm_sq,integral_complex_ofReal]
  have h := congrArg Complex.re hf
  simp only [Nat.cast_zero,neg_zero,Finset.Icc_self,Finset.sum_singleton,Int.natAbs_zero,pow_zero,Int.cast_zero,
    zero_mul,hz,one_mul,←Complex.ofReal_mul,Complex.ofReal_re] at h
  rw [h]
  congr 1
  dsimp only [sectorRatio]
  have hp0 : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp [hp0]
  <;> ring

/-- Every fixed compact pulse obeys the exact universal energy fraction
at all sufficiently large primes. -/
theorem eventual_prime_energy_fraction (h : CompactPulse) :
    ∀ᶠ p : ℕ in atTop, p.Prime →
      (∫ t : ℝ, ‖centeredPrimeSector h p t‖^2) = ((p:ℝ)-1)/((p:ℝ)+1)*(∫ t : ℝ, ‖h t‖^2) := by
  obtain ⟨S,_,hs⟩ := h.exists_support_bound
  have hg := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop S
  filter_upwards [hg] with p hp hprime
  apply short_pulse_prime_energy h hprime (A:= -S) (B:=S)
  · intro t ht
    apply hs
    by_contra! hle
    exact ht (abs_le.mp hle)
  · change S-(-S) < 2*Real.log p
    change S < Real.log p at hp
    linarith

end GaloisForLFunctions.BlackHoleRingdown.ReturnCancellation
