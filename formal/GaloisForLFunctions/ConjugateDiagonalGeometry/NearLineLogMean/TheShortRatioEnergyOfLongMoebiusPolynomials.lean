import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimitiveSpectrumOfTheMoebiusGram
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LongMoebiusSecondMomentRigidity
import GaloisForLFunctions.RHTower.Sieve.GallagherRange
import GaloisForLFunctions.RHTower.FirstMoment

/-!
# The short-ratio energy of a long Möbius polynomial

The L² Fourier identity for a moving logarithmic window retains only
ratios within its width. At width 1/T this positive energy controls the
critical moment through height T. Conversely two clipped prefixes bound
each window by the zero width, uniformly in its starting point.
-/

noncomputable section
open Finset Complex Filter Topology MeasureTheory
open RHTower hiding linePoint
open RHTower.Sieve
open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_le_iff_xiZeroHalfPlaneBound)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

private abbrev amplitude (n : ℕ) : ℂ := coeff n

/-- The two Fourier normalizations differ by reflection and the factor 2π. -/
theorem critical_moebius_logPoly (N : ℕ) (w : ℝ) :
    moebiusPoly N (linePoint (-(2*Real.pi)*w)) = logPoly amplitude (Icc 1 N) w := by
  unfold moebiusPoly edPoly logPoly
  apply sum_congr rfl
  intro n hn
  have hline (t : ℝ) : linePoint t = _root_.RHTower.linePt t := by
    norm_num [linePoint,_root_.RHTower.linePt]
  rw [hline,Complex.ofReal_natCast,natCast_cpow_neg_linePt n (mem_Icc.mp hn).1,
    Real.rpow_neg (Nat.cast_nonneg n),←Real.sqrt_eq_rpow]
  have hphase : -(I*(Real.log n:ℂ))*((-(2*Real.pi)*w:ℝ):ℂ) =
      ((2*Real.pi*(w*Real.log n):ℝ):ℂ)*I := by push_cast; ring
  rw [hphase]
  simp only [amplitude,coeff,mobiusRealCoefficient,mobCoeff,div_eq_mul_inv,Complex.ofReal_mul,
    Complex.ofReal_intCast,Complex.ofReal_inv,mul_assoc]

private def clip (N : ℕ) (u : ℝ) := min N ⌊Real.exp u⌋₊

/-- The endpoints of the moving window cut two prefixes, including empty
prefixes when the window lies outside the coefficient support. -/
private theorem clipped_window (a : ℕ → ℂ) (N : ℕ) {δ : ℝ} (hδ : 0≤δ) (u : ℝ) :
    logWindowSum a (Icc 1 N) δ u =
      (∑ n ∈ Icc 1 (clip N (u+δ)), a n) - ∑ n ∈ Icc 1 (clip N u), a n := by
  have hle : clip N u≤clip N (u+δ) := min_le_min_left _ (Nat.floor_mono
    (Real.exp_le_exp.mpr (le_add_of_nonneg_right hδ)))
  have hs : Icc 1 (clip N u)⊆Icc 1 (clip N (u+δ)) := fun n hn =>
    mem_Icc.mpr ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hle⟩
  have hwin := logWindowSum_log a (Icc 1 N) (fun _ hn => (mem_Icc.mp hn).1) δ (Real.exp_pos u)
  rw [Real.log_exp,←Real.exp_add] at hwin
  rw [hwin,←eq_sub_iff_add_eq.mpr (sum_sdiff (f:=a) hs)]
  apply congrArg (fun s : Finset ℕ => ∑ n ∈ s, a n)
  ext n
  refine Finset.mem_filter.trans (Iff.trans ?_ Finset.mem_sdiff.symm)
  simp only [Finset.mem_Icc,clip,le_min_iff,Nat.le_floor_iff (Real.exp_pos u).le,
    Nat.le_floor_iff (Real.exp_pos (u+δ)).le,←not_le (a:=(n:ℝ)) (b:=Real.exp u)]
  tauto

/-- A uniform prefix bound controls the entire continuum of moving
windows. The factor log N + δ is their exact containing interval length. -/
theorem window_energy_le_of_prefix_bound (a : ℕ → ℂ) {N : ℕ} (hN : 1≤N)
    {M δ : ℝ} (hδ : 0≤δ) (hb : ∀ k≤N, ‖∑ n ∈ Icc 1 k, a n‖≤M) :
    (∫ u : ℝ, ‖logWindowSum a (Icc 1 N) δ u‖^2) ≤ (Real.log N+δ)*(2*M)^2 := by
  let S := Set.Icc (-δ) (Real.log N)
  have hi := integrable_normSq_logWindowSum a (Icc 1 N) δ
  have supp (u : ℝ) (hu : u∉S) : logWindowSum a (Icc 1 N) δ u=0 := by
    apply sum_eq_zero
    intro n hn
    obtain ⟨h1,h2⟩ := mem_Icc.mp hn
    have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr h1
    have hl : 0≤Real.log n := Real.log_nonneg (by exact_mod_cast h1)
    have hr := Real.log_le_log hn0 (Nat.cast_le.mpr h2)
    have hx : u∉logWindow δ n := fun hh => hu
      ⟨by linarith only [hh.1,hl],hh.2.le.trans hr⟩
    rw [Set.indicator_of_notMem hx,zero_smul]
  have bound (u : ℝ) : ‖logWindowSum a (Icc 1 N) δ u‖≤2*M := by
    rw [clipped_window a N hδ u]
    rw [two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hb _ (min_le_left _ _)) (hb _ (min_le_left _ _)))
  have hS : volume S≠⊤ := isCompact_Icc.measure_lt_top.ne
  have hends : -δ≤Real.log N := (neg_nonpos.mpr hδ).trans (Real.log_nonneg (by exact_mod_cast hN))
  calc
    _ = ∫ u in S, ‖logWindowSum a (Icc 1 N) δ u‖^2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by rw [supp u hu,norm_zero,zero_pow (by decide : 2≠0)])).symm
    _ ≤ ∫ _ in S, (2*M)^2 := setIntegral_mono_on hi.integrableOn
      (integrableOn_const hS) measurableSet_Icc (fun u _ => pow_le_pow_left₀ (norm_nonneg _) (bound u) 2)
    _ = _ := by rw [setIntegral_const,Real.volume_real_Icc_of_le hends,smul_eq_mul,sub_neg_eq_add]

/-- A zero-width estimate for the local energy at every finite length
and every bandwidth. No averaging over lengths or window positions is needed
in the bound for the underlying prefixes. -/
theorem bandEnergy_le_width {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ), 1≤N → ∀ δ : ℝ, 0≤δ →
      bandEnergy N δ ≤ C*(Real.log N+δ)*((N:ℝ)^(zetaZeroWidth+ε))^2 := by
  obtain ⟨K,hK,hbound⟩ := exists_norm_moebiusPoly_line_le hε
  let r := zetaZeroWidth+ε
  refine ⟨16*K^2,by positivity,fun N hN δ hδ => ?_⟩
  have hb (k : ℕ) (hk : k≤N) : ‖∑ n ∈ Icc 1 k, amplitude n‖ ≤ 2*(N:ℝ)^r*K := by
    rcases Nat.eq_zero_or_pos k with rfl|hk₀
    · simp only [show Icc 1 0=∅ by decide,sum_empty,norm_zero]
      positivity
    have hh := hbound k 0 hk₀
    have he := critical_moebius_logPoly k 0
    simp only [mul_zero,logPoly,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one] at he
    rw [he] at hh
    simp only [abs_zero,add_zero,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hk) (add_nonneg zetaZeroWidth_nonneg hε.le))
      (by norm_num)) hK)
  exact (window_energy_le_of_prefix_bound amplitude hN hδ hb).trans_eq (by dsimp only [r]; ring)

/-- At reciprocal bandwidth the critical-line time moment costs at most
5πT²/2 times the physical short-window energy. -/
theorem critical_moment_le_short_ratio_energy (N : ℕ) {T : ℝ} (hT : 1≤T) :
    (∫ t in (1:ℝ)..T, ‖moebiusPoly N (linePoint t)‖^2) ≤
      (5*Real.pi/2)*T^2*bandEnergy N T⁻¹ := by
  let c := 2*Real.pi
  let F (w : ℝ) := ‖logPoly amplitude (Icc 1 N) w‖^2
  let W := T/c
  have hc : 0<c := by dsimp only [c]; positivity
  have ht : 0<T := zero_lt_one.trans_le hT
  have hg := integral_Icc_normSq_logPoly_le_window amplitude (Icc 1 N) (inv_pos.mpr ht)
    (W:=W) (by dsimp only [W,c]; field_simp [ht.ne',Real.pi_ne_zero]; ring_nf; norm_num)
  have hpoint (t : ℝ) : ‖moebiusPoly N (linePoint t)‖^2=F (t/(-c)) := by
    have he := critical_moebius_logPoly N (t/(-c))
    rw [show -(2*Real.pi)*(t/(-c))=t by change -c*(t/(-c))=t; field_simp [hc.ne']] at he
    rw [he]
  have hFI : Continuous F := (continuous_logPoly amplitude (Icc 1 N)).norm.pow 2
  have hlow : T/(-c)≤1/(-c) := by
    simp only [div_neg,neg_le_neg_iff]
    exact div_le_div_of_nonneg_right hT hc.le
  have hsub : Set.Ioc (T/(-c)) (1/(-c)) ⊆ Set.Icc (-W) W := by
    intro w hw
    refine ⟨?_,?_⟩
    · simpa only [W,div_neg] using hw.1.le
    · exact hw.2.trans ((div_nonpos_of_nonneg_of_nonpos zero_le_one (neg_nonpos.mpr hc.le)).trans
        (div_nonneg ht.le hc.le))
  have hi : (∫ w in Set.Ioc (T/(-c)) (1/(-c)), F w)≤∫ w in Set.Icc (-W) W, F w :=
    setIntegral_mono_set (hFI.continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall (fun w => sq_nonneg ‖logPoly amplitude (Icc 1 N) w‖))
    (Filter.Eventually.of_forall (fun w hw => hsub hw))
  calc
    _ = ∫ t in (1:ℝ)..T, F (t/(-c)) := intervalIntegral.integral_congr fun t _ => hpoint t
    _ = c*(∫ w in Set.Ioc (T/(-c)) (1/(-c)), F w) := by
      rw [intervalIntegral.integral_comp_div F (neg_ne_zero.mpr hc.ne'),smul_eq_mul,
        intervalIntegral.integral_symm (T/(-c)) (1/(-c)),intervalIntegral.integral_of_le hlow,neg_mul_neg]
    _ ≤ c*((5/(4*(T⁻¹)^2))*bandEnergy N T⁻¹) := mul_le_mul_of_nonneg_left (hi.trans hg) hc.le
    _ = _ := by dsimp only [c]; field_simp [ht.ne']; ring

/-- At polynomial length, arbitrarily small losses suffice in the
zero-width slope of the short-ratio energy, even uniformly in height. -/
theorem short_ratio_energy_at_polynomial_length {θ ε : ℝ} (hθ : 0<θ) (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T →
      bandEnergy ⌊T^θ⌋₊ T⁻¹≤C*T^(ε+2*zetaZeroWidth*θ) := by
  let η := ε/(3*θ)
  have hη : 0<η := div_pos hε (mul_pos (by norm_num) hθ)
  obtain ⟨A,hA,ha⟩ := bandEnergy_le_width hη
  refine ⟨A*(1+η⁻¹),by positivity,fun T hT => ?_⟩
  let N := ⌊T^θ⌋₊
  let r := zetaZeroWidth+η
  have ht := zero_lt_one.trans_le hT
  have hN : 1≤N := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hT hθ.le)
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hle : (N:ℝ)≤T^θ := Nat.floor_le (Real.rpow_nonneg ht.le _)
  have hr : 0≤r := add_nonneg zetaZeroWidth_nonneg hη.le
  have hlog : Real.log N+T⁻¹ ≤ (1+η⁻¹)*(N:ℝ)^η := by
    have hl := Real.log_natCast_le_rpow_div N hη
    have hsmall : T⁻¹≤(N:ℝ)^η := (inv_le_one_of_one_le₀ hT).trans (Real.one_le_rpow hn hη.le)
    rw [div_eq_mul_inv] at hl
    linarith only [hl,hsmall]
  have hprod : (N:ℝ)^η*((N:ℝ)^r)^2=(N:ℝ)^(η+r+r) := by
    rw [Real.rpow_add (zero_lt_one.trans_le hn) (η+r) r,Real.rpow_add (zero_lt_one.trans_le hn) η r,sq,mul_assoc]
  have hpow : (N:ℝ)^(η+r+r)≤T^(ε+2*zetaZeroWidth*θ) := by
    refine (Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by positivity : 0≤η+r+r)).trans_eq ?_
    rw [←Real.rpow_mul ht.le]
    congr 1
    dsimp only [η,r]
    field_simp [hθ.ne']
    ring
  calc
    _ ≤ A*(Real.log N+T⁻¹)*((N:ℝ)^r)^2 := ha N hN _ (inv_nonneg.mpr ht.le)
    _ ≤ A*((1+η⁻¹)*(N:ℝ)^η)*((N:ℝ)^r)^2 := by gcongr
    _ = (A*(1+η⁻¹))*((N:ℝ)^η*((N:ℝ)^r)^2) := by ring
    _ ≤ _ := by rw [hprod]; exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Growth of the local Gram spectrum along arbitrarily long polynomial
sections, with a height sequence allowed to depend on the length. -/
def shortRatioGrowth (β : ℝ) : Prop :=
  ∃ K : ℝ, 0≤K ∧ ∀ θ₀ : ℝ, 0<θ₀ → ∃ θ : ℝ, θ₀≤θ ∧ ∃ C : ℝ, 0≤C ∧
    ∃ᶠ T : ℝ in atTop, bandEnergy ⌊T^θ⌋₊ T⁻¹≤C*T^(K+2*β*θ)

/-- The least nonnegative short-ratio growth slope is exactly the width
of the zeta zeros. The central Fourier band recovers the converse even
from a sparse sequence of heights for each length. -/
theorem shortRatioGrowth_iff_zero_width {β : ℝ} (hβ : 0≤β) :
    shortRatioGrowth β ↔ zetaZeroWidth≤β := by
  constructor
  · rintro ⟨K,hK,hgrowth⟩
    apply zetaZeroWidth_le_of_cofinal_pure_moebius_slope hβ (K:=2+K) (by linarith)
    intro θ₀ hθ₀
    obtain ⟨θ,hθ,C,hC,hfreq⟩ := hgrowth θ₀ hθ₀
    refine ⟨θ,hθ,(5*Real.pi/2)*C,by positivity,?_⟩
    apply (hfreq.and_eventually (eventually_ge_atTop (1:ℝ))).mono
    rintro T ⟨hb,hT⟩
    have hpos := zero_lt_one.trans_le hT
    simp_rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
    calc
      _ ≤ (5*Real.pi/2)*T^2*bandEnergy ⌊T^θ⌋₊ T⁻¹ := critical_moment_le_short_ratio_energy _ hT
      _ ≤ (5*Real.pi/2)*T^2*(C*T^(K+2*β*θ)) := by gcongr
      _ = ((5*Real.pi/2)*C)*T^(2+K+2*β*θ) := by
        rw [show 2+K+2*β*θ=2+(K+2*β*θ) by ring,Real.rpow_add hpos 2 (K+2*β*θ),Real.rpow_two]
        ring
  · intro hb
    refine ⟨1,zero_le_one,fun θ hθ => ⟨θ,le_rfl,?_⟩⟩
    obtain ⟨C,hC,hbound⟩ := short_ratio_energy_at_polynomial_length hθ zero_lt_one
    refine ⟨C,hC,Filter.Eventually.frequently ?_⟩
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    exact (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (by nlinarith only [mul_nonneg (sub_nonneg.mpr hb) hθ.le])) hC)

/-- Purely arithmetic triangular form using only reduced ratios whose
logarithmic distance is strictly less than the reciprocal height. -/
def shortRatioForm (N : ℕ) (T : ℝ) : ℝ :=
  T⁻¹*(∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n) +
    ∑ q ∈ (primitiveRatioPairs N).filter (fun q => |Real.log q.1-Real.log q.2|<T⁻¹),
      atom N q.1 q.2*(T⁻¹-|Real.log q.1-Real.log q.2|)

theorem shortRatioForm_eq_bandEnergy (N : ℕ) {T : ℝ} (hT : 0<T) :
    shortRatioForm N T=bandEnergy N T⁻¹ := by
  rw [shortRatioForm,bandEnergy,short_interval_spectrum,max_eq_left (inv_nonneg.mpr hT.le),sum_filter]
  congr 1
  apply sum_congr rfl
  intro q _
  split_ifs with h
  · rw [max_eq_left (sub_nonneg.mpr h.le)]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt h)),mul_zero]

/-- RH is equivalent to one polynomial height bound for the finite
short-ratio form. Pairs at logarithmic distance at least 1/T are absent. -/
theorem riemannHypothesis_iff_short_ratio_form :
    RiemannHypothesis ↔ ∃ K : ℝ, 0≤K ∧ ∀ θ₀ : ℝ, 0<θ₀ → ∃ θ : ℝ, θ₀≤θ ∧ ∃ C : ℝ, 0≤C ∧
      ∃ᶠ T : ℝ in atTop, shortRatioForm ⌊T^θ⌋₊ T≤C*T^K := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ←zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl,←shortRatioGrowth_iff_zero_width le_rfl]
  unfold shortRatioGrowth
  simp only [mul_zero,zero_mul,add_zero]
  have he (θ C K : ℝ) : (∃ᶠ T : ℝ in atTop, bandEnergy ⌊T^θ⌋₊ T⁻¹≤C*T^K) ↔
      ∃ᶠ T : ℝ in atTop, shortRatioForm ⌊T^θ⌋₊ T≤C*T^K := by
    apply Filter.frequently_congr
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    rw [shortRatioForm_eq_bandEnergy _ hT]
  simp_rw [he]

#print axioms critical_moebius_logPoly
#print axioms shortRatioForm_eq_bandEnergy
#print axioms short_ratio_energy_at_polynomial_length
#print axioms shortRatioGrowth_iff_zero_width
#print axioms riemannHypothesis_iff_short_ratio_form

#print axioms window_energy_le_of_prefix_bound
#print axioms bandEnergy_le_width
#print axioms critical_moment_le_short_ratio_energy
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
