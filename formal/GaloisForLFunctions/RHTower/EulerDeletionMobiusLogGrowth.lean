import GaloisForLFunctions.RHTower.EulerDeletionMobiusCurrentEscape
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# Growing Möbius windows and superlogarithmic current escape

The arbitrary logarithmic saving for the actual harmonic Möbius sum keeps
its unit endpoint defect throughout growing source windows. Their full Gram
energy forces current growth beyond every fixed logarithmic power at each
off-line zero. A cofinal logarithmic ceiling remains an independent RH target.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionMobiusLogGrowth
open DeletionMobiusCurrent DeletionMixedCurrent DeletionReflectedEnergy
open DeletionReflectedGram DeletionJointCirculation DeletionChronologicalLimit

/-- A growing ordinary source window, measured by a fixed logarithmic power. -/
def logWindow (m N : ℕ) : ℕ := ⌊Real.log (N : ℝ)^m⌋₊

/-- Explicit uniform error for every prefix inside the actual arithmetic initial window. -/
theorem sourcePrefix_error_le {s : ℂ} (hs : 0<s.re) {N K : ℕ}
    (hK : 0<K) (hKN : K≤N) :
    ‖sourcePrefix N s K+1‖ ≤ (K : ℝ)*|deningerHarmonicPartial N| := by
  rw [sourcePrefix_initial hK hKN s, sub_add_cancel, norm_mul]
  have hk (n : ℕ) : ‖kernel s n‖≤1 := by
    rw [norm_kernel]
    have hn : (0 : ℝ)≤n := by positivity
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hsum : ‖∑ n ∈ Finset.range K, kernel s n‖ ≤ (K : ℝ) := by
    calc _ ≤ ∑ n ∈ Finset.range K, ‖kernel s n‖ := norm_sum_le _ _
         _ ≤ ∑ _n ∈ Finset.range K, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hk n)
         _ = (K : ℝ) := by simp
  simpa only [Complex.norm_real, Real.norm_eq_abs, mul_comm] using
    mul_le_mul_of_nonneg_left hsum (norm_nonneg (deningerHarmonicPartial N : ℂ))

private theorem log_tendsto :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Every fixed logarithmic window eventually lies in the exact divisor-inversion region. -/
theorem logWindow_le_eventually (m : ℕ) : ∀ᶠ N : ℕ in atTop, logWindow m N≤N := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (burnolEventually_log_pow_le_rpow (show (0 : ℝ)<1 by norm_num) m)
  filter_upwards [h] with N hN
  apply Nat.floor_le_of_le
  simpa using hN

/-- One cutoff controls every positive prefix in the growing window simultaneously. -/
theorem sourcePrefix_logWindow_uniform {s : ℂ} (hs : 0<s.re) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, 0<K → K≤logWindow m N →
      ‖sourcePrefix N s K+1‖≤1/2 ∧ 1/2≤‖sourcePrefix N s K‖ := by
  have ht := (Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero m).norm
  have hh := ht.eventually (eventually_lt_nhds (show ‖(0 : ℝ)‖<(1/2 : ℝ) by norm_num))
  filter_upwards [hh, logWindow_le_eventually m, log_tendsto.eventually_ge_atTop 1]
    with N hN hwindow hlog K hK hKN
  have hlog0 : 0≤Real.log (N : ℝ) := by linarith
  have hfloor : (logWindow m N : ℝ)≤Real.log (N : ℝ)^m := Nat.floor_le (by positivity)
  have hsmall : ‖sourcePrefix N s K+1‖≤1/2 := by
    calc _ ≤ (K : ℝ)*|deningerHarmonicPartial N| := sourcePrefix_error_le hs hK (hKN.trans hwindow)
         _ ≤ Real.log (N : ℝ)^m*|deningerHarmonicPartial N| :=
           mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr hKN).trans hfloor) (abs_nonneg _)
         _ ≤ 1/2 := by
           simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 m)] using hN.le
  have htri : (1 : ℝ)≤‖sourcePrefix N s K+1‖+‖sourcePrefix N s K‖ := by
    simpa using norm_sub_le (sourcePrefix N s K+1) (sourcePrefix N s K)
  exact ⟨hsmall,by linarith⟩

private theorem sum_weight_increments (s : ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range K, (weight s (n+1)-weight s n))=weight s K-1 := by
  induction K with
  | zero => simp [weight]
  | succ K ih => rw [Finset.sum_range_succ, ih]; ring

/-- A growing, uniformly nonzero source window gives a quantitative full-current floor. -/
theorem sourceCurrent_logWindow_lower (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : 1/2<rho.1.re) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (weight rho.1 (logWindow m N)-1)/4≤(sourceCurrent N rho.1).re := by
  filter_upwards [sourcePrefix_logWindow_uniform
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) m] with N hN
  have hsum : (weight rho.1 (logWindow m N)-1)/4 ≤ energyHead N rho.1 (logWindow m N) := by
    rw [← sum_weight_increments, Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    have hp := (hN (n+1) (Nat.succ_pos n) (Nat.succ_le_iff.mpr (Finset.mem_range.mp hn))).2
    have hw : 0≤weight rho.1 (n+1)-weight rho.1 n := by
      apply sub_nonneg.mpr
      exact Real.rpow_le_rpow (by positivity) (by push_cast; linarith)
        (by unfold exponent; linarith)
    change (weight rho.1 (n+1)-weight rho.1 n)/4 ≤
      (weight rho.1 (n+1)-weight rho.1 n)*‖sourcePrefix N rho.1 (n+1)‖^2
    have hsq : (1/4 : ℝ)≤‖sourcePrefix N rho.1 (n+1)‖^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hw]
  exact hsum.trans (mixed_energy_prefix_le_current (Finset.range N) coefficient rho hs.le _)

private theorem weight_logWindow_lower {s : ℂ} (hs : 1/2<s.re) (q : ℕ) :
    ∃ m : ℕ, ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ)^(q+1)≤weight s (logWindow m N) := by
  have ha : 0<exponent s := by unfold exponent; linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (((q+1 : ℕ) : ℝ)/exponent s)
  have hexp : ((q+1 : ℕ) : ℝ)≤(m : ℝ)*exponent s :=
    (div_lt_iff₀ ha).mp hm |>.le
  refine ⟨m,?_⟩
  filter_upwards [log_tendsto.eventually_ge_atTop 1] with N hlog
  have hlog0 : 0≤Real.log (N : ℝ) := by linarith
  calc Real.log (N : ℝ)^(q+1) = Real.log (N : ℝ)^(((q+1 : ℕ) : ℝ)) :=
         (Real.rpow_natCast _ _).symm
       _ ≤ Real.log (N : ℝ)^((m : ℝ)*exponent s) :=
         Real.rpow_le_rpow_of_exponent_le hlog hexp
       _ = (Real.log (N : ℝ)^m)^exponent s := Real.rpow_natCast_mul hlog0 m _
       _ ≤ weight s (logWindow m N) :=
         Real.rpow_le_rpow (by positivity) (Nat.lt_floor_add_one _).le ha.le

/-- The right-half current divided by any fixed logarithmic power tends to positive infinity. -/
theorem sourceCurrent_div_log_pow_tendsto (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : 1/2<rho.1.re) (q : ℕ) :
    Tendsto (fun N : ℕ => (sourceCurrent N rho.1).re / Real.log (N : ℝ)^q) atTop atTop := by
  obtain ⟨m,hm⟩ := weight_logWindow_lower hs q
  have hlow : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ)/8≤(sourceCurrent N rho.1).re/Real.log (N : ℝ)^q := by
    filter_upwards [hm, sourceCurrent_logWindow_lower rho hs m,
      log_tendsto.eventually_ge_atTop 2] with N hweight hcurrent hlog
    have hlogpos : 0<Real.log (N : ℝ) := by linarith
    have hpow : 1≤Real.log (N : ℝ)^q := one_le_pow₀ (by linarith)
    apply (le_div_iff₀ (pow_pos hlogpos q)).mpr
    have htwice : (2 : ℝ)≤Real.log (N : ℝ)^q*Real.log (N : ℝ) := by nlinarith
    rw [pow_succ] at hweight
    nlinarith
  exact tendsto_atTop_mono' atTop hlow (log_tendsto.atTop_div_const (by norm_num : (0 : ℝ)<8))

/-- Every off-line zero forces absolute current escape beyond every logarithmic power. -/
theorem abs_sourceCurrent_div_log_pow_tendsto (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : rho.1.re≠1/2) (q : ℕ) :
    Tendsto (fun N : ℕ => |(sourceCurrent N rho.1).re| / Real.log (N : ℝ)^q) atTop atTop := by
  have hright (r : RiemannGaussian.NontrivialZetaZero) (hr : 1/2<r.1.re) :
      Tendsto (fun N : ℕ => |(sourceCurrent N r.1).re| / Real.log (N : ℝ)^q) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (sourceCurrent_div_log_pow_tendsto r hr q)
    filter_upwards [log_tendsto.eventually_ge_atTop 1] with N hN
    exact div_le_div_of_nonneg_right (le_abs_self _) (pow_nonneg (by linarith) q)
  rcases lt_or_gt_of_ne hs with hleft | hr
  · let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
    have he : r.1=partner rho.1 := rfl
    have hr : 1/2<r.1.re := by
      rw [he]
      simp only [partner, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
      linarith
    simpa only [he, sourceCurrent_partner, Complex.neg_re, abs_neg] using hright r hr
  · exact hright rho hr

/-- Even a zero-dependent logarithmic ceiling on cofinally many actual currents forces the line. -/
theorem sourceCurrent_cofinally_log_bounded_iff (rho : RiemannGaussian.NontrivialZetaZero) :
    (∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧
      |(sourceCurrent N rho.1).re|≤B*Real.log (N : ℝ)^q) ↔ rho.1.re=1/2 := by
  constructor
  · rintro ⟨q,B,hB⟩
    by_contra hr
    have he := (abs_sourceCurrent_div_log_pow_tendsto rho hr q).eventually_gt_atTop B
    obtain ⟨K,hK⟩ := eventually_atTop.mp (he.and (log_tendsto.eventually_ge_atTop 1))
    obtain ⟨N,hKN,hN⟩ := hB K
    have h := hK N hKN
    exact (not_le.mpr h.1) ((div_le_iff₀ (pow_pos (by linarith : 0<Real.log (N : ℝ)) q)).mpr hN)
  · intro hr
    refine ⟨0,0,fun K => ⟨K,le_rfl,?_⟩⟩
    rw [sourceCurrent, quadraticCurrent_of_re_half _ _ hr]
    simp

/-- Exact RH receiver requiring only cofinal logarithmic ceilings for the literal all-cross source. -/
theorem riemannHypothesis_iff_mobius_current_cofinally_log_bounded :
    RiemannHypothesis ↔ ∀ rho : RiemannGaussian.NontrivialZetaZero,
      ∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧
        |(sourceCurrent N rho.1).re|≤B*Real.log (N : ℝ)^q := by
  constructor
  · intro hRH rho
    exact (sourceCurrent_cofinally_log_bounded_iff rho).2 (hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2)
  · intro h s hz ht hs1
    let rho : RiemannGaussian.NontrivialZetaZero := ⟨s,hz,ht,hs1⟩
    exact (sourceCurrent_cofinally_log_bounded_iff rho).1 (h rho)

end RHTower.DeletionMobiusLogGrowth
end
