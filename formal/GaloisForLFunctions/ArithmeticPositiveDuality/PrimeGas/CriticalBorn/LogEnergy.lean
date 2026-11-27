import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.SublinearPacket
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Edges
import GaloisForLFunctions.RHTower.MertensSecondRealVariable

/-! # Distribution of the normalized logarithm of elementary energy -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real MeasureTheory
open scoped Topology

/-- Label cutoff with prescribed logarithmic energy uB. -/
def logEnergyCutoff (u B : ℝ) := exp (exp (u*B))

/-- Cumulative probability up to logarithmic energy uB in the packet
whose upper logarithmic energy is B. -/
def logEnergyCDF (σ u B : ℝ) :=
  (labelLaw σ (logEnergyCutoff 1 B) : Measure ℕ).real {p : ℕ | (p:ℝ)≤logEnergyCutoff u B}

theorem prime_logEnergy_event {p : ℕ} (hp : p.Prime) (u B : ℝ) :
    (p:ℝ)≤logEnergyCutoff u B ↔ log (log p)≤u*B := by
  have pp : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have lp := log_pos (show (1:ℝ)<p by exact_mod_cast hp.one_lt)
  rw [log_le_iff_le_exp lp,log_le_iff_le_exp pp,logEnergyCutoff]

private theorem cutoff_growth {u : ℝ} (hu : 0<u) : Tendsto (logEnergyCutoff u) atTop atTop :=
  tendsto_exp_atTop.comp (tendsto_exp_atTop.comp (_root_.RHTower.tendsto_const_mul_atTop_of_pos hu))

private theorem relative_cutoff {u : ℝ} (hu : u<1) :
    Tendsto (fun B => logEnergyCutoff u B / logEnergyCutoff 1 B) atTop (𝓝 0) := by
  have shrinking := tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
    (_root_.RHTower.tendsto_const_mul_atTop_of_pos (sub_pos.mpr hu)))
  have half : ∀ᶠ B : ℝ in atTop, exp (u*B) ≤ (1/2)*exp B := by
    filter_upwards [shrinking.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with B h
    change exp (-((1-u)*B)) < 1/2 at h
    rw [show -((1-u)*B)=u*B-B by ring,exp_sub,div_lt_iff₀ (exp_pos _)] at h
    exact h.le
  have grow : Tendsto (fun B => exp B-exp (u*B)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ ((_root_.RHTower.tendsto_const_mul_atTop_of_pos
      (by norm_num : (0:ℝ)<1/2)).comp tendsto_exp_atTop)
    exact half.mono fun B h => by change 1/2*exp B ≤ _; linarith only [h]
  apply (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp grow)).congr
  intro B
  simp only [Function.comp_apply,logEnergyCutoff,one_mul,neg_sub,exp_sub]

private theorem measured_ratio (σ : ℝ) {u : ℝ} (hu : 0<u) (hu' : u<1) :
    ∀ᶠ B : ℝ in atTop, logEnergyCDF σ u B =
      powerMass (1-2*σ) (logEnergyCutoff u B) / powerMass (1-2*σ) (logEnergyCutoff 1 B) := by
  filter_upwards [(cutoff_growth hu).eventually_ge_atTop 2,eventually_ge_atTop (0:ℝ)] with B uy hB
  exact initial_measured σ uy (exp_le_exp.mpr (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu'.le hB)))

private theorem harmonic_prime_sum {x : ℝ} (hx : 2≤x) :
    powerMass 0 x = _root_.RHTower.primeRecipSum ⌊x⌋₊ := by
  classical
  have xs : 0≤x := by linarith only [hx]
  have primeset : primes (cutoff x) = (Icc 0 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [mem_cutoff hx,mem_filter,mem_Icc,zero_le,true_and,Nat.le_floor_iff xs,and_comm]
  simp only [powerMass,zero_sub,rpow_neg_one,primeset,sum_filter,_root_.RHTower.primeRecipSum,
    _root_.RHTower.primeRecipWeight]

private theorem harmonic_slope {u : ℝ} (hu : 0<u) :
    Tendsto (fun B => powerMass 0 (logEnergyCutoff u B) / B) atTop (𝓝 u) := by
  have err := _root_.RHTower.tendsto_primeRecipSum_floor_sub_logLog.comp (cutoff_growth hu)
  have normed := err.div_atTop (tendsto_id : Tendsto (fun B : ℝ => B) atTop atTop)
  have lim := normed.add_const u
  rw [zero_add] at lim
  apply lim.congr'
  filter_upwards [(cutoff_growth hu).eventually_ge_atTop 2,eventually_gt_atTop (0:ℝ)] with B hx hB
  rw [harmonic_prime_sum hx]
  simp only [Function.comp_apply,id_eq,logEnergyCutoff,log_exp]
  field_simp [hB.ne'] <;> ring

/-- The probability of an interior logarithmic energy threshold tends
respectively to zero, to its fractional position, or to one. -/
theorem logEnergy_limit (σ : ℝ) {u : ℝ} (hu : 0<u) (hu' : u<1) :
    Tendsto (logEnergyCDF σ u) atTop
      (𝓝 (if σ<1/2 then 0 else if σ=1/2 then u else 1)) := by
  apply (tendsto_congr' (measured_ratio σ hu hu')).mpr
  have top := cutoff_growth (by norm_num : (0:ℝ)<1)
  rcases lt_trichotomy σ (1/2) with lo | mid | hi
  · rw [if_pos lo]
    exact subcritical_sublinear (by linarith only [lo]) top (relative_cutoff hu')
  · subst σ
    rw [if_neg (lt_irrefl _),if_pos rfl,show (1:ℝ)-2*(1/2)=0 by norm_num]
    have h := (harmonic_slope hu).div (harmonic_slope (by norm_num : (0:ℝ)<1)) one_ne_zero
    rw [div_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with B hB
    change (powerMass 0 (logEnergyCutoff u B) / B) / (powerMass 0 (logEnergyCutoff 1 B) / B) = _
    field_simp [hB.ne',(powerMass_pos 0 (logEnergyCutoff 1 B)).ne']
  · rw [if_neg hi.not_gt,if_neg hi.ne']
    exact supercritical_exhaustion (by linarith only [hi]) top (cutoff_growth hu)

/-- At the midpoint in logarithmic energy one occupation probability
of one half characterizes the full gas isometry. -/
theorem midpoint_iff_split (s : ℂ) :
    Tendsto (logEnergyCDF s.re (1/2)) atTop (𝓝 (1/2)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  have lim := logEnergy_limit s.re (by norm_num : (0:ℝ)<1/2) (by norm_num)
  constructor
  · intro h
    have eq := tendsto_nhds_unique lim h
    split_ifs at eq with h₁ h₂
    · norm_num at eq
    · exact h₂
    · norm_num at eq
  · intro h
    simpa only [h,lt_irrefl,if_false,if_pos] using lim

/-- RH is equivalent to the midpoint occupation probability tending to
one half for the elementary weights supplied by each open-strip zero. -/
theorem rh_iff_midpoint : RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val=0 →
    Tendsto (logEnergyCDF s.val.re (1/2)) atTop (𝓝 (1/2)) := by
  rw [rh_iff_unit_clock]
  have eqv (s : OpenStrip) := (elementary_haar_iff_split s.val one_ne_zero).trans
    (midpoint_iff_split s.val).symm
  exact ⟨fun h s hz => (eqv s).mp (h s hz),fun h s hz => (eqv s).mpr (h s hz)⟩

/-- One fixed binary measurement separates reflected ensembles with
limiting probability difference one at every off-line real part. -/
theorem reflected_midpoint_gap (σ : ℝ) :
    Tendsto (fun B => |logEnergyCDF σ (1/2) B - logEnergyCDF (1-σ) (1/2) B|) atTop
      (𝓝 (if σ=1/2 then 0 else 1)) := by
  have mid (r : ℝ) := logEnergy_limit r (by norm_num : (0:ℝ)<1/2) (by norm_num)
  have gap := ((mid σ).sub (mid (1-σ))).abs
  rcases lt_trichotomy σ (1/2) with lo | eq | hi
  · have r : 1/2 < 1-σ := by linarith only [lo]
    simpa only [if_pos lo,if_neg lo.ne,if_neg r.not_gt,if_neg r.ne',zero_sub,abs_neg,abs_one] using gap
  · subst σ
    simp only [show (1:ℝ)-1/2=1/2 by norm_num,sub_self,abs_zero,if_pos]
    exact tendsto_const_nhds
  · have r : 1-σ < 1/2 := by linarith only [hi]
    simpa only [if_neg hi.ne',if_neg hi.not_gt,if_pos r,sub_zero,abs_one] using gap

#print axioms prime_logEnergy_event
#print axioms logEnergy_limit
#print axioms midpoint_iff_split
#print axioms rh_iff_midpoint
#print axioms reflected_midpoint_gap

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
