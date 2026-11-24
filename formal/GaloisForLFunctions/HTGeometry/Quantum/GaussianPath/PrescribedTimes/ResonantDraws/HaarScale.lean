import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.WeakCutMass
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Disorder probability before scalar occupation reaches its Haar scale -/
open Set Filter MeasureTheory ProbabilityTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open WeakBonds
noncomputable section

/-- Probability over the frozen Gaussian couplings at one specified laboratory date. -/
def prescribedScalarProbability (n : ℕ) (t : ℝ) : ℝ :=
  (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real {x | pathGateDistance n 0 x t ≤ 1/10}

private theorem middle_price (n : ℕ) (t : ℝ) :
    let N := n+2
    let h := N/2
    let d : ℕ := 2^h+2^(N-h)
    let m := Fintype.card (PrefixIndex n)
    9*log (2*gaussianDensityFloor/1800)-9*log (1+|t|)-((m:ℝ)+1)*(d:ℝ)*log 256 ≤
      log (prescribedScalarProbability n t) := by
  intro N h d m
  let a : Fin (n+1) := ⟨h-1,by dsimp only [h,N]; omega⟩
  have hl : (leftBlock a).card=h := by rw [leftBlock,Fin.card_Iic]; change h-1+1=h; dsimp [h,N]; omega
  have hr : (rightBlock a).card=N-h := by rw [rightBlock,Fin.card_Ioi]; change n+2-1-(h-1)=_; dsimp [h,N]; omega
  let c := 2*gaussianDensityFloor
  let T := 1+|t|
  let p := prescribedScalarProbability n t
  have hc : 0<c := mul_pos (by norm_num) gaussianDensityFloor_pos
  have hT : 0<T := by dsimp only [T]; positivity
  have h : c^9*(1/(1800*T))^9 ≤ ((256:ℝ)^d)^(m+1)*p := by
    dsimp only [c,T,d,m,p,prescribedScalarProbability]
    simpa only [hl,hr,Nat.cast_pow,Nat.cast_ofNat] using gaussian_weak_cut_scalar_mass n a t
  have hp : 0<p := pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) h) (by positivity)
  have hlog := log_le_log (by positivity) h
  rw [log_mul (by positivity) (by positivity),log_pow,log_pow,
    log_div one_ne_zero (by positivity),log_one,
    log_mul (by norm_num) hT.ne',log_mul (by positivity) hp.ne',log_pow,log_pow] at hlog
  change 9*log (c/1800)-9*log T-((m:ℝ)+1)*(d:ℝ)*log 256 ≤ log p
  rw [log_div hc.ne' (by norm_num)]
  push_cast at hlog
  linarith only [hlog]

private theorem normalized_middle_price :
    Tendsto (fun n : ℕ =>
      let N := n+2
      let h := N/2
      ((Fintype.card (PrefixIndex n):ℝ)+1)*((2^h+2^(N-h):ℕ):ℝ)/(2:ℝ)^N) atTop (𝓝 0) := by
  let k (n : ℕ) := (n+2)/2
  have hk : Tendsto k atTop atTop := tendsto_atTop.mpr fun b => (eventually_ge_atTop (2*b)).mono
    (fun n hn => by dsimp only [k]; omega)
  have h₁ := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).comp hk
  have h₀ := (tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)).comp hk
  have hz : Tendsto (fun n => (48*(k n:ℝ)+24)/(2:ℝ)^(k n)) atTop (𝓝 0) := by
    convert (h₁.const_mul 48).add (h₀.const_mul 24) using 1
    · funext n; simp only [Function.comp_apply,pow_one,pow_zero]; ring
    · norm_num
  apply squeeze_zero (fun _ => by positivity) _ hz
  intro n
  let N := n+2
  let h := k n
  have hl : h ≤ N-h := by dsimp [h,k,N]; omega
  have hm : Fintype.card (PrefixIndex n)+1 ≤ 24*h+12 := by
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    dsimp only [h,k]; omega
  have hd : (2^h+2^(N-h):ℕ) ≤ 2*2^(N-h) := by
    have hh := Nat.pow_le_pow_right (Nat.zero_lt_two) hl
    omega
  change ((Fintype.card (PrefixIndex n):ℝ)+1)*((2^h+2^(N-h):ℕ):ℝ)/(2:ℝ)^N ≤ _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hmid : ((Fintype.card (PrefixIndex n):ℝ)+1)*((2^h+2^(N-h):ℕ):ℝ) ≤
      (24*(h:ℝ)+12)*(2*(2:ℝ)^(N-h)) := mul_le_mul (by exact_mod_cast hm) (by exact_mod_cast hd)
        (Nat.cast_nonneg _) (by positivity)
  have hsum : N-h+h=N := Nat.sub_add_cancel (hl.trans (Nat.sub_le _ _))
  calc
    _ ≤ ((24*(h:ℝ)+12)*(2*(2:ℝ)^(N-h)))*(2:ℝ)^h := mul_le_mul_of_nonneg_right hmid (by positivity)
    _ = (48*(h:ℝ)+24)*((2:ℝ)^(N-h)*2^h) := by ring
    _ = (48*(h:ℝ)+24)*(2:ℝ)^N := by rw [←pow_add,hsum]

/-- At every date schedule with log(1+|t|)=o(2^N), the scalar-event
log probability per Hilbert-space dimension converges to zero. The
long-time scalar Haar exponent at this error is strictly negative. -/
theorem gaussian_prescribed_scalar_before_haar (t : ℕ → ℝ)
    (ht : Tendsto (fun n => log (1+|t n|)/(2:ℝ)^(n+2)) atTop (𝓝 0)) :
    Tendsto (fun n => log (prescribedScalarProbability n (t n))/(2:ℝ)^(n+2)) atTop (𝓝 0) := by
  let c := 9*log (2*gaussianDensityFloor/1800)
  have hc : Tendsto (fun n : ℕ => c/(2:ℝ)^(n+2)) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)).comp
      (tendsto_add_atTop_nat 2)).const_mul c
    simpa only [Function.comp_apply,pow_zero,mul_one_div,mul_zero] using hh
  have hb := (hc.sub (ht.const_mul 9)).sub (normalized_middle_price.mul_const (log 256))
  simp only [mul_zero,zero_mul,sub_zero] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hb tendsto_const_nhds
  · intro n
    have h := div_le_div_of_nonneg_right (middle_price n (t n)) (by positivity : 0≤(2:ℝ)^(n+2))
    dsimp only [c] at h ⊢
    refine le_trans ?_ h
    apply le_of_eq
    ring
  · intro n
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply log_nonpos measureReal_nonneg
    exact (measureReal_mono (μ:=Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1) (subset_univ _)).trans_eq probReal_univ

/-- Reaching even a prescribed exponential probability per Hilbert
dimension takes doubly exponential laboratory time. This bounds every
date on every sufficiently long prefix, including the first such date. -/
theorem gaussian_scalar_probability_deadline {b : ℝ} (hb : 0<b) (hb' : b<1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      prescribedScalarProbability n t ≤ b^(2^(n+2):ℕ) →
      -(log b)/18*((2:ℝ)^(n+2)) ≤ log (1+|t|) := by
  let c := 9*log (2*gaussianDensityFloor/1800)
  have hc : Tendsto (fun n : ℕ => c/(2:ℝ)^(n+2)) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)).comp
      (tendsto_add_atTop_nat 2)).const_mul c
    simpa only [Function.comp_apply,pow_zero,mul_one_div,mul_zero] using hh
  have hl := hc.sub (normalized_middle_price.mul_const (log 256))
  simp only [zero_mul,sub_zero] at hl
  have hneg := log_neg hb hb'
  filter_upwards [hl.eventually_const_lt (show log b/2 < 0 by linarith only [hneg])] with n hn
  intro t ht
  have hmid := middle_price n t
  have hp : 0<prescribedScalarProbability n t := by
    by_contra! hp
    have hz := le_antisymm hp (show 0 ≤ prescribedScalarProbability n t from measureReal_nonneg)
    let a : Fin (n+1) := ⟨0,Nat.succ_pos _⟩
    have hh := gaussian_weak_cut_scalar_mass n a t
    change _ ≤ _*prescribedScalarProbability n t at hh
    rw [hz,mul_zero] at hh
    exact (show 0<(2*gaussianDensityFloor)^9*(1/(1800*(1+|t|)))^9 by
      have := gaussianDensityFloor_pos
      positivity).not_ge hh
  have hupper := log_le_log hp ht
  rw [log_pow,Nat.cast_pow,Nat.cast_ofNat] at hupper
  let D := (2:ℝ)^(n+2)
  have hD : 0<D := by dsimp only [D]; positivity
  let E := ((Fintype.card (PrefixIndex n):ℝ)+1)*
    ((2^((n+2)/2)+2^((n+2)-(n+2)/2):ℕ):ℝ)
  change log b/2 < c/D-E/D*log 256 at hn
  have hprice : log b/2*D < c-E*log 256 := (lt_div_iff₀ hD).mp (by
    rw [sub_div,mul_div_right_comm E (log 256) D]
    exact hn)
  change c-9*log (1+|t|)-E*log 256 ≤ log (prescribedScalarProbability n t) at hmid
  change log (prescribedScalarProbability n t) ≤ D*log b at hupper
  change -(log b)/18*D ≤ _
  linarith only [hprice,hmid,hupper]

#print axioms gaussian_prescribed_scalar_before_haar
#print axioms gaussian_scalar_probability_deadline
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
