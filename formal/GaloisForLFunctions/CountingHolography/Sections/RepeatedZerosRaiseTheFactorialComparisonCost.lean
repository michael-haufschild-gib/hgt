import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Derivatives at critical zeros of factorial comparisons

The Mellin error multiplied by the scale to the power s has a uniform
bound on each closed substrip. Cauchy's inequality then constrains the
value of the factorial frequency polynomial at every critical zero.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Complex MeasureTheory Filter Finset Set Topology Zeta23
open ArithmeticOrientationGeometry RenormalizedIntersectionTheory

private def residual {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (X : ℝ) (s : ℂ) :=
  Complex.exp ((Real.log X:ℝ)*s) *
    (mellin squarePrimeWeight s + NymanMellin.freqPoly c a s * riemannZeta s / s)

private theorem norm_scale {X : ℝ} (hX : 0 < X) (s : ℂ) :
    ‖Complex.exp ((Real.log X:ℝ)*s)‖ = X^s.re := by
  rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Real.rpow_def_of_pos hX]

private theorem residual_bound {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    {X B : ℝ} (hX : 0 < X)
    (hE : IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0))
    (hcap : ∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B)
    (hmass : (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X)
    {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    s.re*‖residual c a X s‖ ≤ B := by
  have h := mellin_difference_initial_interval_bound hs hs'.le (inv_pos.mpr hX)
    (mellinConvergent_squarePrimeWeight s) (NymanMellin.mellinConvergent_nymanCombination c a ha hs hs')
    hE hcap (by simpa only [div_eq_mul_inv] using hmass)
  rw [NymanMellin.mellin_nymanCombination c a ha hs hs',sub_neg_eq_add,Real.inv_rpow hX.le,
    ← div_eq_mul_inv] at h
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hX s.re)).mp ((le_div_iff₀ hs).mp h)
  rw [residual,norm_mul,norm_scale hX]
  linarith only [hh]

private theorem freq_differentiable {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) :
    Differentiable ℂ (NymanMellin.freqPoly c a) := by
  rw [NymanMellin.freqPoly_eq_expSum c a ha]
  fun_prop

/-- The normalized Mellin error has all derivatives bounded on the critical line
by Cauchy estimates with a common quarter-radius disk. -/
private theorem residual_jet_bound (k : ℕ) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (ha : ∀ j, 0 < a j) {X B : ℝ} (hX : 0 < X)
    (hE : IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0))
    (hcap : ∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B)
    (hmass : (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X)
    {ρ : ℂ} (hρ : ρ.re=1/2) : ‖iteratedDeriv k (residual c a X) ρ‖ ≤ (k.factorial:ℝ)*(4*B)/(1/4:ℝ)^k := by
  let U := {s : ℂ | 0 < s.re ∧ s.re < 1}
  have hball {s : ℂ} (hs : s ∈ Metric.closedBall ρ (1/4:ℝ)) : 1/4 ≤ s.re ∧ s.re ≤ 3/4 := by
    have hd := (Complex.abs_re_le_norm (s-ρ)).trans (by simpa only [← dist_eq_norm] using Metric.mem_closedBall.mp hs)
    rw [Complex.sub_re,hρ,abs_le] at hd
    constructor <;> linarith only [hd.1,hd.2]
  have hu : Metric.closedBall ρ (1/4:ℝ) ⊆ U := fun s hs => by
    obtain ⟨h₁,h₂⟩ := hball hs
    exact ⟨by linarith only [h₁],by linarith only [h₂]⟩
  have hr : DifferentiableOn ℂ (residual c a X) U := by
    intro s hs
    have hs₀ : s ≠ 0 := fun e => hs.1.ne' (by rw [e]; rfl)
    have hs₁ : s ≠ 1 := fun e => hs.2.ne (by rw [e]; rfl)
    have he : Differentiable ℂ (fun t : ℂ => Complex.exp ((Real.log X:ℝ)*t)) := by fun_prop
    exact ((he s).mul ((differentiable_mellin_squarePrimeWeight s).add
      ((((freq_differentiable c a ha s).mul (differentiableAt_riemannZeta hs₁)).div
        (differentiableAt_id) hs₀)))).differentiableWithinAt
  have hb (s : ℂ) (hs : s ∈ Metric.sphere ρ (1/4:ℝ)) : ‖residual c a X s‖ ≤ 4*B := by
    have hd := Metric.sphere_subset_closedBall hs
    have h := residual_bound c a ha hX hE hcap hmass (hu hd).1 (hu hd).2
    linarith only [h,mul_le_mul_of_nonneg_right (hball hd).1 (norm_nonneg (residual c a X s))]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num : (0:ℝ)<1/4)
    (hr.diffContOnCl_ball hu) hb

/-- A critical zero fixes the first-order interpolation target of the
factorial frequency polynomial, including the derivative of zeta. -/
theorem factorial_frequency_at_critical_zero {ρ : ℂ} (hζ : riemannZeta ρ=0) (hρ : ρ.re=1/2)
    {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    {X B : ℝ} (hX : 0 < X)
    (hE : IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0))
    (hcap : ∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B)
    (hmass : (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X) :
    X^(1/2:ℝ)*‖(Real.log X:ℂ)*mellin squarePrimeWeight ρ + deriv (mellin squarePrimeWeight) ρ +
      NymanMellin.freqPoly c a ρ * deriv riemannZeta ρ / ρ‖ ≤ 16*B := by
  have h₀ : ρ ≠ 0 := by intro e; rw [e,Complex.zero_re] at hρ; norm_num at hρ
  have h₁ : ρ ≠ 1 := by intro e; rw [e,Complex.one_re] at hρ; norm_num at hρ
  have hzeta := (freq_differentiable c a ha ρ).hasDerivAt.mul (differentiableAt_riemannZeta h₁).hasDerivAt
  have hcore := (differentiable_mellin_squarePrimeWeight ρ).hasDerivAt.add (hzeta.div (hasDerivAt_id ρ) h₀)
  have hscale := ((hasDerivAt_id ρ).const_mul ((Real.log X:ℝ):ℂ)).cexp
  have hd := hscale.mul hcore
  change HasDerivAt (residual c a X) _ ρ at hd
  have he : deriv (residual c a X) ρ = Complex.exp ((Real.log X:ℝ)*ρ) *
      ((Real.log X:ℂ)*mellin squarePrimeWeight ρ+deriv (mellin squarePrimeWeight) ρ+
        NymanMellin.freqPoly c a ρ*deriv riemannZeta ρ/ρ) := by
    rw [hd.deriv]
    simp only [Pi.add_apply,Pi.div_apply,Pi.mul_apply,id_eq,hζ,mul_zero,zero_div,add_zero,zero_add,sub_zero,zero_mul,mul_one]
    field_simp
    ring
  have h := residual_jet_bound 1 c a ha hX hE hcap hmass hρ
  rw [iteratedDeriv_one] at h
  norm_num only [Nat.factorial_one,Nat.cast_one,one_mul,pow_one] at h
  rw [show 4*B/(1/4:ℝ)=16*B by ring] at h
  rwa [he,norm_mul,norm_scale hX,hρ] at h

/-- Every seen critical zero at which the zeta derivative vanishes raises
the eventual cost by a factor of log X. The constant is independent of the
number, coefficients and scales of the factorial kernels. -/
theorem repeated_zero_factorial_cost {ρ : ℂ} (hρ : ρ ∈ criticalSeen) (hd : deriv riemannZeta ρ=0) :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ X : ℝ in atTop,
      ∀ {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ), (∀ j, 0 < a j) →
        ∀ B : ℝ, IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0) →
        (∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B) →
        (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X →
        k*X^(1/2:ℝ)*Real.log X ≤ B := by
  let W := mellin squarePrimeWeight ρ
  let d := deriv (mellin squarePrimeWeight) ρ
  have hw : 0 < ‖W‖ := norm_pos_iff.mpr (mellin_squarePrimeWeight_ne_zero hρ)
  refine ⟨‖W‖/32,div_pos hw (by norm_num),?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (2*‖d‖/‖W‖))] with X hX hlog
  intro m c a ha B hE hcap hmass
  have hX' := zero_lt_one.trans_le hX
  have h := factorial_frequency_at_critical_zero hρ.1.1 hρ.2.1 c a ha hX' hE hcap hmass
  rw [hd,mul_zero,zero_div,add_zero] at h
  have htriangle := norm_sub_norm_le ((Real.log X:ℂ)*W) (-d)
  rw [norm_neg,sub_neg_eq_add,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hX)] at htriangle
  have ht : ‖W‖*Real.log X/2 ≤ ‖(Real.log X:ℂ)*W+d‖ := by
    linarith only [htriangle,(div_le_iff₀ hw).mp hlog]
  have hr := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hX'.le (1/2:ℝ))
  change X^(1/2:ℝ)*‖(Real.log X:ℂ)*W+d‖ ≤ 16*B at h
  linarith only [hr,h]

/-- The leading coefficient controls any fixed polynomial on the positive real ray. -/
private theorem polynomial_ray_lower (k : ℕ) (v : ℕ → ℂ) (hv : v k≠0) :
    ∀ᶠ L : ℝ in atTop, ‖v k‖*L^k/2 ≤ ‖∑ i ∈ range (k+1), (L:ℂ)^i*v i‖ := by
  cases k with
  | zero =>
    filter_upwards [] with L
    simp only [pow_zero,zero_add,range_one,sum_singleton,one_mul]
    linarith only [norm_nonneg (v 0)]
  | succ k =>
    let A := ∑ i ∈ range (k+1), ‖v i‖
    have hpos := norm_pos_iff.mpr hv
    filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (2*A/‖v (k+1)‖)] with L hL hbig
    have hL' := zero_le_one.trans hL
    let T := ∑ i ∈ range (k+1), (L:ℂ)^i*v i
    have hT : ‖T‖≤L^k*A := by
      refine (norm_sum_le _ _).trans ?_
      rw [show L^k*A=∑ i ∈ range (k+1), L^k*‖v i‖ by rw [A,mul_sum]]
      refine sum_le_sum fun i hi => ?_
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL']
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (Nat.le_of_lt_succ (mem_range.mp hi))) (norm_nonneg _)
    have htri := norm_sub_norm_le ((L:ℂ)^(k+1)*v (k+1)) (-T)
    rw [norm_neg,sub_neg_eq_add,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL'] at htri
    rw [sum_range_succ,add_comm T]
    have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hpos).mp hbig) (pow_nonneg hL' k)
    rw [pow_succ] at htri ⊢
    linarith only [hT,htri,h]

/-- A zero of order greater than k forces a k-th logarithmic loss in
every finite factorial approximation of the square prime weight. -/
theorem factorial_cost_at_critical_zero_of_order {ρ : ℂ} (hρ : ρ ∈ criticalSeen) {k : ℕ}
    (hk : ((k+1:ℕ):ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ d : ℝ, 0<d ∧ ∀ᶠ X : ℝ in atTop,
      ∀ {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ), (∀ j, 0<a j) →
        ∀ B : ℝ, IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0) →
        (∀ v>0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖≤B) →
        (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖)≤B/X →
        d*X^(1/2:ℝ)*(Real.log X)^k≤B := by
  let W := mellin squarePrimeWeight
  let v := fun i : ℕ => (k.choose i:ℂ)*iteratedDeriv (k-i) W ρ
  let K := (k.factorial:ℝ)*4/(1/4:ℝ)^k
  have hK : 0<K := by dsimp only [K]; positivity
  have hv : v k≠0 := by simpa [v,W] using mellin_squarePrimeWeight_ne_zero hρ
  have h₀ : ρ≠0 := fun e => by have h := hρ.2.1; rw [e] at h; norm_num at h
  have h₁ : ρ≠1 := fun e => by have h := hρ.2.1; rw [e] at h; norm_num at h
  have hW : AnalyticAt ℂ W ρ :=
    (differentiable_mellin_squarePrimeWeight.differentiableOn.analyticOnNhd isOpen_univ) ρ (mem_univ _)
  have hZ : AnalyticAt ℂ riemannZeta ρ := HTGeometry.analyticAt_riemannZeta h₁
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hZ).mp hk
  refine ⟨‖v k‖/(2*K),div_pos (norm_pos_iff.mpr hv) (mul_pos two_pos hK),?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually (polynomial_ray_lower k v hv)]
    with X hX hpoly
  intro m c a ha B hE hcap hmass
  let L : ℂ := Real.log X
  let E := fun z : ℂ => Complex.exp (L*z)
  let G := fun z : ℂ => E z*(NymanMellin.freqPoly c a z/z)
  have hExp : AnalyticAt ℂ E ρ := by dsimp only [E]; fun_prop
  have hFreq := ((freq_differentiable c a ha).differentiableOn.analyticOnNhd isOpen_univ) ρ (mem_univ _)
  have hG : AnalyticAt ℂ G ρ := hExp.mul (hFreq.div analyticAt_id h₀)
  have he : residual c a X=fun z => E z*W z+G z*riemannZeta z := by
    funext z; dsimp only [residual,E,G,L,W]; ring
  have hjet : iteratedDeriv k (residual c a X) ρ=E ρ*(∑ i ∈ range (k+1), L^i*v i) := by
    rw [he,iteratedDeriv_fun_add (hExp.mul hW).contDiffAt (hG.mul hZ).contDiffAt,
      iteratedDeriv_fun_mul hG.contDiffAt hZ.contDiffAt]
    have hzero : (∑ i ∈ range (k+1), (k.choose i:ℂ)*iteratedDeriv i G ρ*iteratedDeriv (k-i) riemannZeta ρ)=0 :=
      sum_eq_zero fun i _ => by rw [hz (k-i) (Nat.lt_succ_of_le (Nat.sub_le k i)),mul_zero]
    rw [hzero,add_zero,iteratedDeriv_fun_mul hExp.contDiffAt hW.contDiffAt,mul_sum]
    refine sum_congr rfl fun i _ => ?_
    dsimp only [E,v]
    rw [iteratedDeriv_cexp_const_mul]
    ring
  have h := residual_jet_bound k c a ha hX hE hcap hmass hρ.2.1
  rw [hjet,norm_mul] at h
  have heNorm : ‖E ρ‖=X^(1/2:ℝ) := (norm_scale hX ρ).trans (congrArg (X^·) hρ.2.1)
  rw [heNorm] at h
  have hlow := mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hX.le (1/2:ℝ))
  have hb : X^(1/2:ℝ)*(‖v k‖*(Real.log X)^k/2)≤B*K :=
    hlow.trans (h.trans_eq (by dsimp only [K]; ring))
  calc _ = (X^(1/2:ℝ)*(‖v k‖*(Real.log X)^k/2))/K := by ring
    _ ≤ B := (div_le_iff₀ hK).mpr hb

end GaloisForLFunctions.CountingHolography.Sections
