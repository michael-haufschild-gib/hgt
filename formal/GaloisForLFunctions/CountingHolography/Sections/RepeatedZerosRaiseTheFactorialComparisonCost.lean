import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import GaloisForLFunctions.HTGeometry.DiskMultiplierBlaschkeDivision
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
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
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num : (0:ℝ) < 1/4)
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
    have hT : ‖T‖ ≤ L^k*A := by
      refine (norm_sum_le _ _).trans ?_
      rw [show L^k*A=∑ i ∈ range (k+1), L^k*‖v i‖ from Finset.mul_sum _ _ _]
      refine sum_le_sum fun i hi => ?_
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL']
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (Nat.le_of_lt_succ (mem_range.mp hi))) (norm_nonneg _)
    have htri := norm_sub_norm_le ((L:ℂ)^(k+1)*v (k+1)) (-T)
    rw [norm_neg,sub_neg_eq_add,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL'] at htri
    rw [Finset.sum_range_succ,add_comm T]
    have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hpos).mp hbig) (pow_nonneg hL' k)
    rw [pow_succ L k] at htri ⊢
    linarith only [hT,htri,h]

/-- A zero of order greater than k forces a k-th logarithmic loss in
every finite factorial approximation of the square prime weight. -/
theorem factorial_cost_at_critical_zero_of_order {ρ : ℂ} (hρ : ρ ∈ criticalSeen) {k : ℕ}
    (hk : ((k+1:ℕ):ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ X : ℝ in atTop,
      ∀ {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ), (∀ j, 0 < a j) →
        ∀ B : ℝ, IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0) →
        (∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B) →
        (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X →
        d*X^(1/2:ℝ)*(Real.log X)^k ≤ B := by
  let W := mellin squarePrimeWeight
  let v := fun i : ℕ => (k.choose i:ℂ)*iteratedDeriv (k-i) W ρ
  let K := (k.factorial:ℝ)*4/(1/4:ℝ)^k
  have hK : 0 < K := by dsimp only [K]; positivity
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
    rw [he,iteratedDeriv_fun_add (f := fun z => E z*W z) (g := fun z => G z*riemannZeta z)
        (n := k) (hExp.mul hW).contDiffAt (hG.mul hZ).contDiffAt,
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
  have hb : X^(1/2:ℝ)*(‖v k‖*(Real.log X)^k/2) ≤ B*K :=
    hlow.trans (h.trans_eq (by dsimp only [K]; ring))
  calc _ = (X^(1/2:ℝ)*(‖v k‖*(Real.log X)^k/2))/K := by ring
    _ ≤ B := (div_le_iff₀ hK).mpr hb

open HTGeometry

/-- Division at distinct disk zeros bounds the central value by the product
of their distances to the center. -/
private theorem center_bound_of_zeros (S : Finset ℂ) (φ : DiskMultiplier)
    (hS : ∀ a ∈ S, ‖a‖ < 1 ∧ φ.fn a = 0) : ‖φ.fn 0‖ ≤ (∏ a ∈ S, ‖a‖)*φ.bd := by
  classical
  induction S using Finset.induction_on generalizing φ with
  | empty => simpa only [Finset.prod_empty,one_mul] using φ.bd_le 0 (Metric.mem_ball_self one_pos)
  | @insert a T ha ih =>
    obtain ⟨haD,haZ⟩ := hS a (mem_insert_self _ _)
    let ψ := φ.removeNormalizedBlaschkeZero a haD haZ
    have hT (b : ℂ) (hb : b ∈ T) : ‖b‖ < 1 ∧ ψ.fn b = 0 := by
      obtain ⟨hbD,hbZ⟩ := hS b (mem_insert_of_mem hb)
      have h := φ.normalizedBlaschkeFactor_mul_removeNormalizedBlaschkeZero haD haZ hbD
      rw [hbZ,mul_eq_zero] at h
      exact ⟨hbD,h.resolve_left fun e => ha ((normalizedBlaschkeFactor_eq_zero_iff haD hbD.le).mp e ▸ hb)⟩
    have hfact := φ.normalizedBlaschkeFactor_mul_removeNormalizedBlaschkeZero haD haZ
      (show ‖(0:ℂ)‖ < 1 by simp)
    have hnorm : ‖normalizedBlaschkeFactor a 0‖ = ‖a‖ := by
      rw [norm_normalizedBlaschkeFactor_eq_norm_blaschkeFactor]
      simp [blaschkeFactor]
    rw [← hfact,norm_mul,hnorm,prod_insert ha,mul_assoc]
    exact mul_le_mul_of_nonneg_left (ih ψ hT) (norm_nonneg _)

private def phase (u y : ℝ) : ℂ := Complex.exp ((u*y:ℝ)*Complex.I)

private theorem phase_half_period {y : ℝ} (hy : y ≠ 0) : phase (Real.pi/|y|) y = -1 := by
  rcases lt_or_gt_of_ne hy with h | h
  · have he : Real.pi/|y| * y = -Real.pi := by rw [abs_of_neg h]; field_simp
    rw [phase,he,Complex.ofReal_neg,neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num
  · have he : Real.pi/|y| * y = Real.pi := by rw [abs_of_pos h,div_mul_cancel₀ _ hy]
    rw [phase,he,Complex.exp_pi_mul_I]

/-- Averaging over the half-periods of finitely many nonzero frequencies
preserves the central value and the disk bound. A phase relation at an
unprocessed frequency is preserved by each two-point average. -/
private theorem average_disk_zeros (S : Finset ℝ) (z : ℝ → ℂ) (M : ℂ) (D : ℝ)
    (hy : ∀ y ∈ S, y ≠ 0)
    (F : ℝ → ℂ → ℂ)
    (hd : ∀ u ≥ 0, DifferentiableOn ℂ (F u) (Metric.ball 0 1))
    (hb : ∀ u ≥ 0, ∀ w ∈ Metric.ball (0:ℂ) 1, ‖F u w‖ ≤ D)
    (hc : ∀ u ≥ 0, F u 0 = M)
    (hwave : ∀ y ∈ S, ∀ u ≥ 0, ∀ v ≥ 0, F (u+v) (z y) = phase v y*F u (z y)) :
    ∃ φ : DiskMultiplier, φ.bd = D ∧ φ.fn 0 = M ∧ ∀ y ∈ S, φ.fn (z y) = 0 := by
  classical
  have aux (T : Finset ℝ) (hT : T ⊆ S) :
      ∃ G : ℝ → ℂ → ℂ,
        (∀ u ≥ 0, DifferentiableOn ℂ (G u) (Metric.ball 0 1)) ∧
        (∀ u ≥ 0, ∀ w ∈ Metric.ball (0:ℂ) 1, ‖G u w‖ ≤ D) ∧
        (∀ u ≥ 0, G u 0 = M) ∧
        (∀ y ∈ S, ∀ u ≥ 0, ∀ v ≥ 0, G (u+v) (z y) = phase v y*G u (z y)) ∧
        (∀ y ∈ T, ∀ u ≥ 0, G u (z y) = 0) := by
    induction T using Finset.induction_on with
    | empty => exact ⟨F,hd,hb,hc,hwave,by simp⟩
    | @insert a T ha ih =>
      obtain ⟨G,hgd,hgb,hgc,hgw,hgz⟩ := ih (fun y h => hT (mem_insert_of_mem h))
      have haS := hT (mem_insert_self a T)
      let d := Real.pi/|a|
      have hd₀ : 0 ≤ d := div_nonneg Real.pi_pos.le (abs_nonneg a)
      let J := fun (u : ℝ) (w : ℂ) => (G u w+G (u+d) w)/2
      refine ⟨J,fun u hu => ((hgd u hu).add (hgd _ (add_nonneg hu hd₀))).div_const _,?_,?_,?_,?_⟩
      · intro u hu w hw
        change ‖(G u w+G (u+d) w)/2‖ ≤ D
        rw [norm_div,Complex.norm_ofNat,div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        linarith only [norm_add_le (G u w) (G (u+d) w),hgb u hu w hw,hgb _ (add_nonneg hu hd₀) w hw]
      · intro u hu
        dsimp only [J]; rw [hgc u hu,hgc _ (add_nonneg hu hd₀)]; ring
      · intro y hyS u hu v hv
        dsimp only [J]
        rw [show u+v+d=u+d+v by ring,hgw y hyS u hu v hv,hgw y hyS _ (add_nonneg hu hd₀) v hv]
        ring
      · intro y hyT u hu
        dsimp only [J]
        rcases mem_insert.mp hyT with he | hyT
        · subst y
          rw [hgw a haS u hu d hd₀,phase_half_period (hy a haS)]; ring
        · rw [hgz y hyT u hu,hgz y hyT _ (add_nonneg hu hd₀)]; ring
  obtain ⟨G,hgd,hgb,hgc,_,hgz⟩ := aux S (fun _ h => h)
  let φ : DiskMultiplier := ⟨G 0,hgd 0 le_rfl,D,
    (norm_nonneg _).trans (hgb 0 le_rfl 0 (Metric.mem_ball_self one_pos)),hgb 0 le_rfl⟩
  exact ⟨φ,rfl,hgc 0 le_rfl,fun y hyS => hgz y hyS 0 le_rfl⟩

/-- A square-root error budget at every sufficiently large scale controls the
product of the normalized distances to every finite cluster of critical zeros. -/
theorem factorial_budget_at_cluster_of_critical_zeros {C R : ℝ} (hR : 0 < R) (hR' : R < 1/2)
    {ρ : ℂ} (hρ : ρ.re = 1/2) (hzero : riemannZeta ρ = 0) (S : Finset ℝ)
    (hS : ∀ y ∈ S, y ≠ 0 ∧ |y| < R ∧ riemannZeta (ρ+(y:ℂ)*I) = 0)
    (hbudget : ∀ᶠ X : ℝ in atTop, ∃ (m : ℕ) (c : Fin m → ℂ) (a : Fin m → ℝ),
      (∀ j, 0 < a j) ∧ IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0) ∧
      (∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ C*X^(1/2:ℝ)) ∧
      (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ C*X^(1/2:ℝ)/X) :
    (1/2-R)*‖mellin squarePrimeWeight ρ‖ ≤ C*(∏ y ∈ S, |y| / R) := by
  classical
  obtain ⟨T,hT⟩ := eventually_atTop.mp hbudget
  let u₀ := max T 0
  let X := fun u : ℝ => Real.exp (u₀+max u 0)
  have hlarge (u : ℝ) : T ≤ X u := (le_max_left T 0).trans
    ((le_add_of_nonneg_right (le_max_right u 0)).trans
      ((le_add_of_nonneg_right (zero_le_one : (0:ℝ) ≤ 1)).trans (Real.add_one_le_exp _)))
  choose m c a ha hE hcap hmass using fun u => hT (X u) (hlarge u)
  let w := fun z : ℂ => ρ+(R:ℂ)*z
  let z := fun y : ℝ => (y:ℂ)*I/(R:ℂ)
  let F := fun (u : ℝ) (v : ℂ) => Complex.exp (-(Real.log (X u):ℂ)*ρ) *
    residual (c u) (a u) (X u) (w v)
  have hstrip {v : ℂ} (hv : v ∈ Metric.ball 0 1) : 1/2-R < (w v).re ∧ (w v).re < 1/2+R := by
    have h := mul_lt_mul_of_pos_left ((abs_re_le_norm v).trans_lt
      (by simpa only [Metric.mem_ball,dist_zero_right] using hv : ‖v‖ < 1)) hR
    rw [← abs_of_pos hR,← abs_mul,mul_one,abs_of_pos hR] at h
    simp only [w,Complex.add_re,hρ,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    obtain ⟨l,r⟩ := abs_lt.mp h
    constructor <;> linarith only [l,r]
  have hden : 0 < 1/2-R := sub_pos.mpr hR'
  have hD (u : ℝ) : DifferentiableOn ℂ (F u) (Metric.ball 0 1) := by
    intro v hv
    obtain ⟨hl,hr⟩ := hstrip hv
    have h₀ : w v ≠ 0 := fun h => by rw [h,Complex.zero_re] at hl; linarith
    have h₁ : w v ≠ 1 := fun h => by rw [h,Complex.one_re] at hr; linarith
    have hw : DifferentiableAt ℂ w v := by dsimp only [w]; fun_prop
    have he : DifferentiableAt ℂ (fun t : ℂ => Complex.exp ((Real.log (X u):ℂ)*t)) (w v) := by fun_prop
    have hd := (he.mul ((differentiable_mellin_squarePrimeWeight (w v)).add
      (((freq_differentiable (c u) (a u) (ha u) (w v)).mul (differentiableAt_riemannZeta h₁)).div
        differentiableAt_id h₀))).comp v hw
    exact (hd.const_mul _).differentiableWithinAt
  have hnorm (u : ℝ) (v : ℂ) : ‖F u v‖ =
      ‖residual (c u) (a u) (X u) (w v)‖/(X u)^(1/2:ℝ) := by
    rw [F,norm_mul,neg_mul,Complex.exp_neg,norm_inv,norm_scale (Real.exp_pos _),hρ]
    ring
  have hB (u : ℝ) (v : ℂ) (hv : v ∈ Metric.ball 0 1) : ‖F u v‖ ≤ C/(1/2-R) := by
    obtain ⟨hl,hr⟩ := hstrip hv
    have h := residual_bound (c u) (a u) (ha u) (Real.exp_pos _) (hE u) (hcap u) (hmass u)
      (hden.trans hl) (hr.trans (by linarith only [hR']))
    have h' := (mul_le_mul_of_nonneg_right hl.le (norm_nonneg _)).trans h
    rw [hnorm,div_le_div_iff₀ (Real.rpow_pos_of_pos (Real.exp_pos _) _) hden]
    simpa only [mul_comm] using h'
  have hwz (y : ℝ) : w (z y) = ρ+(y:ℂ)*I := by
    dsimp only [w,z]; field_simp [Complex.ofReal_ne_zero.mpr hR.ne']
  have heval (u : ℝ) {s : ℂ} (hs : riemannZeta (w s) = 0) : F u s =
      Complex.exp ((Real.log (X u):ℂ)*(w s-ρ))*mellin squarePrimeWeight (w s) := by
    simp only [F,residual,hs,mul_zero,zero_div,add_zero,← mul_assoc,← Complex.exp_add]
    congr 2; ring
  have hcenter (u : ℝ) : F u 0 = mellin squarePrimeWeight ρ := by
    have h : w 0 = ρ := by simp [w]
    rw [heval _ (h ▸ hzero),h,sub_self,mul_zero,Complex.exp_zero,one_mul]
  have hwave (y : ℝ) (hy : y ∈ S) (u : ℝ) (hu : 0 ≤ u) (v : ℝ) (hv : 0 ≤ v) :
      F (u+v) (z y) = phase v y*F u (z y) := by
    have hz : riemannZeta (w (z y)) = 0 := hwz y ▸ (hS y hy).2.2
    rw [heval _ hz,heval _ hz,hwz,phase,← mul_assoc,← Complex.exp_add]
    simp only [X,Real.log_exp,max_eq_left hu,max_eq_left (add_nonneg hu hv),Complex.ofReal_add,Complex.ofReal_mul]
    congr 2; ring
  obtain ⟨φ,hbd,hφ,hzeros⟩ := average_disk_zeros S z _ _ (fun y hy => (hS y hy).1) F
    (fun u _ => hD u) (fun u _ => hB u) (fun u _ => hcenter u) hwave
  have hzNorm (y : ℝ) : ‖z y‖ = |y| / R := by
    simp only [z,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,abs_of_pos hR]
  have hinj : Function.Injective z := by
    intro a b h
    dsimp only [z] at h
    exact Complex.ofReal_injective ((mul_left_inj' Complex.I_ne_zero).mp
      ((div_left_inj' (Complex.ofReal_ne_zero.mpr hR.ne')).mp h))
  have h := center_bound_of_zeros (S.image z) φ (by
    intro a ha
    obtain ⟨y,hy,rfl⟩ := mem_image.mp ha
    exact ⟨by rw [hzNorm,div_lt_one hR]; exact (hS y hy).2.1,hzeros _ hy⟩)
  rw [hφ,hbd,prod_image (fun _ _ _ _ he => hinj he)] at h
  simp_rw [hzNorm] at h
  have he := (mul_le_mul_of_nonneg_right h hden.le)
  rw [mul_assoc,div_mul_cancel₀ _ hden.ne'] at he
  simpa only [mul_comm] using he

end GaloisForLFunctions.CountingHolography.Sections
