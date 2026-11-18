import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import GaloisForLFunctions.RHTower.ThetaIntegerCutoffMovingPacket

/-!
# The signed spline on the ordinary-prime mesh

On the multiplicative scale the two dilations form one compactly
supported twice differentiable function of mean zero. Its first and
second mesh differences pay, respectively, for errors in the prime
count and for errors in a primitive of that count.
-/

noncomputable section
open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.ArithmeticWeightTheory GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge RHTower.WeilDeletion
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The normalized real prime profile, extended by zero to the left. -/
def dyadicSpline (x : ℝ) : ℝ := if 0 < x then 2*(squarePrimeWeight x).re else 0

private theorem spline_off {x : ℝ}
    (h : x ∉ Set.Icc (Real.exp (-8)) (Real.exp (8+Real.log 4))) : dyadicSpline x=0 := by
  by_cases hx : 0<x
  · simp only [dyadicSpline,if_pos hx,squarePrimeWeight_zero_outside hx h,Complex.zero_re,mul_zero]
  · exact if_neg hx

private theorem spline_compact : HasCompactSupport dyadicSpline :=
  HasCompactSupport.intro isCompact_Icc (fun _ h => spline_off h)

private theorem spline_smooth : ContDiff ℝ 2 dyadicSpline := by
  have hA : ContDiff ℝ 2 splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact (contDiff_upow one_pos 6).of_le (by norm_num)
  have hF : ContDiff ℝ 2 squareLogProfile :=
    (contDiff_const.mul hA).sub (hA.comp (contDiff_id.sub contDiff_const))
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0<x
  · have hl := Real.contDiffAt_log (n := 2) hx.ne'
    have he : ContDiffAt ℝ 2 (fun v : ℝ =>
        2*(Real.exp (-Real.log v/2)*squareLogProfile (Real.log v))) x := by fun_prop
    apply he.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with v hv
    simp only [dyadicSpline,if_pos hv,squarePrimeWeight,Complex.ofReal_re]
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ((le_of_not_gt hx).trans_lt (Real.exp_pos (-8)))] with v hv
    exact spline_off (fun h => hv.not_ge h.1)

private theorem spline_integral : (∫ x, dyadicSpline x) = 0 := by
  have hi : IntegrableOn squarePrimeWeight (Set.Ioi 0) := by
    simpa only [MellinConvergent,sub_self,Complex.cpow_zero,one_smul] using
      mellinConvergent_squarePrimeWeight 1
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioi (0:ℝ)) (f := dyadicSpline) (fun x hx => if_neg hx)]
  have he : (∫ x in Set.Ioi 0, dyadicSpline x) =
      ∫ x in Set.Ioi 0, 2*(squarePrimeWeight x).re :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => if_pos hx
  rw [he,integral_const_mul,show (∫ x in Set.Ioi 0, (squarePrimeWeight x).re) =
    (∫ x in Set.Ioi 0, squarePrimeWeight x).re from integral_re hi,
    squarePrimeWeight_mean_zero,Complex.zero_re,mul_zero]

/-- The common ordinary-prime cutoff of the three square graphs. -/
def splineHorizon (n : ℕ) := 3*windowEnd ((2*n+1)^2+1)

/-- The arithmetic test at n², including the factor two on the prime mass. -/
def sampledSpline (n k : ℕ) : ℝ := dyadicSpline ((k:ℝ)/(n:ℝ)^2)/n

theorem sampledSpline_prime_contact {n k : ℕ} (hn : 0<n) (hk : 0<k) :
    sampledSpline n k = (2/Real.sqrt k)*squareLogProfile (Real.log k-Real.log ((n:ℝ)^2)) := by
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hk' : 0<(k:ℝ) := Nat.cast_pos.mpr hk
  let y := (k:ℝ)/(n:ℝ)^2
  have hy : 0<y := div_pos hk' (sq_pos_of_pos hn')
  have he : Real.exp (-Real.log y/2)=(Real.sqrt y)⁻¹ := by
    rw [neg_div,Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hy]
    congr 2; ring
  change dyadicSpline y/n=_
  rw [dyadicSpline,if_pos hy,squarePrimeWeight,Complex.ofReal_re,he]
  simp only [y,Real.sqrt_div hk'.le,Real.sqrt_sq hn'.le,Real.log_div hk'.ne' (sq_pos_of_pos hn').ne']
  field_simp
  ring

private theorem support_covered (n : ℕ) : Real.exp (8+Real.log 4)*(n:ℝ)^2 ≤ (splineHorizon n:ℝ) := by
  have hn : 4*(n:ℝ)^2 ≤ (((2*n+1:ℕ):ℝ))^2 := by
    push_cast; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have h := (mul_le_mul_of_nonneg_left hn (Real.exp_pos 8).le).trans
    (successorSquareWindowScale_bounds n).2.2
  rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)]
  dsimp only [splineHorizon]
  push_cast
  linarith only [h,Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]

/-- The terminal Abel term vanishes already at the next mesh point. -/
theorem sampledSpline_endpoint {n : ℕ} (hn : 0<n) : sampledSpline n (splineHorizon n+1)=0 := by
  have hs := support_covered n
  have hx := sq_pos_of_pos (Nat.cast_pos.mpr hn : (0:ℝ)<n)
  unfold sampledSpline
  rw [spline_off,zero_div]
  intro h
  have := (div_le_iff₀ hx).mp h.2
  push_cast at this
  linarith

/-- The density on the common finite window costs at most a constant
divided by n. Its continuum contribution is exactly zero. -/
theorem sampledSpline_density : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0<n →
    |∑ k ∈ Icc 1 (splineHorizon n), sampledSpline n k| ≤ C/n := by
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport spline_compact spline_smooth (by norm_num)
  obtain ⟨A,hA,hbound⟩ := successorSquare_window_bound
  refine ⟨(K:ℝ)*A^2,by positivity,fun {n} hn => ?_⟩
  let N := splineHorizon n
  let h := ((n:ℝ)^2)⁻¹
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hh : 0<h := inv_pos.mpr (sq_pos_of_pos hn')
  have hcover : Real.exp (8+Real.log 4) ≤ N*h := by
    rw [show (N:ℝ)*h=N/(n:ℝ)^2 from (div_eq_mul_inv ..).symm]
    exact (le_div_iff₀ (sq_pos_of_pos hn')).mpr (support_covered n)
  have hzero : (∫ x in (0:ℝ)..N*h, dyadicSpline x) = 0 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset,spline_integral]
    intro x hx
    by_contra hbad
    apply hx
    apply spline_off
    exact fun hs => hbad ⟨(Real.exp_pos _).trans_le hs.1,hs.2.trans hcover⟩
  have hb := _root_.RHTower.abs_riemannSum_sub_integral_le (T := N*h) hK.lipschitzOnWith
    spline_smooth.continuous.continuousOn N hh.le le_rfl
  rw [hzero,sub_zero,abs_mul,abs_of_pos hh] at hb
  have hmesh : (N:ℝ)*h ≤ A^2 := by
    rw [show (N:ℝ)*h=N/(n:ℝ)^2 from (div_eq_mul_inv ..).symm]
    apply (div_le_iff₀ (sq_pos_of_pos hn')).mpr
    simpa only [mul_pow] using hbound hn
  have H : |∑ i ∈ range N, dyadicSpline (((i:ℝ)+1)*h)| ≤ (K:ℝ)*A^2 := by
    apply le_of_mul_le_mul_left _ hh
    exact hb.trans (by linarith only [mul_le_mul_of_nonneg_left hmesh
      (mul_nonneg hh.le K.coe_nonneg)])
  have hs : (∑ k ∈ Icc 1 N, sampledSpline n k) =
      (∑ i ∈ range N, dyadicSpline (((i:ℝ)+1)*h))/n := by
    rw [show Icc 1 N = Ico 1 (N+1) by ext k; simp, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, sampledSpline, ←sum_div, Nat.cast_add,Nat.cast_one,
      div_eq_mul_inv,h,add_comm (1:ℝ)]
  change |∑ k ∈ Icc 1 N, sampledSpline n k| ≤ _
  rw [hs,abs_div,abs_of_pos hn']
  exact div_le_div_of_nonneg_right H hn'.le

private theorem translated_increment {K : ℝ≥0} (hK : LipschitzWith K (deriv dyadicSpline))
    (x h : ℝ) :
    |(dyadicSpline (x+h+h)-dyadicSpline (x+h))-(dyadicSpline (x+h)-dyadicSpline x)| ≤
      (K:ℝ)*|h|^2 := by
  let g (t : ℝ) := dyadicSpline (t+h)-dyadicSpline t
  have hd := spline_smooth.differentiable (by norm_num)
  have hg (t : ℝ) : HasDerivAt g (deriv dyadicSpline (t+h)-deriv dyadicSpline t) t :=
    ((hd (t+h)).hasDerivAt.comp_add_const t h).sub (hd t).hasDerivAt
  have hb (t : ℝ) : ‖deriv g t‖ ≤ (K:ℝ)*|h| := by
    rw [(hg t).deriv,Real.norm_eq_abs]
    simpa only [Real.dist_eq,add_sub_cancel_left] using hK.dist_le_mul (t+h) t
  have H := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hg t).differentiableAt) (fun t _ => hb t)
    (Set.mem_univ x) (Set.mem_univ (x+h))
  simpa only [g,Real.norm_eq_abs,add_sub_cancel_left,pow_two,mul_assoc] using H

/-- Uniform first and second differences on the actual square mesh. -/
theorem sampledSpline_differences :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ {n : ℕ}, 0<n → ∀ k : ℕ,
      |sampledSpline n k-sampledSpline n (k+1)| ≤ B/(n:ℝ)^3 ∧
      |(sampledSpline n k-sampledSpline n (k+1))-
        (sampledSpline n (k+1)-sampledSpline n (k+2))| ≤ C/(n:ℝ)^5 := by
  obtain ⟨B,hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport spline_compact spline_smooth (by norm_num)
  have hd : ContDiff ℝ 1 (deriv dyadicSpline) := spline_smooth.deriv'
  obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport spline_compact.deriv hd (by norm_num)
  refine ⟨B,C,B.coe_nonneg,C.coe_nonneg,fun {n} hn k => ?_⟩
  let h := ((n:ℝ)^2)⁻¹
  let x := (k:ℝ)/(n:ℝ)^2
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hh : 0 ≤ h := inv_nonneg.mpr (sq_nonneg _)
  have e₁ : ((k+1:ℕ):ℝ)/(n:ℝ)^2=x+h := by dsimp only [x,h]; push_cast; ring
  have e₂ : ((k+2:ℕ):ℝ)/(n:ℝ)^2=x+h+h := by dsimp only [x,h]; push_cast; ring
  have h₁ : |dyadicSpline x-dyadicSpline (x+h)| ≤ B*h := by
    simpa only [Real.dist_eq,sub_add_cancel_left,abs_neg,abs_of_nonneg hh,
      show x-(x+h) = -h by ring] using hB.dist_le_mul x (x+h)
  have h₂ := translated_increment hC x h
  rw [abs_of_nonneg hh] at h₂
  simp only [sampledSpline, e₁,e₂,←sub_div,abs_div,abs_of_pos hn']
  constructor
  · exact (div_le_div_of_nonneg_right h₁ hn'.le).trans_eq (by dsimp [h]; ring)
  · have he : (dyadicSpline x-dyadicSpline (x+h))-(dyadicSpline (x+h)-dyadicSpline (x+h+h)) =
        (dyadicSpline (x+h+h)-dyadicSpline (x+h))-(dyadicSpline (x+h)-dyadicSpline x) := by ring
    change |(dyadicSpline x-_)-(_-_)|/n ≤ _
    rw [he]
    exact (div_le_div_of_nonneg_right h₂ hn'.le).trans_eq (by dsimp [h]; ring)

#print axioms sampledSpline_endpoint
#print axioms sampledSpline_density
#print axioms sampledSpline_differences

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
