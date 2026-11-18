import GaloisForLFunctions.CountingHolography.Sections.UniformQuadratureForPrimeContacts
import GaloisForLFunctions.CountingHolography.Sections.ThreeSquareConductorsWithZeroPoleDegree
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionPriceEulerAdditivity
import GaloisForLFunctions.ArithmeticWeightTheory.ProductPositivityCouplingIsOneWay
import GaloisForLFunctions.BiScaleUncertainty.InteriorOfBoxSplines
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSplineHasUniformFourthDerivativeRegularizations
import GaloisForLFunctions.RHTower.WeilFullConeSummableDeficitRigidity

/-!
# The ordinary-prime profile of the three square conductors

The continuous contact of any signed divisor is a finite matrix of
translated spline autocorrelations. Above one fixed lag the triple
has only two entries, from the low graph to either upper graph.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory ArithmeticWeightTheory ArithmeticCastelnuovoSeveri
open BiScaleUncertainty.ChebyshevGauge ArithmeticOrientationGeometry _root_.RHTower.WeilDeletion
open scoped Convolution

private theorem integratedContact_eq_full {N : ℕ} (a : Fin N → ℤ) (k : ℕ) :
    integratedContact a k = 2/Real.sqrt k * ∫ u, packet a u*packet a (u+Real.log k) := by
  let L := 3*windowEnd N
  have h := packet_window a
  have hlo : 0 ≤ Real.log (1+(L:ℝ)) := Real.log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hhi : Real.log (windowEnd N) ≤ Real.log (1+(L:ℝ)) := by
    apply Real.log_le_log (Nat.cast_pos.mpr h.1)
    dsimp only [L]
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) (windowEnd N)]
  unfold integratedContact
  congr 1
  rw [intervalIntegral.integral_of_le hlo]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  rw [h.2 _ ?_,zero_mul]
  rcases not_and_or.mp hu with hl | ht
  · exact Or.inl ((not_lt.mp hl).trans (Real.log_nonneg (by norm_num)))
  · exact Or.inr (hhi.trans (not_le.mp ht).le)

/-- The contact at one ordinary lag before prime weighting or flooring. -/
theorem integratedContact_eq_autocorrelations {N : ℕ} (a : Fin N → ℤ) (k : ℕ) :
    integratedContact a k = 2/Real.sqrt k *
      ∑ i, ∑ j, (a i:ℝ)*(a j:ℝ)*splineAutoCorr
        (-Real.log k-Real.log ((i:ℝ)+1)+Real.log ((j:ℝ)+1)) := by
  let x := fun i : Fin N => (Real.log 3+5)+Real.log ((i:ℝ)+1)
  let c := fun i : Fin N => ((a i:ℝ):ℂ)
  have hf : cx (packet a) = fun u => ∑ i, c i*cx cubicSpline (u-x i) := by
    funext u
    change ((∑ i, (a i:ℝ)*cubicSpline (u-(Real.log 3+5)-Real.log ((i:ℝ)+1)) : ℝ):ℂ) = _
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,c,cx,x,sub_add_eq_sub_sub]
  have he := BiScaleUncertainty.weilTest_finset_translates univ c x
    (cx_contDiff contDiff_cubicSpline).continuous (cx_hasCompactSupport hasCompactSupport_cubicSpline) (-Real.log k)
  rw [← hf,ArithmeticCastelnuovoSeveri.weilTest_ofReal] at he
  have hh := congrArg Complex.re he
  simp only [Complex.ofReal_re,Complex.re_sum,sub_neg_eq_add] at hh
  rw [integratedContact_eq_full,hh]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hlag : -Real.log k-x i+x j = -Real.log k-Real.log ((i:ℝ)+1)+Real.log ((j:ℝ)+1) := by
    dsimp only [x]
    ring
  rw [hlag]
  simp only [c,Complex.conj_ofReal,← Complex.ofReal_mul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,splineAutoCorr]

/-- The autocorrelation of the four-box spline is the density of the sum
of eight uniform variables. -/
theorem splineAutoCorr_eq_eight_boxes (x : ℝ) : splineAutoCorr x = upow 1 7 x := by
  have he : upow 1 7 = cubicSpline ⋆ cubicSpline :=
    SpacingScaleHarmonicAnalysis.boxRegularization_eq_upow_convolution
      contDiff_cubicSpline.continuous hasCompactSupport_cubicSpline 3
  rw [splineAutoCorr,weilTest_ofReal,Complex.ofReal_re,he,convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  congr 1
  funext u
  rw [show u-x = -(x-u) by ring]
  exact congrArg (fun y : ℝ => cubicSpline u*y) (SquareRootThreshold.upow_neg 1 3 (x-u))

theorem splineAutoCorr_interior {x : ℝ} (hx : |x| < 8) : 0 < splineAutoCorr x := by
  rw [splineAutoCorr_eq_eight_boxes]
  exact upow_unit_pos 7 (by simpa only [Nat.cast_ofNat,show (7:ℝ)+1=8 by norm_num] using hx)

theorem splineAutoCorr_zero_outside {x : ℝ} (hx : 8 < |x|) : splineAutoCorr x = 0 := by
  rw [splineAutoCorr_eq_eight_boxes]
  by_contra h
  have ht := support_upow_subset (w := 1) one_pos 7 (show x ∈ Function.support (upow 1 7) from h)
  have hb : |x| ≤ 8 := abs_le.mpr (by norm_num at ht ⊢; exact ht)
  exact hx.not_ge hb

private theorem corr_vanish {x : ℝ} (hx : x < -8) : splineAutoCorr x = 0 :=
  splineAutoCorr_zero_outside (lt_abs.mpr (Or.inr (by linarith only [hx])))

private theorem square_profile {n k : ℕ} (hn : 0 < n) :
    let s := Real.log ((n:ℝ)^2)
    let t := Real.log (((2*n+1 : ℕ):ℝ)^2)
    let l := Real.log k
    let R := fun u : ℝ => splineAutoCorr (-l-u)+2*splineAutoCorr (-l-u+s)-splineAutoCorr (-l-u+t)
    integratedContact (successorSquareTriple n) k = 2/Real.sqrt k*(R 0+2*R s-R t) := by
  let d := successorSquareTriple n
  let l := Real.log k
  let s := Real.log ((n:ℝ)^2)
  let t := Real.log (((2*n+1 : ℕ):ℝ)^2)
  let R := fun u : ℝ => splineAutoCorr (-l-u)+2*splineAutoCorr (-l-u+s)-splineAutoCorr (-l-u+t)
  have hrow (i : Fin ((2*n+1)^2+1)) :
      (∑ j, (d i:ℝ)*(d j:ℝ)*splineAutoCorr (-l-Real.log ((i:ℝ)+1)+Real.log ((j:ℝ)+1))) =
        R (Real.log ((i:ℝ)+1))*(d i:ℝ) := by
    let f := fun z : ℝ => splineAutoCorr (-l-Real.log ((i:ℝ)+1)+Real.log z)
    calc _ = (∑ j : Fin ((2*n+1)^2+1), f ((j:ℝ)+1)*(d j:ℝ))*(d i:ℝ) := by
              rw [sum_mul]
              exact sum_congr rfl fun _ _ => by dsimp only [f]; ring
      _ = _ := by
              rw [sum_successorSquareTriple hn f]
              simp only [f,Real.log_one,add_zero,R,s,t]
  rw [integratedContact_eq_autocorrelations]
  change 2/Real.sqrt k*(∑ i, ∑ j, (d i:ℝ)*(d j:ℝ)*splineAutoCorr
    (-l-Real.log ((i:ℝ)+1)+Real.log ((j:ℝ)+1))) = _
  simp_rw [hrow]
  rw [sum_successorSquareTriple hn (fun z => R (Real.log z))]
  simp only [Real.log_one,R,s,t,l]

/-- At every lag above a fixed constant the prime measures only the two
large conductor ratios, with weights two and minus one. -/
theorem successorSquare_long_contact {n k : ℕ} (hn : 0 < n) (hlarge : 8+Real.log 9 < Real.log k) :
    integratedContact (successorSquareTriple n) k = 2/Real.sqrt k *
      (2*splineAutoCorr (Real.log ((n:ℝ)^2)-Real.log k) -
        splineAutoCorr (Real.log (((2*n+1 : ℕ):ℝ)^2)-Real.log k)) := by
  let s := Real.log ((n:ℝ)^2)
  let t := Real.log (((2*n+1 : ℕ):ℝ)^2)
  let l := Real.log k
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos := zero_lt_one.trans_le hn'
  have hs : 0 ≤ s := Real.log_nonneg (one_le_pow₀ hn')
  have hst : s ≤ t := Real.log_le_log (sq_pos_of_pos hpos)
    (pow_le_pow_left₀ hpos.le (by exact_mod_cast (by omega : n ≤ 2*n+1)) 2)
  have hts : t ≤ Real.log 9+s := by
    rw [← Real.log_mul (by norm_num : (9:ℝ) ≠ 0) (sq_pos_of_pos hpos).ne']
    apply Real.log_le_log (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos _)))
    have he := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(n:ℝ)+1)
      (by linarith only [hn'] : 2*(n:ℝ)+1 ≤ 3*n) 2
    push_cast
    linarith only [he]
  have hl : 8 < l := by linarith only [hlarge,Real.log_nonneg (by norm_num : (1:ℝ) ≤ 9)]
  have h₀ := corr_vanish (x := -l) (by linarith only [hl])
  have h₁ := corr_vanish (x := -l-s) (by linarith only [hl,hs])
  have h₂ := corr_vanish (x := -l-t) (by linarith only [hl,hs,hst])
  have h₃ := corr_vanish (x := -l-s+t) (by linarith only [hlarge,hts])
  have h₄ := corr_vanish (x := -l-t+s) (by linarith only [hl,hst])
  rw [square_profile hn]
  change 2/Real.sqrt k*((splineAutoCorr (-l-0)+2*splineAutoCorr (-l-0+s)-splineAutoCorr (-l-0+t))+
    2*(splineAutoCorr (-l-s)+2*splineAutoCorr (-l-s+s)-splineAutoCorr (-l-s+t)) -
    (splineAutoCorr (-l-t)+2*splineAutoCorr (-l-t+s)-splineAutoCorr (-l-t+t))) = _
  simp only [sub_zero,sub_add_cancel,h₀,h₁,h₂,h₃,h₄,zero_add,mul_zero,sub_zero,add_zero,
    show -l+s=s-l by ring,show -l+t=t-l by ring,s,t,l]

/-- Relative lags sufficiently near the middle conductor carry a fixed
positive contact, uniformly in the location of the negative conductor. -/
theorem successorSquare_positive_band :
    ∃ δ c : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧ ∀ {n k : ℕ}, 0 < n →
      8+Real.log 9 < Real.log k → |Real.log ((n:ℝ)^2)-Real.log k| ≤ δ →
      (2/Real.sqrt k)*c ≤ integratedContact (successorSquareTriple n) k := by
  let H := splineAutoCorr 0
  have hH : 0 < H := splineAutoCorr_zero_pos
  have hnear : {v : ℝ | 3*H/4 < splineAutoCorr v} ∈ 𝓝 (0:ℝ) :=
    continuous_splineAutoCorr.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by
      change 3*H/4 < H
      linarith only [hH]))
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hnear
  have hmax (z : ℝ) : splineAutoCorr z ≤ H := by
    unfold H splineAutoCorr
    rw [weilTest_ofReal,weilTest_ofReal,Complex.ofReal_re,Complex.ofReal_re]
    simpa only [sub_zero] using _root_.RHTower.autocorr_le_autocorr_zero
      contDiff_cubicSpline.continuous hasCompactSupport_cubicSpline z
  refine ⟨min (ε/2) 1,H/2,lt_min (half_pos hε) one_pos,min_le_right _ _,half_pos hH,?_⟩
  intro n k hn hlarge hband
  rw [successorSquare_long_contact hn hlarge]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h₀ : 3*H/4 < splineAutoCorr (Real.log ((n:ℝ)^2)-Real.log k) := he (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact (hband.trans (min_le_left _ _)).trans_lt (half_lt_self hε))
  linarith only [h₀,hmax (Real.log (((2*n+1 : ℕ):ℝ)^2)-Real.log k)]

#print axioms successorSquare_positive_band
#print axioms successorSquare_long_contact
#print axioms integratedContact_eq_autocorrelations

end GaloisForLFunctions.CountingHolography.Sections
