import GaloisForLFunctions.RHTower.SelbergFiniteMellinPacket
import GaloisForLFunctions.RHTower.SelbergScatteringCuspNorm
import GaloisForLFunctions.RHTower.SelbergScatteringEntireXiPackets

/-!
# Native admission of complete finite quarter-lattice Eisenstein packets

Every shifted field shares the full Xi entire-transform value. Nevertheless,
the complete finite superposition is native cusp L² exactly when all weights
vanish. Both Weyl branches have distinct exponents. Every nonzero field has a
nonzero completion coefficient at or above the native growth threshold, and
the complete Fourier tail is separately admitted in that same norm.

This excludes finite packets as an independent entire-occurrence construction.
It does not exclude infinite resummation or prove an occurrence theorem or RH.
-/

open Complex Set MeasureTheory
open scoped BigOperators
namespace RHTower.SelbergScatteringFiniteQuarterPacket
open D4BMJointSource D4BMGlobalAngularResponse SelbergScatteringHeightConjugation
open GaloisForLFunctions.RHTower.SelbergFiniteMellinPacket
noncomputable section

/-- The actual quarter-lattice shift of the original physical Eisenstein parameter. -/
def shiftedParameter (q : XiZeroCopy) (j : ℤ) : ℂ :=
  physicalAngularParameter q+(j:ℂ)/4

/-- Both original Weyl branches, expressed relative to the native half-density threshold. -/
def exponent (q : XiZeroCopy) (p : ℤ × Bool) : ℂ :=
  (d4BMCuspSign p.2:ℂ)*shiftedParameter q p.1

/-- The unaltered completion coefficient of each shifted Weyl branch. -/
def coefficient (q : XiZeroCopy) (w : ℤ → ℂ) (p : ℤ × Bool) : ℂ :=
  w p.1*d4BMCompletedEisensteinCuspConstantCoefficient (shiftedParameter q p.1) p.2

/-- A finite superposition retains both Weyl terms and every Fourier mode. -/
def completePacket (q : XiZeroCopy) (J : Finset ℤ) (w : ℤ → ℂ) (z : Fin 2 → ℝ) : ℂ :=
  ∑ j ∈ J, w j*scalarSource (shiftedParameter q j) z

/-- The exact sum of all shifted Weyl terms. -/
def principalPacket (q : XiZeroCopy) (J : Finset ℤ) (w : ℤ → ℂ) (z : Fin 2 → ℝ) : ℂ :=
  ∑ j ∈ J, w j*principal (shiftedParameter q j) z

/-- The full Fourier tail of the finite packet. -/
def tailPacket (q : XiZeroCopy) (J : Finset ℤ) (w : ℤ → ℂ) (z : Fin 2 → ℝ) : ℂ :=
  ∑ j ∈ J, w j*tail (shiftedParameter q j) z

/-- No two Weyl exponents coincide anywhere in the actual nonreal quarter lattice. -/
theorem exponent_injective (q : XiZeroCopy) : Function.Injective (exponent q) := by
  intro ⟨j,b⟩ ⟨k,d⟩ he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  have hq := xi_divisor_support_im_ne_zero q.1
  cases b <;> cases d <;>
    simp only [exponent,shiftedParameter,physicalAngularParameter_eq,d4BMCuspSign,
      Bool.false_eq_true,if_false,if_true,Int.cast_neg,Int.cast_one,neg_one_mul,one_mul,
      Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,Complex.sub_re,
      Complex.sub_im,Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.one_re,
      Complex.one_im,Complex.intCast_re,Complex.intCast_im,zero_div,add_zero,sub_zero] at hre him
  · have hjk : (j:ℝ)=(k:ℝ) := by linarith
    have hjk' : j=k := by exact_mod_cast hjk
    simp [hjk']
  · exact False.elim (hq (by linarith))
  · exact False.elim (hq (by linarith))
  · have hjk : (j:ℝ)=(k:ℝ) := by linarith
    have hjk' : j=k := by exact_mod_cast hjk
    simp [hjk']

private theorem weyl_power_half_density (b : ℂ) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^(-1:ℂ)*(y:ℂ)^(1/2+b) =
      (y:ℂ)^(-1/2:ℂ)*Complex.exp (b*(Real.log y:ℂ)) := by
  simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.ofReal_log hy.le,← Complex.exp_add]
  congr 1
  ring

/-- The complete sum of both Weyl branches is the exact finite native Mellin packet. -/
theorem principalPacket_mellin (q : XiZeroCopy) (J : Finset ℤ) (w : ℤ → ℂ)
    (xy : ℝ × ℝ) (hy : 0 < xy.2) :
    cuspLift 0 (principalPacket q J w) xy =
      (xy.2:ℂ)^(-1/2:ℂ)*packet (J.product Finset.univ) (coefficient q w)
        (exponent q) (Real.log xy.2) := by
  simp only [cuspLift,principalPacket,Complex.ofReal_zero,zero_sub,
    packet,Finset.mul_sum]
  change _ = ∑ i ∈ J ×ˢ (Finset.univ : Finset Bool),
    (xy.2:ℂ)^(-1/2:ℂ)*(coefficient q w i*Complex.exp (exponent q i*(Real.log xy.2:ℂ)))
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_bool,coefficient,exponent,principal,
    d4BMCompletedEisensteinCuspConstantPart,d4BMCompletedEisensteinCuspConstantTerm,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCompletedEisensteinCuspConstantCoefficient,d4BMCuspSign,
    Bool.false_eq_true,if_false,if_true,Int.cast_neg,Int.cast_one,neg_one_mul,one_mul,
    mul_one,Matrix.cons_val_one,Matrix.cons_val_zero]
  have hm := weyl_power_half_density (-(shiftedParameter q j)) hy
  have hp := weyl_power_half_density (shiftedParameter q j) hy
  linear_combination w j*reflectedCompletedLambda (2*shiftedParameter q j)*hm +
    w j*reflectedCompletedLambda (1+2*shiftedParameter q j)*hp

/-- Every Fourier mode survives in the native-admitted finite tail. -/
theorem tailPacket_memLp (q : XiZeroCopy) (J : Finset ℤ) (w : ℤ → ℂ) :
    MemLp (cuspLift 0 (tailPacket q J w)) 2 cuspMeasure := by
  have h := memLp_finsetSum J (fun j _ =>
    (cuspLift_tail_memLp (shiftedParameter q j) 0).const_mul (w j))
  convert h using 1
  funext xy
  simp only [cuspLift,tailPacket,Finset.mul_sum,mul_left_comm]

/-- Full-packet admission is exactly principal-packet admission; the complete tail is subtracted in L². -/
theorem completePacket_memLp_iff_principal (q : XiZeroCopy) (J : Finset ℤ) (w : ℤ → ℂ) :
    MemLp (cuspLift 0 (completePacket q J w)) 2 cuspMeasure ↔
      MemLp (cuspLift 0 (principalPacket q J w)) 2 cuspMeasure := by
  have he : cuspLift 0 (completePacket q J w) =
      cuspLift 0 (principalPacket q J w)+cuspLift 0 (tailPacket q J w) := by
    funext xy
    simp only [cuspLift,completePacket,principalPacket,tailPacket,scalarSource,principal,tail,
      d4BMCompletedEisensteinCuspLeg,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  rw [he]
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using h.sub (tailPacket_memLp q J w)
  · intro h
    exact h.add (tailPacket_memLp q J w)

/-- Actual native L² admission forces each nonzero Weyl coefficient below the threshold. -/
theorem admitted_exponent_negative (q : XiZeroCopy) (J : Finset ℤ) (w : ℤ → ℂ)
    (h : MemLp (cuspLift 0 (completePacket q J w)) 2 cuspMeasure)
    {p : ℤ × Bool} (hp : p ∈ J.product Finset.univ) (hcp : coefficient q w p ≠ 0) :
    (exponent q p).re < 0 := by
  have hprincipal := (completePacket_memLp_iff_principal q J w).mp h
  let g : ℝ → ℂ := fun y => (y:ℂ)^(-1/2:ℂ)*packet (J.product Finset.univ)
    (coefficient q w) (exponent q) (Real.log y)
  have he : cuspLift 0 (principalPacket q J w) =ᵐ[cuspMeasure] g ∘ Prod.snd := by
    rw [cuspMeasure,Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with xy hxy
    exact principalPacket_mellin q J w xy (lt_trans (by norm_num) hxy.2)
  have hcomp : MemLp (g ∘ Prod.snd) 2 cuspMeasure := hprincipal.ae_eq he
  let μ : Measure ℝ := volume.restrict (Ioc (-1/2:ℝ) (1/2))
  let ν : Measure ℝ := volume.restrict (Ioi (2:ℝ))
  letI : IsProbabilityMeasure μ := ⟨by simp [μ,Real.volume_Ioc]; norm_num⟩
  have hpres : MeasurePreserving Prod.snd (μ.prod ν) ν := measurePreserving_snd
  have hgm : AEStronglyMeasurable g ν := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul
    · apply ContinuousOn.cpow_const (show ContinuousOn (fun y : ℝ => (y:ℂ)) _ by fun_prop)
      intro y hy
      exact Complex.ofReal_mem_slitPlane.mpr (lt_trans (by norm_num : (0:ℝ)<2) hy)
    · exact (packet_continuous _ _ _).comp_continuousOn
        (Real.continuousOn_log.mono (fun _ hy => ne_of_gt (lt_trans (by norm_num) hy)))
  have hg : MemLp g 2 ν := by
    apply (memLp_map_measure_iff (hpres.map_eq.symm ▸ hgm) hpres.aemeasurable).mpr at hcomp
    simpa only [hpres.map_eq] using hcomp
  exact active_exponent_negative_of_mellin_memLp _ _ _ (exponent_injective q).injOn hg hp hcp

private theorem lambda_ne_right {s : ℂ} (hs : 1 ≤ s.re) :
    reflectedCompletedLambda s ≠ 0 :=
  mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
    (riemannZeta_ne_zero_of_one_le_re hs)

private theorem lambda_ne_left {s : ℂ} (hs : s.re ≤ 0) (hi : s.im ≠ 0) :
    reflectedCompletedLambda s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro he; exact hi (by rw [he]; rfl)
  have he : reflectedCompletedLambda s = completedRiemannZeta s := by
    rw [reflectedCompletedLambda,riemannZeta_def_of_ne_zero hs0]
    field_simp [gammaR_ne_zero_of_im_ne hi]
  have hr : 1 ≤ (1-s).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  rw [he,← completedRiemannZeta_one_sub s,
    completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE (by linarith : 0 < (1-s).re)]
  exact lambda_ne_right hr

/-- Every nonzero finite complete quarter-lattice packet fails actual native cusp admission. -/
theorem completePacket_memLp_iff_weights_zero (q : XiZeroCopy) (J : Finset ℤ) (w : ℤ → ℂ) :
    MemLp (cuspLift 0 (completePacket q J w)) 2 cuspMeasure ↔
      ∀ j ∈ J, w j = 0 := by
  constructor
  · intro h j hj
    by_contra hw
    have huim : (shiftedParameter q j).im ≠ 0 := by
      have hq := xi_divisor_support_im_ne_zero q.1
      simp only [shiftedParameter,physicalAngularParameter_eq,Complex.add_im,
        Complex.div_ofNat_im,Complex.sub_im,Complex.one_im,Complex.intCast_im,
        zero_div,add_zero,sub_zero]
      exact div_ne_zero hq (by norm_num)
    by_cases hu : 0 ≤ (shiftedParameter q j).re
    · have hc : coefficient q w (j,true) ≠ 0 := by
        apply mul_ne_zero hw
        apply lambda_ne_right
        norm_num [Complex.mul_re]
        linarith
      have hn := admitted_exponent_negative q J w h
        (show (j,true) ∈ J.product Finset.univ by simp [hj]) hc
      simp only [exponent,d4BMCuspSign,if_true,Int.cast_one,one_mul] at hn
      exact not_lt_of_ge hu hn
    · have hc : coefficient q w (j,false) ≠ 0 := by
        apply mul_ne_zero hw
        apply lambda_ne_left
        · norm_num [Complex.mul_re]
          linarith
        · simpa using mul_ne_zero (show (2:ℝ)≠0 by norm_num) huim
      have hn := admitted_exponent_negative q J w h
        (show (j,false) ∈ J.product Finset.univ by simp [hj]) hc
      simp only [exponent,d4BMCuspSign,Bool.false_eq_true,if_false,Int.cast_neg,
        Int.cast_one,neg_one_mul,Complex.neg_re] at hn
      linarith
  · intro h
    have he : cuspLift 0 (completePacket q J w) = 0 := by
      funext xy
      simp only [cuspLift,completePacket]
      rw [Finset.sum_eq_zero (fun j hj => by rw [h j hj,zero_mul]),mul_zero]
      rfl
    rw [he]
    exact MemLp.zero

/-- An admitted proposed limit has finite native L² error against a finite packet only for zero weights. -/
theorem completePacket_error_memLp_iff_weights_zero (q : XiZeroCopy) (J : Finset ℤ)
    (w : ℤ → ℂ) {v : ℝ × ℝ → ℂ} (hv : MemLp v 2 cuspMeasure) :
    MemLp (cuspLift 0 (completePacket q J w)-v) 2 cuspMeasure ↔
      ∀ j ∈ J, w j = 0 := by
  rw [← completePacket_memLp_iff_weights_zero q J w]
  constructor
  · intro h
    simpa only [sub_add_cancel] using h.add hv
  · intro h
    exact h.sub hv

/-- A native-convergent resummation with eventually L² errors must have zero finite packet weights eventually. -/
theorem finitePacket_errors_force_eventually_zero (q : XiZeroCopy)
    (J : ℕ → Finset ℤ) (w : ℕ → ℤ → ℂ) {v : ℝ × ℝ → ℂ} (hv : MemLp v 2 cuspMeasure)
    (h : ∀ᶠ n in Filter.atTop,
      MemLp (cuspLift 0 (completePacket q (J n) (w n))-v) 2 cuspMeasure) :
    ∀ᶠ n in Filter.atTop, ∀ j ∈ J n, w n j = 0 := by
  filter_upwards [h] with n hn
  exact (completePacket_error_memLp_iff_weights_zero q (J n) (w n) hv).mp hn

/-- Every shifted complete field lies in the scalar entire-transform fibre used by this occurrence attempt. -/
theorem shifted_casimir_same_entire_target (q : XiZeroCopy) (j : ℤ) :
    SelbergScatteringEntireTransform.casimirTransform
      ((1/2+shiftedParameter q j)*(1-(1/2+shiftedParameter q j))) =
        SelbergScatteringEntireXiPackets.xiEntireTarget q := by
  have hp : Function.Periodic (fun s : ℂ =>
      SelbergScatteringEntireTransform.casimirTransform (s*(1-s))) (1/4:ℂ) :=
    SelbergScatteringEntireXiPackets.casimirTransform_quarter_exponent_shift
  have he := hp.int_mul j ((q.1:ℂ)/2)
  have hs : 1/2+shiftedParameter q j = (q.1:ℂ)/2+(j:ℂ)*(1/4) := by
    rw [shiftedParameter,physicalAngularParameter_eq]
    ring
  simpa only [hs,SelbergScatteringEntireXiPackets.xiEntireTarget] using he

end
end RHTower.SelbergScatteringFiniteQuarterPacket
