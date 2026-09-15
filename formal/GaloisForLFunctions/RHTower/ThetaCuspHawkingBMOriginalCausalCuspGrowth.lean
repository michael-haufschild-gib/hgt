import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularGrowth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCausalAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCuspJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGreenProfileBounds

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricSourceJets

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace RHTower.D4BMOriginalCausalCuspGrowth
open D4BMCausalCusp D4BMNativeCuspJets D4BMNativeAngularGrowth D4BMNativeAngularCurrent
open D4BMNativeCircle D4BMSquareCuspJets D4BMOriginalCausalAdmission D4BMOriginalCausalPotential
open D4BMJointSource D4BMModularCore D4BMCausalKernel
noncomputable section
set_option autoImplicit false

/-- The literal null-source rectangle controls the complete sampled circle
radius independently of the outgoing endpoint. -/
theorem null_radius_ingoing_bound {p r a b : ℝ} (hp : 0 ≤ p)
    (ha : a ∈ Icc 0 p) (hb : b ∈ Icc 0 r) :
    0 ≤ radius p r a b ∧ radius p r a b ≤ p+Real.log 6 := by
  obtain ⟨hz,hbnd⟩ := nullInvariant_ingoing_bound hp ha.1 hb.1 ha.2 hb.2
  have hr : radius p r a b=Real.arcosh
      (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)) := by
    simp only [radius,max_eq_right hz]
  rw [hr]
  refine ⟨Real.arcosh_nonneg hz,?_⟩
  apply Real.exp_le_exp.mp
  calc
    _ ≤ 2*Real.cosh (Real.arcosh (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2))) := by
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-Real.arcosh (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)))]
    _ ≤ 6*Real.exp p := by rw [Real.cosh_arcosh hz]; linarith
    _ = Real.exp (p+Real.log 6) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<6)]
      ring

private theorem integral_half_decay_le_two (p : ℝ) :
    (∫ a in (0:ℝ)..p, Real.exp (-a/2)) ≤ 2 := by
  have hd (a : ℝ) : HasDerivAt (fun x : ℝ => -2*Real.exp (-x/2)) (Real.exp (-a/2)) a := by
    convert! (((Real.hasDerivAt_exp (-a/2)).comp a
      ((hasDerivAt_id a).neg.div_const 2)).const_mul (-2)) using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hd a)
    ((show Continuous (fun a : ℝ => Real.exp (-a/2)) by fun_prop).intervalIntegrable 0 p)]
  simp only [neg_zero,zero_div,Real.exp_zero,mul_one]
  linarith [Real.exp_pos (-p/2)]

private theorem integral_half_decay_bound {p K : ℝ} (hp : 0 ≤ p) (hK : 0 ≤ K)
    {f : ℝ → ℂ} (hf : ∀ a ∈ Icc (0:ℝ) p, ‖f a‖ ≤ K*Real.exp (-a/2)) :
    ‖∫ a in (0:ℝ)..p, f a‖ ≤ 2*K := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) hp
    (Filter.Eventually.of_forall (fun a (ha : a ∈ Ioc (0:ℝ) p) => hf a ⟨ha.1.le,ha.2⟩))
    ((show Continuous (fun a : ℝ => K*Real.exp (-a/2)) by fun_prop).intervalIntegrable 0 p)
  rw [intervalIntegral.integral_const_mul] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (integral_half_decay_le_two p) hK).trans_eq (mul_comm K 2))

private theorem rectangle_decay_bound {p r K : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hK : 0 ≤ K)
    {f : ℝ → ℝ → ℂ}
    (hf : ∀ a ∈ Icc 0 p, ∀ b ∈ Icc 0 r, ‖f a b‖ ≤ K*Real.exp (-(a+b)/2)) :
    ‖∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b‖ ≤ 4*K := by
  have h := integral_half_decay_bound hp (show 0 ≤ 2*K by positivity) (f:=fun a => ∫ b in (0:ℝ)..r,f a b) (by
    intro a ha
    have h := integral_half_decay_bound hr (show 0 ≤ K*Real.exp (-a/2) by positivity)
      (f:=f a) (by
        intro b hb
        convert hf a ha b hb using 1
        rw [mul_assoc,← Real.exp_add]
        congr 2
        ring)
    simpa only [mul_assoc] using h)
  convert h using 1; ring

/-- Every actual angular derivative of the original signed causal integral has
arbitrary cusp decay and growth only in ingoing time, uniformly in outgoing time. -/
theorem response_angular_growth (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (word : List (Fin 2)) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ p r x k : ℝ, 0 ≤ p → 0 ≤ r → 0 ≤ k →
      ‖coordinateJet word (responseRemainder q (physicalRate q br) amp p r) ![x,k]‖ ≤
        C*Real.exp (B*p-(N:ℝ)*k) := by
  obtain ⟨C,B,hC,hB,h⟩ := native_angular_jet_bound q word N
  obtain ⟨W,hW,hw⟩ := physical_nullSource_decay q br amp
  refine ⟨C*W*Real.exp (B*Real.log 6),B,by positivity,hB,?_⟩
  intro p r x k hp hr hk
  let K := C*W*Real.exp (B*(p+Real.log 6)-(N:ℝ)*k)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : ∀ a ∈ Icc 0 p, ∀ b ∈ Icc 0 r,
      ‖nativeJet (word.map Fin.succ) (nativeRemainder q) ![radius p r a b,x,k]*
        sourceWeight (physicalRate q br) amp a b‖ ≤ K*Real.exp (-(a+b)/2) := by
    intro a ha b hb
    have hd := null_radius_ingoing_bound hp ha hb
    have hn := h (radius p r a b) x k hd.1 hk
    change ‖nativeJet (word.map Fin.succ) (nativeRemainder q) ![radius p r a b,x,k]‖ ≤ _ at hn
    rw [norm_mul]
    calc
      _ ≤ (C*Real.exp (B*(radius p r a b)-(N:ℝ)*k))*(W*Real.exp (-(a+b)/2)) :=
        mul_le_mul hn (hw a b) (norm_nonneg _) (by positivity)
      _ ≤ (C*Real.exp (B*(p+Real.log 6)-(N:ℝ)*k))*(W*Real.exp (-(a+b)/2)) := by
        gcongr
        exact hd.2
      _ = _ := by dsimp [K]; ring
  rw [responseRemainder_jet_integral q (physicalRate q br) amp ⟨p,hp⟩ ⟨r,hr⟩ word ![x,k]]
  change ‖(1/4:ℂ)*(∫ a in (0:ℝ)..p,∫ b in (0:ℝ)..r,
    nativeJet (word.map Fin.succ) (nativeRemainder q) ![radius p r a b,x,k]*
      sourceWeight (physicalRate q br) amp a b)‖ ≤ _
  rw [norm_mul]
  have hc : ‖(1/4:ℂ)‖=(1/4:ℝ) := by norm_num
  rw [hc]
  calc
    _ ≤ (1/4:ℝ)*(4*K) := mul_le_mul_of_nonneg_left (rectangle_decay_bound hp hr hK hb) (by norm_num)
    _ = C*W*Real.exp (B*Real.log 6)*Real.exp (B*p-(N:ℝ)*k) := by
      dsimp [K]
      rw [mul_assoc (C*W),← Real.exp_add]
      rw [show B*Real.log 6+(B*p-(N:ℝ)*k)=B*(p+Real.log 6)-(N:ℝ)*k by ring]
      ring

private theorem lift_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p r : ℝ, p < r →
      ‖nullLift (physicalRate q br) amp p r‖ ≤ C := by
  let s := physicalRate q br
  obtain ⟨C,hC,hc⟩ := sourceAmplitude_profile_norm_le_exp s 0 amp 1
    (fun u : ℝ => (-s*(s-1)/4)*(u:ℂ)^3) (by fun_prop)
  have hs : (2*s).re ≤ -(0:ℝ) := by
    have h := currentRate_re_lt q br
    change (2*s).re < -2 at h
    linarith
  obtain ⟨D,hD,hd⟩ := timeOnset_pair_bound (2*s) 0 hs
  refine ⟨C*D,mul_nonneg hC hD,?_⟩
  intro p r hpr
  have hL := hc ((p-r)/2) (by linarith)
  have he : sourceAmplitude s 0 amp 1 ((p-r)/2)*((-s*(s-1)/4)*(radialUnit ((p-r)/2):ℂ)^3)=
      radialLift s 0 amp 1 ((p-r)/2) := by unfold radialLift; ring
  rw [he] at hL
  simp only [Complex.zero_re,zero_mul,Real.exp_zero,mul_one] at hL
  have hT : ‖timeOnset (2*s) p‖ ≤ D := by
    have h := hd p
    simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at h
    linarith [norm_nonneg (timeOnsetFirst (2*s) p)]
  exact (norm_mul _ _).trans_le (mul_le_mul hL hT (norm_nonneg _) hC)

/-- Uniform outgoing-time control of every angular jet of the original causal
remainder, including its unchanged onset lift. -/
theorem original_angular_growth (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (word : List (Fin 2)) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ p r x k : ℝ, 0 ≤ p → p < r → 0 ≤ k →
      ‖coordinateJet word (D4BMOriginalCuspJets.remainder q br amp p r) ![x,k]‖ ≤
        C*Real.exp (B*p-(N:ℝ)*k) := by
  obtain ⟨C,B,hC,hB,h⟩ := response_angular_growth q br amp word N
  obtain ⟨D,E,hD,hE,hn⟩ := native_angular_jet_bound q word N
  obtain ⟨L,hL,hl⟩ := lift_bound q br amp
  refine ⟨C+L*D,B,by positivity,hB,?_⟩
  intro p r x k hp hpr hk
  have hn' := hn 0 x k le_rfl hk
  change ‖nativeJet (word.map Fin.succ) (nativeRemainder q) ![0,x,k]‖ ≤ _ at hn'
  simp only [mul_zero,zero_sub,← neg_mul] at hn'
  rw [D4BMOriginalCuspJets.original_remainder_jet]
  calc
    _ ≤ ‖coordinateJet word (responseRemainder q (physicalRate q br) amp p r) ![x,k]‖+
      ‖nullLift (physicalRate q br) amp p r*nativeJet (word.map Fin.succ) (nativeRemainder q) ![0,x,k]‖ := norm_add_le _ _
    _ ≤ C*Real.exp (B*p-(N:ℝ)*k)+L*(D*Real.exp (-(N:ℝ)*k)) :=
      add_le_add (h p r x k hp (hp.trans hpr.le) hk)
        ((norm_mul _ _).trans_le (mul_le_mul (hl p r hpr) hn' (norm_nonneg _) hL))
    _ ≤ C*Real.exp (B*p-(N:ℝ)*k)+L*(D*Real.exp (B*p-(N:ℝ)*k)) := by
      gcongr
      nlinarith [mul_nonneg hB hp]
    _ = _ := by ring

private def baseWord (j : Fin 5) : List (Fin 2) := ![[],[1],[0,0],[1,1],[0]] j

private theorem remainder_smooth (q : XiZeroCopy) (br : Bool) (amp : ℂ) (p v : ℝ) :
    ContDiff ℝ ∞ (D4BMOriginalCuspJets.remainder q br amp p v) := by
  have hF := (originalPotential_angular_smooth q br amp p v).comp
    (show ContDiff ℝ ∞ (fun z : Fin 2 → ℝ => (z 0,z 1)) by fun_prop)
  have hP : ContDiff ℝ ∞ (D4BMOriginalCuspJets.principal q br amp p v) := by
    unfold D4BMOriginalCuspJets.principal
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)
  exact hF.sub hP

private theorem source_jet_coordinate (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (p L x k : ℝ) :
    D4BMOriginalReaderCuspBounds.sourceJet q br amp j p L x k=
      coordinateJet (baseWord j) (D4BMOriginalCuspJets.remainder q br amp p (p+L)) ![x,k] := by
  let F := D4BMOriginalCuspJets.remainder q br amp p (p+L)
  have hF := remainder_smooth q br amp p (p+L)
  have h := D4BMOriginalMetricSourceJets.coordinate_base_jets F hF x k
  fin_cases j
  · rfl
  · exact h.1.symm
  · exact h.2.1.symm
  · exact h.2.2.symm
  · change deriv (fun t => F ![t,k]) x=
      GaloisForLFunctions.HTGeometry.ScalarTwoJet.coordDeriv 0 F ![x,k]
    have ht : HasDerivAt (fun t : ℝ => (![t,k] : Fin 2 → ℝ)) (Pi.single 0 1) x := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · simpa using! hasDerivAt_id x
      · simpa using! hasDerivAt_const x k
    exact ((hF.differentiable (by simp) ![x,k]).hasFDerivAt.comp_hasDerivAt x ht).deriv

/-- The five actual metric source operations inherit the original causal
estimate on the complete exterior, including arbitrarily small positive collars. -/
theorem source_jet_growth (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ p L x k : ℝ, 0 ≤ p → 0 < L → 0 ≤ k →
      ‖D4BMOriginalReaderCuspBounds.sourceJet q br amp j p L x k‖ ≤
        C*Real.exp (B*p-(N:ℝ)*k) := by
  obtain ⟨C,B,hC,hB,h⟩ := original_angular_growth q br amp (baseWord j) N
  refine ⟨C,B,hC,hB,?_⟩
  intro p L x k hp hL hk
  rw [source_jet_coordinate]
  exact h p (p+L) x k hp (by linarith) hk

/-- Physical Laplace damping absorbs the derived ingoing growth of each actual
metric source jet, leaving one common integrable time majorant. -/
theorem source_jet_damped (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, B+1 ≤ w.re →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p L x k : ℝ, 0 ≤ p → 0 < L → 0 ≤ k →
        ‖Complex.exp (-w*(p:ℂ))*D4BMOriginalReaderCuspBounds.sourceJet q br amp j p L x k‖ ≤
          C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨C,B,hC,hB,h⟩ := source_jet_growth q br amp j N
  refine ⟨B,hB,fun w hw => ⟨C,hC,?_⟩⟩
  intro p L x k hp hL hk
  rw [norm_mul,Complex.norm_exp]
  have he : (-w*(p:ℂ)).re= -w.re*p := by simp
  rw [he]
  calc
    _ ≤ Real.exp (-w.re*p)*(C*Real.exp (B*p-(N:ℝ)*k)) :=
      mul_le_mul_of_nonneg_left (h p L x k hp hL hk) (Real.exp_nonneg _)
    _ = C*Real.exp ((B-w.re)*p-(N:ℝ)*k) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring
    _ ≤ C*Real.exp (-p-(N:ℝ)*k) := by gcongr; nlinarith
    _ = _ := by rw [show -p-(N:ℝ)*k=-(N:ℝ)*k+(-p) by ring,Real.exp_add,mul_assoc]

end
end RHTower.D4BMOriginalCausalCuspGrowth
