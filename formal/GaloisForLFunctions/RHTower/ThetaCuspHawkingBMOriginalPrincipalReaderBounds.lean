import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalReaderCuspBounds

/-! Uniform horizon control of every canonical principal source coefficient and
its products with both signed angular reader tails and both radial reader branches.
These are convergence-half-plane estimates; full metric/QNM matching remains open. -/

open Set Filter Topology
namespace RHTower.D4BMOriginalPrincipalHorizonBounds
open D4BMJointSource D4BMModularCore D4BMNativeResponse D4BMOriginalCausalAdmission
open D4BMOriginalHorizonTimeTrace D4BMOriginalCharacteristicTransform D4BMOriginalCollarCurrentBounds
noncomputable section
set_option autoImplicit false

private theorem principalExponent_re (q : XiZeroCopy) (i : Fin 3) :
    0 ≤ (principalExponent q i).re ∧ (principalExponent q i).re ≤ 2 := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  fin_cases i <;> norm_num [principalExponent,Complex.mul_re] <;> constructor <;> linarith [hq.1,hq.2]

private theorem reduced_trace_bound (q : XiZeroCopy) (br : Bool) (amp m : ℂ) (hm : 0 ≤ m.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ, 0 < p →
      ‖reducedTrace q br amp m p‖ ≤ C*Real.exp (m.re*p) ∧
      ∀ L : ℝ, 0 < L →
      ‖collarValue (-m) (physicalRate q br) amp L p-reducedTrace q br amp m p‖ ≤
        C*Real.exp (-L)*Real.exp (m.re*p) := by
  obtain ⟨C,hC,h⟩ := physical_null_horizon_traces q br amp m hm
  refine ⟨C,hC,?_⟩
  intro p hp
  obtain ⟨H,Hd,hH,hHd,hbound⟩ := h p hp
  have he : reducedTrace q br amp m p=H := hH.limUnder_eq
  rw [he]
  constructor
  · have hd := (hbound p le_rfl).1
    simpa only [nullValue,sub_self,zero_div,radialResponse_boundary,sub_zero,Real.exp_zero,mul_one] using hd
  · intro L hL
    have hd := (hbound (p+L) (by linarith)).1
    simpa only [collarValue,show p-(p+L)=-L by ring,norm_sub_rev] using hd

/-- The original canonical principal coefficient on the physical collar. -/
def coefficient (q : XiZeroCopy) (br : Bool) (amp : ℂ) (i : Fin 3) (p L : ℝ) : ℂ :=
  D4BMOriginalCuspJets.coefficient q br amp p (p+L) i

/-- Its horizon value retains the original reduced trace and onset lift. -/
def horizonCoefficient (q : XiZeroCopy) (br : Bool) (amp : ℂ) (i : Fin 3) (p : ℝ) : ℂ :=
  principalAmplitude q i*(reducedTrace q br amp (principalExponent q i) p+
    liftHorizon (physicalRate q br) amp*timeOnset (2*physicalRate q br) p)

private theorem coefficient_eq_collar (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (i : Fin 3) (p L : ℝ) :
    coefficient q br amp i p L=principalAmplitude q i*
      (collarValue (-principalExponent q i) (physicalRate q br) amp L p+
        liftCoefficient (physicalRate q br) amp L*timeOnset (2*physicalRate q br) p) := by
  simp only [coefficient,D4BMOriginalCuspJets.coefficient,principalNullResponse,
    D4BMOriginalCausalPotential.nullLift,collarValue,nullValue,liftCoefficient,
    show (p-(p+L))/2=-L/2 by ring]
  ring

/-- All original principal channels have one source-time growth rate and the
geometric horizon error required by their products with angular reader tails. -/
theorem original_principal_coefficient_horizon_estimate (q : XiZeroCopy) (br : Bool)
    (amp : ℂ) (i : Fin 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖horizonCoefficient q br amp i p‖ ≤ B*Real.exp (2*p) ∧
      ‖coefficient q br amp i p L-horizonCoefficient q br amp i p‖ ≤
        B*Real.exp (-L)*Real.exp (2*p) := by
  have hm := principalExponent_re q i
  obtain ⟨C,hC,hc⟩ := reduced_trace_bound q br amp (principalExponent q i) hm.1
  obtain ⟨E,hE,he⟩ := lift_coefficient_error (physicalRate q br) amp
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  obtain ⟨D,hD,hd⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  let A := principalAmplitude q i
  let V := liftHorizon (physicalRate q br) amp
  let B := ‖A‖*(C+(E+‖V‖)*D)
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with L heL hL p hp
  have hO : ‖timeOnset (2*physicalRate q br) p‖ ≤ D := by
    have h := (le_add_of_nonneg_right (norm_nonneg (timeOnsetFirst (2*physicalRate q br) p))).trans (hd p)
    simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using h
  have hexp : Real.exp ((principalExponent q i).re*p) ≤ Real.exp (2*p) := by gcongr; exact hm.2
  have hone : 1 ≤ Real.exp (2*p) := Real.one_le_exp (by positivity)
  have hv : ‖reducedTrace q br amp (principalExponent q i) p‖ ≤ C*Real.exp (2*p) :=
    (hc p hp).1.trans (mul_le_mul_of_nonneg_left hexp hC)
  have herr : ‖collarValue (-principalExponent q i) (physicalRate q br) amp L p-
      reducedTrace q br amp (principalExponent q i) p‖ ≤ C*Real.exp (-L)*Real.exp (2*p) :=
    ((hc p hp).2 L hL).trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  constructor
  · unfold horizonCoefficient
    rw [norm_mul]
    calc
      _ ≤ ‖A‖*(‖reducedTrace q br amp (principalExponent q i) p‖+‖V‖*‖timeOnset (2*physicalRate q br) p‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ ‖A‖*(C*Real.exp (2*p)+‖V‖*D) := by gcongr
      _ ≤ B*Real.exp (2*p) := by
        change _ ≤ ‖A‖*(C+(E+‖V‖)*D)*Real.exp (2*p)
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
        rw [add_mul]
        apply add_le_add_right
        calc
          ‖V‖*D ≤ (E+‖V‖)*D := by gcongr; linarith
          _ ≤ (E+‖V‖)*D*Real.exp (2*p) := le_mul_of_one_le_right (by positivity) hone
  · rw [coefficient_eq_collar]
    change ‖A*(collarValue (-principalExponent q i) (physicalRate q br) amp L p+
      liftCoefficient (physicalRate q br) amp L*timeOnset (2*physicalRate q br) p)-
      A*(reducedTrace q br amp (principalExponent q i) p+V*timeOnset (2*physicalRate q br) p)‖ ≤ _
    rw [show A*(collarValue (-principalExponent q i) (physicalRate q br) amp L p+
        liftCoefficient (physicalRate q br) amp L*timeOnset (2*physicalRate q br) p)-
        A*(reducedTrace q br amp (principalExponent q i) p+V*timeOnset (2*physicalRate q br) p)=
      A*((collarValue (-principalExponent q i) (physicalRate q br) amp L p-
        reducedTrace q br amp (principalExponent q i) p)+
        (liftCoefficient (physicalRate q br) amp L-V)*timeOnset (2*physicalRate q br) p) by ring,norm_mul]
    calc
      _ ≤ ‖A‖*(‖collarValue (-principalExponent q i) (physicalRate q br) amp L p-
          reducedTrace q br amp (principalExponent q i) p‖+
          ‖liftCoefficient (physicalRate q br) amp L-V‖*‖timeOnset (2*physicalRate q br) p‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ ‖A‖*(C*Real.exp (-L)*Real.exp (2*p)+(E*Real.exp (-L))*D) := by gcongr
      _ ≤ B*Real.exp (-L)*Real.exp (2*p) := by
        have hd : E*Real.exp (-L)*D ≤ (E+‖V‖)*D*Real.exp (-L)*Real.exp (2*p) := by
          calc
            _ = E*D*Real.exp (-L)*1 := by ring
            _ ≤ (E+‖V‖)*D*Real.exp (-L)*Real.exp (2*p) := by gcongr; exact le_add_of_nonneg_right (norm_nonneg V)
        calc
          _ ≤ ‖A‖*(C*Real.exp (-L)*Real.exp (2*p)+(E+‖V‖)*D*Real.exp (-L)*Real.exp (2*p)) := by gcongr
          _ = B*Real.exp (-L)*Real.exp (2*p) := by dsimp [B]; ring

end
end RHTower.D4BMOriginalPrincipalHorizonBounds

namespace RHTower.D4BMOriginalAngularReaderBounds
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMJointSource D4BMModularCore
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section
set_option autoImplicit false

private theorem weighted_vertical (u nu w : ℂ) (a : ℝ) (d : ℕ) (neg : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 1 ≤ z 1 →
      ‖(z 1:ℂ)^w*coordDeriv 1 (value u nu a d neg) z‖ ≤ C := by
  obtain ⟨A,hA,ha⟩ := weighted_value_bounded u nu w (a-1) d neg 1 (by norm_num)
  obtain ⟨B,hB,hb⟩ := weighted_value_bounded u (nu+1) w a (d+1) neg 1 (by norm_num)
  obtain ⟨C,hC,hc⟩ := weighted_value_bounded u (nu-1) w a (d+1) neg 1 (by norm_num)
  refine ⟨‖(a:ℂ)‖*A+‖(Real.pi:ℂ)‖*(B+C),by positivity,?_⟩
  intro z hz
  rw [value_coordDeriv_one u nu a d neg z (by linarith)]
  rw [show (z 1:ℂ)^w*((a:ℂ)*value u nu (a-1) d neg z-
    (Real.pi:ℂ)*(value u (nu+1) a (d+1) neg z+value u (nu-1) a (d+1) neg z))=
    (a:ℂ)*((z 1:ℂ)^w*value u nu (a-1) d neg z)-
    (Real.pi:ℂ)*((z 1:ℂ)^w*value u (nu+1) a (d+1) neg z+
      (z 1:ℂ)^w*value u (nu-1) a (d+1) neg z) by ring]
  apply (norm_sub_le _ _).trans
  rw [norm_mul (a:ℂ),norm_mul (Real.pi:ℂ)]
  exact add_le_add (mul_le_mul_of_nonneg_left (ha z hz) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hb z hz) (hc z hz))) (norm_nonneg _))

/-- Actual value and ordinary vertical derivative of the full signed reader tail. -/
def tailJet (r : XiZeroCopy) (d : Bool) (z : Fin 2 → ℝ) : ℂ :=
  if d then coordDeriv 1 (tail (physicalAngularParameter r)) z else tail (physicalAngularParameter r) z

/-- Every complex cusp weight is bounded for both reader operations, uniformly
in the horizontal variable. Both signed Fourier families are retained. -/
theorem tailJet_weighted (r : XiZeroCopy) (d : Bool) (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 1 ≤ z 1 → ‖(z 1:ℂ)^w*tailJet r d z‖ ≤ C := by
  cases d
  · exact weighted_tail_bounded (physicalAngularParameter r) w 1 (by norm_num)
  · obtain ⟨A,hA,ha⟩ := weighted_vertical (physicalAngularParameter r) (physicalAngularParameter r) w (1/2) 0 false
    obtain ⟨B,hB,hb⟩ := weighted_vertical (physicalAngularParameter r) (physicalAngularParameter r) w (1/2) 0 true
    refine ⟨2*(A+B),by positivity,?_⟩
    intro z hz
    simp only [tailJet,ite_true,tail_vertical_eq _ z (by linarith)]
    rw [show (z 1:ℂ)^w*(2*(coordDeriv 1 (value (physicalAngularParameter r) (physicalAngularParameter r) (1/2) 0 false) z+
      coordDeriv 1 (value (physicalAngularParameter r) (physicalAngularParameter r) (1/2) 0 true) z))=
      2*((z 1:ℂ)^w*coordDeriv 1 (value (physicalAngularParameter r) (physicalAngularParameter r) (1/2) 0 false) z+
      (z 1:ℂ)^w*coordDeriv 1 (value (physicalAngularParameter r) (physicalAngularParameter r) (1/2) 0 true) z) by ring,
      norm_mul,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (ha z hz) (hb z hz))) (by norm_num)

private theorem exp_cpow (a : ℂ) (k : ℝ) :
    (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring

/-- Multiplying either actual reader tail jet by any principal source exponent
still gives arbitrary quantitative cusp decay. -/
theorem principal_tail_bound (r : XiZeroCopy) (d : Bool) (a : ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x k : ℝ, 0 ≤ k →
      ‖Complex.exp (a*(k:ℂ))*tailJet r d ![x,Real.exp k]‖ ≤ C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨C,hC,h⟩ := tailJet_weighted r d (a+(N:ℂ))
  refine ⟨C,hC,?_⟩
  intro x k hk
  have hb := h ![x,Real.exp k] (Real.one_le_exp hk)
  simp only [Matrix.cons_val,exp_cpow] at hb
  have he : Complex.exp (a*(k:ℂ))*tailJet r d ![x,Real.exp k]=
      Complex.exp (-(N:ℂ)*(k:ℂ))*(Complex.exp ((a+(N:ℂ))*(k:ℂ))*tailJet r d ![x,Real.exp k]) := by
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    ring
  rw [he,norm_mul,Complex.norm_exp]
  have hn : (-(N:ℂ)*(k:ℂ)).re=-(N:ℝ)*k := by simp
  rw [hn]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)).trans_eq (mul_comm _ _)

end
end RHTower.D4BMOriginalAngularReaderBounds

namespace RHTower.D4BMOriginalPrincipalHorizonBounds
open D4BMJointSource D4BMModularCore D4BMOriginalReaderCuspBounds
noncomputable section
set_option autoImplicit false

/-- Each original principal source channel couples to both radial reader
branches with an integrable source-time bound in the derived half-plane. -/
theorem principal_reader_error (q r : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (i : Fin 3) (hwi : w.im ≠ 0) (hw : 3 ≤ w.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖Complex.exp (-w*(p:ℂ))*(reader r w L*coefficient q br amp i p L-
        horizonReader r w*horizonCoefficient q br amp i p)‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-p) := by
  obtain ⟨C,hC,hc⟩ := original_principal_coefficient_horizon_estimate q br amp i
  obtain ⟨D,hD,hd⟩ := D4BMOriginalCollarCurrentBounds.normalizable_reader_collar_error w (physicalRadialFrequency r) hwi
  let beta := horizonReader r w
  let K := ‖beta‖+2*D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(K+D)*C,by positivity,?_⟩
  filter_upwards [hc,hd,eventually_gt_atTop (0:ℝ)] with L hcL hdL hL p hp
  let S := Real.exp (-L)+Real.exp (-w.re*L)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hS2 : S ≤ 2 := by
    have h1 : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : Real.exp (-w.re*L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    dsimp [S]
    linarith
  have he : ‖reader r w L-beta‖ ≤ D*S := hdL
  have hn : ‖reader r w L‖ ≤ K := by
    have ht := norm_sub_norm_le (reader r w L) beta
    have hm := mul_le_mul_of_nonneg_left hS2 hD
    dsimp [K]
    linarith
  obtain ⟨hv,herr⟩ := hcL p hp
  have ht : ‖reader r w L*coefficient q br amp i p L-beta*horizonCoefficient q br amp i p‖ ≤
      (K+D)*C*S*Real.exp (2*p) := by
    rw [show reader r w L*coefficient q br amp i p L-beta*horizonCoefficient q br amp i p=
      reader r w L*(coefficient q br amp i p L-horizonCoefficient q br amp i p)+
      (reader r w L-beta)*horizonCoefficient q br amp i p by ring]
    calc
      _ ≤ ‖reader r w L‖*‖coefficient q br amp i p L-horizonCoefficient q br amp i p‖+
        ‖reader r w L-beta‖*‖horizonCoefficient q br amp i p‖ := by
          simpa only [norm_mul] using norm_add_le
            (reader r w L*(coefficient q br amp i p L-horizonCoefficient q br amp i p))
            ((reader r w L-beta)*horizonCoefficient q br amp i p)
      _ ≤ K*(C*Real.exp (-L)*Real.exp (2*p))+(D*S)*(C*Real.exp (2*p)) :=
        add_le_add (mul_le_mul hn herr (norm_nonneg _) hK) (mul_le_mul he hv (norm_nonneg _) (by positivity))
      _ ≤ K*(C*S*Real.exp (2*p))+(D*S)*(C*Real.exp (2*p)) := by
        have hLS : Real.exp (-L) ≤ S := le_add_of_nonneg_right (Real.exp_nonneg _)
        gcongr
      _ = _ := by ring
  rw [norm_mul,Complex.norm_exp]
  have hew : (-w*(p:ℂ)).re=-w.re*p := by simp
  rw [hew]
  calc
    _ ≤ Real.exp (-w.re*p)*((K+D)*C*S*Real.exp (2*p)) := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
    _ = (K+D)*C*S*Real.exp ((2-w.re)*p) := by
      rw [show Real.exp (-w.re*p)*((K+D)*C*S*Real.exp (2*p))=
        ((K+D)*C*S)*(Real.exp (-w.re*p)*Real.exp (2*p)) by ring,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by gcongr; nlinarith

/-- The missing principal-source × full reader-tail terms have independent
cusp, horizon and time bounds, for both value and normal reader operations. -/
theorem principal_reader_tail_error (q r : XiZeroCopy) (br : Bool) (amp w a : ℂ)
    (i : Fin 3) (d : Bool) (N : ℕ) (hwi : w.im ≠ 0) (hw : 3 ≤ w.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p x k : ℝ, 0 < p → 0 ≤ k →
      ‖Complex.exp (-w*(p:ℂ))*(reader r w L*coefficient q br amp i p L-
        horizonReader r w*horizonCoefficient q br amp i p)*
        (Complex.exp (a*(k:ℂ))*D4BMOriginalAngularReaderBounds.tailJet r d ![x,Real.exp k])‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨B,hB,hb⟩ := principal_reader_error q r br amp w i hwi hw
  obtain ⟨C,hC,hc⟩ := D4BMOriginalAngularReaderBounds.principal_tail_bound r d a N
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  filter_upwards [hb] with L h p x k hp hk
  rw [norm_mul]
  calc
    _ ≤ (B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-p))*(C*Real.exp (-(N:ℝ)*k)) :=
      mul_le_mul (h p hp) (hc x k hk) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end RHTower.D4BMOriginalPrincipalHorizonBounds
