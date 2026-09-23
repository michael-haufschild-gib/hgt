import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalPrincipalChannels
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCuspJets

/-!
Exact matching of the literal and canonical principal subtractions.

The actual three Xi exponents are distinct. Weighted decay of the difference
and its first two log-height derivatives identifies every principal coefficient,
including the original restored onset lift. Consequently the canonical original
remainder inherits the uniform base-jet horizon and time-integral estimates.
The complete metric reader products and QNM matching remain separate obligations.
-/

open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMOriginalPrincipalMatching
open D4BMGlobalAngularResponse D4BMJointSource D4BMNativeCircle D4BMModularCore
open D4BMAngularSeries D4BMRetardedHorizonGeometry D4BMOriginalHorizonSourceJets D4BMOriginalHorizonForcingBound
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMOriginalBaseCircleJets D4BMSquareCuspJets
noncomputable section
set_option autoImplicit false
private abbrev Point := Fin 2 → ℝ

private theorem coordinate_height (f : Point → ℂ) (hf : ContDiff ℝ ∞ f) (x k : ℝ) :
    coordDeriv 1 f ![x,k]=deriv (fun t => f ![x,t]) k := by
  have hu : Function.update (![x,k] : Point) 1 k=![x,k] := by
    ext i
    fin_cases i <;> simp
  have hF : HasFDerivAt f (fderiv ℝ f ![x,k]) (Function.update (![x,k] : Point) 1 k) := by
    rw [hu]
    exact (hf.differentiable (by simp) ![x,k]).hasFDerivAt
  have h := hF.comp_hasDerivAt k (hasDerivAt_update (![x,k] : Point) 1 k)
  have he : (fun t => f (Function.update (![x,k] : Point) 1 t))=fun t => f ![x,t] := by
    funext t
    congr 1
    ext i
    fin_cases i <;> simp
  simpa only [coordDeriv,he,Function.update_eq_self,Matrix.cons_val_one,Matrix.cons_val_zero,
    Function.comp_def] using h.deriv.symm

private theorem coord_smooth (f : Point → ℂ) (hf : ContDiff ℝ ∞ f) (i : Fin 2) :
    ContDiff ℝ ∞ (coordDeriv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem originalRemainder_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) :
    ContDiff ℝ ∞ (D4BMOriginalCuspJets.remainder q branch amp p r) := by
  have hP : ContDiff ℝ ∞ (D4BMOriginalCuspJets.principal q branch amp p r) := by
    unfold D4BMOriginalCuspJets.principal
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul ((contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)
  exact ((D4BMOriginalCausalPotential.originalPotential_angular_smooth q branch amp p r).comp
    (show ContDiff ℝ ∞ (fun z : Point => (z 0,z 1)) by fun_prop)).sub hP

private theorem originalRemainder_weighted_jets (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : Ici (0:ℝ)) (x : ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*D4BMOriginalCuspJets.remainder q branch amp p r ![x,k]) atTop (𝓝 0) ∧
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*deriv (fun t => D4BMOriginalCuspJets.remainder q branch amp p r ![x,t]) k) atTop (𝓝 0) ∧
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*deriv (deriv (fun t => D4BMOriginalCuspJets.remainder q branch amp p r ![x,t])) k) atTop (𝓝 0) := by
  let f := D4BMOriginalCuspJets.remainder q branch amp p r
  have hF : ContDiff ℝ ∞ f := originalRemainder_smooth q branch amp p r
  have hd : (fun k => coordDeriv 1 f ![x,k])=deriv (fun k => f ![x,k]) :=
    funext (fun k => coordinate_height f hF x k)
  have hdd (k : ℝ) : coordDeriv 1 (coordDeriv 1 f) ![x,k]=deriv (deriv (fun t => f ![x,t])) k := by
    rw [coordinate_height _ (coord_smooth f hF 1),hd]
  refine ⟨D4BMOriginalCuspJets.original_remainder_jet_tendsto_zero q branch amp p r [] (fun _ => x) w,?_,?_⟩
  · have ht := D4BMOriginalCuspJets.original_remainder_jet_tendsto_zero q branch amp p r [1] (fun _ => x) w
    change Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*coordDeriv 1 f ![x,k]) atTop (𝓝 0) at ht
    simpa only [coordinate_height f hF] using ht
  · have ht := D4BMOriginalCuspJets.original_remainder_jet_tendsto_zero q branch amp p r [1,1] (fun _ => x) w
    change Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*coordDeriv 1 (coordDeriv 1 f) ![x,k]) atTop (𝓝 0) at ht
    simpa only [hdd] using ht

private theorem action_weighted_base_jet (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p rho x : ℝ) (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) (j : Fin 5) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      baseOperator j (actionRemainder (center q) (physicalRate q branch) amp p rho) x k) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt w.re
  obtain ⟨C,B,hC,hB,h⟩ := original_action_base_jet_horizon_estimate (center q) (physicalRate q branch) amp j N
  have ht := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr hN)).2 tendsto_id)
  apply squeeze_zero_norm' _ (by simpa using ht.const_mul (C*Real.exp (B*p)))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with k hk
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ Real.exp (w.re*k)*(C*Real.exp (B*p-(N:ℝ)*k)) := by
      gcongr
      exact (h p rho x k hp hr0 hr1 hk).1
    _ = (C*Real.exp (B*p))*Real.exp ((w.re-(N:ℝ))*k) := by
      rw [mul_assoc,← Real.exp_add,← mul_assoc,mul_comm (Real.exp _) C,mul_assoc,← Real.exp_add]
      congr 2
      ring

private def expSum (K c : Fin 3 → ℂ) (t : ℝ) := ∑ i : Fin 3, c i*Complex.exp (K i*(t:ℂ))
private theorem expSum_smooth (K c : Fin 3 → ℂ) : ContDiff ℝ ∞ (expSum K c) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

private theorem expSum_deriv (K c : Fin 3 → ℂ) :
    deriv (expSum K c)=expSum K (fun i => c i*K i) := by
  funext t
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro i _
  convert ((((hasDerivAt_id t).ofReal_comp).const_mul (K i)).cexp.const_mul (c i)) using 1
  all_goals (try simp only [id_eq,Complex.ofReal_one,mul_one])
  all_goals first | rfl | ring

private theorem expSum_second (K c : Fin 3 → ℂ) :
    deriv (deriv (expSum K c))=expSum K (fun i => c i*K i^(2 : ℕ)) := by
  rw [expSum_deriv,expSum_deriv]
  congr 1
  funext i
  ring

private theorem three_modes_unique (K c : Fin 3 → ℂ) (hK : Function.Injective K)
    (h0 : ∀ w : ℂ, Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*expSum K c k) atTop (𝓝 0))
    (h1 : ∀ w : ℂ, Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*deriv (expSum K c) k) atTop (𝓝 0))
    (h2 : ∀ w : ℂ, Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*deriv (deriv (expSum K c)) k) atTop (𝓝 0)) :
    ∀ i, c i=0 := by
  have project (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
      (hcover : ∀ a : Fin 3, a=i ∨ a=j ∨ a=l) : c i=0 := by
    have hlim := ((h2 (-K i)).sub ((h1 (-K i)).const_mul (K j+K l))).add
      ((h0 (-K i)).const_mul (K j*K l))
    have he (k : ℝ) : Complex.exp (-K i*(k:ℂ))*deriv (deriv (expSum K c)) k-
        (K j+K l)*(Complex.exp (-K i*(k:ℂ))*deriv (expSum K c) k)+
        K j*K l*(Complex.exp (-K i*(k:ℂ))*expSum K c k)=c i*(K i-K j)*(K i-K l) := by
      rw [expSum_second,expSum_deriv]
      have hs : expSum K (fun a => c a*K a^(2 : ℕ)) k-(K j+K l)*expSum K (fun a => c a*K a) k+
          K j*K l*expSum K c k=c i*(K i-K j)*(K i-K l)*Complex.exp (K i*(k:ℂ)) := by
        unfold expSum
        rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
        rw [Finset.sum_eq_single i]
        · ring
        · intro a ha hai
          rcases hcover a with rfl | rfl | rfl
          · exact (hai rfl).elim
          all_goals ring
        · simp
      calc
        _ = Complex.exp (-K i*(k:ℂ))*(expSum K (fun a => c a*K a^(2 : ℕ)) k-
          (K j+K l)*expSum K (fun a => c a*K a) k+K j*K l*expSum K c k) := by ring
        _ = Complex.exp (-K i*(k:ℂ))*(c i*(K i-K j)*(K i-K l)*Complex.exp (K i*(k:ℂ))) := by rw [hs]
        _ = c i*(K i-K j)*(K i-K l) := by
          rw [mul_left_comm,← Complex.exp_add,show -K i*(k:ℂ)+K i*(k:ℂ)=0 by ring,Complex.exp_zero,mul_one]
    simp only [mul_zero,sub_zero,add_zero,he] at hlim
    have hz : c i*(K i-K j)*(K i-K l)=0 := tendsto_nhds_unique tendsto_const_nhds hlim
    have hz' := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (fun h => hil (hK h)))
    exact (mul_eq_zero.mp hz').resolve_right (sub_ne_zero.mpr (fun h => hij (hK h)))
  intro i
  fin_cases i
  · exact project 0 1 2 (by omega) (by omega) (by omega) (by intro a; fin_cases a <;> simp)
  · exact project 1 0 2 (by omega) (by omega) (by omega) (by intro a; fin_cases a <;> simp)
  · exact project 2 0 1 (by omega) (by omega) (by omega) (by intro a; fin_cases a <;> simp)

private theorem principalExponent_injective (q : XiZeroCopy) : Function.Injective (principalExponent q) := by
  have hi := xi_divisor_support_im_ne_zero q.1
  intro i j he
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals exfalso; apply hi
  all_goals have h := congrArg Complex.im he
  all_goals norm_num [principalExponent,Complex.mul_im,Complex.mul_re] at h ⊢
  all_goals linarith

/-- The actual principal source integrals equal the original canonical cusp
coefficients, including the restored onset contribution. -/
theorem literalCoefficient_eq_original (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (hp : 0 < (p:ℝ)) (hr : Real.exp (-(width:ℝ)) ≤ 1/4) (i : Fin 3) :
    literalCoefficient q branch amp p (Real.exp (-(width:ℝ))) i=
      D4BMOriginalCuspJets.coefficient q branch amp p (p+width) i := by
  let rho := Real.exp (-(width:ℝ))
  let c (j : Fin 3) := literalCoefficient q branch amp p rho j-
    D4BMOriginalCuspJets.coefficient q branch amp p (p+width) j
  let F : ℝ → ℂ := expSum (principalExponent q) c
  let R : ℝ → ℂ := fun k => D4BMOriginalCuspJets.remainder q branch amp p (p+width) ![0,k]
  let A : ℝ → ℂ := actionRemainder (center q) (physicalRate q branch) amp p rho 0
  have hid : F=fun k => R k-A k := by
    funext k
    have h := originalPotential_eq_action_plus_channels q branch amp p width hp hr 0 k
    dsimp [F,expSum,c,R,A,D4BMOriginalCuspJets.remainder,D4BMOriginalCuspJets.principal]
    simp only [Fin.sum_univ_three,sub_mul] at h ⊢
    dsimp [rho] at h ⊢
    linear_combination -h
  have hR : ContDiff ℝ ∞ R := (originalRemainder_smooth q branch amp p (p+width)).comp
    (show ContDiff ℝ ∞ (fun k : ℝ => (![0,k] : Point)) by
      apply contDiff_pi.mpr
      intro j
      fin_cases j <;> dsimp <;> fun_prop)
  have hF : ContDiff ℝ ∞ F := expSum_smooth _ _
  have hA : ContDiff ℝ ∞ A := by
    have he : A=fun k => R k-F k := by funext k; rw [hid]; dsimp; ring
    rw [he]
    exact hR.sub hF
  have hder : deriv F=fun k => deriv R k-deriv A k := by
    rw [hid]
    funext k
    exact (((hR.differentiable (by simp) k).hasDerivAt).sub
      ((hA.differentiable (by simp) k).hasDerivAt)).deriv
  have hsecond : deriv (deriv F)=fun k => deriv (deriv R) k-deriv (deriv A) k := by
    rw [hder]
    funext k
    exact ((((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) k).hasDerivAt).sub
      (((contDiff_infty_iff_deriv.mp hA).2.differentiable (by simp) k).hasDerivAt)).deriv
  have hlim (w : ℂ) := originalRemainder_weighted_jets q branch amp
    ⟨p,p.property⟩ ⟨(p+width:NNReal),(p+width).property⟩ 0 w
  have ha (j : Fin 5) (w : ℂ) := action_weighted_base_jet q branch amp p rho 0 hp.le
    (show -(1/4:ℝ) ≤ rho by dsimp [rho]; linarith [Real.exp_pos (-(width:ℝ))]) hr j w
  have h0 (w : ℂ) : Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*F k) atTop (𝓝 0) := by
    rw [hid]
    have hA0 : Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*A k) atTop (𝓝 0) := ha 0 w
    simpa only [R,NNReal.coe_add,mul_sub,sub_zero] using (hlim w).1.sub hA0
  have h1 (w : ℂ) : Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*deriv F k) atTop (𝓝 0) := by
    rw [hder]
    have hA1 : Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*deriv A k) atTop (𝓝 0) := ha 1 w
    simpa only [R,NNReal.coe_add,mul_sub,sub_zero] using (hlim w).2.1.sub hA1
  have h2 (w : ℂ) : Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*deriv (deriv F) k) atTop (𝓝 0) := by
    rw [hsecond]
    have hA2 : Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*deriv (deriv A) k) atTop (𝓝 0) := ha 3 w
    simpa only [R,NNReal.coe_add,mul_sub,sub_zero] using (hlim w).2.2.sub hA2
  exact sub_eq_zero.mp (three_modes_unique (principalExponent q) c (principalExponent_injective q) h0 h1 h2 i)

/-- Exact matching of the uniform literal remainder to the canonical remainder
of the original restored potential. -/
theorem actionRemainder_eq_original (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (hp : 0 < (p:ℝ)) (hr : Real.exp (-(width:ℝ)) ≤ 1/4) (x k : ℝ) :
    actionRemainder (center q) (physicalRate q branch) amp p (Real.exp (-(width:ℝ))) x k=
      D4BMOriginalCuspJets.remainder q branch amp p (p+width) ![x,k] := by
  have h := originalPotential_eq_action_plus_channels q branch amp p width hp hr x k
  simp_rw [literalCoefficient_eq_original q branch amp p width hp hr] at h
  dsimp [D4BMOriginalCuspJets.remainder,D4BMOriginalCuspJets.principal]
  linear_combination -h

/-- The original canonical remainder's actual value, horizontal derivatives and
first two log-height derivatives inherit the uniform horizon/cusp estimates. -/
theorem original_remainder_base_jet_horizon_estimate (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (j : Fin 5) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ (p width : NNReal) (x k : ℝ),
      0 < (p:ℝ) → Real.exp (-(width:ℝ)) ≤ 1/4 → 0 ≤ k →
      ‖baseOperator j (fun x k => D4BMOriginalCuspJets.remainder q branch amp p (p+width) ![x,k]) x k‖
        ≤ C*Real.exp (B*(p:ℝ)-(N:ℝ)*k) ∧
      ‖baseOperator j (fun x k => D4BMOriginalCuspJets.remainder q branch amp p (p+width) ![x,k]) x k-
        baseOperator j (actionRemainder (center q) (physicalRate q branch) amp p 0) x k‖
        ≤ C*Real.exp (B*(p:ℝ)-(N:ℝ)*k)*Real.exp (-(width:ℝ)) := by
  obtain ⟨C,B,hC,hB,h⟩ := original_action_base_jet_horizon_estimate (center q) (physicalRate q branch) amp j N
  refine ⟨C,B,hC,hB,?_⟩
  intro p width x k hp hr hk
  have he : (fun x k => D4BMOriginalCuspJets.remainder q branch amp p (p+width) ![x,k])=
      actionRemainder (center q) (physicalRate q branch) amp p (Real.exp (-(width:ℝ))) := by
    funext x k
    exact (actionRemainder_eq_original q branch amp p width hp hr x k).symm
  rw [he]
  simpa only [abs_of_pos (Real.exp_pos _)] using
    h p (Real.exp (-(width:ℝ))) x k hp.le (by linarith [Real.exp_pos (-(width:ℝ))]) hr hk

/-- Independent time, cusp and horizon comparison for the canonical remainder
of the original restored potential, using its actual base derivatives. -/
theorem original_remainder_base_jet_time_horizon_estimate (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (j : Fin 5) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ w : ℂ, B+1 ≤ w.re →
      ∀ (T x k : ℝ) (width : NNReal),
      0 ≤ T → Real.exp (-(width:ℝ)) ≤ 1/4 → 0 ≤ k →
      ‖∫ p in (0:ℝ)..T, Complex.exp (-w*(p:ℂ))*
        (baseOperator j (fun x k => D4BMOriginalCuspJets.remainder q branch amp p (p+(width:ℝ)) ![x,k]) x k-
          baseOperator j (actionRemainder (center q) (physicalRate q branch) amp p 0) x k)‖
        ≤ C*Real.exp (-(N:ℝ)*k)*Real.exp (-(width:ℝ)) := by
  obtain ⟨C,B,hC,hB,h⟩ := original_action_base_jet_time_horizon_estimate (center q) (physicalRate q branch) amp j N
  refine ⟨C,B,hC,hB,?_⟩
  intro w hw T x k width hT hr hk
  have he (p : ℝ) (hp : 0 < p) :
      (fun x k => D4BMOriginalCuspJets.remainder q branch amp p (p+(width:ℝ)) ![x,k])=
        actionRemainder (center q) (physicalRate q branch) amp p (Real.exp (-(width:ℝ))) := by
    funext x k
    exact (actionRemainder_eq_original q branch amp ⟨p,hp.le⟩ width hp hr x k).symm
  have hi : (∫ p in (0:ℝ)..T, Complex.exp (-w*(p:ℂ))*
      (baseOperator j (fun x k => D4BMOriginalCuspJets.remainder q branch amp p (p+(width:ℝ)) ![x,k]) x k-
        baseOperator j (actionRemainder (center q) (physicalRate q branch) amp p 0) x k))=
      ∫ p in (0:ℝ)..T, Complex.exp (-w*(p:ℂ))*
        (baseOperator j (actionRemainder (center q) (physicalRate q branch) amp p (Real.exp (-(width:ℝ)))) x k-
          baseOperator j (actionRemainder (center q) (physicalRate q branch) amp p 0) x k) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hT
    intro p hp
    dsimp only
    rw [he p hp.1]
  rw [hi]
  simpa only [abs_of_pos (Real.exp_pos _)] using
    h w hw T (Real.exp (-(width:ℝ))) x k hT (by linarith [Real.exp_pos (-(width:ℝ))]) hr hk

end
end RHTower.D4BMOriginalPrincipalMatching
