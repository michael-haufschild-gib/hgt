import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalPrincipalReaderBounds

/-! Exact principal subtraction for the original angular source/reader products,
uniform time-integral estimates, and independent cusp/horizon restoration
after the singular metric factor. The forcing transfer and complete metric
counterterm/QNM identification remain separate obligations. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace RHTower.D4BMOriginalAngularReaderBounds
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMJointSource D4BMModularCore
open D4BMOriginalCuspFlux GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section
set_option autoImplicit false

private theorem exp_cpow (a : ℂ) (k : ℝ) :
    (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring

def angularJet (r : XiZeroCopy) (d : Bool) (x k : ℝ) : ℂ :=
  if d then coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x,Real.exp k]
    else D4BMLiteralCusp.scalar (physicalAngularParameter r) ![x,Real.exp k]

def angularPrincipal (r : XiZeroCopy) (d : Bool) (k : ℝ) : ℂ :=
  if d then readerCoefficient r*readerExponent r*Complex.exp ((readerExponent r-1)*(k:ℂ))
    else readerCoefficient r*Complex.exp (readerExponent r*(k:ℂ))

private theorem reader_decomposition (r : XiZeroCopy) (z : Fin 2 → ℝ) :
    D4BMLiteralCusp.scalar (physicalAngularParameter r) z=
      readerPrincipal r z+tail (physicalAngularParameter r) z := by
  have hp := physicalScalar_principal r z
  change D4BMGlobalAngularResponse.principal (physicalAngularParameter r) z=readerPrincipal r z at hp
  rw [← hp]
  rfl

/-- Exact value and normal decompositions of the unchanged physical angular reader. -/
theorem angularJet_decomposition (r : XiZeroCopy) (d : Bool) (x k : ℝ) :
    angularJet r d x k=angularPrincipal r d k+tailJet r d ![x,Real.exp k] := by
  cases d
  · change D4BMLiteralCusp.scalar (physicalAngularParameter r) ![x,Real.exp k]=
      readerCoefficient r*Complex.exp (readerExponent r*(k:ℂ))+tail (physicalAngularParameter r) ![x,Real.exp k]
    have h := reader_decomposition r ![x,Real.exp k]
    change D4BMLiteralCusp.scalar (physicalAngularParameter r) ![x,Real.exp k]=
      readerCoefficient r*(Real.exp k:ℂ)^(readerExponent r)+tail (physicalAngularParameter r) ![x,Real.exp k] at h
    rw [exp_cpow] at h
    exact h
  · let z : Fin 2 → ℝ := ![x,Real.exp k]
    have hz : 0 < z 1 := Real.exp_pos k
    have hn : {z : Fin 2 → ℝ | 0 < z 1} ∈ 𝓝 z :=
      (isOpen_lt continuous_const (continuous_apply (1:Fin 2))).mem_nhds hz
    have hS := (cuspLeg_contDiffOn .scalar (physicalAngularParameter r)).contDiffAt hn
    have hP : ContDiffAt ℝ ∞ (readerPrincipal r) z :=
      contDiffAt_const.mul ((height_cpow_contDiffOn (readerExponent r) ∞).contDiffAt hn)
    have he : tail (physicalAngularParameter r)=fun z => D4BMLiteralCusp.scalar (physicalAngularParameter r) z-readerPrincipal r z := by
      funext z
      rw [reader_decomposition]
      ring
    have hT : ContDiffAt ℝ ∞ (tail (physicalAngularParameter r)) z := by rw [he]; exact hS.sub hP
    have hD : coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z=
        coordDeriv 1 (readerPrincipal r) z+coordDeriv 1 (tail (physicalAngularParameter r)) z := by
      rw [funext (reader_decomposition r)]
      exact coordDeriv_add (hP.differentiableAt (by simp)) (hT.differentiableAt (by simp)) 1
    have hp : coordDeriv 1 (readerPrincipal r) z=
        readerCoefficient r*readerExponent r*(z 1:ℂ)^(readerExponent r-1) := by
      have hd := (height_cpow_hasFDerivAt (readerExponent r) z hz).const_mul (readerCoefficient r)
      change fderiv ℝ (fun z : Fin 2 → ℝ => readerCoefficient r*(z 1:ℂ)^(readerExponent r)) z (Pi.single 1 1)=_
      rw [hd.fderiv]
      simp [D4BMAngularSeries.gradient]
      ring
    rw [hp] at hD
    change coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x,Real.exp k]=
      readerCoefficient r*readerExponent r*(Real.exp k:ℂ)^(readerExponent r-1)+
        coordDeriv 1 (tail (physicalAngularParameter r)) ![x,Real.exp k] at hD
    rw [exp_cpow] at hD
    exact hD

/-- Both actual angular reader operations have a uniform exponential height bound. -/
theorem angularJet_bound (r : XiZeroCopy) (d : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x k : ℝ, 0 ≤ k → ‖angularJet r d x k‖ ≤ C*Real.exp k := by
  obtain ⟨B,hB,hb⟩ := principal_tail_bound r d 0 0
  have hr : (readerExponent r).re ≤ 1 := by
    have hq := (xi_divisor_support_re_mem_open_unit r.1).1
    norm_num [readerExponent]
    linarith
  let A := if d then ‖readerCoefficient r*readerExponent r‖ else ‖readerCoefficient r‖
  have hA : 0 ≤ A := by dsimp [A]; split <;> exact norm_nonneg _
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro x k hk
  have hp : ‖angularPrincipal r d k‖ ≤ A*Real.exp k := by
    cases d
    · change ‖readerCoefficient r*Complex.exp (readerExponent r*(k:ℂ))‖ ≤ ‖readerCoefficient r‖*Real.exp k
      rw [norm_mul,Complex.norm_exp]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_le_of_le_one_left hk hr
    · change ‖(readerCoefficient r*readerExponent r)*Complex.exp ((readerExponent r-1)*(k:ℂ))‖ ≤ ‖readerCoefficient r*readerExponent r‖*Real.exp k
      rw [norm_mul,Complex.norm_exp]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_le_of_le_one_left hk (by linarith : (readerExponent r).re-1 ≤ 1)
  have ht : ‖tailJet r d ![x,Real.exp k]‖ ≤ B := by simpa using hb x k hk
  rw [angularJet_decomposition]
  calc
    _ ≤ ‖angularPrincipal r d k‖+‖tailJet r d ![x,Real.exp k]‖ := norm_add_le _ _
    _ ≤ A*Real.exp k+B := add_le_add hp ht
    _ ≤ (A+B)*Real.exp k := by
      rw [add_mul]
      exact add_le_add_right (le_mul_of_one_le_right hB (Real.one_le_exp hk)) _

end
end RHTower.D4BMOriginalAngularReaderBounds

namespace RHTower.D4BMOriginalPrincipalHorizonBounds
open D4BMJointSource D4BMModularCore D4BMOriginalBaseCircleJets D4BMOriginalCausalPotential
noncomputable section
set_option autoImplicit false

def jetMultiplier (j : Fin 5) (a : ℂ) : ℂ := ![1,a,0,a^(2 : ℕ),0] j

private theorem principal_base_jet (j : Fin 5) (a c : ℂ) (x k : ℝ) :
    baseOperator j (fun _ k => c*Complex.exp (a*(k:ℂ))) x k=
      c*jetMultiplier j a*Complex.exp (a*(k:ℂ)) := by
  have hd (k : ℝ) : HasDerivAt (fun t : ℝ => c*Complex.exp (a*(t:ℂ)))
      (c*a*Complex.exp (a*(k:ℂ))) k := by
    apply (((hasDerivAt_id k).ofReal_comp.const_mul a).cexp.const_mul c).congr_deriv
    simp only [id_eq,Complex.ofReal_one,mul_one]
    ring
  have he : deriv (fun k : ℝ => c*Complex.exp (a*(k:ℂ)))=
      fun k : ℝ => (c*a)*Complex.exp (a*(k:ℂ)) := funext (fun k => (hd k).deriv)
  have hd2 (k : ℝ) : HasDerivAt (fun t : ℝ => (c*a)*Complex.exp (a*(t:ℂ)))
      (c*a^(2 : ℕ)*Complex.exp (a*(k:ℂ))) k := by
    apply (((hasDerivAt_id k).ofReal_comp.const_mul a).cexp.const_mul (c*a)).congr_deriv
    simp only [id_eq,Complex.ofReal_one,mul_one]
    ring
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 by omega) with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [baseOperator,jetMultiplier,Matrix.cons_val]
  · ring
  · exact (hd k).deriv
  · simp
  · rw [he]; exact (hd2 k).deriv
  · simp

/-- The principal part of each genuine angular base operation is exactly the
same three source coefficients, with the differentiated exponent multipliers. -/
theorem principal_jet_expansion (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (p L x k : ℝ) :
    baseOperator j (fun x k => D4BMOriginalCuspJets.principal q br amp p (p+L) ![x,k]) x k=
      ∑ i : Fin 3,coefficient q br amp i p L*jetMultiplier j (principalExponent q i)*Complex.exp (principalExponent q i*(k:ℂ)) := by
  let F (i : Fin 3) (_ k : ℝ) := coefficient q br amp i p L*Complex.exp (principalExponent q i*(k:ℂ))
  have hF (i : Fin 3) : ContDiff ℝ ∞ (fun z : ℝ × ℝ => F i z.1 z.2) :=
    contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).cexp)
  have h : (fun x k => D4BMOriginalCuspJets.principal q br amp p (p+L) ![x,k])=
      fun x k => 1*(1*F 0 x k+1*F 1 x k)+1*F 2 x k := by
    funext x k
    simp only [D4BMOriginalCuspJets.principal,Matrix.cons_val,Fin.sum_univ_three,F,coefficient,one_mul]
  rw [h,baseOperator_linear j _ _ 1 1 ((contDiff_const.mul (hF 0)).add (contDiff_const.mul (hF 1))) (hF 2),
    baseOperator_linear j _ _ 1 1 (hF 0) (hF 1)]
  simp only [one_mul,F,principal_base_jet,Fin.sum_univ_three]

/-- Actual source jets split into their canonical remainder and the unchanged
three differentiated principal terms. No asymptotic replacement is made. -/
theorem original_source_jet_expansion (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (p L x k : ℝ) :
    baseOperator j (originalPotential q br amp p (p+L)) x k=
      D4BMOriginalReaderCuspBounds.sourceJet q br amp j p L x k+
      ∑ i : Fin 3,coefficient q br amp i p L*jetMultiplier j (principalExponent q i)*Complex.exp (principalExponent q i*(k:ℂ)) := by
  have hF := originalPotential_angular_smooth q br amp p (p+L)
  have hP : ContDiff ℝ ∞ (fun z : ℝ × ℝ => D4BMOriginalCuspJets.principal q br amp p (p+L) ![z.1,z.2]) := by
    unfold D4BMOriginalCuspJets.principal
    apply ContDiff.sum
    intro i _
    simp only [Matrix.cons_val]
    exact contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).cexp)
  have h := baseOperator_linear j (originalPotential q br amp p (p+L))
    (fun x k => D4BMOriginalCuspJets.principal q br amp p (p+L) ![x,k]) 1 (-1) hF hP x k
  have hr : D4BMOriginalReaderCuspBounds.sourceJet q br amp j p L x k=
      baseOperator j (originalPotential q br amp p (p+L)) x k-
      baseOperator j (fun x k => D4BMOriginalCuspJets.principal q br amp p (p+L) ![x,k]) x k := by
    simpa only [D4BMOriginalReaderCuspBounds.sourceJet,D4BMOriginalCuspJets.remainder,Matrix.cons_val,one_mul,neg_one_mul,sub_eq_add_neg] using h
  rw [principal_jet_expansion] at hr
  rw [hr]
  ring

end
end RHTower.D4BMOriginalPrincipalHorizonBounds

namespace RHTower.D4BMOriginalAngularProducts
open D4BMJointSource D4BMModularCore D4BMOriginalBaseCircleJets D4BMOriginalCausalPotential
open D4BMOriginalPrincipalHorizonBounds D4BMOriginalAngularReaderBounds D4BMOriginalReaderCuspBounds
noncomputable section
set_option autoImplicit false

def principalJet (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (p L k : ℝ) : ℂ :=
  ∑ i : Fin 3,coefficient q br amp i p L*jetMultiplier j (principalExponent q i)*Complex.exp (principalExponent q i*(k:ℂ))

def horizonPrincipalJet (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (p k : ℝ) : ℂ :=
  ∑ i : Fin 3,horizonCoefficient q br amp i p*jetMultiplier j (principalExponent q i)*Complex.exp (principalExponent q i*(k:ℂ))

/-- Product of actual source and angular reader operations, with its exact
three original principal products subtracted before any cutoff limit. -/
def angularProduct (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 5) (d : Bool)
    (p L x k : ℝ) : ℂ :=
  reader q w L*(baseOperator j (originalPotential q br amp p (p+L)) x k*angularJet q d x k-
    principalJet q br amp j p L k*angularPrincipal q d k)

/-- The corresponding actual horizon coefficients and source trace. -/
def horizonAngularProduct (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 5) (d : Bool)
    (p x k : ℝ) : ℂ :=
  horizonReader q w*((horizonJet q br amp j p x k+horizonPrincipalJet q br amp j p k)*angularJet q d x k-
    horizonPrincipalJet q br amp j p k*angularPrincipal q d k)

private theorem product_difference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 5) (d : Bool)
    (p L x k : ℝ) :
    angularProduct q br amp w j d p L x k-horizonAngularProduct q br amp w j d p x k=
      (reader q w L*sourceJet q br amp j p L x k-horizonReader q w*horizonJet q br amp j p x k)*angularJet q d x k+
      ∑ i : Fin 3,(reader q w L*coefficient q br amp i p L-horizonReader q w*horizonCoefficient q br amp i p)*
        jetMultiplier j (principalExponent q i)*(Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k]) := by
  rw [angularProduct,original_source_jet_expansion,horizonAngularProduct]
  simp only [angularJet_decomposition,principalJet,horizonPrincipalJet,Fin.sum_univ_three]
  ring

/-- All five genuine source base operations, paired with both physical angular
reader operations, have a joint horizon/cusp error with an integrable time
majorant. The subtraction is performed on the full original product. -/
theorem original_angular_product_error (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5)
    (d : Bool) (N : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p x k : ℝ, 0 < p → 0 ≤ k →
      ‖Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w j d p L x k-
        horizonAngularProduct q br amp w j d p x k)‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := original_reader_source_jet_error q br amp j (N+1)
  obtain ⟨D,hD,hd⟩ := angularJet_bound q d
  refine ⟨G+2,by positivity,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := hg w hwi (by linarith)
  have ht (i : Fin 3) := principal_reader_tail_error q q br amp w (principalExponent q i) i d N hwi (by linarith : 3 ≤ w.re)
  choose B hB hb using ht
  let M : ℝ := C*D+∑ i : Fin 3,B i*‖jetMultiplier j (principalExponent q i)‖
  have hM : 0 ≤ M := by dsimp [M]; exact add_nonneg (mul_nonneg hC hD) (Finset.sum_nonneg (fun i _ => mul_nonneg (hB i) (norm_nonneg _)))
  refine ⟨M,hM,?_⟩
  filter_upwards [hc,hb 0,hb 1,hb 2] with L hcL h0 h1 h2 p x k hp hk
  let S := Real.exp (-L)+Real.exp (-w.re*L)
  let E := S*Real.exp (-(N:ℝ)*k)*Real.exp (-p)
  have he : 0 ≤ E := by dsimp [E,S]; positivity
  have htail (i : Fin 3) :
      ‖Complex.exp (-w*(p:ℂ))*(reader q w L*coefficient q br amp i p L-
        horizonReader q w*horizonCoefficient q br amp i p)*
        (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])‖ ≤ B i*E := by
    rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with rfl | rfl | rfl
    · simpa only [E,S,mul_assoc] using h0 p x k hp hk
    · simpa only [E,S,mul_assoc] using h1 p x k hp hk
    · simpa only [E,S,mul_assoc] using h2 p x k hp hk
  have hsource :
      ‖Complex.exp (-w*(p:ℂ))*(reader q w L*sourceJet q br amp j p L x k-
        horizonReader q w*horizonJet q br amp j p x k)*angularJet q d x k‖ ≤ (C*D)*E := by
    rw [norm_mul]
    calc
      _ ≤ (C*S*Real.exp (-((N+1:ℕ):ℝ)*k)*Real.exp (-p))*(D*Real.exp k) :=
        mul_le_mul (hcL p x k hp hk) (hd x k hk) (norm_nonneg _) (by dsimp [S]; positivity)
      _ = (C*D)*E := by
        rw [show C*S*Real.exp (-((N+1:ℕ):ℝ)*k)*Real.exp (-p)*(D*Real.exp k)=
          (C*D*S*Real.exp (-p))*(Real.exp (-((N+1:ℕ):ℝ)*k)*Real.exp k) by ring,← Real.exp_add]
        have hex : -((N+1:ℕ):ℝ)*k+k=-(N:ℝ)*k := by push_cast; ring
        rw [hex]
        dsimp [E]
        ring
  have hsum :
      ‖∑ i : Fin 3,Complex.exp (-w*(p:ℂ))*(reader q w L*coefficient q br amp i p L-
        horizonReader q w*horizonCoefficient q br amp i p)*jetMultiplier j (principalExponent q i)*
        (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])‖ ≤
        (∑ i : Fin 3,B i*‖jetMultiplier j (principalExponent q i)‖)*E := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [show Complex.exp (-w*(p:ℂ))*(reader q w L*coefficient q br amp i p L-
        horizonReader q w*horizonCoefficient q br amp i p)*jetMultiplier j (principalExponent q i)*
        (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])=
        (Complex.exp (-w*(p:ℂ))*(reader q w L*coefficient q br amp i p L-
        horizonReader q w*horizonCoefficient q br amp i p)*
        (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k]))*jetMultiplier j (principalExponent q i) by ring,norm_mul]
    exact (mul_le_mul_of_nonneg_right (htail i) (norm_nonneg _)).trans_eq (by ring)
  rw [product_difference,mul_add,Finset.mul_sum]
  simp only [mul_assoc] at hsource hsum ⊢
  apply (norm_add_le _ _).trans
  apply (add_le_add hsource hsum).trans_eq
  dsimp [M,E]
  ring

/-- The complete principal-subtracted products retain the same bound after the
actual source-time integral, uniformly over every upper time cutoff. -/
theorem original_angular_product_time_error (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (d : Bool) (N : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ T x k : ℝ, 0 ≤ T → 0 ≤ k →
      ‖∫ p in (0:ℝ)..T,Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w j d p L x k-
        horizonAngularProduct q br amp w j d p x k)‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,h⟩ := original_angular_product_error q br amp j d N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨B,hB,h⟩ := h w hwi hw
  refine ⟨B,hB,?_⟩
  filter_upwards [h] with L hL T x k hT hk
  let C := B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi : IntervalIntegrable (fun p : ℝ => C*Real.exp (-p)) MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall (fun p hp => hL p x k hp.1 hk)) hi
  calc
    _ ≤ ∫ p in (0:ℝ)..T,C*Real.exp (-p) := hb
    _ = C*(1-Real.exp (-T)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp,neg_zero,Real.exp_zero]
    _ ≤ _ := by change C*(1-Real.exp (-T)) ≤ C; nlinarith [Real.exp_nonneg (-T)]

end
end RHTower.D4BMOriginalAngularProducts

namespace RHTower.D4BMOriginalAngularProducts
open D4BMJointSource D4BMJointWave D4BMModularCore
noncomputable section
set_option autoImplicit false

private theorem geometric_collar_bound (L : ℝ) (hL : 0 < L) :
    Real.exp (-L) ≤ (tortoiseRadius (-L/2))^(2 : ℕ)-1 := by
  let R := tortoiseRadius (-L/2)
  have hR : 1 < R := tortoiseRadius_exterior (-L/2) (by linarith)
  have hR0 : R ≠ 0 := by linarith
  have h := radialUnit_one_sub (-L/2)
  rw [show 2*(-L/2)=-L by ring,radialUnit_inverse_radius] at h
  change 1-R⁻¹=Real.exp (-L)*(1+R⁻¹) at h
  have he : R-1=Real.exp (-L)*(R+1) := by
    have hh := congrArg (fun t : ℝ => t*R) h
    field_simp [hR0] at hh
    nlinarith
  calc
    _ ≤ Real.exp (-L)*(R+1)^(2 : ℕ) := le_mul_of_one_le_right (Real.exp_nonneg _) (by nlinarith)
    _ = (Real.exp (-L)*(R+1))*(R+1) := by ring
    _ = R^(2 : ℕ)-1 := by rw [← he]; ring

/-- The actual singular metric factor consumes one geometric horizon order.
After this loss, every cusp order remains uniform in both cutoff lengths. -/
theorem metric_angular_product_time_error (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (d : Bool) (N : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ T x k : ℝ, 0 ≤ T → 0 ≤ k →
      ‖(∫ p in (0:ℝ)..T,Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w j d p L x k-
        horizonAngularProduct q br amp w j d p x k))/((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)‖ ≤
        B*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,h⟩ := original_angular_product_time_error q br amp j d N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨B,hB,h⟩ := h w hwi hw
  refine ⟨2*B,by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with L hL hpos T x k hT hk
  let R := tortoiseRadius (-L/2)
  have hR : 1 < R := tortoiseRadius_exterior (-L/2) (by linarith)
  have hf : 0 < R^(2 : ℕ)-1 := by nlinarith
  have hgeo : Real.exp (-L) ≤ R^(2 : ℕ)-1 := geometric_collar_bound L hpos
  have hdec : Real.exp (-w.re*L) ≤ Real.exp (-L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hS : Real.exp (-L)+Real.exp (-w.re*L) ≤ 2*(R^(2 : ℕ)-1) := by linarith
  have hn : ‖(R:ℂ)^(2 : ℕ)-1‖=R^(2 : ℕ)-1 := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hf]
  change ‖_/( (R:ℂ)^(2 : ℕ)-1)‖ ≤ _
  rw [norm_div,hn]
  apply (div_le_iff₀ hf).mpr
  calc
    _ ≤ B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k) := hL T x k hT hk
    _ ≤ B*(2*(R^(2 : ℕ)-1))*Real.exp (-(N:ℝ)*k) := by gcongr
    _ = _ := by ring

/-- Independent horizon and cusp restoration of the metric-weighted difference
holds along every nonnegative time-cutoff net and every horizontal path. -/
theorem metric_angular_product_joint_limit (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (d : Bool) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∀ (T : ℝ × ℝ → Ici (0:ℝ)) (X : ℝ × ℝ → ℝ),
      Tendsto (fun z : ℝ × ℝ =>
        (∫ p in (0:ℝ)..(T z:ℝ),Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w j d p z.1 (X z) z.2-
          horizonAngularProduct q br amp w j d p (X z) z.2))/((tortoiseRadius (-z.1/2):ℂ)^(2 : ℕ)-1))
        ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨G,hG,h⟩ := metric_angular_product_time_error q br amp j d 1
  refine ⟨G,hG,?_⟩
  intro w hwi hw T X
  obtain ⟨B,hB,hb⟩ := h w hwi hw
  have he : Tendsto (fun z : ℝ × ℝ => B*Real.exp (-z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul B).comp tendsto_snd
  apply squeeze_zero_norm' _ he
  filter_upwards [hb.prod_mk (eventually_ge_atTop (0:ℝ))] with z hz
  simpa only [Nat.cast_one,neg_one_mul] using hz.1 (T z) (X z) z.2 (T z).property hz.2

end
end RHTower.D4BMOriginalAngularProducts
