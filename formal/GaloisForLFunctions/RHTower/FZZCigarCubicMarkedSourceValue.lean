import GaloisForLFunctions.RHTower.FZZCigarCubicMarkedFinitePartExtraction
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Exact original cubic marked source value

The mixed derivative of the actual pole-cleared source retains both local marked
remainders, the original exterior, and every derivative of its clearing factors
and restored subtraction terms. Their complete logarithmic correction cancels,
giving `H_aab = 128*MarkedFP - 96*FP + 10368*pi`.

The proved source jet and original unmarked value then determine the original
marked finite part as `-141*pi/8`, its independent two-cutoff limit at that value,
and its normalized position-log ratio `47/224`. No source integral is defined
by a special-function value. The local analytic and integrability obligations
are discharged through the original admitted source families.

These are fixed-dimensional position-source results. Fractional screening-count
continuation, complete physical normalization, the independent phase frame and
the integrated mixed replica--momentum Ward producer remain separate obligations.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private theorem second_mul (f g : ℝ → ℝ) (a : ℝ)
    (hf : AnalyticAt ℝ f a) (hg : AnalyticAt ℝ g a) :
    deriv (deriv (fun x => f x*g x)) a =
      deriv (deriv f) a*g a+2*deriv f a*deriv g a+f a*deriv (deriv g) a := by
  have h := iteratedDeriv_fun_mul (n := 2) hf.contDiffAt hg.contDiffAt
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,iteratedDeriv_succ,
    iteratedDeriv_zero,Nat.choose_zero_right,Nat.choose_self,Nat.choose_one_right,
    Nat.cast_ofNat,Nat.cast_one,zero_add,one_mul] at h
  simp only [Nat.reduceSub,iteratedDeriv_zero] at h
  rw [h]
  ring

private theorem second_add (f g : ℝ → ℝ) (a : ℝ)
    (hf : AnalyticAt ℝ f a) (hg : AnalyticAt ℝ g a) :
    deriv (deriv (fun x => f x+g x)) a = deriv (deriv f) a+deriv (deriv g) a := by
  have h := iteratedDeriv_fun_add (n := 2) hf.contDiffAt hg.contDiffAt
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using h

private theorem binomial_succ (β : ℝ) (n : ℕ) :
    fzzScreeningFifthBinomial β (n+1) =
      fzzScreeningFifthBinomial β n * (β/2-n)/(n+1) := by
  unfold fzzScreeningFifthBinomial
  rw [descPochhammer_succ_right]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_natCast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private def exteriorWeight (α β : ℝ) : Measure ℂ :=
  (volume.restrict fzzScreeningPlaneExterior).withDensity
    (fun z => ENNReal.ofReal (fzzScreeningPlaneKernel α β z))

private theorem kernel_nonnegative (α β : ℝ) (z : ℂ) :
    0 ≤ fzzScreeningPlaneKernel α β z :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)

private theorem exterior_admission (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fzzScreeningPlaneKernel α β) fzzScreeningPlaneExterior := by
  have h := fzzScreeningPlaneExterior_integrable α (Real.log (-2-α-β))
  rw [Real.exp_log (by linarith : 0 < -2-α-β)] at h
  simpa only [show -2-α-(-2-α-β)=β by ring] using h

private theorem plane_kernel_shift (α β δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖) =
      fzzScreeningPlaneKernel (α+δ) β z := by
  have hn := norm_pos_iff.mpr hz
  rw [show Real.exp (δ*Real.log ‖z‖)=‖z‖^δ by rw [Real.rpow_def_of_pos hn,mul_comm]]
  unfold fzzScreeningPlaneKernel
  rw [Real.rpow_add hn]
  ring

private theorem exterior_mgf (α β δ : ℝ) :
    ProbabilityTheory.mgf (fun z : ℂ => Real.log ‖z‖) (exteriorWeight α β) δ =
      ∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel (α+δ) β z := by
  rw [ProbabilityTheory.mgf,exteriorWeight,integral_withDensity_eq_integral_toReal_smul
    (by unfold fzzScreeningPlaneKernel; fun_prop)
    (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (kernel_nonnegative α β _),smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℂ))] with z hz
  exact plane_kernel_shift α β δ hz

private theorem exterior_analytic (α β : ℝ) (hs : α+β < -2) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel s β z) α := by
  have hmem : (0:ℝ) ∈ interior (ProbabilityTheory.integrableExpSet
      (fun z : ℂ => Real.log ‖z‖) (exteriorWeight α β)) := by
    apply mem_interior_iff_mem_nhds.mpr
    have hn : ∀ᶠ δ : ℝ in 𝓝 0,(α+δ)+β < -2 :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hs)
    filter_upwards [hn] with δ hδ
    change Integrable (fun z : ℂ => Real.exp (δ*Real.log ‖z‖)) (exteriorWeight α β)
    rw [exteriorWeight,integrable_withDensity_iff_integrable_smul'
      (by unfold fzzScreeningPlaneKernel; fun_prop)
      (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (kernel_nonnegative α β _),smul_eq_mul]
    apply (exterior_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℂ))] with z hz
    exact (plane_kernel_shift α β δ hz).symm
  have h := (ProbabilityTheory.analyticAt_mgf hmem).comp_sub α
  simpa only [zero_add,exterior_mgf,show ∀ s : ℝ,α+(s-α)=s by intro s; ring] using h

private theorem exterior_reflection (α β : ℝ) :
    (∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel α β z) =
      ∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel β α z := by
  have hp : (fun z : ℂ => 1-z) ⁻¹' fzzScreeningPlaneExterior = fzzScreeningPlaneExterior := by
    ext z
    simp only [fzzScreeningPlaneExterior,mem_preimage,mem_compl_iff,mem_union,
      mem_ball,dist_eq_norm,sub_zero,sub_sub_cancel_left,norm_neg,norm_sub_rev (1:ℂ) z,or_comm]
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1:ℂ)).measurableEmbedding (fzzScreeningPlaneKernel α β)
      fzzScreeningPlaneExterior
  rw [hp] at h
  simpa only [fzzScreeningPlaneKernel_reflection] using h.symm

private theorem fifth_singular_analytic (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted s β z) α := by
  have h := fzzScreeningFifthSubtracted_singular_analytic (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  rw [show -8+(α+8)=α by ring] at h
  have ht := h.comp_sub α
  simpa only [zero_add,show ∀ s : ℝ,α+(s-α)=s by intro s; ring] using ht

private theorem fifth_regular_analytic (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted α s z) β := by
  have h := fzzScreeningFifthSubtracted_regular_analytic (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  simpa only [show -8+(α+8)=α by ring] using h

private def originalRegularPart (α β : ℝ) : ℝ :=
  (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted α β z)+
  (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted β α z)+
  (∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel α β z)

private theorem regularPart_symm (α β : ℝ) : originalRegularPart α β = originalRegularPart β α := by
  unfold originalRegularPart
  rw [exterior_reflection α β]
  ring
private theorem regularPart_analytic (α β : ℝ) (ha : -8 < α) (hb : -8 < β) (hs : α+β < -2) :
    AnalyticAt ℝ (fun s => originalRegularPart s β) α :=
  ((fifth_singular_analytic α β ha).add (fifth_regular_analytic β α hb)).add
    (exterior_analytic α β hs)
private theorem regularPart_analytic_right (α β : ℝ) (ha : -8 < α) (hb : -8 < β) (hs : α+β < -2) :
    AnalyticAt ℝ (originalRegularPart α) β := by
  apply (regularPart_analytic β α hb ha (by linarith)).congr
  filter_upwards with s
  exact regularPart_symm s α

private theorem factor_deriv : HasDerivAt fzzScreeningHigherPoleFactor 8 (-6) := by
  have h := (((hasDerivAt_id (-6:ℝ)).add_const 2).mul
    ((hasDerivAt_id (-6:ℝ)).add_const 4)).mul ((hasDerivAt_id (-6:ℝ)).add_const 6)
  exact h.congr_deriv (by norm_num)
private theorem factor_zero : fzzScreeningHigherPoleFactor (-6) = 0 := by
  norm_num [fzzScreeningHigherPoleFactor]
private theorem half_power_deriv (α c : ℝ) :
    HasDerivAt (fun s : ℝ => (1/2:ℝ)^(s+c))
      (Real.log (1/2)*(1/2:ℝ)^(α+c)) α := by
  simpa only [mul_one,id_eq] using HasDerivAt.const_rpow (by norm_num : (0:ℝ)<1/2)
    ((hasDerivAt_id α).add_const c)

private def radialSlope : ℕ → ℝ
  | 0 => -32
  | 1 => -16
  | 2 => -6+8*Real.log (1/2)
  | n+3 => 8*(1/2:ℝ)^(2*((n+3:ℕ):ℝ)-4)/(2*((n+3:ℕ):ℝ)-4)

private theorem radial_deriv (k : ℕ) :
    HasDerivAt (fun α => fzzScreeningHigherClearedRadial α k) (radialSlope k) (-6) := by
  rcases k with _ | (_ | (_ | n))
  · have h := ((((hasDerivAt_id (-6:ℝ)).add_const 4).mul
      ((hasDerivAt_id (-6:ℝ)).add_const 6)).mul (half_power_deriv (-6) 2))
    exact h.congr_deriv (by norm_num [radialSlope,Real.rpow_neg])
  · have h := ((((hasDerivAt_id (-6:ℝ)).add_const 2).mul
      ((hasDerivAt_id (-6:ℝ)).add_const 6)).mul (half_power_deriv (-6) 4))
    exact h.congr_deriv (by norm_num [radialSlope,Real.rpow_neg])
  · have h := ((((hasDerivAt_id (-6:ℝ)).add_const 2).mul
      ((hasDerivAt_id (-6:ℝ)).add_const 4)).mul (half_power_deriv (-6) 6))
    exact h.congr_deriv (by norm_num [radialSlope])
  · have hn : -6+2*((n+3:ℕ):ℝ)+2 ≠ 0 := by
      push_cast
      linarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]
    have h := (factor_deriv.fun_mul (half_power_deriv (-6) (2*((n+3:ℕ):ℝ)+2))).fun_div
      ((hasDerivAt_id (-6:ℝ)).add_const (2*((n+3:ℕ):ℝ)+2))
      (by simpa only [add_assoc,id_eq] using hn)
    have he (α : ℝ) : α+(2*((n+3:ℕ):ℝ)+2)=α+2*((n+3:ℕ):ℝ)+2 := by ring
    simp only [he,id_eq,factor_zero,zero_mul,sub_zero,mul_one,add_zero] at h
    change HasDerivAt (fun α : ℝ => fzzScreeningHigherPoleFactor α *
      (1/2:ℝ)^(α+2*((n+3:ℕ):ℝ)+2)/(α+2*((n+3:ℕ):ℝ)+2))
      (8*(1/2:ℝ)^(2*((n+3:ℕ):ℝ)-4)/(2*((n+3:ℕ):ℝ)-4)) (-6)
    exact h.congr_deriv (by
      rw [show -6+2*((n+3:ℕ):ℝ)+2=2*((n+3:ℕ):ℝ)-4 by ring]
      field_simp [show 2*((n+3:ℕ):ℝ)-4 ≠ 0 by
        push_cast
        linarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]])

private def countertermSlope (β : ℝ) : ℝ :=
  2*Real.pi*∑ k ∈ Finset.range 6,fzzScreeningFifthAngularCoefficient β k*radialSlope k

private theorem counterterm_deriv (β : ℝ) :
    HasDerivAt (fun α => fzzScreeningHigherClearedCounterterm α β) (countertermSlope β) (-6) := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro k hk
  exact (radial_deriv k).const_mul (fzzScreeningFifthAngularCoefficient β k)

private theorem countertermSlope_analytic (β : ℝ) : AnalyticAt ℝ countertermSlope β := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (fzzScreeningFifthAngularCoefficient_analytic β k).mul analyticAt_const

private theorem counterterm_analytic_right (α β : ℝ) :
    AnalyticAt ℝ (fun s => fzzScreeningHigherClearedCounterterm α s) β := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (fzzScreeningFifthAngularCoefficient_analytic β k).mul analyticAt_const

private theorem countertermSlope_cubic :
    countertermSlope (-6) = -14449*Real.pi/8+576*Real.pi*Real.log (1/2) := by
  simp only [countertermSlope,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    fzzScreeningFifthAngularCoefficient,radialSlope]
  simp only [binomial_succ (-6) 4,binomial_succ (-6) 3,binomial_succ (-6) 2,
    binomial_succ (-6) 1,binomial_succ (-6) 0]
  norm_num [fzzScreeningFifthBinomial]
  ring

private theorem source_right_deriv (α : ℝ) (ha : α ∈ Ioo (-7) (-5)) :
    deriv (fun β => fzzScreeningHigherClearedSource α β) (-6) =
      8*fzzScreeningHigherPoleFactor α*originalRegularPart α (-6)+
      8*fzzScreeningHigherClearedCounterterm α (-6)+fzzScreeningHigherPoleFactor α*countertermSlope α := by
  have hr := (regularPart_analytic_right α (-6) (by linarith [ha.1]) (by norm_num)
    (by linarith [ha.2])).differentiableAt.hasDerivAt
  have h := (((factor_deriv.const_mul (fzzScreeningHigherPoleFactor α)).fun_mul hr).fun_add
    (factor_deriv.fun_mul (counterterm_analytic_right α (-6)).differentiableAt.hasDerivAt)).fun_add
    ((counterterm_deriv α).const_mul (fzzScreeningHigherPoleFactor α))
  change deriv (fun β =>
    fzzScreeningHigherPoleFactor α*fzzScreeningHigherPoleFactor β*originalRegularPart α β+
    fzzScreeningHigherPoleFactor β*fzzScreeningHigherClearedCounterterm α β+
    fzzScreeningHigherPoleFactor α*fzzScreeningHigherClearedCounterterm β α) (-6) = _
  rw [h.deriv]
  simp only [factor_zero,mul_zero,zero_mul,add_zero]
  ring

private theorem higher_factor_analytic (α : ℝ) :
    AnalyticAt ℝ fzzScreeningHigherPoleFactor α := by
  unfold fzzScreeningHigherPoleFactor
  fun_prop

private theorem half_power_analytic (α c : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => (1/2 : ℝ)^(s+c)) α := by
  have h : AnalyticAt ℝ (fun s : ℝ => Real.exp (Real.log (1/2)*(s+c))) α := by fun_prop
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1/2)] using h

private theorem higher_radial_analytic (α : ℝ) (ha : -8 < α) (k : ℕ) :
    AnalyticAt ℝ (fun s => fzzScreeningHigherClearedRadial s k) α := by
  rcases k with _ | (_ | (_ | n))
  · exact (show AnalyticAt ℝ (fun s : ℝ => (s+4)*(s+6)) α by fun_prop).mul
      (half_power_analytic α 2)
  · exact (show AnalyticAt ℝ (fun s : ℝ => (s+2)*(s+6)) α by fun_prop).mul
      (half_power_analytic α 4)
  · exact (show AnalyticAt ℝ (fun s : ℝ => (s+2)*(s+4)) α by fun_prop).mul
      (half_power_analytic α 6)
  · have hp : AnalyticAt ℝ (fun s : ℝ => (1/2 : ℝ)^(s+2*((n+3:ℕ):ℝ)+2)) α := by
      convert half_power_analytic α (2*((n+3:ℕ):ℝ)+2) using 1; simp only [add_assoc]
    have hd : α+2*((n+3:ℕ):ℝ)+2 ≠ 0 := by
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith
    exact ((higher_factor_analytic α).mul hp).div (by fun_prop) hd

private theorem higher_counterterm_analytic_left (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun s => fzzScreeningHigherClearedCounterterm s β) α := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact analyticAt_const.mul (higher_radial_analytic α ha k)


private theorem factor_deriv_all (α : ℝ) :
    HasDerivAt fzzScreeningHigherPoleFactor (3*α^(2 : ℕ)+24*α+44) α := by
  have h := ((((hasDerivAt_id' α).add_const 2).fun_mul
    ((hasDerivAt_id' α).add_const 4)).fun_mul ((hasDerivAt_id' α).add_const 6))
  exact h.congr_deriv (by ring)

private theorem factor_second : deriv (deriv fzzScreeningHigherPoleFactor) (-6) = -12 := by
  have he : deriv fzzScreeningHigherPoleFactor = fun α : ℝ => 3*α^(2 : ℕ)+24*α+44 :=
    funext (fun α => (factor_deriv_all α).deriv)
  rw [he]
  have h := (((((hasDerivAt_id' (-6:ℝ)).fun_pow 2).const_mul 3).fun_add
    ((hasDerivAt_id' (-6:ℝ)).const_mul 24)).add_const 44)
  rw [h.deriv]
  norm_num

private theorem half_power_second (α c : ℝ) :
    deriv (deriv (fun s : ℝ => (1/2:ℝ)^(s+c))) α =
      (Real.log (1/2))^(2 : ℕ)*(1/2:ℝ)^(α+c) := by
  have he : deriv (fun s : ℝ => (1/2:ℝ)^(s+c)) =
      fun s : ℝ => Real.log (1/2)*(1/2:ℝ)^(s+c) :=
    funext (fun s => (half_power_deriv s c).deriv)
  rw [he,((half_power_deriv α c).const_mul (Real.log (1/2))).deriv]
  ring

private theorem quad_deriv (α c d : ℝ) :
    HasDerivAt (fun s : ℝ => (s+c)*(s+d)) (2*α+c+d) α := by
  exact (((hasDerivAt_id' α).add_const c).fun_mul ((hasDerivAt_id' α).add_const d)).congr_deriv (by ring)

private theorem quad_second (α c d : ℝ) :
    deriv (deriv (fun s : ℝ => (s+c)*(s+d))) α = 2 := by
  have he : deriv (fun s : ℝ => (s+c)*(s+d)) = fun s : ℝ => 2*s+c+d :=
    funext (fun s => (quad_deriv s c d).deriv)
  rw [he]
  simpa only [mul_one] using
    (((hasDerivAt_id' α).const_mul 2).add_const c |>.add_const d).deriv

private theorem quad_power_second (c d e : ℝ) :
    deriv (deriv (fun α : ℝ => (α+c)*(α+d)*(1/2:ℝ)^(α+e))) (-6) =
      (2+2*Real.log (1/2)*(-12+c+d)+(Real.log (1/2))^(2 : ℕ)*((-6+c)*(-6+d)))*
        (1/2:ℝ)^(-6+e) := by
  rw [second_mul (fun α : ℝ => (α+c)*(α+d)) (fun α : ℝ => (1/2:ℝ)^(α+e)) (-6)
    (by fun_prop) (half_power_analytic (-6) e),quad_second,
    (quad_deriv (-6) c d).deriv,half_power_second,(half_power_deriv (-6) e).deriv]
  ring

private def tailQuot (d α : ℝ) : ℝ := (1/2:ℝ)^(α+(6+d))/(α+(6+d))

private theorem tailQuot_analytic (d : ℝ) (hd : 0 < d) : AnalyticAt ℝ (tailQuot d) (-6) := by
  exact (half_power_analytic (-6) (6+d)).div (by fun_prop) (by linarith)

private theorem tailQuot_value (d : ℝ) : tailQuot d (-6) = (1/2:ℝ)^d/d := by
  unfold tailQuot
  rw [show (-6:ℝ)+(6+d)=d by ring]

private theorem tailQuot_deriv (d : ℝ) (hd : 0 < d) :
    HasDerivAt (tailQuot d) ((1/2:ℝ)^d*(Real.log (1/2)/d-1/d^(2 : ℕ))) (-6) := by
  have h := (half_power_deriv (-6) (6+d)).fun_div
    ((hasDerivAt_id' (-6:ℝ)).add_const (6+d)) (by linarith)
  exact h.congr_deriv (by
    simp only [show (-6:ℝ)+(6+d)=d by ring]
    field_simp [hd.ne'])

private theorem tail_radial_second (d : ℝ) (hd : 0 < d) :
    deriv (deriv (fun α => fzzScreeningHigherPoleFactor α*tailQuot d α)) (-6) =
      (1/2:ℝ)^d*(-12/d-16/d^(2 : ℕ)+16*Real.log (1/2)/d) := by
  rw [second_mul _ _ (-6) (higher_factor_analytic (-6)) (tailQuot_analytic d hd),
    factor_second,factor_deriv.deriv,factor_zero,zero_mul,add_zero,
    (tailQuot_deriv d hd).deriv,tailQuot_value]
  ring

private def radialSecond : ℕ → ℝ
  | 0 => 32-64*Real.log (1/2)
  | 1 => 8-32*Real.log (1/2)
  | 2 => 2-12*Real.log (1/2)+8*(Real.log (1/2))^(2 : ℕ)
  | n+3 =>
    let d : ℝ := 2*((n+3:ℕ):ℝ)-4
    (1/2:ℝ)^d*(-12/d-16/d^(2 : ℕ)+16*Real.log (1/2)/d)

private theorem radial_second (k : ℕ) :
    deriv (deriv (fun α => fzzScreeningHigherClearedRadial α k)) (-6) = radialSecond k := by
  rcases k with _ | (_ | (_ | n))
  · change deriv (deriv (fun α : ℝ => (α+4)*(α+6)*(1/2:ℝ)^(α+2))) (-6) = _
    rw [quad_power_second]
    norm_num [radialSecond,Real.rpow_neg]
    ring
  · change deriv (deriv (fun α : ℝ => (α+2)*(α+6)*(1/2:ℝ)^(α+4))) (-6) = _
    rw [quad_power_second]
    norm_num [radialSecond,Real.rpow_neg]
    ring
  · change deriv (deriv (fun α : ℝ => (α+2)*(α+4)*(1/2:ℝ)^(α+6))) (-6) = _
    rw [quad_power_second]
    norm_num [radialSecond]
    ring
  · let d : ℝ := 2*((n+3:ℕ):ℝ)-4
    have hd : 0 < d := by dsimp [d]; push_cast; linarith [show (0:ℝ)≤n from Nat.cast_nonneg n]
    have he : (fun α => fzzScreeningHigherClearedRadial α (n+3)) =
        fun α => fzzScreeningHigherPoleFactor α*tailQuot d α := by
      funext α
      unfold fzzScreeningHigherClearedRadial tailQuot
      rw [show α+(6+d)=α+2*((n+3:ℕ):ℝ)+2 by dsimp [d]; ring]
      ring
    rw [he,tail_radial_second d hd]
    rfl

private theorem counterterm_second :
    deriv (deriv (fun α => fzzScreeningHigherClearedCounterterm α (-6))) (-6) =
      Real.pi*(137093/48-(14449/4)*Real.log (1/2)+576*(Real.log (1/2))^(2 : ℕ)) := by
  have hsum := iteratedDeriv_fun_sum (n := 2) (x := (-6:ℝ)) (I := Finset.range 6)
    (f := fun k α => fzzScreeningFifthAngularCoefficient (-6) k*fzzScreeningHigherClearedRadial α k)
    (fun k _ => (analyticAt_const.mul (higher_radial_analytic (-6) (by norm_num) k)).contDiffAt)
  have he : iteratedDeriv 2 (fun α => fzzScreeningHigherClearedCounterterm α (-6)) (-6) =
      2*Real.pi*∑ k ∈ Finset.range 6, fzzScreeningFifthAngularCoefficient (-6) k*
        iteratedDeriv 2 (fun α => fzzScreeningHigherClearedRadial α k) (-6) := by
    unfold fzzScreeningHigherClearedCounterterm
    have ha : AnalyticAt ℝ (fun α : ℝ => ∑ k ∈ Finset.range 6,
        fzzScreeningFifthAngularCoefficient (-6) k*fzzScreeningHigherClearedRadial α k) (-6) := by
      apply Finset.analyticAt_fun_sum
      intro k hk
      exact analyticAt_const.mul (higher_radial_analytic (-6) (by norm_num) k)
    rw [iteratedDeriv_const_mul (2*Real.pi) ha.contDiffAt,hsum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact iteratedDeriv_const_mul (fzzScreeningFifthAngularCoefficient (-6) k)
      (higher_radial_analytic (-6) (by norm_num) k).contDiffAt
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at he
  rw [he]
  simp_rw [radial_second]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    fzzScreeningFifthAngularCoefficient,radialSecond]
  simp only [binomial_succ (-6) 4,binomial_succ (-6) 3,binomial_succ (-6) 2,
    binomial_succ (-6) 1,binomial_succ (-6) 0]
  norm_num [fzzScreeningFifthBinomial]
  ring

private def binomialMark (β : ℝ) (n : ℕ) : ℝ :=
  (descPochhammer ℝ n).derivative.eval (β/2)/(2*(n.factorial:ℝ))

private theorem binomial_hasDerivAt (n : ℕ) (β : ℝ) :
    HasDerivAt (fun s => fzzScreeningFifthBinomial s n) (binomialMark β n) β := by
  have h : HasDerivAt (fun s : ℝ => (descPochhammer ℝ n).eval (s/2))
      ((descPochhammer ℝ n).derivative.eval (β/2)/2) β := by
    simpa only [Function.comp_def,mul_one_div,id_eq] using
      ((descPochhammer ℝ n).hasDerivAt (β/2)).comp β ((hasDerivAt_id β).div_const 2)
  exact (h.div_const (n.factorial:ℝ)).congr_deriv (by unfold binomialMark; ring)

private def coefficientMark (β : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => binomialMark β 1+2*binomialMark β 2
  | 2 => binomialMark β 2+6*binomialMark β 3+6*binomialMark β 4
  | 3 => binomialMark β 3+12*binomialMark β 4+30*binomialMark β 5
  | 4 => binomialMark β 4+20*binomialMark β 5
  | 5 => binomialMark β 5
  | _ => 0

private theorem coefficient_hasDerivAt (k : ℕ) (β : ℝ) :
    HasDerivAt (fun s => fzzScreeningFifthAngularCoefficient s k) (coefficientMark β k) β := by
  rcases k with _ | (_ | (_ | (_ | (_ | (_ | n)))))
  · exact hasDerivAt_const β 1
  · exact (binomial_hasDerivAt 1 β).fun_add ((binomial_hasDerivAt 2 β).const_mul 2)
  · exact ((binomial_hasDerivAt 2 β).fun_add ((binomial_hasDerivAt 3 β).const_mul 6)).fun_add ((binomial_hasDerivAt 4 β).const_mul 6)
  · exact ((binomial_hasDerivAt 3 β).fun_add ((binomial_hasDerivAt 4 β).const_mul 12)).fun_add ((binomial_hasDerivAt 5 β).const_mul 30)
  · exact (binomial_hasDerivAt 4 β).fun_add ((binomial_hasDerivAt 5 β).const_mul 20)
  · exact binomial_hasDerivAt 5 β
  · exact hasDerivAt_const β 0

private theorem countertermSlope_deriv :
    HasDerivAt countertermSlope (Real.pi*(892229/960-336*Real.log (1/2))) (-6) := by
  have h : HasDerivAt countertermSlope
      (2*Real.pi*∑ k ∈ Finset.range 6,coefficientMark (-6) k*radialSlope k) (-6) := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro k hk
    exact (coefficient_hasDerivAt k (-6)).mul_const (radialSlope k)
  apply h.congr_deriv
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,coefficientMark,radialSlope,
    binomialMark,descPochhammer_succ_right,descPochhammer_zero,Polynomial.derivative_mul,
    Polynomial.derivative_sub,Polynomial.derivative_X,Polynomial.derivative_natCast,
    Polynomial.derivative_one,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_one,Polynomial.eval_zero,Polynomial.eval_X,Polynomial.eval_natCast]
  norm_num
  ring

private theorem second_const_mul (c : ℝ) (f : ℝ → ℝ) (a : ℝ) (hf : AnalyticAt ℝ f a) :
    deriv (deriv (fun x => c*f x)) a = c*deriv (deriv f) a := by
  have h := iteratedDeriv_const_mul (n := 2) c hf.contDiffAt
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using h

private theorem originalRegularPart_value :
    originalRegularPart (-6) (-6) = fzzScreeningCubicPlaneFinitePart+
      10993*Real.pi/32-144*Real.pi*Real.log (1/2) := by
  rw [fzzScreeningCubicPlaneFinitePart_eq_fifthRemainders]
  unfold originalRegularPart
  ring

private theorem originalRegularPart_derivative :
    deriv (fun α => originalRegularPart α (-6)) (-6) = fzzScreeningCubicMarkedPlaneFinitePart-
      Real.pi*(36*(Real.log (1/2))^(2 : ℕ)-(13681/64)*Real.log (1/2)+962749/7680) := by
  change deriv (fun α =>
    (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted α (-6) z)+
    (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted (-6) α z)+
    (∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel α (-6) z)) (-6) = _
  rw [fzzScreeningCubicOriginalRemainders_hasDerivAt.deriv,
    fzzScreeningCubicMarkedPlaneFinitePart_eq_fifthMarks]
  ring

/-- Exact mixed-jet extraction retains both original marked local integrals,
the exterior, and every second derivative of the clearing and subtraction factors. -/
theorem fzzScreeningHigherClearedSource_cubic_third_extraction :
    deriv (deriv (fun a => deriv (fun b =>
      fzzScreeningHigherClearedSource (-6+a) (-6+b)) 0)) 0 =
      128*fzzScreeningCubicMarkedPlaneFinitePart-96*fzzScreeningCubicPlaneFinitePart+10368*Real.pi := by
  have second_eq (f : ℝ → ℝ) (x : ℝ) :
      deriv (deriv f) x = iteratedDeriv 2 f x := by
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [second_eq]
  simp_rw [deriv_comp_const_add,add_zero]
  rw [iteratedDeriv_comp_const_add 2
    (fun α => deriv (fun β => fzzScreeningHigherClearedSource α β) (-6)) (-6)]
  dsimp only
  rw [add_zero]
  have he : (fun α => deriv (fun β => fzzScreeningHigherClearedSource α β) (-6)) =ᶠ[𝓝 (-6)]
      fun α => 8*fzzScreeningHigherPoleFactor α*originalRegularPart α (-6)+
        8*fzzScreeningHigherClearedCounterterm α (-6)+fzzScreeningHigherPoleFactor α*countertermSlope α := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (-6:ℝ) ∈ Ioo (-7) (-5))] with α hα
    exact source_right_deriv α hα
  rw [he.iteratedDeriv_eq 2]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  change deriv (deriv (fun α =>
    8*fzzScreeningHigherPoleFactor α*originalRegularPart α (-6)+
    8*fzzScreeningHigherClearedCounterterm α (-6)+
    fzzScreeningHigherPoleFactor α*countertermSlope α)) (-6) = _
  have hA := higher_factor_analytic (-6)
  have hR := regularPart_analytic (-6) (-6) (by norm_num) (by norm_num) (by norm_num)
  have hC := higher_counterterm_analytic_left (-6) (-6) (by norm_num)
  have hS := countertermSlope_analytic (-6)
  have h8A : AnalyticAt ℝ (fun α => 8*fzzScreeningHigherPoleFactor α) (-6) := analyticAt_const.mul hA
  have h8C : AnalyticAt ℝ (fun α => 8*fzzScreeningHigherClearedCounterterm α (-6)) (-6) :=
    analyticAt_const.mul hC
  rw [second_add
      (fun α => 8*fzzScreeningHigherPoleFactor α*originalRegularPart α (-6)+
        8*fzzScreeningHigherClearedCounterterm α (-6))
      (fun α => fzzScreeningHigherPoleFactor α*countertermSlope α) (-6)
      ((h8A.mul hR).add h8C) (hA.mul hS),
    second_add
      (fun α => 8*fzzScreeningHigherPoleFactor α*originalRegularPart α (-6))
      (fun α => 8*fzzScreeningHigherClearedCounterterm α (-6)) (-6) (h8A.mul hR) h8C,
    second_mul _ _ (-6) h8A hR,second_mul _ _ (-6) hA hS,
    second_const_mul 8 _ (-6) hA,second_const_mul 8 _ (-6) hC,
    factor_second,(factor_deriv.const_mul 8).deriv,factor_deriv.deriv,
    counterterm_second,countertermSlope_deriv.deriv]
  simp only [factor_zero,mul_zero,zero_mul,add_zero]
  rw [countertermSlope_cubic,originalRegularPart_value,originalRegularPart_derivative]
  ring

/-- The original marked finite part is determined by its admitted mixed source jet. -/
theorem fzzScreeningCubicMarkedPlaneFinitePart_value :
    fzzScreeningCubicMarkedPlaneFinitePart = -141*Real.pi/8 := by
  have h := fzzScreeningHigherClearedSource_cubic_third_extraction
  rw [fzzScreeningHigherClearedSource_cubic_third_value,fzzScreeningCubicPlaneFinitePart_value] at h
  linarith

/-- The two original marked cutoffs converge independently with both distinct
collision primitives retained. -/
theorem fzzScreeningCubicMarkedPlane_independent_cutoff_value :
    Tendsto (fun P : ℝ × ℝ => fzzScreeningPlaneMarkedCutoff (-6) (-6) P.1 P.2+
      2*Real.pi*fzzScreeningCubicSingularMarkedCollisionPrimitive (Real.exp (-P.1))+
      2*Real.pi*fzzScreeningCubicMarkedCollisionPrimitive (Real.exp (-P.2))) (atTop ×ˢ atTop)
      (𝓝 (-141*Real.pi/8)) := by
  simpa only [fzzScreeningCubicMarkedPlaneFinitePart_value] using
    fzzScreeningCubicMarkedPlane_independent_cutoff_limit

/-- The normalized position-log insertion is formed from the original finite parts. -/
theorem fzzScreeningCubicMarkedPlaneFinitePart_ratio :
    fzzScreeningCubicMarkedPlaneFinitePart/fzzScreeningCubicPlaneFinitePart = 47/224 := by
  rw [fzzScreeningCubicMarkedPlaneFinitePart_value,fzzScreeningCubicPlaneFinitePart_value]
  field_simp [Real.pi_ne_zero]
  ring

end GaloisForLFunctions.RHTower
