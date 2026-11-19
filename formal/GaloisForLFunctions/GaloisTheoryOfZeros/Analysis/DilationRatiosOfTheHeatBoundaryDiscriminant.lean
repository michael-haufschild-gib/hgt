import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheBoundaryMomentsOfAHeatWindow
import GaloisForLFunctions.HTGeometry.AnalyticSlopeFactor

/-!
# Measuring a heat collision by two time offsets

A zero of order k has dilation ratio a^k, including along moving complex
directions and moving dilations. This is the local analytic analogue of
Ponge–Tian's moving-dilation lemma (arXiv:2605.25591, Lemma 2.17).
Pairing opposite offsets cancels the linear bias. In a regular spatial
window of the actual heat transform, a ratio of absolute values below
three halves arbitrarily close to the base time distinguishes order zero
from every collision.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
noncomputable section
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- At a finite-order zero even the phase of the dilation ratio is fixed
by the moving dilation, regardless of the incoming complex direction. -/
theorem analytic_dilation_at_finite_order {D : ℂ → ℂ} {k : ℕ}
    (hD : AnalyticAt ℂ D 0) (hk : analyticOrderAt D 0 = (k:ℕ∞))
    {ι : Type*} {l : Filter ι} {w a : ι → ℂ} {A : ℂ}
    (hw : Tendsto w l (𝓝 0)) (hn : ∀ᶠ i in l, w i ≠ 0) (ha : Tendsto a l (𝓝 A)) :
    Tendsto (fun i => D (a i*w i)/D (w i)) l (𝓝 (A^k)) := by
  obtain ⟨V,hV,hv,hfactor⟩ := hD.analyticOrderAt_eq_natCast.mp hk
  have hf : ∀ᶠ z in 𝓝 (0:ℂ), D z=z^k*V z := by
    simpa only [sub_zero,smul_eq_mul] using hfactor
  have haw := ha.mul hw
  rw [mul_zero] at haw
  have h := (ha.pow k).mul ((hV.continuousAt.tendsto.comp haw).div (hV.continuousAt.tendsto.comp hw) hv)
  rw [div_self hv,mul_one] at h
  apply h.congr'
  filter_upwards [hn,hw.eventually hf,haw.eventually hf,hw.eventually (hV.continuousAt.eventually_ne hv)]
    with i hwi h₁ h₂ hi
  change a i^k*(V (a i*w i)/V (w i)) = _
  rw [h₁,h₂,mul_pow]
  field_simp

/-- For opposite time offsets the product of the two raw ratios has an
analytic quadratic remainder. No symmetry assumption on the analytic unit
or on the spatial window is needed. -/
theorem symmetric_dilation_quadratic_remainder {D : ℂ → ℂ} {k : ℕ}
    (hD : AnalyticAt ℂ D 0) (hk : analyticOrderAt D 0 = (k:ℕ∞)) (a : ℂ) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ),
      (D (a*z)/D z)*(D (a*(-z))/D (-z)) = a^(2*k)+z^2*U z := by
  obtain ⟨V,hV,hv,hfactor⟩ := hD.analyticOrderAt_eq_natCast.mp hk
  have hf : ∀ᶠ z in 𝓝 (0:ℂ), D z=z^k*V z := by simpa only [sub_zero,smul_eq_mul] using hfactor
  let Q (z : ℂ) := a^k*(V (a*z)/V z)
  have hscale : AnalyticAt ℂ (fun z : ℂ => a*z) 0 := analyticAt_const.mul analyticAt_id
  have hVa : AnalyticAt ℂ V (a*0) := by simpa only [mul_zero] using hV
  have hQ : AnalyticAt ℂ Q 0 := analyticAt_const.mul ((hVa.comp hscale).div hV hv)
  have Q₀ : Q 0 = a^k := by simp only [Q,mul_zero,div_self hv,mul_one]
  let P (z : ℂ) := Q z*Q (-z)
  have hnQ : AnalyticAt ℂ Q (-0) := by simpa only [neg_zero] using hQ
  have hP : AnalyticAt ℂ P 0 := hQ.mul (hnQ.comp analyticAt_id.neg)
  have hd : deriv P 0 = 0 := by
    have hq := hQ.differentiableAt.hasDerivAt
    have hneg := hnQ.differentiableAt.hasDerivAt.comp (0:ℂ) (hasDerivAt_id (x:=(0:ℂ))).neg
    have hp := hq.mul hneg
    simpa only [P,Function.comp_def,id_eq,neg_zero,mul_neg,mul_one,neg_mul,
      mul_comm (deriv Q 0),add_neg_cancel,neg_add_cancel] using hp.deriv
  let U := HTGeometry.analyticSlope (HTGeometry.analyticSlope P 0) 0
  refine ⟨U,HTGeometry.analyticAt_analyticSlope_two hP,?_⟩
  have hlin : Tendsto (fun z : ℂ => a*z) (𝓝 0) (𝓝 0) := by simpa only [mul_zero] using hscale.continuousAt.tendsto
  have her : ∀ᶠ z in 𝓝[≠] (0:ℂ), D (a*z)/D z=Q z := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hf,
      mem_nhdsWithin_of_mem_nhds (hlin.eventually hf),
      mem_nhdsWithin_of_mem_nhds (hV.continuousAt.eventually_ne hv)] with z hz h₁ h₂ hzV
    have hz' : z ≠ 0 := hz
    rw [h₁,h₂,mul_pow]
    dsimp only [Q]
    field_simp
  have hneg : Tendsto (fun z : ℂ => -z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [neg_zero] using (continuous_neg.tendsto (0:ℂ)).mono_left nhdsWithin_le_nhds,
      self_mem_nhdsWithin.mono fun z hz => neg_ne_zero.mpr hz⟩
  filter_upwards [her,hneg.eventually her] with z hz hneg'
  rw [hz,hneg']
  have he := HTGeometry.eq_taylor_two_add_sq_mul P 0 z
  simpa only [P,neg_zero,Q₀,hd,sub_zero,mul_zero,add_zero,two_mul,pow_add,U] using he

/-- An isolating spatial window of each marked place measures the exact
intersection multiplicity by dilation, with quadratic bias after pairing. -/
theorem heat_boundary_dilation_reads_multiplicity (τ z : ℂ) :
    ∃ l u : ℂ, (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
      (∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0) ∧
      let D := fun w => heatBoundaryDiscriminant (τ+w) l u
      let k := heatIntersectionMultiplicity (τ,z)
      (∀ a : ℂ, Tendsto (fun w => D (a*w)/D w) (𝓝[≠] 0) (𝓝 (a^k))) ∧
        ∀ a : ℂ, ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ ∀ᶠ w in 𝓝[≠] (0:ℂ),
          (D (a*w)/D w)*(D (a*(-w))/D (-w)) = a^(2*k)+w^2*U w := by
  have hc := isCollision_iff_analyticOrderAt.mpr
    (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top τ z)).symm
  obtain ⟨l,u,hin,hb,hD,hk,_⟩ := hc.boundaryMoment_regular_winding
  refine ⟨l,u,hin,hb,fun a => ?_, fun a => ?_⟩
  · exact analytic_dilation_at_finite_order hD hk (tendsto_id.mono_left nhdsWithin_le_nhds)
      self_mem_nhdsWithin (tendsto_const_nhds (x:=a))
  · exact symmetric_dilation_quadratic_remainder hD hk a

/-- RH is equivalent to finding arbitrarily small offsets with modulus
doubling ratio below three halves on each regular spatial window at each
positive time. All readings come from the theta transform on its boundary. -/
theorem rh_iff_heat_boundary_doubling :
    RiemannHypothesis ↔ ∀ (t : ℝ), 0 < t → ∀ l u : ℂ, l.re ≤ u.re → l.im ≤ u.im →
      (∀ s, complexHeat (t:ℂ) (RHTower.rectangleBoundaryPath l u s) ≠ 0) →
      let D := fun w : ℂ => heatBoundaryDiscriminant ((t:ℂ)+w) l u
      ContinuousAt D 0 → ∃ᶠ w in 𝓝[≠] (0:ℂ), ‖D (2*w)/D w‖ < 3/2 := by
  rw [riemannHypothesis_iff_forall_pos_not_mem_branchTimes]
  constructor
  · intro hr t ht l u hx hy hb D hc
    have hd : D 0 ≠ 0 := by
      change heatBoundaryDiscriminant ((t:ℂ)+0) l u ≠ 0
      rw [add_zero,heatBoundaryDiscriminant_eq_zero_iff _ _ _ hx hy hb]
      rintro ⟨z,_,hz⟩
      exact hr t ht ⟨((t:ℂ),z),hz,rfl⟩
    have h₂ : Tendsto (fun w : ℂ => 2*w) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [mul_zero] using ((tendsto_const_nhds (x:=(2:ℂ))).mul
        (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun w : ℂ => w) (𝓝[≠] 0) (𝓝 0)))
    have hh := ((hc.tendsto.comp h₂).div (hc.tendsto.mono_left nhdsWithin_le_nhds) hd).norm
    rw [div_self hd,norm_one] at hh
    exact (hh.eventually_lt_const (by norm_num : (1:ℝ) < 3/2)).frequently
  · rintro h t ht ⟨⟨τ,z⟩,hc,he⟩
    change τ = (t:ℂ) at he
    subst τ
    have hm := (heatIntersectionMultiplicity_ne_zero_iff _).mpr hc
    have hc' := isCollision_iff_analyticOrderAt.mpr
      (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top (t:ℂ) z)).symm
    obtain ⟨l,u,hin,hb,hD,hk,_⟩ := hc'.boundaryMoment_regular_winding
    have hlim := (analytic_dilation_at_finite_order hD hk
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun w : ℂ => w) (𝓝[≠] 0) (𝓝 0))
      self_mem_nhdsWithin (tendsto_const_nhds (x:=(2:ℂ)))).norm
    let k := heatIntersectionMultiplicity ((t:ℂ),z)
    change Tendsto _ _ (𝓝 ‖(2:ℂ)^k‖) at hlim
    rw [norm_pow,show ‖(2:ℂ)‖=2 by norm_num] at hlim
    have hlarge : (3/2:ℝ) < 2^k := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.pos_of_ne_zero hm)
      exact (by norm_num : (3/2:ℝ)<2).trans_le (by simpa only [pow_one] using hh)
    obtain ⟨w,hw,hw'⟩ := ((h t ht l u (hin.1.trans hin.2.1).le (hin.2.2.1.trans hin.2.2.2).le hb
      hD.continuousAt).and_eventually (hlim.eventually_const_lt hlarge)).exists
    exact hw.not_ge hw'.le

#print axioms analytic_dilation_at_finite_order
#print axioms symmetric_dilation_quadratic_remainder
#print axioms heat_boundary_dilation_reads_multiplicity
#print axioms rh_iff_heat_boundary_doubling

end GaloisForLFunctions.GaloisTheoryOfZeros
