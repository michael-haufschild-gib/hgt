import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheBoundaryMomentsOfAHeatWindow
import GaloisForLFunctions.RHTower.ModulusHolography
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Geometric means of the theta boundary discriminant

A complete circle average of the logarithmic modulus removes the analytic
unit in a radial comparison. The slope in log radius then gives the local
heat intersection multiplicity exactly at every sufficiently small scale.
Two time circles detect collisions without choosing a phase. On a real
time segment, reciprocal powers of the same determinant give a second
test through the self-duality of quadratic Muckenhoupt weights.
-/

open Complex Set Filter Topology Metric MeasureTheory
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
noncomputable section
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Angular mean of the logarithmic modulus of the spatial moment
determinant, sampled on a circle in complex time. -/
def heatBoundaryLogMean (τ l u : ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun w => Real.log ‖heatBoundaryDiscriminant (τ+w) l u‖) 0 r

private theorem affine_log_mean {D : ℂ → ℂ} {k : ℕ} (hD : AnalyticAt ℂ D 0)
    (hk : analyticOrderAt D 0 = (k:ℕ∞)) :
    ∃ R > 0, ∃ b : ℝ, ∀ r : ℝ, 0<r → r<R →
      Real.circleAverage (fun w => Real.log ‖D w‖) 0 r = (k:ℝ)*Real.log r+b := by
  obtain ⟨V,hV,hv,hf⟩ := hD.analyticOrderAt_eq_natCast.mp hk
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp
    (hf.and (hV.eventually_analyticAt.and (hV.continuousAt.eventually_ne hv)))
  refine ⟨R,hR,Real.log ‖V 0‖,fun r hr hrR => ?_⟩
  exact RHTower.circleAverage_log_norm_single_zero hr hrR (fun w hw => (hball hw).2.1)
    (fun w hw => (hball hw).2.2) (fun w hw => by simpa only [smul_eq_mul] using (hball hw).1)

/-- In a regular spatial window about any marked place, the logarithmic
mean is exactly affine throughout a punctured interval. Its slope counts
the heat intersection, including higher spatial multiplicities. -/
theorem heat_boundary_log_mean_at_place (τ z : ℂ) :
    ∃ l u : ℂ, (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
      (∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0) ∧
      ∃ R > 0, ∃ b : ℝ, ∀ r : ℝ, 0<r → r<R →
        heatBoundaryLogMean τ l u r = (heatIntersectionMultiplicity (τ,z):ℝ)*Real.log r+b := by
  have hc := isCollision_iff_analyticOrderAt.mpr
    (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top τ z)).symm
  obtain ⟨l,u,hin,hreg,hD,hk,_⟩ := hc.boundaryMoment_regular_winding
  exact ⟨l,u,hin,hreg,affine_log_mean hD hk⟩

/-- The real radial increment, with no phase choice, recovers the winding
of the actual theta determinant. Both radii may be chosen independently. -/
theorem heat_boundary_annular_mass (τ z : ℂ) :
    ∃ l u : ℂ, (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
      (∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0) ∧
      ∃ R > 0, ∀ r s : ℝ, 0<r → r<s → s<R →
        (heatBoundaryLogMean τ l u s-heatBoundaryLogMean τ l u r)/Real.log (s/r) =
          (heatIntersectionMultiplicity (τ,z):ℝ) := by
  obtain ⟨l,u,hin,hreg,R,hR,b,h⟩ := heat_boundary_log_mean_at_place τ z
  refine ⟨l,u,hin,hreg,R,hR,fun r s hr hrs hsR => ?_⟩
  have hd := Real.log_pos ((one_lt_div hr).mpr hrs)
  apply (div_eq_iff hd.ne').mpr
  rw [h s (hr.trans hrs) hsR,h r hr (hrs.trans hsR),Real.log_div (hr.trans hrs).ne' hr.ne']
  ring

/-- RH is equivalent to exact equality of the two angular means at
arbitrarily small dyadic radii in all regular analytic spatial windows.
The angular mean cancels the contribution of every nonvanishing factor. -/
theorem rh_iff_equal_heat_boundary_means :
    RiemannHypothesis ↔ ∀ t : ℝ, 0<t → ∀ l u : ℂ, l.re ≤ u.re → l.im ≤ u.im →
      (∀ s, complexHeat (t:ℂ) (RHTower.rectangleBoundaryPath l u s) ≠ 0) →
      AnalyticAt ℂ (fun w => heatBoundaryDiscriminant ((t:ℂ)+w) l u) 0 →
      ∀ ε > 0, ∃ r : ℝ, 0<r ∧ 2*r<ε ∧
        heatBoundaryLogMean t l u (2*r) = heatBoundaryLogMean t l u r := by
  rw [riemannHypothesis_iff_forall_pos_not_mem_branchTimes]
  constructor
  · intro h t ht l u hl hu hreg hD ε hε
    let D := fun w : ℂ => heatBoundaryDiscriminant ((t:ℂ)+w) l u
    have h₀ : D 0 ≠ 0 := by
      change heatBoundaryDiscriminant ((t:ℂ)+0) l u ≠ 0
      rw [add_zero,heatBoundaryDiscriminant_eq_zero_iff _ _ _ hl hu hreg]
      rintro ⟨z,_,hz⟩
      exact h t ht ⟨((t:ℂ),z),hz,rfl⟩
    have hk : analyticOrderAt D 0 = (0:ℕ∞) :=
      hD.analyticOrderAt_eq_natCast.mpr ⟨D,hD,h₀,by simp⟩
    obtain ⟨R,hR,b,h⟩ := affine_log_mean hD hk
    let r := min R ε/4
    have hr : 0<r := div_pos (lt_min hR hε) (by norm_num)
    have h₁ := min_le_left R ε
    have h₂ := min_le_right R ε
    have hR' : 2*r<R := by dsimp only [r]; linarith only [h₁,hR]
    have hε' : 2*r<ε := by dsimp only [r]; linarith only [h₂,hε]
    refine ⟨r,hr,hε',?_⟩
    change Real.circleAverage (fun w => Real.log ‖D w‖) 0 (2*r) = _
    rw [h _ (by linarith only [hr]) hR']
    change _ = Real.circleAverage (fun w => Real.log ‖D w‖) 0 r
    rw [h _ hr (by linarith only [hr,hR'])]
    simp
  · rintro h t ht ⟨⟨τ,z⟩,hc,he⟩
    change τ=(t:ℂ) at he
    subst τ
    have hpos := (heatIntersectionMultiplicity_ne_zero_iff _).mpr hc
    have hs := isCollision_iff_analyticOrderAt.mpr
      (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top (t:ℂ) z)).symm
    obtain ⟨l,u,hin,hreg,hD,hk,_⟩ := hs.boundaryMoment_regular_winding
    obtain ⟨R,hR,b,hm⟩ := affine_log_mean hD hk
    obtain ⟨r,hr,hR',heq⟩ := h t ht l u (hin.1.trans hin.2.1).le
      (hin.2.2.1.trans hin.2.2.2).le hreg hD R hR
    let k := heatIntersectionMultiplicity ((t:ℂ),z)
    change ∀ r : ℝ, 0<r → r<R → _ = (k:ℝ)*Real.log r+b at hm
    unfold heatBoundaryLogMean at heq
    rw [hm _ (by linarith only [hr]) hR',hm _ hr (by linarith only [hr,hR']),
      Real.log_mul (by norm_num) hr.ne'] at heq
    have hkpos : 0<(k:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hpos)
    linarith only [heq,mul_pos hkpos (Real.log_pos (by norm_num : (1:ℝ)<2))]


/-- Along real time the reciprocal-weight threshold records the full
multiplicity. The integrability tests for a power and its dual exchange
under sign change, as in Fang–Phan, Proposition 2.2. -/
private theorem real_slice_power_integrability {D : ℂ → ℂ} {k : ℕ}
    (hD : AnalyticAt ℂ D 0) (hk : analyticOrderAt D 0 = (k:ℕ∞)) :
    ∃ R > 0, ∀ r : ℝ, 0<r → r<R → ∀ α : ℝ,
      IntegrableOn (fun t : ℝ => ‖D (t:ℂ)‖^α) (Ioo 0 r) ↔ -1<(k:ℝ)*α := by
  obtain ⟨V,hV,hv,hf⟩ := hD.analyticOrderAt_eq_natCast.mp hk
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp
    (hf.and (hV.eventually_analyticAt.and (hV.continuousAt.eventually_ne hv)))
  refine ⟨R,hR,fun r hr hrR α => ?_⟩
  let U (t : ℝ) := ‖V (t:ℂ)‖^α
  have inball (t : ℝ) (ht : t ∈ Icc 0 r) : (t:ℂ) ∈ ball 0 R := by
    simpa only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1] using ht.2.trans_lt hrR
  have cont : ContinuousOn U (Icc 0 r) := by
    intro t ht
    have h := hball (inball t ht)
    exact (((h.2.1.continuousAt.comp Complex.continuous_ofReal.continuousAt).norm).rpow_const
      (Or.inl (norm_ne_zero_iff.mpr h.2.2))).continuousWithinAt
  have hU (t : ℝ) (ht : t ∈ Icc 0 r) : U t ≠ 0 :=
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr (hball (inball t ht)).2.2) _).ne'
  have factor (t : ℝ) (ht : t ∈ Ioo 0 r) : ‖D (t:ℂ)‖^α = t^((k:ℝ)*α)*U t := by
    have h := (hball (inball t (Ioo_subset_Icc_self ht))).1
    simp only [sub_zero,smul_eq_mul] at h
    rw [h,norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _),norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1,Real.rpow_natCast_mul ht.1.le]
  rw [←intervalIntegral.integrableOn_Ioo_rpow_iff hr]
  constructor
  · intro h
    have hh := h.mul_continuousOn_of_subset (cont.inv₀ hU) measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
    exact hh.congr_fun (fun t ht => by rw [factor t ht]; exact mul_inv_cancel_right₀ (hU t (Ioo_subset_Icc_self ht)) _) measurableSet_Ioo
  · intro h
    exact (h.mul_continuousOn_of_subset cont measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self).congr_fun
      (fun t ht => (factor t ht).symm) measurableSet_Ioo

/-- Both members of the reciprocal pair are locally integrable exactly
inside the open interval of exponents of width twice the reciprocal
collision multiplicity. The critical endpoint is excluded. -/
theorem heat_boundary_reciprocal_pair (τ z : ℂ) :
    ∃ l u : ℂ, (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
      (∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0) ∧
      ∃ R > 0, ∀ r : ℝ, 0<r → r<R → ∀ α : ℝ,
        let D := fun t : ℝ => heatBoundaryDiscriminant (τ+(t:ℂ)) l u
        (IntegrableOn (fun t : ℝ => ‖D t‖^α) (Ioo 0 r) ∧
          IntegrableOn (fun t : ℝ => ‖D t‖^(-α)) (Ioo 0 r)) ↔
          |(heatIntersectionMultiplicity (τ,z):ℝ)*α|<1 := by
  have hc := isCollision_iff_analyticOrderAt.mpr
    (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top τ z)).symm
  obtain ⟨l,u,hin,hreg,hD,hk,_⟩ := hc.boundaryMoment_regular_winding
  obtain ⟨R,hR,h⟩ := real_slice_power_integrability hD hk
  refine ⟨l,u,hin,hreg,R,hR,fun r hr hrR α => ?_⟩
  dsimp only
  rw [h r hr hrR α,h r hr hrR (-α),abs_lt,mul_neg]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨h₁,by linarith only [h₂]⟩

/-- A single inverse-modulus integral on a short real-time segment is a
complete test on regular analytic windows. A collision of any order
already has a nonintegrable inverse on every such segment. -/
theorem rh_iff_locally_integrable_inverse_heat_boundary :
    RiemannHypothesis ↔ ∀ t : ℝ, 0<t → ∀ l u : ℂ, l.re ≤ u.re → l.im ≤ u.im →
      (∀ s, complexHeat (t:ℂ) (RHTower.rectangleBoundaryPath l u s) ≠ 0) →
      AnalyticAt ℂ (fun w => heatBoundaryDiscriminant ((t:ℂ)+w) l u) 0 →
      ∃ r > 0, IntegrableOn (fun s : ℝ => ‖heatBoundaryDiscriminant ((t:ℂ)+(s:ℂ)) l u‖⁻¹) (Ioo 0 r) := by
  rw [riemannHypothesis_iff_forall_pos_not_mem_branchTimes]
  constructor
  · intro h t ht l u hl hu hreg hD
    let D := fun w : ℂ => heatBoundaryDiscriminant ((t:ℂ)+w) l u
    have h₀ : D 0 ≠ 0 := by
      change heatBoundaryDiscriminant ((t:ℂ)+0) l u ≠ 0
      rw [add_zero,heatBoundaryDiscriminant_eq_zero_iff _ _ _ hl hu hreg]
      rintro ⟨z,_,hz⟩
      exact h t ht ⟨((t:ℂ),z),hz,rfl⟩
    have hk : analyticOrderAt D 0 = (0:ℕ∞) :=
      hD.analyticOrderAt_eq_natCast.mpr ⟨D,hD,h₀,by simp⟩
    obtain ⟨R,hR,H⟩ := real_slice_power_integrability hD hk
    refine ⟨R/2,half_pos hR,?_⟩
    simpa only [Real.rpow_neg_one] using
      (H (R/2) (half_pos hR) (half_lt_self hR) (-1)).mpr (by norm_num)
  · rintro h t ht ⟨⟨τ,z⟩,hc,he⟩
    change τ=(t:ℂ) at he
    subst τ
    have hc' := isCollision_iff_analyticOrderAt.mpr
      (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top (t:ℂ) z)).symm
    obtain ⟨l,u,hin,hreg,hD,hk,_⟩ := hc'.boundaryMoment_regular_winding
    obtain ⟨R,hR,H⟩ := real_slice_power_integrability hD hk
    obtain ⟨s,hs,hint⟩ := h t ht l u (hin.1.trans hin.2.1).le
      (hin.2.2.1.trans hin.2.2.2).le hreg hD
    let r := min R s/2
    have hr : 0<r := half_pos (lt_min hR hs)
    have hrR : r<R := (half_lt_self (lt_min hR hs)).trans_le (min_le_left _ _)
    have hrs : r≤s := ((half_lt_self (lt_min hR hs)).le).trans (min_le_right _ _)
    have htest := (H r hr hrR (-1)).mp (by
      simpa only [Real.rpow_neg_one] using hint.mono_set (Ioo_subset_Ioo_right hrs))
    have hpos := (heatIntersectionMultiplicity_ne_zero_iff _).mpr hc
    have hmin : (1:ℝ) ≤ (heatIntersectionMultiplicity ((t:ℂ),z):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hpos
    change -1 < (heatIntersectionMultiplicity ((t:ℂ),z):ℝ)*(-1) at htest
    linarith only [htest,hmin]

#print axioms heat_boundary_reciprocal_pair
#print axioms rh_iff_locally_integrable_inverse_heat_boundary
#print axioms heat_boundary_log_mean_at_place
#print axioms heat_boundary_annular_mass
#print axioms rh_iff_equal_heat_boundary_means
end GaloisForLFunctions.GaloisTheoryOfZeros
