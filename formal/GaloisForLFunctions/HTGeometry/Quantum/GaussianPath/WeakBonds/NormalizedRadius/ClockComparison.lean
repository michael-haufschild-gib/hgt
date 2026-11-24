import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.RadialBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.FixedRadius

/-! # Comparing fixed-radius and Gaussian first-clock tails -/
open Set MeasureTheory ProbabilityTheory Metric Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
open PrescribedTimes PassageMoments.DerivativeBounds
noncomputable section

/-- A direction with normalized clock above twice a deadline misses that
deadline on every radius up to twice the root mean square. The independent
radial interval has probability at least three quarters. -/
theorem fixed_radius_clock_comparison (n : ℕ) (J : (PrefixIndex n → ℝ) → ℝ) (hJ : Measurable J)
    (hh : ∀ a > (0:ℝ), ∀ x, a*J (a • x)=J x) {G : ℝ} (hG : 0≤G) :
    let r := sqrt (Fintype.card (PrefixIndex n):ℝ)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    (3/4:ℝ)*μ.real {x | 2*G<J (atRadius r x)} ≤ μ.real {x | G<J x} := by
  intro r μ
  let m := Fintype.card (ChainLabel (n+2))
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) ((pathCoeffEquiv n).symm (Sum.inl (0,0))).isLt
  have hr : r=sqrt (m:ℝ) := by simp only [r,PrefixIndex,Fintype.card_fin,m]
  have hrpos : 0<r := by rw [hr]; exact sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  let α := gaussianAngularMeasure m
  let ν := gaussianRadiusMeasure m
  letI : IsProbabilityMeasure α := ⟨gaussianAngularMeasure_univ hm⟩
  letI : IsProbabilityMeasure ν := ⟨gaussianRadiusMeasure_univ hm⟩
  let E := {x : PrefixIndex n → ℝ | G<J x}
  let F := {x : PrefixIndex n → ℝ | 2*G<J (atRadius r x)}
  let A := {y : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 | 2*G<J (r • y.val.ofLp)}
  let B := {u : Ioi (0:ℝ) | u.val≤2*r}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hJ
  have hn : Measurable (coefficientNorm (n:=n)) := (MeasurableEquiv.toLp 2 (PrefixIndex n → ℝ)).measurable.norm
  have hF : MeasurableSet F := measurableSet_lt measurable_const (hJ.comp ((measurable_const.div hn).smul measurable_id))
  have he : polarCoordinates m ⁻¹' F=A ×ˢ univ := by
    ext ⟨y,u⟩
    change 2*G<J ((r/coefficientNorm (u.val • y.val.ofLp)) • (u.val • y.val.ofLp)) ↔ _ ∧ _
    have hnu : coefficientNorm (u.val • y.val.ofLp)=u.val := by
      change ‖u.val • y.val‖=u.val
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos u.property,norm_eq_of_mem_sphere,mul_one]
    rw [hnu,smul_smul,div_mul_cancel₀ _ u.property.ne']
    exact ⟨fun h => ⟨h,mem_univ _⟩,fun h => h.1⟩
  have hmass : μ.real F=α.real A := by
    have hraw : μ.real F=(α.prod ν).real (polarCoordinates m ⁻¹' F) := gaussian_polar_event m hm F hF
    rw [hraw,he,measureReal_prod_prod]
    change α.real A*ν.real univ=α.real A
    rw [probReal_univ,mul_one]
  have hs : A ×ˢ B ⊆ polarCoordinates m ⁻¹' E := by
    rintro ⟨y,u⟩ ⟨hy,hu⟩
    change 2*G<J (r • y.val.ofLp) at hy
    change G<J (u.val • y.val.ofLp)
    apply (mul_lt_mul_iff_right₀ u.property).mp
    rw [hh _ u.property]
    have h := mul_lt_mul_of_pos_left hy hrpos
    rw [hh _ hrpos] at h
    apply lt_of_le_of_lt _ h
    change u.val*G≤r*(2*G)
    exact (mul_le_mul_of_nonneg_right hu hG).trans_eq (by ring)
  have hb : (3/4:ℝ)≤ν.real B := by
    change (3/4:ℝ)≤ν.real {u : Ioi (0:ℝ) | u.val≤2*r}
    rw [hr]
    exact gaussian_radius_mass m hm
  change (3/4:ℝ)*μ.real F≤μ.real E
  have hraw : μ.real E=(α.prod ν).real (polarCoordinates m ⁻¹' E) := gaussian_polar_event m hm E hE
  rw [hmass,hraw,mul_comm (3/4:ℝ)]
  exact (mul_le_mul_of_nonneg_left hb measureReal_nonneg).trans
    ((measureReal_prod_prod A B).symm.le.trans (measureReal_mono (μ:=α.prod ν) hs))

#print axioms fixed_radius_clock_comparison
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
