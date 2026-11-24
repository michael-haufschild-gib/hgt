import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.DilationAverage

/-! # Selecting first-passage sublevel events while averaging Gaussian rays -/
open Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
noncomputable section

/-- Dilation leaves an early-passage event true once it is true. -/
def expansionClosed {ι : Type*} (B : Set (ι → ℝ)) : Prop :=
  ∀ a : ℝ, 1≤a → ∀ x ∈ B, a • x ∈ B

private theorem ray_le_width {ι : Type*} (E : Set (ι → ℝ)) (x : ι → ℝ) {b : ℝ} (hb : 1≤b) :
    rayMass b E x≤b-1 := (measureReal_mono (subset_univ _)).trans_eq
      ((measureReal_restrict_apply_univ _).trans (Real.volume_real_Icc_of_le hb))

private theorem expanded_mass {ι : Type*} {B : Set (ι → ℝ)} (hB : expansionClosed B)
    (E : Set (ι → ℝ)) {x : ι → ℝ} (hx : x∈B) (b : ℝ) :
    rayMass b (B ∩ E) x=rayMass b E x := by
  let F (a : ℝ) := a • x
  have he : F ⁻¹' (B ∩ E) ∩ Icc 1 b=F ⁻¹' E ∩ Icc 1 b := by
    ext a
    constructor
    · exact fun h => ⟨h.1.2,h.2⟩
    · exact fun h => ⟨⟨hB a h.2.1 x hx,h.1⟩,h.2⟩
  change (volume.restrict (Icc 1 b)).real (F ⁻¹' (B ∩ E))=(volume.restrict (Icc 1 b)).real (F ⁻¹' E)
  rw [measureReal_restrict_apply' measurableSet_Icc,measureReal_restrict_apply' measurableSet_Icc,he]

private theorem full_mass {ι : Type*} {x : ι → ℝ} {b : ℝ} (hb : 1≤b) :
    rayMass b univ x=b-1 := by
  rw [rayMass,preimage_univ,measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le hb]

/-- The discrepancy from conditioning before dilation is paid entirely
by samples entering the selected event somewhere on the ray interval. -/
private theorem ray_discrepancy {ι : Type*} {B : Set (ι → ℝ)} (hB : expansionClosed B)
    (E : Set (ι → ℝ)) (x : ι → ℝ) {b : ℝ} (hb : 1≤b) :
    let R := rayMass b
    let W := B.indicator (R E)
    0≤R (B ∩ E) x-W x ∧
      R (B ∩ E) x-W x ≤ R B x-B.indicator (fun _ => b-1) x := by
  classical
  intro R W
  by_cases hx : x∈B
  · have hfull := expanded_mass hB univ hx b
    rw [inter_univ,full_mass hb] at hfull
    simp only [R,W,indicator_of_mem hx,expanded_mass hB E hx b,hfull,sub_self,le_refl,and_self]
  · have he : R (B ∩ E) x ≤ R B x := measureReal_mono (preimage_mono inter_subset_left)
    simpa only [W,indicator_of_notMem hx,sub_zero] using
      And.intro (show 0≤R (B ∩ E) x from measureReal_nonneg) he

/-- The normalized selected ray mean differs from the actual joint
probability by at most twice the excess Gaussian dilation Jacobian. -/
theorem selected_mean_error {ι : Type*} [Fintype ι] (B E : Set (ι → ℝ))
    (hm : MeasurableSet B) (he : MeasurableSet E) (hB : expansionClosed B) {b : ℝ} (hb : 1<b) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    |(∫ x, B.indicator (rayMass b E) x ∂μ)/(b-1)-μ.real (B ∩ E)| ≤ 2*(b^Fintype.card ι-1) := by
  classical
  intro μ
  let R := rayMass (ι:=ι) b
  let L := b-1
  let d := b^Fintype.card ι-1
  have hL : 0<L := sub_pos.mpr hb
  have hR (S : Set (ι → ℝ)) (hS : MeasurableSet S) : Integrable (R S) μ :=
    Integrable.of_bound (measurable_rayMass b hS).aestronglyMeasurable L (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤R S x from measureReal_nonneg)]
      exact ray_le_width S x hb.le)
  have hJ := hR (B ∩ E) (hm.inter he)
  have hW := (hR E he).indicator hm
  have hK := (integrable_const (μ:=μ) L).indicator hm
  have h₀ : 0≤∫ x, R (B ∩ E) x-B.indicator (R E) x ∂μ :=
    integral_nonneg fun x => (ray_discrepancy hB E x hb.le).1
  have h₁ := integral_mono (hJ.sub hW) ((hR B hm).sub hK) (fun x => (ray_discrepancy hB E x hb.le).2)
  let j := ∫ x, R (B ∩ E) x ∂μ
  let w := ∫ x, B.indicator (R E) x ∂μ
  let z := ∫ x, R B x ∂μ
  have hi : (∫ x, B.indicator (fun _ => L) x ∂μ)=μ.real B*L := by
    rw [integral_indicator hm,setIntegral_const,smul_eq_mul]
  rw [integral_sub hJ hW] at h₀
  simp only [Pi.sub_apply] at h₁
  rw [integral_sub hJ hW,integral_sub (hR B hm) hK,hi] at h₁
  change 0≤j-w at h₀
  change j-w≤z-μ.real B*L at h₁
  have hz := (abs_le.mp (mean_rayMass_error B hm hb)).2
  have hj := abs_le.mp (mean_rayMass_error (B ∩ E) (hm.inter he) hb)
  change z/L-μ.real B≤d at hz
  change -d≤j/L-μ.real (B ∩ E) ∧ j/L-μ.real (B ∩ E)≤d at hj
  have hh := div_le_div_of_nonneg_right h₁ hL.le
  rw [sub_div,sub_div (z:ℝ),mul_div_cancel_right₀ _ hL.ne'] at hh
  have hwj : w/L≤j/L := div_le_div_of_nonneg_right (sub_nonneg.mp h₀) hL.le
  have hd : 0≤d := sub_nonneg.mpr (one_le_pow₀ hb.le)
  change |w/L-μ.real (B ∩ E)| ≤ 2*d
  exact abs_le.mpr ⟨by linarith only [hh,hz,hj.1],by linarith only [hwj,hj.2,hd]⟩

#print axioms selected_mean_error
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
