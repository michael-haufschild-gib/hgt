import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarParitySourceProfile
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCovarianceReflection

/-!
# Nonzero Weil source coupling in both constrained parity sectors

The two parity profiles are identified with actual reflected aperture L²
defects and their continuous complete-domain functionals. On a pure-parity
state the original forcing moment is exactly half the corresponding kernel
integral. Endpoint divergence excludes every two-pole representative in both
channels. Each constrained parity sector realizes every complex source moment,
and the original and reflected moments are jointly surjective. These facts do
not determine the moment of a selected ground or exclude its forced equation.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology ENNReal
noncomputable section
namespace RHTower

/-- The actual L² source defect in a reflection channel. -/
def ccmPolarParityBoundaryDefect (a : SuzukiPositiveAperture) (r : ℝ) : suzukiApertureHilbert a :=
  ccmPolarWeilBoundaryDefect a+(r:ℂ) • suzukiAperturePhysicalReflection a (ccmPolarWeilBoundaryDefect a)

/-- The full source functional plus its reflected channel, before restricting the test parity. -/
def ccmPolarParityBoundarySourceFunctional (a : SuzukiPositiveAperture) (r : ℝ) :
    CCMArchimedeanFormDomain a →L[ℂ] ℂ :=
  ccmPolarBoundarySourceFunctional a+(r:ℂ) • (ccmPolarBoundarySourceFunctional a).comp
    (ccmArchimedeanFormReflection a).toContinuousLinearMap

/-- Reflection transports the complete source functional to the literal L² defect. -/
theorem ccmPolarParityBoundarySourceFunctional_eq_inner (a : SuzukiPositiveAperture) (r : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    ccmPolarParityBoundarySourceFunctional a r u =
      inner ℂ (ccmPolarParityBoundaryDefect a r) (ccmArchimedeanFormToAperture a u) := by
  change inner ℂ (ccmPolarWeilBoundaryDefect a : SoninL2) (ccmArchimedeanFormToAperture a u : SoninL2)+
    (r:ℂ)*inner ℂ (ccmPolarWeilBoundaryDefect a : SoninL2)
      (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) : SoninL2) =
        inner ℂ ((ccmPolarWeilBoundaryDefect a : SoninL2)+(r:ℂ) • l2Reflection (ccmPolarWeilBoundaryDefect a : SoninL2))
          (ccmArchimedeanFormToAperture a u : SoninL2)
  rw [inner_add_left,inner_smul_left (l2Reflection (ccmPolarWeilBoundaryDefect a : SoninL2))
    (ccmArchimedeanFormToAperture a u : SoninL2) (r:ℂ),Complex.conj_ofReal,
    ccmArchimedeanFormToAperture_reflection]
  exact congrArg (fun z : ℂ => inner ℂ (ccmPolarWeilBoundaryDefect a : SoninL2)
    (ccmArchimedeanFormToAperture a u : SoninL2)+(r:ℂ)*z)
      (l2Reflection_symmetric (ccmPolarWeilBoundaryDefect a : SoninL2)
        (ccmArchimedeanFormToAperture a u : SoninL2)).symm

/-- The reflected source defect has exactly the two-channel physical profile. -/
theorem ccmPolarParityBoundaryDefect_coeFn (a : SuzukiPositiveAperture) (r : ℝ) :
    ((ccmPolarParityBoundaryDefect a r : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (ccmPolarParityBoundaryProfile a r) := by
  let d : SoninL2 := (ccmPolarWeilBoundaryDefect a : SoninL2)
  have hn := (ccmPolarWeilBoundaryDefect_coeFn a).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  change (((d+(r:ℂ) • l2Reflection d : SoninL2)) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add d ((r:ℂ) • l2Reflection d), Lp.coeFn_smul (r:ℂ) (l2Reflection d),
    l2Reflection_ae d, ccmPolarWeilBoundaryDefect_coeFn a,hn] with x ha hs hr hd hn
  simp only [Pi.add_apply,Pi.smul_apply] at ha hs
  rw [ha,hs,hr]
  change d x = _ at hd
  change d (-x) = (centralInterval a.1).indicator (ccmPolarBoundaryArithmeticProfile a) (-x) at hn
  rw [hd,hn]
  by_cases hx : x ∈ centralInterval a.1
  · have hnx := (neg_mem_centralInterval_iff a.1 x).mpr hx
    simp only [indicator_of_mem hx,indicator_of_mem hnx,ccmPolarParityBoundaryProfile,smul_eq_mul]
  · have hnx := mt (neg_mem_centralInterval_iff a.1 x).mp hx
    simp [indicator_of_notMem hx,indicator_of_notMem hnx]

/-- Exact complete-domain integral of each reflected source functional. -/
theorem ccmPolarParityBoundarySourceFunctional_eq_integral (a : SuzukiPositiveAperture) (r : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    ccmPolarParityBoundarySourceFunctional a r u =
      ∫ x : ℝ, (centralInterval a.1).indicator (ccmPolarParityBoundaryProfile a r) x *
        (ccmArchimedeanFormToAperture a u : SoninL2) x := by
  rw [ccmPolarParityBoundarySourceFunctional_eq_inner]
  change inner ℂ (ccmPolarParityBoundaryDefect a r : SoninL2) (ccmArchimedeanFormToAperture a u : SoninL2)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmPolarParityBoundaryDefect_coeFn a r] with x hx
  rw [hx]
  by_cases hi : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hi,RCLike.inner_apply,ccmPolarParityBoundaryProfile,
      ccmPolarBoundaryArithmeticProfile,map_add,map_mul,Complex.conj_ofReal]
    ring
  · simp [indicator_of_notMem hi]

/-- On a pure-parity vector, its reflected source moment is precisely twice its original moment. -/
theorem ccmPolarParityBoundarySourceFunctional_on_parity (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) (u : CCMArchimedeanFormDomain a)
    (hu : ccmArchimedeanFormReflection a u=(r:ℂ) • u) :
    ccmPolarParityBoundarySourceFunctional a r u = 2*ccmPolarBoundarySourceFunctional a u := by
  change ccmPolarBoundarySourceFunctional a u+(r:ℂ)*
    ccmPolarBoundarySourceFunctional a (ccmArchimedeanFormReflection a u)=_
  rw [hu,map_smul,smul_eq_mul]
  rcases hr with rfl | rfl <;> norm_num <;> ring

/-- The forcing numerator of a parity state is one half of the corresponding exact physical kernel integral. -/
theorem ccmPolarBoundarySourceFunctional_on_parity_eq_integral (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) (u : CCMArchimedeanFormDomain a)
    (hu : ccmArchimedeanFormReflection a u=(r:ℂ) • u) :
    ccmPolarBoundarySourceFunctional a u = (1/2:ℂ)*
      ∫ x : ℝ, (centralInterval a.1).indicator (ccmPolarParityBoundaryProfile a r) x *
        (ccmArchimedeanFormToAperture a u : SoninL2) x := by
  rw [← ccmPolarParityBoundarySourceFunctional_eq_integral,
    ccmPolarParityBoundarySourceFunctional_on_parity a hr u hu]
  ring
private theorem not_ae_bounded_of_tendsto_right {a l C : ℝ} (hl : l<a) (f : ℝ → ℝ)
    (ht : Tendsto f (𝓝[<] a) atTop)
    (hb : ∀ᵐ x : ℝ, x ∈ Ioo l a → f x ≤ C) : False := by
  have he : ∀ᶠ x in 𝓝[<] a, x ∈ Ioo l a ∧ C+1 ≤ f x := by
    filter_upwards [Ioo_mem_nhdsLT hl, ht.eventually_ge_atTop (C+1)] with x hx hy
    exact ⟨hx,hy⟩
  obtain ⟨b,hb',hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  have hm : volume (Ioo b a) ≠ 0 := isOpen_Ioo.measure_ne_zero volume (nonempty_Ioo.mpr hb')
  obtain ⟨x,hx,hbx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hb)
  have h := hsub hx
  have := hbx h.1
  linarith [h.2]

/-- Neither parity source profile has an essential upper bound on the aperture. -/
theorem not_ae_bounded_ccmPolarParityBoundaryProfile (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) (C : ℝ) :
    ¬ ∀ᵐ x : ℝ, x ∈ Ioo (-a.1) a.1 → (ccmPolarParityBoundaryProfile a r x).re≤C :=
  not_ae_bounded_of_tendsto_right (by linarith [a.property]) _
    (tendsto_ccmPolarParityBoundaryProfile_re_right a hr)

/-- Each actual parity source defect lies outside the entire two-pole span. -/
theorem ccmPolarParityBoundaryDefect_ne_forcing (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) (c : ℂ × ℂ) :
    ccmPolarParityBoundaryDefect a r ≠ ccmPolarForcing a c := by
  intro heq
  let q : ℝ → ℂ := fun x => c.1*ccmPolarProfile (1/2) x+c.2*ccmPolarProfile (-1/2) x
  have hq : Continuous q := by dsimp [q,ccmPolarProfile]; fun_prop
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
  apply not_ae_bounded_ccmPolarParityBoundaryProfile a hr C
  have hd := ccmPolarParityBoundaryDefect_coeFn a r
  rw [heq] at hd
  filter_upwards [hd,ccmPolarForcing_coeFn a c] with x hx hy
  intro hxin
  have hi : x ∈ centralInterval a.1 := Ioo_subset_Icc_self hxin
  rw [indicator_of_mem hi] at hx hy
  have he : ccmPolarParityBoundaryProfile a r x=q x := hx.symm.trans hy
  rw [he]
  exact (Complex.re_le_norm _).trans (hC x hi)

private theorem exists_reflected_source_ne_zero (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ccmPolarParityBoundarySourceFunctional a r u ≠ 0 := by
  by_contra h
  have hzero : ∀ u, IsPolarConstrained a u → ccmPolarParityBoundarySourceFunctional a r u=0 := by
    simpa only [not_exists,not_and,not_not] using h
  obtain ⟨c,hc,_⟩ := existsUnique_ccmPolarForcing_representative a
    (ccmPolarParityBoundarySourceFunctional a r) hzero
  apply ccmPolarParityBoundaryDefect_ne_forcing a hr c
  apply (denseRange_ccmArchimedeanFormToAperture a).eq_of_inner_left ℂ
  intro u
  rw [← ccmPolarParityBoundarySourceFunctional_eq_inner]
  exact hc u

/-- At every aperture, the original source functional is nonzero separately on both constrained parity sectors. -/
theorem exists_polarParity_boundarySource_ne_zero (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ccmArchimedeanFormReflection a u=(r:ℂ) • u ∧ ccmPolarBoundarySourceFunctional a u ≠ 0 := by
  obtain ⟨v,hv,hne⟩ := exists_reflected_source_ne_zero a hr
  let u := v+(r:ℂ) • ccmArchimedeanFormReflection a v
  have hu : IsPolarConstrained a u :=
    (ccmPolarConstraintSubmodule a).add_mem hv ((ccmPolarConstraintSubmodule a).smul_mem _ hv.reflection)
  have hpar : ccmArchimedeanFormReflection a u=(r:ℂ) • u := by
    rcases hr with rfl | rfl
    · change ccmArchimedeanFormReflection a (v+(1:ℂ) • ccmArchimedeanFormReflection a v)=
        (1:ℂ) • (v+(1:ℂ) • ccmArchimedeanFormReflection a v)
      simp only [one_smul,map_add,ccmArchimedeanFormReflection_involutive]
      abel
    · change ccmArchimedeanFormReflection a (v+((-1:ℝ):ℂ) • ccmArchimedeanFormReflection a v)=
        ((-1:ℝ):ℂ) • (v+((-1:ℝ):ℂ) • ccmArchimedeanFormReflection a v)
      simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul,map_add,map_neg,ccmArchimedeanFormReflection_involutive]
      abel
  refine ⟨u,hu,hpar,?_⟩
  have hF : ccmPolarBoundarySourceFunctional a u=ccmPolarParityBoundarySourceFunctional a r v := by
    change ccmPolarBoundarySourceFunctional a (v+(r:ℂ) • ccmArchimedeanFormReflection a v)=
      ccmPolarBoundarySourceFunctional a v+(r:ℂ)*ccmPolarBoundarySourceFunctional a (ccmArchimedeanFormReflection a v)
    rw [map_add,map_smul,smul_eq_mul]
  rwa [hF]

/-- Every complex moment occurs in each completed constrained reflection sector. -/
theorem exists_polarParity_boundarySource_eq (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) (z : ℂ) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ccmArchimedeanFormReflection a u=(r:ℂ) • u ∧ ccmPolarBoundarySourceFunctional a u=z := by
  obtain ⟨v,hv,hpar,hne⟩ := exists_polarParity_boundarySource_ne_zero a hr
  let t := z / ccmPolarBoundarySourceFunctional a v
  refine ⟨t • v,(ccmPolarConstraintSubmodule a).smul_mem t hv,?_,?_⟩
  · rw [map_smul,hpar,smul_smul,smul_smul,mul_comm]
  · rw [map_smul,smul_eq_mul]
    exact div_mul_cancel₀ z hne

/-- The original and reflected source moments are jointly independent on the actual constrained space. -/
theorem polarConstrained_jointBoundarySource_surjective (a : SuzukiPositiveAperture) :
    Function.Surjective (fun u : ccmPolarConstraintSubmodule a =>
      (ccmPolarBoundarySourceFunctional a u.1,
        ccmPolarBoundarySourceFunctional a (ccmArchimedeanFormReflection a u.1))) := by
  intro z
  obtain ⟨e,he,hRe,hFe⟩ := exists_polarParity_boundarySource_eq a (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)=-1)
    ((z.1+z.2)/2)
  obtain ⟨o,ho,hRo,hFo⟩ := exists_polarParity_boundarySource_eq a (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ)=-1)
    ((z.1-z.2)/2)
  refine ⟨⟨e+o,(ccmPolarConstraintSubmodule a).add_mem he ho⟩,?_⟩
  apply Prod.ext
  · change ccmPolarBoundarySourceFunctional a (e+o)=z.1
    rw [map_add,hFe,hFo]
    ring
  · change ccmPolarBoundarySourceFunctional a (ccmArchimedeanFormReflection a (e+o))=z.2
    rw [map_add,hRe,hRo,map_add,map_smul,map_smul]
    simp only [Complex.ofReal_one,Complex.ofReal_neg,smul_eq_mul,one_mul,neg_one_mul,hFe,hFo]
    ring
end RHTower
