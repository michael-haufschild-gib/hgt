import GaloisForLFunctions.RHTower.CCM.CCMFinitePointGramObstruction
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundEnergy

/-!
# Finite physical sampling leaves the pole-constrained ground energy unchanged

Every arbitrary prescription on finitely many strict-interior physical points
has a smooth exact-pole realization of arbitrarily small form norm. Each sampling
fibre is dense in the complete constrained sector. Continuity of the complete
Weil quadratic and physical mass therefore preserves the exact Rayleigh infimum.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
namespace RHTower

private theorem polar_add {a : SuzukiPositiveAperture}
    {u v : CCMArchimedeanFormDomain a}
    (hu : IsPolarConstrained a u) (hv : IsPolarConstrained a v) :
    IsPolarConstrained a (u + v) := by
  simp only [IsPolarConstrained, map_add, inner_add_right,
    hu.1, hu.2, hv.1, hv.2, add_zero, and_self]

private def zeroInteriorSource (a : SuzukiPositiveAperture) :
    CCMComplexSmoothInteriorSource a where
  toFun := 0
  smooth := contDiff_const
  hasCompactSupport := by
    change IsCompact (tsupport (0 : ℝ → ℂ))
    rw [tsupport_zero]
    exact isCompact_empty
  tsupport_subset := by
    rw [tsupport_zero]
    exact empty_subset _

private theorem zeroInteriorSource_form (a : SuzukiPositiveAperture) :
    (zeroInteriorSource a).toCCMFormVector = 0 := by
  apply ccmArchimedeanFormToAperture_injective
  apply Subtype.ext
  rw [map_zero]
  apply Lp.ext
  filter_upwards [(zeroInteriorSource a).toCCMFormVector_physical_coeFn,
    (Lp.coeFn_zero ℂ 2 volume)] with x hx hz
  exact hx.trans hz.symm

/-- Arbitrary finite interior samples have zero capacity in the exact pole-constrained form. -/
theorem exists_ccmPolarConstrained_finite_interpolant_norm_lt
    (a : SuzukiPositiveAperture) (s : Finset ℝ) (v : ℝ → ℂ)
    (hs : ∀ x ∈ s, |x| < a.1) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧
      (∀ x ∈ s, g x = v x) ∧ ‖g.toCCMFormVector‖ < ε := by
  classical
  induction s using Finset.induction_on generalizing ε with
  | empty =>
    refine ⟨zeroInteriorSource a, ?_, by simp, ?_⟩
    · rw [zeroInteriorSource_form]; simp [IsPolarConstrained]
    · simpa [zeroInteriorSource_form] using hε
  | @insert x s hxs ih =>
    obtain ⟨g, hg, hgv, hgn⟩ := ih
      (fun y hy => hs y (Finset.mem_insert_of_mem hy)) (ε / 2) (by positivity)
    let c := v x - g x
    let t := insert x s
    let i : t := ⟨x, Finset.mem_insert_self _ _⟩
    obtain ⟨h, hh, hhv, hhn, _⟩ := exists_ccmPolarConstrained_finite_point_isolator
      a (fun j : t => (j : ℝ)) Subtype.val_injective i
      (hs x (Finset.mem_insert_self _ _)) (ε / (2 * (‖c‖ + 1))) (by positivity)
    let u := g.combo h h c 0
    have hvect : u.toCCMFormVector = g.toCCMFormVector + c • h.toCCMFormVector := by
      simp [u, CCMComplexSmoothInteriorSource.combo_toCCMFormVector]
    refine ⟨u, ?_, ?_, ?_⟩
    · rw [hvect]
      exact polar_add hg (hh.smul c)
    · intro y hy
      rcases Finset.mem_insert.mp hy with hyx | hys
      · rw [hyx]
        have hhi : h x = 1 := by simpa [i] using hhv i
        simp [u, CCMComplexSmoothInteriorSource.combo_apply, hhi, c]
      · have hhy : h y = 0 := by
          have hne : (⟨y, Finset.mem_insert_of_mem hys⟩ : t) ≠ i := by
            intro he; have he' := congrArg Subtype.val he
            have hyx : y = x := he'
            exact hxs (hyx ▸ hys)
          simpa [hne] using hhv ⟨y, Finset.mem_insert_of_mem hys⟩
        simp [u, CCMComplexSmoothInteriorSource.combo_apply, hhy, hgv y hys]
    · have hsmall : ‖c‖ * ‖h.toCCMFormVector‖ < ε / 2 := by
        have hb := (lt_div_iff₀ (by positivity : 0 < 2 * (‖c‖ + 1))).mp hhn
        nlinarith [norm_nonneg h.toCCMFormVector]
      rw [hvect]
      calc
        ‖g.toCCMFormVector + c • h.toCCMFormVector‖ ≤
            ‖g.toCCMFormVector‖ + ‖c • h.toCCMFormVector‖ := norm_add_le _ _
        _ = ‖g.toCCMFormVector‖ + ‖c‖ * ‖h.toCCMFormVector‖ := by rw [norm_smul]
        _ < ε := by linarith

/-- Prescribed samples coexist with arbitrarily small complete Weil energy. -/
theorem exists_ccmPolarConstrained_finite_interpolant_source_small
    (a : SuzukiPositiveAperture) (s : Finset ℝ) (v : ℝ → ℂ)
    (hs : ∀ x ∈ s, |x| < a.1) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧
      (∀ x ∈ s, g x = v x) ∧ ‖g.toCCMFormVector‖ < ε ∧
      |ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector| < ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
    (continuous_ccmRestrictedWeilSourceQuadratic a).continuousAt ε hε
  obtain ⟨g, hg, hgv, hgn⟩ := exists_ccmPolarConstrained_finite_interpolant_norm_lt
    a s v hs (min ε δ) (lt_min hε hδ)
  refine ⟨g, hg, hgv, hgn.trans_le (min_le_left _ _), ?_⟩
  have hdist : dist g.toCCMFormVector (0 : CCMArchimedeanFormDomain a) < δ := by
    simpa only [dist_zero_right] using hgn.trans_le (min_le_right _ _)
  simpa only [ccmRestrictedWeilSourceQuadratic_zero, dist_zero_right, Real.norm_eq_abs]
    using hd hdist

end RHTower

namespace RHTower

/-- Every finite sampling fibre is form-norm dense in the complete pole-constrained sector. -/
theorem exists_ccmPolarConstrained_sample_preserving_close
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hu : IsPolarConstrained a u) (s : Finset ℝ) (v : ℝ → ℂ)
    (hs : ∀ x ∈ s, |x| < a.1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧
      (∀ x ∈ s, g x = v x) ∧ ‖g.toCCMFormVector - u‖ < ε := by
  obtain ⟨f, hf, hfn⟩ := exists_polarConstrained_smooth_close a u hu
    (half_pos hε)
  obtain ⟨h, hh, hhv, hhn⟩ := exists_ccmPolarConstrained_finite_interpolant_norm_lt
    a s (fun x => v x - f x) hs (ε / 2) (half_pos hε)
  let g := f.combo h h 1 0
  have hvec : g.toCCMFormVector = f.toCCMFormVector + h.toCCMFormVector := by
    simp [g, CCMComplexSmoothInteriorSource.combo_toCCMFormVector]
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [hvec]
    exact polar_add hf hh
  · intro x hx
    simp [g, CCMComplexSmoothInteriorSource.combo_apply, hhv x hx]
  · rw [hvec]
    calc
      ‖f.toCCMFormVector + h.toCCMFormVector - u‖ =
          ‖(f.toCCMFormVector - u) + h.toCCMFormVector‖ := by congr 1; abel
      _ ≤ ‖f.toCCMFormVector - u‖ + ‖h.toCCMFormVector‖ := norm_add_le _ _
      _ < ε := by linarith

/-- Prescribing arbitrary finitely many physical values does not raise the actual
pole-constrained Rayleigh infimum at any aperture. -/
theorem exists_ccmPolarConstrained_sampled_rayleigh_lt
    (a : SuzukiPositiveAperture) (s : Finset ℝ) (v : ℝ → ℂ)
    (hs : ∀ x ∈ s, |x| < a.1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧
      (∀ x ∈ s, g x = v x) ∧
      ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 ∧
      ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector /
        ‖ccmArchimedeanFormToAperture a g.toCCMFormVector‖ ^ 2 <
          ccmRestrictedWeilPolarGroundEnergy a + ε := by
  obtain ⟨f, hf, hfne, hfR⟩ := exists_polarConstrained_smooth_rayleigh_lt a (half_pos hε)
  let u := f.toCCMFormVector
  let R : CCMArchimedeanFormDomain a → ℝ := fun w =>
    ccmRestrictedWeilSourceQuadratic a w / ‖ccmArchimedeanFormToAperture a w‖ ^ 2
  have hnorm0 : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≠ 0 := by
    have := norm_pos_iff.mpr hfne
    positivity
  have hR : ContinuousAt R u := by
    refine ContinuousAt.div (continuous_ccmRestrictedWeilSourceQuadratic a).continuousAt ?_ hnorm0
    exact ((continuous_norm.comp (ccmArchimedeanFormToAperture a).continuous).pow 2).continuousAt
  have hN : ContinuousAt (fun w : CCMArchimedeanFormDomain a =>
      ‖ccmArchimedeanFormToAperture a w‖) u :=
    (continuous_norm.comp (ccmArchimedeanFormToAperture a).continuous).continuousAt
  obtain ⟨δ₁, hδ₁, hR'⟩ := Metric.continuousAt_iff.1 hR (ε / 2) (half_pos hε)
  have hnpos : 0 < ‖ccmArchimedeanFormToAperture a u‖ := norm_pos_iff.mpr hfne
  obtain ⟨δ₂, hδ₂, hN'⟩ := Metric.continuousAt_iff.1 hN
    (‖ccmArchimedeanFormToAperture a u‖) hnpos
  obtain ⟨g, hg, hgv, hclose⟩ := exists_ccmPolarConstrained_sample_preserving_close
    a u hf s v hs (lt_min hδ₁ hδ₂)
  have hdist : dist g.toCCMFormVector u < min δ₁ δ₂ := by
    rw [dist_eq_norm]; exact hclose
  have hgne : ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 := by
    intro h0
    have := hN' (lt_of_lt_of_le hdist (min_le_right _ _))
    rw [Real.dist_eq, h0, norm_zero, zero_sub, abs_neg, abs_of_pos hnpos] at this
    exact lt_irrefl _ this
  refine ⟨g, hg, hgv, hgne, ?_⟩
  have hr := hR' (lt_of_lt_of_le hdist (min_le_left _ _))
  rw [Real.dist_eq] at hr
  have hupper := (abs_lt.mp hr).2
  change R g.toCCMFormVector < _
  change R u < ccmRestrictedWeilPolarGroundEnergy a + ε / 2 at hfR
  linarith

/-- Rayleigh values of exact constrained smooth sources with prescribed physical samples. -/
def ccmSampledPolarRayleighSet (a : SuzukiPositiveAperture) (s : Finset ℝ)
    (v : ℝ → ℂ) : Set ℝ :=
  {r | ∃ g : CCMComplexSmoothInteriorSource a,
    IsPolarConstrained a g.toCCMFormVector ∧ (∀ x ∈ s, g x = v x) ∧
    ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 ∧
    r = ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector /
      ‖ccmArchimedeanFormToAperture a g.toCCMFormVector‖ ^ 2}

/-- Exact ground-energy invariance under arbitrary finite physical sampling constraints. -/
theorem ccmSampledPolarRayleigh_inf_eq (a : SuzukiPositiveAperture) (s : Finset ℝ)
    (v : ℝ → ℂ) (hs : ∀ x ∈ s, |x| < a.1) :
    sInf (ccmSampledPolarRayleighSet a s v) = ccmRestrictedWeilPolarGroundEnergy a := by
  have hfloor : ∀ r ∈ ccmSampledPolarRayleighSet a s v,
      ccmRestrictedWeilPolarGroundEnergy a ≤ r := by
    rintro r ⟨g, hg, _, hgne, rfl⟩
    exact ccmRestrictedWeilPolarGroundEnergy_le_rayleigh a g.toCCMFormVector hg hgne
  have hbdd : BddBelow (ccmSampledPolarRayleighSet a s v) := ⟨_, hfloor⟩
  obtain ⟨g, hg, hgv, hgne, _⟩ := exists_ccmPolarConstrained_sampled_rayleigh_lt
    a s v hs zero_lt_one
  have hne : (ccmSampledPolarRayleighSet a s v).Nonempty :=
    ⟨_, g, hg, hgv, hgne, rfl⟩
  apply le_antisymm
  · by_contra hn
    have hgap : 0 < sInf (ccmSampledPolarRayleighSet a s v) -
        ccmRestrictedWeilPolarGroundEnergy a := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨f, hf, hfv, hfne, hfR⟩ := exists_ccmPolarConstrained_sampled_rayleigh_lt
      a s v hs (half_pos hgap)
    have hle := csInf_le hbdd
      (show ccmRestrictedWeilSourceQuadratic a f.toCCMFormVector /
          ‖ccmArchimedeanFormToAperture a f.toCCMFormVector‖ ^ 2 ∈
          ccmSampledPolarRayleighSet a s v from ⟨f, hf, hfv, hfne, rfl⟩)
    linarith
  · exact le_csInf hne hfloor

end RHTower
