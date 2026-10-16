import GaloisForLFunctions.RHTower.OddSectorExactFibreRecovery

/-!
# Exact arithmetic multipliers for the blind odd minimum

Positive odd mixtures purify inside the same aperture. Consequently the
attained blind minimum supplies the null-cone condition for finite arithmetic
separation. Exact-fibre recovery extends the resulting multipliers to the
whole odd form domain, with no measurement tolerance or positivity premise.
-/

open Complex MeasureTheory Set Finsupp Filter Topology
open scoped InnerProduct
noncomputable section
namespace RHTower.OddSector
open EvenSector WeilOneSided

def blindMinimizer (a : SuzukiPositiveAperture) : BlindUnitSource a :=
  Classical.choose (exists_blind_minimizer a)

def blindMinimum (a : SuzukiPositiveAperture) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a (blindMinimizer a).1

theorem blindMinimum_le (a : SuzukiPositiveAperture) (u : BlindUnitSource a) :
    blindMinimum a ≤ ccmRestrictedWeilSourceQuadratic a u.1 :=
  Classical.choose_spec (exists_blind_minimizer a) u

theorem blindMinimum_mul_mass_le {a : SuzukiPositiveAperture} (u : OddFormSource a)
    (hb : formProfile u ∈ blindProfiles) :
    blindMinimum a * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 ≤ formEnergy u := by
  by_cases hz : ccmArchimedeanFormToAperture a u.1 = 0
  · have hu : u.1 = 0 := ccmArchimedeanFormToAperture_injective a (by rw [hz,map_zero])
    simp [formEnergy,hu,ccmRestrictedWeilSourceQuadratic_zero]
  have hr : 0 < ‖ccmArchimedeanFormToAperture a u.1‖ := norm_pos_iff.mpr hz
  let c : ℂ := (‖ccmArchimedeanFormToAperture a u.1‖ : ℂ)⁻¹
  let v : BlindUnitSource a := ⟨c • u.1,by rw [map_smul,u.2,smul_neg],by
    rw [map_smul,norm_smul]
    simp only [c,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      inv_mul_cancel₀ hr.ne'],by
    intro j
    rw [map_smul,energyProfile_smul]
    change _ * formProfile u (Real.log j) = 0
    rw [hb j,mul_zero]⟩
  have hm := blindMinimum_le a v
  change blindMinimum a ≤ ccmRestrictedWeilSourceQuadratic a (c • u.1) at hm
  rw [ccmRestrictedWeilSourceQuadratic_smul] at hm
  have hdiv : blindMinimum a ≤
      formEnergy u / ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 := by
    simpa only [c,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      inv_pow,div_eq_mul_inv,mul_comm,formEnergy] using hm
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mp hdiv

def interiorMass {a : SuzukiPositiveAperture} (f : InteriorWindowedSmoothOddTestFn a) : ℝ :=
  (interiorProfile f 0).re

theorem interiorMass_eq_norm_sq {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) :
    interiorMass f = ‖ccmArchimedeanFormToAperture a
      (interiorCCMSource f).toCCMFormVector‖ ^ 2 := by
  rw [interiorMass,show interiorProfile f =
    energyProfile a (ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector)
      from (energyProfile_interiorCCMSource f).symm,energyProfile_zero,Complex.ofReal_re]

def activeInteriorTrace {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) : apertureNodes a →₀ ℝ :=
  (interiorTrace f).subtypeDomain (· ∈ apertureNodes a)

private theorem activeInteriorTrace_purification {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) (c : InteriorWindowedSmoothOddTestFn a →₀ ℝ)
    (hf : interiorTrace f = mixtureTrace a c) :
    activeInteriorTrace f = linearCombination ℝ activeInteriorTrace c := by
  change (lsubtypeDomain (apertureNodes a : Set LogIndex) :
    (LogIndex →₀ ℝ) →ₗ[ℝ] (apertureNodes a →₀ ℝ)) (interiorTrace f) = _
  rw [hf]
  exact apply_linearCombination ℝ _ interiorTrace c

private theorem interiorMass_purification {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) (c : InteriorWindowedSmoothOddTestFn a →₀ ℝ)
    (hf : interiorProfile f = mixtureProfile a c) :
    interiorMass f = linearCombination ℝ interiorMass c := by
  simp only [interiorMass,hf,mixtureProfile,linearCombination_apply,Finsupp.sum,
    Finset.sum_apply,Pi.smul_apply,Complex.real_smul,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,smul_eq_mul]

private theorem blind_residual_nonneg_on_null_cone (a : SuzukiPositiveAperture)
    (c : InteriorWindowedSmoothOddTestFn a →₀ ℝ) (hc : ∀ f,0 ≤ c f)
    (ht : linearCombination ℝ activeInteriorTrace c = 0) :
    0 ≤ linearCombination ℝ
      (fun f : InteriorWindowedSmoothOddTestFn a => interiorEnergy f - blindMinimum a * interiorMass f) c := by
  obtain ⟨f,hP,hT,hE⟩ := exists_interior_purification_moments a c hc
  have ha : activeInteriorTrace f = 0 := (activeInteriorTrace_purification f c hT).trans ht
  have hz : interiorTrace f = 0 :=
    (Finsupp.subtypeDomain_eq_zero_iff (fun _ hj => interiorTrace_support_subset f hj)).mp ha
  let u : OddFormSource a := ⟨(interiorCCMSource f).toCCMFormVector,odd_interiorCCMSource f⟩
  have hb : formProfile u ∈ blindProfiles := by
    rw [formProfile,energyProfile_interiorCCMSource]
    exact interiorProfile_blind_of_trace_zero f hz
  have hm := blindMinimum_mul_mass_le u hb
  change blindMinimum a * ‖ccmArchimedeanFormToAperture a
    (interiorCCMSource f).toCCMFormVector‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a (interiorCCMSource f).toCCMFormVector at hm
  rw [sourceEnergy_interiorCCMSource,← interiorMass_eq_norm_sq] at hm
  change blindMinimum a * interiorMass f ≤ interiorEnergy f at hm
  rw [hE,interiorMass_purification f c hP] at hm
  have hn := sub_nonneg.mpr hm
  simpa only [mixtureEnergy,linearCombination_apply,Finsupp.sum,smul_eq_mul,
    mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_left_comm] using hn

/-- Finite exact multipliers exist at the attained blind minimum, including at zero tolerance. -/
theorem exists_exact_interior_multiplier (a : SuzukiPositiveAperture) :
    ∃ lam : apertureNodes a → ℝ, ∀ f : InteriorWindowedSmoothOddTestFn a,
      (∑ j,lam j * interiorTrace f j.1) ≤ interiorEnergy f - blindMinimum a * interiorMass f := by
  classical
  have hsign (j : apertureNodes a) := exists_interior_signed_coordinates a j.1
    ((mem_apertureNodes a j.1).mp j.2)
  obtain ⟨lam,hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
    (activeInteriorTrace (a := a)) (fun f => interiorEnergy f - blindMinimum a * interiorMass f)
    (fun j => by
      obtain ⟨p,m,kp,km,-,hm,-,hT⟩ := hsign j
      refine ⟨m,km,hm,?_⟩
      change Finsupp.subtypeDomain _ (logVector m.1.1.1) = _
      rw [hT]
      ext k
      simp only [Finsupp.subtypeDomain_apply,Finsupp.single_apply]
      rw [show j.1 = k.1 ↔ j = k from ⟨Subtype.ext,congrArg Subtype.val⟩])
    (fun j => by
      obtain ⟨p,m,kp,km,hp,-,hT,-⟩ := hsign j
      refine ⟨p,kp,hp,?_⟩
      change Finsupp.subtypeDomain _ (logVector p.1.1.1) = _
      rw [hT]
      ext k
      simp only [Finsupp.subtypeDomain_apply,Finsupp.single_apply]
      rw [show j.1 = k.1 ↔ j = k from ⟨Subtype.ext,congrArg Subtype.val⟩])
    (blind_residual_nonneg_on_null_cone a)
  refine ⟨lam,fun f => ?_⟩
  have h := hlam f
  rw [linearCombination_apply,
    Finsupp.sum_fintype _ (fun j t => t • lam j) (fun j => by simp)] at h
  simpa only [activeInteriorTrace,Finsupp.subtypeDomain_apply,smul_eq_mul,mul_comm] using h

/-- The exact same finite multipliers act on every complete odd source. -/
theorem exists_exact_form_multiplier (a : SuzukiPositiveAperture) :
    ∃ lam : apertureNodes a → ℝ, ∀ u : OddFormSource a,
      (∑ j,lam j * formTrace u j.1) +
        blindMinimum a * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 ≤ formEnergy u := by
  obtain ⟨lam,hlam⟩ := exists_exact_interior_multiplier a
  refine ⟨lam,fun u => ?_⟩
  obtain ⟨f,hT,hP,hE⟩ := exists_exact_fibre_recovery a u
  have hM : Tendsto (fun n => interiorMass (f n)) atTop
      (𝓝 (‖ccmArchimedeanFormToAperture a u.1‖ ^ 2)) := by
    have h := (Complex.continuous_re.tendsto _).comp (hP 0)
    simpa only [Function.comp_def,interiorMass,formProfile,energyProfile_zero,
      Complex.ofReal_re] using h
  have hn : ∀ n, (∑ j,lam j * formTrace u j.1) ≤
      interiorEnergy (f n) - blindMinimum a * interiorMass (f n) := by
    intro n
    simpa only [hT n] using hlam (f n)
  have h := ge_of_tendsto (hE.sub (tendsto_const_nhds.mul hM)) (Filter.Eventually.of_forall hn)
  linarith

/-- One finite arithmetic correction selected for each aperture. -/
def blindMultiplier (a : SuzukiPositiveAperture) : apertureNodes a → ℝ :=
  Classical.choose (exists_exact_form_multiplier a)

theorem blindMultiplier_spec (a : SuzukiPositiveAperture) (u : OddFormSource a) :
    (∑ j,blindMultiplier a j * formTrace u j.1) +
      blindMinimum a * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 ≤ formEnergy u :=
  Classical.choose_spec (exists_exact_form_multiplier a) u

end RHTower.OddSector
