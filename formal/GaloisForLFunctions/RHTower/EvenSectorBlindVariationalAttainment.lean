import GaloisForLFunctions.RHTower.EvenSectorEnergyCompletion
import GaloisForLFunctions.RHTower.EvenSectorPositiveBlindEnergy

/-!
# An actual normalized blind minimizer at every EWU aperture

The blind constraints are quadratic, not a linear source subspace. They are
nevertheless closed in physical L2. A narrow even polar bump supplies a
nonzero feasible source at every aperture; compact energy sublevels and
lower semicontinuity then produce an actual minimum in the complete form
domain. This proves attainment, without assuming a sign for the minimum.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped InnerProduct NNReal ComplexConjugate

noncomputable section
namespace RHTower.EvenSector
open WeilOneSided SeparatedBump

/-- All integer logarithmic observations vanish, as full complex values. -/
def blindProfiles : Set (ℝ → ℂ) :=
  {P | ∀ n : LogIndex, P (Real.log (n : ℕ)) = 0}

theorem isClosed_blindProfiles : IsClosed blindProfiles := by
  change IsClosed (⋂ n : LogIndex, {P : ℝ → ℂ | P (Real.log (n : ℕ)) = 0})
  exact isClosed_iInter fun n : LogIndex =>
    isClosed_eq (continuous_apply (Real.log (n : ℕ))) continuous_const

/-- Actual unit even polar sources with every arithmetic observation zero. -/
def BlindUnitSource (a : SuzukiPositiveAperture) : Type :=
  {u : CCMArchimedeanFormDomain a // IsPolarConstrained a u ∧ CCMEvenSector.IsEven a u ∧
    ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
    energyProfile a (ccmArchimedeanFormToAperture a u) ∈ blindProfiles}

theorem energyProfile_even {a : SuzukiPositiveAperture} {u : CCMArchimedeanFormDomain a}
    (hu : CCMEvenSector.IsEven a u) :
    Function.Even (energyProfile a (ccmArchimedeanFormToAperture a u)) := by
  intro h
  have hr : l2Reflection (ccmArchimedeanFormToAperture a u).1 =
      (ccmArchimedeanFormToAperture a u).1 := by
    rw [← ccmArchimedeanFormToAperture_reflection, hu]
  have hh := inner_logTranslationCLM_reflection h (ccmArchimedeanFormToAperture a u).1
  rw [hr] at hh
  simpa only [energyProfile, ccmApertureCorrelation, neg_neg] using hh

theorem energyProfile_neg (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (h : ℝ) :
    energyProfile a f (-h) = conj (energyProfile a f h) := by
  simp only [energyProfile, ccmApertureCorrelation, neg_neg]
  rw [inner_logTranslationCLM]
  exact inner_conj_symm _ _

/-- Complex blindness and the original real symmetric arithmetic trace coincide in the even sector. -/
theorem energyProfile_eq_zero_iff_trace_zero {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (hu : CCMEvenSector.IsEven a u) (h : ℝ) :
    energyProfile a (ccmArchimedeanFormToAperture a u) h = 0 ↔
      (energyProfile a (ccmArchimedeanFormToAperture a u) h +
        energyProfile a (ccmArchimedeanFormToAperture a u) (-h)).re = 0 := by
  have he := energyProfile_even hu h
  have hc := energyProfile_neg a (ccmArchimedeanFormToAperture a u) h
  have hi := congrArg Complex.im (hc.symm.trans he)
  simp only [Complex.conj_im] at hi
  rw [he, Complex.add_re]
  constructor
  · intro hz; rw [hz]; simp
  · intro hr
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith

theorem energyProfile_smul (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (c : ℂ) (h : ℝ) :
    energyProfile a (c • f) h = conj c * c * energyProfile a f h := by
  simp only [energyProfile, ccmApertureCorrelation, Submodule.coe_smul,
    map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply]
  ring

/-- Feasibility is unconditional, including arbitrarily small positive apertures. -/
theorem nonempty_blindUnitSource (a : SuzukiPositiveAperture) :
    Nonempty (BlindUnitSource a) := by
  let b := min a.1 (Real.log 2 / 4)
  have hb : 0 < b := lt_min a.2 (by have := Real.log_pos one_lt_two; positivity)
  obtain ⟨j : ℕ, hj⟩ := exists_nat_gt (1 / b)
  have hjb : 1 < (j : ℝ) * b := (div_lt_iff₀ hb).mp hj
  have hr : 3 * (nodeBump j).rOut < b := by
    rw [nodeBump_rOut, mul_one_div]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hra : 3 * (nodeBump j).rOut < a.1 := hr.trans_le (min_le_left _ _)
  have hrl : 6 * (nodeBump j).rOut < Real.log 2 := by
    have h := min_le_right a.1 (Real.log 2 / 4)
    dsimp only [b] at hr
    linarith [Real.log_pos one_lt_two]
  let f : InteriorWindowedSmoothEvenPolarTestFn a :=
    ⟨smoothPolarBump j, fun x hx => by
      have hh := smoothPolarBump_tsupport j hx
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩⟩
  let u := (interiorCCMSource f).toCCMFormVector
  have hu : ccmArchimedeanFormToAperture a u ≠ 0 :=
    ccmArchimedeanFormToAperture_toCCMFormVector_ne_zero_of_apply_ne_zero
      (interiorCCMSource f) (x := 0) (by
        change (smoothPolarBump j).1.1.1 0 ≠ 0
        rw [smoothPolarBump_zero]
        exact one_ne_zero)
  have hblind : energyProfile a (ccmArchimedeanFormToAperture a u) ∈ blindProfiles := by
    intro n
    rw [energyProfile_interiorCCMSource]
    have hs (x : ℝ) (hx : (smoothPolarBump j).1.1.1 x ≠ 0) :
        |x| ≤ 3 * (nodeBump j).rOut :=
      abs_le.mpr (smoothPolarBump_tsupport j (subset_tsupport _ hx))
    have hk := weilTest_support_abs_le hs hs
    have hn : Real.log 2 ≤ Real.log (n : ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast n.2)
    by_contra h
    have hh := hk (Real.log (n : ℕ)) h
    linarith [le_abs_self (Real.log (n : ℕ))]
  let r := ‖ccmArchimedeanFormToAperture a u‖
  have hr0 : 0 < r := norm_pos_iff.mpr hu
  let c : ℂ := (r : ℂ)⁻¹
  refine ⟨⟨c • u, (polar_interiorCCMSource f).smul c,
    (even_interiorCCMSource f).smul a c, ?_, ?_⟩⟩
  · rw [map_smul, norm_smul]
    change ‖(r : ℂ)⁻¹‖ * r = 1
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      inv_mul_cancel₀ hr0.ne']
  · intro n
    rw [map_smul, energyProfile_smul, hblind n, mul_zero]

theorem isCompact_blindPhysicalBudget (a : SuzukiPositiveAperture) (B : ℝ) :
    IsCompact (physicalEvenPolarBudget a B ∩ energyProfile a ⁻¹' blindProfiles) :=
  (isCompact_physicalEvenPolarBudget a B).inter_right
    (isClosed_blindProfiles.preimage (continuous_energyProfile a))

/-- Even a pointwise completion of blind mixtures has an actual single blind source. -/
theorem closure_nativeBlindProfiles_has_source (a : SuzukiPositiveAperture) (B : ℝ) :
    closure (nativeEnergyProfiles a B ∩ blindProfiles) ⊆
      {P | ∃ u : BlindUnitSource a, ccmRestrictedWeilSourceQuadratic a u.1 ≤ B ∧
        energyProfile a (ccmArchimedeanFormToAperture a u.1) = P} := by
  intro P hP
  have hc := closure_nativeEnergyProfiles_subset_completed a B
    (closure_mono inter_subset_left hP)
  obtain ⟨u, hp, he, hn, hQ, hu⟩ := (mem_completedEnergyProfiles_iff a B P).mp hc
  have hb : P ∈ blindProfiles :=
    closure_minimal inter_subset_right isClosed_blindProfiles hP
  exact ⟨⟨u, hp, he, hn, by rw [hu]; exact hb⟩, hQ, hu⟩

/-- On the actual blind polar domain, the optimized energy is exactly the archimedean integral. -/
theorem sourceQuadratic_blind_eq_gamma {a : SuzukiPositiveAperture} (u : BlindUnitSource a) :
    ccmRestrictedWeilSourceQuadratic a u.1 =
      ∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
        ‖(u.1.1 : ℝ → ℂ) ξ‖ ^ 2 := by
  have hp := u.2.1.1
  have hm := u.2.1.2
  simp only [ccmRestrictedWeilSourceQuadratic, hp, hm, map_zero,
    mul_zero, add_zero, Complex.zero_re]
  have hz : ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
        (inner ℂ (logTranslationCLM (Real.log n) (ccmArchimedeanFormToAperture a u.1).1)
            (ccmArchimedeanFormToAperture a u.1).1 +
          inner ℂ (logTranslationCLM (-Real.log n) (ccmArchimedeanFormToAperture a u.1).1)
            (ccmArchimedeanFormToAperture a u.1).1).re = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hminus := u.2.2.2.2 ⟨n, (Finset.mem_Icc.mp hn).1⟩
    have hplus := energyProfile_even u.2.2.1 (Real.log n)
    rw [hminus] at hplus
    simp only [energyProfile, ccmApertureCorrelation, neg_neg] at hplus hminus
    rw [hplus, hminus]
    simp
  rw [hz, sub_zero]

/-- **Blind attainment at every aperture.** The actual complete Weil energy
has a normalized even polar arithmetic-blind minimizer. Neither RH nor blind
positivity nor a pre-existing feasible-source premise is used. -/
theorem exists_blind_minimizer (a : SuzukiPositiveAperture) :
    ∃ u : BlindUnitSource a, ∀ v : BlindUnitSource a,
      ccmRestrictedWeilSourceQuadratic a u.1 ≤ ccmRestrictedWeilSourceQuadratic a v.1 := by
  obtain ⟨u₀⟩ := nonempty_blindUnitSource a
  let B := ccmRestrictedWeilSourceQuadratic a u₀.1
  let K := physicalEvenPolarBudget a B ∩ energyProfile a ⁻¹' blindProfiles
  have h₀ : ccmArchimedeanFormToAperture a u₀.1 ∈ K := by
    refine ⟨⟨u₀.2.2.2.1, ?_, u₀.2.1.1, u₀.2.1.2, u₀.1, rfl, le_rfl⟩, u₀.2.2.2.2⟩
    rw [← ccmArchimedeanFormToAperture_reflection, u₀.2.2.1]
  obtain ⟨f, hf, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨_, h₀⟩
    (isCompact_blindPhysicalBudget a B)
    ((lowerSemicontinuous_ccmRestrictedWeilExtendedSourceQuadratic a).lowerSemicontinuousOn K)
  obtain ⟨hn, he, hp, hm, u, hJ, hQ⟩ := hf.1
  have hue : CCMEvenSector.IsEven a u := by
    apply ccmArchimedeanFormToAperture_injective a
    apply Subtype.ext
    rw [ccmArchimedeanFormToAperture_reflection, hJ, he]
  let w : BlindUnitSource a := ⟨u, by
    refine ⟨?_, hue, ?_, ?_⟩
    · exact ⟨by simpa only [hJ] using hp,
        by simpa only [hJ] using hm⟩
    · rw [hJ]; exact hn
    · rw [hJ]; exact hf.2⟩
  refine ⟨w, fun v => ?_⟩
  change ccmRestrictedWeilSourceQuadratic a u ≤ _
  by_cases hvB : ccmRestrictedWeilSourceQuadratic a v.1 ≤ B
  · have hvK : ccmArchimedeanFormToAperture a v.1 ∈ K := by
      refine ⟨⟨v.2.2.2.1, ?_, v.2.1.1, v.2.1.2, v.1, rfl, hvB⟩, v.2.2.2.2⟩
      rw [← ccmArchimedeanFormToAperture_reflection, v.2.2.1]
    have hh := hmin hvK
    change ccmRestrictedWeilExtendedSourceQuadratic a f ≤
      ccmRestrictedWeilExtendedSourceQuadratic a (ccmArchimedeanFormToAperture a v.1) at hh
    rw [← hJ, ccmRestrictedWeilExtendedSourceQuadratic_embedding,
      ccmRestrictedWeilExtendedSourceQuadratic_embedding] at hh
    exact EReal.coe_le_coe_iff.mp hh
  · exact hQ.trans (le_of_not_ge hvB)

end RHTower.EvenSector
