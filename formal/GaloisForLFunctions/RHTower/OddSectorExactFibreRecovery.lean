import GaloisForLFunctions.RHTower.OddSectorSmoothFormDensity
import GaloisForLFunctions.RHTower.OddSectorBlindVariationalAttainment

/-!
# Exact arithmetic-fibre recovery by one smooth odd source

At every fixed positive aperture, every complete odd source has smooth
strict-interior approximants in its exact arithmetic fibre. Each approximant
is one source, not a mixed state. The whole autocorrelation and literal Weil
energy converge together. Normalization preserves exact blindness, giving
smooth blind unit recovery of every complete blind unit source.
-/

open Complex MeasureTheory Set Finsupp Filter Topology Zeta23
noncomputable section
namespace RHTower.OddSector
open EvenSector WeilOneSided

def profileObservable (a : SuzukiPositiveAperture) (x : ℝ) :
    (InteriorWindowedSmoothOddTestFn a →₀ ℝ) →ₗ[ℝ] ℂ where
  toFun c := mixtureProfile a c x
  map_add' c d := by simp only [map_add,Pi.add_apply]
  map_smul' r c := by simp only [map_smul,Pi.smul_apply,RingHom.id_apply]

/-- **Exact fibre recovery.** No aperture enlargement or arithmetic defect is
needed to recover any complete odd source by single smooth odd sources. -/
theorem exists_exact_fibre_recovery (a : SuzukiPositiveAperture) (u : OddFormSource a) :
    ∃ f : ℕ → InteriorWindowedSmoothOddTestFn a,
      (∀ n,interiorTrace (f n) = formTrace u) ∧
      (∀ x,Tendsto (fun n => interiorProfile (f n) x) atTop (𝓝 (formProfile u x))) ∧
      Tendsto (fun n => interiorEnergy (f n)) atTop (𝓝 (formEnergy u)) := by
  classical
  obtain ⟨g,hP,hE⟩ := exists_interior_odd_observable_approximation a u
  let v (n : ℕ) := formTrace u - interiorTrace (g n)
  have hvs (n : ℕ) : (v n).support ⊆ apertureNodes a := by
    intro j hj
    by_contra hn
    have h₁ : formTrace u j = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hn (formTrace_support_subset u h))
    have h₂ : interiorTrace (g n) j = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hn (interiorTrace_support_subset (g n) h))
    exact Finsupp.mem_support_iff.mp hj (by simp only [v,Finsupp.sub_apply,h₁,h₂,sub_zero])
  have hv (j : LogIndex) : Tendsto (fun n => v n j) atTop (𝓝 0) := by
    simpa only [v,Finsupp.sub_apply,formTrace_apply,sub_self] using
      (tendsto_const_nhds (x := formLogValue u j)).sub
        (trace_tendsto_of_profile_tendsto u g hP j)
  let c (n : ℕ) := Finsupp.single (g n) (1 : ℝ) + traceRepair a (v n)
  have hc (n : ℕ) (f : InteriorWindowedSmoothOddTestFn a) : 0 ≤ c n f := by
    change 0 ≤ Finsupp.single (g n) (1 : ℝ) f + traceRepair a (v n) f
    apply add_nonneg _ (traceRepair_nonneg a (v n) f)
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  choose f hfP hfT hfE using fun n => exists_interior_purification_moments a (c n) (hc n)
  refine ⟨f,?_,?_,?_⟩
  · intro n
    rw [hfT]
    dsimp only [c]
    rw [map_add,mixtureTrace,linearCombination_single,one_smul]
    change interiorTrace (g n) + mixtureTrace a (traceRepair a (v n)) = formTrace u
    rw [traceRepair_trace a (v n) (hvs n)]
    dsimp only [v]
    abel
  · intro x
    have ht := traceRepair_observable_tendsto a (profileObservable a x) v hv
    change Tendsto (fun n => mixtureProfile a (traceRepair a (v n)) x) atTop (𝓝 0) at ht
    have h := (hP x).add ht
    simpa only [hfP,c,map_add,mixtureProfile,linearCombination_single,one_smul,
      Pi.add_apply,add_zero] using h
  · have ht := traceRepair_observable_tendsto a (mixtureEnergy a) v hv
    have h := hE.add ht
    simpa only [hfE,c,map_add,mixtureEnergy,linearCombination_single,one_smul,add_zero] using h

theorem interiorProfile_blind_of_trace_zero {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) (hf : interiorTrace f = 0) :
    interiorProfile f ∈ blindProfiles := by
  intro j
  change EF.weilTest f.1.1.1.1 f.1.1.1.1 (Real.log j) = 0
  rw [← energyProfile_interiorCCMSource]
  apply (energyProfile_eq_zero_iff_odd_trace_zero (odd_interiorCCMSource f) _).2
  rw [energyProfile_interiorCCMSource]
  have ht := congrArg (fun v : LogIndex →₀ ℝ => v j) hf
  change (interiorProfile f (Real.log j)+interiorProfile f (-Real.log j)).re/Real.sqrt j = 0 at ht
  have hs : Real.sqrt (j : ℕ) ≠ 0 := ne_of_gt
    (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < j.1 by omega)))
  exact (div_eq_zero_iff.mp ht).resolve_right hs

def SmoothBlindUnitSource (a : SuzukiPositiveAperture) : Type :=
  {f : InteriorWindowedSmoothOddTestFn a // interiorTrace f = 0 ∧
    ‖ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector‖ = 1}

def SmoothBlindUnitSource.toBlindUnitSource {a : SuzukiPositiveAperture}
    (f : SmoothBlindUnitSource a) : BlindUnitSource a :=
  ⟨(interiorCCMSource f.1).toCCMFormVector,odd_interiorCCMSource f.1,f.2.2,by
    rw [energyProfile_interiorCCMSource]
    exact interiorProfile_blind_of_trace_zero f.1 f.2.1⟩

private theorem exists_mass_normalization {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) (hT : interiorTrace f = 0)
    (hM : 0 < (interiorProfile f 0).re) :
    ∃ g : SmoothBlindUnitSource a,
      interiorProfile g.1 = (interiorProfile f 0).re⁻¹ • interiorProfile f ∧
      interiorEnergy g.1 = (interiorProfile f 0).re⁻¹ * interiorEnergy f := by
  classical
  let r := (interiorProfile f 0).re⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr hM.le
  obtain ⟨g,hP,hTg,hE⟩ := exists_interior_purification_moments a (Finsupp.single f r)
    (fun k => by
      simp only [Finsupp.single_apply]
      split_ifs <;> first | exact hr | exact le_rfl)
  have hp : interiorProfile g = r • interiorProfile f := by
    simpa only [mixtureProfile,linearCombination_single] using hP
  have ht : interiorTrace g = 0 := by
    simpa only [mixtureTrace,linearCombination_single,hT,smul_zero] using hTg
  have hn : ‖ccmArchimedeanFormToAperture a (interiorCCMSource g).toCCMFormVector‖ = 1 := by
    have hm : (interiorProfile g 0).re = 1 := by
      rw [hp,Pi.smul_apply,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      exact inv_mul_cancel₀ hM.ne'
    have hz := congrArg (fun P : ℝ → ℂ => (P 0).re) (energyProfile_interiorCCMSource g)
    rw [energyProfile_zero,Complex.ofReal_re] at hz
    change ‖ccmArchimedeanFormToAperture a (interiorCCMSource g).toCCMFormVector‖^2 =
      (interiorProfile g 0).re at hz
    rw [hm] at hz
    nlinarith [norm_nonneg (ccmArchimedeanFormToAperture a (interiorCCMSource g).toCCMFormVector)]
  refine ⟨⟨g,ht,hn⟩,hp,?_⟩
  simpa only [mixtureEnergy,linearCombination_single,smul_eq_mul] using hE

/-- **Normalized exact blind recovery.** Every complete blind odd unit source
is recovered by smooth blind odd unit sources at the identical aperture. -/
theorem exists_smooth_blind_unit_recovery (a : SuzukiPositiveAperture) (u : BlindUnitSource a) :
    ∃ f : ℕ → SmoothBlindUnitSource a,
      (∀ x,Tendsto (fun n => interiorProfile (f n).1 x) atTop
        (𝓝 (energyProfile a (ccmArchimedeanFormToAperture a u.1) x))) ∧
      Tendsto (fun n => interiorEnergy (f n).1) atTop
        (𝓝 (ccmRestrictedWeilSourceQuadratic a u.1)) := by
  let w : OddFormSource a := ⟨u.1,u.2.1⟩
  obtain ⟨f,hT,hP,hE⟩ := exists_exact_fibre_recovery a w
  have hw : formTrace w = 0 := by
    ext j
    change (formProfile w (Real.log j)+formProfile w (-Real.log j)).re/Real.sqrt j = 0
    change (energyProfile a (ccmArchimedeanFormToAperture a u.1) (Real.log j)+
      energyProfile a (ccmArchimedeanFormToAperture a u.1) (-Real.log j)).re/Real.sqrt j = 0
    rw [energyProfile_odd u.2.1,u.2.2.2 j]
    simp
  have hM : Tendsto (fun n => (interiorProfile (f n) 0).re) atTop (𝓝 (1 : ℝ)) := by
    have h := (Complex.continuous_re.tendsto _).comp (hP 0)
    simpa only [Function.comp_def,formProfile,w,energyProfile_zero,u.2.2.1,one_pow,
      Complex.ofReal_re] using h
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hM).1 0 zero_lt_one)
  choose g hgP hgE using fun n : ℕ => exists_mass_normalization (f (n+N))
    ((hT (n+N)).trans hw) (hN (n+N) (Nat.le_add_left N n))
  have hshift : Tendsto (fun n : ℕ => n+N) atTop atTop := tendsto_add_atTop_nat N
  have hi : Tendsto (fun n => (interiorProfile (f (n+N)) 0).re⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def,inv_one] using (hM.comp hshift).inv₀ one_ne_zero
  refine ⟨g,?_,?_⟩
  · intro x
    have h := hi.smul ((hP x).comp hshift)
    simpa only [Function.comp_def,hgP,Pi.smul_apply,one_smul,formProfile,w] using h
  · have h := hi.mul (hE.comp hshift)
    simpa only [Function.comp_def,hgE,one_mul,formEnergy,w] using h

/-- The attained complete minimum is approached by normalized single smooth
odd sources satisfying every arithmetic constraint exactly. -/
theorem exists_blind_minimizer_with_smooth_recovery (a : SuzukiPositiveAperture) :
    ∃ u : BlindUnitSource a,
      (∀ v : BlindUnitSource a,
        ccmRestrictedWeilSourceQuadratic a u.1 ≤ ccmRestrictedWeilSourceQuadratic a v.1) ∧
      ∃ f : ℕ → SmoothBlindUnitSource a,
        (∀ x,Tendsto (fun n => interiorProfile (f n).1 x) atTop
          (𝓝 (energyProfile a (ccmArchimedeanFormToAperture a u.1) x))) ∧
        Tendsto (fun n => interiorEnergy (f n).1) atTop
          (𝓝 (ccmRestrictedWeilSourceQuadratic a u.1)) := by
  obtain ⟨u,hu⟩ := exists_blind_minimizer a
  exact ⟨u,hu,exists_smooth_blind_unit_recovery a u⟩

/-- **No relaxation gap.** The smooth blind unit infimum equals an attained
complete blind odd minimum at every positive aperture. -/
theorem exists_blind_minimizer_without_relaxation_gap (a : SuzukiPositiveAperture) :
    ∃ u : BlindUnitSource a,
      (∀ v : BlindUnitSource a,
        ccmRestrictedWeilSourceQuadratic a u.1 ≤ ccmRestrictedWeilSourceQuadratic a v.1) ∧
      sInf (Set.range (fun f : SmoothBlindUnitSource a => interiorEnergy f.1)) =
        ccmRestrictedWeilSourceQuadratic a u.1 := by
  obtain ⟨u,hu,f,-,hE⟩ := exists_blind_minimizer_with_smooth_recovery a
  have hlo (g : SmoothBlindUnitSource a) :
      ccmRestrictedWeilSourceQuadratic a u.1 ≤ interiorEnergy g.1 := by
    have h := hu g.toBlindUnitSource
    simpa only [SmoothBlindUnitSource.toBlindUnitSource,sourceEnergy_interiorCCMSource,
      interiorEnergy,interiorProfile] using h
  have hb : BddBelow (Set.range (fun f : SmoothBlindUnitSource a => interiorEnergy f.1)) :=
    ⟨ccmRestrictedWeilSourceQuadratic a u.1,by rintro _ ⟨g,rfl⟩; exact hlo g⟩
  have hn : (Set.range (fun f : SmoothBlindUnitSource a => interiorEnergy f.1)).Nonempty :=
    ⟨interiorEnergy (f 0).1,f 0,rfl⟩
  refine ⟨u,hu,le_antisymm ?_ ?_⟩
  · exact ge_of_tendsto hE (Eventually.of_forall fun n => csInf_le hb ⟨f n,rfl⟩)
  · exact le_csInf hn (by rintro _ ⟨g,rfl⟩; exact hlo g)

end RHTower.OddSector
