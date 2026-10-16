import GaloisForLFunctions.RHTower.OddSectorEnergyCompletion
import GaloisForLFunctions.RHTower.EvenSectorBlindVariationalAttainment

/-!
# An actual blind odd minimizer at every aperture

A narrow differentiated even bump proves odd blind feasibility. Closed
quadratic arithmetic constraints, physical compactness, and lower
semicontinuity give an actual unit odd minimizer in the complete form domain.
The same source minimizes against every blind profile obtained by completing
finite positive odd mixtures at fixed aperture and finite energy. No sign of
the minimum, RH, or odd-positive arithmetic source is assumed.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped InnerProduct NNReal ComplexConjugate ContDiff

noncomputable section
namespace RHTower.OddSector
open EvenSector WeilOneSided SeparatedBump

/-- Actual unit odd sources with every integer logarithmic observation zero. -/
def BlindUnitSource (a : SuzukiPositiveAperture) : Type :=
  {u : CCMArchimedeanFormDomain a // ccmArchimedeanFormReflection a u=-u ∧
    ‖ccmArchimedeanFormToAperture a u‖=1 ∧
    energyProfile a (ccmArchimedeanFormToAperture a u) ∈ blindProfiles}

theorem energyProfile_odd {a : SuzukiPositiveAperture} {u : CCMArchimedeanFormDomain a}
    (hu : ccmArchimedeanFormReflection a u=-u) :
    Function.Even (energyProfile a (ccmArchimedeanFormToAperture a u)) := by
  intro h
  have hr : l2Reflection (ccmArchimedeanFormToAperture a u).1=
      -(ccmArchimedeanFormToAperture a u).1 := by
    rw [← ccmArchimedeanFormToAperture_reflection,hu,map_neg,Submodule.coe_neg]
  have hh := inner_logTranslationCLM_reflection h (ccmArchimedeanFormToAperture a u).1
  rw [hr,map_neg,inner_neg_left,inner_neg_right,neg_neg] at hh
  simpa only [energyProfile,ccmApertureCorrelation,neg_neg] using hh

/-- Complex blindness is exactly the original real symmetric odd arithmetic constraint. -/
theorem energyProfile_eq_zero_iff_odd_trace_zero {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u=-u) (h : ℝ) :
    energyProfile a (ccmArchimedeanFormToAperture a u) h=0 ↔
      (energyProfile a (ccmArchimedeanFormToAperture a u) h+
        energyProfile a (ccmArchimedeanFormToAperture a u) (-h)).re=0 := by
  have he := energyProfile_odd hu h
  have hc := energyProfile_neg a (ccmArchimedeanFormToAperture a u) h
  have hi := congrArg Complex.im (hc.symm.trans he)
  simp only [Complex.conj_im] at hi
  rw [he,Complex.add_re]
  constructor
  · intro hz; rw [hz]; simp
  · intro hr
    apply Complex.ext <;> simp only [Complex.zero_re,Complex.zero_im] <;> linarith

/-- Odd blind feasibility is unconditional at every positive aperture. -/
theorem nonempty_blindUnitSource (a : SuzukiPositiveAperture) :
    Nonempty (BlindUnitSource a) := by
  let b := min a.1 (Real.log 2/4)
  have hb : 0<b := lt_min a.2 (by have := Real.log_pos one_lt_two; positivity)
  obtain ⟨j : ℕ,hj⟩ := exists_nat_gt (1/b)
  have hjb : 1<(j : ℝ)*b := (div_lt_iff₀ hb).mp hj
  have hr : 3*(nodeBump j).rOut<b := by
    rw [nodeBump_rOut,mul_one_div]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hra : 3*(nodeBump j).rOut<a.1 := hr.trans_le (min_le_left _ _)
  have hrl : 6*(nodeBump j).rOut<Real.log 2 := by
    have h := min_le_right a.1 (Real.log 2/4)
    dsimp only [b] at hr
    linarith [Real.log_pos one_lt_two]
  let g : ℝ → ℂ := (smoothPolarBump j).1.1.1
  have hg : ContDiff ℝ ∞ g := (smoothPolarBump j).2
  have hgc : HasCompactSupport g := (smoothPolarBump j).1.1.2.2
  have hge : Function.Even g := (smoothPolarBump j).1.2.1
  have hd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hdo : Function.Odd (deriv g) := by
    intro x
    have h := congrArg (fun h : ℝ → ℂ => deriv h x) (funext hge)
    rw [deriv_comp_neg] at h
    linear_combination -h
  have hds : tsupport (deriv g) ⊆
      Icc (-(3*(nodeBump j).rOut)) (3*(nodeBump j).rOut) :=
    tsupport_deriv_subset.trans (smoothPolarBump_tsupport j)
  have hne : ∃ x,deriv g x≠0 := by
    by_contra! hz
    have hc := is_const_of_deriv_eq_zero (hg.differentiable (by simp)) hz 0
      (3*(nodeBump j).rOut+1)
    have hzero : g (3*(nodeBump j).rOut+1)=0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hh := (smoothPolarBump_tsupport j hm).2
      linarith
    have h0 : g 0=1 := smoothPolarBump_zero j
    rw [h0,hzero] at hc
    exact one_ne_zero hc
  let f : InteriorWindowedSmoothOddTestFn a :=
    ⟨⟨⟨⟨deriv g,hd.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top)),
      hgc.deriv⟩,hdo⟩,hd⟩,fun x hx =>
        ⟨by linarith [(hds hx).1],by linarith [(hds hx).2]⟩⟩
  let u := (interiorCCMSource f).toCCMFormVector
  obtain ⟨x,hx⟩ := hne
  have hu : ccmArchimedeanFormToAperture a u≠0 :=
    ccmArchimedeanFormToAperture_toCCMFormVector_ne_zero_of_apply_ne_zero
      (interiorCCMSource f) (x := x) hx
  have hblind : energyProfile a (ccmArchimedeanFormToAperture a u) ∈ blindProfiles := by
    intro n
    rw [energyProfile_interiorCCMSource]
    have hs (x : ℝ) (hx : deriv g x≠0) : |x|≤3*(nodeBump j).rOut :=
      abs_le.mpr (hds (subset_tsupport _ hx))
    have hk := weilTest_support_abs_le hs hs
    have hn : Real.log 2≤Real.log (n : ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast n.2)
    by_contra h
    have hh := hk (Real.log (n : ℕ)) h
    linarith [le_abs_self (Real.log (n : ℕ))]
  let r := ‖ccmArchimedeanFormToAperture a u‖
  have hr0 : 0<r := norm_pos_iff.mpr hu
  let c : ℂ := (r : ℂ)⁻¹
  refine ⟨⟨c • u,?_,?_,?_⟩⟩
  · rw [map_smul,odd_interiorCCMSource,smul_neg]
  · rw [map_smul,norm_smul]
    change ‖(r : ℂ)⁻¹‖*r=1
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,inv_mul_cancel₀ hr0.ne']
  · intro n
    rw [map_smul,energyProfile_smul,hblind n,mul_zero]

theorem isCompact_blindPhysicalBudget (a : SuzukiPositiveAperture) (B : ℝ) :
    IsCompact (physicalOddBudget a B ∩ energyProfile a ⁻¹' blindProfiles) :=
  (isCompact_physicalOddBudget a B).inter_right
    (isClosed_blindProfiles.preimage (continuous_energyProfile a))

/-- Blindness may emerge only in the limit; one actual odd source still realizes it. -/
theorem closure_nativeBlindProfiles_has_source (a : SuzukiPositiveAperture) (B : ℝ) :
    closure (nativeEnergyProfiles a B) ∩ blindProfiles ⊆
      {P | ∃ u : BlindUnitSource a, ccmRestrictedWeilSourceQuadratic a u.1≤B ∧
        energyProfile a (ccmArchimedeanFormToAperture a u.1)=P} := by
  rintro P ⟨hP,hb⟩
  have hc := closure_nativeEnergyProfiles_subset_completed a B hP
  obtain ⟨u,ho,hn,hQ,hu⟩ := (mem_completedEnergyProfiles_iff a B P).mp hc
  exact ⟨⟨u,ho,hn,by rw [hu]; exact hb⟩,hQ,hu⟩

/-- The actual blind odd objective retains its negative pole direction.
Arithmetic terms vanish; no pole cancellation is imposed on the source. -/
theorem sourceQuadratic_blind_eq_gamma_sub_pole {a : SuzukiPositiveAperture}
    (u : BlindUnitSource a) :
    ccmRestrictedWeilSourceQuadratic a u.1=
      (∫ ξ : ℝ,2*gammaHardyPhaseRate (2*Real.pi*ξ)*‖(u.1.1 : ℝ → ℂ) ξ‖^2)-
        2*‖inner ℂ (ccmPolarApertureVector a (1/2))
          (ccmArchimedeanFormToAperture a u.1)‖^2 := by
  have hr : l2Reflection (ccmArchimedeanFormToAperture a u.1).1=
      -(ccmArchimedeanFormToAperture a u.1).1 := by
    rw [← ccmArchimedeanFormToAperture_reflection,u.2.1,map_neg,Submodule.coe_neg]
  have hp : inner ℂ (ccmPolarApertureVector a (-1/2))
      (ccmArchimedeanFormToAperture a u.1)=
      -inner ℂ (ccmPolarApertureVector a (1/2))
        (ccmArchimedeanFormToAperture a u.1) := by
    have hh := inner_ccmPolarL2Vector_reflection a (1/2)
      (ccmArchimedeanFormToAperture a u.1).1
    rw [hr,inner_neg_right] at hh
    simpa only [Submodule.coe_inner,ccmPolarApertureVector_coe,neg_div] using hh.symm
  have hz : ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))),
      (ArithmeticFunction.vonMangoldt n : ℝ)*(1/Real.sqrt n)*
        (inner ℂ (logTranslationCLM (Real.log n) (ccmArchimedeanFormToAperture a u.1).1)
            (ccmArchimedeanFormToAperture a u.1).1+
          inner ℂ (logTranslationCLM (-Real.log n) (ccmArchimedeanFormToAperture a u.1).1)
            (ccmArchimedeanFormToAperture a u.1).1).re=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hm := u.2.2.2 ⟨n,(Finset.mem_Icc.mp hn).1⟩
    have hp := energyProfile_odd u.2.1 (Real.log n)
    rw [hm] at hp
    simp only [energyProfile,ccmApertureCorrelation,neg_neg] at hp hm
    rw [hp,hm]
    simp
  rw [ccmRestrictedWeilSourceQuadratic,hz,hp]
  simp only [map_neg,neg_mul,mul_neg,Complex.add_re,Complex.neg_re,sub_zero]
  rw [mul_comm (conj _) _,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_re]
  ring

/-- **Blind odd attainment.** Every positive aperture has an actual normalized
arithmetic-blind odd minimizer of the complete Weil energy. -/
theorem exists_blind_minimizer (a : SuzukiPositiveAperture) :
    ∃ u : BlindUnitSource a, ∀ v : BlindUnitSource a,
      ccmRestrictedWeilSourceQuadratic a u.1≤ccmRestrictedWeilSourceQuadratic a v.1 := by
  obtain ⟨u₀⟩ := nonempty_blindUnitSource a
  let B := ccmRestrictedWeilSourceQuadratic a u₀.1
  let K := physicalOddBudget a B ∩ energyProfile a ⁻¹' blindProfiles
  have h₀ : ccmArchimedeanFormToAperture a u₀.1 ∈ K := by
    refine ⟨⟨u₀.2.2.1,?_,u₀.1,rfl,le_rfl⟩,u₀.2.2.2⟩
    rw [← ccmArchimedeanFormToAperture_reflection,u₀.2.1,map_neg,Submodule.coe_neg]
  obtain ⟨f,hf,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨_,h₀⟩
    (isCompact_blindPhysicalBudget a B)
    ((lowerSemicontinuous_ccmRestrictedWeilExtendedSourceQuadratic a).lowerSemicontinuousOn K)
  obtain ⟨hn,ho,u,hJ,hQ⟩ := hf.1
  have huo : ccmArchimedeanFormReflection a u=-u := by
    apply ccmArchimedeanFormToAperture_injective a
    apply Subtype.ext
    rw [ccmArchimedeanFormToAperture_reflection,map_neg,hJ,ho,Submodule.coe_neg]
  let w : BlindUnitSource a := ⟨u,huo,by rw [hJ]; exact hn,by rw [hJ]; exact hf.2⟩
  refine ⟨w,fun v => ?_⟩
  change ccmRestrictedWeilSourceQuadratic a u≤_
  by_cases hvB : ccmRestrictedWeilSourceQuadratic a v.1≤B
  · have hvK : ccmArchimedeanFormToAperture a v.1 ∈ K := by
      refine ⟨⟨v.2.2.1,?_,v.1,rfl,hvB⟩,v.2.2.2⟩
      rw [← ccmArchimedeanFormToAperture_reflection,v.2.1,map_neg,Submodule.coe_neg]
    have hh := hmin hvK
    change ccmRestrictedWeilExtendedSourceQuadratic a f≤
      ccmRestrictedWeilExtendedSourceQuadratic a (ccmArchimedeanFormToAperture a v.1) at hh
    rw [← hJ,ccmRestrictedWeilExtendedSourceQuadratic_embedding,
      ccmRestrictedWeilExtendedSourceQuadratic_embedding] at hh
    exact EReal.coe_le_coe_iff.mp hh
  · exact hQ.trans (le_of_not_ge hvB)

/-- **No rank or completion escape in the blind odd problem.** One actual
minimizer controls every blind finite-energy mixture completion at this aperture. -/
theorem exists_blind_minimizer_for_mixture_completion (a : SuzukiPositiveAperture) :
    ∃ u : BlindUnitSource a,
      (∀ v : BlindUnitSource a,
        ccmRestrictedWeilSourceQuadratic a u.1≤ccmRestrictedWeilSourceQuadratic a v.1) ∧
      ∀ B : ℝ, (closure (nativeEnergyProfiles a B) ∩ blindProfiles).Nonempty →
        ccmRestrictedWeilSourceQuadratic a u.1≤B := by
  obtain ⟨u,hu⟩ := exists_blind_minimizer a
  refine ⟨u,hu,fun B ⟨P,hP⟩ => ?_⟩
  obtain ⟨v,hv,-⟩ := closure_nativeBlindProfiles_has_source a B hP
  exact (hu v).trans hv

end RHTower.OddSector
