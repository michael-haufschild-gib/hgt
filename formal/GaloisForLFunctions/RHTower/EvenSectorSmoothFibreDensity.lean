import GaloisForLFunctions.RHTower.EvenSectorSmoothApproximation
import GaloisForLFunctions.RHTower.EvenSectorSmoothTraceCorrection

/-!
# Single smooth source density inside every exact arithmetic fibre

Mollification gives a common finite trace support. Positive smooth coordinate
corrections remove the entire defect while their profile and energy tend to
zero. Exact scalarization then produces one source at every stage.
-/

open Complex MeasureTheory Set Finsupp Filter Topology Zeta23
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

def smoothedMixture (c : WeilEvenPolarTestFn →₀ ℝ) (n : ℕ) :
    SmoothEvenPolarTestFn →₀ ℝ := c.mapDomain (fun f => polarSmooth f n)

theorem smoothedMixture_nonneg (c : WeilEvenPolarTestFn →₀ ℝ) (hc : ∀ f,0 ≤ c f)
    (n : ℕ) : ∀ f,0 ≤ smoothedMixture c n f := Finsupp.mapDomain_nonneg hc

theorem smoothedMixture_trace_tendsto (c : WeilEvenPolarTestFn →₀ ℝ) (j : LogIndex) :
    Tendsto (fun n => smoothMixtureTrace (smoothedMixture c n) j)
      atTop (𝓝 (polarMixtureTrace c j)) := by
  classical
  simp only [smoothMixtureTrace,smoothedMixture,linearCombination_mapDomain,polarMixtureTrace]
  simp only [linearCombination_apply,Finsupp.sum,Finsupp.finsetSum_apply,
    Finsupp.smul_apply,smul_eq_mul,Function.comp_def]
  exact tendsto_finsetSum c.support fun f _ => (polarSmooth_trace_tendsto f j).const_mul (c f)

theorem smoothedMixture_energy_tendsto (c : WeilEvenPolarTestFn →₀ ℝ) :
    Tendsto (fun n => smoothMixtureEnergy (smoothedMixture c n))
      atTop (𝓝 (polarMixtureEnergy c)) := by
  classical
  simp only [smoothMixtureEnergy,smoothedMixture,linearCombination_mapDomain,polarMixtureEnergy]
  simp only [linearCombination_apply,Finsupp.sum,smul_eq_mul,Function.comp_def]
  exact tendsto_finsetSum c.support fun f _ => (polarSmooth_energy_tendsto f).const_mul (c f)

theorem smoothedMixture_profile_tendsto (c : WeilEvenPolarTestFn →₀ ℝ) (x : ℝ) :
    Tendsto (fun n => smoothMixtureProfile (smoothedMixture c n) x)
      atTop (𝓝 (realPolarMixtureProfile c x)) := by
  classical
  simp only [smoothMixtureProfile,smoothedMixture,linearCombination_mapDomain,realPolarMixtureProfile]
  simp only [linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,Function.comp_def]
  exact tendsto_finsetSum c.support fun f _ => (tendsto_weilTest_mollify f.1 x).const_smul (c f)

private theorem support_linearCombination_subset {ι : Type*} (c : ι →₀ ℝ)
    (T : ι → LogIndex →₀ ℝ) (s : Finset LogIndex)
    (hs : ∀ f ∈ c.support,(T f).support ⊆ s) :
    (linearCombination ℝ T c).support ⊆ s := by
  classical
  intro j hj
  by_contra hn
  apply (Finsupp.mem_support_iff.mp hj)
  simp only [linearCombination_apply,Finsupp.sum,Finsupp.finsetSum_apply,
    Finsupp.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro f hf
  have hz : T f j=0 := by
    by_contra hh
    exact hn (hs f hf (Finsupp.mem_support_iff.mpr hh))
  rw [hz,mul_zero]

theorem smoothedMixture_common_trace_support (c : WeilEvenPolarTestFn →₀ ℝ) :
    ∃ s : Finset LogIndex,(polarMixtureTrace c).support ⊆ s ∧
      ∀ n,(smoothMixtureTrace (smoothedMixture c n)).support ⊆ s := by
  classical
  choose S hS hSn using polarSmooth_common_trace_support
  let s := c.support.biUnion S
  have hinc (f : WeilEvenPolarTestFn) (hf : f ∈ c.support) : S f ⊆ s := by
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨f,hf,hj⟩
  refine ⟨s,support_linearCombination_subset c _ s (fun f hf => (hS f).trans (hinc f hf)),?_⟩
  intro n
  rw [smoothMixtureTrace,smoothedMixture,linearCombination_mapDomain]
  exact support_linearCombination_subset c _ s (fun f hf => (hSn f n).trans (hinc f hf))

/-- Smooth positive mixtures recover the entire profile and energy while
remaining in the exact original arithmetic fibre at every stage. -/
theorem exists_smooth_mixture_exact_fibre_limit (c : WeilEvenPolarTestFn →₀ ℝ)
    (hc : ∀ f,0 ≤ c f) :
    ∃ d : ℕ → SmoothEvenPolarTestFn →₀ ℝ,
      (∀ n f,0 ≤ d n f) ∧
      (∀ n,smoothMixtureTrace (d n)=polarMixtureTrace c) ∧
      Tendsto (fun n => smoothMixtureEnergy (d n)) atTop (𝓝 (polarMixtureEnergy c)) ∧
      ∀ x,Tendsto (fun n => smoothMixtureProfile (d n) x)
        atTop (𝓝 (realPolarMixtureProfile c x)) := by
  classical
  obtain ⟨s,hcS,hdS⟩ := smoothedMixture_common_trace_support c
  let v : ℕ → LogIndex →₀ ℝ := fun n => polarMixtureTrace c-smoothMixtureTrace (smoothedMixture c n)
  have hvS (n : ℕ) : (v n).support ⊆ s := by
    intro j hj
    by_contra hn
    have hz₁ : polarMixtureTrace c j=0 := by
      by_contra hh
      exact hn (hcS (Finsupp.mem_support_iff.mpr hh))
    have hz₂ : smoothMixtureTrace (smoothedMixture c n) j=0 := by
      by_contra hh
      exact hn (hdS n (Finsupp.mem_support_iff.mpr hh))
    exact (Finsupp.mem_support_iff.mp hj) (by simp [v,hz₁,hz₂])
  have hvt (j : LogIndex) : Tendsto (fun n => v n j) atTop (𝓝 0) := by
    simpa only [v,Finsupp.sub_apply,sub_self] using
      (tendsto_const_nhds (x := polarMixtureTrace c j)).sub (smoothedMixture_trace_tendsto c j)
  let d : ℕ → SmoothEvenPolarTestFn →₀ ℝ :=
    fun n => smoothedMixture c n+smoothTraceRepair s (v n)
  refine ⟨d,fun n f => add_nonneg (smoothedMixture_nonneg c hc n f)
    (smoothTraceRepair_nonneg s (v n) f),?_,?_,?_⟩
  · intro n
    rw [show d n=smoothedMixture c n+smoothTraceRepair s (v n) by rfl,
      map_add,smoothTraceRepair_trace s (v n) (hvS n)]
    dsimp only [v]
    abel
  · have hr := smoothTraceRepair_observable_tendsto smoothMixtureEnergy s v (fun j _ => hvt j)
    simpa only [d,map_add,add_zero] using (smoothedMixture_energy_tendsto c).add hr
  · intro x
    have hr := smoothTraceRepair_observable_tendsto
      (linearCombination ℝ (fun f : SmoothEvenPolarTestFn => EF.weilTest f.1.1.1 f.1.1.1 x))
      s v (fun j _ => hvt j)
    have hr' : Tendsto (fun n => smoothMixtureProfile (smoothTraceRepair s (v n)) x)
        atTop (𝓝 0) := by
      simpa only [smoothMixtureProfile,linearCombination_apply,Finsupp.sum,
        Finset.sum_apply,Pi.smul_apply] using hr
    simpa only [d,map_add,Pi.add_apply,add_zero] using (smoothedMixture_profile_tendsto c x).add hr'

/-- **Exact-fibre single-source density.** Every actual positive C² even-polar
mixture is a profile-and-energy limit of single smooth even-polar sources.
Every integer coordinate is already exact at every stage. -/
theorem exists_single_smooth_exact_fibre_limit (c : WeilEvenPolarTestFn →₀ ℝ)
    (hc : ∀ f,0 ≤ c f) :
    ∃ f : ℕ → SmoothEvenPolarTestFn,
      (∀ n,logVector (f n).1.1=polarMixtureTrace c) ∧
      Tendsto (fun n => weilArchRe (EF.weilTest (f n).1.1.1 (f n).1.1.1))
        atTop (𝓝 (polarMixtureEnergy c)) ∧
      ∀ x,Tendsto (fun n => EF.weilTest (f n).1.1.1 (f n).1.1.1 x)
        atTop (𝓝 (realPolarMixtureProfile c x)) := by
  obtain ⟨d,hd,ht,he,hp⟩ := exists_smooth_mixture_exact_fibre_limit c hc
  choose f hf hft hfe using fun n => exists_smooth_scalarization_moments (d n) (hd n)
  exact ⟨f,fun n => (hft n).trans (ht n),by simpa only [hfe] using he,
    fun x => by simpa only [hf] using hp x⟩

end RHTower.EvenSector
