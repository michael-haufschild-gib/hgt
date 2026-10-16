import GaloisForLFunctions.RHTower.EvenSectorSmoothFibreDensity

/-!
# Actual single-source completion of arithmetic energy fibres

Every whole integer trace is realized by a single smooth even pole-free
source. In every such exact fibre, the single smooth source energy epigraph
has the same closure as the full C² positive-mixture epigraph.
-/

open MeasureTheory Set Finsupp Filter Topology Zeta23
open scoped NNReal
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

def nonnegativeRealCoefficients {ι : Type*} (c : ι →₀ ℝ≥0) : ι →₀ ℝ :=
  c.mapRange (fun r => (r : ℝ)) NNReal.coe_zero

theorem nonnegativeRealCoefficients_nonneg {ι : Type*} (c : ι →₀ ℝ≥0) (i : ι) :
    0 ≤ nonnegativeRealCoefficients c i := (c i).coe_nonneg

/-- **Unconditional exact-fibre density.** The input is an actual finite
nonnegative-weighted family. Single smooth sources recover its entire
autocorrelation and energy in the limit, with all integer samples exact. -/
theorem smooth_single_source_exact_fibre_density (c : WeilEvenPolarTestFn →₀ ℝ≥0) :
    ∃ f : ℕ → SmoothEvenPolarTestFn,
      (∀ n,logVector (f n).1.1=polarMixtureTrace (nonnegativeRealCoefficients c)) ∧
      Tendsto (fun n => weilArchRe (EF.weilTest (f n).1.1.1 (f n).1.1.1))
        atTop (𝓝 (polarMixtureEnergy (nonnegativeRealCoefficients c))) ∧
      ∀ x,Tendsto (fun n => EF.weilTest (f n).1.1.1 (f n).1.1.1 x)
        atTop (𝓝 (realPolarMixtureProfile (nonnegativeRealCoefficients c) x)) :=
  exists_single_smooth_exact_fibre_limit _ (nonnegativeRealCoefficients_nonneg c)

/-- Every finitely supported whole arithmetic trace has a single smooth
compact even pole-free source realization. -/
theorem exists_single_smooth_trace (v : LogIndex →₀ ℝ) :
    ∃ f : SmoothEvenPolarTestFn,logVector f.1.1=v := by
  obtain ⟨c,hc,ht⟩ := exists_evenPolar_mixture_trace v
  obtain ⟨f,hf,_,_⟩ := exists_single_smooth_exact_fibre_limit c hc
  exact ⟨f 0,(hf 0).trans ht⟩

theorem exists_single_smooth_fibre_recovery (c : WeilTestFn →₀ ℝ) (hc : ∀ f,0 ≤ c f)
    {ε : ℝ} (hε : 0<ε) :
    ∃ f : SmoothEvenPolarTestFn,
      logVector f.1.1=linearCombination ℝ logVector c ∧
      weilArchRe (EF.weilTest f.1.1.1 f.1.1.1)<fullMixtureEnergy c+ε := by
  obtain ⟨d,hd,ht,he⟩ := exists_evenPolar_exact_fibre_recovery c hc (half_pos hε)
  obtain ⟨f,hf,hE,_⟩ := exists_single_smooth_exact_fibre_limit d hd
  have hlt := hE.eventually (gt_mem_nhds (show polarMixtureEnergy d<polarMixtureEnergy d+ε/2 by linarith))
  obtain ⟨n,hn⟩ := hlt.exists
  exact ⟨f n,(hf n).trans ht,by linarith⟩

/-- Full C² positive mixtures admit actual single smooth even-polar recovery
in their exact whole arithmetic fibre. No source-positivity premise occurs. -/
theorem full_mixture_single_smooth_recovery (c : WeilTestFn →₀ ℝ≥0) :
    ∃ f : ℕ → SmoothEvenPolarTestFn,∀ n,
      logVector (f n).1.1=linearCombination ℝ logVector (nonnegativeRealCoefficients c) ∧
      weilArchRe (EF.weilTest (f n).1.1.1 (f n).1.1.1)<
        fullMixtureEnergy (nonnegativeRealCoefficients c)+1/((n : ℝ)+1) := by
  choose f hf using fun n => exists_single_smooth_fibre_recovery
    (nonnegativeRealCoefficients c) (nonnegativeRealCoefficients_nonneg c) (invSucc_pos n)
  exact ⟨f,hf⟩

/-- The energy epigraph of actual single smooth even-polar sources in one
exact whole arithmetic fibre. -/
def singleSmoothEnergyEpigraph (v : LogIndex →₀ ℝ) : Set ℝ :=
  {r | ∃ f : SmoothEvenPolarTestFn,logVector f.1.1=v ∧
    weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) ≤ r}

/-- **Single-source fibre completion.** Convexification, arbitrary C²
regularity, and removal of the even-polar restriction do not enlarge any
closed arithmetic energy epigraph. -/
theorem singleSmooth_energy_fibre_closure_eq (v : LogIndex →₀ ℝ) :
    closure (singleSmoothEnergyEpigraph v)=closure (fullEnergyEpigraph v) := by
  classical
  apply le_antisymm
  · apply closure_mono
    rintro r ⟨f,ht,he⟩
    refine ⟨Finsupp.single f.1.1 1,?_,?_,?_⟩
    · intro g
      simp only [Finsupp.single_apply]
      split_ifs <;> norm_num
    · simpa only [linearCombination_single,one_smul] using ht
    · simpa only [fullMixtureEnergy,linearCombination_single,one_smul] using he
  · apply closure_minimal _ isClosed_closure
    rintro r ⟨c,hc,ht,he⟩
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨f,hf,hE⟩ := exists_single_smooth_fibre_recovery c hc (half_pos hε)
    refine ⟨r+ε/2,⟨f,hf.trans ht,by linarith⟩,?_⟩
    rw [Real.dist_eq,show r-(r+ε/2)=-(ε/2) by ring,abs_neg,abs_of_pos (half_pos hε)]
    linarith

end RHTower.EvenSector
