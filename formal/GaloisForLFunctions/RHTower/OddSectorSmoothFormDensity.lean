import GaloisForLFunctions.RHTower.OddSectorInteriorTraceRepair
import GaloisForLFunctions.RHTower.CCMParityTopLayerOddFloor

/-!+# Smooth odd approximation in the complete form domain

Odd symmetrization preserves the strict aperture and converges in the form
norm. Consequently both the whole autocorrelation and the literal Weil
energy converge. Arithmetic traces of complete odd sources have the same
finite active set as their smooth approximants, including at the diameter.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ContDiff
noncomputable section
namespace RHTower.OddSector
open EvenSector WeilOneSided

def OddFormSource (a : SuzukiPositiveAperture) : Type :=
  {u : CCMArchimedeanFormDomain a // ccmArchimedeanFormReflection a u = -u}

def oddInteriorSource {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a) :
    InteriorWindowedSmoothOddTestFn a :=
  let f := CCMParityTopLayer.oddSymSource g
  ⟨⟨⟨⟨f,f.smooth.of_le (WithTop.coe_le_coe.mpr
    (show (2 : ℕ∞) ≤ ⊤ from le_top)),f.hasCompactSupport⟩,
    CCMParityTopLayer.oddSymSource_odd g⟩,f.smooth⟩,f.tsupport_subset⟩

theorem oddInteriorSource_formVector {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) :
    (interiorCCMSource (oddInteriorSource g)).toCCMFormVector =
      ccmRestrictedWeilOddPart a g.toCCMFormVector :=
  (CCMParityTopLayer.oddPart_toCCMFormVector g).symm

/-- The exact form norm admits strict-interior smooth odd approximation. -/
theorem exists_interior_odd_form_approximation (a : SuzukiPositiveAperture)
    (u : OddFormSource a) :
    ∃ f : ℕ → InteriorWindowedSmoothOddTestFn a,
      Tendsto (fun n => (interiorCCMSource (f n)).toCCMFormVector) atTop (𝓝 u.1) := by
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp
    (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a u.1)
  choose g hg using hv
  have hlim' : Tendsto (fun n => (g n).toCCMFormVector) atTop (𝓝 u.1) := by
    simpa only [hg] using hlim
  have hc : Continuous (ccmRestrictedWeilOddPart a) := by
    change Continuous (fun v : CCMArchimedeanFormDomain a =>
      (2 : ℂ)⁻¹ • (v - ccmArchimedeanFormReflection a v))
    exact (continuous_const : Continuous (fun _ : CCMArchimedeanFormDomain a => (2 : ℂ)⁻¹)).smul
      (continuous_id.sub (ccmArchimedeanFormReflection a).continuous)
  have hu : ccmRestrictedWeilOddPart a u.1 = u.1 := by
    rw [ccmRestrictedWeilOddPart,u.2,sub_neg_eq_add,← two_smul ℂ u.1,smul_smul,
      inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0),one_smul]
  refine ⟨fun n => oddInteriorSource (g n),?_⟩
  simpa only [Function.comp_def,oddInteriorSource_formVector,hu] using (hc.tendsto u.1).comp hlim'

def formProfile {a : SuzukiPositiveAperture} (u : OddFormSource a) : ℝ → ℂ :=
  energyProfile a (ccmArchimedeanFormToAperture a u.1)

def formEnergy {a : SuzukiPositiveAperture} (u : OddFormSource a) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a u.1

/-- Smooth odd profiles recover the entire profile and the exact energy together. -/
theorem exists_interior_odd_observable_approximation (a : SuzukiPositiveAperture)
    (u : OddFormSource a) :
    ∃ f : ℕ → InteriorWindowedSmoothOddTestFn a,
      (∀ x,Tendsto (fun n => interiorProfile (f n) x) atTop (𝓝 (formProfile u x))) ∧
      Tendsto (fun n => interiorEnergy (f n)) atTop (𝓝 (formEnergy u)) := by
  obtain ⟨f,hf⟩ := exists_interior_odd_form_approximation a u
  refine ⟨f,?_,?_⟩
  · intro x
    have hp := ((continuous_energyProfile a).tendsto _).comp
      (((ccmArchimedeanFormToAperture a).continuous.tendsto _).comp hf)
    have hx := ((continuous_apply x).tendsto _).comp hp
    simpa only [Function.comp_def,energyProfile_interiorCCMSource,interiorProfile,formProfile] using hx
  · have hq := ((continuous_ccmRestrictedWeilSourceQuadratic a).tendsto _).comp hf
    simpa only [Function.comp_def,sourceEnergy_interiorCCMSource,interiorEnergy,interiorProfile,
      formEnergy] using hq

def formLogValue {a : SuzukiPositiveAperture} (u : OddFormSource a) (j : LogIndex) : ℝ :=
  (formProfile u (Real.log j) + formProfile u (-Real.log j)).re / Real.sqrt j

theorem trace_tendsto_of_profile_tendsto {a : SuzukiPositiveAperture}
    (u : OddFormSource a) (f : ℕ → InteriorWindowedSmoothOddTestFn a)
    (hf : ∀ x,Tendsto (fun n => interiorProfile (f n) x) atTop (𝓝 (formProfile u x)))
    (j : LogIndex) :
    Tendsto (fun n => interiorTrace (f n) j) atTop (𝓝 (formLogValue u j)) := by
  have h := ((Complex.continuous_re.tendsto _).comp
    ((hf (Real.log j)).add (hf (-Real.log j)))).div_const (Real.sqrt j)
  simpa only [Function.comp_def,interiorTrace,logVector_apply,logValue,interiorProfile,
    formLogValue] using h

theorem formLogValue_eq_zero_outside {a : SuzukiPositiveAperture}
    (u : OddFormSource a) (j : LogIndex) (hj : j ∉ apertureNodes a) :
    formLogValue u j = 0 := by
  obtain ⟨f,hf,-⟩ := exists_interior_odd_observable_approximation a u
  have ht := trace_tendsto_of_profile_tendsto u f hf j
  have hz (n : ℕ) : interiorTrace (f n) j = 0 := by
    apply Finsupp.notMem_support_iff.mp
    exact fun h => hj (interiorTrace_support_subset (f n) h)
  simp only [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- The complete arithmetic trace uses only the strict active aperture nodes. -/
def formTrace {a : SuzukiPositiveAperture} (u : OddFormSource a) : LogIndex →₀ ℝ :=
  Finsupp.onFinset (apertureNodes a) (formLogValue u)
    (fun j hj => Classical.byContradiction fun h => hj (formLogValue_eq_zero_outside u j h))

theorem formTrace_apply {a : SuzukiPositiveAperture} (u : OddFormSource a) (j : LogIndex) :
    formTrace u j = formLogValue u j := rfl

theorem formTrace_support_subset {a : SuzukiPositiveAperture} (u : OddFormSource a) :
    (formTrace u).support ⊆ apertureNodes a := by
  intro j hj
  by_contra hn
  exact Finsupp.mem_support_iff.mp hj (formLogValue_eq_zero_outside u j hn)

end RHTower.OddSector
