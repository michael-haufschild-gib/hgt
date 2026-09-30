import GaloisForLFunctions.RHTower.CCMFiniteSamplingGroundRigidity
import GaloisForLFunctions.RHTower.CCMPrimePoleJumpBochner

/-!
# Finite literal prime-curvature probes retain the complete ground floor

The complete ordered two-step footprint is finite. Interior source values can
be set to zero in a form-norm dense exact-pole fibre; all remaining footprint
values are already zero by strict support. Literal generator, jump energy and
iterated energy therefore vanish simultaneously at every prescribed probe.
-/

open scoped BigOperators
noncomputable section
set_option autoImplicit false
namespace RHTower.FinitePrimeCurvatureProbes
open HTGeometry.JumpBochner

def successors (a : SuzukiPositiveAperture) (s : Finset ℝ) : Finset ℝ :=
  s.biUnion fun x => (ccmPrimePoleJumpIndices a).image fun i => ccmPrimePoleJumpShift i x

def footprint (a : SuzukiPositiveAperture) (s : Finset ℝ) : Finset ℝ :=
  s ∪ successors a s ∪ successors a (successors a s)

def interiorFootprint (a : SuzukiPositiveAperture) (s : Finset ℝ) : Finset ℝ :=
  (footprint a s).filter fun x => |x| < a.1

def sourceObservable {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a)
    (x : ℝ) : ℝ := (g x).re / primePoleProfile x

/-- All three readers use the literal index set, rates and endpoint cutoffs. -/
def Silent (a : SuzukiPositiveAperture) (s : Finset ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ s,
    generator (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) ccmPrimePoleJumpShift f x = 0 ∧
    energyDensity (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a)
      ccmPrimePoleJumpShift f f x = 0 ∧
    gammaTwo (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) ccmPrimePoleJumpShift f x = 0

private theorem mem_successors {a : SuzukiPositiveAperture} {s : Finset ℝ} {x : ℝ}
    (hx : x ∈ s) {i : ℕ × Bool} (hi : i ∈ ccmPrimePoleJumpIndices a) :
    ccmPrimePoleJumpShift i x ∈ successors a s := by
  exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

private theorem footprint_base {a : SuzukiPositiveAperture} {s : Finset ℝ} {x : ℝ}
    (hx : x ∈ s) : x ∈ footprint a s := by
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx)))

private theorem footprint_one {a : SuzukiPositiveAperture} {s : Finset ℝ} {x : ℝ}
    (hx : x ∈ s) {i : ℕ × Bool} (hi : i ∈ ccmPrimePoleJumpIndices a) :
    ccmPrimePoleJumpShift i x ∈ footprint a s := by
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (mem_successors hx hi))))

private theorem footprint_two {a : SuzukiPositiveAperture} {s : Finset ℝ} {x : ℝ}
    (hx : x ∈ s) {i j : ℕ × Bool} (hi : i ∈ ccmPrimePoleJumpIndices a)
    (hj : j ∈ ccmPrimePoleJumpIndices a) :
    ccmPrimePoleJumpShift i (ccmPrimePoleJumpShift j x) ∈ footprint a s := by
  exact Finset.mem_union.mpr (Or.inr (mem_successors (mem_successors hx hj) hi))

private theorem source_zero_outside {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) {x : ℝ} (hx : ¬ |x| < a.1) : g x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hx (abs_lt.mpr (g.tsupport_subset hmem))

private theorem observable_zero_footprint {a : SuzukiPositiveAperture} {s : Finset ℝ}
    (g : CCMComplexSmoothInteriorSource a)
    (hg : ∀ x ∈ interiorFootprint a s, g x = 0) :
    ∀ x ∈ footprint a s, sourceObservable g x = 0 := by
  intro x hx
  have hzero : g x = 0 := by
    by_cases hi : |x| < a.1
    · exact hg x (Finset.mem_filter.mpr ⟨hx, hi⟩)
    · exact source_zero_outside g hi
  simp only [sourceObservable, hzero, Complex.zero_re, zero_div]

private theorem silent_of_zero_footprint {a : SuzukiPositiveAperture} {s : Finset ℝ}
    (f : ℝ → ℝ) (hf : ∀ x ∈ footprint a s, f x = 0) : Silent a s f := by
  intro x hx
  have h₀ : f x = 0 := hf x (footprint_base hx)
  have h₁ : ∀ i ∈ ccmPrimePoleJumpIndices a, f (ccmPrimePoleJumpShift i x) = 0 :=
    fun i hi => hf _ (footprint_one hx hi)
  have h₂ : ∀ i ∈ ccmPrimePoleJumpIndices a, ∀ j ∈ ccmPrimePoleJumpIndices a,
      f (ccmPrimePoleJumpShift i (ccmPrimePoleJumpShift j x)) = 0 :=
    fun i hi j hj => hf _ (footprint_two hx hi hj)
  constructor
  · unfold generator
    apply Finset.sum_eq_zero
    intro i hi
    simp [difference, h₀, h₁ i hi]
  constructor
  · unfold energyDensity
    have hs : (∑ i ∈ ccmPrimePoleJumpIndices a,
        ccmPrimePoleJumpRate a i x * difference ccmPrimePoleJumpShift i f x *
          difference ccmPrimePoleJumpShift i f x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [difference, h₀, h₁ i hi]
    rw [hs, zero_div]
  · rw [gammaTwo_eq_pairSum]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    simp [difference, h₀, h₁ i hi, h₁ j hj, h₂ i hi j hj, h₂ j hj i hi]

/-- A complete zero footprint removes all literal local readers, including rate defects. -/
theorem silent_of_interior_samples_zero {a : SuzukiPositiveAperture} {s : Finset ℝ}
    (g : CCMComplexSmoothInteriorSource a)
    (hg : ∀ x ∈ interiorFootprint a s, g x = 0) : Silent a s (sourceObservable g) :=
  silent_of_zero_footprint _ (observable_zero_footprint g hg)

/-- Every finite simultaneous zero-curvature repair is dense in the exact constrained form domain. -/
theorem exists_silent_source_close (a : SuzukiPositiveAperture) (s : Finset ℝ)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧
      Silent a s (sourceObservable g) ∧ ‖g.toCCMFormVector - u‖ < ε := by
  obtain ⟨g, hg, hgv, hgn⟩ := exists_ccmPolarConstrained_sample_preserving_close
    a u hu (interiorFootprint a s) (fun _ => 0)
    (fun _ hx => (Finset.mem_filter.mp hx).2) hε
  exact ⟨g, hg, silent_of_interior_samples_zero g hgv, hgn⟩

/-- All finite literal curvature probes can vanish simultaneously arbitrarily near the ground floor. -/
theorem exists_silent_source_rayleigh_lt (a : SuzukiPositiveAperture) (s : Finset ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧ Silent a s (sourceObservable g) ∧
      ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 ∧
      ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector /
        ‖ccmArchimedeanFormToAperture a g.toCCMFormVector‖^2 <
          ccmRestrictedWeilPolarGroundEnergy a + ε := by
  obtain ⟨g, hg, hgv, hgne, hgR⟩ := exists_ccmPolarConstrained_sampled_rayleigh_lt
    a (interiorFootprint a s) (fun _ => 0)
    (fun _ hx => (Finset.mem_filter.mp hx).2) hε
  exact ⟨g, hg, silent_of_interior_samples_zero g hgv, hgne, hgR⟩

def silentRayleighSet (a : SuzukiPositiveAperture) (s : Finset ℝ) : Set ℝ :=
  {r | ∃ g : CCMComplexSmoothInteriorSource a,
    IsPolarConstrained a g.toCCMFormVector ∧ Silent a s (sourceObservable g) ∧
    ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 ∧
    r = ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector /
      ‖ccmArchimedeanFormToAperture a g.toCCMFormVector‖^2}

/-- Exact ground-energy invariance under any finite simultaneous literal prime-curvature repair. -/
theorem silentRayleigh_inf_eq (a : SuzukiPositiveAperture) (s : Finset ℝ) :
    sInf (silentRayleighSet a s) = ccmRestrictedWeilPolarGroundEnergy a := by
  have hfloor : ∀ r ∈ silentRayleighSet a s, ccmRestrictedWeilPolarGroundEnergy a ≤ r := by
    rintro r ⟨g, hg, _, hgne, rfl⟩
    exact ccmRestrictedWeilPolarGroundEnergy_le_rayleigh a g.toCCMFormVector hg hgne
  have hbdd : BddBelow (silentRayleighSet a s) := ⟨_, hfloor⟩
  obtain ⟨g, hg, hgs, hgne, _⟩ := exists_silent_source_rayleigh_lt a s zero_lt_one
  have hne : (silentRayleighSet a s).Nonempty := ⟨_, g, hg, hgs, hgne, rfl⟩
  apply le_antisymm
  · by_contra hn
    have hgap : 0 < sInf (silentRayleighSet a s) - ccmRestrictedWeilPolarGroundEnergy a :=
      sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨f, hf, hfs, hfne, hfR⟩ := exists_silent_source_rayleigh_lt a s (half_pos hgap)
    have hle := csInf_le hbdd
      (show ccmRestrictedWeilSourceQuadratic a f.toCCMFormVector /
          ‖ccmArchimedeanFormToAperture a f.toCCMFormVector‖^2 ∈ silentRayleighSet a s from
        ⟨f, hf, hfs, hfne, rfl⟩)
    linarith
  · exact le_csInf hne hfloor

end RHTower.FinitePrimeCurvatureProbes
