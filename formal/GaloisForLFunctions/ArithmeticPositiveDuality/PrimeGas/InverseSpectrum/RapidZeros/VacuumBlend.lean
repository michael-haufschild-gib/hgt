import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.BalancedPair

/-! # Adding a vacuum component transports finite readings and analytic germs -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology U0NaturalBoundary

def vacuumMass (n : ℕ+) : ℝ := if n = 1 then 1 else 0

private theorem vacuumMass_nonneg (n : ℕ+) : 0 ≤ vacuumMass n := by unfold vacuumMass; split <;> norm_num

def vacuumBlend (v : MissingWave) := lawOmission (midpointExterior (exteriorLaw v) vacuumMass vacuumMass_nonneg
  (hasSum_ite_eq (1:ℕ+) (1:ℝ)))

theorem vacuumBlend_probability (v : MissingWave) (n : ℕ+) :
    occupationProbability (vacuumBlend v) n = (occupationProbability v n+vacuumMass n)/2 :=
  congrFun (lawOmission_probability _) n

private theorem vacuum_heat (u : ℂ) : HasSum (fun n => (vacuumMass n:ℂ)*heat u n) 1 := by
  apply (hasSum_ite_eq (1:ℕ+) (1:ℂ)).congr_fun
  intro n
  by_cases h : n = 1
  · subst n
    simp [vacuumMass,heat,energy]
  · simp [vacuumMass,h]

private theorem blend_terms (v : MissingWave) (s b : ℂ) :
    HasSum (fun n => (occupationProbability (vacuumBlend v) n:ℂ)*heat (2*s-1) n) b ↔
      HasSum (fun n => (occupationProbability v n:ℂ)*heat (2*s-1) n) (2*b-1) := by
  have huv (n : ℕ+) : (occupationProbability (vacuumBlend v) n:ℂ)*heat (2*s-1) n =
      ((occupationProbability v n:ℂ)*heat (2*s-1) n+(vacuumMass n:ℂ)*heat (2*s-1) n)/2 := by
    rw [vacuumBlend_probability,Complex.ofReal_div,Complex.ofReal_add]
    push_cast
    ring
  constructor
  · intro h
    apply ((h.mul_left (2:ℂ)).sub (vacuum_heat (2*s-1))).congr_fun
    intro n
    rw [huv]
    ring
  · intro h
    have hh := (h.add (vacuum_heat (2*s-1))).div_const 2
    rw [show (2*b-1+1)/2 = b by ring] at hh
    exact hh.congr_fun huv

theorem vacuumBlend_finiteSplit_iff (v : MissingWave) (s : ℂ) :
    finiteSplit (vacuumBlend v) s ↔ finiteSplit v s := by
  rw [← response_absolute_iff,← response_absolute_iff,summable_norm_iff,summable_norm_iff]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨2*b-1,(blend_terms v s b).mp hb⟩
  · rintro ⟨b,hb⟩
    refine ⟨(b+1)/2,(blend_terms v s _).mpr ?_⟩
    rwa [show 2*((b+1)/2)-1 = b by ring]

theorem vacuumBlend_response (v : MissingWave) {s : ℂ} (h : finiteSplit v s) :
    compositionResponse (vacuumBlend v) s = (compositionResponse v s+1)/2 := by
  have hh := ((response_absolute_iff v s).mpr h).of_norm.hasSum
  apply HasSum.tsum_eq
  apply (blend_terms v s _).mpr
  rw [show 2*((compositionResponse v s+1)/2)-1 = compositionResponse v s by ring]
  exact hh

/-- A local continuation from finite readings passes through the affine vacuum mixture in either direction. -/
theorem vacuumBlend_continues_iff (v : MissingWave) (D : Set ℂ) (s : ℂ)
    (hD : ∀ z ∈ D, finiteSplit v z) :
    ContinuesAcross (compositionResponse (vacuumBlend v)) D s ↔ ContinuesAcross (compositionResponse v) D s := by
  constructor
  · rintro ⟨g,hg,he⟩
    refine ⟨fun z => 2*g z-1,(analyticAt_const.mul hg).sub analyticAt_const,?_⟩
    filter_upwards [he,self_mem_nhdsWithin] with z hz hmem
    rw [hz,vacuumBlend_response v (hD z hmem)]
    ring
  · rintro ⟨g,hg,he⟩
    refine ⟨fun z => (g z+1)/2,(hg.add analyticAt_const).div_const,?_⟩
    filter_upwards [he,self_mem_nhdsWithin] with z hz hmem
    rw [hz,vacuumBlend_response v (hD z hmem)]

#print axioms vacuumBlend_probability
#print axioms vacuumBlend_finiteSplit_iff
#print axioms vacuumBlend_response
#print axioms vacuumBlend_continues_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
