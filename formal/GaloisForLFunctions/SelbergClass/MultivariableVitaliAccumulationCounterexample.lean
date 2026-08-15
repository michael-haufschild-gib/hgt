import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Accumulation on a complex hyperplane is not a uniqueness principle

This is the precise several-complex-variables obstruction relevant to the
Kaczorowski--Perelli continuation audit.  In `ℂ²`, agreement of globally
analytic functions on a complex hyperplane, even with an interior-domain
accumulation point, does not imply equality.  It is not a counterexample to a
full multivariable Vitali theorem: it isolates only the invalid replacement of
a uniqueness set by a bare accumulation point.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

/-- The two-complex-variable domain used for the counterexample. -/
abbrev SCVTwo := Fin 2 → ℂ

/-- The complex coordinate hyperplane `H = {z | z₀ = 0}` in `ℂ²`. -/
def scvAccumulationHyperplane : Set SCVTwo :=
  {z | z 0 = 0}

/-- The globally analytic zero function on `ℂ²`. -/
def scvZero : SCVTwo → ℂ := fun _ => 0

/-- The globally analytic first coordinate function on `ℂ²`. -/
def scvFirstCoordinate : SCVTwo → ℂ := fun z => z 0

/-- The zero function is analytic on all of `ℂ²`. -/
theorem analyticOnNhd_scvZero :
    AnalyticOnNhd ℂ scvZero Set.univ := by
  intro z _
  exact analyticAt_const

/-- The first coordinate projection is analytic on all of `ℂ²`. -/
theorem analyticOnNhd_scvFirstCoordinate :
    AnalyticOnNhd ℂ scvFirstCoordinate Set.univ := by
  intro z _
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt z

/-- The two analytic functions agree on the full coordinate hyperplane. -/
theorem scvZero_eq_scvFirstCoordinate_on_hyperplane :
    Set.EqOn scvZero scvFirstCoordinate scvAccumulationHyperplane := by
  intro z hz
  simpa [scvZero, scvFirstCoordinate, scvAccumulationHyperplane] using hz.symm

/-- The origin is an accumulation point of the punctured coordinate hyperplane. -/
theorem zero_mem_closure_scvAccumulationHyperplane_punctured :
    (0 : SCVTwo) ∈ closure (scvAccumulationHyperplane \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let z : SCVTwo := Pi.single 1 ((ε / 2 : ℝ) : ℂ)
  refine ⟨z, ?_, ?_⟩
  · constructor
    · change z 0 = 0
      simp [z]
    · intro hz
      have hz' := congrFun hz (1 : Fin 2)
      have hhalf : (ε / 2 : ℝ) = 0 := by
        exact Complex.ofReal_eq_zero.mp (by simpa [z] using hz')
      linarith
  · rw [dist_zero_left, Pi.norm_single, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]
    linarith

/-- The two analytic functions are nevertheless distinct. -/
theorem scvZero_ne_scvFirstCoordinate : scvZero ≠ scvFirstCoordinate := by
  intro h
  have h' : (0 : ℂ) = 1 := by
    simpa [scvZero, scvFirstCoordinate] using
      congrFun h (Pi.single 0 (1 : ℂ))
  exact zero_ne_one h'

/-- A bare accumulation point on a complex hyperplane is not enough for a
multivariable analytic uniqueness conclusion. -/
theorem multivariableAccumulationCounterexample :
    ∃ f g : SCVTwo → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧
      AnalyticOnNhd ℂ g Set.univ ∧
      Set.EqOn f g scvAccumulationHyperplane ∧
      (0 : SCVTwo) ∈ closure (scvAccumulationHyperplane \ {0}) ∧
      f ≠ g := by
  exact ⟨scvZero, scvFirstCoordinate, analyticOnNhd_scvZero,
    analyticOnNhd_scvFirstCoordinate,
    scvZero_eq_scvFirstCoordinate_on_hyperplane,
    zero_mem_closure_scvAccumulationHyperplane_punctured,
    scvZero_ne_scvFirstCoordinate⟩

end GaloisForLFunctions.SelbergClass
