import GaloisForLFunctions.HTGeometry.FokasLenellsRawBounds

/-!
# Actual scattering endpoints through zero frequency

The uniformly bounded raw flow has an integrable derivative on the whole
line. Both endpoint states therefore exist for every real frequency and
agree with the original Jost endpoint states at positive frequency.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawOrientedSolution (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) : SpectralVector :=
  rawInteractionSolution q k v (if left then -x else x)

def rawOrientedDerivative (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) : SpectralVector :=
  if left then -rawInteractionDerivative q k v (-x) else rawInteractionDerivative q k v x

theorem rawOrientedSolution_hasDerivAt (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) :
    HasDerivAt (rawOrientedSolution q k v left) (rawOrientedDerivative q k v left x) x := by
  cases left
  · exact rawInteractionSolution_hasDerivAt q k v x
  · change HasDerivAt (fun y : ℝ => rawInteractionSolution q k v (-y)) (-rawInteractionDerivative q k v (-x)) x
    have hd := (rawInteractionSolution_hasDerivAt q k v (-x)).scomp x (hasDerivAt_id x).neg
    convert! hd using 1
    simp only [neg_one_smul,rawInteractionDerivative]

theorem rawOrientedSolution_initial (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    rawOrientedSolution q k v left 0 = v := by
  cases left <;> simpa only [rawOrientedSolution,Bool.false_eq_true,↓reduceIte,neg_zero] using
    rawInteractionSolution_initial q k v

theorem rawOrientedDerivative_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    Integrable (rawOrientedDerivative q k v left) := by
  cases left
  · exact rawInteractionDerivative_integrable q k v
  · exact (rawInteractionDerivative_integrable q k v).comp_neg.neg

def rawAsymptoticVector (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) : SpectralVector :=
  v+∫ x in Set.Ioi (0 : ℝ), rawOrientedDerivative q k v left x

/-- Endpoint existence follows from the actual differential equation and its proved integrable derivative. -/
theorem rawOrientedSolution_tendsto (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    Tendsto (rawOrientedSolution q k v left) atTop (𝓝 (rawAsymptoticVector q k v left)) := by
  have hh := tendsto_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => rawOrientedSolution_hasDerivAt q k v left x)
    (rawOrientedDerivative_integrable q k v left).integrableOn
  simpa only [rawOrientedSolution_initial,rawAsymptoticVector] using hh

theorem rawInteractionSolution_tendsto_right (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Tendsto (rawInteractionSolution q k v) atTop (𝓝 (rawAsymptoticVector q k v false)) :=
  rawOrientedSolution_tendsto q k v false

theorem rawInteractionSolution_tendsto_left (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Tendsto (rawInteractionSolution q k v) atBot (𝓝 (rawAsymptoticVector q k v true)) := by
  have hh := (rawOrientedSolution_tendsto q k v true).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def,rawOrientedSolution,↓reduceIte,neg_neg] using hh

/-- The actual asymptotic maps inherit the total-mass bound, uniformly across zero frequency. -/
theorem rawAsymptoticVector_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    ‖rawAsymptoticVector q k v left‖ ≤ ‖v‖*Real.exp (|k| * rawInteractionMass q) := by
  apply le_of_tendsto (rawOrientedSolution_tendsto q k v left).norm
  exact Eventually.of_forall fun x => rawInteractionSolution_global_bound q k v (if left then -x else x)

theorem rawAsymptoticVector_zero_frequency (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    rawAsymptoticVector q 0 v left = v := by
  have hh := rawOrientedSolution_tendsto q 0 v left
  change Tendsto (fun x => rawInteractionSolution q 0 v (if left then -x else x)) atTop _ at hh
  simp only [rawInteractionSolution_zero_frequency] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

/-- The right endpoint is literally the one used in the existing scattering matrix. -/
theorem rawAsymptoticVector_exp_right (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    rawAsymptoticVector q (Real.exp κ) v false = rightAsymptoticVector q κ v := by
  have hh := rawInteractionSolution_tendsto_right q (Real.exp κ) v
  rw [rawInteractionSolution_exp_eq] at hh
  exact tendsto_nhds_unique hh (interactionSolution_tendsto_right q κ v)

/-- The same identification holds for the left Jost normalization. -/
theorem rawAsymptoticVector_exp_left (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    rawAsymptoticVector q (Real.exp κ) v true = leftAsymptoticVector q κ v := by
  have hh := rawInteractionSolution_tendsto_left q (Real.exp κ) v
  rw [rawInteractionSolution_exp_eq] at hh
  exact tendsto_nhds_unique hh (interactionSolution_tendsto_left q κ v)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
