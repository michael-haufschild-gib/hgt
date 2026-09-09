import GaloisForLFunctions.HTGeometry.WuDoubleNullEnergy
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Wu integration at every Schwartz derivative and moment order

Lemma 2.3 of arXiv:2609.08421 is insensitive to the angular norm used there.
Here its same scalar integration mechanism controls every weighted derivative
of a Schwartz source, and every weighted derivative of its Fourier transform.
The original Schwartz seminorms discharge all boundedness and regularity inputs.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
noncomputable section

/-- All polynomially weighted derivatives are bounded continuous curves, with their native seminorm. -/
def schwartzJet (f : SchwartzMap ℝ ℂ) (k n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s => (s ^ k : ℝ) • iteratedDeriv n (f : ℝ → ℂ) s)
    ((continuous_id.pow k).smul ((f.smooth n).continuous_iteratedDeriv' n))
    (SchwartzMap.seminorm ℝ k n f)
    (fun s => by
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      exact SchwartzMap.le_seminorm' ℝ k n f s)

theorem norm_schwartzJet_le (f : SchwartzMap ℝ ℂ) (k n : ℕ) :
    ‖schwartzJet f k n‖ ≤ SchwartzMap.seminorm ℝ k n f :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

/-- A single theorem covers every physical-space moment and derivative order. -/
theorem schwartz_jet_energy_le (f : SchwartzMap ℝ ℂ) (k n : ℕ) (d t : ℝ) :
    energy d t (fun s => (s ^ k : ℝ) • iteratedDeriv n (f : ℝ → ℂ) s) ≤
      (SchwartzMap.seminorm ℝ k n f) ^ 2 / (2 * Real.exp d) := by
  exact (energy_le d t (schwartzJet f k n)).trans (div_le_div_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_schwartzJet_le f k n)) (by positivity))

/-- The native Fourier transform obeys the same estimate at every dual moment and derivative order. -/
theorem fourier_schwartz_jet_energy_le (f : SchwartzMap ℝ ℂ) (k n : ℕ) (d t : ℝ) :
    energy d t (fun s => (s ^ k : ℝ) •
      iteratedDeriv n (SchwartzMap.fourierTransformCLM ℂ f : ℝ → ℂ) s) ≤
      (SchwartzMap.seminorm ℝ k n (SchwartzMap.fourierTransformCLM ℂ f)) ^ 2 /
        (2 * Real.exp d) :=
  schwartz_jet_energy_le _ k n d t

/-- A two-variable Schwartz field inherits the full characteristic rectangle gain. -/
theorem schwartz_rectangle_energy_le (f : SchwartzMap (ℝ × ℝ) ℂ) (d u v : ℝ) :
    rectangleEnergy d u v f ≤ (SchwartzMap.seminorm ℝ 0 0 f) ^ 2 / (2 * Real.exp d) ^ 2 := by
  exact (rectangleEnergy_le d u v f.toBoundedContinuousFunction).trans
    (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr f.norm_toBoundedContinuousFunction_le)
      (sq_nonneg _))

end
end GaloisForLFunctions.HTGeometry.Wu
