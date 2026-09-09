import GaloisForLFunctions.HTGeometry.WuExponentialEnergy
import GaloisForLFunctions.HTGeometry.SelfAdjointPropagator

/-!
# Wu energy bounds for Schrödinger evolution

Lemma 2.3 of arXiv:2609.08421 applies sharply to the corpus's exact unitary
propagator. Writing the generator as `H + H*` discharges self-adjointness for
arbitrary bounded operator data. No evolution, boundedness, or positivity
premise is supplied by the caller.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
open MeasureTheory
noncomputable section
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-- Hermitian part without a self-adjointness premise. -/
def hermitianGenerator (H : 𝓗 →L[ℂ] 𝓗) : 𝓗 →L[ℂ] 𝓗 := H + star H

theorem hermitianGenerator_selfAdjoint (H : 𝓗 →L[ℂ] 𝓗) :
    IsSelfAdjoint (hermitianGenerator H) := by
  show star (H + star H) = H + star H
  simp [add_comm]

/-- Exact weighted energy of the existing Schrödinger solution. -/
theorem schrodinger_energy (H : 𝓗 →L[ℂ] 𝓗) (x : 𝓗) (d t : ℝ) :
    energy d t (fun s => propagator (hermitianGenerator H) s x) = mass d t * ‖x‖ ^ 2 := by
  unfold energy
  simp_rw [norm_propagator_apply (hermitianGenerator_selfAdjoint H)]
  rw [intervalIntegral.integral_mul_const, integral_weight]

/-- Exact stability in the initial datum over an arbitrarily long observation interval. -/
theorem schrodinger_difference_energy (H : 𝓗 →L[ℂ] 𝓗) (x y : 𝓗) (d t : ℝ) :
    energy d t (fun s => propagator (hermitianGenerator H) s x -
      propagator (hermitianGenerator H) s y) = mass d t * ‖x - y‖ ^ 2 := by
  simp_rw [← map_sub]
  exact schrodinger_energy H (x - y) d t

/-- The orbit is bounded in its original Hilbert norm, with the exact norm of the datum. -/
def schrodingerOrbit (H : 𝓗 →L[ℂ] 𝓗) (x : 𝓗) : BoundedContinuousFunction ℝ 𝓗 :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s => propagator (hermitianGenerator H) s x)
    ((continuous_propagator _).clm_apply continuous_const) ‖x‖
    (fun s => (norm_propagator_apply (hermitianGenerator_selfAdjoint H) s x).le)

theorem norm_schrodingerOrbit (H : 𝓗 →L[ℂ] 𝓗) (x : 𝓗) : ‖schrodingerOrbit H x‖ = ‖x‖ := by
  apply le_antisymm
  · exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _
  · have h := (schrodingerOrbit H x).norm_coe_le_norm 0
    simpa [schrodingerOrbit] using h

/-- The paper's uniform square-energy bound, now for a genuine quantum evolution. -/
theorem schrodinger_energy_le (H : 𝓗 →L[ℂ] 𝓗) (x : 𝓗) (d t : ℝ) :
    energy d t (fun s => propagator (hermitianGenerator H) s x) ≤
      ‖x‖ ^ 2 / (2 * Real.exp d) := by
  have h := energy_le d t (schrodingerOrbit H x)
  rwa [norm_schrodingerOrbit] at h

/-- Every bounded reporter inherits the energy gain from the full state. -/
def observedSchrodingerOrbit {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (H : 𝓗 →L[ℂ] 𝓗) (x : 𝓗) (A : 𝓗 →L[ℂ] Y) : BoundedContinuousFunction ℝ Y :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s => A (propagator (hermitianGenerator H) s x))
    (A.continuous.comp (schrodingerOrbit H x).continuous) (‖A‖ * ‖x‖)
    (fun s => by
      calc ‖A (propagator (hermitianGenerator H) s x)‖ ≤
          ‖A‖ * ‖propagator (hermitianGenerator H) s x‖ := A.le_opNorm _
        _ = _ := by rw [norm_propagator_apply (hermitianGenerator_selfAdjoint H)])

theorem observed_schrodinger_energy_le {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (H : 𝓗 →L[ℂ] 𝓗) (x : 𝓗) (A : 𝓗 →L[ℂ] Y) (d t : ℝ) :
    energy d t (fun s => A (propagator (hermitianGenerator H) s x)) ≤
      (‖A‖ * ‖x‖) ^ 2 / (2 * Real.exp d) := by
  have hb : ‖observedSchrodingerOrbit H x A‖ ≤ ‖A‖ * ‖x‖ :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _
  exact (energy_le d t (observedSchrodingerOrbit H x A)).trans
    (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb) (by positivity))

end
end GaloisForLFunctions.HTGeometry.Wu
