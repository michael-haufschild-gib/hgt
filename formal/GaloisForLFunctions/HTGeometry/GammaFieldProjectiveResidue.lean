import GaloisForLFunctions.HTGeometry.GammaLowestPowerResidue

/-!
# The projective boundary of a Gamma-field element, with its residue

Composing the two layers: the coefficients of a Gamma polynomial are elements of `ℂ(s)⟨ψ⟩`, each
converging after division by its own normalization shape, and `Γ` beats every such coefficient
downwards.  So dividing by the lowest Gamma power together with the shape of its coefficient leaves
exactly the residue of that coefficient.

This is eq. (3) with an explicit limit: the projective boundary of an element of `ℂ(s)⟨Γ⟩` is the
algebraic-logarithmic residue of the coefficient of its lowest Gamma power.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- A convergent function has polynomial growth. -/
theorem HasPolyGrowthLine.of_tendsto {f : ℝ → ℂ} {c : ℂ}
    (hf : Tendsto f atTop (nhds c)) : HasPolyGrowthLine f := by
  refine ⟨0, ‖c‖ + 1, by positivity, ?_⟩
  have hnorm : Tendsto (fun t : ℝ => ‖f t‖) atTop (nhds ‖c‖) := hf.norm
  have hlt : ∀ᶠ t : ℝ in atTop, ‖f t‖ < ‖c‖ + 1 :=
    hnorm.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hlt] with t ht
  simpa using ht.le

/-- **Eq. (3) with the residue.**  A finite Gamma polynomial whose coefficients converge after
division by a common shape, and whose coefficients below the lowest index vanish, converges after
division by that power of `Γ` times the shape — to the residue of the lowest coefficient. -/
theorem tendsto_gammaField_projective (hσ : 0 < σ) {d : ℕ} (A : ℕ → ℝ → ℂ) (u : ℕ) (hu : u ≤ d)
    (shape : ℝ → ℂ) (cs : ℕ → ℂ) (hshape : ∀ᶠ t : ℝ in atTop, shape t ≠ 0)
    (hconv : ∀ i, Tendsto (fun t : ℝ => A i t / shape t) atTop (nhds (cs i)))
    (hlow : ∀ i < u, A i = fun _ => 0) :
    Tendsto (fun t : ℝ => (∑ i ∈ Finset.range (d + 1), A i t * gammaLine σ t ^ i)
        / (gammaLine σ t ^ u * shape t)) atTop (nhds (cs u)) := by
  classical
  have hgrow : ∀ i, HasPolyGrowthLine (fun t : ℝ => A i t / shape t) :=
    fun i => HasPolyGrowthLine.of_tendsto (hconv i)
  have hlow' : ∀ i < u, (fun t : ℝ => A i t / shape t) = fun _ => 0 := by
    intro i hi
    funext t
    rw [hlow i hi]
    simp
  have hmain := tendsto_gammaSum_div_pow (σ := σ) hσ (fun i t => A i t / shape t) u hgrow
    (hconv u) hlow' hu
  refine hmain.congr' ?_
  filter_upwards [hshape] with t ht
  have hγ : gammaLine σ t ^ u ≠ 0 := pow_ne_zero u (gammaLine_ne_zero hσ t)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp

end GaloisForLFunctions
