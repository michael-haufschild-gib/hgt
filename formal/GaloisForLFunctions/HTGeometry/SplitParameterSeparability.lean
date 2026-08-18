import GaloisForLFunctions.HTGeometry.AlgebraSpectrumTopology
import GaloisForLFunctions.Bottcher.Q62SmoothPieceReduction

/-!
# Separability of the specialised relation at a split parameter

At a parameter whose fibre carries `n` complex points taking pairwise distinct values on `θ`, the
monic degree-`n` relation satisfied by `θ` specialises to a separable polynomial: it is monic of
degree `n` and the `n` distinct values are roots.  No identification of the specialisation with a
product of linear factors is needed.

This is the separability input of the chart data of `AlgebraSpectrumCovering`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **Separability of the specialised relation at a split parameter.**  If `n ≥ 1` complex points
over `s` take pairwise distinct values on `θ`, and `θ` satisfies a monic relation of degree `n`,
then that relation specialises at `s` to a separable polynomial. -/
theorem separable_biFibre_of_separating {n : ℕ} (hn : 1 ≤ n) {θ : B} {p : ℂ[X][X]}
    (hp : Polynomial.aeval θ p = 0) (hmonic : p.Monic) (hdeg : p.natDegree = n) {s : ℂ}
    (χ : Fin n → AlgSpec B) (hproj : ∀ i, AlgSpec.proj B (χ i) = s)
    (hsep : Function.Injective fun i => χ i θ) :
    (biFibre p s).Separable := by
  refine Bottcher.separable_of_distinct_roots hn ?_ (fun i => χ i θ) hsep ?_
  · rw [biFibre_natDegree hmonic]; exact hdeg
  · intro k
    have h := AlgSpec.apply_aeval θ p (χ k)
    rw [hp, map_zero] at h
    have h2 : biEval p (AlgSpec.proj B (χ k), χ k θ) = 0 := h.symm
    rw [hproj k, biEval_eq_eval_biFibre] at h2
    exact h2

end

end GaloisForLFunctions.HTGeometry
