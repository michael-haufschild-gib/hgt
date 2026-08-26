import GaloisForLFunctions.HTGeometry.LocalHomeomorphPullback
import GaloisForLFunctions.HTGeometry.MonicCoefficientRootCovering

/-!
# Continuous separable monic root families

Coefficient-space simple-root charts and topological pullback combine to cover arbitrary
continuous coefficient families over arbitrary topological bases.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology Set Polynomial

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Root cover obtained by pulling universal monic roots back along a coefficient family. -/
abbrev ContinuousMonicRootPullback (d : ℕ) (c : X → (Fin d → ℂ)) :=
  LocalHomeomorphPullback (monicCoeffRootProj (d := d)) c

/-- Projection of a pulled-back monic root cover. -/
abbrev continuousMonicRootPullbackProj {d : ℕ} {c : X → (Fin d → ℂ)} :
    ContinuousMonicRootPullback d c → X :=
  localHomeomorphPullbackProj

/-- A continuous family of separable monic polynomials has a locally homeomorphic root cover over
an arbitrary topological base. -/
theorem isLocalHomeomorph_continuousMonicRootPullbackProj {d : ℕ}
    {c : X → (Fin d → ℂ)} (hc : Continuous c)
    (hsep : ∀ x : X, (monicCoeffPolynomial d (c x)).Separable) :
    IsLocalHomeomorph (continuousMonicRootPullbackProj (d := d) (c := c)) := by
  intro q
  have hsep_q : (monicCoeffPolynomial d q.1.2.1.1).Separable := by
    have hcoeff : c q.1.1 = q.1.2.1.1 := q.2
    rw [← hcoeff]
    exact hsep q.1.1
  obtain ⟨e, hqe, hproj⟩ := exists_chart_monicCoeffRootProj q.1.2 hsep_q
  exact exists_chart_localHomeomorphPullbackProj_of_chart q e hqe hproj hc

end

end GaloisForLFunctions.HTGeometry

