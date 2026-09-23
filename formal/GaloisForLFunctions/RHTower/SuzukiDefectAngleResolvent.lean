import GaloisForLFunctions.HTGeometry.ResolventParameterContinuity
import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality

/-!
# The defect angle along a resolvent ray

Suzuki's defect angle of a shifted operator is the projective polarization of the two resolvent
energies of the deficiency pair, so it inherits the two properties an intermediate-value argument
needs: it is continuous wherever the shift is in the resolvent set and the total energy is nonzero,
and far below the spectrum it tends to the projective polarization of the two squared norms — the
free endpoint, computed from the source pair alone with no reference to the operator.
-/

noncomputable section

namespace RHTower

open Filter Topology Bornology GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The defect angle of a shifted operator is the resolvent polarization of the source pair. -/
theorem suzukiDefectAngle_resolvent (a : H →L[ℝ] H) (u v : H) (t : ℝ) :
    GaloisForLFunctions.RHTower.suzukiDefectAngle
        (inner ℝ u ((resolvent a t) u)) (inner ℝ v ((resolvent a t) v))
      = resolventPolarization a u v t := rfl

/-- **Interior continuity of the defect angle in the shift.** -/
theorem continuousAt_suzukiDefectAngle_resolvent (a : H →L[ℝ] H) (u v : H) {r : ℝ}
    (hr : r ∈ resolventSet ℝ a)
    (hsum : inner ℝ u ((resolvent a r) u) + inner ℝ v ((resolvent a r) v) ≠ (0 : ℝ)) :
    ContinuousAt (fun t : ℝ => GaloisForLFunctions.RHTower.suzukiDefectAngle
      (inner ℝ u ((resolvent a t) u)) (inner ℝ v ((resolvent a t) v))) r := by
  simpa only [suzukiDefectAngle_resolvent] using
    continuousAt_resolventPolarization a u v hr hsum

/-- **The free endpoint of the defect angle.**  Far below the spectrum the angle is the projective
polarization of the two squared norms of the source pair. -/
theorem tendsto_suzukiDefectAngle_resolvent (a : H →L[ℝ] H) (u v : H)
    (hne : ‖u‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ) ≠ 0) :
    Tendsto (fun t : ℝ => GaloisForLFunctions.RHTower.suzukiDefectAngle
        (inner ℝ u ((resolvent a t) u)) (inner ℝ v ((resolvent a t) v)))
      (cobounded ℝ ⊓ 𝓟 (resolventSet ℝ a))
      (𝓝 ((‖u‖ ^ (2 : ℕ) - ‖v‖ ^ (2 : ℕ)) / (‖u‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ)))) := by
  simpa only [suzukiDefectAngle_resolvent] using tendsto_resolventPolarization a u v hne

omit [CompleteSpace H] in
/-- **The ground endpoint of the defect angle.**  Theorem A's `(7)`: as the shift rises to the
spectral floor the angle tends to the projective polarization of the two ground overlaps. -/
theorem tendsto_suzukiDefectAngle_resolvent_ground {a : H →L[ℝ] H} {lam0 : ℝ} {gu gv wu wv : H}
    (hgu : a gu = lam0 • gu) (hgv : a gv = lam0 • gv) {Cu Cv : ℝ}
    (hu : ∀ᶠ t in 𝓝[<] lam0, t ∈ resolventSet ℝ a ∧ ‖(resolvent a t) wu‖ ≤ Cu)
    (hv : ∀ᶠ t in 𝓝[<] lam0, t ∈ resolventSet ℝ a ∧ ‖(resolvent a t) wv‖ ≤ Cv)
    (hne : inner ℝ (gu + wu) gu + inner ℝ (gv + wv) gv ≠ (0 : ℝ)) :
    Tendsto (fun t : ℝ => GaloisForLFunctions.RHTower.suzukiDefectAngle
        (inner ℝ (gu + wu) ((resolvent a t) (gu + wu)))
        (inner ℝ (gv + wv) ((resolvent a t) (gv + wv))))
      (𝓝[<] lam0)
      (𝓝 ((inner ℝ (gu + wu) gu - inner ℝ (gv + wv) gv)
        / (inner ℝ (gu + wu) gu + inner ℝ (gv + wv) gv))) := by
  simpa only [suzukiDefectAngle_resolvent] using
    tendsto_resolventPolarization_ground hgu hgv hu hv hne

end RHTower
