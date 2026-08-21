import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Local smoothness of the Boyer--Lindquist Kerr--Newman coefficient field

The totalized Boyer--Lindquist formula is not globally smooth at the zeros of
its denominators. This file records the honest coordinate locus where `Sigma`,
`Delta`, and `sin(theta)` are nonzero, and proves that every metric coefficient
is smooth there. It is a regularity layer for future local curvature work, not
yet a local pseudo-metric or an Einstein--Maxwell field-equation proof.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

noncomputable section

/-- Boyer--Lindquist metric field on the coordinate tuple `(t, r, theta, phi)`. -/
def kerrNewmanBoyerLindquistCoordinateMetric
    (mass spin charge : ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun x => kerrNewmanBoyerLindquistMetric mass spin charge (x 1) (x 2)

/-- Coordinate locus where the Boyer--Lindquist denominators and angular orbit factor are
nonzero. -/
def kerrNewmanBoyerLindquistSmoothLocus
    (mass spin charge : ℝ) : Set (Fin 4 → ℝ) :=
  {x | kerrNewmanSigma spin (x 1) (x 2) ≠ 0 ∧
    kerrNewmanDelta mass spin charge (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}

/-- The radial coordinate is smooth. -/
theorem contDiff_kerrNewmanBoyerLindquist_radius :
    ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => x 1) :=
  contDiff_apply ℝ ℝ 1

/-- The polar coordinate is smooth. -/
theorem contDiff_kerrNewmanBoyerLindquist_polar :
    ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => x 2) :=
  contDiff_apply ℝ ℝ 2

/-- The Boyer--Lindquist `Sigma` field is smooth on all coordinates. -/
theorem contDiff_kerrNewmanBoyerLindquist_sigma
    (spin : ℝ) :
    ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => kerrNewmanSigma spin (x 1) (x 2)) := by
  unfold kerrNewmanSigma
  exact (contDiff_kerrNewmanBoyerLindquist_radius.pow 2).add
    (contDiff_const.mul
      ((Real.contDiff_cos.comp contDiff_kerrNewmanBoyerLindquist_polar).pow 2))

/-- The Boyer--Lindquist `Delta` field is smooth on all coordinates. -/
theorem contDiff_kerrNewmanBoyerLindquist_delta
    (mass spin charge : ℝ) :
    ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => kerrNewmanDelta mass spin charge (x 1)) := by
  have hlinear : ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => 2 * mass * x 1) :=
    (contDiff_const.mul contDiff_const).mul contDiff_kerrNewmanBoyerLindquist_radius
  unfold kerrNewmanDelta
  exact ((contDiff_kerrNewmanBoyerLindquist_radius.pow 2).sub hlinear).add contDiff_const |>.add
    contDiff_const

/-- The angular factor `sin(theta)^2` is smooth on all coordinates. -/
theorem contDiff_kerrNewmanBoyerLindquist_sinSq :
    ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => Real.sin (x 2) ^ 2) :=
  (Real.contDiff_sin.comp contDiff_kerrNewmanBoyerLindquist_polar).pow 2

/-- Every Boyer--Lindquist Kerr--Newman metric coefficient is smooth on the honest coordinate
locus. -/
theorem contDiffOn_kerrNewmanBoyerLindquistCoordinateMetric
    (mass spin charge : ℝ) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => kerrNewmanBoyerLindquistCoordinateMetric mass spin charge x i j)
      (kerrNewmanBoyerLindquistSmoothLocus mass spin charge) := by
  let U := kerrNewmanBoyerLindquistSmoothLocus mass spin charge
  change ContDiffOn ℝ ∞
    (fun x => kerrNewmanBoyerLindquistCoordinateMetric mass spin charge x i j) U
  have hSigmaNe : ∀ x ∈ U, kerrNewmanSigma spin (x 1) (x 2) ≠ 0 := fun x hx => hx.1
  have hDeltaNe : ∀ x ∈ U, kerrNewmanDelta mass spin charge (x 1) ≠ 0 := fun x hx => hx.2.1
  have hSigma : ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ =>
      kerrNewmanSigma spin (x 1) (x 2)) U :=
    (contDiff_kerrNewmanBoyerLindquist_sigma spin).contDiffOn
  have hDelta : ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ =>
      kerrNewmanDelta mass spin charge (x 1)) U :=
    (contDiff_kerrNewmanBoyerLindquist_delta mass spin charge).contDiffOn
  have hSinSq : ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ => Real.sin (x 2) ^ 2) U :=
    contDiff_kerrNewmanBoyerLindquist_sinSq.contDiffOn
  have hCross : ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ => 2 * mass * x 1 - charge ^ 2) U :=
    ((contDiff_const.mul contDiff_const).mul contDiff_kerrNewmanBoyerLindquist_radius).sub
      contDiff_const |>.contDiffOn
  have hRadialSqPlusSpinSq : ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ =>
      (x 1 ^ 2 + spin ^ 2)) U :=
    ((contDiff_kerrNewmanBoyerLindquist_radius.pow 2).add contDiff_const).contDiffOn
  fin_cases i <;> fin_cases j
  · change ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ =>
      -(kerrNewmanDelta mass spin charge (x 1) - spin ^ 2 * Real.sin (x 2) ^ 2) /
        kerrNewmanSigma spin (x 1) (x 2)) U
    exact ((hDelta.sub ((contDiffOn_const (c := spin ^ 2)).mul hSinSq)).neg.div hSigma hSigmaNe)
  · exact contDiffOn_const
  · exact contDiffOn_const
  · change ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ =>
      -(spin * Real.sin (x 2) ^ 2 * (2 * mass * x 1 - charge ^ 2)) /
        kerrNewmanSigma spin (x 1) (x 2)) U
    exact ((((contDiffOn_const (c := spin)).mul hSinSq).mul hCross).neg.div hSigma hSigmaNe)
  · exact contDiffOn_const
  · change ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ =>
      kerrNewmanSigma spin (x 1) (x 2) / kerrNewmanDelta mass spin charge (x 1)) U
    exact hSigma.div hDelta hDeltaNe
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · simpa [kerrNewmanBoyerLindquistCoordinateMetric, kerrNewmanBoyerLindquistMetric,
      kerrNewmanKillingBlock] using hSigma
  · exact contDiffOn_const
  · change ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ =>
      -(spin * Real.sin (x 2) ^ 2 * (2 * mass * x 1 - charge ^ 2)) /
        kerrNewmanSigma spin (x 1) (x 2)) U
    exact ((((contDiffOn_const (c := spin)).mul hSinSq).mul hCross).neg.div hSigma hSigmaNe)
  · exact contDiffOn_const
  · exact contDiffOn_const
  · change ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ =>
      Real.sin (x 2) ^ 2 *
          ((x 1 ^ 2 + spin ^ 2) ^ 2 - spin ^ 2 *
            kerrNewmanDelta mass spin charge (x 1) * Real.sin (x 2) ^ 2) /
        kerrNewmanSigma spin (x 1) (x 2)) U
    exact (hSinSq.mul ((hRadialSqPlusSpinSq.pow 2).sub
      (((contDiffOn_const (c := spin ^ 2)).mul hDelta).mul hSinSq))).div hSigma hSigmaNe

end

end GaloisForLFunctions.HTGeometry
