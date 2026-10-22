import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant

/-!
# Finite-mass rigidity of the four-dimensional Teukolsky parity split

The Birmingham--Mokhtari scalar and vector gravitational potentials have an exact factorization
of their `d = 4` parity gap.  With `Q` the paired horizon eigenvalue, `x = omega_4 M / r`, and
`u = r^(2 : ℕ) / l^(2 : ℕ)`, the gap is

`6 x (2 (Q+2) + 3 (Q+u+3) x + 6 x^(2 : ℕ)) / (Q+2+3x)^(2 : ℕ)`.

Consequently positive mass fixes its sign throughout the physical chamber `Q,u >= 0`; the split
cannot cross into the negative chiral chamber at finite mass.  Removing the linear mass jet also
gives an exact second-jet completion.  On the theta continuum `Q = 1/4 + xi^(2 : ℕ)`, its massless
curvature is strictly positive for exterior radius `u >= 1`.

These statements use the full rational potential, rather than a perturbative truncation.  They
control the radial parity factor only; they do not assert nonlinear angular source incidence with
the gravitational Jost divisor.

**[LITERATURE-DERIVED] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Exact finite-mass scalar/vector parity gap in the `d=4` Birmingham--Mokhtari potential. -/
theorem d4ParitySplit_eq_finiteMassFactor
    (Q x u : ℝ) (hden : Q + 2 + 3 * x ≠ 0) :
    d4ScalarBracket Q x u - d4VectorBracket Q x =
      6 * x * (2 * (Q + 2) + 3 * (Q + u + 3) * x + 6 * x ^ (2 : ℕ)) /
        (Q + 2 + 3 * x) ^ (2 : ℕ) := by
  let d : ℝ := Q + 2 + 3 * x
  have hd : d ≠ 0 := by simpa [d] using hden
  have hd2 : d ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hd
  change d4ScalarU Q x u / (16 * d ^ (2 : ℕ)) - (Q - 3 * x) =
    6 * x * (2 * (Q + 2) + 3 * (Q + u + 3) * x + 6 * x ^ (2 : ℕ)) / d ^ (2 : ℕ)
  apply (eq_div_iff hd2).2
  field_simp [hd2]
  dsimp [d, d4ScalarU]
  ring

/-- Positive mass gives a strict scalar-over-vector parity gap throughout the physical chamber. -/
theorem d4ParitySplit_pos_of_physical
    {Q x u : ℝ} (hQ : 0 ≤ Q) (hx : 0 < x) (hu : 0 ≤ u) :
    0 < d4ScalarBracket Q x u - d4VectorBracket Q x := by
  have hden : 0 < Q + 2 + 3 * x := by linarith
  rw [d4ParitySplit_eq_finiteMassFactor Q x u (ne_of_gt hden)]
  positivity

/-- On nonnegative mass, the finite parity gap vanishes only at the massless background. -/
theorem d4ParitySplit_eq_zero_iff_massless
    {Q x u : ℝ} (hQ : 0 ≤ Q) (hx : 0 ≤ x) (hu : 0 ≤ u) :
    d4ScalarBracket Q x u - d4VectorBracket Q x = 0 ↔ x = 0 := by
  constructor
  · intro hgap
    rcases hx.eq_or_lt with rfl | hxpos
    · rfl
    · exact False.elim ((ne_of_gt (d4ParitySplit_pos_of_physical hQ hxpos hu)) hgap)
  · rintro rfl
    have hQ2 : Q + 2 ≠ 0 := by linarith
    rw [d4ScalarBracket_zero hQ2]
    simp [d4VectorBracket]

/-- Continuous completion of the parity gap after removing its linear mass jet and two powers
of the mass coordinate. -/
def d4ParitySplitSecondJetCompletion (Q u x : ℝ) : ℝ :=
  (18 * (Q + 2) * (Q + u - 1) + 36 * (Q - 1) * x) /
    ((Q + 2) * (Q + 2 + 3 * x) ^ (2 : ℕ))

/-- Exact second-jet factorization of the full finite-mass parity gap. -/
theorem d4ParitySplit_sub_linear_eq_secondJet
    (Q x u : ℝ) (hQ2 : Q + 2 ≠ 0) (hden : Q + 2 + 3 * x ≠ 0) :
    d4ScalarBracket Q x u - d4VectorBracket Q x -
        (12 / (Q + 2)) * x =
      x ^ (2 : ℕ) * d4ParitySplitSecondJetCompletion Q u x := by
  rw [d4ParitySplit_eq_finiteMassFactor Q x u hden]
  unfold d4ParitySplitSecondJetCompletion
  let d : ℝ := Q + 2 + 3 * x
  have hd : d ≠ 0 := by simpa [d] using hden
  change
    6 * x * (2 * (Q + 2) + 3 * (Q + u + 3) * x + 6 * x ^ (2 : ℕ)) / d ^ (2 : ℕ) -
        12 / (Q + 2) * x =
      x ^ (2 : ℕ) * ((18 * (Q + 2) * (Q + u - 1) + 36 * (Q - 1) * x) /
        ((Q + 2) * d ^ (2 : ℕ)))
  field_simp [hQ2, hd]
  dsimp [d]
  ring

/-- The completed second Taylor coefficient at the massless background. -/
theorem d4ParitySplitSecondJetCompletion_zero
    (Q u : ℝ) (hQ2 : Q + 2 ≠ 0) :
    d4ParitySplitSecondJetCompletion Q u 0 =
      18 * (Q + u - 1) / (Q + 2) ^ (2 : ℕ) := by
  unfold d4ParitySplitSecondJetCompletion
  field_simp [hQ2]
  ring

/-- The second-jet completion is continuous at the massless background. -/
theorem continuousAt_d4ParitySplitSecondJetCompletion_zero
    (Q u : ℝ) (hQ2 : Q + 2 ≠ 0) :
    ContinuousAt (d4ParitySplitSecondJetCompletion Q u) 0 := by
  unfold d4ParitySplitSecondJetCompletion
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  exact mul_ne_zero hQ2 (pow_ne_zero 2 (by simpa using hQ2))

/-- Twice the completed second Taylor coefficient of the parity gap at zero mass. -/
def d4SecondMassParityCurvature (Q u : ℝ) : ℝ :=
  36 * (Q + u - 1) / (Q + 2) ^ (2 : ℕ)

theorem d4SecondMassParityCurvature_eq_twice_completion
    (Q u : ℝ) (hQ2 : Q + 2 ≠ 0) :
    d4SecondMassParityCurvature Q u =
      2 * d4ParitySplitSecondJetCompletion Q u 0 := by
  rw [d4ParitySplitSecondJetCompletion_zero Q u hQ2]
  unfold d4SecondMassParityCurvature
  ring

/-- Physical theta-continuum second mass curvature is strictly positive in the exterior. -/
theorem d4SecondMassParityCurvature_pos_physical
    (xi u : ℝ) (hu : 1 ≤ u) :
    0 < d4SecondMassParityCurvature (d4ThetaPhysicalAngularQ xi) u := by
  unfold d4SecondMassParityCurvature d4ThetaPhysicalAngularQ
  have hQ : 0 < (1 / 4 : ℝ) + xi ^ (2 : ℕ) := by positivity
  have hnum : 0 < (1 / 4 : ℝ) + xi ^ (2 : ℕ) + u - 1 := by linarith
  exact div_pos (mul_pos (by norm_num) hnum) (sq_pos_of_pos (by linarith))

end

end RHTower
