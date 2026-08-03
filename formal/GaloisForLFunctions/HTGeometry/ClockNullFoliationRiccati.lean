import GaloisForLFunctions.HTGeometry.ClockNullFrameEquivalence

/-!
# Null foliations are not an obstruction in two dimensions

The foliation reconstruction requires the foliation to be non-null: its carré du champ `Γ(φ,φ)`
must be nowhere zero. A potential constant along a **null** direction therefore falls outside it.

In two dimensions that apparent gap is empty, and for a different reason. Writing `ξ`, `η` for the
two null coordinates, the exponent `w = F(ξ) + η` has

`□w = 0`,  `Γ(w,w) = -4F'(ξ)`,

so `-(□w + Γ(w,w)) = 4F'(ξ)` is a potential constant along the null direction `ξ`, carried by the
globally nonvanishing probe `e^{w}`. Every such potential is therefore in the Riccati class and is
determined outright.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

/-! ## Components of the null covectors -/

theorem nullCovectors_zero_zero : nullCovectors 0 0 = 1 := by
  rw [nullCovectors_zero]
  simp

theorem nullCovectors_zero_one : nullCovectors 0 1 = 1 := by
  rw [nullCovectors_zero]
  simp [Ne.symm fin_zero_ne_one]

theorem nullCovectors_one_zero : nullCovectors 1 0 = 1 := by
  rw [nullCovectors_one]
  simp

theorem nullCovectors_one_one : nullCovectors 1 1 = -1 := by
  rw [nullCovectors_one]
  simp [Ne.symm fin_zero_ne_one]

/-- The chain rule for a composite with a linear phase, in the shape the computations below meet
it. -/
theorem coordPartial_phaseComp {d : ℕ} {n : Fin (d + 1) → ℝ} {w : ℝ → ℝ} {c : ℝ}
    {x : Fin (d + 1) → ℝ} (hw : HasDerivAt w c (covectorPhase n x)) (i : Fin (d + 1)) :
    coordPartial i (fun y => w (covectorPhase n y)) x = n i * c :=
  coordPartial_covectorLift hw i

/-! ## The null exponent -/

/-- Exponent of the probe adapted to a null foliation: `F(ξ) + η`. -/
noncomputable def nullExponent (F : ℝ → ℝ) : (Fin (1 + 1) → ℝ) → ℝ := fun y =>
  F (covectorPhase (nullCovectors 0) y) + covectorPhase (nullCovectors 1) y

theorem contDiff_nullExponent {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (nullExponent F) :=
  (hF.comp (contDiff_covectorPhase _)).add (contDiff_covectorPhase _)

theorem coordPartial_nullExponent {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (i : Fin (1 + 1))
    (x : Fin (1 + 1) → ℝ) :
    coordPartial i (nullExponent F) x
      = nullCovectors 0 i * deriv F (covectorPhase (nullCovectors 0) x)
        + nullCovectors 1 i := by
  have hd : HasDerivAt F (deriv F (covectorPhase (nullCovectors 0) x))
      (covectorPhase (nullCovectors 0) x) :=
    (hF.differentiable (by simp) _).hasDerivAt
  have hfd : DifferentiableAt ℝ (fun y => F (covectorPhase (nullCovectors 0) y)) x :=
    (hd.comp_hasFDerivAt x
      (differentiableAt_of_contDiff_infty (contDiff_covectorPhase _) x).hasFDerivAt).differentiableAt
  have hgd : DifferentiableAt ℝ (covectorPhase (nullCovectors 1)) x :=
    differentiableAt_of_contDiff_infty (contDiff_covectorPhase _) x
  show coordPartial i
      (fun y => F (covectorPhase (nullCovectors 0) y) + covectorPhase (nullCovectors 1) y) x = _
  rw [coordPartial_add hfd hgd i, coordPartial_phaseComp hd i, coordPartial_covectorPhase]

theorem coordPartial_nullExponent_fun {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (i : Fin (1 + 1)) :
    coordPartial i (nullExponent F)
      = fun y => nullCovectors 0 i * deriv F (covectorPhase (nullCovectors 0) y)
        + nullCovectors 1 i := by
  funext y
  exact coordPartial_nullExponent hF i y

theorem coordPartial_sq_nullExponent {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (i : Fin (1 + 1))
    (x : Fin (1 + 1) → ℝ) :
    coordPartial i (coordPartial i (nullExponent F)) x
      = nullCovectors 0 i
        * (nullCovectors 0 i * deriv (deriv F) (covectorPhase (nullCovectors 0) x)) := by
  have hF' : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  have hd : HasDerivAt (deriv F) (deriv (deriv F) (covectorPhase (nullCovectors 0) x))
      (covectorPhase (nullCovectors 0) x) :=
    (hF'.differentiable (by simp) _).hasDerivAt
  have hfd : DifferentiableAt ℝ (fun y => deriv F (covectorPhase (nullCovectors 0) y)) x :=
    (hd.comp_hasFDerivAt x
      (differentiableAt_of_contDiff_infty (contDiff_covectorPhase _) x).hasFDerivAt).differentiableAt
  rw [coordPartial_nullExponent_fun hF i]
  show coordPartial i
      (fun y => nullCovectors 0 i * deriv F (covectorPhase (nullCovectors 0) y)
        + nullCovectors 1 i) x = _
  rw [coordPartial_add (hfd.const_mul _) (differentiableAt_const _) i,
    coordPartial_const_mul hfd _ i, coordPartial_phaseComp hd i,
    coordPartial_const i (nullCovectors 1 i) x]
  ring

/-! ## The two invariants -/

theorem gradPair_nullExponent {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (x : Fin (1 + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.gradPair
        (nullExponent F) (nullExponent F) x
      = -4 * deriv F (covectorPhase (nullCovectors 0) x) := by
  rw [ofSignature_gradPair, Fin.sum_univ_two, coordPartial_nullExponent hF,
    coordPartial_nullExponent hF, nullEps_zero, nullEps_one, nullCovectors_zero_zero,
    nullCovectors_zero_one, nullCovectors_one_zero, nullCovectors_one_one]
  ring

theorem dalembert_nullExponent {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (x : Fin (1 + 1) → ℝ) :
    (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert
        (nullExponent F) x = 0 := by
  rw [SmoothPseudoMetric.ofSignature_dalembert nullEps nullEps_ne_zero (contDiff_nullExponent hF) x,
    Fin.sum_univ_two, coordPartial_sq_nullExponent hF, coordPartial_sq_nullExponent hF,
    nullEps_zero, nullEps_one, nullCovectors_zero_zero, nullCovectors_zero_one]
  ring

/-! ## Null-foliated potentials are Riccati -/

/-- **The potential adapted to a null foliation.** -/
theorem chartRiccatiPotential_nullExponent {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    chartRiccatiPotential (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart
        (nullExponent F)
      = fun x => 4 * deriv F (covectorPhase (nullCovectors 0) x) := by
  funext x
  rw [chartRiccatiPotential, dalembert_nullExponent hF, gradPair_nullExponent hF]
  ring

/-- **Every potential constant along a null direction is determined.** The globally nonvanishing
probe is `e^{F(ξ) + η}`, so the non-nullity hypothesis of the foliation reconstruction is not an
obstruction in two dimensions. -/
theorem noCommonZero_nullFoliated {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    NoCommonZero (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert
      (fun x => 4 * deriv F (covectorPhase (nullCovectors 0) x)) := by
  rw [← chartRiccatiPotential_nullExponent hF]
  exact noCommonZero_chartRiccatiPotential _ (contDiff_nullExponent hF)

/-- **Determination of a null-foliated potential.** -/
theorem potential_eq_nullFoliated {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {other : (Fin (1 + 1) → ℝ) → ℝ}
    (hother : ∀ u ∈ solutionSet
        (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert
        (fun x => 4 * deriv F (covectorPhase (nullCovectors 0) x)),
      SolvesPotentialWave
        (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert other u) :
    other = fun x => 4 * deriv F (covectorPhase (nullCovectors 0) x) :=
  potential_eq_of_noCommonZero (noCommonZero_nullFoliated hF) hother

end GaloisForLFunctions.HTGeometry
