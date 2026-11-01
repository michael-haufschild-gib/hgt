import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity
import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeOfTheCompleteWeilFamily
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleConductorMinimizesTheCompletedEnergy
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapPositivityAtEveryOverlap

/-!
# The limit structure of the resolution family and its degeneration

At a fixed overlap `c` the complete Weil family has a limit as the horizon grows: the normalized
Ramanujan vectors `r_m` are quasimodes of `W_{φ,c,N}` with eigenvalues the completed conductor
energies `E_m(c)` (CACT). The **limit structure** is the Ramanujan-graded form
`Σ_m E_m(c) y_m²` (`limitForm`).

* **Polarized by an identity** (`limitForm_nonneg`): the shells repay every conductor, so each
  `E_m(c)` is a positive Fourier integral `(2/(Mφ(m))) Σ_{(a,m)=1} (m/a) ∫_{ac/m}^∞ |φ̂(2πt)|²`.
* **The pole conductor is the ground state** (`ground_mul_sum_sq_le_limitForm`): `E_1(c) ≤ E_m(c)`,
  so the limit's gap on all vectors is the ground energy `E_1(c)`.
* **The limit degenerates along every growing schedule** (`tendsto_limitForm_comp`): for every
  overlap schedule `c_N → ∞` and every finite conductor profile, the limit form tends to `0`.
  The polarization of the limit carries no gap into the RH regime; there the sign is decided by
  the corrections that carry the zeros.
* **Inherited in the universal regime, degenerate in the RH regime** (`tiltedSpline_inheritance_and_degeneration`):
  for the tilted spline the form dominates a polynomial floor `K/c⁷` throughout `1 ≤ c ≤ (log N)^α`,
  `α < 1/9`, while at the RH-complete schedules `2(log N)^β`, `β > 1/4`, the ground energy tends to `0`
  and positivity is RH.
* **The `SL₂`-type structure is blind on the hyperplane**: the pole pair, the Krein state of the
  boost–successor plane, can be added with any weight without changing the Hodge index on the pole
  hyperplane (`RenormalizedIntersectionTheory.renormalizedHodgeIndex_add_polePair_iff`). The
  hyperbolic plane supplies the one archimedean square and nothing on `v₁^⊥`.
* **Shells**: on the boost hyperplane the glued archimedean state is Weil's dilation form plus the
  squares of the half-line shells at every resolution
  (`AdelicKreinGeometry.hermQuad_gram_weilArchState_shell`). The universal-regime decompositions
  degenerate to `0`, so the dilation form at the edge is not their limit.
-/

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.EdgeHodgeTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- **The limit structure**: the Ramanujan-graded form `Σ_{m ∈ s} E_m(c) y_m²`. -/
def limitForm (φ : ℝ → ℝ) (c : ℝ) (s : Finset ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ m ∈ s, completedConductorEnergy φ c m * y m ^ 2

/-- **The limit is the fixed-overlap limit of the family**: the normalized Ramanujan vectors are
quasimodes with eigenvalues the completed conductor energies. -/
theorem tendsto_ramanujan_quasimode {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℝ} (hc : 0 < c) {m : ℕ}
    (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N)
        (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) :=
  CriticalArithmeticCorrelationTheory.tendsto_completeWeilMatrix_ramanujan_quasimode_norm
    hφ.contDiff hφ.supp hφ.sq_pos hc hm

/-- **The limit is polarized by the repayment identity.** -/
theorem limitForm_nonneg {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℝ} (hc : 0 < c) {s : Finset ℕ}
    (hs : ∀ m ∈ s, 0 < m) (y : ℕ → ℝ) : 0 ≤ limitForm φ c s y :=
  sum_nonneg fun m hm => mul_nonneg
    (completedConductorEnergy_nonneg hφ.contDiff hφ.supp hφ.sq_pos hc (hs m hm)) (sq_nonneg _)

/-- **The pole conductor is the ground state of the limit.** -/
theorem ground_mul_sum_sq_le_limitForm {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℝ} (hc : 0 < c)
    {s : Finset ℕ} (hs : ∀ m ∈ s, 0 < m) (y : ℕ → ℝ) :
    completedConductorEnergy φ c 1 * ∑ m ∈ s, y m ^ 2 ≤ limitForm φ c s y := by
  rw [limitForm, mul_sum]
  exact sum_le_sum fun m hm => mul_le_mul_of_nonneg_right
    (completedConductorEnergy_one_le hφ.contDiff hφ.supp hφ.sq_pos hc (hs m hm)) (sq_nonneg _)

/-- **The limit degenerates along every growing schedule.** -/
theorem tendsto_limitForm_comp {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (s : Finset ℕ) (y : ℕ → ℝ) :
    Tendsto (fun N => limitForm φ (c N) s y) atTop (𝓝 0) := by
  have h : Tendsto (fun N => ∑ m ∈ s, completedConductorEnergy φ (c N) m * y m ^ 2) atTop
      (𝓝 (∑ m ∈ s, 0 * y m ^ 2)) :=
    tendsto_finsetSum _ fun m _ =>
      (((tendsto_completedConductorEnergy_atTop hφ.contDiff hφ.supp hφ.sq_pos m).comp hc).mul
        tendsto_const_nhds)
  simpa only [limitForm, zero_mul, sum_const_zero] using h

/-- The ground energy vanishes along every growing schedule. -/
theorem tendsto_ground_comp {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) :
    Tendsto (fun N => completedConductorEnergy φ (c N) 1) atTop (𝓝 0) :=
  (tendsto_completedConductorEnergy_atTop hφ.contDiff hφ.supp hφ.sq_pos 1).comp hc

theorem tendsto_two_mul_rpow_log {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun N : ℕ => 2 * Real.log N ^ β) atTop atTop :=
  ((tendsto_rpow_atTop hβ).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop
    two_pos

/-- **Inherited in the universal regime, degenerate in the RH regime.** For the tilted spline:
throughout `1 ≤ c ≤ (log N)^α`, `α < 1/9`, the form dominates the polynomial floor `K/(2c⁷)`; at the
schedules `2(log N)^β`, `β > 1/4`, the ground energy of the limit tends to `0` and eventual
positivity is RH. -/
theorem tiltedSpline_inheritance_and_degeneration {α β : ℝ} (hα : 0 < α)
    (hα' : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent) (hβ : 1 / 4 < β) :
    (∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (CriticalArithmeticCorrelationTheory.tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) *
          ‖x‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N x) ∧
    Tendsto (fun N : ℕ => completedConductorEnergy tiltedUnitSpline (2 * Real.log N ^ β) 1) atTop
      (𝓝 0) ∧
    (RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, PositiveAt tiltedUnitSpline (2 * Real.log N ^ β) N) :=
  ⟨CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
      hα hα',
    tendsto_ground_comp admissible_tiltedUnitSpline (tendsto_two_mul_rpow_log (by linarith)),
    riemannHypothesis_iff_eventually_positiveAt_log admissible_tiltedUnitSpline hβ⟩

end GaloisForLFunctions.EdgeHodgeTheory

#print axioms GaloisForLFunctions.EdgeHodgeTheory.tiltedSpline_inheritance_and_degeneration
