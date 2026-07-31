import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewDistribution
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewHilbert

/-!
# Suzuki's screw function: hull, value law, and parity law

Suzuki's screw function of a multiplicity-weighted family of positive ordinates is the
summable-spectrum screw series with weights `2 m / gamma ^ 2`. Applying the relation-hull
laws to that weight family determines its complete cofinal behaviour without assuming
simplicity of the divisor or rational independence of the ordinates:

* the lower limit vanishes;
* the upper limit is the maximal energy of the relation hull;
* every value between them recurs, approximately with bounded gaps and exactly on interior
  levels;
* the uniform time law converges weakly to a limiting distribution supported exactly on
  that interval;
* the absolute upper bound `4 ∑ m / gamma ^ 2` is attained precisely when every finite
  integer relation among the ordinates has even total coefficient.

The last item replaces rational independence by an exact parity criterion, which is
strictly weaker: a trivial relation lattice satisfies it automatically.
-/

open Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

variable {G : Type*}

/-- Screw weight of an ordinate carrying analytic multiplicity. -/
def suzukiScrewWeight (mult : G → ℕ) (gamma : G → ℝ) : G → ℝ :=
  fun g => 2 * (mult g : ℝ) / (gamma g) ^ 2

/-- Suzuki's screw function of a multiplicity-weighted positive ordinate family. -/
def suzukiScrewFunction (mult : G → ℕ) (gamma : G → ℝ) : ℝ → ℝ :=
  screwSeries (suzukiScrewWeight mult gamma) gamma

theorem suzukiScrewFunction_apply (mult : G → ℕ) (gamma : G → ℝ) (t : ℝ) :
    suzukiScrewFunction mult gamma t =
      ∑' g, 2 * (mult g : ℝ) / (gamma g) ^ 2 * (1 - Real.cos (gamma g * t)) := rfl

theorem suzukiScrewWeight_pos {mult : G → ℕ} {gamma : G → ℝ}
    (hmult : ∀ g, 0 < mult g) (hgamma : ∀ g, gamma g ≠ 0) (g : G) :
    0 < suzukiScrewWeight mult gamma g := by
  have hm : (0 : ℝ) < (mult g : ℝ) := by exact_mod_cast hmult g
  have hg : (0 : ℝ) < (gamma g) ^ 2 := pow_pos (abs_pos.mpr (hgamma g)) 2 |>.trans_eq
    (by rw [sq_abs])
  exact div_pos (by linarith) hg

theorem suzukiScrewWeight_nonneg {mult : G → ℕ} {gamma : G → ℝ} (g : G) :
    0 ≤ suzukiScrewWeight mult gamma g := by
  have hm : (0 : ℝ) ≤ (mult g : ℝ) := Nat.cast_nonneg _
  have hg : (0 : ℝ) ≤ (gamma g) ^ 2 := sq_nonneg _
  exact div_nonneg (by linarith) hg

section Laws

variable [Countable G] {mult : G → ℕ} {gamma : G → ℝ}
  (hsum : Summable (suzukiScrewWeight mult gamma))

include hsum

/-- **Vanishing lower limit of Suzuki's screw function.** -/
theorem suzukiScrewFunction_liminf_eq_zero :
    liminf (suzukiScrewFunction mult gamma) atTop = 0 :=
  screwSeries_liminf_eq_zero (fun g => suzukiScrewWeight_nonneg g) hsum

/-- **Exact upper limit of Suzuki's screw function**: the maximal energy of the relation
hull of the ordinates. -/
theorem suzukiScrewFunction_limsup_eq :
    limsup (suzukiScrewFunction mult gamma) atTop =
      screwHullMax (suzukiScrewWeight mult gamma) gamma :=
  screwSeries_limsup_eq_screwHullMax (fun g => suzukiScrewWeight_nonneg g) hsum

/-- **No-gap cofinal value law for Suzuki's screw function.** -/
theorem closure_suzukiScrewFunction_image_Ici (T : ℝ) :
    closure (suzukiScrewFunction mult gamma '' Set.Ici T) =
      Set.Icc 0 (screwHullMax (suzukiScrewWeight mult gamma) gamma) :=
  closure_screwSeries_image_Ici (fun g => suzukiScrewWeight_nonneg g) hsum T

/-- Every value of the cofinal range is approached with bounded gaps. -/
theorem exists_window_suzukiScrewFunction_near
    {y : ℝ} (hy : y ∈ Set.Icc 0 (screwHullMax (suzukiScrewWeight mult gamma) gamma))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧
      ∀ tau : ℝ, ∃ t ∈ Set.Icc tau (tau + L),
        |suzukiScrewFunction mult gamma t - y| < ε :=
  exists_window_screwSeries_near (fun g => suzukiScrewWeight_nonneg g) hsum hy hε

/-- Every interior value is attained exactly with bounded gaps. -/
theorem exists_window_suzukiScrewFunction_eq
    {y : ℝ} (hy0 : 0 < y)
    (hyM : y < screwHullMax (suzukiScrewWeight mult gamma) gamma) :
    ∃ L : ℝ, 0 < L ∧
      ∀ tau : ℝ, ∃ t ∈ Set.Icc tau (tau + L), suzukiScrewFunction mult gamma t = y :=
  exists_window_screwSeries_eq (fun g => suzukiScrewWeight_nonneg g) hsum hy0 hyM

/-- **Limiting value distribution of Suzuki's screw function.** -/
theorem tendsto_timeAverage_suzukiScrewFunction (phi : BoundedContinuousFunction ℝ ℝ) :
    Tendsto
      (fun A : ℝ =>
        ∫ u in (0 : ℝ)..1, phi (suzukiScrewFunction mult gamma (A * (2 * u - 1))))
      atTop
      (𝓝 (∫ y, phi y
        ∂(screwValueLaw (fun g => suzukiScrewWeight_nonneg g) hsum gamma : Measure ℝ))) :=
  tendsto_timeAverage_screwSeries (fun g => suzukiScrewWeight_nonneg g) hsum gamma phi

/-- The limiting distribution is supported exactly on the cofinal value interval. -/
theorem suzukiScrewFunction_law_support :
    (screwValueLaw (fun g => suzukiScrewWeight_nonneg (mult := mult) (gamma := gamma) g)
        hsum gamma : Measure ℝ).support =
      Set.Icc 0 (screwHullMax (suzukiScrewWeight mult gamma) gamma) :=
  screwValueLaw_support (fun g => suzukiScrewWeight_nonneg g) hsum gamma

/-- **Parity law for Suzuki's screw function.** The absolute upper bound
`4 ∑ m / gamma ^ 2` is the true upper limit exactly when every finite integer relation
among the ordinates has even total coefficient. -/
theorem suzukiScrewFunction_limsup_eq_absolute_bound_iff
    (hmult : ∀ g, 0 < mult g) (hgamma : ∀ g, gamma g ≠ 0) :
    limsup (suzukiScrewFunction mult gamma) atTop =
        2 * ∑' g, suzukiScrewWeight mult gamma g ↔
      ∀ n : G →₀ ℤ, n ∈ screwRelationLattice gamma → Even (n.sum fun _ m => m) := by
  rw [suzukiScrewFunction_limsup_eq hsum]
  exact screwHullMax_eq_two_mul_tsum_iff (suzukiScrewWeight_pos hmult hgamma) hsum

/-- Rational independence of the ordinates is sufficient for the parity criterion, hence
strictly stronger than needed. -/
theorem suzukiScrewFunction_limsup_eq_absolute_bound_of_independent
    (hmult : ∀ g, 0 < mult g) (hgamma : ∀ g, gamma g ≠ 0)
    (hindep : ∀ n : G →₀ ℤ, n ∈ screwRelationLattice gamma → n = 0) :
    limsup (suzukiScrewFunction mult gamma) atTop =
      2 * ∑' g, suzukiScrewWeight mult gamma g :=
  (suzukiScrewFunction_limsup_eq_absolute_bound_iff hsum hmult hgamma).mpr
    (parity_of_screwRelationLattice_trivial hindep)

omit [Countable G] in
/-- **Hilbert screw property.** Squared Hilbert chords along Suzuki's screw line depend
only on the time difference and reproduce the screw function itself. -/
theorem sq_norm_suzukiScrewEmbed_sub (t u : ℝ) :
    ‖screwEmbed (fun g => suzukiScrewWeight_nonneg (mult := mult) (gamma := gamma) g) hsum
          (screwPhase gamma t) -
        screwEmbed (fun g => suzukiScrewWeight_nonneg (mult := mult) (gamma := gamma) g) hsum
          (screwPhase gamma u)‖ ^ 2 =
      suzukiScrewFunction mult gamma (t - u) :=
  sq_norm_screwEmbed_screwPhase_sub (fun g => suzukiScrewWeight_nonneg g) hsum gamma t u

end Laws

end

end RHTower
