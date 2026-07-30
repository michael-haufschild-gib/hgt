import GaloisForLFunctions.HTGeometry.LocalTemporalConstraintCausalityLaw
import GaloisForLFunctions.HTGeometry.AnalyticOrderRigidityLaw

/-!
# Analytic locality creates unresolved temporal directions

This file closes the analytic bridge between a locality onset and the
observer-time constraint filtration.  If every two-factor rectangle response
is `O (‖g‖ ^ r)`, then every corresponding Taylor character vanishes below
order `r`.  The full rectangle span therefore lies in the unresolved temporal
kernel, with an exact rank lower bound including all spectator configurations.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Four-branch analytic response of a spectral rectangle. -/
def rectangleAnalyticResponse
    {A B C : Type*}
    (f : A × B × C → ℂ → ℂ)
    (a₀ : A) (b₀ : B) (j : RectangleContrastIndex A B C a₀ b₀)
    (g : ℂ) : ℂ :=
  f (j.left, j.right, j.background) g +
    f (a₀, b₀, j.background) g -
    f (j.left, b₀, j.background) g -
    f (a₀, j.right, j.background) g

/-- Taylor series of a spectral rectangle response. -/
def rectangleFPowerSeries
    {A B C : Type*}
    (series : A × B × C → FormalMultilinearSeries ℂ ℂ ℂ)
    (a₀ : A) (b₀ : B) (j : RectangleContrastIndex A B C a₀ b₀) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  series (j.left, j.right, j.background) +
    series (a₀, b₀, j.background) -
    series (j.left, b₀, j.background) -
    series (a₀, j.right, j.background)

theorem hasFPowerSeriesAt_rectangleFPowerSeries
    {A B C : Type*}
    (f : A × B × C → ℂ → ℂ)
    (series : A × B × C → FormalMultilinearSeries ℂ ℂ ℂ)
    (hseries : ∀ x, HasFPowerSeriesAt (f x) (series x) 0)
    (a₀ : A) (b₀ : B) (j : RectangleContrastIndex A B C a₀ b₀) :
    HasFPowerSeriesAt
      (rectangleAnalyticResponse f a₀ b₀ j)
      (rectangleFPowerSeries series a₀ b₀ j) 0 := by
  simpa [rectangleAnalyticResponse, rectangleFPowerSeries] using!
    (((hseries (j.left, j.right, j.background)).add
      (hseries (a₀, b₀, j.background))).sub
      (hseries (j.left, b₀, j.background))).sub
      (hseries (a₀, j.right, j.background))

/-- Scalar spectral jet obtained by evaluating each homogeneous Taylor
coefficient on unit directions. -/
def analyticSpectralJet
    {X : Type*}
    (series : X → FormalMultilinearSeries ℂ ℂ ℂ) :
    ℕ → X → ℂ :=
  fun n x => series x n (fun _ => 1)

theorem rectangleFPowerSeries_apply_eq_zero_below_onset
    {A B C : Type*}
    (f : A × B × C → ℂ → ℂ)
    (series : A × B × C → FormalMultilinearSeries ℂ ℂ ℂ)
    (hseries : ∀ x, HasFPowerSeriesAt (f x) (series x) 0)
    (a₀ : A) (b₀ : B) (r : ℕ)
    (hO : ∀ j : RectangleContrastIndex A B C a₀ b₀,
      rectangleAnalyticResponse f a₀ b₀ j
        =O[𝓝 0] fun g : ℂ => ‖g‖ ^ r)
    (j : RectangleContrastIndex A B C a₀ b₀) (n : Fin r) :
    rectangleFPowerSeries series a₀ b₀ j n = 0 := by
  by_cases hz : rectangleFPowerSeries series a₀ b₀ j = 0
  · rw [hz]
    rfl
  · apply FormalMultilinearSeries.apply_eq_zero_of_lt_order
    have hord :
        r ≤ (rectangleFPowerSeries series a₀ b₀ j).order :=
      le_fpowerSeries_order_of_isBigO_norm_pow
        (hasFPowerSeriesAt_rectangleFPowerSeries
          f series hseries a₀ b₀ j)
        hz r (hO j)
    exact n.isLt.trans_le hord

/-- Every rectangle character vanishes on every analytic spectral jet below
the locality onset. -/
theorem analyticRectangleJet_vanishes_below_onset
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : A × B × C → ℂ → ℂ)
    (series : A × B × C → FormalMultilinearSeries ℂ ℂ ℂ)
    (hseries : ∀ x, HasFPowerSeriesAt (f x) (series x) 0)
    (a₀ : A) (b₀ : B) (r : ℕ)
    (hO : ∀ j : RectangleContrastIndex A B C a₀ b₀,
      rectangleAnalyticResponse f a₀ b₀ j
        =O[𝓝 0] fun g : ℂ => ‖g‖ ^ r) :
    ∀ (j : RectangleContrastIndex A B C a₀ b₀) (n : Fin r),
      ∑ x, ((rectangleContrastRelation (R := ℚ) a₀ b₀ j x : ℚ) : ℂ) *
        analyticSpectralJet series n x = 0 := by
  intro j n
  have hzero :=
    rectangleFPowerSeries_apply_eq_zero_below_onset
      f series hseries a₀ b₀ r hO j n
  have heval := congrArg
    (fun p : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ =>
      p (fun _ => 1)) hzero
  rw [← Finsupp.sum_fintype
    (rectangleContrastRelation (R := ℚ) a₀ b₀ j)
    (fun x a => (a : ℂ) * analyticSpectralJet series n x)
    (fun _ => by simp)]
  simp only [rectangleContrastRelation]
  rw [Finsupp.sum_sub_index (by intros; push_cast; ring),
    Finsupp.sum_sub_index (by intros; push_cast; ring),
    Finsupp.sum_add_index' (by intros; simp) (by intros; push_cast; ring)]
  simpa [rectangleFPowerSeries, analyticSpectralJet] using! heval

/-- **Analytic locality-to-time theorem.** Rectangle onset at order `r`
forces the full independent rectangle family into the temporal constraint
kernel below `r`. -/
theorem analyticRectangleConstraint_finrank_lower_bound
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : A × B × C → ℂ → ℂ)
    (series : A × B × C → FormalMultilinearSeries ℂ ℂ ℂ)
    (hseries : ∀ x, HasFPowerSeriesAt (f x) (series x) 0)
    (a₀ : A) (b₀ : B) (r : ℕ)
    (hO : ∀ j : RectangleContrastIndex A B C a₀ b₀,
      rectangleAnalyticResponse f a₀ b₀ j
        =O[𝓝 0] fun g : ℂ => ‖g‖ ^ r) :
    (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C ≤
      Module.finrank ℚ
        (rationalSpectralConstraintSpace
          (analyticSpectralJet series) r) := by
  exact rectangleConstraint_finrank_lower_bound a₀ b₀
    (analyticSpectralJet series) r
    (analyticRectangleJet_vanishes_below_onset
      f series hseries a₀ b₀ r hO)

end

end GaloisForLFunctions.HTGeometry
