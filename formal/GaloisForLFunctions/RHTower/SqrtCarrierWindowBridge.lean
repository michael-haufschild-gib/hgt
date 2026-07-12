import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import GaloisForLFunctions.RHTower.DpolyBallFloor

/-!
# The certified carrier floor in the window machinery's native shapes

The certified floor for the square-dilated Möbius carrier holds at every point of the
half-plane `re z ≥ 1/2 + ε` under a purely numeric gap condition.  This file re-emits it
in each interface shape the tree's floor/window machinery consumes:

* `RHTower.sqrtCarrier_certified_floor_line` — the floor at every point of the vertical
  line `re = σ` for any `σ ≥ 1/2 + ε`;
* `RHTower.sqrtCarrier_good_height_cofinal` — the cofinal good-heights format of
  `FloorFailureCofinal`: above every bound there is a height with the floor (indeed all
  heights carry it);
* `RHTower.sqrtCarrier_weighted_dpoly_floor` — the detection-native form: in the
  σ-weighted one-dimensional coefficient convention of `SecondMoment`/
  `DetectionSecondMoment` (`dpoly` with coefficients `sqrtMoebiusCoeff n · n^(-σ)`), the
  carrier is bounded away from zero at every height — the mollified-carrier
  nondegeneracy datum the window machinery places against detection windows;
* `RHTower.sqrtCarrier_strip_floor` — the sub-abscissa extension: through
  `dpoly2_chart_floor`, a finite variation budget pushes the certified floor to real
  part `σ₁`, including `σ₁` below `1/2 + ε`, at every height;
* `RHTower.sqrtCarrier_ball_floor` — the chart form: through `dpoly2_ball_floor`, the
  certified center floor spreads to any closed ball around a center on the half-plane,
  with the log-Lipschitz budget — floors on annulus charts crossing below the abscissa.
-/

noncomputable section

namespace RHTower

open Complex Metric

private theorem re_add_mul_I (σ τ : ℝ) : ((σ : ℂ) + (τ : ℂ) * I).re = σ := by simp

/-- The certified floor on the whole vertical line `re = σ`, `σ ≥ 1/2 + ε`. -/
theorem sqrtCarrier_certified_floor_line {ε t₀ : ℝ} (hε : 0 < ε) {σ : ℝ}
    (hσ : 1 / 2 + ε ≤ σ) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) (τ : ℝ) :
    t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ :=
  sqrtCarrier_certified_floor hε (by rw [re_add_mul_I]; exact hσ) hN hgap

/-- **Good heights, `FloorFailureCofinal` format.**  At every real part `σ ≥ 1/2 + ε` the
certified floor holds at cofinally many heights — the `hline` datum of the cofinal floor
machinery, here without any density hypothesis. -/
theorem sqrtCarrier_good_height_cofinal {ε t₀ : ℝ} (hε : 0 < ε) {σ : ℝ}
    (hσ : 1 / 2 + ε ≤ σ) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) :
    ∀ M : ℝ, ∃ τ, M < τ ∧
      t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ :=
  fun M => ⟨M + 1, by linarith,
    sqrtCarrier_certified_floor_line hε hσ hN hgap (M + 1)⟩

/-- **Detection-native nondegeneracy.**  In the σ-weighted one-dimensional coefficient
convention of the second-moment/detection stack, the weighted square-dilated carrier is
bounded away from zero at every height `τ` — the carrier floor datum for window
placement against the mollified detection polynomial. -/
theorem sqrtCarrier_weighted_dpoly_floor {ε t₀ : ℝ} (hε : 0 < ε) {σ : ℝ}
    (hσ : 1 / 2 + ε ≤ σ) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) (τ : ℝ) :
    t₀ < ‖dpoly (fun n => sqrtMoebiusCoeff n * (n : ℝ) ^ (-σ)) (Finset.Icc 1 N) τ‖ := by
  have h := sqrtCarrier_certified_floor_line hε hσ hN hgap τ
  rwa [dpoly2_line_eq _ _ (fun _ hn => (Finset.mem_Icc.mp hn).1) σ τ] at h

/-- **Sub-abscissa strip floor.**  A finite variation budget extends the certified floor
from the line `re = 1/2 + ε` to real part `σ₁` — including `σ₁ < 1/2 + ε`, below the
carrier's abscissa of convergence — at every height. -/
theorem sqrtCarrier_strip_floor {ε t₀ ε₁ : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) (σ₁ : ℝ)
    (hbudget : ∑ n ∈ Finset.Icc 1 N, |sqrtMoebiusCoeff n| *
        |(n : ℝ) ^ (-σ₁) - (n : ℝ) ^ (-(1 / 2 + ε))| ≤ t₀ - ε₁) (τ : ℝ) :
    ε₁ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ₁ : ℂ) + (τ : ℂ) * I)‖ :=
  dpoly2_chart_floor sqrtMoebiusCoeff (Finset.Icc 1 N)
    (fun _ hn => (Finset.mem_Icc.mp hn).1) σ₁ (1 / 2 + ε) τ t₀ ε₁
    (sqrtCarrier_certified_floor_line hε le_rfl hN hgap τ) hbudget

/-- **Chart/ball floor.**  The certified center floor spreads to any closed ball around a
center on the half-plane, with the log-Lipschitz budget of `DpolyBallFloor` — carrier
floors on annulus charts, including charts crossing below the abscissa. -/
theorem sqrtCarrier_ball_floor {ε t₀ ε₁ R : ℝ} (hε : 0 < ε) {z₀ : ℂ}
    (hz₀ : 1 / 2 + ε ≤ z₀.re) {N : ℕ} (hN : 1 ≤ Nat.sqrt N) (hR : 0 ≤ R)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε))
    (hbudget : (∑ n ∈ Finset.Icc 1 N, |sqrtMoebiusCoeff n| *
        (Real.log n * (n : ℝ) ^ (-(z₀.re - R)))) * R ≤ t₀ - ε₁) :
    ∀ z ∈ closedBall z₀ R, ε₁ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖ :=
  dpoly2_ball_floor sqrtMoebiusCoeff (Finset.Icc 1 N)
    (fun _ hn => (Finset.mem_Icc.mp hn).1) hR
    (sqrtCarrier_certified_floor hε hz₀ hN hgap) hbudget

end RHTower
