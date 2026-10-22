import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinSignedMaassWhittakerTail
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.PathConnected

/-!
# Local summable bounds for the literal angular derivative family

The arithmetic coefficient is the actual completed Eisenstein divisor sum.
Every fixed index power is summable with every positive exponential rate.
Consequently the signed Fourier--Bessel family has a locally uniform summable
majorant on every compact positive-height interval, without a restriction on
the complex spectral parameters.  These are bounds for the full infinite
series, not a finite-mode approximation.
-/

open Complex Real Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMAngularSeries
noncomputable section

/-- The literal arithmetic coefficient with a fixed Fourier derivative degree. -/
def coefficient (u : ℂ) (d N : ℕ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ * ((N + 1 : ℕ) : ℂ) ^ d

/-- Actual signed Fourier--Bessel summand, closed under both coordinate derivatives. -/
def term (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool) (N : ℕ) (z : Fin 2 → ℝ) : ℂ :=
  coefficient u d N * d4BMCompletedEisensteinFourierPhase negative N (z 0) *
    (Real.rpow (z 1) a : ℂ) * modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * z 1) nu

/-- The complete infinite angular family. -/
def value (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool) (z : Fin 2 → ℝ) : ℂ :=
  ∑' N : ℕ, term u nu a d negative N z

/-- Arithmetic admission at every positive exponential rate. -/
theorem coefficient_weighted_summable (u : ℂ) (d : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    Summable (fun N : ℕ => ‖coefficient u d N‖ * Real.exp (-(((N : ℝ) + 1) * delta))) := by
  let r : ℝ := 3 * |u.re| + 1 + d
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hb := (summable_natSucc_rpow_exp_neg_and_tsum_le hr hdelta).1
  apply Summable.of_nonneg_of_le (fun N => by positivity) _ hb
  intro N
  have hn : 0 < (N : ℝ) + 1 := by positivity
  have hc : ‖coefficient u d N‖ ≤ ((N : ℝ) + 1) ^ r := by
    rw [coefficient, norm_mul, norm_pow, Complex.norm_natCast]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ((N : ℝ) + 1) ^ (3 * |u.re| + 1) * ((N : ℝ) + 1) ^ d := by
        gcongr
        simpa only [Nat.cast_add, Nat.cast_one] using
          d4BM_norm_completedEisensteinWhittakerCoefficient_le u ⟨N + 1, by omega⟩
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_add hn]
  have he : Real.exp (-(((N : ℝ) + 1) * delta)) ≤ Real.exp (-((N : ℝ) * delta)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul hc he (by positivity) (by positivity)

/-- A fixed Bessel-order constant on a positive-height neighborhood. -/
def besselBound (nu : ℂ) (l : ℝ) : ℝ :=
  Real.exp (‖nu‖ ^ 2 / (2 * l)) * Real.sqrt (2 * Real.pi / l)

/-- The actual Bessel carrier has a common exponential bound at every positive lower height. -/
theorem bessel_local_bound (nu : ℂ) (l : ℝ) (hl : 0 < l)
    (N : ℕ) (Y : ℝ) (hY : l ≤ Y) :
    ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) nu‖ ≤
      besselBound nu l * Real.exp (-(((N : ℝ) + 1) * l)) := by
  let s : {x : ℝ // 0 < x} := ⟨2 * Real.pi * ((N : ℝ) + 1) * Y, by
    have : 0 < Y := hl.trans_le hY
    positivity⟩
  have hn : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hp : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hsN : ((N : ℝ) + 1) * l ≤ (s : ℝ) := by
    dsimp [s]
    have hq : 0 ≤ ((N : ℝ) + 1) * Y := mul_nonneg (by positivity) (hl.trans_le hY).le
    nlinarith [mul_le_mul_of_nonneg_left hY (by positivity : 0 ≤ (N : ℝ) + 1),
      mul_le_mul_of_nonneg_right hp hq]
  have hsl : l ≤ (s : ℝ) := by nlinarith
  have ho : ‖nu‖ ^ 2 / (2 * (s : ℝ)) ≤ ‖nu‖ ^ 2 / (2 * l) := by
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have hsq : Real.sqrt (2 * Real.pi / (s : ℝ)) ≤ Real.sqrt (2 * Real.pi / l) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left (by positivity) hl hsl
  have he : Real.exp (-(s : ℝ)) ≤ Real.exp (-(((N : ℝ) + 1) * l)) :=
    Real.exp_le_exp.mpr (neg_le_neg hsN)
  calc
    _ ≤ Real.exp (-(s : ℝ)) * Real.exp (‖nu‖ ^ 2 / (2 * (s : ℝ))) *
        Real.sqrt (2 * Real.pi / (s : ℝ)) := d4BM_norm_modifiedBesselKOrder_le s nu
    _ ≤ Real.exp (-(((N : ℝ) + 1) * l)) * Real.exp (‖nu‖ ^ 2 / (2 * l)) *
        Real.sqrt (2 * Real.pi / l) := by gcongr
    _ = _ := by dsimp [besselBound]; ring

/-- Locally uniform summable admission of every term in the actual derivative family. -/
theorem term_local_majorant (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (l h : ℝ) (hl : 0 < l) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ N z, l ≤ z 1 → z 1 ≤ h →
      ‖term u nu a d negative N z‖ ≤ M N := by
  have hc : ContinuousOn (fun y : ℝ => (Real.rpow y a : ℂ)) (Icc l h) := by
    intro y hy
    exact (Complex.ofRealCLM.continuous.continuousAt.comp
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hl.trans_le hy.1))
        (n := 0)).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hKB : 0 ≤ besselBound nu l := by unfold besselBound; positivity
  refine ⟨fun N => (B * besselBound nu l) *
    (‖coefficient u d N‖ * Real.exp (-(((N : ℝ) + 1) * l))),
    (coefficient_weighted_summable u d l hl).mul_left _, ?_⟩
  intro N z hz0 hz1
  have hy : ‖(Real.rpow (z 1) a : ℂ)‖ ≤ B := (hC (z 1) ⟨hz0, hz1⟩).trans (le_max_left _ _)
  have hk := bessel_local_bound nu l hl N (z 1) hz0
  rw [term, norm_mul, norm_mul, norm_mul,
    d4BM_norm_completedEisensteinFourierPhase, mul_one]
  calc
    _ ≤ ‖coefficient u d N‖ * B *
        (besselBound nu l * Real.exp (-(((N : ℝ) + 1) * l))) := by gcongr
    _ = _ := by ring

/-- Absolute convergence of the complete derivative family at every positive height. -/
theorem term_summable (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) : Summable (fun N => term u nu a d negative N z) := by
  obtain ⟨M, hM, hb⟩ := term_local_majorant u nu a d negative (z 1) (z 1) hz
  exact Summable.of_norm_bounded hM (fun N => hb N z le_rfl le_rfl)

end
end RHTower.D4BMAngularSeries
