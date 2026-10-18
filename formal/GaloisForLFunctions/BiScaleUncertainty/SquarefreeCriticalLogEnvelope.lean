import GaloisForLFunctions.BiScaleUncertainty.SquarefreeCancellationTransfer
import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyMellin

/-!
# An unconditional critical envelope for the literal squarefree discrepancy

The corpus's logarithmic Mertens saving pays the two tails of the exact
squarefree divisor identity. The resulting critical source has a reciprocal
logarithmic-coordinate envelope, with no auxiliary weight in the source.
-/

noncomputable section
open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace RHTower.SquarefreeDiscrepancy

private theorem discrepancy_density_bounds :
    0 ≤ Sieve.squarefreeDensity ∧ Sieve.squarefreeDensity ≤ 1 := by
  rw [Sieve.squarefreeDensity_eq]
  constructor
  · positivity
  · have hp := Real.pi_gt_three
    rw [div_le_iff₀ (pow_pos Real.pi_pos 2)]
    nlinarith

private theorem abs_error_le_count_error_add_one {x : ℝ} (hx : 0 ≤ x) :
    |error x| ≤
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ)^2) - Sieve.squarefreeDensity * (⌊x⌋₊ : ℝ)| + 1 := by
  have hf := Nat.floor_le hx
  have hgap := Nat.lt_floor_add_one x
  obtain ⟨hρ0, hρ1⟩ := discrepancy_density_bounds
  have hdiff : |Sieve.squarefreeDensity * ((⌊x⌋₊ : ℝ) - x)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hρ0, abs_of_nonpos (sub_nonpos.mpr hf)]
    have h := mul_le_mul_of_nonneg_right hρ1 (sub_nonneg.mpr hf)
    nlinarith
  have he : error x =
      ((∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ)^2) - Sieve.squarefreeDensity * (⌊x⌋₊ : ℝ)) +
        Sieve.squarefreeDensity * ((⌊x⌋₊ : ℝ) - x) := by
    simp only [error, count]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hdiff)

/-- The unweighted physical source has an unconditional reciprocal-clock tail.
The arithmetic constant comes from the proved logarithmic Mertens estimate. -/
theorem eventually_abs_error_exp_critical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      |error (Real.exp t)| * Real.exp (-t / 2) ≤ C / t := by
  obtain ⟨B, hB, hrate⟩ := Sieve.deningerMertensM_log_pow_rate 2
  obtain ⟨K, hK⟩ := eventually_atTop.mp hrate
  refine ⟨2 + 192 * B, by positivity, ?_⟩
  have hdom : ∀ᶠ t : ℝ in atTop, 2 * t ≤ Real.exp (t / 4) := by
    simpa only [Real.rpow_one, one_mul, div_eq_mul_inv, mul_comm] using
      GaloisForLFunctions.HTGeometry.eventually_mul_rpow_le_exp_rpow 2
        (c := (1 : ℝ) / 4) (δ := 1) (p := 1) (by norm_num) (by norm_num)
  have hexp : Tendsto (fun t : ℝ => Real.exp (t / 4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  filter_upwards [hdom, eventually_ge_atTop (4 : ℝ),
    hexp.eventually_ge_atTop (K : ℝ)] with t hdom ht4 hKt
  have ht : 0 < t := by linarith
  let y := Real.exp (t / 2)
  let q := y / t
  let D := ⌊q⌋₊
  let N := ⌊Real.exp t⌋₊
  have hy : 0 < y := Real.exp_pos _
  have hq : 0 < q := div_pos hy ht
  have he4 : 1 ≤ Real.exp (t / 4) := by linarith
  have hy4 : y = Real.exp (t / 4)^2 := by
    dsimp [y]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hq4 : 2 * Real.exp (t / 4) ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ ht, hy4]
    nlinarith [Real.exp_pos (t / 4)]
  have hq2 : 2 ≤ q := by linarith
  have hDle : (D : ℝ) ≤ q := Nat.floor_le hq.le
  have hDgap : q < (D : ℝ) + 1 := Nat.lt_floor_add_one q
  have hDhalf : q / 2 ≤ (D : ℝ) := by linarith
  have hD4 : Real.exp (t / 4) ≤ (D : ℝ) := by linarith
  have hD1 : 1 ≤ D := by exact_mod_cast he4.trans hD4
  have hDK : K ≤ D := by exact_mod_cast hKt.trans hD4
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hNt : (N : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
  have hDN : D ≤ N := by
    apply (Nat.le_floor_iff (Real.exp_pos t).le).mpr
    apply hDle.trans
    calc
      q = y / t := rfl
      _ ≤ y := div_le_self hy.le (by linarith)
      _ ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
  let δ := 16 * B / t^2
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hM : ∀ n : ℕ, D ≤ n → |Sieve.mertensM n| ≤ δ * n := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (hD1.trans hn)
    have hlog : t / 4 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_exp (t / 4)]
      exact Real.log_le_log (Real.exp_pos _) (hD4.trans (by exact_mod_cast hn))
    have hlogpos : 0 < Real.log (n : ℝ) := by linarith
    calc
      |Sieve.mertensM n| ≤ B * n / Real.log (n : ℝ)^2 := hK n (hDK.trans hn)
      _ ≤ B * n / (t / 4)^2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      _ = δ * n := by dsimp [δ]; field_simp; ring
  have hcount := abs_squarefree_count_sub_le_of_mertens hD1 hDN hδ hM
  have herror := (abs_error_le_count_error_add_one (Real.exp_pos t).le).trans
    (add_le_add hcount le_rfl)
  have hmain : |error (Real.exp t)| ≤ (1 + 192 * B) * y / t + 1 := by
    have htail : 6 * δ * (N : ℝ) / D ≤ 192 * B * y / t := by
      calc
        _ ≤ 6 * δ * Real.exp t / D := by
          apply div_le_div_of_nonneg_right _ hD0.le
          exact mul_le_mul_of_nonneg_left hNt (by positivity)
        _ ≤ 6 * δ * Real.exp t / (q / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hDhalf
        _ = _ := by
          have he : Real.exp t = y^2 := by
            dsimp [y]
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
          rw [he]
          dsimp [δ, q]
          field_simp
          ring
    have hhead : (D : ℝ) ≤ y / t := hDle
    dsimp only [N] at hcount
    change |error (Real.exp t)| ≤ (D : ℝ) + 6 * δ * (N : ℝ) / D + 1 at herror
    calc
      _ ≤ (D : ℝ) + 6 * δ * (N : ℝ) / D + 1 := herror
      _ ≤ y / t + 192 * B * y / t + 1 := by linarith
      _ = _ := by ring
  have hycancel : y * Real.exp (-t / 2) = 1 := by
    dsimp [y]
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hyge : t ≤ y := by
    have h := mul_le_mul_of_nonneg_right hq2 ht.le
    dsimp [q] at h
    rw [div_mul_cancel₀ _ ht.ne'] at h
    linarith
  have hsmall : Real.exp (-t / 2) ≤ 1 / t := by
    rw [le_div_iff₀ ht]
    have h := mul_le_mul_of_nonneg_right hyge (Real.exp_pos (-t / 2)).le
    nlinarith [hycancel]
  have hbound := mul_le_mul_of_nonneg_right hmain (Real.exp_pos (-t / 2)).le
  calc
    _ ≤ ((1 + 192 * B) * y / t + 1) * Real.exp (-t / 2) := hbound
    _ = (1 + 192 * B) / t + Real.exp (-t / 2) := by
      calc
        _ = ((1 + 192 * B) / t) * (y * Real.exp (-t / 2)) + Real.exp (-t / 2) := by ring
        _ = _ := by rw [hycancel]; ring
    _ ≤ (1 + 192 * B) / t + 1 / t := add_le_add le_rfl hsmall
    _ = _ := by ring

end RHTower.SquarefreeDiscrepancy
