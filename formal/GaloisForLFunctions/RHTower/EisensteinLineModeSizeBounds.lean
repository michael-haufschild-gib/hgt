import GaloisForLFunctions.RHTower.EisensteinCuspTailImaginaryOrderBound
import GaloisForLFunctions.RHTower.BesselKImaginaryOrderPowerSaving

/-!
# Mode sizes of the completed Eisenstein series on the line

The `N`-th Fourier mode of `E*(·, 1/2 + it)` at height `Y` has modulus
`‖σ_{2it}(N+1)‖ · √Y · ‖K_{2π(N+1)Y}(it)‖`, independent of the horizontal coordinate and of the
sign of the frequency.  This module bounds the `ℓ¹` and `ℓ²` sums of these mode sizes over all
frequencies, at every height `Y ≥ 1/2` and every `t ≥ 2`:

* modes with `2π(N+1)Y ≤ 2t` (there are at most `t/(πY)` of them) are bounded by the power
  saving `‖K_{iτ}(x)‖ ≤ 420 e^{-πτ/2} τ^{-1/3}` and the divisor-sum polylog bounds;
* modes with `2π(N+1)Y > 2t` are bounded by `‖K_{iτ}(x)‖ ≤ e · e^{-x}`, which then carries a
  factor `e^{-7t/4}` (`ℓ¹`) or `e^{-7t/2}` (`ℓ²`) together with exponential decay in `Y`.

The `ℓ²` sum is `O(t^{1/3} log³ t · e^{-πt})` uniformly in `Y`, and the `ℓ¹` sum is
`O(t^{2/3} log t · e^{-πt/2} / √Y)`; these are the inputs of the mean-square bound for the
Eisenstein source of the on-line clock.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Geometric tails with polynomial weights -/

/-- `Σ_N (N+1) e^{-a(N+1)} ≤ 4/a²`, with summability. -/
theorem summable_succ_mul_exp_neg_and_tsum_le {a : ℝ} (ha : 0 < a) :
    Summable (fun N : ℕ => ((N : ℝ) + 1) * Real.exp (-(a * ((N : ℝ) + 1)))) ∧
      ∑' N : ℕ, ((N : ℝ) + 1) * Real.exp (-(a * ((N : ℝ) + 1))) ≤ 4 / a ^ 2 := by
  set r : ℝ := Real.exp (-(a / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have := Real.exp_lt_exp.mpr (show -(a / 2) < 0 by linarith)
    simpa [hr] using this
  have hterm : ∀ N : ℕ, ((N : ℝ) + 1) * Real.exp (-(a * ((N : ℝ) + 1))) ≤ (2 / a) * r ^ (N + 1) := by
    intro N
    have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    have h1 : (N : ℝ) + 1 ≤ (2 / a) * Real.exp (a * ((N : ℝ) + 1) / 2) := by
      have := Real.add_one_le_exp (a * ((N : ℝ) + 1) / 2)
      calc (N : ℝ) + 1 = (2 / a) * (a * ((N : ℝ) + 1) / 2) := by field_simp
        _ ≤ (2 / a) * Real.exp (a * ((N : ℝ) + 1) / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
    have h2 : r ^ (N + 1) = Real.exp (-(a * ((N : ℝ) + 1) / 2)) := by
      rw [hr, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc ((N : ℝ) + 1) * Real.exp (-(a * ((N : ℝ) + 1)))
        ≤ (2 / a) * Real.exp (a * ((N : ℝ) + 1) / 2) * Real.exp (-(a * ((N : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = (2 / a) * r ^ (N + 1) := by
          rw [h2, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hgeom : Summable (fun N : ℕ => (2 / a) * r ^ (N + 1)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left ((2 / a) * r)
    refine this.congr fun N => ?_
    ring
  have hsum : Summable (fun N : ℕ => ((N : ℝ) + 1) * Real.exp (-(a * ((N : ℝ) + 1)))) :=
    Summable.of_nonneg_of_le (fun N => by positivity) hterm hgeom
  refine ⟨hsum, ?_⟩
  have htsum : ∑' N : ℕ, (2 / a) * r ^ (N + 1) = (2 / a) * (r * (1 - r)⁻¹) := by
    rw [show (fun N : ℕ => (2 / a) * r ^ (N + 1)) = fun N : ℕ => ((2 / a) * r) * r ^ N by
      funext N; ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; ring
  have hrr : r * (1 - r)⁻¹ ≤ 2 / a := by
    have hpos : 0 < 1 - r := by linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hpos ha]
    -- `r a ≤ 2 (1 - r)`, i.e. `r (a + 2) ≤ 2`; from `e^{a/2} ≥ 1 + a/2`, `r ≤ 1/(1 + a/2)`.
    have hexp : 1 + a / 2 ≤ Real.exp (a / 2) := by
      have := Real.add_one_le_exp (a / 2); linarith
    have hrinv : r * Real.exp (a / 2) = 1 := by
      rw [hr, ← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_left hexp hr0]
  calc ∑' N : ℕ, ((N : ℝ) + 1) * Real.exp (-(a * ((N : ℝ) + 1)))
      ≤ ∑' N : ℕ, (2 / a) * r ^ (N + 1) := hsum.tsum_le_tsum hterm hgeom
    _ = (2 / a) * (r * (1 - r)⁻¹) := htsum
    _ ≤ (2 / a) * (2 / a) := mul_le_mul_of_nonneg_left hrr (by positivity)
    _ = 4 / a ^ 2 := by field_simp; ring

/-- `Σ_N (N+1)² e^{-a(N+1)} ≤ 64/a³`, with summability. -/
theorem summable_succ_sq_mul_exp_neg_and_tsum_le {a : ℝ} (ha : 0 < a) :
    Summable (fun N : ℕ => ((N : ℝ) + 1) ^ 2 * Real.exp (-(a * ((N : ℝ) + 1)))) ∧
      ∑' N : ℕ, ((N : ℝ) + 1) ^ 2 * Real.exp (-(a * ((N : ℝ) + 1))) ≤ 64 / a ^ 3 := by
  have hhalf := summable_succ_mul_exp_neg_and_tsum_le (a := a / 2) (by positivity)
  have hterm : ∀ N : ℕ, ((N : ℝ) + 1) ^ 2 * Real.exp (-(a * ((N : ℝ) + 1))) ≤
      (4 / a) * (((N : ℝ) + 1) * Real.exp (-(a / 2 * ((N : ℝ) + 1)))) := by
    intro N
    have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    have h1 : (N : ℝ) + 1 ≤ (4 / a) * Real.exp (a * ((N : ℝ) + 1) / 4) := by
      have := Real.add_one_le_exp (a * ((N : ℝ) + 1) / 4)
      calc (N : ℝ) + 1 = (4 / a) * (a * ((N : ℝ) + 1) / 4) := by field_simp
        _ ≤ (4 / a) * Real.exp (a * ((N : ℝ) + 1) / 4) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
    have hsplit : Real.exp (-(a * ((N : ℝ) + 1))) =
        Real.exp (-(a * ((N : ℝ) + 1) / 4)) * Real.exp (-(a * ((N : ℝ) + 1) / 4)) *
          Real.exp (-(a / 2 * ((N : ℝ) + 1))) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hE : Real.exp (a * ((N : ℝ) + 1) / 4) * Real.exp (-(a * ((N : ℝ) + 1) / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ((N : ℝ) + 1) ^ 2 * Real.exp (-(a * ((N : ℝ) + 1)))
        = ((N : ℝ) + 1) * ((N : ℝ) + 1) * Real.exp (-(a * ((N : ℝ) + 1))) := by ring
      _ ≤ ((4 / a) * Real.exp (a * ((N : ℝ) + 1) / 4)) * ((N : ℝ) + 1) *
          Real.exp (-(a * ((N : ℝ) + 1))) := by gcongr
      _ = (4 / a) * (((N : ℝ) + 1) * Real.exp (-(a / 2 * ((N : ℝ) + 1)))) *
          (Real.exp (a * ((N : ℝ) + 1) / 4) * Real.exp (-(a * ((N : ℝ) + 1) / 4))) *
          Real.exp (-(a * ((N : ℝ) + 1) / 4)) := by rw [hsplit]; ring
      _ ≤ (4 / a) * (((N : ℝ) + 1) * Real.exp (-(a / 2 * ((N : ℝ) + 1)))) * 1 * 1 := by
          rw [hE]
          gcongr
          exact Real.exp_le_one_iff.mpr (by nlinarith)
      _ = (4 / a) * (((N : ℝ) + 1) * Real.exp (-(a / 2 * ((N : ℝ) + 1)))) := by ring
  have hmaj := hhalf.1.mul_left (4 / a)
  have hsum : Summable (fun N : ℕ => ((N : ℝ) + 1) ^ 2 * Real.exp (-(a * ((N : ℝ) + 1)))) :=
    Summable.of_nonneg_of_le (fun N => by positivity) hterm hmaj
  refine ⟨hsum, ?_⟩
  calc ∑' N : ℕ, ((N : ℝ) + 1) ^ 2 * Real.exp (-(a * ((N : ℝ) + 1)))
      ≤ ∑' N : ℕ, (4 / a) * (((N : ℝ) + 1) * Real.exp (-(a / 2 * ((N : ℝ) + 1)))) :=
        hsum.tsum_le_tsum hterm hmaj
    _ = (4 / a) * ∑' N : ℕ, ((N : ℝ) + 1) * Real.exp (-(a / 2 * ((N : ℝ) + 1))) := tsum_mul_left
    _ ≤ (4 / a) * (4 / (a / 2) ^ 2) := mul_le_mul_of_nonneg_left hhalf.2 (by positivity)
    _ = 64 / a ^ 3 := by field_simp; ring

/-! ## Mode sizes -/

/-- The modulus of the `N`-th Fourier mode of `E*(·, 1/2 + it)` at height `Y`. -/
def eisensteinLineModeSize (t Y : ℝ) (N : ℕ) : ℝ :=
  ‖d4BMCompletedEisensteinWhittakerCoefficient ((t : ℂ) * I) ⟨N + 1, by omega⟩‖ * Real.sqrt Y *
    ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖

theorem eisensteinLineModeSize_nonneg (t Y : ℝ) (N : ℕ) : 0 ≤ eisensteinLineModeSize t Y N := by
  unfold eisensteinLineModeSize; positivity

theorem norm_eisensteinLineTailTerm_eq_modeSize (t : ℝ) (negative : Bool) (x Y : ℝ) (N : ℕ) :
    ‖eisensteinLineTailTerm t negative x Y N‖ = eisensteinLineModeSize t Y N := by
  unfold eisensteinLineTailTerm eisensteinLineModeSize
  simp only [pow_zero, mul_one]
  rw [norm_mul, norm_mul, norm_mul, d4BM_norm_completedEisensteinFourierPhase, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg Y)]

/-- The uniform majorant `d(N+1) √Y e · e^{-2π(N+1)Y}`, valid at every height `Y ≥ 1/2`. -/
theorem eisensteinLineModeSize_le_exp {t Y : ℝ} (hY : 1 / 2 ≤ Y) (N : ℕ) :
    eisensteinLineModeSize t Y N ≤
      ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        (Real.exp 1 * Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y))) := by
  unfold eisensteinLineModeSize
  have hx : 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) * Y := one_le_two_pi_mul_succ_mul hY N
  have hK := norm_modifiedBesselKOrder_I_mul_le_exp hx t
  have hc := norm_whittakerCoefficient_I_mul_le t ⟨N + 1, by omega⟩
  have hs : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  calc _ ≤ ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖ := by gcongr
    _ ≤ _ := by gcongr

/-- The power-saving majorant `d(N+1) √Y · 420 e^{-πt/2} t^{-1/3}`, valid at every mode. -/
theorem eisensteinLineModeSize_le_powerSaving {t Y : ℝ} (ht : 2 ≤ t) (hY : 0 < Y) (N : ℕ) :
    eisensteinLineModeSize t Y N ≤
      ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        (420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ))) := by
  unfold eisensteinLineModeSize
  have hx : 0 < 2 * Real.pi * ((N : ℝ) + 1) * Y := by positivity
  have hK := norm_modifiedBesselKOrder_I_mul_le_powerSaving ht hx
  have hc := norm_whittakerCoefficient_I_mul_le t ⟨N + 1, by omega⟩
  have hs : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  calc _ ≤ ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖ := by gcongr
    _ ≤ _ := by gcongr

theorem summable_eisensteinLineModeSize {t Y : ℝ} (hY : 1 / 2 ≤ Y) :
    Summable (eisensteinLineModeSize t Y) := by
  have hY0 : 0 ≤ Y := by linarith
  have hmaj := (summable_succ_mul_exp_neg_and_tsum_le (a := Real.pi) Real.pi_pos).1
  refine Summable.of_nonneg_of_le (eisensteinLineModeSize_nonneg t Y)
    (fun N => (eisensteinLineModeSize_le_exp hY N).trans ?_)
    ((hmaj.mul_left (Real.sqrt Y * Real.exp 1)))
  have hd : ((N + 1 : ℕ).divisors.card : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast Nat.card_divisors_le_self (N + 1)
  have hexp : Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)) ≤
      Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
    apply Real.exp_le_exp.mpr
    have hp : (0 : ℝ) ≤ Real.pi * ((N : ℝ) + 1) := by positivity
    have h2Y : (1 : ℝ) ≤ 2 * Y := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2Y hp]
  calc ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        (Real.exp 1 * Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)))
      ≤ ((N : ℝ) + 1) * Real.sqrt Y * (Real.exp 1 * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) := by
        gcongr
    _ = Real.sqrt Y * Real.exp 1 * (((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) := by
        ring

theorem summable_eisensteinLineModeSize_sq {t Y : ℝ} (hY : 1 / 2 ≤ Y) :
    Summable (fun N => eisensteinLineModeSize t Y N ^ 2) := by
  have hY0 : 0 ≤ Y := by linarith
  have hmaj := (summable_succ_sq_mul_exp_neg_and_tsum_le (a := 2 * Real.pi) (by positivity)).1
  refine Summable.of_nonneg_of_le (fun N => by positivity)
    (fun N => ?_) ((hmaj.mul_left (Y * Real.exp 1 ^ 2)))
  have h := eisensteinLineModeSize_le_exp (t := t) hY N
  have hd : ((N + 1 : ℕ).divisors.card : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast Nat.card_divisors_le_self (N + 1)
  have hexp : Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)) ≤
      Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
    apply Real.exp_le_exp.mpr
    have hp : (0 : ℝ) ≤ Real.pi * ((N : ℝ) + 1) := by positivity
    have h2Y : (1 : ℝ) ≤ 2 * Y := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2Y hp]
  have hsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0
  have hE : Real.exp (-(Real.pi * ((N : ℝ) + 1))) ^ 2 =
      Real.exp (-(2 * Real.pi * ((N : ℝ) + 1))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc eisensteinLineModeSize t Y N ^ 2
      ≤ (((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        (Real.exp 1 * Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)))) ^ 2 := by
        gcongr
        exact eisensteinLineModeSize_nonneg t Y N
    _ ≤ (((N : ℝ) + 1) * Real.sqrt Y * (Real.exp 1 * Real.exp (-(Real.pi * ((N : ℝ) + 1))))) ^ 2 := by
        gcongr
    _ = ((N : ℝ) + 1) ^ 2 * Real.sqrt Y ^ 2 * Real.exp 1 ^ 2 *
          Real.exp (-(Real.pi * ((N : ℝ) + 1))) ^ 2 := by ring
    _ = Y * Real.exp 1 ^ 2 * (((N : ℝ) + 1) ^ 2 * Real.exp (-(2 * Real.pi * ((N : ℝ) + 1)))) := by
        rw [hsq, hE]; ring

/-! ## The head/tail split at `N₀ = ⌊t/(πY)⌋` -/

/-- Every mode beyond the head has `2π(N+1)Y > 2t`. -/
theorem two_mul_lt_of_floor_le {t Y : ℝ} (hY : 0 < Y) {N : ℕ}
    (hN : ⌊t / (Real.pi * Y)⌋₊ ≤ N) : 2 * t < 2 * Real.pi * ((N : ℝ) + 1) * Y := by
  have h := Nat.lt_floor_add_one (t / (Real.pi * Y))
  have hN' : (⌊t / (Real.pi * Y)⌋₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hπY : 0 < Real.pi * Y := by positivity
  have : t / (Real.pi * Y) < (N : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hπY] at this
  nlinarith

/-- The tail majorant with its exponential factors: for `2π(N+1)Y > 2t` and `Y ≥ 1/2`,
`e^{-2π(N+1)Y} ≤ e^{-7t/4} e^{-πY/8} e^{-π(N+1)/16}`. -/
theorem exp_neg_two_pi_le_split {t Y : ℝ} (hY : 1 / 2 ≤ Y) {N : ℕ}
    (h : 2 * t < 2 * Real.pi * ((N : ℝ) + 1) * Y) :
    Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)) ≤
      Real.exp (-(7 * t / 4)) * Real.exp (-(Real.pi * Y / 8)) *
        Real.exp (-(Real.pi * ((N : ℝ) + 1) / 16)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hπ := Real.pi_pos
  have hπY : 0 ≤ Real.pi * Y := by positivity
  have hπN : 0 ≤ Real.pi * ((N : ℝ) + 1) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hN hπY
  have h2 := mul_le_mul_of_nonneg_left hY hπN
  nlinarith [h1, h2, h]

/-- The squared tail majorant: `e^{-4π(N+1)Y} ≤ e^{-7t/2} e^{-πY/4} e^{-π(N+1)/8}`. -/
theorem exp_neg_four_pi_le_split {t Y : ℝ} (hY : 1 / 2 ≤ Y) {N : ℕ}
    (h : 2 * t < 2 * Real.pi * ((N : ℝ) + 1) * Y) :
    Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)) ^ 2 ≤
      Real.exp (-(7 * t / 2)) * Real.exp (-(Real.pi * Y / 4)) *
        Real.exp (-(Real.pi * ((N : ℝ) + 1) / 8)) := by
  have hb := exp_neg_two_pi_le_split hY h
  have h0 : 0 ≤ Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)) := (Real.exp_pos _).le
  calc Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)) ^ 2
      ≤ (Real.exp (-(7 * t / 4)) * Real.exp (-(Real.pi * Y / 8)) *
          Real.exp (-(Real.pi * ((N : ℝ) + 1) / 16))) ^ 2 := by gcongr
    _ = Real.exp (2 * (-(7 * t / 4))) * Real.exp (2 * (-(Real.pi * Y / 8))) *
          Real.exp (2 * (-(Real.pi * ((N : ℝ) + 1) / 16))) := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        push_cast; ring_nf
    _ = _ := by
        rw [show 2 * (-(7 * t / 4)) = -(7 * t / 2) by ring,
          show 2 * (-(Real.pi * Y / 8)) = -(Real.pi * Y / 4) by ring,
          show 2 * (-(Real.pi * ((N : ℝ) + 1) / 16)) = -(Real.pi * ((N : ℝ) + 1) / 8) by ring]

theorem floor_le_of_half {t Y : ℝ} (ht : 0 ≤ t) (hY : 1 / 2 ≤ Y) :
    (⌊t / (Real.pi * Y)⌋₊ : ℝ) ≤ t / (Real.pi * Y) ∧ t / (Real.pi * Y) ≤ t + 1 := by
  have hπ := Real.pi_gt_three
  have hπY : 0 < Real.pi * Y := by positivity
  refine ⟨Nat.floor_le (by positivity), ?_⟩
  rw [div_le_iff₀ hπY]
  have h32 : (3 : ℝ) / 2 ≤ Real.pi * Y := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h32 (by linarith : (0 : ℝ) ≤ t + 1)]

/-- **The `ℓ¹` bound.** For `t ≥ 2` and `Y ≥ 1/2`,
`Σ_N mode_N ≤ 420 e^{-πt/2} t^{-1/3} · t(1 + log(t+1))/(π√Y) + (1024/π²) e √Y e^{-7t/4} e^{-πY/8}`. -/
theorem tsum_eisensteinLineModeSize_le {t Y : ℝ} (ht : 2 ≤ t) (hY : 1 / 2 ≤ Y) :
    ∑' N : ℕ, eisensteinLineModeSize t Y N ≤
      420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ)) *
          (t / (Real.pi * Real.sqrt Y)) * (1 + Real.log (t + 1)) +
        4 / (Real.pi / 16) ^ 2 * Real.exp 1 * Real.sqrt Y * Real.exp (-(7 * t / 4)) *
          Real.exp (-(Real.pi * Y / 8)) := by
  have hY0 : 0 < Y := by linarith
  have ht0 : 0 < t := by linarith
  have hπ := Real.pi_gt_three
  have hsum := summable_eisensteinLineModeSize (t := t) hY
  set N₀ : ℕ := ⌊t / (Real.pi * Y)⌋₊ with hN₀
  obtain ⟨hfl, hfl'⟩ := floor_le_of_half ht0.le hY
  rw [← hsum.sum_add_tsum_nat_add N₀]
  -- head
  have hhead : ∑ N ∈ Finset.range N₀, eisensteinLineModeSize t Y N ≤
      420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ)) *
        (t / (Real.pi * Real.sqrt Y)) * (1 + Real.log (t + 1)) := by
    set A : ℝ := 420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ)) with hA
    have hA0 : 0 ≤ A := by positivity
    have hs : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
    have hbound : ∑ N ∈ Finset.range N₀, eisensteinLineModeSize t Y N ≤
        ∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y * A :=
      Finset.sum_le_sum fun N _ => eisensteinLineModeSize_le_powerSaving ht hY0 N
    rw [← Finset.sum_mul, ← Finset.sum_mul] at hbound
    have hdiv : ∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) ≤
        (t / (Real.pi * Y)) * (1 + Real.log (t + 1)) := by
      rcases Nat.eq_zero_or_pos N₀ with h0 | hpos
      · rw [h0, Finset.sum_range_zero]
        have : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
        positivity
      · refine (sum_range_card_divisors_succ_le N₀ hpos).trans ?_
        have hlog : Real.log (N₀ : ℝ) ≤ Real.log (t + 1) :=
          Real.log_le_log (by exact_mod_cast hpos) (hfl.trans hfl')
        have h1 : 0 ≤ 1 + Real.log (N₀ : ℝ) := by
          have : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hpos
          have := Real.log_nonneg this
          linarith
        calc (N₀ : ℝ) * (1 + Real.log (N₀ : ℝ))
            ≤ (t / (Real.pi * Y)) * (1 + Real.log (N₀ : ℝ)) :=
              mul_le_mul_of_nonneg_right hfl h1
          _ ≤ (t / (Real.pi * Y)) * (1 + Real.log (t + 1)) := by gcongr
    have hsqY : Real.sqrt Y * (t / (Real.pi * Y)) = t / (Real.pi * Real.sqrt Y) := by
      have hsq : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0.le
      have hs0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
      field_simp
      nlinarith [hsq]
    calc ∑ N ∈ Finset.range N₀, eisensteinLineModeSize t Y N
        ≤ (∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ)) * Real.sqrt Y * A := hbound
      _ ≤ ((t / (Real.pi * Y)) * (1 + Real.log (t + 1))) * Real.sqrt Y * A := by
          gcongr
      _ = A * (Real.sqrt Y * (t / (Real.pi * Y))) * (1 + Real.log (t + 1)) := by ring
      _ = _ := by rw [hsqY, hA]
  -- tail
  have htail : ∑' N : ℕ, eisensteinLineModeSize t Y (N + N₀) ≤
      4 / (Real.pi / 16) ^ 2 * Real.exp 1 * Real.sqrt Y * Real.exp (-(7 * t / 4)) *
        Real.exp (-(Real.pi * Y / 8)) := by
    set B : ℝ := Real.exp 1 * Real.sqrt Y * Real.exp (-(7 * t / 4)) *
      Real.exp (-(Real.pi * Y / 8)) with hB
    have hB0 : 0 ≤ B := by positivity
    have hgeom := summable_succ_mul_exp_neg_and_tsum_le (a := Real.pi / 16) (by positivity)
    have hmaj : ∀ N : ℕ, eisensteinLineModeSize t Y (N + N₀) ≤
        B * ((((N + N₀ : ℕ) : ℝ) + 1) *
          Real.exp (-(Real.pi / 16 * (((N + N₀ : ℕ) : ℝ) + 1)))) := by
      intro N
      have h := eisensteinLineModeSize_le_exp (t := t) hY (N + N₀)
      have hgt : 2 * t < 2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y :=
        two_mul_lt_of_floor_le hY0 (by omega)
      have hsplit := exp_neg_two_pi_le_split hY hgt
      have hd : ((N + N₀ + 1 : ℕ).divisors.card : ℝ) ≤ ((N + N₀ : ℕ) : ℝ) + 1 := by
        exact_mod_cast Nat.card_divisors_le_self (N + N₀ + 1)
      have hs : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
      calc eisensteinLineModeSize t Y (N + N₀)
          ≤ ((N + N₀ + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
            (Real.exp 1 * Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y))) := h
        _ ≤ (((N + N₀ : ℕ) : ℝ) + 1) * Real.sqrt Y *
            (Real.exp 1 * (Real.exp (-(7 * t / 4)) * Real.exp (-(Real.pi * Y / 8)) *
              Real.exp (-(Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) / 16)))) := by gcongr
        _ = B * ((((N + N₀ : ℕ) : ℝ) + 1) *
            Real.exp (-(Real.pi / 16 * (((N + N₀ : ℕ) : ℝ) + 1)))) := by
            rw [hB]; ring_nf
    have hshift : Summable (fun N : ℕ => (((N + N₀ : ℕ) : ℝ) + 1) *
        Real.exp (-(Real.pi / 16 * (((N + N₀ : ℕ) : ℝ) + 1)))) :=
      (summable_nat_add_iff (f := fun M : ℕ => ((M : ℝ) + 1) *
        Real.exp (-(Real.pi / 16 * ((M : ℝ) + 1)))) N₀).mpr hgeom.1
    have hshiftsum : Summable (fun N : ℕ => eisensteinLineModeSize t Y (N + N₀)) :=
      (summable_nat_add_iff N₀).mpr hsum
    calc ∑' N : ℕ, eisensteinLineModeSize t Y (N + N₀)
        ≤ ∑' N : ℕ, B * ((((N + N₀ : ℕ) : ℝ) + 1) *
            Real.exp (-(Real.pi / 16 * (((N + N₀ : ℕ) : ℝ) + 1)))) :=
          hshiftsum.tsum_le_tsum hmaj (hshift.mul_left B)
      _ = B * ∑' N : ℕ, (((N + N₀ : ℕ) : ℝ) + 1) *
            Real.exp (-(Real.pi / 16 * (((N + N₀ : ℕ) : ℝ) + 1))) := tsum_mul_left
      _ ≤ B * ∑' M : ℕ, ((M : ℝ) + 1) * Real.exp (-(Real.pi / 16 * ((M : ℝ) + 1))) := by
          have hfull := hgeom.1.sum_add_tsum_nat_add N₀
          have hnn : 0 ≤ ∑ M ∈ Finset.range N₀,
              ((M : ℝ) + 1) * Real.exp (-(Real.pi / 16 * ((M : ℝ) + 1))) :=
            Finset.sum_nonneg fun M _ => by positivity
          exact mul_le_mul_of_nonneg_left (by linarith) hB0
      _ ≤ B * (4 / (Real.pi / 16) ^ 2) := mul_le_mul_of_nonneg_left hgeom.2 hB0
      _ = _ := by rw [hB]; ring
  linarith

/-- **The `ℓ²` bound.** For `t ≥ 2` and `Y ≥ 1/2`,
`Σ_N mode_N² ≤ 420² e^{-πt} t^{-2/3} · (t/π)(1 + log(t+1))³ + (64/(π/8)³) e² Y e^{-7t/2} e^{-πY/4}`;
the head is uniform in `Y`. -/
theorem tsum_eisensteinLineModeSize_sq_le {t Y : ℝ} (ht : 2 ≤ t) (hY : 1 / 2 ≤ Y) :
    ∑' N : ℕ, eisensteinLineModeSize t Y N ^ 2 ≤
      420 ^ 2 * Real.exp (-(Real.pi * t)) * t ^ (-(2 / 3 : ℝ)) *
          (t / Real.pi) * (1 + Real.log (t + 1)) ^ 3 +
        64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2 * Y * Real.exp (-(7 * t / 2)) *
          Real.exp (-(Real.pi * Y / 4)) := by
  have hY0 : 0 < Y := by linarith
  have ht0 : 0 < t := by linarith
  have hπ := Real.pi_gt_three
  have hsum := summable_eisensteinLineModeSize_sq (t := t) hY
  set N₀ : ℕ := ⌊t / (Real.pi * Y)⌋₊ with hN₀
  obtain ⟨hfl, hfl'⟩ := floor_le_of_half ht0.le hY
  rw [← hsum.sum_add_tsum_nat_add N₀]
  have hsqY : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0.le
  have hE2 : Real.exp (-(Real.pi * t) / 2) ^ 2 = Real.exp (-(Real.pi * t)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hT2 : (t ^ (-(1 / 3 : ℝ))) ^ 2 = t ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  -- head
  have hhead : ∑ N ∈ Finset.range N₀, eisensteinLineModeSize t Y N ^ 2 ≤
      420 ^ 2 * Real.exp (-(Real.pi * t)) * t ^ (-(2 / 3 : ℝ)) *
        (t / Real.pi) * (1 + Real.log (t + 1)) ^ 3 := by
    set A : ℝ := 420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ)) with hA
    have hA0 : 0 ≤ A := by positivity
    have hbound : ∑ N ∈ Finset.range N₀, eisensteinLineModeSize t Y N ^ 2 ≤
        ∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) ^ 2 * (Y * A ^ 2) := by
      refine Finset.sum_le_sum fun N _ => ?_
      have h := eisensteinLineModeSize_le_powerSaving ht hY0 N
      calc eisensteinLineModeSize t Y N ^ 2
          ≤ (((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y * A) ^ 2 := by
            gcongr
            exact eisensteinLineModeSize_nonneg t Y N
        _ = ((N + 1 : ℕ).divisors.card : ℝ) ^ 2 * Real.sqrt Y ^ 2 * A ^ 2 := by ring
        _ = ((N + 1 : ℕ).divisors.card : ℝ) ^ 2 * (Y * A ^ 2) := by rw [hsqY]; ring
    rw [← Finset.sum_mul] at hbound
    have hdiv : ∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) ^ 2 ≤
        (t / (Real.pi * Y)) * (1 + Real.log (t + 1)) ^ 3 := by
      rcases Nat.eq_zero_or_pos N₀ with h0 | hpos
      · rw [h0, Finset.sum_range_zero]
        have : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
        positivity
      · have h := Sieve.sum_card_divisors_pow_le_polylog 2 N₀ hpos
        have hre : ∑ n ∈ Finset.Icc 1 N₀, ((n.divisors.card : ℝ) ^ 2) =
            ∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) ^ 2 := by
          have hIcc : Finset.Icc 1 N₀ = Finset.Ico 1 (N₀ + 1) := by ext n; simp
          rw [hIcc, Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel]
          refine Finset.sum_congr rfl (fun N _ => ?_)
          rw [add_comm]
        rw [hre] at h
        have h3 : (2 : ℕ) ^ 2 - 1 = 3 := by norm_num
        rw [h3] at h
        refine h.trans ?_
        have hlog : Real.log (N₀ : ℝ) ≤ Real.log (t + 1) :=
          Real.log_le_log (by exact_mod_cast hpos) (hfl.trans hfl')
        have h1 : 0 ≤ 1 + Real.log (N₀ : ℝ) := by
          have : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hpos
          have := Real.log_nonneg this
          linarith
        calc (N₀ : ℝ) * (1 + Real.log (N₀ : ℝ)) ^ 3
            ≤ (t / (Real.pi * Y)) * (1 + Real.log (N₀ : ℝ)) ^ 3 :=
              mul_le_mul_of_nonneg_right hfl (by positivity)
          _ ≤ (t / (Real.pi * Y)) * (1 + Real.log (t + 1)) ^ 3 := by gcongr
    have hYcancel : (t / (Real.pi * Y)) * Y = t / Real.pi := by
      field_simp
    calc ∑ N ∈ Finset.range N₀, eisensteinLineModeSize t Y N ^ 2
        ≤ (∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) ^ 2) * (Y * A ^ 2) := hbound
      _ ≤ ((t / (Real.pi * Y)) * (1 + Real.log (t + 1)) ^ 3) * (Y * A ^ 2) := by gcongr
      _ = ((t / (Real.pi * Y)) * Y) * A ^ 2 * (1 + Real.log (t + 1)) ^ 3 := by ring
      _ = _ := by
          rw [hYcancel, hA, mul_pow, mul_pow, hE2, hT2]; ring
  -- tail
  have htail : ∑' N : ℕ, eisensteinLineModeSize t Y (N + N₀) ^ 2 ≤
      64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2 * Y * Real.exp (-(7 * t / 2)) *
        Real.exp (-(Real.pi * Y / 4)) := by
    set B : ℝ := Real.exp 1 ^ 2 * Y * Real.exp (-(7 * t / 2)) * Real.exp (-(Real.pi * Y / 4))
      with hB
    have hB0 : 0 ≤ B := by positivity
    have hgeom := summable_succ_sq_mul_exp_neg_and_tsum_le (a := Real.pi / 8) (by positivity)
    have hmaj : ∀ N : ℕ, eisensteinLineModeSize t Y (N + N₀) ^ 2 ≤
        B * ((((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1)))) := by
      intro N
      have h := eisensteinLineModeSize_le_exp (t := t) hY (N + N₀)
      have hgt : 2 * t < 2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y :=
        two_mul_lt_of_floor_le hY0 (by omega)
      have hsplit := exp_neg_four_pi_le_split hY hgt
      have hd : ((N + N₀ + 1 : ℕ).divisors.card : ℝ) ≤ ((N + N₀ : ℕ) : ℝ) + 1 := by
        exact_mod_cast Nat.card_divisors_le_self (N + N₀ + 1)
      have hs : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
      calc eisensteinLineModeSize t Y (N + N₀) ^ 2
          ≤ (((N + N₀ + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
            (Real.exp 1 * Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y)))) ^ 2 := by
            gcongr
            exact eisensteinLineModeSize_nonneg t Y _
        _ ≤ ((((N + N₀ : ℕ) : ℝ) + 1) * Real.sqrt Y *
            (Real.exp 1 * Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y)))) ^ 2 := by
            gcongr
        _ = (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 * Real.sqrt Y ^ 2 * Real.exp 1 ^ 2 *
            Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y)) ^ 2 := by ring
        _ = (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 * Y * Real.exp 1 ^ 2 *
            Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y)) ^ 2 := by rw [hsqY]
        _ ≤ (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 * Y * Real.exp 1 ^ 2 *
            (Real.exp (-(7 * t / 2)) * Real.exp (-(Real.pi * Y / 4)) *
              Real.exp (-(Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) / 8))) := by gcongr
        _ = B * ((((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1)))) := by
            rw [hB]; ring_nf
    have hshift : Summable (fun N : ℕ => (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1)))) :=
      (summable_nat_add_iff (f := fun M : ℕ => ((M : ℝ) + 1) ^ 2 *
        Real.exp (-(Real.pi / 8 * ((M : ℝ) + 1)))) N₀).mpr hgeom.1
    have hshiftsum : Summable (fun N : ℕ => eisensteinLineModeSize t Y (N + N₀) ^ 2) :=
      (summable_nat_add_iff (f := fun M : ℕ => eisensteinLineModeSize t Y M ^ 2) N₀).mpr hsum
    calc ∑' N : ℕ, eisensteinLineModeSize t Y (N + N₀) ^ 2
        ≤ ∑' N : ℕ, B * ((((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1)))) :=
          hshiftsum.tsum_le_tsum hmaj (hshift.mul_left B)
      _ = B * ∑' N : ℕ, (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1))) := tsum_mul_left
      _ ≤ B * ∑' M : ℕ, ((M : ℝ) + 1) ^ 2 * Real.exp (-(Real.pi / 8 * ((M : ℝ) + 1))) := by
          have hfull := hgeom.1.sum_add_tsum_nat_add N₀
          have hnn : 0 ≤ ∑ M ∈ Finset.range N₀,
              ((M : ℝ) + 1) ^ 2 * Real.exp (-(Real.pi / 8 * ((M : ℝ) + 1))) :=
            Finset.sum_nonneg fun M _ => by positivity
          exact mul_le_mul_of_nonneg_left (by linarith) hB0
      _ ≤ B * (64 / (Real.pi / 8) ^ 3) := mul_le_mul_of_nonneg_left hgeom.2 hB0
      _ = _ := by rw [hB]; ring
  linarith

/-- The tail of the `ℓ²` sum beyond `N₀ = ⌊t/(πY)⌋`, with its exponential factors. -/
theorem tsum_eisensteinLineModeSize_sq_tail_le {t Y : ℝ} (hY : 1 / 2 ≤ Y) :
    ∑' N : ℕ, eisensteinLineModeSize t Y (N + ⌊t / (Real.pi * Y)⌋₊) ^ 2 ≤
      64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2 * Y * Real.exp (-(7 * t / 2)) *
        Real.exp (-(Real.pi * Y / 4)) := by
  have hY0 : 0 < Y := by linarith
  have hsum := summable_eisensteinLineModeSize_sq (t := t) hY
  have hsqY : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0.le
  set N₀ : ℕ := ⌊t / (Real.pi * Y)⌋₊ with hN₀
  set B : ℝ := Real.exp 1 ^ 2 * Y * Real.exp (-(7 * t / 2)) * Real.exp (-(Real.pi * Y / 4))
    with hB
  have hB0 : 0 ≤ B := by positivity
  have hgeom := summable_succ_sq_mul_exp_neg_and_tsum_le (a := Real.pi / 8) (by positivity)
  have hmaj : ∀ N : ℕ, eisensteinLineModeSize t Y (N + N₀) ^ 2 ≤
      B * ((((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1)))) := by
    intro N
    have h := eisensteinLineModeSize_le_exp (t := t) hY (N + N₀)
    have hgt : 2 * t < 2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y :=
      two_mul_lt_of_floor_le hY0 (by omega)
    have hsplit := exp_neg_four_pi_le_split hY hgt
    have hd : ((N + N₀ + 1 : ℕ).divisors.card : ℝ) ≤ ((N + N₀ : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.card_divisors_le_self (N + N₀ + 1)
    have hs : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
    calc eisensteinLineModeSize t Y (N + N₀) ^ 2
        ≤ (((N + N₀ + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
          (Real.exp 1 * Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y)))) ^ 2 := by
          gcongr
          exact eisensteinLineModeSize_nonneg t Y _
      _ ≤ ((((N + N₀ : ℕ) : ℝ) + 1) * Real.sqrt Y *
          (Real.exp 1 * Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y)))) ^ 2 := by
          gcongr
      _ = (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 * Real.sqrt Y ^ 2 * Real.exp 1 ^ 2 *
          Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y)) ^ 2 := by ring
      _ = (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 * Y * Real.exp 1 ^ 2 *
          Real.exp (-(2 * Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) * Y)) ^ 2 := by rw [hsqY]
      _ ≤ (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 * Y * Real.exp 1 ^ 2 *
          (Real.exp (-(7 * t / 2)) * Real.exp (-(Real.pi * Y / 4)) *
            Real.exp (-(Real.pi * (((N + N₀ : ℕ) : ℝ) + 1) / 8))) := by gcongr
      _ = B * ((((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1)))) := by
          rw [hB]; ring_nf
  have hshift : Summable (fun N : ℕ => (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
      Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1)))) :=
    (summable_nat_add_iff (f := fun M : ℕ => ((M : ℝ) + 1) ^ 2 *
      Real.exp (-(Real.pi / 8 * ((M : ℝ) + 1)))) N₀).mpr hgeom.1
  have hshiftsum : Summable (fun N : ℕ => eisensteinLineModeSize t Y (N + N₀) ^ 2) :=
    (summable_nat_add_iff (f := fun M : ℕ => eisensteinLineModeSize t Y M ^ 2) N₀).mpr hsum
  calc ∑' N : ℕ, eisensteinLineModeSize t Y (N + N₀) ^ 2
      ≤ ∑' N : ℕ, B * ((((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1)))) :=
        hshiftsum.tsum_le_tsum hmaj (hshift.mul_left B)
    _ = B * ∑' N : ℕ, (((N + N₀ : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(Real.pi / 8 * (((N + N₀ : ℕ) : ℝ) + 1))) := tsum_mul_left
    _ ≤ B * ∑' M : ℕ, ((M : ℝ) + 1) ^ 2 * Real.exp (-(Real.pi / 8 * ((M : ℝ) + 1))) := by
        have hfull := hgeom.1.sum_add_tsum_nat_add N₀
        have hnn : 0 ≤ ∑ M ∈ Finset.range N₀,
            ((M : ℝ) + 1) ^ 2 * Real.exp (-(Real.pi / 8 * ((M : ℝ) + 1))) :=
          Finset.sum_nonneg fun M _ => by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) hB0
    _ ≤ B * (64 / (Real.pi / 8) ^ 3) := mul_le_mul_of_nonneg_left hgeom.2 hB0
    _ = _ := by rw [hB]; ring

/-- Above height `t/π` there are no head modes: the `ℓ²` sum is exponentially small in `t` and
in `Y`. -/
theorem tsum_eisensteinLineModeSize_sq_le_of_gt {t Y : ℝ} (hY : 1 / 2 ≤ Y)
    (hYt : t / Real.pi < Y) :
    ∑' N : ℕ, eisensteinLineModeSize t Y N ^ 2 ≤
      64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2 * Y * Real.exp (-(7 * t / 2)) *
        Real.exp (-(Real.pi * Y / 4)) := by
  have h := tsum_eisensteinLineModeSize_sq_tail_le (t := t) hY
  have h0 : ⌊t / (Real.pi * Y)⌋₊ = 0 := by
    rw [Nat.floor_eq_zero, div_lt_one (by positivity)]
    have hπ := Real.pi_pos
    rw [div_lt_iff₀ hπ] at hYt
    linarith
  rw [h0] at h
  simpa using h

end

end RHTower
