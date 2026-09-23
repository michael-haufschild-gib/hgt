import GaloisForLFunctions.HTGeometry.PolygammaSeries
import GaloisForLFunctions.HTGeometry.LineAsymptoticScale

/-!
# Sums over the shift orbit of a vertical point

The remainder of every telescoped expansion of a digamma jet is a sum over the shift orbit
`s, s+1, s+2, …` of a vertical point.  Two elementary facts control such sums (both already in the
corpus): every orbit point has modulus at least the ordinate `t`, and at least its own real part
`σ+n`.  Splitting the orbit at
`n ≈ t` and telescoping the far part gives

`∑_{n≥0} ‖s+n‖^{-(q+3)} ≤ 4·t^{-(q+2)}`,

which is one order better than the trivial bound and is exactly the gain each expansion step needs.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ t : ℝ}

theorem norm_shift_pos {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (n : ℕ) :
    0 < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
  lt_of_lt_of_le (by positivity) (norm_vertical_add_nat_ge_re (σ := σ) t n)

theorem summable_norm_shift_inv_pow {σ : ℝ} (hσ : 0 < σ) (t : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n : ℕ => ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ k) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_one_div_shift_pow hσ k hk)
  have hge := norm_vertical_add_nat_ge_re (σ := σ) t n
  have hpos : (0 : ℝ) < σ + (n : ℝ) := by positivity
  rw [one_div, ← inv_pow]
  exact pow_le_pow_left₀ (by positivity) (by
    rw [inv_le_inv₀ (norm_shift_pos hσ t n) hpos]
    exact hge) k

/-- The far part of the orbit telescopes. -/
theorem tsum_inv_sq_shift_le {N : ℕ} (hN : 2 ≤ (N : ℝ)) :
    ∑' i : ℕ, (((N : ℝ) + i) ^ (2 : ℕ))⁻¹ ≤ ((N : ℝ) - 1)⁻¹ := by
  have hpos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hmaj := hasSum_one_div_shift_mul_succ hpos
  have hterm : ∀ i : ℕ, (((N : ℝ) + i) ^ (2 : ℕ))⁻¹
      ≤ 1 / (((N : ℝ) - 1 + i) * ((N : ℝ) - 1 + i + 1)) := by
    intro i
    have h1 : (0 : ℝ) < (N : ℝ) - 1 + i := by positivity
    have h2 : (0 : ℝ) < (N : ℝ) + i := by linarith
    have heq : (N : ℝ) - 1 + i + 1 = (N : ℝ) + i := by ring
    rw [heq, one_div, ← inv_pow, sq, mul_inv]
    have : (((N : ℝ) + i))⁻¹ ≤ ((N : ℝ) - 1 + i)⁻¹ := by
      rw [inv_le_inv₀ h2 h1]
      linarith
    exact mul_le_mul_of_nonneg_right this (le_of_lt (inv_pos.mpr h2))
  have hsummable : Summable (fun i : ℕ => (((N : ℝ) + i) ^ (2 : ℕ))⁻¹) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) hterm hmaj.summable
  calc ∑' i : ℕ, (((N : ℝ) + i) ^ (2 : ℕ))⁻¹
      ≤ ∑' i : ℕ, 1 / (((N : ℝ) - 1 + i) * ((N : ℝ) - 1 + i + 1)) :=
        hsummable.tsum_le_tsum hterm hmaj.summable
    _ = 1 / ((N : ℝ) - 1) := hmaj.tsum_eq
    _ = ((N : ℝ) - 1)⁻¹ := one_div _

/-- **The cube bound.**  Summing the inverse cubes over the shift orbit gains one full order. -/
theorem tsum_norm_shift_inv_cube_le {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 2 ≤ t) :
    ∑' n : ℕ, ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (3 : ℕ) ≤ 4 / t ^ (2 : ℕ) := by
  have htpos : (0 : ℝ) < t := by linarith
  obtain ⟨N, hNt, hNlt⟩ : ∃ N : ℕ, t ≤ (N : ℝ) ∧ (N : ℝ) < t + 1 :=
    ⟨⌈t⌉₊, Nat.le_ceil t, Nat.ceil_lt_add_one htpos.le⟩
  have hN2 : 2 ≤ (N : ℝ) := le_trans ht hNt
  have hsum := summable_norm_shift_inv_pow hσ t (k := 3) (by norm_num)
  rw [← hsum.sum_add_tsum_nat_add N]
  have hnear : ∑ i ∈ Finset.range N, ‖(σ : ℂ) + (t : ℂ) * Complex.I + (i : ℂ)‖⁻¹ ^ (3 : ℕ)
      ≤ 2 / t ^ (2 : ℕ) := by
    have hbound : ∀ i ∈ Finset.range N,
        ‖(σ : ℂ) + (t : ℂ) * Complex.I + (i : ℂ)‖⁻¹ ^ (3 : ℕ) ≤ (t ^ (3 : ℕ))⁻¹ := by
      intro i _
      rw [← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 3
      rw [inv_le_inv₀ (norm_shift_pos hσ t i) htpos]
      exact norm_vertical_add_nat_ge_im (σ := σ) t i
    have hcard := Finset.sum_le_sum hbound
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hcard
    have hNle : (N : ℝ) ≤ t + 1 := le_of_lt hNlt
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have hstep : (N : ℝ) * (t ^ (3 : ℕ))⁻¹ ≤ 2 / t ^ (2 : ℕ) := by
      rw [← sub_nonneg]
      have hexp : 2 / t ^ (2 : ℕ) - (N : ℝ) * (t ^ (3 : ℕ))⁻¹ = (2 * t - (N : ℝ)) / t ^ (3 : ℕ) := by
        field_simp
      rw [hexp]
      refine div_nonneg ?_ (by positivity)
      linarith
    linarith
  have hfar : ∑' i : ℕ, ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖⁻¹ ^ (3 : ℕ)
      ≤ 2 / t ^ (2 : ℕ) := by
    have hterm : ∀ i : ℕ,
        ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖⁻¹ ^ (3 : ℕ)
          ≤ t⁻¹ * (((N : ℝ) + i) ^ (2 : ℕ))⁻¹ := by
      intro i
      have hp : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖ :=
        norm_shift_pos hσ t (i + N)
      have h1 : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖ :=
        norm_vertical_add_nat_ge_im (σ := σ) t (i + N)
      have h2 : (N : ℝ) + i ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖ := by
        refine le_trans ?_ (norm_vertical_add_nat_ge_re (σ := σ) t (i + N))
        push_cast
        linarith
      have hNi : (0 : ℝ) < (N : ℝ) + i := by linarith
      have hinv1 : ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖⁻¹ ≤ t⁻¹ := by
        rw [inv_le_inv₀ hp htpos]; exact h1
      have hinv2 : ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖⁻¹ ≤ ((N : ℝ) + i)⁻¹ := by
        rw [inv_le_inv₀ hp hNi]; exact h2
      have hstep : ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖⁻¹ ^ (3 : ℕ)
          = ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖⁻¹
            * (‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖⁻¹
              * ‖(σ : ℂ) + (t : ℂ) * Complex.I + ((i + N : ℕ) : ℂ)‖⁻¹) := by ring
      rw [hstep, sq, mul_inv]
      refine mul_le_mul hinv1 (mul_le_mul hinv2 hinv2 (by positivity) (by positivity))
        (by positivity) (by positivity)
    have hmajsummable : Summable (fun i : ℕ => t⁻¹ * (((N : ℝ) + i) ^ (2 : ℕ))⁻¹) := by
      refine Summable.mul_left _ ?_
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
        (summable_one_div_shift_pow (by linarith : (0 : ℝ) < (N : ℝ)) 2 (by norm_num))
      rw [one_div]
    have hle := Summable.tsum_le_tsum hterm
      ((summable_nat_add_iff N).mpr hsum) hmajsummable
    have hmaj : ∑' i : ℕ, t⁻¹ * (((N : ℝ) + i) ^ (2 : ℕ))⁻¹ ≤ t⁻¹ * ((N : ℝ) - 1)⁻¹ := by
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (tsum_inv_sq_shift_le hN2) (by positivity)
    have hNm1 : t / 2 ≤ (N : ℝ) - 1 := by linarith
    have hfinal : t⁻¹ * ((N : ℝ) - 1)⁻¹ ≤ 2 / t ^ (2 : ℕ) := by
      have hpos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
      have hinv : ((N : ℝ) - 1)⁻¹ ≤ (t / 2)⁻¹ := by
        rw [inv_le_inv₀ hpos (by positivity)]
        exact hNm1
      calc t⁻¹ * ((N : ℝ) - 1)⁻¹ ≤ t⁻¹ * (t / 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 2 / t ^ (2 : ℕ) := by field_simp
    linarith
  refine le_trans (add_le_add hnear hfar) (le_of_eq ?_)
  ring

/-- **The general orbit bound.**  Every exponent at least three gains one order. -/
theorem tsum_norm_shift_inv_pow_le {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 2 ≤ t) (q : ℕ) :
    ∑' n : ℕ, ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (q + 3) ≤ 4 / t ^ (q + 2) := by
  have htpos : (0 : ℝ) < t := by linarith
  have hterm : ∀ n : ℕ, ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (q + 3)
      ≤ (t ^ q)⁻¹ * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (3 : ℕ) := by
    intro n
    have hp : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := norm_shift_pos hσ t n
    have hinv : ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ≤ t⁻¹ := by
      rw [inv_le_inv₀ hp htpos]
      exact norm_vertical_add_nat_ge_im (σ := σ) t n
    have hq : ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ q ≤ (t ^ q)⁻¹ := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) hinv q
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (q + 3)
        = ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ q
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (3 : ℕ) := by rw [← pow_add]
      _ ≤ (t ^ q)⁻¹ * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
  have hsum3 := summable_norm_shift_inv_pow hσ t (k := 3) (by norm_num)
  have hsumq := summable_norm_shift_inv_pow hσ t (k := q + 3) (by omega)
  have hle := Summable.tsum_le_tsum hterm hsumq (hsum3.mul_left _)
  have hcube := tsum_norm_shift_inv_cube_le hσ ht
  rw [tsum_mul_left] at hle
  have hstep : (t ^ q)⁻¹ * (∑' n : ℕ, ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (3 : ℕ))
      ≤ (t ^ q)⁻¹ * (4 / t ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hcube (by positivity)
  have hfinal : (t ^ q)⁻¹ * (4 / t ^ (2 : ℕ)) = 4 / t ^ (q + 2) := by
    rw [pow_add]
    field_simp
  linarith [hle, hstep, hfinal.le, hfinal.ge]


end GaloisForLFunctions
