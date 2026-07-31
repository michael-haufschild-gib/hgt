import GaloisForLFunctions.HTGeometry.GammaVerticalDecay

/-!
# Gamma decays faster than any power on a vertical line

Adjoining `Γ` to the digamma field creates an *exponential* valuation direction, not merely a decaying
one: on a fixed vertical line every quotient of nonzero digamma-field coefficients has
algebraic-logarithmic size, while `Γ` outruns every power of the height.

The Euler bound `‖Γ(s)‖ ≤ Γ(Re s)` is only a bound, and the one-step recursion turns it into decay of
order `1/t`.  Iterating the recursion `k` times factors `Γ(σ + k + it) = Γ(σ + it) ∏_{j<k}(σ + j + it)`
whose `k` factors each have modulus at least `t`, so

`‖Γ(σ + it)‖ ≤ Γ(σ + k) / t^k`

for **every** `k`.  Consequently `t^n Γ(σ + it) → 0` for every `n`.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- Iterated functional equation: `Γ(s + k) = Γ(s) ∏_{j<k}(s + j)` away from the poles. -/
theorem Gamma_add_nat_eq {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) (k : ℕ) :
    Complex.Gamma (s + k) = Complex.Gamma s * ∏ j ∈ Finset.range k, (s + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : s + ((k : ℕ) + 1 : ℕ) = (s + k) + 1 := by push_cast; ring
      rw [hstep, Complex.Gamma_add_one (s + k) (hs k), ih, Finset.prod_range_succ]
      ring

/-- **Super-polynomial vertical decay of `Γ`.**  For every `σ > 0`, every `k` and every `t > 0`,
`‖Γ(σ + it)‖ ≤ Γ(σ + k) / t^k`. -/
theorem norm_Gamma_vertical_le_pow {σ : ℝ} (hσ : 0 < σ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Real.Gamma (σ + k) / t ^ k := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hjre : ∀ j : ℕ, (s + j).re = σ + j := by
    intro j
    simp [hsdef]
  have hjne : ∀ j : ℕ, s + j ≠ 0 := by
    intro j h
    have := hjre j
    rw [h] at this
    simp only [Complex.zero_re] at this
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith [hjre j, hσ]
  have hprod := Gamma_add_nat_eq hjne k
  have hnorm : ‖Complex.Gamma (s + k)‖
      = ‖Complex.Gamma s‖ * ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖ := by
    rw [hprod, norm_mul, norm_prod]
  have hfac : ∀ j ∈ Finset.range k, t ≤ ‖s + (j : ℂ)‖ := by
    intro j _
    have habs := Complex.abs_im_le_norm (s + (j : ℂ))
    have him : (s + (j : ℂ)).im = t := by simp [hsdef]
    rw [him, abs_of_pos ht] at habs
    exact habs
  have hprodge : t ^ k ≤ ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖ := by
    calc t ^ k = ∏ _j ∈ Finset.range k, t := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖ :=
          Finset.prod_le_prod (fun _ _ => ht.le) hfac
  have hGk : ‖Complex.Gamma (s + k)‖ ≤ Real.Gamma (σ + k) := by
    have hpos : 0 < (s + (k : ℂ)).re := by
      rw [hjre k]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h := norm_Gamma_le_real_Gamma_re hpos
    rwa [hjre k] at h
  rw [le_div_iff₀ (by positivity)]
  calc ‖Complex.Gamma s‖ * t ^ k
      ≤ ‖Complex.Gamma s‖ * ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hprodge (norm_nonneg _)
    _ = ‖Complex.Gamma (s + k)‖ := hnorm.symm
    _ ≤ Real.Gamma (σ + k) := hGk

/-- **`Γ` outruns every power.**  For every `σ > 0` and every `n`, `t^n Γ(σ + it) → 0`. -/
theorem Gamma_vertical_tendsto_zero_mul_pow {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Tendsto (fun t : ℝ => ((t : ℂ)) ^ n * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun t : ℝ => Real.Gamma (σ + (n + 1 : ℕ)) / t)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hbound := norm_Gamma_vertical_le_pow hσ (n + 1) ht
    have htn : ‖((t : ℂ)) ^ n‖ = t ^ n := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    rw [norm_mul, htn]
    calc t ^ n * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ t ^ n * (Real.Gamma (σ + (n + 1 : ℕ)) / t ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = Real.Gamma (σ + (n + 1 : ℕ)) / t := by
          rw [pow_succ]
          field_simp
  · exact tendsto_const_nhds.div_atTop tendsto_id

end GaloisForLFunctions
