import GaloisForLFunctions.HTGeometry.RatCoeffJetResidue
import GaloisForLFunctions.HTGeometry.LinePolyGrowth

/-!
# The lowest Gamma power carries the residue

On a vertical line `Γ` beats every power of the height downwards, so a coefficient of polynomial
growth multiplied by any positive power of `Γ` tends to zero.  In a finite Gamma polynomial whose
coefficients have polynomial growth, dividing by the lowest occurring power therefore leaves exactly
the limit of that coefficient.

This is eq. (25)–(3) on the Gamma layer: the projective boundary of an element of `ℂ(s)⟨Γ⟩` is the
residue of the coefficient of its lowest Gamma power.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- Polynomial growth of a function of the height on a fixed vertical line. -/
def HasPolyGrowthLine (f : ℝ → ℂ) : Prop :=
  ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ᶠ t : ℝ in atTop, ‖f t‖ ≤ C * t ^ M

theorem HasPolyGrowthLine.of_hasPolyGrowth {σ₀ : ℝ} {A : ℂ → ℂ} (hA : HasPolyGrowth σ₀ A)
    (hσ : σ₀ ≤ σ) : HasPolyGrowthLine (fun t : ℝ => A ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
  hA σ hσ

/-- The value of Gamma on a vertical line. -/
noncomputable def gammaLine (σ : ℝ) (t : ℝ) : ℂ :=
  Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- Gamma has no zeros on a vertical line to the right of the imaginary axis. -/
theorem gammaLine_ne_zero (hσ : 0 < σ) (t : ℝ) : gammaLine σ t ≠ 0 := by
  rw [gammaLine]
  refine Complex.Gamma_ne_zero (fun m => ?_)
  intro h
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  rw [h] at hre
  simp at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- **Gamma kills polynomial growth on a line.**  A positive power of `Γ` times a coefficient of
polynomial growth tends to zero. -/
theorem tendsto_gammaLine_pow_mul (hσ : 0 < σ) {f : ℝ → ℂ} (hf : HasPolyGrowthLine f) (k : ℕ) :
    Tendsto (fun t : ℝ => gammaLine σ t ^ (k + 1) * f t) atTop (nhds 0) := by
  obtain ⟨M, C, hC, hb⟩ := hf
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hgam : Tendsto (fun t : ℝ => ‖(t : ℂ) ^ M * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
      atTop (nhds 0) := by
    have := (tendsto_pow_mul_Gamma_vertical hσ M).norm
    simpa using this
  have hlim : Tendsto (fun t : ℝ =>
      C * ‖(t : ℂ) ^ M * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop (nhds 0) := by
    have := hgam.const_mul C
    simpa using this
  have hsmall : Tendsto (fun t : ℝ => ‖gammaLine σ t‖) atTop (nhds 0) := by
    have := (tendsto_pow_mul_Gamma_vertical hσ 0).norm
    simpa [gammaLine] using this
  have hle1 : ∀ᶠ t : ℝ in atTop, ‖gammaLine σ t‖ ≤ 1 := by
    have := hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [this] with t ht using ht.le
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  filter_upwards [hb, hle1, eventually_ge_atTop (0 : ℝ)] with t hbt hg1 ht
  have hnormt : ‖(t : ℂ) ^ M‖ = t ^ M := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hpowle : ‖gammaLine σ t‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hg1
  calc ‖gammaLine σ t ^ (k + 1) * f t‖
      = ‖gammaLine σ t‖ ^ k * (‖gammaLine σ t‖ * ‖f t‖) := by
        rw [norm_mul, norm_pow, pow_succ]
        ring
    _ ≤ 1 * (‖gammaLine σ t‖ * (C * t ^ M)) := by
        have hstep : ‖gammaLine σ t‖ * ‖f t‖ ≤ ‖gammaLine σ t‖ * (C * t ^ M) :=
          mul_le_mul_of_nonneg_left hbt (norm_nonneg _)
        exact mul_le_mul hpowle hstep (by positivity) zero_le_one
    _ = C * (t ^ M * ‖gammaLine σ t‖) := by ring
    _ = C * ‖(t : ℂ) ^ M * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [norm_mul, hnormt, gammaLine]

/-- **The lowest Gamma power carries the residue.**  A finite Gamma polynomial with coefficients of
polynomial growth, whose coefficients below the index `u` vanish, converges after division by `Γ^u`
to the limit of the `u`-th coefficient. -/
theorem tendsto_gammaSum_div_pow (hσ : 0 < σ) {d : ℕ} (A : ℕ → ℝ → ℂ) (u : ℕ)
    (hgrow : ∀ i, HasPolyGrowthLine (A i)) {c : ℂ} (hAu : Tendsto (A u) atTop (nhds c))
    (hlow : ∀ i < u, A i = fun _ => 0) (hu : u ≤ d) :
    Tendsto (fun t : ℝ => ∑ i ∈ Finset.range (d + 1), A i t * gammaLine σ t ^ i
        / gammaLine σ t ^ u) atTop (nhds c) := by
  classical
  have hterm : ∀ i ∈ Finset.range (d + 1), Tendsto (fun t : ℝ =>
      A i t * gammaLine σ t ^ i / gammaLine σ t ^ u) atTop
      (nhds (if i = u then c else 0)) := by
    intro i _
    rcases lt_trichotomy i u with hlt | rfl | hgt
    · rw [if_neg (by omega), hlow i hlt]
      simp
    · rw [if_pos rfl]
      refine hAu.congr' (Filter.Eventually.of_forall fun t => ?_)
      show A i t = A i t * gammaLine σ t ^ i / gammaLine σ t ^ i
      rw [mul_div_assoc, div_self (pow_ne_zero i (gammaLine_ne_zero hσ t)), mul_one]
    · rw [if_neg (by omega)]
      obtain ⟨k, hk⟩ : ∃ k : ℕ, i = u + (k + 1) := ⟨i - u - 1, by omega⟩
      have hlim := tendsto_gammaLine_pow_mul hσ (hgrow i) k
      refine hlim.congr' (Filter.Eventually.of_forall fun t => ?_)
      have hne : gammaLine σ t ^ u ≠ 0 := pow_ne_zero u (gammaLine_ne_zero hσ t)
      rw [hk, pow_add]
      field_simp
      ring
  have hsum := tendsto_finsetSum (Finset.range (d + 1)) hterm
  have hmem : u ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_ite_eq' (Finset.range (d + 1)) u (fun _ => c), if_pos hmem] at hsum
  exact hsum

end GaloisForLFunctions
