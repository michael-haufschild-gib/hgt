import GaloisForLFunctions.RHTower.Sieve.HalaszFullSeriesSum
import GaloisForLFunctions.RHTower.Sieve.HalaszWindow
import GaloisForLFunctions.HTGeometry.DiameterCoveringMeasure

/-!
# Large values of the series are confined to one frequency window

A frequency at distance at least `δ` damps the Dirichlet series, so any frequency at which the series
exceeds the damped bound is close.  The corpus's window estimate then pins all such frequencies
together: two of them satisfy

`(t − u)² · logSqWeight z ≤ 2π²δ²`,

provided `|t − u| · log z ≤ π`, which holds automatically on an interval of length `π / log z`.  So on
such an interval the large-value set has diameter at most `√(2π²δ² / logSqWeight z)`, of order
`δ / log z`.

This is the statement that converts the pointwise damping into a measure bound: outside one window of
width `O(δ / log z)` the series is uniformly small.
-/

namespace RHTower.Sieve

open Complex

section

variable {f : ℕ → ℂ}

theorem log_le_log_of_mem_primesLE {z p : ℕ} (hp : p ∈ Nat.primesLE z) :
    Real.log (p : ℝ) ≤ Real.log (z : ℝ) := by
  rw [Nat.mem_primesLE] at hp
  have hple : ((p : ℝ)) ≤ ((z : ℝ)) := by exact_mod_cast hp.1
  have hppos : (0 : ℝ) < ((p : ℝ)) := by exact_mod_cast hp.2.pos
  exact Real.log_le_log hppos hple

theorem abs_sub_mul_log_le_of_abs_sub_le {z : ℕ} {t u : ℝ}
    (hz : |t - u| * Real.log (z : ℝ) ≤ Real.pi) :
    ∀ p ∈ Nat.primesLE z, |(t - u) * Real.log (p : ℝ)| ≤ Real.pi := by
  intro p hp
  have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := by
    rw [Nat.mem_primesLE] at hp
    have h1 : (1 : ℝ) ≤ ((p : ℝ)) := by exact_mod_cast hp.2.one_lt.le
    exact Real.log_nonneg h1
  rw [abs_mul, abs_of_nonneg hlogp]
  refine le_trans (mul_le_mul_of_nonneg_left (log_le_log_of_mem_primesLE hp) (abs_nonneg _)) hz

/-- **Two large values are within one window.**  Both frequencies must be close, so the corpus's
window estimate applies to them. -/
theorem sub_sq_mul_logSqWeight_le_of_norm_gt
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) {t u : ℝ}
    (hspace : |t - u| * Real.log (z : ℝ) ≤ Real.pi)
    (ht : (1 + 1 / (σ - 1)) *
        Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
      ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖)
    (hu : (1 + 1 / (σ - 1)) *
        Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
      ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((u : ℝ) : ℂ) * Complex.I) n‖) :
    (t - u) ^ 2 * logSqWeight z ≤ 2 * Real.pi ^ 2 * δ ^ 2 := by
  have hsre : ∀ v : ℝ, (1 : ℝ) < (((σ : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I).re := by
    intro v
    rw [re_ofReal_add_mul_I]
    exact hσ
  have hclose : ∀ v : ℝ,
      (1 + 1 / (σ - 1)) *
          Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
        ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) n‖ →
      Real.sqrt (mulDistSqPair f (charFn v) (Nat.primesLE z)) ≤ δ := by
    intro v hv
    by_contra hfar
    have hfar' : δ ≤ Real.sqrt (mulDistSqPair f (charFn v) (Nat.primesLE z)) :=
      le_of_lt (not_le.mp hfar)
    have hbound := norm_tsum_twistedSummand_le_of_far hf1 hmul hbdd (hsre v) hz hδ
      (by rw [im_ofReal_add_mul_I]; exact hfar')
    rw [re_ofReal_add_mul_I] at hbound
    linarith
  exact sq_sub_mul_logSqWeight_le hz (fun p _ => hbdd p) (hclose t ht) (hclose u hu)
    (abs_sub_mul_log_le_of_abs_sub_le hspace)

/-- **The large-value set has diameter `O(δ / log z)`.**  Written as a bound on `|t − u|` once the
window weight is positive. -/
theorem abs_sub_le_of_norm_gt
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hW : 0 < logSqWeight z) {t u : ℝ}
    (hspace : |t - u| * Real.log (z : ℝ) ≤ Real.pi)
    (ht : (1 + 1 / (σ - 1)) *
        Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
      ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖)
    (hu : (1 + 1 / (σ - 1)) *
        Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
      ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((u : ℝ) : ℂ) * Complex.I) n‖) :
    |t - u| ≤ Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z) := by
  have hwin := sub_sq_mul_logSqWeight_le_of_norm_gt hf1 hmul hbdd hσ hz hδ hspace ht hu
  have hsq : (t - u) ^ 2 ≤ 2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z := by
    rw [le_div_iff₀ hW]
    exact hwin
  have habs : |t - u| ^ 2 ≤ 2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z := by
    rwa [sq_abs]
  have hnn : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z :=
    le_trans (sq_nonneg _) habs
  exact (Real.le_sqrt (abs_nonneg _) hnn).mpr habs

/-- **The measure of the large-value set on a long range.**  Cover `[-T, T]` by cells of length
`π / log z`; inside each cell the large-value set has diameter at most `√(2π²δ²/logSqWeight z)`, so its
measure is at most `(2T log z/π + 1)` times twice that. -/
theorem volume_largeValues_le
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz2 : 2 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hW : 0 < logSqWeight z) {T : ℝ} (hT : 0 ≤ T) :
    MeasureTheory.volume
        ({t : ℝ | (1 + 1 / (σ - 1)) *
              Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
            ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖}
          ∩ Set.Icc (-T) T)
      ≤ ENNReal.ofReal ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
          (2 * Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z))) := by
  have hz1 : (1 : ℝ) < ((z : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hz2
  have hlogz : 0 < Real.log ((z : ℕ) : ℝ) := Real.log_pos hz1
  have hz : 1 ≤ z := le_trans one_le_two hz2
  set hcell : ℝ := Real.pi / Real.log ((z : ℕ) : ℝ) with hhdef
  have hhpos : 0 < hcell := by
    rw [hhdef]
    exact div_pos Real.pi_pos hlogz
  set w : ℝ := Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z) with hwdef
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hcells : ∀ a : ℝ,
      ∀ x ∈ {t : ℝ | (1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
          ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖}
        ∩ Set.Icc a (a + hcell),
      ∀ y ∈ {t : ℝ | (1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
          ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖}
        ∩ Set.Icc a (a + hcell),
      |x - y| ≤ w := by
    intro a x hx y hy
    have hxy : |x - y| ≤ hcell := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2],
        by linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]⟩
    have hspace : |x - y| * Real.log ((z : ℕ) : ℝ) ≤ Real.pi := by
      refine le_trans (mul_le_mul_of_nonneg_right hxy hlogz.le) (le_of_eq ?_)
      rw [hhdef, div_mul_cancel₀]
      exact hlogz.ne'
    exact abs_sub_le_of_norm_gt hf1 hmul hbdd hσ hz hδ hW hspace hx.1 hy.1
  have hmain := GaloisForLFunctions.HTGeometry.volume_inter_Icc_le_of_cells hT hhpos hw hcells
  refine le_trans hmain (le_of_eq ?_)
  congr 1
  rw [hhdef, div_div_eq_mul_div]


end

end RHTower.Sieve
