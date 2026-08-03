import GaloisForLFunctions.RHTower.Sieve.TuranKubilius
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# The duality principle

A large sieve inequality has two equivalent shapes.  In *Bessel* form it says that the squared
correlations of any vector against a finite family are controlled by its energy,

`∑_r |⟪φ_r, a⟫|² ≤ Δ ‖a‖²`;

in *bilinear* form it says that any combination of the family has controlled energy,

`‖∑_r c_r φ_r‖² ≤ Δ ∑_r |c_r|²`.

The two are equivalent, and each direction is a single application of Cauchy–Schwarz followed by
dividing by the quantity being bounded.  Nothing analytic enters: the argument works in any inner
product space and for any finite family.

This is the step that converts the analytic large sieve — proved for exponential sums at well-spaced
points — into the bilinear form in which it is applied to Dirichlet polynomials.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Bessel form implies bilinear form.** -/
theorem norm_sum_smul_sq_le_of_bessel (s : Finset ι) (φ : ι → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hB : ∀ a : H, ∑ r ∈ s, ‖⟪φ r, a⟫_ℂ‖ ^ 2 ≤ Δ * ‖a‖ ^ 2) (c : ι → ℂ) :
    ‖∑ r ∈ s, c r • φ r‖ ^ 2 ≤ Δ * ∑ r ∈ s, ‖c r‖ ^ 2 := by
  classical
  set v : H := ∑ r ∈ s, c r • φ r with hv
  have hself : ⟪v, v⟫_ℂ = ∑ r ∈ s, (starRingEnd ℂ) (c r) * ⟪φ r, v⟫_ℂ := by
    rw [hv, sum_inner]
    exact Finset.sum_congr rfl fun r _ => inner_smul_left _ _ _
  have hnormself : ‖⟪v, v⟫_ℂ‖ = ‖v‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hbound : ‖v‖ ^ 2 ≤ ∑ r ∈ s, ‖c r‖ * ‖⟪φ r, v⟫_ℂ‖ := by
    rw [← hnormself, hself]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro r _
    rw [norm_mul]
    simp
  have hcs : (∑ r ∈ s, ‖c r‖ * ‖⟪φ r, v⟫_ℂ‖) ^ 2
      ≤ (∑ r ∈ s, ‖c r‖ ^ 2) * ∑ r ∈ s, ‖⟪φ r, v⟫_ℂ‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s _ _
  have hA : (0 : ℝ) ≤ ∑ r ∈ s, ‖c r‖ ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hbess := hB v
  have hvnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hsum_nn : (0 : ℝ) ≤ ∑ r ∈ s, ‖c r‖ * ‖⟪φ r, v⟫_ℂ‖ :=
    Finset.sum_nonneg fun r _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hkey : (‖v‖ ^ 2) ^ 2 ≤ (∑ r ∈ s, ‖c r‖ ^ 2) * (Δ * ‖v‖ ^ 2) := by
    have h1 : (‖v‖ ^ 2) ^ 2 ≤ (∑ r ∈ s, ‖c r‖ * ‖⟪φ r, v⟫_ℂ‖) ^ 2 := by
      have := sq_nonneg ‖v‖
      nlinarith [hbound, hsum_nn, this]
    have h2 : (∑ r ∈ s, ‖c r‖ ^ 2) * ∑ r ∈ s, ‖⟪φ r, v⟫_ℂ‖ ^ 2
        ≤ (∑ r ∈ s, ‖c r‖ ^ 2) * (Δ * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hbess hA
    linarith
  rcases eq_or_lt_of_le (sq_nonneg ‖v‖) with hz | hpos
  · rw [← hz]
    positivity
  · nlinarith [hkey, hpos, hA, hΔ]

/-- Conjugate-times-self is the squared norm, as a complex scalar. -/
theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Bilinear form implies Bessel form.** -/
theorem sum_norm_inner_sq_le_of_bilinear (s : Finset ι) (φ : ι → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hL : ∀ c : ι → ℂ, ‖∑ r ∈ s, c r • φ r‖ ^ 2 ≤ Δ * ∑ r ∈ s, ‖c r‖ ^ 2) (a : H) :
    ∑ r ∈ s, ‖⟪φ r, a⟫_ℂ‖ ^ 2 ≤ Δ * ‖a‖ ^ 2 := by
  classical
  set c : ι → ℂ := fun r => ⟪φ r, a⟫_ℂ with hc
  set S : ℝ := ∑ r ∈ s, ‖c r‖ ^ 2 with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun r _ => sq_nonneg _
  set w : H := ∑ r ∈ s, c r • φ r with hw
  have hval : ⟪w, a⟫_ℂ = ((S : ℝ) : ℂ) := by
    rw [hw, sum_inner, hSdef, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [inner_smul_left, hc]
    exact conj_mul_self _
  have hle : S ≤ ‖w‖ * ‖a‖ := by
    have h1 : ‖⟪w, a⟫_ℂ‖ ≤ ‖w‖ * ‖a‖ := norm_inner_le_norm w a
    have hnorm : ‖((S : ℝ) : ℂ)‖ = S := by
      simp [abs_of_nonneg hSnn]
    rw [hval, hnorm] at h1
    exact h1
  have hwsq : ‖w‖ ^ 2 ≤ Δ * S := by
    have h := hL c
    rw [← hw, ← hSdef] at h
    exact h
  have hann : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hkey : S ^ 2 ≤ Δ * S * ‖a‖ ^ 2 := by
    nlinarith [hle, hwsq, hSnn, hann, hwnn]
  rcases eq_or_lt_of_le hSnn with hz | hpos
  · rw [← hz]
    positivity
  · rw [hSdef] at hpos ⊢
    nlinarith [hkey, hpos]

end RHTower.Sieve
