import GaloisForLFunctions.RHTower.Sieve.CircleRowSum

/-!
# The large sieve for frequencies separated on the circle

The Bessel inequality of `LargeSieveWeak.lean` requires the user to supply a `Δ` dominating every
`N + ∑_{t ≠ r} 2‖conj(ξ_r) ξ_t - 1‖^{-1}`.  With the chord bound of `CircleDistance.lean` and the
row sum of `CircleRowSum.lean` that quantity is now *computed* from a separation hypothesis: for
frequencies `ξ_r = e(λ_r)` with the `λ_r` pairwise `δ`-separated in `ℝ/ℤ`,

`∑_r |⟪e(λ_r), a⟫|² ≤ (N + δ^{-1} ∑_{1 ≤ k ≤ M} k^{-1}) ‖a‖²`,  `M ≥ (2δ)^{-1}`.

So the admissible `Δ` is `N + O(δ^{-1} log δ^{-1})`, with everything explicit and no hypothesis
beyond the separation.  The sharp `N + δ^{-1}` is not this statement: the harmonic factor is the
provable ceiling of the absolute-value method (`SeparatedRowSum.lean`), and removing it needs
cancellation, i.e. Montgomery–Vaughan's refinement of Hilbert's inequality for arbitrary well-spaced
frequencies.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The frequency on the unit circle attached to a real number. -/
noncomputable def circleFreq (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem norm_circleFreq (x : ℝ) : ‖circleFreq x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The correlation of two circle frequencies is the frequency of their difference. -/
theorem conj_circleFreq_mul (x y : ℝ) :
    (starRingEnd ℂ) (circleFreq x) * circleFreq y = circleFreq (y - x) := by
  rw [circleFreq, circleFreq, circleFreq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The chordal separation of two circle frequencies. -/
theorem four_mul_toIntDist_le_norm_sub (x y : ℝ) :
    4 * toIntDist (y - x) ≤ ‖(starRingEnd ℂ) (circleFreq x) * circleFreq y - 1‖ := by
  rw [conj_circleFreq_mul]
  exact four_mul_toIntDist_le (y - x)

/-- **Large sieve for frequencies separated on the circle.**  The admissible `Δ` is explicit. -/
theorem largeSieve_separated {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) (lam : ι → ℝ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ toIntDist (lam b - lam a))
    {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ))
    (a : EuclideanSpace ℂ (Fin N)) :
    ∑ r ∈ s, ‖⟪expRow N (circleFreq (lam r)), a⟫_ℂ‖ ^ 2
      ≤ ((N : ℝ) + (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ)) * ‖a‖ ^ 2 := by
  classical
  have hH0 : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hξ : ∀ r ∈ s, ‖circleFreq (lam r)‖ = 1 := fun r _ => norm_circleFreq _
  -- distinct separated frequencies have nontrivial correlation
  have hne : ∀ r ∈ s, ∀ t ∈ s, r ≠ t →
      (starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) ≠ 1 := by
    intro r hr t ht hrt hcon
    have hsep' := hsep r hr t ht hrt
    have hchord := four_mul_toIntDist_le_norm_sub (lam r) (lam t)
    rw [hcon, sub_self, norm_zero] at hchord
    linarith
  -- the row sum is bounded by the harmonic sum
  have hΔ : ∀ r ∈ s, (N : ℝ)
      + ∑ t ∈ s.erase r, 2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
      ≤ (N : ℝ) + (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
    intro r hr
    have hterm : ∀ t ∈ s.erase r,
        2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
          ≤ (1 / 2) * (1 / toIntDist (lam t - lam r)) := by
      intro t ht
      have ht' := Finset.mem_erase.mp ht
      have hsep' := hsep r hr t ht'.2 (Ne.symm ht'.1)
      have hchord := four_mul_toIntDist_le_norm_sub (lam r) (lam t)
      have hpos : (0 : ℝ) < 4 * toIntDist (lam t - lam r) := by linarith
      have hstep : 2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
          ≤ 2 / (4 * toIntDist (lam t - lam r)) := by
        gcongr
      have hval : 2 / (4 * toIntDist (lam t - lam r))
          = (1 / 2) * (1 / toIntDist (lam t - lam r)) := by
        rw [div_mul_eq_div_div_swap]
        ring
      rw [hval] at hstep
      exact hstep
    have hrow := circle_row_sum_le s lam hδ0 hδ hsep (r := r) hr (M := M) hM
    have hchain : ∑ t ∈ s.erase r,
        2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
          ≤ (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
      calc ∑ t ∈ s.erase r,
            2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
          ≤ ∑ t ∈ s.erase r, (1 / 2) * (1 / toIntDist (lam t - lam r)) :=
            Finset.sum_le_sum hterm
        _ = (1 / 2) * ∑ t ∈ s.erase r, 1 / toIntDist (lam t - lam r) := by rw [Finset.mul_sum]
        _ ≤ (1 / 2) * ((2 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hrow (by norm_num)
        _ = (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by ring
    linarith
  have hΔ0 : (0 : ℝ) ≤ (N : ℝ) + (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
    have : (0 : ℝ) ≤ (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by positivity
    positivity
  exact largeSieve_bessel N s (fun r => circleFreq (lam r)) hξ hne hΔ0 hΔ a

end RHTower.Sieve
