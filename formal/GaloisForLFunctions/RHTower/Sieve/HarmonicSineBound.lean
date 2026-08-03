import GaloisForLFunctions.RHTower.Sieve.AbelTail

/-!
# The harmonic-weighted sine sum is uniformly bounded

Splitting the range at `⌈1/θ⌉` makes both halves bounded by absolute constants:

* below the cut each term satisfies `|sin(dθ)|/(d+1) ≤ dθ/(d+1) ≤ θ`, so that part is at most
  `⌈1/θ⌉ θ ≤ 1 + θ`;
* above the cut Abel's tail inequality gives `2B/(⌈1/θ⌉ + 1) ≤ 2Bθ`, and Jordan's inequality bounds
  `B = 1/|sin(θ/2)|` by `π/θ`, so that part is at most `2π`.

Hence `|∑_{d < M} sin(dθ)/(d+1)| ≤ 1 + 3π`, uniformly in `M` and in `0 < θ ≤ π`.  It is the tail
lemma's factor "weight at the cut" that makes the second half work: a bound without it would
degrade as `θ → 0` exactly where the first half is longest.
-/

namespace RHTower.Sieve

open Finset

/-- **Uniform bound for the harmonic-weighted sine sum.** -/
theorem abs_sum_sin_div_le_uniform {θ : ℝ} (h0 : 0 < θ) (hpi : θ ≤ Real.pi) (M : ℕ) :
    |∑ d ∈ Finset.range M, (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ)|
      ≤ 1 + 3 * Real.pi := by
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hhalf : (0 : ℝ) < θ / 2 := by linarith
  have hhalfpi : θ / 2 < Real.pi := by linarith
  have hsinpos : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi hhalf hhalfpi
  have habs : |Real.sin (θ / 2)| = Real.sin (θ / 2) := abs_of_pos hsinpos
  -- the exponential is nontrivial
  have hθne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    have hz : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 0 := by
      rw [hcon, sub_self, norm_zero]
    rw [norm_exp_I_sub_one θ, habs] at hz
    linarith
  -- Jordan's inequality bounds the Dirichlet constant
  have hjordan : 2 / Real.pi * (θ / 2) ≤ Real.sin (θ / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have hBle : 1 / |Real.sin (θ / 2)| ≤ Real.pi / θ := by
    rw [habs, div_le_div_iff₀ hsinpos h0]
    have hkey : Real.pi * (2 / Real.pi * (θ / 2)) = θ := by field_simp
    nlinarith [hjordan, hkey, hpipos, h0]
  -- weights
  have hw0 : ∀ i : ℕ, (0 : ℝ) ≤ 1 / ((i : ℝ) + 1) := by
    intro i; positivity
  have hwanti : ∀ i : ℕ, (1 : ℝ) / ((((i + 1 : ℕ)) : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
    intro i
    have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have h2 : ((i : ℝ) + 1) ≤ (((i + 1 : ℕ) : ℝ) + 1) := by push_cast; linarith
    exact one_div_le_one_div_of_le h1 h2
  obtain ⟨a, hage, hale⟩ : ∃ a : ℕ, (1 : ℝ) / θ ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1 / θ + 1 :=
    ⟨⌈1 / θ⌉₊, Nat.le_ceil _,
      le_of_lt (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / θ))⟩
  -- head bound on any initial segment
  have hhead : ∀ c : ℕ, (c : ℝ) ≤ (a : ℝ) →
      |∑ d ∈ Finset.range c, (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ)| ≤ 1 + θ := by
    intro c hc
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ Finset.range c,
        |(1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ)| ≤ θ := by
      intro d _
      rw [abs_mul, abs_of_nonneg (hw0 d)]
      have hs : |Real.sin ((d : ℝ) * θ)| ≤ (d : ℝ) * θ := by
        refine le_trans Real.abs_sin_le_abs ?_
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) * θ)]
      have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hd1]
      nlinarith [hs, h0, Nat.cast_nonneg (α := ℝ) d]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hstep : (c : ℝ) * θ ≤ (1 / θ + 1) * θ :=
      mul_le_mul_of_nonneg_right (le_trans hc hale) h0.le
    have hval : (1 / θ + 1) * θ = 1 + θ := by field_simp
    linarith
  by_cases hMa : M ≤ a
  · have hc : (M : ℝ) ≤ (a : ℝ) := by exact_mod_cast hMa
    have := hhead M hc
    linarith
  · have hlt : a ≤ M := by omega
    have hsplit : ∑ d ∈ Finset.range M, (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ)
        = (∑ d ∈ Finset.range a, (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ))
          + ∑ d ∈ Finset.Ico a M, (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive _ (Nat.zero_le a) hlt).symm
    have htail := abs_sum_Ico_mul_le_of_bounded_partial
      (g := fun d : ℕ => Real.sin ((d : ℝ) * θ)) (w := fun d : ℕ => 1 / ((d : ℝ) + 1))
      (B := 1 / |Real.sin (θ / 2)|) a M (fun k => abs_sum_sin_le hθne k) hw0 hwanti
    have htail2 : 2 * (1 / |Real.sin (θ / 2)|) * (1 / ((a : ℝ) + 1)) ≤ 2 * Real.pi := by
      have hapos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have hinv : 1 / ((a : ℝ) + 1) ≤ θ := by
        rw [div_le_iff₀ hapos]
        have hth : θ * (1 / θ) = 1 := by field_simp
        nlinarith [hage, hth, h0]
      have hBnn : (0 : ℝ) ≤ 1 / |Real.sin (θ / 2)| := by positivity
      have hs1 : 2 * (1 / |Real.sin (θ / 2)|) * (1 / ((a : ℝ) + 1))
          ≤ 2 * (1 / |Real.sin (θ / 2)|) * θ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      have hs2 : 2 * (1 / |Real.sin (θ / 2)|) * θ ≤ 2 * (Real.pi / θ) * θ := by
        nlinarith [hBle, h0]
      have hs3 : 2 * (Real.pi / θ) * θ = 2 * Real.pi := by field_simp
      linarith
    have hheada := hhead a (le_refl _)
    rw [hsplit]
    have habs2 := abs_add_le (∑ d ∈ Finset.range a, (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ))
      (∑ d ∈ Finset.Ico a M, (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ))
    linarith [habs2, hheada, htail, htail2, hpi]

end RHTower.Sieve
