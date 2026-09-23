import GaloisForLFunctions.HTGeometry.CauchySecondOrderStep

/-!
# Iterating a second-order operator on shrinking discs

Applying `f ↦ c₀f + c₁f′ − f″` repeatedly costs one Cauchy radius per application.  Working on discs
of radius `δ` nested inside a disc of radius `nδ` about the centre, the sup norm on the `k`-th disc
obeys

`M_{k+1} ≤ (ε + γ/δ + 2/δ²)·M_k`,

so after `n` steps the value at the centre is at most `M·(ε + γ/δ + 2/δ²)ⁿ`.

The whole gain of a caustic-null jet is the size of `ε`: on the balance window the leading
coefficient is `O(u^{-1/2})`, while `γ` is bounded and `δ` may be taken comparable with the window
width `√u`, so each factor is `O(u^{-1/2})` and `n` steps buy `u^{-n/2}`.
-/

open Complex Metric

namespace HTGeometry

noncomputable section

/-- **The Cauchy iteration for a second-order operator.** -/
theorem norm_secondOrderIterate_le {Φ : ℕ → ℂ → ℂ} {c₀ c₁ : ℂ → ℂ} {z₀ : ℂ}
    {δ M ε γ : ℝ} (n : ℕ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hdc : ∀ (k : ℕ) (ζ : ℂ), ‖ζ - z₀‖ ≤ (n : ℝ) * δ → DiffContOnCl ℂ (Φ k) (ball ζ δ))
    (hstep : ∀ (k : ℕ) (ζ : ℂ),
      Φ (k + 1) ζ = c₀ ζ * Φ k ζ + c₁ ζ * deriv (Φ k) ζ - deriv (deriv (Φ k)) ζ)
    (hc₀ : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → ‖c₀ ζ‖ ≤ ε)
    (hc₁ : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → ‖c₁ ζ‖ ≤ γ)
    (hbase : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → ‖Φ 0 ζ‖ ≤ M) :
    ‖Φ n z₀‖ ≤ M * (ε + γ / δ + 2 / δ ^ (2 : ℕ)) ^ n := by
  set K : ℝ := ε + γ / δ + 2 / δ ^ (2 : ℕ) with hK
  have hnδ : (0 : ℝ) ≤ (n : ℝ) * δ := by positivity
  have key : ∀ k : ℕ, k ≤ n → ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ ((n : ℝ) - (k : ℝ)) * δ →
      ‖Φ k ζ‖ ≤ M * K ^ k := by
    intro k
    induction k with
    | zero =>
        intro _ ζ hζ
        have hζ' : ‖ζ - z₀‖ ≤ (n : ℝ) * δ := by
          simpa using hζ
        simpa using hbase ζ hζ'
    | succ k ih =>
        intro hk ζ hζ
        have hkn : k ≤ n := Nat.le_of_succ_le hk
        have hknR : ((k : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hk
        have hin : ‖ζ - z₀‖ ≤ (n : ℝ) * δ := by
          have hle : ((n : ℝ) - ((k : ℝ) + 1)) * δ ≤ (n : ℝ) * δ := by
            have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
            nlinarith
          have hcast : ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * δ = ((n : ℝ) - ((k : ℝ) + 1)) * δ := by
            push_cast
            ring
          rw [hcast] at hζ
          linarith
        have hsph : ∀ ξ ∈ sphere ζ δ, ‖Φ k ξ‖ ≤ M * K ^ k := by
          intro ξ hξ
          rw [mem_sphere_iff_norm] at hξ
          refine ih hkn ξ ?_
          have htri : ‖ξ - z₀‖ ≤ ‖ξ - ζ‖ + ‖ζ - z₀‖ := by
            have := norm_add_le (ξ - ζ) (ζ - z₀)
            simpa using this
          have hcast : ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * δ = ((n : ℝ) - ((k : ℝ) + 1)) * δ := by
            push_cast
            ring
          rw [hcast] at hζ
          have hexp : ((n : ℝ) - (k : ℝ)) * δ = δ + ((n : ℝ) - ((k : ℝ) + 1)) * δ := by ring
          rw [hexp]
          linarith [hξ ▸ htri]
        have hcauchy := norm_secondOrderOperator_le (f := Φ k) (z := ζ) (c₀ := c₀ ζ)
          (c₁ := c₁ ζ) (R := δ) (M := M * K ^ k) hδ (hdc k ζ hin) hsph
        have hval : Φ (k + 1) ζ
            = c₀ ζ * Φ k ζ + c₁ ζ * deriv (Φ k) ζ - deriv (deriv (Φ k)) ζ := hstep k ζ
        rw [hval]
        have hMk : (0 : ℝ) ≤ M * K ^ k := by
          have hK0 : (0 : ℝ) ≤ K := by
            have := hc₀ z₀ (by rw [sub_self, norm_zero]; positivity)
            have hε : (0 : ℝ) ≤ ε := le_trans (norm_nonneg _) this
            have hγ : (0 : ℝ) ≤ γ := le_trans (norm_nonneg _) (hc₁ z₀ (by rw [sub_self, norm_zero]; positivity))
            rw [hK]
            positivity
          positivity
        have hb0 : ‖c₀ ζ‖ * (M * K ^ k) ≤ ε * (M * K ^ k) :=
          mul_le_mul_of_nonneg_right (hc₀ ζ hin) hMk
        have hb1 : ‖c₁ ζ‖ * (M * K ^ k / δ) ≤ γ * (M * K ^ k / δ) :=
          mul_le_mul_of_nonneg_right (hc₁ ζ hin) (by positivity)
        have hfin : ε * (M * K ^ k) + γ * (M * K ^ k / δ) + 2 * (M * K ^ k) / δ ^ (2 : ℕ)
            = M * K ^ (k + 1) := by
          have hδne : δ ≠ 0 := ne_of_gt hδ
          have h1 : ε * (M * K ^ k) + γ * (M * K ^ k / δ) + 2 * (M * K ^ k) / δ ^ (2 : ℕ)
              = (M * K ^ k) * (ε + γ / δ + 2 / δ ^ (2 : ℕ)) := by
            field_simp
          rw [h1, ← hK, pow_succ]
          ring
        linarith [hcauchy, hb0, hb1, hfin.le, hfin.ge]
  have hz : ‖z₀ - z₀‖ ≤ ((n : ℝ) - (n : ℝ)) * δ := by simp
  exact key n le_rfl z₀ hz

end

end HTGeometry
