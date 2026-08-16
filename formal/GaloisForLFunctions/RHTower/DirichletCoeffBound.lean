import GaloisForLFunctions.RHTower.DirichletCoeffFormula

/-!
# Bohr's coefficient estimate

A Dirichlet series converging uniformly on `Re s ≥ x`, with sum bounded by `C` there, has

```text
‖a_n‖  ≤  C · (n+1)^σ        for every σ ≥ x .
```

No interchange of limits is used.  Given `ε`, uniform convergence produces a cut `N` past which the
partial sum is within `ε` of the sum, hence bounded by `C + ε` on the half-plane; the exact
coefficient formula for the finite sum `S_N` extracts `a_n` as a vertical mean, and the trivial
bound on a mean gives `‖a_n‖ ≤ (C + ε)(n+1)^σ`.  Letting `ε → 0` finishes.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **Bohr's coefficient estimate.** -/
theorem norm_coeff_le {a : ℕ → ℂ} {x C : ℝ} {F : ℂ → ℂ}
    (hF : TendstoUniformlyOn (dirichletPartialSum a) F atTop {s : ℂ | x ≤ s.re})
    (hC : ∀ s : ℂ, x ≤ s.re → ‖F s‖ ≤ C) (n : ℕ) {σ : ℝ} (hσ : x ≤ σ) :
    ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ σ := by
  have hK : (0 : ℝ) < ((n : ℝ) + 1) ^ σ := Real.rpow_pos_of_pos (by positivity) σ
  have hstep : ∀ ε : ℝ, 0 < ε → ‖a n‖ ≤ (C + ε) * ((n : ℝ) + 1) ^ σ := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := (Filter.eventually_atTop).1 ((Metric.tendstoUniformlyOn_iff.1 hF) ε hε)
    set N : ℕ := max N₀ (n + 1) with hNdef
    have hnN : n < N := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
    -- the partial sum is bounded on the vertical line
    have hbound : ∀ t : ℝ,
        ‖dirichletPartialSum a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C + ε := by
      intro t
      have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ {s : ℂ | x ≤ s.re} := by
        simpa using hσ
      have hcl := hN₀ N (le_max_left _ _) _ hmem
      have hFb := hC ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ)
      rw [dist_eq_norm] at hcl
      have htri := norm_le_norm_add_norm_sub'
        (dirichletPartialSum a N ((σ : ℂ) + (t : ℂ) * Complex.I))
        (F ((σ : ℂ) + (t : ℂ) * Complex.I))
      have hsymm : ‖dirichletPartialSum a N ((σ : ℂ) + (t : ℂ) * Complex.I)
          - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)
            - dirichletPartialSum a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_sub_rev _ _
      rw [hsymm] at htri
      linarith
    -- the mean is bounded by the same quantity
    have hmean : ∀ T : ℝ, 0 < T →
        ‖(1 / (2 * T)) • ∫ t in (-T)..T,
          dirichletPartialSum a N ((σ : ℂ) + (t : ℂ) * Complex.I)
            * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (C + ε) * ((n : ℝ) + 1) ^ σ := by
      intro T hT
      have hint : ‖∫ t in (-T)..T,
          dirichletPartialSum a N ((σ : ℂ) + (t : ℂ) * Complex.I)
            * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ((C + ε) * ((n : ℝ) + 1) ^ σ) * |T - -T| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => ?_
        have hnorm : ‖(((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            = ((n : ℝ) + 1) ^ σ := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
          congr 1
          simp
        rw [norm_mul, hnorm]
        exact mul_le_mul_of_nonneg_right (hbound t) hK.le
      have habs : |T - -T| = 2 * T := by
        rw [show T - -T = 2 * T by ring, abs_of_nonneg (by linarith)]
      rw [habs] at hint
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hpos : (0 : ℝ) < 1 / (2 * T) := by positivity
      calc (1 / (2 * T)) * ‖_‖ ≤ (1 / (2 * T)) * (((C + ε) * ((n : ℝ) + 1) ^ σ) * (2 * T)) :=
            mul_le_mul_of_nonneg_left hint hpos.le
        _ = (C + ε) * ((n : ℝ) + 1) ^ σ := by field_simp
    -- pass to the limit
    have hlim := (tendsto_vertical_mean_partialSum a hnN σ).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hmean T hT
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hδK : 0 < δ / ((n : ℝ) + 1) ^ σ := by positivity
  have h := hstep (δ / ((n : ℝ) + 1) ^ σ) hδK
  have hval : (C + δ / ((n : ℝ) + 1) ^ σ) * ((n : ℝ) + 1) ^ σ
      = C * ((n : ℝ) + 1) ^ σ + δ := by
    field_simp
  rw [hval] at h
  exact h

end GaloisForLFunctions.RHTower

end
