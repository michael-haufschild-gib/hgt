import GaloisForLFunctions.HTGeometry.PolygammaDepthExpansion
import GaloisForLFunctions.HTGeometry.PolygammaLeadingAsymptotic

/-!
# The polygamma leading asymptotic, uniformly in the abscissa

The corpus's depth expansion of the polygamma jets carries a constant that does not depend on the
abscissa: `‖ψ⁽ᵐ⁺¹⁾(σ+it) − ∑ b_i (s⋯(s+m+i))⁻¹‖ ≤ C/t^{m+2+K}` for *every* `σ > 0`.  Together with
the comparison between a rising product and the corresponding power — also uniform — this upgrades
the leading law `s^{m+1}·ψ⁽ᵐ⁺¹⁾(s) → (−1)^m m!` from a statement on one vertical line to one that
holds uniformly on every vertical tube `0 < σ ≤ M`.

That is the uniformity the projective boundary law states for its `o(1)`: it is uniform after adding
a variable in a fixed compact subset of a vertical tube.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- On a vertical line the modulus dominates the ordinate. -/
theorem norm_vertical_ge_im (σ t : ℝ) : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
  (norm_vertical_add_nat_ge_im (σ := σ) t 0).trans (by simp)

/-- A rising product agrees with the corresponding power up to a relative error of order `1/‖s‖`,
with a constant depending only on the length. -/
theorem exists_norm_pow_div_risingProd_sub_one_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 < x.re → 1 ≤ ‖x‖ →
      ‖x ^ (m + 1) / risingProd x (m + 1) - 1‖ ≤ C / ‖x‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_risingProd_sub_pow_le m
  refine ⟨C, hC, fun x hre hx => ?_⟩
  have hx0 : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hprod : ‖x‖ ^ (m + 1) ≤ ‖risingProd x (m + 1)‖ := norm_pow_le_norm_risingProd hre (m + 1)
  have hprodpos : (0 : ℝ) < ‖risingProd x (m + 1)‖ :=
    lt_of_lt_of_le (by positivity) hprod
  have hprodne : risingProd x (m + 1) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hprodpos
    exact lt_irrefl 0 hprodpos
  have hsub : x ^ (m + 1) / risingProd x (m + 1) - 1
      = (x ^ (m + 1) - risingProd x (m + 1)) / risingProd x (m + 1) := by
    field_simp
  have hnum : ‖x ^ (m + 1) - risingProd x (m + 1)‖ ≤ C * ‖x‖ ^ m := by
    rw [← norm_neg]
    simpa using hbound x hx
  rw [hsub, norm_div, div_le_div_iff₀ hprodpos hx0]
  calc ‖x ^ (m + 1) - risingProd x (m + 1)‖ * ‖x‖
      ≤ (C * ‖x‖ ^ m) * ‖x‖ := mul_le_mul_of_nonneg_right hnum (norm_nonneg _)
    _ = C * ‖x‖ ^ (m + 1) := by ring
    _ ≤ C * ‖risingProd x (m + 1)‖ := mul_le_mul_of_nonneg_left hprod hC

/-- **The leading polygamma law, uniformly on a vertical tube.**  For every `ε` there is a height
beyond which `s^{m+1}·ψ⁽ᵐ⁺¹⁾(s)` is within `ε` of `(−1)^m m!` simultaneously for all abscissas
`0 < σ ≤ M`. -/
theorem exists_uniform_height_pow_mul_iteratedDeriv_digamma (m : ℕ) {M : ℝ} (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
          * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        - (-1 : ℂ) ^ m * ((m.factorial : ℕ) : ℂ)‖ ≤ ε := by
  classical
  obtain ⟨b, C, hC, hexp⟩ := exists_jet_expansion m 0
  obtain ⟨C₁, hC₁, hratio⟩ := exists_norm_pow_div_risingProd_sub_one_le m
  -- the uniform estimate against the expansion's constant
  set A : ℝ := ‖b 0‖ * C₁ + (1 + M) ^ (m + 1) * C with hA
  have hA0 : 0 ≤ A := by positivity
  have hmain : ∀ σ t : ℝ, 0 < σ → σ ≤ M → 2 ≤ t →
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
          * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        - b 0‖ ≤ A / t := by
    intro σ t hσ hσM ht
    set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
    have htpos : (0 : ℝ) < t := by linarith
    have hsre : (0 : ℝ) < s.re := by
      rw [hs]
      simpa using hσ
    have hsge : t ≤ ‖s‖ := norm_vertical_ge_im σ t
    have hsone : (1 : ℝ) ≤ ‖s‖ := le_trans (by linarith) hsge
    have hsle : ‖s‖ ≤ (1 + M) * t := by
      rw [hs]
      have h := norm_add_le ((σ : ℂ)) ((t : ℂ) * Complex.I)
      have h1 : ‖(σ : ℂ)‖ = σ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
      have h2 : ‖(t : ℂ) * Complex.I‖ = t := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos htpos]
      rw [h1, h2] at h
      nlinarith
    -- the expansion at depth zero
    have hbound := hexp σ t hσ ht
    rw [Finset.sum_range_one] at hbound
    simp only [Nat.add_zero] at hbound
    have hprodne : risingProd s (m + 1) ≠ 0 := by
      intro h0
      have := norm_pow_le_norm_risingProd hsre (m + 1)
      rw [h0, norm_zero] at this
      have : (1 : ℝ) ≤ 0 := le_trans (one_le_pow₀ hsone) this
      linarith
    -- split into the shape defect and the expansion error
    have hsplit : s ^ (m + 1)
        * iteratedDeriv (m + 1) Complex.digamma s - b 0
        = b 0 * (s ^ (m + 1) / risingProd s (m + 1) - 1)
          + s ^ (m + 1) * (iteratedDeriv (m + 1) Complex.digamma s
            - b 0 * (risingProd s (m + 1))⁻¹) := by
      field_simp
      ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hfirst : ‖b 0 * (s ^ (m + 1) / risingProd s (m + 1) - 1)‖ ≤ ‖b 0‖ * C₁ / t := by
      rw [norm_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (hratio s hsre hsone) (norm_nonneg _)) ?_
      rw [mul_div_assoc']
      refine div_le_div_of_nonneg_left ?_ htpos hsge |>.trans (le_refl _)
      · positivity
    have hsecond : ‖s ^ (m + 1) * (iteratedDeriv (m + 1) Complex.digamma s
        - b 0 * (risingProd s (m + 1))⁻¹)‖ ≤ (1 + M) ^ (m + 1) * C / t := by
      rw [norm_mul, norm_pow]
      have hb : ‖iteratedDeriv (m + 1) Complex.digamma s - b 0 * (risingProd s (m + 1))⁻¹‖
          ≤ C / t ^ (m + 2) := by
        rw [hs]
        exact hbound
      refine le_trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hsle (m + 1)) hb
        (norm_nonneg _) (by positivity)) ?_
      have hEq : ((1 + M) * t) ^ (m + 1) * (C / t ^ (m + 2)) = (1 + M) ^ (m + 1) * C / t := by
        rw [mul_pow, pow_succ t (m + 1)]
        field_simp
      exact le_of_eq hEq
    calc ‖b 0 * (s ^ (m + 1) / risingProd s (m + 1) - 1)‖
        + ‖s ^ (m + 1) * (iteratedDeriv (m + 1) Complex.digamma s
          - b 0 * (risingProd s (m + 1))⁻¹)‖
        ≤ ‖b 0‖ * C₁ / t + (1 + M) ^ (m + 1) * C / t := add_le_add hfirst hsecond
      _ = A / t := by rw [hA]; ring
  -- identify the constant by the known limit on one line
  have hb0 : b 0 = (-1 : ℂ) ^ m * ((m.factorial : ℕ) : ℂ) := by
    have hlim := tendsto_pow_mul_iteratedDeriv_digamma_vertical (σ := M) hM m
    have hAdiv : Tendsto (fun t : ℝ => A / t) atTop (nhds 0) :=
      (tendsto_const_nhds (x := A)).div_atTop tendsto_id
    have hconst : Tendsto (fun t : ℝ => ((M : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * iteratedDeriv (m + 1) Complex.digamma ((M : ℂ) + (t : ℂ) * Complex.I))
        atTop (nhds (b 0)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hAdiv
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
      rw [dist_eq_norm]
      exact hmain M t hM (le_refl M) ht
    exact tendsto_nhds_unique hconst hlim
  -- turn the uniform bound into the epsilon statement
  obtain ⟨T₀, hT₀⟩ : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → A / t ≤ ε := by
    refine ⟨max 2 (A / ε + 1), fun t ht => ?_⟩
    have h2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
    have htpos : (0 : ℝ) < t := by linarith
    have hAe : A / ε ≤ t := by
      have := le_trans (le_max_right (2 : ℝ) (A / ε + 1)) ht
      linarith
    rw [div_le_iff₀ htpos]
    calc A = (A / ε) * ε := by field_simp
      _ ≤ t * ε := mul_le_mul_of_nonneg_right hAe (le_of_lt hε)
      _ = ε * t := by ring
  refine ⟨max 2 T₀, fun σ t hσ hσM ht => ?_⟩
  have h2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have hT : T₀ ≤ t := le_trans (le_max_right _ _) ht
  rw [← hb0]
  exact le_trans (hmain σ t hσ hσM h2) (hT₀ t hT)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The leading polygamma law as uniform convergence on the tube.** -/
theorem tendstoUniformlyOn_pow_mul_iteratedDeriv_digamma (m : ℕ) {M : ℝ} (hM : 0 < M) :
    TendstoUniformlyOn
      (fun (t : ℝ) (σ : ℝ) => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      (fun _ : ℝ => (-1 : ℂ) ^ m * ((m.factorial : ℕ) : ℂ)) atTop (Set.Ioc 0 M) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨T, hT⟩ := exists_uniform_height_pow_mul_iteratedDeriv_digamma m hM (half_pos hε)
  filter_upwards [eventually_ge_atTop T] with t ht σ hσ
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt (hT σ t hσ.1 hσ.2 ht) (by linarith)

end

end GaloisForLFunctions.HTGeometry
