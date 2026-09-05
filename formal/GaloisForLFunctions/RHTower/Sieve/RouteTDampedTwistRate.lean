import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusTwistRate
import GaloisForLFunctions.RHTower.Sieve.RouteTDampedTwistAllHeights

/-!
# The Ramaré cofactor with a super-polylogarithmic saving, uniformly in the frequency

The damped rectangle of `Sieve/RouteTDampedTwistAllHeights` is the plain rectangle of
`Sieve/RouteTMoebiusTwistAllHeights` with every edge constant multiplied by the single factor
`dampedCorrBound P c`, `c` the left abscissa.  So the rate estimate
`Sieve/RouteTMoebiusTwistRate.routeTMoebiusAllHeightsSmoothBound_le_rate` transfers verbatim, with
that factor in front:

```text
   ‖∑_{n ≤ N} μ(n)u^{ω_P(n)}n^{−iτ}‖ ≤ K·dampedCorrBound P c·N·exp(−(log N)^{1/20}) ,
```

uniformly over every real frequency `|τ| ≤ N`, every damping `u ∈ [0,1]` and every finite set `P`
of primes.  This is Matomäki–Teräväinen's — and Matomäki–Radziwiłł's — pointwise input for the
Ramaré cofactor, with a saving that beats every power of the logarithm.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The damped correction factor is at least one. -/
theorem one_le_dampedCorrBound {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) {c : ℝ} (hc : 1 / 2 ≤ c) :
    1 ≤ dampedCorrBound P c := by
  rw [dampedCorrBound]
  have hone : (1 : ℝ) = ∏ _p ∈ P, (1 : ℝ) := by simp
  rw [hone]
  refine Finset.prod_le_prod (fun i _ => zero_le_one) fun p hp => ?_
  have hlt := rpow_neg_lt_one (hP p hp) hc
  have h0 : (0 : ℝ) < (p : ℝ) ^ (-c) := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have h2 : (2 : ℕ) ≤ p := hP p hp
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) h2
    exact Real.rpow_pos_of_pos hp0 _
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The damped rectangle is the plain rectangle scaled by the correction factor. -/
theorem routeTDampedAllHeightsSmoothBound_eq (A C C' M δ : ℝ) (P : Finset ℕ) (N H τ U d : ℝ) :
    routeTDampedAllHeightsSmoothBound A C C' M δ P N H τ U d
      = dampedCorrBound P (routeTContourLeft A δ (|τ| + U))
          * routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ U d := by
  rw [routeTDampedAllHeightsSmoothBound, routeTMoebiusAllHeightsSmoothBound]
  ring

/-- **The Ramaré cofactor sum, uniformly over every frequency below the cutoff.** -/
theorem exists_norm_sum_dampedTwist_le_rate :
    ∃ (A δ K : ℝ), 0 < δ ∧ 0 < K ∧ ∀ᶠ N : ℝ in atTop,
      ∀ (P : Finset ℕ) (u τ : ℝ), (∀ q ∈ P, q.Prime) → 0 ≤ u → u ≤ 1 → |τ| ≤ N →
        ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P u τ n‖
          ≤ K * dampedCorrBound P (routeTContourLeft A δ (|τ| + N))
              * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20))) := by
  obtain ⟨A, C, C', M, δ, hC, hC', hM, hδ, hmain⟩ :=
    exists_norm_sum_dampedTwist_le_routeTSharp_allHeights
  refine ⟨A, δ, (162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
      + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2, hδ, by positivity, ?_⟩
  filter_upwards [eventually_rate_growth, eventually_routeT_contour_rate_data A δ hδ]
    with N hgrow hdata
  obtain ⟨hN0, hL8, hNbase, hF2, hF3⟩ := hgrow
  intro P u τ hPprime hu0 hu1 hτ
  set L : ℝ := Real.log N with hLdef
  set ε : ℝ := L ^ ((1 : ℝ) / 20) with hεdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hε0 : (0 : ℝ) < ε := Real.rpow_pos_of_pos hL0 _
  have hbase := routeTInverseBaseHeight_ge
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set H : ℝ := N * Real.exp (-(3 * ε)) with hHdef
  set d : ℝ := 1 + 1 / L with hddef
  set S : ℝ := |τ| + N with hSdef
  have hH0 : (0 : ℝ) < H := by rw [hHdef]; positivity
  have hd1 : (1 : ℝ) < d := by
    rw [hddef]
    have : (0 : ℝ) < 1 / L := by positivity
    linarith
  have hd2 : d ≤ 2 := by
    rw [hddef]
    have : 1 / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hSbase : routeTInverseBaseHeight ≤ S := by
    rw [hSdef]; linarith [abs_nonneg τ]
  have hS2N : S ≤ 2 * N := by rw [hSdef]; linarith
  obtain ⟨hshift, hedge, hinv⟩ := hdata S hSbase hS2N
  have hdright : d ≤ routeTContourRight A S := by
    rw [hddef, routeTContourRight]
    linarith [hinv]
  have hkey := hmain P u N H τ N d hPprime hu0 hu1 hN0 hH0 (by linarith) hd1 hd2
    (by rw [← hSdef]; exact hSbase) (by rw [← hSdef]; exact hdright)
  refine le_trans hkey ?_
  set Kd : ℝ := dampedCorrBound P (routeTContourLeft A δ S) with hKddef
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  have hc12 : (1 : ℝ) / 2 ≤ routeTContourLeft A δ S := routeTContourLeft_ge_half A δ S
  have hKd1 : (1 : ℝ) ≤ Kd := by rw [hKddef]; exact one_le_dampedCorrBound hP2 hc12
  have hKd0 : (0 : ℝ) ≤ Kd := by linarith
  have hplain := routeTMoebiusAllHeightsSmoothBound_le_rate (A := A) (C := C) (C' := C')
    (M := M) (δ := δ) (N := N) (τ := τ) hC hC' hM hδ hN0 hL8 hNbase hF2 hF3 hshift hedge
  have hsplit : routeTDampedAllHeightsSmoothBound A C C' M δ P N H τ N d
      = Kd * routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d :=
    routeTDampedAllHeightsSmoothBound_eq A C C' M δ P N H τ N d
  rw [hsplit]
  have hHpos : (0 : ℝ) ≤ H + 1 := by linarith
  have hstep : Kd * routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d / (2 * Real.pi)
        + (H + 1)
      ≤ Kd * (routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d / (2 * Real.pi)
          + (H + 1)) := by
    have : H + 1 ≤ Kd * (H + 1) := by nlinarith [hKd1, hHpos]
    have heq : Kd * routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d / (2 * Real.pi)
        = Kd * (routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d / (2 * Real.pi)) := by
      ring
    rw [heq]
    nlinarith [this]
  refine le_trans hstep ?_
  have hfin := mul_le_mul_of_nonneg_left hplain hKd0
  calc Kd * (routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d / (2 * Real.pi) + (H + 1))
      ≤ Kd * (((162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
            + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2) * N * Real.exp (-ε)) := hfin
    _ = ((162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
            + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2) * Kd * N * Real.exp (-ε) := by ring

end

end RHTower.Sieve
