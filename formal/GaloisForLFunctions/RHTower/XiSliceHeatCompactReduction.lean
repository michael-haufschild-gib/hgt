import GaloisForLFunctions.RHTower.XiSliceHeatThresholdVerificationHeight

/-!
# RH as a family of compact heat checks

**Theorem** (`exists_riemannHypothesis_iff_compact_heat_checks`).  There are constants `t₀, K₀` such
that, with `T(λ) = max(t₀, e^{100/λ})` and `M(λ) = max(K₀, T(λ) log T(λ) / 8)`,

  RH  ⟺  for every `λ > 0`, every height `0 ≤ t ≤ T(λ)` and every order `m < M(λ)`,
          `T_{2m}(λ, 0, t) ≥ 0`.

So for each heat `λ > 0` the Riemann hypothesis at that heat is a statement about finitely many
continuous functions `t ↦ T_{2m}(λ, 0, t)` on a compact interval.  Heights above `T(λ)` are settled by
the effective slice Ki–Kim–Lee theorem (`exists_xiSliceHeatTransfer_pos_heat_over_log`), and orders
above `M(λ)` by the large-order positivity of the slice coefficients
(`exists_xiSliceCoeff_pos_large_order`).  The direction `⟹` is `λ_WD = 0`.
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

theorem mul_log_le_mul_log_of_le {t T : ℝ} (ht : 0 ≤ t) (hT : 1 ≤ T) (htT : t ≤ T) :
    t * Real.log t ≤ T * Real.log T := by
  rcases le_total t 1 with h1 | h1
  · have : t * Real.log t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (Real.log_nonpos ht h1)
    have : 0 ≤ T * Real.log T := mul_nonneg (by linarith) (Real.log_nonneg hT)
    linarith
  · exact mul_le_mul htT (Real.log_le_log (by linarith) htT) (Real.log_nonneg h1) (by linarith)

/-- **RH as compact heat checks.** -/
theorem exists_riemannHypothesis_iff_compact_heat_checks :
    ∃ t₀ K₀ : ℝ, RiemannHypothesis ↔ ∀ lam : ℝ, 0 < lam → ∀ t : ℝ, 0 ≤ t →
      t ≤ max t₀ (Real.exp (100 / lam)) → ∀ m : ℕ,
        (m : ℝ) < max K₀ (max t₀ (Real.exp (100 / lam)) *
          Real.log (max t₀ (Real.exp (100 / lam))) / 8) →
        0 ≤ xiSliceHeatTransfer lam 0 t (2 * m) := by
  obtain ⟨t₀, ht₀, hkkl⟩ := exists_xiSliceHeatTransfer_pos_heat_over_log
  obtain ⟨K₀, hK₀⟩ := exists_xiSliceCoeff_pos_large_order
  refine ⟨t₀, K₀, ⟨fun hRH lam hlam t _ _ m _ => ?_, fun h => ?_⟩⟩
  · have hW : wdHeatThreshold = 0 := riemannHypothesis_iff_wdHeatThreshold_eq_zero.mp hRH
    exact (xiSliceHeatTransfer_pos_of_gt (by rw [hW]; exact hlam) t m).le
  · refine riemannHypothesis_iff_wdHeatThreshold_eq_zero.mpr (le_antisymm ?_ wdHeatThreshold_nonneg)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    refine csInf_le wdHeatAdmissible_bddBelow fun t n => ?_
    set T := max t₀ (Real.exp (100 / ε)) with hT
    have hT1 : 1 ≤ T := le_trans (by linarith) (le_max_left _ _)
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    swap
    · rw [xiSliceHeatTransfer_odd_eq_zero hε.le]
    rw [← two_mul]
    -- reduce to nonnegative heights
    suffices key : ∀ u : ℝ, 0 ≤ u → 0 ≤ xiSliceHeatTransfer ε 0 u (2 * m) by
      rcases le_total 0 t with ht | ht
      · exact key t ht
      · rw [← neg_neg t, xiSliceHeatTransfer_neg_height hε]
        exact key (-t) (by linarith)
    intro u hu
    by_cases huT : T < u
    · -- large heights: effective Ki–Kim–Lee
      have hu0 : 0 < u := lt_of_le_of_lt (by linarith) huT
      have hut0 : t₀ ≤ |u| := by rw [abs_of_pos hu0]; exact le_trans (le_max_left _ _) huT.le
      have hexp : Real.exp (100 / ε) < u := lt_of_le_of_lt (le_max_right _ _) huT
      have hlog : 100 / ε < Real.log u := by
        rw [← Real.log_exp (100 / ε)]
        exact Real.log_lt_log (Real.exp_pos _) hexp
      have hlogpos : 0 < Real.log u := lt_trans (by positivity) hlog
      have hle : 100 / Real.log |u| ≤ ε := by
        rw [abs_of_pos hu0, div_le_iff₀ hlogpos]
        rw [div_lt_iff₀ hε] at hlog
        linarith
      exact (hkkl u hut0 ε hle m).le
    · push Not at huT
      by_cases hm : (m : ℝ) < max K₀ (T * Real.log T / 8)
      · exact h ε hε u hu huT m hm
      · -- large orders: all slice coefficients involved are positive
        push Not at hm
        have hcoef : ∀ k : ℕ, m ≤ k → 0 < xiSliceCoeff u (2 * k) := by
          intro k hk
          have hk' : (m : ℝ) ≤ k := by exact_mod_cast hk
          have hlogle := mul_log_le_mul_log_of_le hu hT1 huT
          refine hK₀ u hu k ?_ ?_
          · linarith [le_max_left K₀ (T * Real.log T / 8)]
          · linarith [le_max_right K₀ (T * Real.log T / 8)]
        have hT' := hasSum_xiSliceHeatTransfer_kernelSliceMoment hε.le 0 u (2 * m)
        simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT'
        have hterm : ∀ k : ℕ, 0 ≤ ((((ε / 2) ^ k / k.factorial *
            ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
              xiSliceCoeff u (2 * m + 2 * k)) := by
          intro k
          refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
          rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
          exact (hcoef (m + k) (by omega)).le
        exact le_trans (hterm 0) (le_hasSum hT' 0 fun j _ => hterm j)

end

end RHTower.DeBruijn
