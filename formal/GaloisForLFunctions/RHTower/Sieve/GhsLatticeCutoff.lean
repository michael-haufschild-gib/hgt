import GaloisForLFunctions.RHTower.Sieve.DistinctReciprocalSum

/-!
# The lattice estimate at the Perron cutoff

Only three multiples of `d` can lie within distance `d` of `X`; every other multiple is at distance
at least `d|n − n₀|/2` from it, where `n₀ = ⌊X/d⌋`.  Summing the reciprocals of the distinct
integers `n − n₀` therefore costs only a harmonic factor, which is the estimate `(E3)` that keeps
the truncated Perron error factor-aware.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- **Lemma E, equation (E3).**  The lattice estimate near the Perron cutoff: ordering the
multiples of `d` by distance from `X`, the truncated Perron weights sum to `O(1 + X log M/(T d))`. -/
theorem lattice_min_sum_le {X d T : ℝ} (hX : 0 < X) (hd : 0 < d) (hT : 0 < T) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, min 1 (X / (T * |X - d * (n : ℝ)|))
      ≤ 3 + (4 * X / (T * d)) * (1 + Real.log M) := by
  classical
  set n₀ : ℕ := ⌊X / d⌋₊ with hn₀
  set Mid : Finset ℕ := (Finset.Icc 1 M).filter (fun n => n₀ ≤ n + 1 ∧ n ≤ n₀ + 1) with hMid
  set Far : Finset ℕ := (Finset.Icc 1 M).filter (fun n => ¬ (n₀ ≤ n + 1 ∧ n ≤ n₀ + 1)) with hFar
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M)
    (fun n => n₀ ≤ n + 1 ∧ n ≤ n₀ + 1) (fun n => min 1 (X / (T * |X - d * (n : ℝ)|)))
  have hMidcard : Mid.card ≤ 3 := by
    have hsub : Mid ⊆ Finset.Icc (n₀ - 1) (n₀ + 1) := by
      intro n hn
      rw [hMid, Finset.mem_filter] at hn
      rw [Finset.mem_Icc]
      omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have hMidsum : ∑ n ∈ Mid, min 1 (X / (T * |X - d * (n : ℝ)|)) ≤ 3 := by
    have hterm : ∀ n ∈ Mid, min 1 (X / (T * |X - d * (n : ℝ)|)) ≤ 1 := fun n _ => min_le_left _ _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast hMidcard
  have hFarsum : ∑ n ∈ Far, min 1 (X / (T * |X - d * (n : ℝ)|))
      ≤ (4 * X / (T * d)) * (1 + Real.log M) := by
    have hfrac : (0 : ℝ) ≤ X / d - (n₀ : ℝ) := by
      rw [hn₀, sub_nonneg]
      exact Nat.floor_le (by positivity)
    have hfrac1 : X / d - (n₀ : ℝ) < 1 := by
      have h := Nat.lt_floor_add_one (X / d)
      rw [hn₀]
      linarith
    have hterm : ∀ n ∈ Far, min 1 (X / (T * |X - d * (n : ℝ)|))
        ≤ (2 * X / (T * d)) * (1 / |((((n : ℤ) - (n₀ : ℤ)) : ℤ) : ℝ)|) := by
      intro n hn
      rw [hFar, Finset.mem_filter] at hn
      have hne : 2 ≤ |((n : ℤ) - (n₀ : ℤ))| := by
        have h := hn.2
        rcases Nat.lt_or_ge (n + 1) n₀ with hc | hc
        · rw [abs_of_nonpos (by omega)]
          omega
        · rw [abs_of_nonneg (by omega)]
          omega
      have hneR : (2 : ℝ) ≤ |((n : ℝ) - (n₀ : ℝ))| := by
        have hc : ((|((n : ℤ) - (n₀ : ℤ))| : ℤ) : ℝ) = |((n : ℝ) - (n₀ : ℝ))| := by
          push_cast
          rfl
        rw [← hc]
        exact_mod_cast hne
      have hdist : d * (|((n : ℝ) - (n₀ : ℝ))| / 2) ≤ |X - d * (n : ℝ)| := by
        have hkey : |((n : ℝ) - (n₀ : ℝ))| - 1 ≤ |X / d - (n : ℝ)| := by
          have h1 : |(n : ℝ) - (n₀ : ℝ)| ≤ |X / d - (n : ℝ)| + |X / d - (n₀ : ℝ)| := by
            have := abs_sub_abs_le_abs_sub ((n : ℝ) - X / d) ((n₀ : ℝ) - X / d)
            calc |(n : ℝ) - (n₀ : ℝ)| = |((n : ℝ) - X / d) - ((n₀ : ℝ) - X / d)| := by
                  congr 1; ring
              _ ≤ |(n : ℝ) - X / d| + |(n₀ : ℝ) - X / d| := abs_sub _ _
              _ = |X / d - (n : ℝ)| + |X / d - (n₀ : ℝ)| := by
                  rw [abs_sub_comm ((n : ℝ)), abs_sub_comm ((n₀ : ℝ))]
          have h2 : |X / d - (n₀ : ℝ)| ≤ 1 := by
            rw [abs_of_nonneg hfrac]
            linarith
          linarith
        have habs : |X - d * (n : ℝ)| = d * |X / d - (n : ℝ)| := by
          have he : X - d * (n : ℝ) = d * (X / d - (n : ℝ)) := by field_simp
          rw [he, abs_mul, abs_of_pos hd]
        rw [habs]
        have : |((n : ℝ) - (n₀ : ℝ))| / 2 ≤ |X / d - (n : ℝ)| := by linarith
        exact mul_le_mul_of_nonneg_left this hd.le
      have hpos : (0 : ℝ) < |((n : ℝ) - (n₀ : ℝ))| := by linarith
      have hdpos : (0 : ℝ) < d * (|((n : ℝ) - (n₀ : ℝ))| / 2) := by positivity
      have hXabs : (0 : ℝ) < |X - d * (n : ℝ)| := lt_of_lt_of_le hdpos hdist
      have hcast : |((((n : ℤ) - (n₀ : ℤ)) : ℤ) : ℝ)| = |((n : ℝ) - (n₀ : ℝ))| := by
        push_cast
        rfl
      rw [hcast]
      refine le_trans (min_le_right _ _) ?_
      rw [div_le_iff₀ (by positivity)]
      have hstep : X ≤ (2 * X / (T * d)) * (1 / |((n : ℝ) - (n₀ : ℝ))|)
          * (T * |X - d * (n : ℝ)|) := by
        have h5 : (2 * X / (T * d)) * (1 / |((n : ℝ) - (n₀ : ℝ))|) * (T * |X - d * (n : ℝ)|)
            ≥ (2 * X / (T * d)) * (1 / |((n : ℝ) - (n₀ : ℝ))|)
              * (T * (d * (|((n : ℝ) - (n₀ : ℝ))| / 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hdist hT.le
        have h6 : (2 * X / (T * d)) * (1 / |((n : ℝ) - (n₀ : ℝ))|)
            * (T * (d * (|((n : ℝ) - (n₀ : ℝ))| / 2))) = X := by
          field_simp
        linarith
      linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hinj : ∀ i ∈ Far, ∀ j ∈ Far, ((i : ℤ) - (n₀ : ℤ)) = ((j : ℤ) - (n₀ : ℤ)) → i = j := by
      intro i _ j _ h
      omega
    have hnez : ∀ i ∈ Far, ((i : ℤ) - (n₀ : ℤ)) ≠ 0 := by
      intro i hi
      rw [hFar, Finset.mem_filter] at hi
      have h := hi.2
      omega
    have hrec := sum_inv_abs_le_of_injOn Far (fun i => (i : ℤ) - (n₀ : ℤ)) hinj hnez
    have hcard : (Far.card : ℝ) ≤ (M : ℝ) := by
      have : Far.card ≤ (Finset.Icc 1 M).card := Finset.card_le_card (Finset.filter_subset _ _)
      rw [Nat.card_Icc] at this
      have h2 : Far.card ≤ M := by omega
      exact_mod_cast h2
    have hlog : Real.log (Far.card : ℝ) ≤ Real.log (M : ℝ) := by
      rcases Nat.eq_zero_or_pos Far.card with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        rcases Nat.eq_zero_or_pos M with hM | hM
        · rw [hM]; simp
        · exact Real.log_nonneg (by exact_mod_cast hM)
      · exact Real.log_le_log (by exact_mod_cast h0) hcard
    have hcoef : (0 : ℝ) ≤ 2 * X / (T * d) := by positivity
    have hstep1 : (2 * X / (T * d))
        * (∑ i ∈ Far, 1 / |((((i : ℤ) - (n₀ : ℤ)) : ℤ) : ℝ)|)
        ≤ (2 * X / (T * d)) * (2 * (1 + Real.log (Far.card : ℝ))) :=
      mul_le_mul_of_nonneg_left hrec hcoef
    have hstep2 : (2 * X / (T * d)) * (2 * (1 + Real.log (Far.card : ℝ)))
        ≤ (4 * X / (T * d)) * (1 + Real.log (M : ℝ)) := by
      have hid : (2 * X / (T * d)) * (2 * (1 + Real.log (Far.card : ℝ)))
          = (4 * X / (T * d)) * (1 + Real.log (Far.card : ℝ)) := by ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  linarith [hsplit, hMidsum, hFarsum]

end

end RHTower.Sieve
