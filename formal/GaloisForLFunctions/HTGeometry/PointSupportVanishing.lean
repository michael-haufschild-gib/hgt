import GaloisForLFunctions.HTGeometry.SchwartzCompactSupport
import GaloisForLFunctions.HTGeometry.TemperedOrder

/-!
# A distribution supported at the origin kills every function vanishing to high order

If a tempered distribution annihilates every Schwartz function vanishing near the origin, then it
annihilates every Schwartz function whose derivatives up to the order of the distribution vanish at
the origin.  The mechanism is the localisation estimate: replacing `φ` by `χ_ε φ` changes nothing,
while each Schwartz seminorm of `χ_ε φ` is `O(ε)`.
-/

open Set SchwartzMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **Vanishing to the order of the distribution forces annihilation.** -/
theorem exists_order_apply_eq_zero (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    (hu : ∀ ψ : SchwartzMap ℝ ℂ, (∃ δ > 0, ∀ x : ℝ, |x| ≤ δ → (ψ : ℝ → ℂ) x = 0) → u ψ = 0) :
    ∃ N : ℕ, ∀ φ : SchwartzMap ℝ ℂ,
      (∀ j, j ≤ N → iteratedDeriv j (φ : ℝ → ℂ) 0 = 0) → u φ = 0 := by
  obtain ⟨s, C, hC, hbound⟩ := exists_schwartz_seminorm_bound u
  refine ⟨s.sup (fun p => p.2), fun φ hvanish => ?_⟩
  set N := s.sup (fun p : ℕ × ℕ => p.2) with hN
  -- a bound for the top derivative on the unit interval
  have hcont : ContinuousOn (fun t : ℝ => ‖iteratedDeriv (N+1) (φ : ℝ → ℂ) t‖) (Icc (-1:ℝ) 1) :=
    (ContDiff.continuous_iteratedDeriv (N+1) φ.smooth'
      (by exact_mod_cast le_top)).norm.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  have hMle : ∀ t ∈ Icc (-1:ℝ) 1, ‖iteratedDeriv (N+1) (φ : ℝ → ℂ) t‖ ≤ M := by
    intro t ht
    have := hM t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
    exact this
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hMle 0 ⟨by norm_num, by norm_num⟩)
  set K : ℝ := C * (∑ p ∈ s, (2:ℝ) ^ p.1 * cutoffProductConst M N p.2) with hK
  have hKnn : 0 ≤ K := by
    refine mul_nonneg (le_of_lt hC) (Finset.sum_nonneg fun p _ => ?_)
    exact mul_nonneg (by positivity) (cutoffProductConst_nonneg hMnn N p.2)
  -- the localisation estimate
  have key : ∀ ε : ℝ, 0 < ε → 2 * ε ≤ 1 → ‖u φ‖ ≤ K * ε := by
    intro ε hε hε1
    have hε01 : ε ≤ 1 := by linarith
    -- the difference is supported away from the origin
    have hdiff : u (φ - cutoffSchwartz ε hε φ) = 0 := by
      refine hu _ ⟨ε, hε, fun x hx => ?_⟩
      have : (φ - cutoffSchwartz ε hε φ : SchwartzMap ℝ ℂ) x
          = (φ : ℝ → ℂ) x - (cutoffSchwartz ε hε φ : ℝ → ℂ) x := rfl
      rw [this]
      exact sub_cutoffSchwartz_eq_zero_near hε hx
    have hsame : u φ = u (cutoffSchwartz ε hε φ) := by
      have := congrArg (fun y => y + u (cutoffSchwartz ε hε φ)) hdiff
      simp only [map_sub, sub_add_cancel, zero_add] at this
      exact this
    -- each seminorm of the localisation is `O(ε)`
    have hsem : (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (cutoffSchwartz ε hε φ)
        ≤ (∑ p ∈ s, (2:ℝ) ^ p.1 * cutoffProductConst M N p.2) * ε := by
      have hsumnn : (0:ℝ) ≤ (∑ q ∈ s, (2:ℝ) ^ q.1 * cutoffProductConst M N q.2) * ε :=
        mul_nonneg (Finset.sum_nonneg fun q _ =>
          mul_nonneg (by positivity) (cutoffProductConst_nonneg hMnn N q.2)) hε.le
      refine Seminorm.finset_sup_apply_le hsumnn fun p hp => ?_
      have hple : p.2 ≤ N := Finset.le_sup (f := fun q : ℕ × ℕ => q.2) hp
      have hbnd := seminorm_cutoffSchwartz_le (φ := φ) (N := N) (M := M) hvanish hMle p.1 p.2
        hple hε hε1
      have hpow : ε ^ (p.1 + (N - p.2 + 1)) ≤ ε := by
        have h1 : (1:ℕ) ≤ p.1 + (N - p.2 + 1) := by omega
        calc ε ^ (p.1 + (N - p.2 + 1)) ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε01 h1
          _ = ε := pow_one ε
      have hcoef : (0:ℝ) ≤ (2:ℝ) ^ p.1 * cutoffProductConst M N p.2 :=
        mul_nonneg (by positivity) (cutoffProductConst_nonneg hMnn N p.2)
      have hterm : ((2:ℝ) ^ p.1 * cutoffProductConst M N p.2) * ε ^ (p.1 + (N - p.2 + 1))
          ≤ ((2:ℝ) ^ p.1 * cutoffProductConst M N p.2) * ε :=
        mul_le_mul_of_nonneg_left hpow hcoef
      have hsum : ((2:ℝ) ^ p.1 * cutoffProductConst M N p.2) * ε
          ≤ (∑ q ∈ s, (2:ℝ) ^ q.1 * cutoffProductConst M N q.2) * ε := by
        refine mul_le_mul_of_nonneg_right ?_ hε.le
        refine Finset.single_le_sum (f := fun q : ℕ × ℕ => (2:ℝ) ^ q.1 * cutoffProductConst M N q.2)
          (fun q _ => mul_nonneg (by positivity) (cutoffProductConst_nonneg hMnn N q.2)) hp
      have : (schwartzSeminormFamily ℂ ℝ ℂ) p (cutoffSchwartz ε hε φ)
          ≤ ((2:ℝ) ^ p.1 * cutoffProductConst M N p.2) * ε ^ (p.1 + (N - p.2 + 1)) := hbnd
      linarith [this, hterm, hsum]
    calc ‖u φ‖ = ‖u (cutoffSchwartz ε hε φ)‖ := by rw [hsame]
      _ ≤ C * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (cutoffSchwartz ε hε φ) :=
          hbound (cutoffSchwartz ε hε φ)
      _ ≤ C * ((∑ p ∈ s, (2:ℝ) ^ p.1 * cutoffProductConst M N p.2) * ε) :=
          mul_le_mul_of_nonneg_left hsem (le_of_lt hC)
      _ = K * ε := by rw [hK]; ring
  -- let the localisation scale tend to zero
  by_contra hne
  have hpos : 0 < ‖u φ‖ := norm_pos_iff.mpr hne
  rcases le_or_gt K 0 with hK0 | hK0
  · have := key (1/2) (by norm_num) (by norm_num)
    nlinarith [hpos, this]
  · set ε : ℝ := min (1/2) (‖u φ‖ / (2 * K)) with hεdef
    have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : 2 * ε ≤ 1 := by
      have : ε ≤ 1/2 := min_le_left _ _
      linarith
    have hkey := key ε hεpos hε1
    have hεle : ε ≤ ‖u φ‖ / (2 * K) := min_le_right _ _
    have : K * ε ≤ ‖u φ‖ / 2 := by
      calc K * ε ≤ K * (‖u φ‖ / (2 * K)) := mul_le_mul_of_nonneg_left hεle (le_of_lt hK0)
        _ = ‖u φ‖ / 2 := by field_simp
    linarith [hkey, this, hpos]

end

end GaloisForLFunctions.HTGeometry
