import GaloisForLFunctions.HTGeometry.IntegrableOfBoundedWindows

/-!
# Square integrability of a window limit

If the window masses of a family are bounded by one constant and converge to the window masses of a
limit function, then the limit has the same bound on every window, hence is square integrable.

No Fatou lemma is needed: the bound passes to the limit by `le_of_tendsto`, and the criterion of
bounded window masses does the rest.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Square integrability of a window limit.** -/
theorem integrable_sq_of_bounded_window_limits {ι : Type*} {L : Filter ι} [L.NeBot]
    {f : ι → ℝ → ℝ} {v : ℝ → ℝ} {N : ℝ} (hv : Continuous v)
    (hconv : ∀ K : ℝ, 0 < K → Tendsto (fun i => ∫ x in (-K)..K, f i x * f i x) L
      (𝓝 (∫ x in (-K)..K, v x * v x)))
    (hb : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, (∫ x in (-K)..K, f i x * f i x) ≤ N) :
    Integrable fun x => v x ^ 2 := by
  have hNnn : 0 ≤ N := by
    obtain ⟨i, hi⟩ := (hb 1 one_pos).exists
    refine le_trans ?_ hi
    refine intervalIntegral.integral_nonneg (by norm_num) fun x _ => ?_
    nlinarith [sq_nonneg (f i x)]
  refine integrable_of_bounded_windows (hv.pow 2) (fun x => sq_nonneg _) (C := N) ?_
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hset : Icc (-((0 : ℕ) : ℝ)) ((0 : ℕ) : ℝ) = {(0 : ℝ)} := by
      norm_num
    rw [hset, MeasureTheory.setIntegral_measure_zero]
    · exact hNnn
    · simp
  · have hKpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hle : -((n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by linarith
    have hIcc : (∫ x in Icc (-((n : ℕ) : ℝ)) ((n : ℕ) : ℝ), v x ^ 2)
        = ∫ x in (-((n : ℕ) : ℝ))..((n : ℕ) : ℝ), v x * v x := by
      rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x _ => by ring
    rw [hIcc]
    refine le_of_tendsto (hconv _ hKpos) ?_
    filter_upwards [hb _ hKpos] with i hi
    exact hi

end GaloisForLFunctions.HTGeometry
