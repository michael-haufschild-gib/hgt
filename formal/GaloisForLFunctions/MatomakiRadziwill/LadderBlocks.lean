import GaloisForLFunctions.MatomakiRadziwill.RamareBlockMVT

/-!
# Prime blocks and cofactor polynomials of one scale

The block decomposition of a scale is `Σ_v Q_v(w) R_v(w)` (`pairPoly_eq_sum_blocks`), with

* `Q_v = Σ_{p ∈ Pr, ⌊H log p⌋ = v} f(p)/p · p^{2πiw}` (`blockQ`),
* `R_v = Σ_{m ∈ cof(v)} f(m)/((ω(m)+1)m) · m^{2πiw}` (`blockR`).

Pointwise Cauchy–Schwarz gives `|Σ_v Q_v R_v|² ≤ #V Σ_v |Q_v|²|R_v|²` (`normSq_sum_blocks_le`), and
the mean value theorem gives `∫_{|w| ≤ W} |R_v|² ≤ 10πW/lo + 40e` for the cofactor range
`(lo, 4lo]`, `lo = Xe^{-v/H} ≥ 1` (`integral_normSq_blockR_le`).
-/

open Finset MeasureTheory RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The prime block `Q_v`. -/
def blockQ (f : ℕ → ℂ) (Pr : Finset ℕ) (H : ℝ) (v : ℕ) (w : ℝ) : ℂ :=
  logPoly (coefA f) (Pr.filter fun p => blk H p = v) w

/-- The cofactor polynomial `R_v`. -/
def blockR (f : ℕ → ℂ) (Pr : Finset ℕ) (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ)
    (v : ℕ) (w : ℝ) : ℂ :=
  logPoly (coefC f Pr) (cof rest X H v) w

/-- **The block decomposition is a sum of products.** -/
theorem pairPoly_eq_sum_blocks (f : ℕ → ℂ) {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime)
    (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) (w : ℝ) :
    pairPoly f Pr rest X H w
      = ∑ v ∈ Pr.image (blk H), blockQ f Pr H v w * blockR f Pr rest X H v w := by
  classical
  have hrow : ∀ p ∈ Pr, ∑ m ∈ cof rest X H (blk H p),
      coefA f p * coefC f Pr m * unitLogPhase w (p * m)
      = coefA f p * unitLogPhase w p * blockR f Pr rest X H (blk H p) w := by
    intro p hp
    rw [blockR, logPoly_eq_sum_mul_unitLogPhase, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := by
      have : (0 : ℝ) < m := lt_of_le_of_lt (cofLo_nonneg X H _) (mem_cof.mp hm).1
      exact_mod_cast this
    rw [unitLogPhase_mul w (hPr p hp).ne_zero hm0.ne']
    ring
  rw [pairPoly, sum_congr rfl hrow,
    ← sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem (blk H) hp)]
  refine sum_congr rfl fun v _ => ?_
  rw [blockQ, logPoly_eq_sum_mul_unitLogPhase, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [(mem_filter.mp hp).2]

/-- **Pointwise Cauchy–Schwarz over the blocks.** -/
theorem normSq_sum_blocks_le {V : Finset ℕ} (Q R : ℕ → ℂ) :
    ‖∑ v ∈ V, Q v * R v‖ ^ 2 ≤ (V.card : ℝ) * ∑ v ∈ V, ‖Q v‖ ^ 2 * ‖R v‖ ^ 2 := by
  have h1 : ‖∑ v ∈ V, Q v * R v‖ ≤ ∑ v ∈ V, ‖Q v‖ * ‖R v‖ := by
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    exact sum_congr rfl fun v _ => norm_mul _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := V) (f := fun v => ‖Q v‖ * ‖R v‖)
  calc ‖∑ v ∈ V, Q v * R v‖ ^ 2 ≤ (∑ v ∈ V, ‖Q v‖ * ‖R v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (V.card : ℝ) * ∑ v ∈ V, (‖Q v‖ * ‖R v‖) ^ 2 := h2
    _ = (V.card : ℝ) * ∑ v ∈ V, ‖Q v‖ ^ 2 * ‖R v‖ ^ 2 := by
        congr 1
        exact sum_congr rfl fun v _ => by ring

theorem norm_coefC_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (Pr : Finset ℕ) (m : ℕ) :
    ‖coefC f Pr m‖ ≤ 1 / m := by
  rw [coefC, norm_div, norm_mul, Complex.norm_natCast]
  have hw : (1 : ℝ) ≤ ‖(((omegaIn Pr m : ℝ) + 1 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : (0 : ℝ) ≤ omegaIn Pr m := Nat.cast_nonneg _
    rw [abs_of_pos (by linarith)]
    linarith
  push_cast at hw ⊢
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0; simp
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_le_div_iff₀ (by positivity) hm0, one_mul]
    calc ‖f m‖ * (m : ℝ) ≤ 1 * m := mul_le_mul_of_nonneg_right (hf m) hm0.le
      _ ≤ ‖((omegaIn Pr m : ℂ) + 1)‖ * m := mul_le_mul_of_nonneg_right hw hm0.le

/-- `#cof(v) ≤ 3 lo + 1`. -/
theorem card_cof_le (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) (v : ℕ) :
    ((cof rest X H v).card : ℝ) ≤ 3 * cofLo X H v + 1 := by
  have h0 := cofLo_nonneg X H v
  have hsub : cof rest X H v ⊆ Ioc ⌊cofLo X H v⌋₊ ⌊4 * cofLo X H v⌋₊ := filter_subset _ _
  have h1 := card_le_card hsub
  rw [Nat.card_Ioc] at h1
  have hfl1 : (⌊4 * cofLo X H v⌋₊ : ℝ) ≤ 4 * cofLo X H v := Nat.floor_le (by linarith)
  have hfl2 : cofLo X H v < (⌊cofLo X H v⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hab : ⌊cofLo X H v⌋₊ ≤ ⌊4 * cofLo X H v⌋₊ := Nat.floor_le_floor (by linarith)
  have h2 : ((⌊4 * cofLo X H v⌋₊ - ⌊cofLo X H v⌋₊ : ℕ) : ℝ)
      = (⌊4 * cofLo X H v⌋₊ : ℝ) - ⌊cofLo X H v⌋₊ := Nat.cast_sub hab
  have h1' : ((cof rest X H v).card : ℝ) ≤ ((⌊4 * cofLo X H v⌋₊ - ⌊cofLo X H v⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith

/-- **The mean value theorem for a cofactor polynomial.** -/
theorem integral_normSq_blockR_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (Pr : Finset ℕ)
    (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) (v : ℕ)
    (hlo : 1 ≤ cofLo X H v) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖blockR f Pr rest X H v w‖ ^ (2 : ℕ))
      ≤ 10 * Real.pi * W / cofLo X H v + 40 * Real.exp 1 := by
  classical
  set lo := cofLo X H v with hlodef
  have hmem : ∀ m ∈ cof rest X H v, lo < m ∧ (m : ℝ) ≤ 4 * lo := fun m hm =>
    ⟨(mem_cof.mp hm).1, (mem_cof.mp hm).2.1⟩
  have hbase := integral_normSq_sum_unitLogPhase_le (cof rest X H v) id (coefC f Pr)
    (fun m hm => by
      have : (0 : ℝ) < m := lt_of_le_of_lt (by linarith) (hmem m hm).1
      exact_mod_cast this)
    (N := ⌊4 * lo⌋₊) (fun m hm => Nat.le_floor (hmem m hm).2) hW
  have hfib : ∑ n ∈ (cof rest X H v).image id,
        ‖∑ i ∈ cof rest X H v with id i = n, coefC f Pr i‖ ^ (2 : ℕ)
      = ∑ m ∈ cof rest X H v, ‖coefC f Pr m‖ ^ 2 := by
    rw [image_id]
    refine sum_congr rfl fun n hn => ?_
    have : (cof rest X H v).filter (fun i => id i = n) = {n} := by
      ext i
      simp only [mem_filter, mem_singleton, id]
      exact ⟨fun h => h.2, by rintro rfl; exact ⟨hn, rfl⟩⟩
    rw [this, sum_singleton]
  simp_rw [blockR, logPoly_eq_sum_mul_unitLogPhase]
  rw [hfib] at hbase
  have hterm : ∀ m ∈ cof rest X H v, ‖coefC f Pr m‖ ^ 2 ≤ 1 / lo ^ 2 := by
    intro m hm
    have h1 := norm_coefC_le hf Pr m
    have h2 : (1 : ℝ) / m ≤ 1 / lo := one_div_le_one_div_of_le (by linarith) (hmem m hm).1.le
    calc ‖coefC f Pr m‖ ^ 2 ≤ (1 / lo) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ = 1 / lo ^ 2 := by ring
  have hsum : ∑ m ∈ cof rest X H v, ‖coefC f Pr m‖ ^ 2 ≤ 4 / lo := by
    calc ∑ m ∈ cof rest X H v, ‖coefC f Pr m‖ ^ 2
        ≤ ∑ _m ∈ cof rest X H v, 1 / lo ^ 2 := sum_le_sum hterm
      _ = ((cof rest X H v).card : ℝ) * (1 / lo ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (3 * lo + 1) * (1 / lo ^ 2) :=
          mul_le_mul_of_nonneg_right (card_cof_le rest X H v) (by positivity)
      _ ≤ 4 / lo := by
          rw [show (3 * lo + 1) * (1 / lo ^ 2) = (3 * lo + 1) / lo ^ 2 by ring,
            div_le_div_iff₀ (by positivity) (by linarith)]
          nlinarith
  have hN : ((⌊4 * lo⌋₊ : ℕ) : ℝ) ≤ 4 * lo := Nat.floor_le (by linarith)
  have hcoef0 : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊4 * lo⌋₊ : ℕ) : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le
    have : (0 : ℝ) ≤ W := by linarith
    positivity
  calc (∫ w in Set.Icc (-W) W, ‖∑ m ∈ cof rest X H v, coefC f Pr m * unitLogPhase w m‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊4 * lo⌋₊ : ℕ) : ℝ))
          * ∑ m ∈ cof rest X H v, ‖coefC f Pr m‖ ^ 2 := hbase
    _ ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (4 * lo)) * (4 / lo) := by
        refine mul_le_mul (by nlinarith [Real.exp_pos 1]) hsum (sum_nonneg fun _ _ => by positivity)
          (by have := Real.pi_pos; have := (Real.exp_pos 1).le; nlinarith)
    _ = 10 * Real.pi * W / lo + 40 * Real.exp 1 := by
        field_simp
        ring

end

end GaloisForLFunctions.MatomakiRadziwill
