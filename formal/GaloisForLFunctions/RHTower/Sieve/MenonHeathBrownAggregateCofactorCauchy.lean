import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownComplementCofactorReceiver
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIColoring

/-!
# Heath--Brown aggregate Cauchy with an attached cofactor

Finite Cauchy expands the window-relevant degree-three packet into its literal boxes while an
arbitrary cofactor remains attached at every original frequency.  No box selection or product
length is discarded.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Finite Cauchy across the literal degree-three Heath--Brown boxes, with an arbitrary
cofactor retained at each original frequency. -/
theorem sum_normSq_windowRelevantAggregate_mul_le_boxCores
    (L X : ℕ) (T0 t N : ℝ) (S : Finset ℕ)
    (s : ℕ → ℂ) (D : ℕ → ℂ) :
    ∑ r ∈ S,
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N (s r) * D r‖ ^ 2 ≤
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
        ∑ box : HeathBrownBoxChoice L X 3, ∑ r ∈ S,
          ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 := by
  classical
  have hpoint : ∀ r : ℕ,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N (s r) * D r‖ ^ 2 ≤
        (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
          ∑ box : HeathBrownBoxChoice L X 3,
            ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 := by
    intro r
    let f : HeathBrownBoxChoice L X 3 → ℂ := fun box =>
      (if IsHeathBrownBoxEligible L X 3 T0 t box ∧
          IsHeathBrownBoxWindowRelevant N X 3 box then
        heathBrownBoxTerm L X 3 box (s r)
      else 0) * D r
    have hsum :
        heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N (s r) * D r =
          ∑ box : HeathBrownBoxChoice L X 3, f box := by
      rw [heathBrownWindowRelevantEligibleDyadicAggregate, Finset.sum_mul]
    have hcs :
        ‖∑ box : HeathBrownBoxChoice L X 3, f box‖ ^ 2 ≤
          (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
            ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ ^ 2 := by
      have htri : ‖∑ box : HeathBrownBoxChoice L X 3, f box‖ ≤
          ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ := norm_sum_le _ _
      have hcauchy :
          (∑ box : HeathBrownBoxChoice L X 3, ‖f box‖) ^ 2 ≤
            (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
              ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (HeathBrownBoxChoice L X 3)))
          (f := fun box => ‖f box‖))
      nlinarith [norm_nonneg (∑ box : HeathBrownBoxChoice L X 3, f box),
        Finset.sum_nonneg (fun box (_ : box ∈
          (Finset.univ : Finset (HeathBrownBoxChoice L X 3))) => norm_nonneg (f box))]
    have hterm : ∀ box : HeathBrownBoxChoice L X 3,
        ‖f box‖ ^ 2 ≤ 64 *
          ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 := by
      intro box
      by_cases hbox : IsHeathBrownBoxEligible L X 3 T0 t box ∧
          IsHeathBrownBoxWindowRelevant N X 3 box
      · have hbase := norm_heathBrownBoxTerm_three_le_eight_mul_core box (s r)
        have hmul : ‖f box‖ ≤ 8 *
            ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ := by
          rw [show f box = heathBrownBoxTerm L X 3 box (s r) * D r by
            simp [f, hbox], norm_mul, norm_mul]
          calc
            ‖heathBrownBoxTerm L X 3 box (s r)‖ * ‖D r‖ ≤
                (8 * ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
                  (s r)‖) * ‖D r‖ :=
              mul_le_mul_of_nonneg_right hbase (norm_nonneg (D r))
            _ = 8 *
                (‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
                  (s r)‖ * ‖D r‖) := by ring
        nlinarith [norm_nonneg (f box),
          norm_nonneg (heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r)]
      · rw [show f box = 0 by simp [f, hbox]]
        simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64)
            (sq_nonneg
              ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
                (s r) * D r‖))
    rw [hsum]
    calc
      ‖∑ box : HeathBrownBoxChoice L X 3, f box‖ ^ 2 ≤
          (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
            ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ ^ 2 := hcs
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
            ∑ box : HeathBrownBoxChoice L X 3,
              (64 * ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
                (s r) * D r‖ ^ 2) := by
          gcongr with box
          exact hterm box
      _ = (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
            ∑ box : HeathBrownBoxChoice L X 3,
              ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
                (s r) * D r‖ ^ 2 := by
          rw [← Finset.mul_sum]
          ring
  calc
    ∑ r ∈ S,
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N (s r) * D r‖ ^ 2 ≤
      ∑ r ∈ S, (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
        ∑ box : HeathBrownBoxChoice L X 3,
          ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 :=
        Finset.sum_le_sum fun r _ => hpoint r
    _ = (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
        ∑ box : HeathBrownBoxChoice L X 3, ∑ r ∈ S,
          ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm

/-- Literal finite set of eligible, window-relevant degree-three boxes. -/
noncomputable def menonHeathBrownActiveBoxes
    (L X : ℕ) (T0 t N : ℝ) : Finset (HeathBrownBoxChoice L X 3) := by
  classical
  exact (Finset.univ : Finset (HeathBrownBoxChoice L X 3)).filter
    (fun box => IsHeathBrownBoxEligible L X 3 T0 t box ∧
      IsHeathBrownBoxWindowRelevant N X 3 box)

/-- Strong active-box form of aggregate Cauchy.  Ineligible or window-irrelevant boxes stay
absent from the receiver instead of being reintroduced as harmless nonnegative terms. -/
theorem sum_normSq_windowRelevantAggregate_mul_le_activeBoxCores
    (L X : ℕ) (T0 t N : ℝ) (S : Finset ℕ)
    (s : ℕ → ℂ) (D : ℕ → ℂ) :
    ∑ r ∈ S,
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N (s r) * D r‖ ^ 2 ≤
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
        ∑ box ∈ menonHeathBrownActiveBoxes L X T0 t N,
          ∑ r ∈ S,
            ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 := by
  classical
  let active : Finset (HeathBrownBoxChoice L X 3) :=
    menonHeathBrownActiveBoxes L X T0 t N
  have hpoint : ∀ r : ℕ,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N (s r) * D r‖ ^ 2 ≤
        (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
          ∑ box ∈ active,
            ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 := by
    intro r
    let f : HeathBrownBoxChoice L X 3 → ℂ := fun box =>
      (if IsHeathBrownBoxEligible L X 3 T0 t box ∧
          IsHeathBrownBoxWindowRelevant N X 3 box then
        heathBrownBoxTerm L X 3 box (s r)
      else 0) * D r
    have hsum :
        heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N (s r) * D r =
          ∑ box : HeathBrownBoxChoice L X 3, f box := by
      rw [heathBrownWindowRelevantEligibleDyadicAggregate, Finset.sum_mul]
    have hcs :
        ‖∑ box : HeathBrownBoxChoice L X 3, f box‖ ^ 2 ≤
          (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
            ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ ^ 2 := by
      have htri : ‖∑ box : HeathBrownBoxChoice L X 3, f box‖ ≤
          ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ := norm_sum_le _ _
      have hcauchy :
          (∑ box : HeathBrownBoxChoice L X 3, ‖f box‖) ^ 2 ≤
            (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
              ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (HeathBrownBoxChoice L X 3)))
          (f := fun box => ‖f box‖))
      nlinarith [norm_nonneg (∑ box : HeathBrownBoxChoice L X 3, f box),
        Finset.sum_nonneg (fun box (_ : box ∈
          (Finset.univ : Finset (HeathBrownBoxChoice L X 3))) => norm_nonneg (f box))]
    have hsumActive :
        ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ ^ 2 ≤
          64 * ∑ box ∈ active,
            ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 := by
      calc
        ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ ^ 2 =
            ∑ box ∈ active, ‖f box‖ ^ 2 := by
          symm
          refine Finset.sum_subset (Finset.subset_univ active) ?_
          intro box _ hnot
          have hbox : ¬ (IsHeathBrownBoxEligible L X 3 T0 t box ∧
              IsHeathBrownBoxWindowRelevant N X 3 box) := by
            intro hactive
            exact hnot (by
              simp only [active, menonHeathBrownActiveBoxes, Finset.mem_filter,
                Finset.mem_univ, true_and]
              exact hactive)
          simp [f, hbox]
        _ ≤ ∑ box ∈ active,
            64 * ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
              (s r) * D r‖ ^ 2 := by
          refine Finset.sum_le_sum fun box hbox => ?_
          have hactive := (Finset.mem_filter.mp hbox).2
          have hbase := norm_heathBrownBoxTerm_three_le_eight_mul_core box (s r)
          have hmul : ‖f box‖ ≤ 8 *
              ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ := by
            rw [show f box = heathBrownBoxTerm L X 3 box (s r) * D r by
              simp [f, hactive], norm_mul, norm_mul]
            calc
              ‖heathBrownBoxTerm L X 3 box (s r)‖ * ‖D r‖ ≤
                  (8 * ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
                    (s r)‖) * ‖D r‖ :=
                mul_le_mul_of_nonneg_right hbase (norm_nonneg (D r))
              _ = 8 *
                  (‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
                    (s r)‖ * ‖D r‖) := by ring
          nlinarith [norm_nonneg (f box),
            norm_nonneg
              (heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r)]
        _ = 64 * ∑ box ∈ active,
            ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
              (s r) * D r‖ ^ 2 := by rw [Finset.mul_sum]
    rw [hsum]
    have hcard0 : 0 ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) := by
      positivity
    calc
      ‖∑ box : HeathBrownBoxChoice L X 3, f box‖ ^ 2 ≤
          (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
            ∑ box : HeathBrownBoxChoice L X 3, ‖f box‖ ^ 2 := hcs
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
          (64 * ∑ box ∈ active,
            ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
              (s r) * D r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsumActive hcard0
      _ = _ := by ring
  calc
    ∑ r ∈ S,
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N (s r) * D r‖ ^ 2 ≤
      ∑ r ∈ S, (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
        ∑ box ∈ active,
          ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q (s r) * D r‖ ^ 2 :=
        Finset.sum_le_sum fun r _ => hpoint r
    _ = (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
        ∑ box ∈ active, ∑ r ∈ S,
          ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
            (s r) * D r‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ = _ := by rfl

end

end RHTower.Sieve
