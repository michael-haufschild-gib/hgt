import GaloisForLFunctions.RHTower.Sieve.MaynardEligibleAggregate

/-!
# Corrected aggregate-to-greedy-group selection

This is the pointwise all-short selector after removing the false universal-total premise.  A
bound for the complementary low-total signed aggregate forces a large eligible box; exact scalar
removal and robust greedy grouping then produce the literal Huxley factor.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Exact cost of selecting one eligible box and removing its signed binomial scalar. -/
def heathBrownEligibleBoxCost (L X k : ℕ) : ℝ :=
  (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) * (2 ^ k : ℝ)

theorem heathBrownEligibleBoxCost_pos
    (L X k : ℕ) (hk : 0 < k) : 0 < heathBrownEligibleBoxCost L X k := by
  have hne := nonempty_heathBrownBoxChoice L X k hk
  have hcard : 0 < Fintype.card (HeathBrownBoxChoice L X k) :=
    Fintype.card_pos_iff.mpr hne
  dsimp [heathBrownEligibleBoxCost]
  positivity

/-- **Corrected pointwise aggregate-to-group theorem.** -/
theorem exists_heathBrown_eligible_aggregate_dyadic_robust_group
    (L X k : ℕ) (hk : 0 < k) {T0 t e V E : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t) (hV : 0 < V) (s : ℂ)
    (haggregate : V + E ≤ ‖heathBrownDyadicAggregate L X k s‖)
    (hlow : ‖heathBrownLowTotalDyadicAggregate L X k T0 t s‖ ≤ E)
    (hshort : ∀ c : HeathBrownBoxChoice L X k,
      ∀ i : HeathBrownBoxFactorIndex k c.m,
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t)
    (hreserve : ∀ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c →
        heathBrownEligibleBoxCost L X k *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤ V) :
    ∃ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c ∧
        ∃ u : Finset (HeathBrownBoxFactorIndex k c.m), u.Nonempty ∧
          let alpha := ∑ i ∈ u,
            dyadicLogExponent T0
              (heathBrownBoxFactorExponent c.a c.b c.q i)
          t ≤ alpha ∧ alpha < 4 * t ∧
            u.card ≤ Fintype.card (HeathBrownBoxFactorIndex k c.m) ∧
            ((groupedDyadicLower
              (fun i : {i // i ∈ u} =>
                heathBrownBoxFactorExponent c.a c.b c.q i) : ℕ) : ℝ) =
                T0 ^ alpha ∧
            ((groupedDyadicLower
              (fun i : {i // i ∈ u} =>
                heathBrownBoxFactorExponent c.a c.b c.q i) : ℕ) : ℝ) ^ e ≤
              ‖∏ i : {i // i ∈ u}, LSeries
                (complexCoeff (arithmeticDyadicBlock
                  (heathBrownFactorBase L X
                    (heathBrownBoxFactorKind k c.m i))
                  (heathBrownBoxFactorExponent c.a c.b c.q i))) s‖ := by
  have heligLarge : V ≤ ‖heathBrownEligibleDyadicAggregate L X k T0 t s‖ :=
    norm_heathBrownEligibleDyadicAggregate_ge_of_lowTotal L X k T0 t s
      haggregate hlow
  obtain ⟨c, helig, hterm⟩ :=
    exists_large_eligible_heathBrownBox L X k hk T0 t s hV heligLarge
  have hterm' : V ≤ heathBrownEligibleBoxCost L X k *
      ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q s‖ := by
    dsimp [heathBrownBoxTerm] at hterm
    rw [norm_heathBrownDyadicTermProduct_eq_choose_mul_core] at hterm
    have hchoose : (k.choose c.m : ℝ) ≤ (2 ^ k : ℝ) := by
      exact_mod_cast Nat.choose_le_two_pow k c.m
    calc
      V ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
          ((k.choose c.m : ℝ) *
            ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q s‖) := hterm
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
          ((2 ^ k : ℝ) *
            ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q s‖) := by
        gcongr
      _ = heathBrownEligibleBoxCost L X k *
          ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q s‖ := by
        simp [heathBrownEligibleBoxCost, mul_assoc]
  have hscaled := (hreserve c helig).trans hterm'
  have hPpos := heathBrownEligibleBoxCost_pos L X k hk
  have hcore :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤
          ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q s‖ := by
    exact (mul_le_mul_iff_right₀ hPpos).mp hscaled
  have htotal : t ≤ ∑ i : HeathBrownBoxFactorIndex k c.m,
      dyadicLogExponent T0
        (heathBrownBoxFactorExponent c.a c.b c.q i) := by
    simpa [IsHeathBrownBoxEligible, heathBrownBoxTotalExponent] using helig
  obtain ⟨u, hu⟩ := exists_heathBrown_box_dyadic_robust_group
    L X k c.m c.a c.b c.q hT0 ht (hshort c) htotal s hcore
  exact ⟨c, helig, u, hu⟩

end RHTower.Sieve
