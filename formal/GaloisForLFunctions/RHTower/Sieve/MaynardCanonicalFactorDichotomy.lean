import GaloisForLFunctions.RHTower.Sieve.MaynardMobiusAllShort
import GaloisForLFunctions.RHTower.Sieve.MaynardEligibleGreedySelection

/-!
# Canonical long-factor versus raised-Huxley dichotomy

Once the canonical degree-`60` Möbius cutoff is used, a large eligible Heath--Brown box has only
two possibilities: every factor is short and robust greedy grouping produces a literal raised-
Huxley candidate, or one long factor is literally zeta/logarithm and belongs to the derivative-test
branch.  There is no third long-Möbius case.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- A literal box contains a factor above all-short admission, and its kind is zeta or logarithm. -/
def HasLongZetaOrLogFactor
    (L X k : ℕ) {T0 t : ℝ} (c : HeathBrownBoxChoice L X k) : Prop :=
  ∃ i : HeathBrownBoxFactorIndex k c.m,
    2 * t < dyadicLogExponent T0
      (heathBrownBoxFactorExponent c.a c.b c.q i) ∧
      (heathBrownBoxFactorKind k c.m i = .zeta ∨
        heathBrownBoxFactorKind k c.m i = .log)

/-- **Exact canonical factor dichotomy.**  A large eligible aggregate selects one eligible core.
If all its factors are short, robust grouping gives the literal Huxley subproduct.  Otherwise its
long factor is zeta/logarithm because the supplied cutoff certificate excludes long Möbius atoms. -/
theorem exists_heathBrown_eligible_long_zeta_log_or_robust_group_of_large
    (L X k : ℕ) (hk : 0 < k) {T0 t e V : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t) (hV : 0 < V) (s : ℂ)
    (haggregate : V ≤ ‖heathBrownEligibleDyadicAggregate L X k T0 t s‖)
    (hmobius : ∀ c : HeathBrownBoxChoice L X k,
      ∀ i : HeathBrownBoxFactorIndex k c.m,
        heathBrownBoxFactorKind k c.m i = .moebius →
          dyadicLogExponent T0
            (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t)
    (hreserve : ∀ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c →
        heathBrownEligibleBoxCost L X k *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤ V) :
    ∃ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c ∧
        (groupedDyadicLower
          (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤
            ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q s‖ ∧
        (HasLongZetaOrLogFactor L X k (T0 := T0) (t := t) c ∨
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
                    (heathBrownBoxFactorExponent c.a c.b c.q i))) s‖) := by
  classical
  obtain ⟨c, helig, hterm⟩ :=
    exists_large_eligible_heathBrownBox L X k hk T0 t s hV haggregate
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
  have hcost := heathBrownEligibleBoxCost_pos L X k hk
  have hcore :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤
          ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q s‖ :=
    (mul_le_mul_iff_right₀ hcost).mp hscaled
  refine ⟨c, helig, hcore, ?_⟩
  by_cases hshort : ∀ i : HeathBrownBoxFactorIndex k c.m,
      dyadicLogExponent T0
        (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t
  · right
    have htotal : t ≤ ∑ i : HeathBrownBoxFactorIndex k c.m,
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent c.a c.b c.q i) := by
      simpa [IsHeathBrownBoxEligible, heathBrownBoxTotalExponent] using helig
    exact exists_heathBrown_box_dyadic_robust_group
      L X k c.m c.a c.b c.q hT0 ht hshort htotal s hcore
  · left
    push Not at hshort
    obtain ⟨i, hilong⟩ := hshort
    exact ⟨i, hilong,
      heathBrown_factorKind_eq_zeta_or_log_of_long c (hmobius c) i hilong⟩

/-- Degree-`60` specialization with the canonical cutoff chosen internally.  The returned cutoff
already satisfies the exact finite Heath--Brown identity range. -/
theorem exists_canonical_sixty_long_zeta_log_or_robust_group_of_large
    {T0 t e V : ℝ} (hT0 : 1 < T0) (ht : 0 < t) {X : ℕ}
    (hX : (X : ℝ) ≤ T0 ^ (120 * t)) (hV : 0 < V) (s : ℂ)
    (haggregate : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      V ≤ ‖heathBrownEligibleDyadicAggregate L X 60 T0 t s‖)
    (hreserve : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      ∀ c : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T0 t c →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤ V) :
    ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧
      ∃ c : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T0 t c ∧
          (groupedDyadicLower
            (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤
              ‖heathBrownDyadicCoreProduct L X 60 c.m c.a c.b c.q s‖ ∧
          (HasLongZetaOrLogFactor L X 60 (T0 := T0) (t := t) c ∨
            ∃ u : Finset (HeathBrownBoxFactorIndex 60 c.m), u.Nonempty ∧
              let alpha := ∑ i ∈ u,
                dyadicLogExponent T0
                  (heathBrownBoxFactorExponent c.a c.b c.q i)
              t ≤ alpha ∧ alpha < 4 * t ∧
                u.card ≤ Fintype.card (HeathBrownBoxFactorIndex 60 c.m) ∧
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
                        (heathBrownBoxFactorKind 60 c.m i))
                      (heathBrownBoxFactorExponent c.a c.b c.q i))) s‖) := by
  obtain ⟨L, hL, hXL, hmobius⟩ :=
    exists_sixty_cutoff_all_moebius_factors_short hT0 ht.le hX
  refine ⟨L, hL, hXL, ?_⟩
  exact exists_heathBrown_eligible_long_zeta_log_or_robust_group_of_large
    L X 60 (by norm_num) hT0 ht hV s (haggregate L hL hXL) hmobius
      (hreserve L hL hXL)

end RHTower.Sieve
