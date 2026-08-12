import GaloisForLFunctions.RHTower.Sieve.MaynardDefectExcision
import GaloisForLFunctions.RHTower.Sieve.MaynardMobiusAllShort
import GaloisForLFunctions.RHTower.Sieve.MaynardCanonicalFactorDichotomy

/-!
# Canonical defect excision for literal Heath--Brown boxes

The all-short reduction does not require every box factor to be short.  Long zeta/logarithm
factors that remain below their own multiplicative thresholds cancel exactly from a large core.
If at least one unit of greedy mass remains on short factors, that retained product supplies the
same robust Huxley group as an entirely short box.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

abbrev heathBrownBoxFactorValue
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k) (s : ℂ) :
    HeathBrownBoxFactorIndex k c.m → ℂ :=
  fun i => LSeries (complexCoeff (arithmeticDyadicBlock
    (heathBrownFactorBase L X (heathBrownBoxFactorKind k c.m i))
    (heathBrownBoxFactorExponent c.a c.b c.q i))) s

/-- A literal core stays in the robust all-short branch even when it contains long atoms, provided
those atoms are individually sub-threshold and the short atoms contain mass at least `t`. -/
theorem exists_heathBrown_box_robust_group_after_zeta_log_excision
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    {T0 t e : ℝ} (hT0 : 1 < T0) (ht : 0 < t) (s : ℂ)
    (hcore :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤
          ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q s‖)
    (hmobius : ∀ i : HeathBrownBoxFactorIndex k c.m,
      heathBrownBoxFactorKind k c.m i = .moebius →
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t)
    (hlongUpper : ∀ i : HeathBrownBoxFactorIndex k c.m,
      (heathBrownBoxFactorKind k c.m i = .zeta ∨
        heathBrownBoxFactorKind k c.m i = .log) →
      2 * t < dyadicLogExponent T0
        (heathBrownBoxFactorExponent c.a c.b c.q i) →
      ‖heathBrownBoxFactorValue L X k c s i‖ ≤
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ^ e)
    (htotalShort : t ≤ ∑ i ∈ shortDyadicFactorSet T0 t
      (heathBrownBoxFactorExponent c.a c.b c.q),
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent c.a c.b c.q i)) :
    ∃ u : Finset (HeathBrownBoxFactorIndex k c.m),
      u.Nonempty ∧
      u ⊆ shortDyadicFactorSet T0 t
        (heathBrownBoxFactorExponent c.a c.b c.q) ∧
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
          ‖∏ i : {i // i ∈ u}, heathBrownBoxFactorValue L X k c s i‖ := by
  apply exists_dyadic_robust_greedy_large_group_after_excision
    (heathBrownBoxFactorExponent c.a c.b c.q)
    (heathBrownBoxFactorValue L X k c s) hT0 ht
  · rw [heathBrownBoxFactorProduct_eq_core]
    exact hcore
  · intro i hilong
    apply hlongUpper i
    · exact heathBrown_factorKind_eq_zeta_or_log_of_long c hmobius i hilong
    · exact hilong
  · exact htotalShort

/-- Aggregate selector with the false global all-short premise replaced by the two exact local
conditions needed after excision: long zeta/logarithm atoms are sub-threshold, and retained short
mass is at least `t`. -/
theorem exists_heathBrown_eligible_robust_group_after_zeta_log_excision_of_large
    (L X k : ℕ) (hk : 0 < k) {T0 t e V : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t) (hV : 0 < V) (s : ℂ)
    (haggregate : V ≤ ‖heathBrownEligibleDyadicAggregate L X k T0 t s‖)
    (hmobius : ∀ c : HeathBrownBoxChoice L X k,
      ∀ i : HeathBrownBoxFactorIndex k c.m,
        heathBrownBoxFactorKind k c.m i = .moebius →
          dyadicLogExponent T0
            (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t)
    (hlongUpper : ∀ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c →
      ∀ i : HeathBrownBoxFactorIndex k c.m,
        (heathBrownBoxFactorKind k c.m i = .zeta ∨
          heathBrownBoxFactorKind k c.m i = .log) →
        2 * t < dyadicLogExponent T0
          (heathBrownBoxFactorExponent c.a c.b c.q i) →
        ‖heathBrownBoxFactorValue L X k c s i‖ ≤
          (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ^ e)
    (hshortMass : ∀ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c →
      t ≤ ∑ i ∈ shortDyadicFactorSet T0 t
        (heathBrownBoxFactorExponent c.a c.b c.q),
          dyadicLogExponent T0
            (heathBrownBoxFactorExponent c.a c.b c.q i))
    (hreserve : ∀ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c →
        heathBrownEligibleBoxCost L X k *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ e ≤ V) :
    ∃ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c ∧
      ∃ u : Finset (HeathBrownBoxFactorIndex k c.m),
        u.Nonempty ∧
        u ⊆ shortDyadicFactorSet T0 t
          (heathBrownBoxFactorExponent c.a c.b c.q) ∧
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
            ‖∏ i : {i // i ∈ u}, heathBrownBoxFactorValue L X k c s i‖ := by
  obtain ⟨c, helig, hcore, _⟩ :=
    exists_heathBrown_eligible_long_zeta_log_or_robust_group_of_large
      L X k hk hT0 ht hV s haggregate hmobius hreserve
  refine ⟨c, helig, ?_⟩
  exact exists_heathBrown_box_robust_group_after_zeta_log_excision
    L X k c hT0 ht s hcore (hmobius c) (hlongUpper c helig)
      (hshortMass c helig)

end RHTower.Sieve
