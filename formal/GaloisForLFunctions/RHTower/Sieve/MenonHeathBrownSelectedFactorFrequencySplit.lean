import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownMediumMobiusPolynomialFrequency
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIFrequencySplit

/-!
# Exhaustive pointwise bound for one selected Heath--Brown factor

On a positive dyadic frequency band, a selected zeta/logarithm factor is either above height or
lies in the fixed order-twenty-six derivative range.  A selected Möbius factor instead uses the
uniform polynomial-frequency logarithmic saving.  The maximum below records all three branches
without choosing a favourable case.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- Common pointwise envelope for the Möbius, over-height, and derivative branches. -/
def menonHeathBrownSelectedFactorUpper
    (X : ℕ) (N sigma T : ℝ) (kind : HeathBrownFactorKind) (q : ℕ) : ℝ :=
  max
    (N ^ (1 - sigma) * (Real.log N) ^ (-400 : ℝ))
    (max
      (2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X / T *
        N ^ (1 - sigma))
      (heathBrownDerivativeConstant X kind q * N ^ (1 - sigma) *
        N ^ (-maynardDerivativeDeficit 26)))

/-- Every sufficiently late selected factor is controlled by the common envelope throughout its
complete positive dyadic frequency band.  No zeta/log branch is omitted. -/
theorem eventually_norm_heathBrownBoxFactorValue_le_selectedFactorUpper
    : ∀ᶠ q : ℕ in atTop,
      ∀ (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
        (i : HeathBrownBoxFactorIndex k box.m) (sigma T tau : ℝ),
      1 ≤ X → 1 ≤ sigma → 0 < T → T ≤ tau → tau ≤ 2 * T →
      heathBrownBoxFactorExponent box.a box.b box.q i = q →
      (heathBrownBoxFactorKind k box.m i = .moebius → 2 ^ q ≤ L) →
      |tau| ≤ (((2 ^ q : ℕ) : ℝ)) ^ (24 : ℕ) →
      ‖heathBrownBoxFactorValue L X k box
          ((sigma : ℂ) + (tau : ℝ) * Complex.I) i‖ ≤
        menonHeathBrownSelectedFactorUpper X (((2 ^ q : ℕ) : ℝ)) sigma T
          (heathBrownBoxFactorKind k box.m i) q := by
  filter_upwards [
    eventually_norm_heathBrownBoxFactorValue_moebius_le_rpow_mul_log_rpow_neg_pow_twentyFour
      (400 : ℝ),
    eventually_menonHeathBrown_derivativeOrderTwentySix_ready] with q hmoebius hready
  intro L X k box i sigma T tau hX hsigma hT hTtau htauT hexponent hcut hfrequency
  subst q
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))
  let kind : HeathBrownFactorKind := heathBrownBoxFactorKind k box.m i
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.one_le_two_pow
  have htau : 0 < tau := hT.trans_le hTtau
  cases hkind : kind with
  | moebius =>
      have hfactor := hmoebius L X k box i sigma tau hsigma (by
        simpa only [kind] using hkind) rfl (hcut (by
          simpa only [kind] using hkind)) hfrequency
      exact hfactor.trans (by
        rw [menonHeathBrownSelectedFactorUpper]
        exact le_max_left _ _)
  | zeta =>
      have hkind' : heathBrownBoxFactorKind k box.m i = .zeta := by
        simpa only [kind] using hkind
      by_cases hover : T ≤ N
      · have hfactor := norm_heathBrownBoxFactorValue_zeta_le_over_height
          box i hkind' hX hT (zero_le_one.trans hsigma) hTtau htauT (by
            simpa only [N] using hover)
        have hover' :
            (6 * Real.pi + 1) / T * N ^ (1 - sigma) ≤
              2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X / T *
                N ^ (1 - sigma) := by
          have henv : 1 ≤ 2 * maynardLongPolylogEnvelope X := by
            have := one_le_maynardLongPolylogEnvelope X
            linarith
          have hbase : 0 ≤ (6 * Real.pi + 1) / T * N ^ (1 - sigma) := by positivity
          calc
            (6 * Real.pi + 1) / T * N ^ (1 - sigma) ≤
                (2 * maynardLongPolylogEnvelope X) *
                  ((6 * Real.pi + 1) / T * N ^ (1 - sigma)) :=
              le_mul_of_one_le_left hbase henv
            _ = 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X / T *
                N ^ (1 - sigma) := by ring
        refine hfactor.trans ?_
        simpa only [N] using hover'.trans (by
          rw [menonHeathBrownSelectedFactorUpper]
          exact le_max_of_le_right (le_max_left _ _))
      · have hrange := derivativeOrderTwentySix_range_of_not_overHeight
          hN (by simpa only [N] using hready.2) hover hTtau htau
          (by simpa only [N] using hfrequency)
        have hfactor := norm_heathBrownBoxFactorValue_le_derivative_defect
          L X k box i (Or.inl hkind') hX (zero_le_one.trans hsigma) hrange.1
          (k₀ := 26) (by norm_num)
          (box.factorExponent_le_log_X_of_zeta_or_log i (Or.inl hkind')) hready.1
          (by simpa only [N] using hrange.2.1) (by simpa only [N] using hrange.2.2)
        refine hfactor.trans ?_
        simpa only [N] using (by
          rw [menonHeathBrownSelectedFactorUpper]
          exact le_max_of_le_right (le_max_right _ _) :
            heathBrownDerivativeConstant X
                (heathBrownBoxFactorKind k box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i) *
              N ^ (1 - sigma) * N ^ (-maynardDerivativeDeficit 26) ≤
            menonHeathBrownSelectedFactorUpper X N sigma T
              (heathBrownBoxFactorKind k box.m i)
              (heathBrownBoxFactorExponent box.a box.b box.q i))
  | log =>
      have hkind' : heathBrownBoxFactorKind k box.m i = .log := by
        simpa only [kind] using hkind
      by_cases hover : T ≤ N
      · have hfactor := norm_heathBrownBoxFactorValue_log_le_over_height
          box i hkind' hX hT (zero_le_one.trans hsigma) hTtau htauT (by
            simpa only [N] using hover)
        refine hfactor.trans ?_
        simpa only [N] using (by
          rw [menonHeathBrownSelectedFactorUpper]
          exact le_max_of_le_right (le_max_left _ _) :
            2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X / T *
                N ^ (1 - sigma) ≤
              menonHeathBrownSelectedFactorUpper X N sigma T
                (heathBrownBoxFactorKind k box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i))
      · have hrange := derivativeOrderTwentySix_range_of_not_overHeight
          hN (by simpa only [N] using hready.2) hover hTtau htau
          (by simpa only [N] using hfrequency)
        have hfactor := norm_heathBrownBoxFactorValue_le_derivative_defect
          L X k box i (Or.inr hkind') hX (zero_le_one.trans hsigma) hrange.1
          (k₀ := 26) (by norm_num)
          (box.factorExponent_le_log_X_of_zeta_or_log i (Or.inr hkind')) hready.1
          (by simpa only [N] using hrange.2.1) (by simpa only [N] using hrange.2.2)
        refine hfactor.trans ?_
        simpa only [N] using (by
          rw [menonHeathBrownSelectedFactorUpper]
          exact le_max_of_le_right (le_max_right _ _) :
            heathBrownDerivativeConstant X
                (heathBrownBoxFactorKind k box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i) *
              N ^ (1 - sigma) * N ^ (-maynardDerivativeDeficit 26) ≤
            menonHeathBrownSelectedFactorUpper X N sigma T
              (heathBrownBoxFactorKind k box.m i)
              (heathBrownBoxFactorExponent box.a box.b box.q i))

end

end RHTower.Sieve
