import GaloisForLFunctions.RHTower.SuzukiCauchyReporterSecantSharpTransition

/-!
# Sharp arithmetic localization of Suzuki reporter-secant energy

The factor-two cutoff in the first arithmetic localization of Suzuki's Cauchy wall packet is not
the true sign boundary.  The exact transition atlas places the unique zero strictly between
`3p/2` and `2p` for every nonzero shallow lag `p`.

This module transports that continuous transition into the literal finite Mangoldt packet.  It
proves that every ordered arithmetic pair beyond its exact transition depth contributes
nonpositively, so the full Cauchy reporter energy is bounded above by the complementary transition
core.  The latter is strictly smaller than the earlier factor-two core: between the exact root and
`2p` there is always a nonempty interval of strictly negative interaction.

Thus the remaining cofinal prime--polar--Gamma estimate only has to control pairs before the exact
source-specific transition, rather than every pair above the multiplicative hyperbola cutoff.
-/

open Set
open scoped NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A zero-lag reporter secant is the zero vector, hence has zero cross-Gram with every lag. -/
theorem suzukiReporterSecantCauchyGram_zero_left (q : ℝ≥0) :
    suzukiReporterSecantCauchyGram 0 q = 0 := by
  simp [suzukiReporterSecantCauchyGram, cauchyHalfExponentialKernel]

/-- **Exact transition half-line.**  Once a second lag reaches the unique transition depth of a
nonzero first lag, their reporter-secant Cauchy cross-Gram is nonpositive.  This includes both the
middle band and the old factor-two region. -/
theorem suzukiReporterSecantCauchyGram_nonpos_of_transitionDepth_le
    (p : {p : ℝ≥0 // p ≠ 0}) (q : ℝ≥0)
    (hpq : p.1 ≤ q)
    (htransition : suzukiReporterSecantTransitionDepth p ≤ q) :
    suzukiReporterSecantCauchyGram p.1 q ≤ 0 := by
  by_cases htwo : 2 * p.1 ≤ q
  · let r : ℝ≥0 := q - 2 * p.1
    have hq : q = 2 * p.1 + r := by
      dsimp only [r]
      calc
        q = (q - 2 * p.1) + 2 * p.1 := (tsub_add_cancel_of_le htwo).symm
        _ = 2 * p.1 + (q - 2 * p.1) := add_comm _ _
    rw [hq]
    exact suzukiReporterSecantCauchyGram_two_mul_add_nonpos p.1 r
  · have hqTwo : q ≤ 2 * p.1 := le_of_not_ge htwo
    let r : ℝ≥0 := q - p.1
    have hq : q = p.1 + r := by
      dsimp only [r]
      calc
        q = (q - p.1) + p.1 := (tsub_add_cancel_of_le hpq).symm
        _ = p.1 + (q - p.1) := add_comm _ _
    have hrle : r ≤ p.1 := by
      dsimp only [r]
      rw [tsub_le_iff_right]
      simpa [two_mul] using hqTwo
    let P : SuzukiReporterSecantStrictMiddleBand :=
      { shallow := p.1
        residual := r
        residual_le_shallow := hrle
        shallow_ne_zero := p.2 }
    have hresidual : P.transitionResidual ≤ (P.residual : ℝ) := by
      change suzukiReporterSecantTransitionResidual p ≤ (r : ℝ)
      have ht : (suzukiReporterSecantTransitionDepth p : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast htransition
      change (p.1 : ℝ) + suzukiReporterSecantTransitionResidual p ≤ (q : ℝ) at ht
      rw [hq] at ht
      push_cast at ht
      linarith
    rw [hq]
    rcases P.gram_sign_trichotomy with hpos | hzero | hneg
    · exact False.elim (not_lt_of_ge hresidual hpos.1)
    · exact hzero.2.le
    · exact hneg.2.le

/-- Strict form of the transition half-line: past the unique transition depth the cross-Gram is
strictly negative. -/
theorem suzukiReporterSecantCauchyGram_neg_of_transitionDepth_lt
    (p : {p : ℝ≥0 // p ≠ 0}) (q : ℝ≥0)
    (htransition : suzukiReporterSecantTransitionDepth p < q) :
    suzukiReporterSecantCauchyGram p.1 q < 0 := by
  have hpdepth : p.1 < suzukiReporterSecantTransitionDepth p := by
    change (p.1 : ℝ) < (p.1 : ℝ) +
      suzukiReporterSecantTransitionResidual p
    have hr := (suzukiReporterSecantTransitionResidual_mem p).1
    have hp0 : 0 < (p.1 : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr p.2)
    linarith
  have hpq : p.1 ≤ q := (hpdepth.trans htransition).le
  by_cases htwo : 2 * p.1 ≤ q
  · let r : ℝ≥0 := q - 2 * p.1
    have hq : q = 2 * p.1 + r := by
      dsimp only [r]
      calc
        q = (q - 2 * p.1) + 2 * p.1 := (tsub_add_cancel_of_le htwo).symm
        _ = 2 * p.1 + (q - 2 * p.1) := add_comm _ _
    rw [hq]
    exact suzukiReporterSecantCauchyGram_two_mul_add_neg p r
  · have hqTwo : q ≤ 2 * p.1 := le_of_not_ge htwo
    let r : ℝ≥0 := q - p.1
    have hq : q = p.1 + r := by
      dsimp only [r]
      calc
        q = (q - p.1) + p.1 := (tsub_add_cancel_of_le hpq).symm
        _ = p.1 + (q - p.1) := add_comm _ _
    have hrle : r ≤ p.1 := by
      dsimp only [r]
      rw [tsub_le_iff_right]
      simpa [two_mul] using hqTwo
    let P : SuzukiReporterSecantStrictMiddleBand :=
      { shallow := p.1
        residual := r
        residual_le_shallow := hrle
        shallow_ne_zero := p.2 }
    have hresidual : P.transitionResidual < (P.residual : ℝ) := by
      change suzukiReporterSecantTransitionResidual p < (r : ℝ)
      have ht : (suzukiReporterSecantTransitionDepth p : ℝ) < (q : ℝ) := by
        exact_mod_cast htransition
      change (p.1 : ℝ) + suzukiReporterSecantTransitionResidual p < (q : ℝ) at ht
      rw [hq] at ht
      push_cast at ht
      linarith
    rw [hq]
    rcases P.gram_sign_trichotomy with hpos | hzero | hneg
    · exact False.elim (not_lt_of_ge hresidual.le hpos.1)
    · exfalso
      linarith [hresidual, hzero.1]
    · exact hneg.2

/-- **Strict improvement over factor two.**  For every nonzero shallow lag there is a deeper lag
strictly before `2p` whose interaction is already strictly negative. -/
theorem exists_suzukiReporterSecantCauchyGram_neg_before_factorTwo
    (p : {p : ℝ≥0 // p ≠ 0}) :
    ∃ q : ℝ≥0,
      suzukiReporterSecantTransitionDepth p < q ∧
      q < 2 * p.1 ∧
      suzukiReporterSecantCauchyGram p.1 q < 0 := by
  let q : ℝ≥0 := (suzukiReporterSecantTransitionDepth p + 2 * p.1) / 2
  have hwindow := suzukiReporterSecantTransitionDepth_mem p
  have hdepthTwo : suzukiReporterSecantTransitionDepth p < 2 * p.1 := by
    exact_mod_cast hwindow.2
  have hdepthTwoReal : (suzukiReporterSecantTransitionDepth p : ℝ) <
      2 * (p.1 : ℝ) := by
    exact_mod_cast hdepthTwo
  have hleft : suzukiReporterSecantTransitionDepth p < q := by
    change (suzukiReporterSecantTransitionDepth p : ℝ) <
      ((suzukiReporterSecantTransitionDepth p + 2 * p.1) / 2 : ℝ≥0)
    push_cast
    linarith
  have hright : q < 2 * p.1 := by
    change (((suzukiReporterSecantTransitionDepth p + 2 * p.1) / 2 : ℝ≥0) : ℝ) <
      (2 * p.1 : ℝ≥0)
    push_cast
    linarith
  exact ⟨q, hleft, hright,
    suzukiReporterSecantCauchyGram_neg_of_transitionDepth_lt p q hleft⟩

/-- Symmetric exact-transition separation predicate for two reporter lags.  Zero lags are included
because their reporter secant vanishes identically. -/
def suzukiReporterSecantTransitionSeparated (p q : ℝ≥0) : Prop :=
  p = 0 ∨ q = 0 ∨
    (∃ hp : p ≠ 0, p ≤ q ∧
      suzukiReporterSecantTransitionDepth ⟨p, hp⟩ ≤ q) ∨
    (∃ hq : q ≠ 0, q ≤ p ∧
      suzukiReporterSecantTransitionDepth ⟨q, hq⟩ ≤ p)

/-- Every transition-separated pair has favorable nonpositive interaction. -/
theorem suzukiReporterSecantCauchyGram_nonpos_of_transitionSeparated
    {p q : ℝ≥0} (h : suzukiReporterSecantTransitionSeparated p q) :
    suzukiReporterSecantCauchyGram p q ≤ 0 := by
  rcases h with hp | hq | hforward | hreverse
  · rw [hp, suzukiReporterSecantCauchyGram_zero_left]
  · rw [hq, suzukiReporterSecantCauchyGram_comm,
      suzukiReporterSecantCauchyGram_zero_left]
  · obtain ⟨hp, hpq, hdepth⟩ := hforward
    exact suzukiReporterSecantCauchyGram_nonpos_of_transitionDepth_le
      ⟨p, hp⟩ q hpq hdepth
  · obtain ⟨hq, hqp, hdepth⟩ := hreverse
    rw [suzukiReporterSecantCauchyGram_comm]
    exact suzukiReporterSecantCauchyGram_nonpos_of_transitionDepth_le
      ⟨q, hq⟩ p hqp hdepth

/-- Before the exact transition depth, every ordered nonzero reporter-secant cross-Gram is
strictly positive.  Together with the transition half-line, this closes the complete sign atlas. -/
theorem suzukiReporterSecantCauchyGram_pos_of_lt_transitionDepth
    (p : {p : ℝ≥0 // p ≠ 0}) (q : ℝ≥0)
    (hpq : p.1 ≤ q)
    (htransition : q < suzukiReporterSecantTransitionDepth p) :
    0 < suzukiReporterSecantCauchyGram p.1 q := by
  have hdepthTwo : suzukiReporterSecantTransitionDepth p < 2 * p.1 := by
    exact_mod_cast (suzukiReporterSecantTransitionDepth_mem p).2
  have hqTwo : q ≤ 2 * p.1 := (htransition.trans hdepthTwo).le
  let r : ℝ≥0 := q - p.1
  have hq : q = p.1 + r := by
    dsimp only [r]
    calc
      q = (q - p.1) + p.1 := (tsub_add_cancel_of_le hpq).symm
      _ = p.1 + (q - p.1) := add_comm _ _
  have hrle : r ≤ p.1 := by
    dsimp only [r]
    rw [tsub_le_iff_right]
    simpa [two_mul] using hqTwo
  let P : SuzukiReporterSecantSharpPositivePair :=
    { shallow := p.1
      residual := r
      residual_le_shallow := hrle
      shallow_ne_zero := p.2
      residual_lt_transitionResidual := by
        change (r : ℝ) < suzukiReporterSecantTransitionResidual p
        have ht : (q : ℝ) <
            (suzukiReporterSecantTransitionDepth p : ℝ) := by
          exact_mod_cast htransition
        change (q : ℝ) < (p.1 : ℝ) +
          suzukiReporterSecantTransitionResidual p at ht
        rw [hq] at ht
        push_cast at ht
        linarith }
  rw [hq]
  exact P.gram_pos

/-- Every pair outside the exact-transition-separated region has strictly positive raw Gram. -/
theorem suzukiReporterSecantCauchyGram_pos_of_not_transitionSeparated
    {p q : ℝ≥0} (h : ¬ suzukiReporterSecantTransitionSeparated p q) :
    0 < suzukiReporterSecantCauchyGram p q := by
  have hp : p ≠ 0 := by
    intro hp
    exact h (Or.inl hp)
  have hq : q ≠ 0 := by
    intro hq
    exact h (Or.inr (Or.inl hq))
  rcases le_total p q with hpq | hqp
  · have hnotdepth :
        ¬ suzukiReporterSecantTransitionDepth ⟨p, hp⟩ ≤ q := by
      intro hdepth
      exact h (Or.inr (Or.inr (Or.inl ⟨hp, hpq, hdepth⟩)))
    exact suzukiReporterSecantCauchyGram_pos_of_lt_transitionDepth
      ⟨p, hp⟩ q hpq (lt_of_not_ge hnotdepth)
  · have hnotdepth :
        ¬ suzukiReporterSecantTransitionDepth ⟨q, hq⟩ ≤ p := by
      intro hdepth
      exact h (Or.inr (Or.inr (Or.inr ⟨hq, hqp, hdepth⟩)))
    rw [suzukiReporterSecantCauchyGram_comm]
    exact suzukiReporterSecantCauchyGram_pos_of_lt_transitionDepth
      ⟨q, hq⟩ p hqp (lt_of_not_ge hnotdepth)

/-- **Complete exact sign classification.**  A Suzuki reporter-secant Cauchy cross-Gram is
strictly positive exactly when its lag pair lies before the symmetric exact transition. -/
theorem suzukiReporterSecantCauchyGram_pos_iff_not_transitionSeparated
    (p q : ℝ≥0) :
    0 < suzukiReporterSecantCauchyGram p q ↔
      ¬ suzukiReporterSecantTransitionSeparated p q := by
  constructor
  · intro hpos hsep
    exact (not_lt_of_ge
      (suzukiReporterSecantCauchyGram_nonpos_of_transitionSeparated hsep)) hpos
  · exact suzukiReporterSecantCauchyGram_pos_of_not_transitionSeparated

/-- Equivalent closed form of the sign atlas: transition separation is exactly nonpositivity. -/
theorem suzukiReporterSecantTransitionSeparated_iff_gram_nonpos (p q : ℝ≥0) :
    suzukiReporterSecantTransitionSeparated p q ↔
      suzukiReporterSecantCauchyGram p q ≤ 0 := by
  constructor
  · exact suzukiReporterSecantCauchyGram_nonpos_of_transitionSeparated
  · intro hgram
    by_contra hsep
    exact (not_lt_of_ge hgram)
      (suzukiReporterSecantCauchyGram_pos_of_not_transitionSeparated hsep)

/-- Exact-transition separation for one ordered pair in the literal natural-aperture packet. -/
def suzukiNaturalApertureTransitionSeparated (N : ℕ) (ij : ℕ × ℕ) : Prop :=
  suzukiReporterSecantTransitionSeparated
    (suzukiNaturalApertureLag N ij.1)
    (suzukiNaturalApertureLag N ij.2)

/-- Total Mangoldt pair energy in the favorable exact-transition-separated region. -/
noncomputable def suzukiNaturalApertureTransitionSeparatedCauchyEnergy (N : ℕ) : ℝ :=
  by
    classical
    exact ∑ ij ∈ (suzukiNaturalAperturePairSet N).filter
        (suzukiNaturalApertureTransitionSeparated N),
      suzukiNaturalApertureCauchyPairTerm N ij

/-- Sole arithmetic sector which can still contribute positive Cauchy reporter energy. -/
noncomputable def suzukiNaturalApertureTransitionCoreCauchyEnergy (N : ℕ) : ℝ :=
  by
    classical
    exact ∑ ij ∈ (suzukiNaturalAperturePairSet N).filter
        (fun ij => ¬ suzukiNaturalApertureTransitionSeparated N ij),
      suzukiNaturalApertureCauchyPairTerm N ij

/-- The exact-transition-separated portion of every finite Mangoldt packet is nonpositive. -/
theorem suzukiNaturalApertureTransitionSeparatedCauchyEnergy_nonpos (N : ℕ) :
    suzukiNaturalApertureTransitionSeparatedCauchyEnergy N ≤ 0 := by
  classical
  rw [suzukiNaturalApertureTransitionSeparatedCauchyEnergy]
  apply Finset.sum_nonpos
  intro ij hij
  rw [Finset.mem_filter] at hij
  have hwi : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.1).property
  have hwj : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.2).property
  have hgram := suzukiReporterSecantCauchyGram_nonpos_of_transitionSeparated hij.2
  dsimp [suzukiNaturalApertureCauchyPairTerm]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hwi hgram) hwj

/-- Every term in the complementary transition core is nonnegative.  Thus the exact transition is
the canonical sign boundary of the literal weighted Mangoldt pair energy, not only a useful cutoff. -/
theorem suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg (N : ℕ) :
    0 ≤ suzukiNaturalApertureTransitionCoreCauchyEnergy N := by
  classical
  rw [suzukiNaturalApertureTransitionCoreCauchyEnergy]
  apply Finset.sum_nonneg
  intro ij hij
  rw [Finset.mem_filter] at hij
  have hwi : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.1).property
  have hwj : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.2).property
  have hgram :=
    suzukiReporterSecantCauchyGram_pos_of_not_transitionSeparated hij.2
  dsimp [suzukiNaturalApertureCauchyPairTerm]
  exact mul_nonneg (mul_nonneg hwi hgram.le) hwj

/-- Exact signed decomposition of the full literal Mangoldt reporter-secant Cauchy energy. -/
theorem suzukiNaturalApertureCauchyEnergy_eq_transitionSeparated_add_core (N : ℕ) :
    suzukiNaturalApertureCauchyEnergy N =
      suzukiNaturalApertureTransitionSeparatedCauchyEnergy N +
        suzukiNaturalApertureTransitionCoreCauchyEnergy N := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (suzukiNaturalAperturePairSet N)
    (suzukiNaturalApertureTransitionSeparated N)
    (suzukiNaturalApertureCauchyPairTerm N)
  unfold suzukiNaturalApertureCauchyEnergy
    suzukiNaturalApertureTransitionSeparatedCauchyEnergy
    suzukiNaturalApertureTransitionCoreCauchyEnergy
  exact hsplit.symm

/-- **Sharp arithmetic localization.**  The full literal Mangoldt reporter-secant Cauchy energy is
bounded above by the transition core.  All removed ordered pairs have their exact favorable sign;
no absolute-value estimate or discarded positive term enters. -/
theorem suzukiNaturalApertureCauchyEnergy_le_transitionCore (N : ℕ) :
    suzukiNaturalApertureCauchyEnergy N ≤
      suzukiNaturalApertureTransitionCoreCauchyEnergy N := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (suzukiNaturalAperturePairSet N)
    (suzukiNaturalApertureTransitionSeparated N)
    (suzukiNaturalApertureCauchyPairTerm N)
  have hnegative :=
    suzukiNaturalApertureTransitionSeparatedCauchyEnergy_nonpos N
  unfold suzukiNaturalApertureTransitionSeparatedCauchyEnergy at hnegative
  unfold suzukiNaturalApertureCauchyEnergy
    suzukiNaturalApertureTransitionCoreCauchyEnergy
  rw [← hsplit]
  exact add_le_of_nonpos_left hnegative

end

end GaloisForLFunctions.RHTower
