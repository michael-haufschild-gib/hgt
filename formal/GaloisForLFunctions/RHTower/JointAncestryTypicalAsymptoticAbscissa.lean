import GaloisForLFunctions.RHTower.JointAncestryTypicalCapReceiver
import GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers

/-!
# Typical JAS positivity produces the asymptotic abscissa law

`JasTypicalPositiveAt σ` says that at level `σ`, for every resolution `N ≥ 3` and tolerance
`ε > 0`, every finite set of large primes has at most `ε N^{|P|}` phase vectors `k : P → ℤ/N`
with negative aggregate `Re jasPhaseAggregate σ 1 N P k`.

* **AAL producer** (`asymptoticAbscissaLaw_of_jasTypicalPositive`).  Typical positivity at every
  level `σ ∈ (½, 1)` gives the asymptotic abscissa law.  If only finitely many zeros lie right of
  `½ + h` and one does, their maximal real part `β₀` is the global maximum and is attained by
  finitely many copies.  At `σ = (½ + β₀)/2` this contradicts
  `exists_card_jasPhaseAggregate_re_neg_gt_of_finite_top`.
* **Closure** (`riemannHypothesis_of_zerosApproachLine_of_jasTypicalPositive`).  With the zeros
  approaching the line this gives RH
  (`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`).

So the typical JAS receiver is an attainment receiver: its only escape is a non-attained supremum
of the real parts, which the large-height statement "zeros approach the line" removes.
-/

open Complex Set

namespace RHTower

noncomputable section

open BacklundConverse

/-- **Typical JAS positivity at level `σ`.**  For every resolution `N ≥ 3` and tolerance
`ε > 0`, on every finite set of large primes at most an `ε`-fraction of the phase vectors have
negative aggregate. -/
def JasTypicalPositiveAt (σ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ P : Finset Nat.Primes,
    (∀ p ∈ P, X < (p : ℕ)) →
      ((Finset.univ.filter fun k : ↥P → Fin N =>
        (jasPhaseAggregate σ 1 N P k).re < 0).card : ℝ) ≤ ε * (N : ℝ) ^ P.card

/-- **Typical positivity below a finitely attained top is impossible.** -/
theorem false_of_finite_top_of_jasTypicalPositiveAt {β₀ σ : ℝ}
    (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀)
    (hfin : {q : XiZeroCopy | (q.1 : ℂ).re = β₀}.Finite)
    (hne : ∃ q : XiZeroCopy, (q.1 : ℂ).re = β₀) (hσ : 1 / 2 < σ) (hσβ : σ < β₀)
    (hpos : JasTypicalPositiveAt σ) : False := by
  obtain ⟨N, hN, ε, hε, h⟩ :=
    exists_card_jasPhaseAggregate_re_neg_gt_of_finite_top hmax hfin hne hσ hσβ
  obtain ⟨X, hX⟩ := hpos N hN ε hε
  obtain ⟨P, hP, hlt⟩ := h X
  exact absurd (hX P hP) (not_le.mpr hlt)

/-- **Typical JAS positivity at every level in `(½, 1)` gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_jasTypicalPositive
    (hpos : ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → JasTypicalPositiveAt σ) : AsymptoticAbscissaLaw := by
  intro h hh hF q₀
  by_contra hlt
  push Not at hlt
  obtain ⟨q₁, hq₁S, hmaxS⟩ := hF.exists_maximalFor (fun q : XiZeroCopy => (q.1 : ℂ).re)
    {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re} ⟨q₀, hlt⟩
  have hq₁ : 1 / 2 + h < (q₁.1 : ℂ).re := hq₁S
  set β₀ := (q₁.1 : ℂ).re with hβ₀
  have hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀ := by
    intro q
    by_cases hq : 1 / 2 + h < (q.1 : ℂ).re
    · by_contra hgt
      push Not at hgt
      exact absurd (hmaxS hq hgt.le) (not_le.mpr hgt)
    · push Not at hq
      linarith
  have hfin : {q : XiZeroCopy | (q.1 : ℂ).re = β₀}.Finite :=
    hF.subset fun q hq => by
      simp only [mem_setOf_eq] at hq ⊢
      rw [hq]
      exact hq₁
  have hβ1 : β₀ < 1 := xiZeroCopy_re_lt_one q₁
  exact false_of_finite_top_of_jasTypicalPositiveAt hmax hfin ⟨q₁, rfl⟩
    (σ := (1 / 2 + β₀) / 2) (by linarith) (by linarith)
    (hpos _ (by linarith) (by linarith))

/-- **Zeros approaching the line and typical JAS positivity give RH.** -/
theorem riemannHypothesis_of_zerosApproachLine_of_jasTypicalPositive (hZ : ZerosApproachLine)
    (hpos : ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → JasTypicalPositiveAt σ) : RiemannHypothesis :=
  riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
    ⟨hZ, asymptoticAbscissaLaw_of_jasTypicalPositive hpos⟩

end

end RHTower
