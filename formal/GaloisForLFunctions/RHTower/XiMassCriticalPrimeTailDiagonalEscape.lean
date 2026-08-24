import GaloisForLFunctions.RHTower.XiMassCriticalPrimeTailFiniteExtinction

/-!
# Diagonal escape of every moving finite prime-tail approximation

Every fixed finite critical prime-tail current becomes extinct, while a surviving reflection
self-intersection charge makes the complete current unbounded after subtraction of any fixed finite
packet. This file closes the quantifier gap between those facts.

If RH fails, no moving finite-stage approximation scheme can outrun the obstruction: for every
sequence of finite prime-power packets, one can choose a diagonal sequence of future-time samples
along which the full-minus-finite error tends to infinity. Conversely, RH supplies a globally
bounded empty-packet remainder and therefore forbids this universal diagonal escape. Thus the
failure of RH is exactly failure of every finite-stage completion scheme under adversarial
source-time diagonalization.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Every moving finite prime-power approximation admits a diagonal sample along which its error
escapes every finite bound. -/
def XiMassCriticalPrimeTailFiniteStageDiagonalEscape
    (a sigma : ℝ) : Prop :=
  ∀ S : ℕ → Finset DeningerPrimePowerIndex,
    ∃ u : ℕ → ℝ,
      (∀ n, 0 ≤ u n) ∧
      Tendsto
        (fun n => ‖xiMassCriticalPrimeTailGreenCurrent a sigma (u n) -
          xiMassCriticalPrimeTailGreenCurrentFinite a sigma (u n) (S n)‖)
        atTop atTop

/-- Failure of RH is exactly unavoidable diagonal escape against every moving finite source
truncation. -/
theorem not_riemannHypothesis_iff_xiMassCriticalPrimeTailFiniteStageDiagonalEscape
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    ¬ RiemannHypothesis ↔
      XiMassCriticalPrimeTailFiniteStageDiagonalEscape a sigma := by
  constructor
  · intro hnot S
    have hwitness : ∀ n : ℕ, ∃ u : ℝ, 0 ≤ u ∧ (n : ℝ) <
        ‖xiMassCriticalPrimeTailGreenCurrent a sigma u -
          xiMassCriticalPrimeTailGreenCurrentFinite a sigma u (S n)‖ := by
      intro n
      exact xiMassCriticalPrimeTailGreenRemainder_unbounded_of_not_riemannHypothesis
        ha hsigma hnot (S n) n
    choose u hu_nonneg hu_escape using hwitness
    refine ⟨u, hu_nonneg, ?_⟩
    apply Filter.tendsto_atTop.2
    intro C
    have hnat : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
      (Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop) C
    filter_upwards [hnat] with n hn
    exact hn.trans (hu_escape n).le
  · intro hescape hRH
    obtain ⟨C, hC⟩ :=
      (riemannHypothesis_iff_xiMassCriticalPrimeTailGreenCurrentLineBound
        ha hsigma).mp hRH
    obtain ⟨u, hu_nonneg, hu_escape⟩ :=
      hescape (fun _ => ∅)
    have heventually : ∀ᶠ n in atTop, C + 1 ≤
        ‖xiMassCriticalPrimeTailGreenCurrent a sigma (u n) -
          xiMassCriticalPrimeTailGreenCurrentFinite a sigma (u n) ∅‖ :=
      (Filter.tendsto_atTop.1 hu_escape) (C + 1)
    obtain ⟨n, hn⟩ := heventually.exists
    have hbound := hC (u n) (hu_nonneg n)
    simp [xiMassCriticalPrimeTailGreenCurrentFinite] at hn
    linarith

/-- One nonzero reflection self-intersection charge forces diagonal escape against every moving
finite prime-power approximation. -/
theorem xiMassCriticalPrimeTailFiniteStageDiagonalEscape_of_reflectionCharge_ne_zero
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    {T : ℝ} (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0) :
    XiMassCriticalPrimeTailFiniteStageDiagonalEscape a sigma := by
  rw [← not_riemannHypothesis_iff_xiMassCriticalPrimeTailFiniteStageDiagonalEscape
    ha hsigma]
  intro hRH
  exact hcharge
    (xiReflectionSelfIntersectionCharge_eq_zero_of_riemannHypothesis hRH T)

/-- The arithmetic diagonal-escape obstruction is exactly existence of a nonzero reflection
self-intersection charge. -/
theorem xiMassCriticalPrimeTailFiniteStageDiagonalEscape_iff_exists_reflectionCharge_ne_zero
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    XiMassCriticalPrimeTailFiniteStageDiagonalEscape a sigma ↔
      ∃ T : ℝ, xiReflectionSelfIntersectionCharge T ≠ 0 := by
  rw [← not_riemannHypothesis_iff_xiMassCriticalPrimeTailFiniteStageDiagonalEscape
    ha hsigma]
  constructor
  · intro hnot
    by_contra h
    push Not at h
    exact hnot
      (riemannHypothesis_iff_forall_reflectionSelfIntersectionCharge_eq_zero.mpr h)
  · rintro ⟨T, hT⟩ hRH
    exact hT
      (xiReflectionSelfIntersectionCharge_eq_zero_of_riemannHypothesis hRH T)

end

end RHTower
