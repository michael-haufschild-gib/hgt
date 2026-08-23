import GaloisForLFunctions.RHTower.BurnolLemmaSevenFive

/-!
# Burnol's Theorem 7.1: the two aperture indices coincide

For an arbitrary multiset `(Z, m)` of the open critical strip, Lemma 7.4 says that failure of
completeness at an aperture forces minimality there, and Lemma 7.5 says that minimality at an
aperture forces failure of completeness at every smaller aperture.  Together:

* the set of apertures at which the system is **complete** is an *up-set*;
* the set of apertures at which it is **minimal** is a *down-set*;
* the two sets cover `(0, ∞)`.

That is exactly `a₁(Z) = a₂(Z)`: the supremum of the minimality set is the infimum of the
completeness set.

## Main results

* `meromorphicOrderAt_eq_top_of_eq_zero`
* `not_isComplete_of_isMinimal_of_lt`
* `isComplete_of_lt`, `isMinimal_of_lt`
* `burnol_theorem_seven_one`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The transform of the zero vector vanishes identically on the strip, so it has infinite order. -/
theorem meromorphicOrderAt_eq_top_of_eq_zero {a : ℝ} (ha : 0 < a) {v : SoninL2} {c d : ℂ}
    (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    (hv : v = 0) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    meromorphicOrderAt (extendedMellinContinuation a c d v) ρ = ⊤ := by
  have hzero : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      extendedMellinContinuation a c d v s = 0 := by
    intro s hs1 hs2
    rw [extendedMellinContinuation_eq_soninMellinIntegral ha hev hc hd hs1 hs2,
      soninMellinIntegral]
    refine integral_eq_zero_of_ae ?_
    have hzc : ((v : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [hv]
      exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [ae_restrict_of_ae hzc] with t ht
    simp [ht]
  have hA0 : AnalyticOnNhd ℂ (extendedMellinContinuation a c d v)
      {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h] at hy; norm_num at hy
    have hy1 : y ≠ 1 := by intro h; rw [h] at hy; norm_num at hy
    exact analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hy0 hy1
  have hB0 : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) {y : ℂ | 0 < y.re ∧ y.re < 1} :=
    fun _ _ => analyticAt_const
  have hz₀ : ((3 / 4 : ℝ) : ℂ) ∈ {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    constructor <;> simp <;> norm_num
  have hzz : extendedMellinContinuation a c d v =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)] fun _ : ℂ => 0 := by
    have hopen : IsOpen {y : ℂ | 1 / 2 < y.re ∧ y.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem₀ : ((3 / 4 : ℝ) : ℂ) ∈ {y : ℂ | 1 / 2 < y.re ∧ y.re < 1} := by
      constructor <;> simp <;> norm_num
    filter_upwards [hopen.mem_nhds hmem₀] with y hy
    exact hzero y hy.1 hy.2
  have hnb : extendedMellinContinuation a c d v =ᶠ[𝓝 ρ] fun _ : ℂ => 0 := by
    have hallzero : ∀ y : ℂ, 0 < y.re → y.re < 1 →
        extendedMellinContinuation a c d v y = 0 := fun y hy0 hy1 =>
      hA0.eqOn_of_preconnected_of_eventuallyEq hB0 isPreconnected_criticalStrip hz₀ hzz ⟨hy0, hy1⟩
    filter_upwards [isOpen_criticalOpenStrip.mem_nhds
      (⟨hρ0, hρ1⟩ : ρ ∈ {u : ℂ | 0 < u.re ∧ u.re < 1})] with y hy
    exact hallzero y hy.1 hy.2
  have hana : AnalyticAt ℂ (extendedMellinContinuation a c d v) ρ := hA0 ρ ⟨hρ0, hρ1⟩
  rw [hana.meromorphicOrderAt_eq, analyticOrderAt_eq_top.2 (by
    filter_upwards [hnb] with y hy; exact hy)]
  rfl

/-- **Lemma 7.5 from the minimality predicate.** -/
theorem not_isComplete_of_isMinimal_of_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {Z : Set ℂ} {m : ℂ → ℕ} (hZ : ∀ w ∈ Z, 0 < w.re ∧ w.re < 1)
    {ρ : ℂ} (hρZ : ρ ∈ Z) (hmρ : 1 ≤ m ρ)
    (hmin : IsMinimalEvaluatorSystem a Z m) : ¬ IsCompleteEvaluatorSystem b Z m := by
  obtain ⟨hρ0, hρ1⟩ := hZ ρ hρZ
  obtain ⟨v, c, d, hev, hmem, hc, hd, hother, hself⟩ := hmin ρ hρZ (m ρ - 1) (by omega)
  have hv : v ≠ 0 := by
    intro h0
    have := meromorphicOrderAt_eq_top_of_eq_zero ha hev hc hd h0 hρ0 hρ1
    rw [this] at hself
    exact absurd hself.symm WithTop.coe_ne_top
  have hselfle : (((m ρ : ℤ) - 1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) ρ := by
    rw [hself]
    have hcast : (((m ρ - 1 : ℕ) : ℤ)) = ((m ρ : ℤ) - 1) := by
      have : (1 : ℕ) ≤ m ρ := hmρ
      omega
    rw [hcast]
  have hotherle : ∀ w ∈ Z, w ≠ ρ →
      ((m w : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) w :=
    hother
  exact not_isCompleteEvaluatorSystem_of_lt ha hb hab hZ hρ0 hρ1 hev hmem hc hd hv
    hotherle hselfle hρZ

/-- **Completeness is upward closed in the aperture.** -/
theorem isComplete_of_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {Z : Set ℂ} {m : ℂ → ℕ} (hZ : ∀ w ∈ Z, 0 < w.re ∧ w.re < 1)
    {ρ : ℂ} (hρZ : ρ ∈ Z) (hmρ : 1 ≤ m ρ)
    (hcompb : IsCompleteEvaluatorSystem b Z m) : IsCompleteEvaluatorSystem a Z m := by
  by_contra hnc
  exact not_isComplete_of_isMinimal_of_lt ha hb hab hZ hρZ hmρ
    (isMinimal_of_not_isComplete ha hZ hnc) hcompb

/-- **Minimality is downward closed in the aperture.** -/
theorem isMinimal_of_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {Z : Set ℂ} {m : ℂ → ℕ} (hZ : ∀ w ∈ Z, 0 < w.re ∧ w.re < 1)
    {ρ : ℂ} (hρZ : ρ ∈ Z) (hmρ : 1 ≤ m ρ)
    (hmin : IsMinimalEvaluatorSystem a Z m) : IsMinimalEvaluatorSystem b Z m :=
  isMinimal_of_not_isComplete hb hZ
    (not_isComplete_of_isMinimal_of_lt ha hb hab hZ hρZ hmρ hmin)

/-- **Burnol's Theorem 7.1.**  For every nonempty multiset of the open critical strip the aperture
set on which the evaluator system is complete is an up-set, the aperture set on which it is minimal
is a down-set, and the two cover every positive aperture.  Equivalently `a₁(Z) = a₂(Z)`. -/
theorem burnol_theorem_seven_one {Z : Set ℂ} {m : ℂ → ℕ}
    (hZ : ∀ w ∈ Z, 0 < w.re ∧ w.re < 1) {ρ : ℂ} (hρZ : ρ ∈ Z) (hmρ : 1 ≤ m ρ) :
    (∀ a : ℝ, 0 < a → ¬ IsCompleteEvaluatorSystem a Z m → IsMinimalEvaluatorSystem a Z m) ∧
    (∀ a b : ℝ, 0 < a → 0 < b → b < a → IsCompleteEvaluatorSystem b Z m →
      IsCompleteEvaluatorSystem a Z m) ∧
    (∀ a b : ℝ, 0 < a → 0 < b → b < a → IsMinimalEvaluatorSystem a Z m →
      IsMinimalEvaluatorSystem b Z m) :=
  ⟨fun a ha hnc => isMinimal_of_not_isComplete ha hZ hnc,
   fun a b ha hb hab hcb => isComplete_of_lt ha hb hab hZ hρZ hmρ hcb,
   fun a b ha hb hab hmin => isMinimal_of_lt ha hb hab hZ hρZ hmρ hmin⟩

end

end RHTower
