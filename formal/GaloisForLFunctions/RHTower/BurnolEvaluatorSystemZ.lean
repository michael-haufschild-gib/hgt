import GaloisForLFunctions.RHTower.ExtendedSoninOrderDrop
import GaloisForLFunctions.RHTower.SoninMellinInjective

/-!
# Evaluator systems attached to an arbitrary multiset of the critical strip

Burnol's §7 studies, for an arbitrary multiset `Z` of points of the open critical strip, the system
of evaluators `f ↦ M(f)^{(k)}(w)`, `w ∈ Z`, `k < m(w)`, inside `L_a`.  In the jet dictionary the
corpus uses throughout, "`f` is orthogonal to every evaluator of the system" is "the continued
Mellin transform of `f` vanishes to order at least `m(w)` at every `w ∈ Z`", and "`f` is not
orthogonal to the `k`-th evaluator at `ρ`" is "the transform has order exactly `k` at `ρ`".

With that dictionary `IsCompleteEvaluatorSystem` and `IsMinimalEvaluatorSystem` below are literally
Burnol's notions, and Lemma 7.4 — *not complete implies minimal* — is a consequence of the order
drop of `ExtendedSoninOrderDrop`.

## Main results

* `meromorphicOrderAt_extendedMellin_ne_top`
* `IsCompleteEvaluatorSystem`, `IsMinimalEvaluatorSystem`
* `isMinimal_of_not_isComplete` — **Burnol's Lemma 7.4**
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The continued Mellin transform of a nonzero vector of `L_a` has finite order at every point of
the open critical strip. -/
theorem meromorphicOrderAt_extendedMellin_ne_top {a : ℝ} (ha : 0 < a) {v : SoninL2} {c d : ℂ}
    (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    (hv : v ≠ 0) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    meromorphicOrderAt (extendedMellinContinuation a c d v) z ≠ ⊤ := by
  intro htop
  have hz0' : z ≠ 0 := by intro h; rw [h] at hz0; norm_num at hz0
  have hz1' : z ≠ 1 := by intro h; rw [h] at hz1; norm_num at hz1
  have hana : AnalyticAt ℂ (extendedMellinContinuation a c d v) z :=
    analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hz0' hz1'
  have hordtop : analyticOrderAt (extendedMellinContinuation a c d v) z = ⊤ := by
    rw [hana.meromorphicOrderAt_eq] at htop
    induction hx : analyticOrderAt (extendedMellinContinuation a c d v) z with
    | top => rfl
    | coe n =>
        rw [hx] at htop
        simp at htop
  have hzero : extendedMellinContinuation a c d v =ᶠ[𝓝 z] 0 := by
    have h := analyticOrderAt_eq_top.1 hordtop
    filter_upwards [h] with y hy
    exact hy
  have hA1 : AnalyticOnNhd ℂ (extendedMellinContinuation a c d v)
      {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h] at hy; norm_num at hy
    have hy1 : y ≠ 1 := by intro h; rw [h] at hy; norm_num at hy
    exact analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hy0 hy1
  have hA2 : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) {y : ℂ | 0 < y.re ∧ y.re < 1} :=
    fun _ _ => analyticAt_const
  have hall : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      extendedMellinContinuation a c d v s = 0 := by
    intro s hs1 hs2
    exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 isPreconnected_criticalStrip
      ⟨hz0, hz1⟩ hzero ⟨by linarith, hs2⟩
  exact hv (eq_zero_of_extendedMellinContinuation_eq_zero ha hev hc hd hall)

/-! ## Complete and minimal evaluator systems -/

/-- The evaluator system attached to `(Z, m)` is **complete** in `L_a`: a vector all of whose jets
vanish is zero. -/
def IsCompleteEvaluatorSystem (a : ℝ) (Z : Set ℂ) (m : ℂ → ℕ) : Prop :=
  ∀ (v : SoninL2) (c d : ℂ), v ∈ evenSubspace →
    (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) →
    (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) →
    (∀ w ∈ Z, ((m w : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) w) → v = 0

/-- The evaluator system attached to `(Z, m)` is **minimal** in `L_a`: for every `ρ ∈ Z` and every
jet index `k < m ρ` some vector kills every other evaluator but not this one. -/
def IsMinimalEvaluatorSystem (a : ℝ) (Z : Set ℂ) (m : ℂ → ℕ) : Prop :=
  ∀ ρ ∈ Z, ∀ k : ℕ, k < m ρ →
    ∃ (v : SoninL2) (c d : ℂ), v ∈ evenSubspace ∧ v ∈ centralSoninExtendedCarrier a ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) ∧
      (∀ w ∈ Z, w ≠ ρ → ((m w : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) w) ∧
      meromorphicOrderAt (extendedMellinContinuation a c d v) ρ = ((k : ℤ) : WithTop ℤ)

/-- **Burnol's Lemma 7.4.**  If the evaluator system attached to a multiset of the open critical
strip is *not* complete in `L_a`, it is minimal. -/
theorem isMinimal_of_not_isComplete {a : ℝ} (ha : 0 < a) {Z : Set ℂ} {m : ℂ → ℕ}
    (hZ : ∀ w ∈ Z, 0 < w.re ∧ w.re < 1)
    (hnc : ¬ IsCompleteEvaluatorSystem a Z m) :
    IsMinimalEvaluatorSystem a Z m := by
  classical
  rw [IsCompleteEvaluatorSystem] at hnc
  push Not at hnc
  obtain ⟨v, c, d, hev, hc, hd, hann, hv⟩ := hnc
  intro ρ hρ k hk
  obtain ⟨hρ0, hρ1⟩ := hZ ρ hρ
  have hfin : meromorphicOrderAt (extendedMellinContinuation a c d v) ρ ≠ ⊤ :=
    meromorphicOrderAt_extendedMellin_ne_top ha hev hc hd hv hρ0 hρ1
  -- the order at `ρ` is a natural number at least `m ρ`
  obtain ⟨n, hn⟩ : ∃ n : ℤ, meromorphicOrderAt (extendedMellinContinuation a c d v) ρ
      = ((n : ℤ) : WithTop ℤ) := by
    induction hx : meromorphicOrderAt (extendedMellinContinuation a c d v) ρ with
    | top => exact absurd hx hfin
    | coe n => exact ⟨n, rfl⟩
  have hnm : ((m ρ : ℤ)) ≤ n := by
    have := hann ρ hρ
    rw [hn] at this
    exact_mod_cast this
  have hkn : (k : ℤ) < n := by
    have : ((k : ℤ)) < ((m ρ : ℤ)) := by exact_mod_cast hk
    omega
  obtain ⟨j, hj⟩ : ∃ j : ℕ, n = (k : ℤ) + (j : ℤ) := ⟨(n - k).toNat, by omega⟩
  have hstep : meromorphicOrderAt (extendedMellinContinuation a c d v) ρ
      = (((k + j : ℕ) : ℤ) : WithTop ℤ) := by
    rw [hn, hj]
    congr 1
  obtain ⟨w, c', d', hev', hmem', hc', hd', hordw, hother⟩ :=
    exists_order_eq_of_add ha hρ0 hρ1 k j v c d hev hc hd hstep
  refine ⟨w, c', d', hev', hmem', hc', hd', ?_, hordw⟩
  intro y hy hyρ
  obtain ⟨hy0, hy1⟩ := hZ y hy
  rw [hother y hy0 hy1 hyρ]
  exact hann y hy

end

end RHTower
