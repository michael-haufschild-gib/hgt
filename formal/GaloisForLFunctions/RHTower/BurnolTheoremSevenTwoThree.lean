import GaloisForLFunctions.RHTower.BurnolTheoremSevenOne

/-!
# Burnol's Lemma 7.6 and Theorems 7.2, 7.3

Iterating the dilation shift of `BurnolLemmaSevenFive` along a finite list of strip points gains
one order of vanishing at each entry of the list, at the cost of an arbitrarily small drop of the
aperture.  This is Burnol's replacement of `θ(s)` by `P(s)θ(s)` — the polynomial `P` is here the
product of the dilation-difference multipliers.

Consequences:

* **Lemma 7.6 / Theorem 7.2** — if the system is not complete at `a`, it stays not complete at every
  smaller aperture *even after adding arbitrarily finitely many evaluators*; by Lemma 7.4 it is then
  minimal there.
* **Theorem 7.3** — dually, if the system is complete at some `b < a`, then it stays complete at `a`
  *after omitting arbitrarily finitely many evaluators*.

## Main results

* `exists_nonzero_annihilating_list` — **Lemma 7.6**
* `not_isComplete_add_of_lt` — **Theorem 7.2**
* `isComplete_omit_of_lt` — **Theorem 7.3**
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Classical in
/-- **Lemma 7.6.**  Iterating the dilation shift along a list of strip points. -/
theorem exists_nonzero_annihilating_list :
    ∀ (L : List ℂ), (∀ ρ ∈ L, 0 < ρ.re ∧ ρ.re < 1) →
      ∀ (a b : ℝ), 0 < b → b < a →
      ∀ (v : SoninL2) (c d : ℂ), v ∈ evenSubspace → v ∈ centralSoninExtendedCarrier a →
        (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
          ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) →
        (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) →
        v ≠ 0 →
      ∃ (V : SoninL2) (c' d' : ℂ), V ≠ 0 ∧ V ∈ evenSubspace ∧
        V ∈ centralSoninExtendedCarrier b ∧
        (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval b →
          ((fourierUnitary V : SoninL2) : ℝ → ℂ) x = c') ∧
        (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (V : ℝ → ℂ) t = d') ∧
        ∀ w : ℂ, 0 < w.re → w.re < 1 →
          ((L.count w : ℤ) : WithTop ℤ)
              + meromorphicOrderAt (extendedMellinContinuation a c d v) w
            ≤ meromorphicOrderAt (extendedMellinContinuation b c' d' V) w := by
  intro L
  induction L with
  | nil =>
      intro _ a b hb hab v c d hev hmem hc hd hv
      have ha : 0 < a := lt_trans hb hab
      have hsub : centralInterval b ⊆ centralInterval a := by
        intro x hx
        rcases hx with ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      have hcb : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval b →
          ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c := by
        filter_upwards [hc] with x hx hmem'
        exact hx (hsub hmem')
      have hdb : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (v : ℝ → ℂ) t = d := by
        filter_upwards [hd] with t ht hmem'
        exact ht (hsub hmem')
      refine ⟨v, c, d, hv, hev, centralSoninExtendedCarrier_antitone hab.le hmem, hcb, hdb, ?_⟩
      intro w hw0 hw1
      have heq : meromorphicOrderAt (extendedMellinContinuation b c d v) w
          = meromorphicOrderAt (extendedMellinContinuation a c d v) w := by
        have hloc : extendedMellinContinuation b c d v
            =ᶠ[𝓝[≠] w] extendedMellinContinuation a c d v := by
          refine EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds
          filter_upwards [isOpen_criticalOpenStrip.mem_nhds
            (⟨hw0, hw1⟩ : w ∈ {u : ℂ | 0 < u.re ∧ u.re < 1})] with u hu
          exact extendedMellinContinuation_aperture_eq hb hab.le hev hcb hdb hc hd hu.1 hu.2
        exact meromorphicOrderAt_congr hloc
      rw [heq]
      simp
  | cons ρ L ih =>
      intro hL a b hb hab v c d hev hmem hc hd hv
      have ha : 0 < a := lt_trans hb hab
      obtain ⟨hρ0, hρ1⟩ := hL ρ (by simp)
      have hLtail : ∀ x ∈ L, 0 < x.re ∧ x.re < 1 := fun x hx => hL x (by simp [hx])
      set b' : ℝ := (a + b) / 2 with hb'
      have hbb' : b < b' := by rw [hb']; linarith
      have hb'a : b' < a := by rw [hb']; linarith
      have hb'0 : 0 < b' := lt_trans hb hbb'
      obtain ⟨V₁, c₁, d₁, hV₁ne, hV₁ev, hV₁mem, hc₁, hd₁, hord₁⟩ :=
        ih hLtail a b' hb'0 hb'a v c d hev hmem hc hd hv
      obtain ⟨V, c', d', hVne, hVev, hVmem, hc', hd', hordfun⟩ :=
        exists_dilationShift hb'0 hb hbb' hρ0 hρ1 hV₁ev hV₁mem hc₁ hd₁ hV₁ne
      refine ⟨V, c', d', hVne, hVev, hVmem, hc', hd', ?_⟩
      intro w hw0 hw1
      have hr0 : 0 < b' / b := div_pos hb'0 hb
      have hmult : ((((if ρ = w then 1 else 0) : ℕ) : ℤ) : WithTop ℤ)
          ≤ meromorphicOrderAt (dilationDifferenceMultiplier (b' / b) ρ) w := by
        by_cases hwρ : ρ = w
        · rw [if_pos hwρ]
          have hone := one_le_meromorphicOrderAt_of_eq_zero
            ((differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt ρ)
            (dilationDifferenceMultiplier_self (b' / b) ρ)
          rw [← hwρ]
          simpa using hone
        · rw [if_neg hwρ]
          simpa using meromorphicOrderAt_nonneg_of_analyticAt
            ((differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt w)
      rw [hordfun w hw0 hw1]
      have hcount : ((ρ :: L).count w : ℤ)
          = (((if ρ = w then 1 else 0) : ℕ) : ℤ) + (L.count w : ℤ) := by
        simp only [List.count_cons, beq_iff_eq]
        split_ifs <;> push_cast <;> ring
      have hsplit : (((ρ :: L).count w : ℤ) : WithTop ℤ)
            + meromorphicOrderAt (extendedMellinContinuation a c d v) w
          = ((((if ρ = w then 1 else 0) : ℕ) : ℤ) : WithTop ℤ)
            + ((((L.count w : ℕ) : ℤ) : WithTop ℤ)
              + meromorphicOrderAt (extendedMellinContinuation a c d v) w) := by
        rw [← add_assoc, ← WithTop.coe_add]
        congr 2
      rw [hsplit]
      exact add_le_add hmult (hord₁ w hw0 hw1)

/-- **Theorem 7.2.**  Failure of completeness persists to every smaller aperture, even after
adding arbitrarily finitely many evaluators; by Lemma 7.4 the enlarged system is then minimal. -/
theorem not_isComplete_add_of_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {m : ℂ → ℕ} {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hmρ : 1 ≤ m ρ)
    (L : List ℂ) (hL : ∀ x ∈ L, 0 < x.re ∧ x.re < 1) {m' : ℂ → ℕ}
    (hm' : ∀ w : ℂ, m' w ≤ m w + L.count w)
    (hnc : ¬ IsCompleteEvaluatorSystem a {w : ℂ | 0 < w.re ∧ w.re < 1} m) :
    ¬ IsCompleteEvaluatorSystem b {w : ℂ | 0 < w.re ∧ w.re < 1} m' := by
  classical
  intro hcomp
  have hZ : ∀ w ∈ {w : ℂ | 0 < w.re ∧ w.re < 1}, 0 < w.re ∧ w.re < 1 := fun w hw => hw
  have hmin := isMinimal_of_not_isComplete ha hZ hnc
  obtain ⟨v, c, d, hev, hmem, hc, hd, hother, hself⟩ :=
    hmin ρ ⟨hρ0, hρ1⟩ (m ρ - 1) (by omega)
  have hv : v ≠ 0 := by
    intro h0
    have := meromorphicOrderAt_eq_top_of_eq_zero ha hev hc hd h0 hρ0 hρ1
    rw [this] at hself
    exact absurd hself.symm WithTop.coe_ne_top
  obtain ⟨V, c', d', hVne, hVev, hVmem, hc', hd', hord⟩ :=
    exists_nonzero_annihilating_list (ρ :: L) (by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · rw [h]; exact ⟨hρ0, hρ1⟩
      · exact hL x h) a b hb hab v c d hev hmem hc hd hv
  refine hVne (hcomp V c' d' hVev hc' hd' ?_)
  intro w hw
  obtain ⟨hw0, hw1⟩ := hw
  refine le_trans ?_ (hord w hw0 hw1)
  have hbase : (((m w : ℤ) - (if ρ = w then 1 else 0) : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) w := by
    by_cases hwρ : ρ = w
    · rw [if_pos hwρ, ← hwρ]
      have hcast : ((m ρ : ℤ) - 1 : ℤ) = ((m ρ - 1 : ℕ) : ℤ) := by omega
      rw [hcast, hself]
    · rw [if_neg hwρ, sub_zero]
      exact hother w ⟨hw0, hw1⟩ (Ne.symm hwρ)
  have hcount : (((ρ :: L).count w : ℤ) : WithTop ℤ)
      = (((if ρ = w then 1 else 0) : ℤ) : WithTop ℤ) + ((L.count w : ℤ) : WithTop ℤ) := by
    rw [← WithTop.coe_add]
    congr 1
    simp only [List.count_cons, beq_iff_eq]
    split_ifs <;> push_cast <;> ring
  rw [hcount, add_assoc]
  have hstep : ((m' w : ℤ) : WithTop ℤ)
      ≤ (((if ρ = w then 1 else 0) : ℤ) : WithTop ℤ)
        + (((L.count w : ℤ) : WithTop ℤ) + (((m w : ℤ) - (if ρ = w then 1 else 0) : ℤ)
          : WithTop ℤ)) := by
    rw [← WithTop.coe_add, ← WithTop.coe_add]
    refine WithTop.coe_le_coe.2 ?_
    have hcast : ((m' w : ℤ)) ≤ ((m w : ℤ)) + ((L.count w : ℤ)) := by exact_mod_cast hm' w
    have hrhs : ((if ρ = w then (1 : ℤ) else 0)
        + ((L.count w : ℤ) + ((m w : ℤ) - (if ρ = w then (1 : ℤ) else 0))))
        = (L.count w : ℤ) + (m w : ℤ) := by
      by_cases hwρ : ρ = w
      · rw [if_pos hwρ]; ring
      · rw [if_neg hwρ]; ring
    rw [hrhs]
    omega
  refine le_trans hstep ?_
  gcongr

/-- **Theorem 7.3.**  Completeness at some smaller aperture forces completeness at `a` even after
omitting arbitrarily finitely many evaluators. -/
theorem isComplete_omit_of_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {m m' : ℂ → ℕ} {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hmρ : 1 ≤ m' ρ)
    (L : List ℂ) (hL : ∀ x ∈ L, 0 < x.re ∧ x.re < 1)
    (hm : ∀ w : ℂ, m w ≤ m' w + L.count w)
    (hcompb : IsCompleteEvaluatorSystem b {w : ℂ | 0 < w.re ∧ w.re < 1} m) :
    IsCompleteEvaluatorSystem a {w : ℂ | 0 < w.re ∧ w.re < 1} m' := by
  by_contra hnc
  exact not_isComplete_add_of_lt ha hb hab hρ0 hρ1 hmρ L hL hm hnc hcompb

end

end RHTower
