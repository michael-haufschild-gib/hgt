import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Tactic

/-!
# Tangent iterations of a divergent phase wrap infinitely often

The tangent-addition recurrence

```
F 0 = 0,      F (k+1) = (F k + h k) / (1 - F k * h k)
```

is the discrete Riccati flow used to quantise an accumulated phase.  Whenever no denominator
vanishes it is solved exactly by the accumulated arctangent phase,

```
F N = tan (∑_{k < N} arctan (h k)).
```

If the increments are positive, tend to zero, and have divergent arctangent sum, the accumulated
phase crosses every multiple of `π` with an overshoot smaller than the last increment.  Taking the
first crossing index of `m π` therefore produces a subsequence along which `F` tends to `0`.  In
particular such an iteration **cannot** tend to `+∞`, and the mirror statement rules out `-∞` for
negative increments.

This is the exact obstruction to endpoint quantisation of a Riccati-encoded phase: divergence of
the phase forces recurrent returns to zero rather than escape to infinity.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The tangent-addition recurrence -/

/-- The tangent-addition (discrete Riccati) recurrence `F 0 = 0`,
`F (k+1) = (F k + h k) / (1 - F k * h k)`. -/
noncomputable def tangentIterate (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (k + 1) => (tangentIterate h k + h k) / (1 - tangentIterate h k * h k)

@[simp]
theorem tangentIterate_zero (h : ℕ → ℝ) : tangentIterate h 0 = 0 := rfl

theorem tangentIterate_succ (h : ℕ → ℝ) (k : ℕ) :
    tangentIterate h (k + 1)
      = (tangentIterate h k + h k) / (1 - tangentIterate h k * h k) := rfl

/-- The accumulated arctangent phase `S N = ∑_{k < N} arctan (h k)`. -/
def arctanPartialSum (h : ℕ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, Real.arctan (h k)

@[simp]
theorem arctanPartialSum_zero (h : ℕ → ℝ) : arctanPartialSum h 0 = 0 := by
  simp [arctanPartialSum]

theorem arctanPartialSum_succ (h : ℕ → ℝ) (N : ℕ) :
    arctanPartialSum h (N + 1) = arctanPartialSum h N + Real.arctan (h N) :=
  Finset.sum_range_succ _ _

theorem arctanPartialSum_neg (h : ℕ → ℝ) (N : ℕ) :
    arctanPartialSum (fun k => -h k) N = -arctanPartialSum h N := by
  simp only [arctanPartialSum, Real.arctan_neg]
  exact Finset.sum_neg_distrib _

/-- The cosine of an arctangent is strictly positive. -/
theorem cos_arctan_pos (x : ℝ) : 0 < Real.cos (Real.arctan x) := by
  rw [Real.cos_arctan]
  positivity

/-- **Exact solution of the tangent recurrence.**  As long as no denominator vanishes, the
iteration is the tangent of the accumulated arctangent phase, and that phase stays off the poles of
the tangent. -/
theorem cos_ne_zero_and_tangentIterate_eq_tan (h : ℕ → ℝ) :
    ∀ N : ℕ, (∀ k, k < N → 1 - tangentIterate h k * h k ≠ 0) →
      Real.cos (arctanPartialSum h N) ≠ 0 ∧
        tangentIterate h N = Real.tan (arctanPartialSum h N) := by
  intro N
  induction N with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩ <;> simp
  | succ N ih =>
      intro hden
      obtain ⟨hcos, hval⟩ := ih fun k hk => hden k (Nat.lt_succ_of_lt hk)
      have hdenN : 1 - tangentIterate h N * h N ≠ 0 := hden N (Nat.lt_succ_self N)
      set S := arctanPartialSum h N with hS
      set α := Real.arctan (h N) with hα
      have hcosα : 0 < Real.cos α := cos_arctan_pos (h N)
      have htanα : Real.tan α = h N := Real.tan_arctan (h N)
      have hsinS : Real.sin S = Real.tan S * Real.cos S := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp
      have hsinα : Real.sin α = h N * Real.cos α := by
        rw [← htanα, Real.tan_eq_sin_div_cos]
        field_simp
      have hcosSum : Real.cos (S + α)
          = Real.cos S * Real.cos α * (1 - tangentIterate h N * h N) := by
        rw [Real.cos_add, hsinS, hsinα, ← hval]
        ring
      have hsinSum : Real.sin (S + α)
          = Real.cos S * Real.cos α * (tangentIterate h N + h N) := by
        rw [Real.sin_add, hsinS, hsinα, ← hval]
        ring
      have hcosSumNe : Real.cos (S + α) ≠ 0 := by
        rw [hcosSum]
        exact mul_ne_zero (mul_ne_zero hcos (ne_of_gt hcosα)) hdenN
      refine ⟨by rwa [arctanPartialSum_succ], ?_⟩
      rw [arctanPartialSum_succ, tangentIterate_succ, Real.tan_eq_sin_div_cos, hsinSum, hcosSum]
      rw [mul_div_mul_left _ _ (mul_ne_zero hcos (ne_of_gt hcosα))]

theorem tangentIterate_eq_tan (h : ℕ → ℝ) (N : ℕ)
    (hden : ∀ k, k < N → 1 - tangentIterate h k * h k ≠ 0) :
    tangentIterate h N = Real.tan (arctanPartialSum h N) :=
  (cos_ne_zero_and_tangentIterate_eq_tan h N hden).2

/-! ## Phase wrapping -/

/-- The first index at which the accumulated phase of a positive increment sequence reaches
`m π`. -/
def phaseWrapIndex (u : ℕ → ℝ) (m : ℕ) : ℕ :=
  sInf {N : ℕ | (m : ℝ) * Real.pi ≤ ∑ k ∈ Finset.range N, u k}

variable {u : ℕ → ℝ}

theorem phaseWrapIndex_spec
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, u k) atTop atTop) (m : ℕ) :
    (m : ℝ) * Real.pi ≤ ∑ k ∈ Finset.range (phaseWrapIndex u m), u k := by
  have hne : {N : ℕ | (m : ℝ) * Real.pi ≤ ∑ k ∈ Finset.range N, u k}.Nonempty :=
    (hdiv.eventually_ge_atTop ((m : ℝ) * Real.pi)).exists
  exact Nat.sInf_mem hne

theorem lt_of_lt_phaseWrapIndex {m N : ℕ} (hN : N < phaseWrapIndex u m) :
    ∑ k ∈ Finset.range N, u k < (m : ℝ) * Real.pi := by
  by_contra hcon
  exact absurd (Nat.sInf_le (Set.mem_setOf_eq ▸ not_lt.mp hcon)) (not_le.mpr hN)

theorem phaseWrapIndex_pos
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, u k) atTop atTop) {m : ℕ} (hm : 1 ≤ m) :
    0 < phaseWrapIndex u m := by
  rcases Nat.eq_zero_or_pos (phaseWrapIndex u m) with h0 | hpos
  · exfalso
    have hspec := phaseWrapIndex_spec (u := u) hdiv m
    rw [h0] at hspec
    simp only [Finset.range_zero, Finset.sum_empty] at hspec
    have : (0 : ℝ) < (m : ℝ) * Real.pi :=
      mul_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm) Real.pi_pos
    linarith
  · exact hpos

/-- **Minimal overshoot.**  At the first crossing of `m π` the accumulated phase exceeds `m π` by
strictly less than the last increment. -/
theorem phaseWrap_overshoot_lt
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, u k) atTop atTop) {m : ℕ} (hm : 1 ≤ m) :
    (∑ k ∈ Finset.range (phaseWrapIndex u m), u k) - (m : ℝ) * Real.pi
      < u (phaseWrapIndex u m - 1) := by
  have hpos := phaseWrapIndex_pos (u := u) hdiv hm
  have hsucc : phaseWrapIndex u m - 1 + 1 = phaseWrapIndex u m := Nat.succ_pred_eq_of_pos hpos
  have hprev : ∑ k ∈ Finset.range (phaseWrapIndex u m - 1), u k < (m : ℝ) * Real.pi :=
    lt_of_lt_phaseWrapIndex (u := u) (by omega)
  have hsplit : ∑ k ∈ Finset.range (phaseWrapIndex u m), u k
      = (∑ k ∈ Finset.range (phaseWrapIndex u m - 1), u k) + u (phaseWrapIndex u m - 1) := by
    conv_lhs => rw [← hsucc]
    exact Finset.sum_range_succ _ _
  rw [hsplit]
  linarith

theorem tendsto_phaseWrapIndex_atTop
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, u k) atTop atTop) :
    Tendsto (phaseWrapIndex u) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun B => ?_
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ N, N ≤ B → (∑ k ∈ Finset.range N, u k) ≤ C := by
    refine ⟨(Finset.range (B + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos B)⟩
      (fun N => ∑ k ∈ Finset.range N, u k), fun N hN => ?_⟩
    exact Finset.le_sup' (fun N => ∑ k ∈ Finset.range N, u k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hN))
  obtain ⟨M, hM⟩ := exists_nat_gt (C / Real.pi)
  refine ⟨M + 1, fun m hm => ?_⟩
  by_contra hcon
  have hle : phaseWrapIndex u m ≤ B := le_of_lt (not_le.mp hcon)
  have hspec := phaseWrapIndex_spec (u := u) hdiv m
  have hchain : (m : ℝ) * Real.pi ≤ C := hspec.trans (hC _ hle)
  have hMm : (M : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self M) hm
  have hdivpi : C / Real.pi < (m : ℝ) := lt_trans hM hMm
  rw [div_lt_iff₀ Real.pi_pos] at hdivpi
  linarith

/-- **Phase-wrap lemma.**  For increments tending to zero whose partial sums diverge, the tangent
of the accumulated phase tends to zero along the first-crossing indices.  No sign hypothesis is
needed: minimality of the crossing index forces the crossing increment to be positive. -/
theorem tendsto_tan_phaseWrap (hu0 : Tendsto u atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, u k) atTop atTop) :
    Tendsto (fun m => Real.tan (∑ k ∈ Finset.range (phaseWrapIndex u m), u k))
      atTop (𝓝 0) := by
  set S : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, u k with hS
  set n : ℕ → ℕ := phaseWrapIndex u with hn
  set δ : ℕ → ℝ := fun m => S (n m) - (m : ℝ) * Real.pi with hδ
  have hn_top : Tendsto n atTop atTop := tendsto_phaseWrapIndex_atTop hdiv
  have hprev_top : Tendsto (fun m => n m - 1) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun B => ?_
    obtain ⟨M, hM⟩ := tendsto_atTop_atTop.mp hn_top (B + 1)
    exact ⟨M, fun m hm => by have := hM m hm; omega⟩
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have hlower : ∀ᶠ m in atTop, 0 ≤ δ m := by
      filter_upwards with m
      have := phaseWrapIndex_spec (u := u) hdiv m
      simpa [hδ, hS, hn, sub_nonneg] using this
    have hupper : ∀ᶠ m in atTop, δ m ≤ u (n m - 1) := by
      filter_upwards [eventually_ge_atTop 1] with m hm
      exact (phaseWrap_overshoot_lt (u := u) hdiv hm).le
    have hcomp : Tendsto (fun m => u (n m - 1)) atTop (𝓝 0) := hu0.comp hprev_top
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp hlower hupper
  have hper : ∀ m : ℕ, Real.tan (S (n m)) = Real.tan (δ m) := by
    intro m
    have := Real.tan_periodic.sub_nat_mul_eq (x := S (n m)) m
    rw [hδ]
    exact this.symm
  have hcont : Tendsto (fun m => Real.tan (δ m)) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.tan 0 := by
      have hfun : Real.tan = fun x : ℝ => Real.sin x / Real.cos x :=
        funext Real.tan_eq_sin_div_cos
      rw [hfun]
      exact Real.continuous_sin.continuousAt.div Real.continuous_cos.continuousAt (by simp)
    have := hc.tendsto.comp hδ0
    simpa [Real.tan_zero] using this
  exact (hcont.congr fun m => (hper m).symm)

/-! ## The obstruction -/

/-- **Recurrent return to zero.**  A tangent iteration whose increments tend to zero and whose
arctangent phase diverges has a subsequence tending to zero. -/
theorem exists_subseq_tangentIterate_tendsto_zero {h : ℕ → ℝ}
    (h0 : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (arctanPartialSum h) atTop atTop)
    (hden : ∀ k, 1 - tangentIterate h k * h k ≠ 0) :
    ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧
      Tendsto (fun m => tangentIterate h (n m)) atTop (𝓝 0) := by
  set u : ℕ → ℝ := fun k => Real.arctan (h k) with hu
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have hc : ContinuousAt Real.arctan 0 := Real.continuous_arctan.continuousAt
    have := hc.tendsto.comp h0
    simpa [hu, Real.arctan_zero] using this
  have hsum : (fun N => ∑ k ∈ Finset.range N, u k) = arctanPartialSum h := rfl
  have hdiv' : Tendsto (fun N => ∑ k ∈ Finset.range N, u k) atTop atTop := by
    rw [hsum]; exact hdiv
  refine ⟨phaseWrapIndex u, tendsto_phaseWrapIndex_atTop hdiv', ?_⟩
  have hval : ∀ m : ℕ, tangentIterate h (phaseWrapIndex u m)
      = Real.tan (∑ k ∈ Finset.range (phaseWrapIndex u m), u k) := fun m =>
    tangentIterate_eq_tan h _ fun k _ => hden k
  exact (tendsto_tan_phaseWrap hu0 hdiv').congr fun m => (hval m).symm

/-- **No escape to `+∞`.**  Under the hypotheses above the tangent iteration cannot tend to
`+∞`. -/
theorem not_tendsto_atTop_tangentIterate {h : ℕ → ℝ}
    (h0 : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (arctanPartialSum h) atTop atTop)
    (hden : ∀ k, 1 - tangentIterate h k * h k ≠ 0) :
    ¬ Tendsto (tangentIterate h) atTop atTop := by
  intro htop
  obtain ⟨n, hn, hzero⟩ := exists_subseq_tangentIterate_tendsto_zero h0 hdiv hden
  exact not_tendsto_nhds_of_tendsto_atTop (htop.comp hn) 0 hzero

/-! ## Comparison tests for the accumulated phase -/

/-- **Divergence test.**  A minorant with divergent partial sums forces the accumulated arctangent
phase to `+∞`. -/
theorem tendsto_arctanPartialSum_atTop_of_eventually_ge {h b : ℕ → ℝ}
    (hbound : ∀ᶠ k in atTop, b k ≤ Real.arctan (h k))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, b k) atTop atTop) :
    Tendsto (arctanPartialSum h) atTop atTop := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hbound
  set a : ℕ → ℝ := fun k => Real.arctan (h k) with ha
  have hcmp : ∀ N, K ≤ N →
      (∑ k ∈ Finset.range N, b k) + (∑ k ∈ Finset.range K, (a k - b k))
        ≤ ∑ k ∈ Finset.range N, a k := by
    intro N hN
    have hsplitA : (∑ k ∈ Finset.range K, a k) + ∑ k ∈ Finset.Ico K N, a k
        = ∑ k ∈ Finset.range N, a k := Finset.sum_range_add_sum_Ico a hN
    have hsplitB : (∑ k ∈ Finset.range K, b k) + ∑ k ∈ Finset.Ico K N, b k
        = ∑ k ∈ Finset.range N, b k := Finset.sum_range_add_sum_Ico b hN
    have htail : ∑ k ∈ Finset.Ico K N, b k ≤ ∑ k ∈ Finset.Ico K N, a k :=
      Finset.sum_le_sum fun k hk => hK k (Finset.mem_Ico.mp hk).1
    rw [Finset.sum_sub_distrib, ← hsplitA, ← hsplitB]
    linarith
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (∑ k ∈ Finset.range K, (a k - b k)) hdiv)
  filter_upwards [eventually_ge_atTop K] with N hN
  exact hcmp N hN

/-- **Divergence test, negative side.** -/
theorem tendsto_arctanPartialSum_atBot_of_eventually_le {h b : ℕ → ℝ}
    (hbound : ∀ᶠ k in atTop, Real.arctan (h k) ≤ b k)
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, b k) atTop atBot) :
    Tendsto (arctanPartialSum h) atTop atBot := by
  have hneg : Tendsto (arctanPartialSum fun k => -h k) atTop atTop := by
    refine tendsto_arctanPartialSum_atTop_of_eventually_ge
      (b := fun k => -b k) ?_ ?_
    · filter_upwards [hbound] with k hk
      rw [Real.arctan_neg]
      linarith
    · exact (tendsto_neg_atTop_iff.mpr hdiv).congr fun N => (Finset.sum_neg_distrib _).symm
  have hrw : ∀ N, arctanPartialSum (fun k => -h k) N = -arctanPartialSum h N := fun N =>
    arctanPartialSum_neg h N
  have : Tendsto (fun N => -arctanPartialSum h N) atTop atTop := hneg.congr hrw
  exact tendsto_neg_atTop_iff.mp this

/-! ## The mirrored negative iteration -/

theorem tangentIterate_neg (h : ℕ → ℝ) (N : ℕ) :
    tangentIterate (fun k => -h k) N = -tangentIterate h N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [tangentIterate_succ, tangentIterate_succ, ih]
      have hden : 1 - -tangentIterate h N * -h N = 1 - tangentIterate h N * h N := by ring
      rw [hden, ← neg_div]
      congr 1
      ring

/-- **No escape to `-∞`.**  A tangent iteration whose increments tend to zero and whose arctangent
phase diverges to `-∞` cannot tend to `-∞`; it returns to zero along a subsequence. -/
theorem not_tendsto_atBot_tangentIterate {h : ℕ → ℝ}
    (h0 : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (arctanPartialSum h) atTop atBot)
    (hden : ∀ k, 1 - tangentIterate h k * h k ≠ 0) :
    ¬ Tendsto (tangentIterate h) atTop atBot := by
  intro hbot
  set g : ℕ → ℝ := fun k => -h k with hg
  have hg0 : Tendsto g atTop (𝓝 0) := by simpa [hg] using h0.neg
  have hgdiv : Tendsto (arctanPartialSum g) atTop atTop := by
    have hgh : ∀ N, arctanPartialSum g N = -arctanPartialSum h N := fun N =>
      arctanPartialSum_neg h N
    have hneg := tendsto_neg_atTop_iff.mpr hdiv
    exact hneg.congr fun N => (hgh N).symm
  have hgden : ∀ k, 1 - tangentIterate g k * g k ≠ 0 := by
    intro k
    have hrw : 1 - tangentIterate g k * g k = 1 - tangentIterate h k * h k := by
      rw [hg, tangentIterate_neg]; ring
    rw [hrw]
    exact hden k
  have hgtop : Tendsto (tangentIterate g) atTop atTop := by
    have hgh : ∀ N, tangentIterate g N = -tangentIterate h N := fun N => tangentIterate_neg h N
    have hneg := tendsto_neg_atTop_iff.mpr hbot
    exact hneg.congr fun N => (hgh N).symm
  exact not_tendsto_atTop_tangentIterate hg0 hgdiv hgden hgtop

end

end GaloisForLFunctions.HTGeometry
