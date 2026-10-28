import GaloisForLFunctions.ArithmeticIndexDescent.AShortNewCellPaysItsOwnInteraction

/-!
# Nested positive sections with widths chosen once

For every strictly increasing sequence of centres, the complete Weil form is
coercive on a single choice of independently profiled cells, uniformly over
all finite prefixes. Canonical envelopes determine each mixed-source charge
before the smaller actual widths are chosen. A decreasing reserve pays all
extensions while retaining a unit square-mass floor. Logarithmic centres give
an infinite arithmetic family with no subsequent shrinking of old cells.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

private def cellEnvelopeWidth (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  min 1 ((b (n + 1) - b n) / 2)

private def prefixEnvelope (b : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ Finset.range n,
    Icc (b i - cellEnvelopeWidth b i / 2) (b i + cellEnvelopeWidth b i / 2)

private theorem cellEnvelopeWidth_pos {b : ℕ → ℝ} (hb : StrictMono b) (n : ℕ) :
    0 < cellEnvelopeWidth b n :=
  lt_min zero_lt_one (div_pos (sub_pos.mpr (hb (Nat.lt_succ_self n))) (by norm_num))

private theorem not_mem_prefixEnvelope {b : ℕ → ℝ} (hb : StrictMono b) (n : ℕ) :
    b n ∉ prefixEnvelope b n := by
  intro hmem
  simp only [prefixEnvelope, Set.mem_iUnion] at hmem
  obtain ⟨i, hi, hui⟩ := hmem
  have hin : i < n := Finset.mem_range.mp hi
  have hnext : b (i + 1) ≤ b n := hb.monotone (by omega)
  have hinc : b i < b (i + 1) := hb (Nat.lt_succ_self i)
  have he : cellEnvelopeWidth b i ≤ (b (i + 1) - b i) / 2 := min_le_right _ _
  linarith only [hui.2, hnext, hinc, he]

private theorem exists_prefixEnvelope_gap {b : ℕ → ℝ} (hb : StrictMono b) (n : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ u ∈ prefixEnvelope b n, d < |u - b n| := by
  have hc : IsCompact (prefixEnvelope b n) :=
    (Finset.range n).isCompact_biUnion fun _ _ => isCompact_Icc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hc.isClosed.isOpen_compl
    (b n) (not_mem_prefixEnvelope hb n)
  refine ⟨r / 2, div_pos hr (by norm_num), ?_⟩
  intro u hu
  have hfar : r ≤ |u - b n| := by
    by_contra hnot
    have huB : u ∈ Metric.ball (b n) r := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_not_ge hnot
    exact hball huB hu
  linarith only [hr, hfar]

private theorem exists_prefixEnvelope_window {b : ℕ → ℝ} (hb : StrictMono b) (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ u ∈ prefixEnvelope b n, |u| < R := by
  let S := ∑ i ∈ Finset.range n, (|b i| + cellEnvelopeWidth b i / 2)
  have hterm (i : ℕ) : 0 ≤ |b i| + cellEnvelopeWidth b i / 2 :=
    add_nonneg (abs_nonneg _) (div_nonneg (cellEnvelopeWidth_pos hb i).le (by norm_num))
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hterm i
  refine ⟨S + 1, by linarith only [hS], ?_⟩
  intro u hu
  simp only [prefixEnvelope, Set.mem_iUnion] at hu
  obtain ⟨i, hi, hui⟩ := hu
  have hdist : |u - b i| ≤ cellEnvelopeWidth b i / 2 :=
    abs_le.mpr ⟨by linarith only [hui.1], by linarith only [hui.2]⟩
  have htri := abs_add_le (u - b i) (b i)
  rw [sub_add_cancel] at htri
  have hiS : |b i| + cellEnvelopeWidth b i / 2 ≤ S :=
    Finset.single_le_sum (fun j _ => hterm j) hi
  linarith only [hdist, htri, hiS]

/-- All finite independently profiled prefixes are positive for one fixed
choice of widths. No positivity or mixed-source estimate is an input. -/
theorem exists_fixedCellWidths_coercive {b : ℕ → ℝ} (hb : StrictMono b) :
    ∃ w : ℕ → ℝ, (∀ n, 0 < w n) ∧ (∀ n, w n ≤ 1) ∧
      ∀ N : ℕ, ∀ G : ℕ → realTests,
        (∀ i ∈ Finset.range N, ∀ u, w i / 2 < |u - b i| → (G i).1 u = 0) →
        sectionMass (∑ i ∈ Finset.range N, G i).1 ≤
          realWeilForm (∑ i ∈ Finset.range N, G i) (∑ i ∈ Finset.range N, G i) := by
  let a : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)
  have hε (n : ℕ) : 0 < ε n := by
    apply sub_pos.mpr
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith only)
  have haε (n : ℕ) : a n - ε n = a (n + 1) := by
    dsimp [a, ε]
    push_cast
    ring
  choose R hR hwindow using exists_prefixEnvelope_window hb
  choose d hd hgap using exists_prefixEnvelope_gap hb
  choose η hη hext using fun n =>
    exists_shortCell_diagonal_extension (hR n) (hd n) (hε n) (b n) (a (n + 1))
  let w : ℕ → ℝ := fun n => min (cellEnvelopeWidth b n) (min (d n) (η n / 2))
  have hw (n : ℕ) : 0 < w n :=
    lt_min (cellEnvelopeWidth_pos hb n) (lt_min (hd n) (div_pos (hη n) (by norm_num)))
  have hwe (n : ℕ) : w n ≤ cellEnvelopeWidth b n := min_le_left _ _
  have hwd (n : ℕ) : w n ≤ d n := (min_le_right _ _).trans (min_le_left _ _)
  have hwη (n : ℕ) : w n < η n := by
    have hh : w n ≤ η n / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hh, hη n]
  refine ⟨w, hw, fun n => (hwe n).trans (min_le_left _ _), ?_⟩
  have hfloor (N : ℕ) : ∀ G : ℕ → realTests,
      (∀ i ∈ Finset.range N, ∀ u, w i / 2 < |u - b i| → (G i).1 u = 0) →
      a N * sectionMass (∑ i ∈ Finset.range N, G i).1 ≤
        realWeilForm (∑ i ∈ Finset.range N, G i) (∑ i ∈ Finset.range N, G i) := by
    induction N with
    | zero =>
      intro G _
      simp only [Finset.range_zero, Finset.sum_empty, map_zero, LinearMap.zero_apply]
      simp [sectionMass]
    | succ n ih =>
      intro G hG
      let p : realTests := ∑ i ∈ Finset.range n, G i
      have hold := ih G (fun i hi => hG i (Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))))
      change a n * sectionMass p.1 ≤ realWeilForm p p at hold
      have hgs := hG n (Finset.mem_range.mpr (Nat.lt_succ_self n))
      have hp0 : ∀ u, u ∉ prefixEnvelope b n → p.1 u = 0 := by
        intro u hu
        change (∑ i ∈ Finset.range n, G i).1 u = 0
        rw [Submodule.coe_sum, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro i hi
        apply hG i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))) u
        by_contra hnot
        have hdist : |u - b i| ≤ w i / 2 := le_of_not_gt hnot
        have hcell : u ∈ Icc (b i - cellEnvelopeWidth b i / 2)
            (b i + cellEnvelopeWidth b i / 2) := by
          obtain ⟨hl, hr⟩ := abs_le.mp hdist
          constructor <;> linarith only [hl, hr, hwe i]
        apply hu
        simp only [prefixEnvelope, Set.mem_iUnion]
        exact ⟨i, hi, hcell⟩
      have hpR : ∀ u, R n < |u| → p.1 u = 0 := by
        intro u hu
        apply hp0
        intro hm
        exact (hwindow n u hm).not_gt hu
      have hpd : ∀ u, p.1 u ≠ 0 → d n < |u - b n| := by
        intro u hu
        apply hgap n u
        by_contra hm
        exact hu (hp0 u hm)
      have hdisj : ∀ u, p.1 u * (G n).1 u = 0 := by
        intro u
        by_cases hpz : p.1 u = 0
        · rw [hpz, zero_mul]
        have hdist := hpd u hpz
        have hz : (G n).1 u = 0 := hgs u (by linarith only [hdist, hwd n, hd n])
        rw [hz, mul_zero]
      have hnew := hext n (w n) (hw n) (hwη n) p (G n) hpR hpd hgs
      rw [Finset.sum_range_succ]
      change a (n + 1) * sectionMass (p + G n).1 ≤ realWeilForm (p + G n) (p + G n)
      rw [sectionMass_add_of_disjoint p (G n) hdisj]
      have hcost : a n * sectionMass p.1 - ε n * sectionMass p.1 =
          a (n + 1) * sectionMass p.1 := by rw [← sub_mul, haε n]
      nlinarith only [hold, hnew, hcost]
  intro N G hG
  have ha : 1 ≤ a N := by
    have hh : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    dsimp [a]
    linarith only [hh]
  have hmass := mul_le_mul_of_nonneg_right ha (sectionMass_nonneg (∑ i ∈ Finset.range N, G i).1)
  rw [one_mul] at hmass
  exact hmass.trans (hfloor N G hG)

/-- The arithmetic centres `log(n+1)` admit fixed positive widths with a unit
Weil floor on every finite independently profiled prefix. -/
theorem exists_fixedLogCellWidths_coercive :
    ∃ w : ℕ → ℝ, (∀ n, 0 < w n) ∧ (∀ n, w n ≤ 1) ∧
      ∀ N : ℕ, ∀ G : ℕ → realTests,
        (∀ i ∈ Finset.range N, ∀ u,
          w i / 2 < |u - Real.log ((i : ℝ) + 1)| → (G i).1 u = 0) →
        sectionMass (∑ i ∈ Finset.range N, G i).1 ≤
          realWeilForm (∑ i ∈ Finset.range N, G i) (∑ i ∈ Finset.range N, G i) := by
  apply exists_fixedCellWidths_coercive
  intro i j hij
  apply Real.log_lt_log (by positivity)
  have hc : (i : ℝ) < j := by exact_mod_cast hij
  linarith only [hc]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_fixedCellWidths_coercive
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_fixedLogCellWidths_coercive
