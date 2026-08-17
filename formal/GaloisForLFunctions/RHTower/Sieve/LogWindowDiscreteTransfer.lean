import GaloisForLFunctions.RHTower.Sieve.LogWindowPlancherel

/-!
# From a discrete family of window sums to the mean square over the line

A short-interval estimate proved by Plancherel controls `∫_ℝ |S(u)|² du`, where
`S(u) = ∑_{u < log n ≤ u+δ} a_n`.  The statements that consume it are usually *discrete*: a finite
family of starting points, one for each outer variable of a bilinear decomposition.  This file is
the interface between the two.

Two facts do the work.  First, two windows of the same length `δ` differ only in the two end
intervals, so `|S(u) - S(u')|` is at most the coefficient bound times the number of integers in
`(e^u, e^{u'}]` together with those in `(e^{u+δ}, e^{u'+δ}]`; each count is at most the length of
the interval plus one.  Second, if the starting points are spread out enough that the intervals
`[u_i, u_i + λ)` are pairwise disjoint, then averaging the pointwise bound over each interval and
summing gives

```text
λ ∑_i |S(u_i)|²  ≤  2 ∫_ℝ |S(u)|² du  +  2λC²·#{i} ,
```

where `C` bounds the oscillation of `S` on each interval.  The second term is the price of
discretisation, and it is negligible exactly when the windows are long.
-/

open MeasureTheory Finset Complex

namespace RHTower.Sieve

noncomputable section

/-- The integers of a finite set lying in a real interval are at most its length plus one. -/
theorem card_filter_mem_Ioc_le (s : Finset ℕ) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    ((s.filter (fun n : ℕ => α < (n : ℝ) ∧ (n : ℝ) ≤ β)).card : ℝ) ≤ β - α + 1 := by
  classical
  have hsub : s.filter (fun n : ℕ => α < (n : ℝ) ∧ (n : ℝ) ≤ β) ⊆ Finset.Ioc ⌊α⌋₊ ⌊β⌋₊ := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨-, h1, h2⟩
    rw [Finset.mem_Ioc]
    exact ⟨(Nat.floor_lt hα).2 h1, Nat.le_floor h2⟩
  have hcard : (s.filter (fun n : ℕ => α < (n : ℝ) ∧ (n : ℝ) ≤ β)).card ≤ ⌊β⌋₊ - ⌊α⌋₊ := by
    have := Finset.card_le_card hsub
    rwa [Nat.card_Ioc] at this
  have hβ : (⌊β⌋₊ : ℝ) ≤ β := Nat.floor_le (hα.trans hαβ)
  have hα' : α - 1 < (⌊α⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one α
    linarith
  have hstep : ((⌊β⌋₊ - ⌊α⌋₊ : ℕ) : ℝ) ≤ β - α + 1 := by
    rcases le_total ⌊α⌋₊ ⌊β⌋₊ with hle | hle
    · rw [Nat.cast_sub hle]
      linarith
    · rw [Nat.sub_eq_zero_of_le hle]
      push_cast
      linarith
  exact le_trans (by exact_mod_cast hcard) hstep

/-- **The window sum moves slowly.**  Two logarithmic windows of the same length differ only in the
two end intervals, so the sums differ by at most the coefficient bound times the number of integers
those end intervals contain. -/
private theorem norm_logWindowSum_sub_le (a : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) {M : ℝ}
    (hM : ∀ n, ‖a n‖ ≤ M) {δ u u' : ℝ} (h : u ≤ u') :
    ‖logWindowSum a s δ u - logWindowSum a s δ u'‖
      ≤ M * ((Real.exp u' - Real.exp u + 1)
          + (Real.exp (u' + δ) - Real.exp (u + δ) + 1)) := by
  classical
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (a 0)) (hM 0)
  set L : Finset ℕ :=
    s.filter (fun n : ℕ => Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u') with hL
  set R : Finset ℕ :=
    s.filter (fun n : ℕ => Real.exp (u + δ) < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp (u' + δ)) with hR
  have hterm : ∀ n ∈ s,
      ‖(Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) u) • a n
        - (Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) u') • a n‖
        ≤ M * ((if n ∈ L then (1 : ℝ) else 0) + (if n ∈ R then (1 : ℝ) else 0)) := by
    intro n hn
    have hn1 : 1 ≤ n := hs n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hmem : ∀ v : ℝ, v ∈ logWindow δ n ↔ (v < Real.log n ∧ Real.log n ≤ v + δ) := by
      intro v
      rw [logWindow, Set.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    by_cases hcu : u ∈ logWindow δ n <;> by_cases hcu' : u' ∈ logWindow δ n
    · rw [Set.indicator_of_mem hcu, Set.indicator_of_mem hcu']
      simp only [sub_self, norm_zero]
      positivity
    · -- `log n ∈ (u, u+δ]` but not in `(u', u'+δ]`; since `u ≤ u'` this forces `log n ≤ u'`
      have h1 := (hmem u).1 hcu
      have h2 : ¬ (u' < Real.log n ∧ Real.log n ≤ u' + δ) := fun hc => hcu' ((hmem u').2 hc)
      have h3 : Real.log n ≤ u' := by
        by_contra hcon
        exact h2 ⟨by linarith, by linarith⟩
      have hnL : n ∈ L := by
        refine Finset.mem_filter.2 ⟨hn, ?_, ?_⟩
        · have := Real.exp_lt_exp.2 h1.1
          rwa [Real.exp_log hnpos] at this
        · have := Real.exp_le_exp.2 h3
          rwa [Real.exp_log hnpos] at this
      rw [Set.indicator_of_mem hcu, Set.indicator_of_notMem hcu']
      simp only [one_smul, zero_smul, sub_zero, if_pos hnL]
      have : (0 : ℝ) ≤ (if n ∈ R then (1 : ℝ) else 0) := by positivity
      nlinarith [hM n, norm_nonneg (a n)]
    · -- `log n ∈ (u', u'+δ]` but not in `(u, u+δ]`; since `u ≤ u'` this forces `u + δ < log n`
      have h1 := (hmem u').1 hcu'
      have h2 : ¬ (u < Real.log n ∧ Real.log n ≤ u + δ) := fun hc => hcu ((hmem u).2 hc)
      have h3 : u + δ < Real.log n := by
        by_contra hcon
        exact h2 ⟨by linarith, by linarith⟩
      have hnR : n ∈ R := by
        refine Finset.mem_filter.2 ⟨hn, ?_, ?_⟩
        · have := Real.exp_lt_exp.2 h3
          rwa [Real.exp_log hnpos] at this
        · have := Real.exp_le_exp.2 h1.2
          rwa [Real.exp_log hnpos] at this
      rw [Set.indicator_of_notMem hcu, Set.indicator_of_mem hcu']
      simp only [one_smul, zero_smul, zero_sub, norm_neg, if_pos hnR]
      have : (0 : ℝ) ≤ (if n ∈ L then (1 : ℝ) else 0) := by positivity
      nlinarith [hM n, norm_nonneg (a n)]
    · rw [Set.indicator_of_notMem hcu, Set.indicator_of_notMem hcu']
      simp only [zero_smul, sub_self, norm_zero]
      positivity
  have hsplit : logWindowSum a s δ u - logWindowSum a s δ u'
      = ∑ n ∈ s, ((Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) u) • a n
          - (Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) u') • a n) := by
    rw [logWindowSum, logWindowSum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  refine le_trans (norm_sum_le_of_le _ hterm) ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem]
  have hLs : L ∩ s = L := Finset.inter_eq_left.2 (Finset.filter_subset _ _)
  have hRs : R ∩ s = R := Finset.inter_eq_left.2 (Finset.filter_subset _ _)
  rw [Finset.inter_comm s L, Finset.inter_comm s R, hLs, hRs]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hu' : (0 : ℝ) ≤ Real.exp u := (Real.exp_pos u).le
  have hcardL : ((L.card : ℕ) : ℝ) ≤ Real.exp u' - Real.exp u + 1 :=
    card_filter_mem_Ioc_le s hu' (Real.exp_le_exp.2 h)
  have hcardR : ((R.card : ℕ) : ℝ) ≤ Real.exp (u' + δ) - Real.exp (u + δ) + 1 :=
    card_filter_mem_Ioc_le s (Real.exp_pos (u + δ)).le
      (Real.exp_le_exp.2 (show u + δ ≤ u' + δ by linarith))
  exact mul_le_mul_of_nonneg_left (add_le_add hcardL hcardR) hM0

/-- **Discrete-to-integral transfer.**  A family of starting points whose surrounding intervals of
common length `lam` are pairwise disjoint, and on each of which the window sum oscillates by at most
`C`, has its discrete mean square controlled by the mean square over the whole line. -/
theorem sum_normSq_logWindowSum_le_integral {ι : Type*} (a : ℕ → ℂ) (s : Finset ℕ) (δ : ℝ)
    {lam : ℝ} (hlam : 0 < lam) {C : ℝ} (hC : 0 ≤ C) (I : Finset ι) (pt : ι → ℝ)
    (hdisj : (I : Set ι).PairwiseDisjoint fun i => Set.Ico (pt i) (pt i + lam))
    (hosc : ∀ i ∈ I, ∀ u ∈ Set.Ico (pt i) (pt i + lam),
      ‖logWindowSum a s δ (pt i) - logWindowSum a s δ u‖ ≤ C) :
    lam * ∑ i ∈ I, ‖logWindowSum a s δ (pt i)‖ ^ 2
      ≤ 2 * (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2) + 2 * lam * C ^ 2 * (I.card : ℝ) := by
  classical
  have hgnn : ∀ u : ℝ, 0 ≤ ‖logWindowSum a s δ u‖ ^ 2 := fun u => by positivity
  have hgint : Integrable (fun u : ℝ => ‖logWindowSum a s δ u‖ ^ 2) (volume : Measure ℝ) := by
    have h2 := memLp_logWindowSum a s δ 2
    exact (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have hvol : ∀ α β : ℝ, (volume : Measure ℝ) (Set.Ico α β) ≠ ⊤ := by
    intro α β
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hconstOn : ∀ (c : ℝ) (α β : ℝ),
      IntegrableOn (fun _ : ℝ => c) (Set.Ico α β) (volume : Measure ℝ) := by
    intro c α β
    exact integrableOn_const (hvol α β) (by finiteness)
  have hpiece : ∀ i ∈ I,
      lam * ‖logWindowSum a s δ (pt i)‖ ^ 2
        ≤ 2 * (∫ u in Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ u‖ ^ 2)
          + 2 * lam * C ^ 2 := by
    intro i hi
    have hbound : ∀ u ∈ Set.Ico (pt i) (pt i + lam),
        ‖logWindowSum a s δ (pt i)‖ ^ 2
          ≤ 2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * C ^ 2 := by
      intro u hu
      have hsub := hosc i hi u hu
      have hrev : ‖logWindowSum a s δ (pt i)‖ - ‖logWindowSum a s δ u‖ ≤ C :=
        le_trans (norm_sub_norm_le _ _) hsub
      nlinarith [hrev, norm_nonneg (logWindowSum a s δ u),
        norm_nonneg (logWindowSum a s δ (pt i)), hC,
        sq_nonneg (‖logWindowSum a s δ u‖ - C)]
    have hmono : (∫ _u in Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ (pt i)‖ ^ 2)
        ≤ ∫ u in Set.Ico (pt i) (pt i + lam),
            (2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * C ^ 2) := by
      refine setIntegral_mono_on (hconstOn _ _ _) ?_ measurableSet_Ico hbound
      exact (hgint.integrableOn.const_mul 2).add (hconstOn _ _ _)
    have hmeas : (volume : Measure ℝ).real (Set.Ico (pt i) (pt i + lam)) = lam := by
      rw [measureReal_def, Real.volume_Ico,
        ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ pt i + lam - pt i)]
      ring
    have hleft : (∫ _u in Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ (pt i)‖ ^ 2)
        = lam * ‖logWindowSum a s δ (pt i)‖ ^ 2 := by
      rw [setIntegral_const, hmeas, smul_eq_mul]
    have hright : (∫ u in Set.Ico (pt i) (pt i + lam),
          (2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * C ^ 2))
        = 2 * (∫ u in Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ u‖ ^ 2)
          + lam * (2 * C ^ 2) := by
      rw [integral_add (hgint.integrableOn.const_mul 2) (hconstOn _ _ _),
        integral_const_mul, setIntegral_const, hmeas, smul_eq_mul]
    rw [hleft] at hmono
    rw [hright] at hmono
    linarith
  have hsum := Finset.sum_le_sum hpiece
  rw [← Finset.mul_sum] at hsum
  have hunion : ∑ i ∈ I, (∫ u in Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ u‖ ^ 2)
      = ∫ u in ⋃ i ∈ I, Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ u‖ ^ 2 :=
    (integral_biUnion_finset I (fun i _ => measurableSet_Ico) hdisj
      (fun i _ => hgint.integrableOn)).symm
  have hle : (∫ u in ⋃ i ∈ I, Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ u‖ ^ 2)
      ≤ ∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2 :=
    setIntegral_le_integral hgint (Filter.Eventually.of_forall hgnn)
  have hsplit : ∑ i ∈ I,
        (2 * (∫ u in Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ u‖ ^ 2)
          + 2 * lam * C ^ 2)
      = 2 * (∑ i ∈ I, ∫ u in Set.Ico (pt i) (pt i + lam), ‖logWindowSum a s δ u‖ ^ 2)
        + 2 * lam * C ^ 2 * (I.card : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsplit, hunion] at hsum
  linarith

end

end RHTower.Sieve
