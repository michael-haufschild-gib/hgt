import GaloisForLFunctions.RHTower.Sieve.FibreStartSeparated

/-!
# Sampling a nonnegative function at separated points

A family of points separated by `σ` carries half-open intervals of length `σ` that are pairwise
disjoint, so a function that is comparable to its values on such an interval is summed at the points
at the cost of one integral:

```text
∑_i F(u_i)  ≤  (2/σ)·∫_ℝ F  +  c·#points ,
```

whenever `F ≥ 0` is integrable and `F(u_i) ≤ 2·F(v) + c` for `v ∈ (u_i, u_i + σ]`.

This is the passage from a discrete family to an integral that the fibre mean square needs: the
starting points `log(x/a)` are `1/(2√x)`-separated (`log_start_separated`), and across such a shift
a logarithmic window sum changes by a bounded number of terms.  Unlike Gallagher's `C¹` argument it
needs no derivative — only the comparison on one interval — which is what a window sum, a step
function, can supply.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset

/-- Half-open intervals of length `σ` at `σ`-separated points are pairwise disjoint. -/
theorem pairwiseDisjoint_Ioc_of_separated {ι : Type*} {t : Finset ι} {u : ι → ℝ} {σ : ℝ}
    (_hσ : 0 < σ) (hsep : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → σ ≤ |u i - u j|) :
    (↑t : Set ι).PairwiseDisjoint (fun i => Set.Ioc (u i) (u i + σ)) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe] at hi hj
  have hgap := hsep i hi j hj hij
  rw [Function.onFun, Set.disjoint_left]
  intro v hv hv'
  rw [Set.mem_Ioc] at hv hv'
  rcases le_total (u i) (u j) with hle | hle
  · have : σ ≤ u j - u i := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hgap
      linarith
    linarith [hv.2, hv'.1]
  · have : σ ≤ u i - u j := by
      rw [abs_of_nonneg (by linarith)] at hgap
      linarith
    linarith [hv'.2, hv.1]

/-- **Sampling at separated points.** -/
theorem sum_le_integral_of_separated {F : ℝ → ℝ} (hF0 : ∀ v, 0 ≤ F v) (hFint : Integrable F)
    {ι : Type*} {t : Finset ι} {u : ι → ℝ} {σ c : ℝ} (hσ : 0 < σ)
    (hsep : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → σ ≤ |u i - u j|)
    (hdom : ∀ i ∈ t, ∀ v ∈ Set.Ioc (u i) (u i + σ), F (u i) ≤ 2 * F v + c) :
    ∑ i ∈ t, F (u i) ≤ (2 / σ) * (∫ v, F v) + c * (t.card : ℝ) := by
  classical
  -- one point at a time
  have hvol : ∀ i : ι, volume.real (Set.Ioc (u i) (u i + σ)) = σ := by
    intro i
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hstep : ∀ i ∈ t,
      σ * F (u i) ≤ 2 * (∫ v in Set.Ioc (u i) (u i + σ), F v) + c * σ := by
    intro i hi
    have hfin : volume (Set.Ioc (u i) (u i + σ)) ≠ ⊤ := by simp
    have hFon : IntegrableOn F (Set.Ioc (u i) (u i + σ)) := hFint.integrableOn
    have hcst : IntegrableOn (fun _ : ℝ => F (u i)) (Set.Ioc (u i) (u i + σ)) :=
      integrableOn_const hfin (by finiteness)
    have hRHS : IntegrableOn (fun v : ℝ => 2 * F v + c) (Set.Ioc (u i) (u i + σ)) :=
      (hFon.const_mul 2).add (integrableOn_const hfin (by finiteness))
    have hmono : (∫ _v in Set.Ioc (u i) (u i + σ), F (u i))
        ≤ ∫ v in Set.Ioc (u i) (u i + σ), (2 * F v + c) :=
      setIntegral_mono_on hcst hRHS measurableSet_Ioc (fun v hv => hdom i hi v hv)
    rw [setIntegral_const, smul_eq_mul, hvol i] at hmono
    rw [MeasureTheory.integral_add ((hFon.const_mul 2)) (integrableOn_const hfin (by finiteness)),
      integral_const_mul, setIntegral_const, smul_eq_mul, hvol i] at hmono
    linarith
  -- the intervals are disjoint, so their integrals add up to at most the whole one
  have hdisj := pairwiseDisjoint_Ioc_of_separated hσ hsep
  have hunion : ∑ i ∈ t, (∫ v in Set.Ioc (u i) (u i + σ), F v)
      = ∫ v in ⋃ i ∈ t, Set.Ioc (u i) (u i + σ), F v :=
    (integral_biUnion_finset t (fun i _ => measurableSet_Ioc) hdisj
      (fun i _ => hFint.integrableOn)).symm
  have hle : (∫ v in ⋃ i ∈ t, Set.Ioc (u i) (u i + σ), F v) ≤ ∫ v, F v :=
    setIntegral_le_integral hFint (Filter.Eventually.of_forall hF0)
  have hsum : σ * (∑ i ∈ t, F (u i))
      ≤ 2 * (∑ i ∈ t, ∫ v in Set.Ioc (u i) (u i + σ), F v) + (t.card : ℝ) * (c * σ) := by
    have hb := Finset.sum_le_sum hstep
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul] at hb
    exact hb
  rw [hunion] at hsum
  have hfinal : σ * (∑ i ∈ t, F (u i)) ≤ 2 * (∫ v, F v) + (t.card : ℝ) * (c * σ) := by
    linarith [hsum, hle]
  have hdiv : ∑ i ∈ t, F (u i) ≤ (2 * (∫ v, F v) + (t.card : ℝ) * (c * σ)) / σ := by
    rw [le_div_iff₀ hσ]
    linarith [hfinal]
  refine le_trans hdiv (le_of_eq ?_)
  field_simp

end RHTower.Sieve

end
