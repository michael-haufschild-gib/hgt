import Mathlib

/-!
# Splitting a mean square by level sets

The reduction a Type II mean square consumes: below a threshold the square is bounded by the
threshold, and above it the dyadic level sets are counted by a large-values theorem.  The split
itself is pointwise and carries no analysis:

```text
x² ≤ V₀² + ∑_{j < J} (2^{j+1}V₀)² · 1_{2^j V₀ ≤ x}       (0 ≤ x ≤ M ≤ 2^J V₀),
```

because a value below `V₀` is dominated by the threshold, and a value in the dyadic block
`[2^j V₀, 2^{j+1}V₀]` is dominated by the block's top while switching that block's indicator on.
Integrating over a set of finite measure turns it into the mean-square split.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- **The pointwise level split.** -/
theorem sq_le_levelSplit {V₀ M x : ℝ} (hV₀ : 0 < V₀) (hx : 0 ≤ x) (hxM : x ≤ M)
    {J : ℕ} (hJ : M ≤ 2 ^ J * V₀) :
    x ^ 2 ≤ V₀ ^ 2
      + ∑ j ∈ Finset.range J,
          (2 ^ (j + 1) * V₀) ^ 2 * (if 2 ^ j * V₀ ≤ x then (1 : ℝ) else 0) := by
  classical
  have hnn : ∀ j ∈ Finset.range J,
      (0 : ℝ) ≤ (2 ^ (j + 1) * V₀) ^ 2 * (if 2 ^ j * V₀ ≤ x then (1 : ℝ) else 0) := by
    intro j _
    split_ifs <;> positivity
  by_cases hsmall : x ≤ V₀
  · have h1 : x ^ 2 ≤ V₀ ^ 2 := by nlinarith [hx, hsmall]
    have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J,
        (2 ^ (j + 1) * V₀) ^ 2 * (if 2 ^ j * V₀ ≤ x then (1 : ℝ) else 0) :=
      Finset.sum_nonneg hnn
    linarith
  · push Not at hsmall
    have hJpos : 0 < J := by
      by_contra hJ0
      have hJ0' : J = 0 := by omega
      subst hJ0'
      simp only [pow_zero, one_mul] at hJ
      linarith [hsmall, hxM, hJ]
    have hex : ∃ j ∈ Finset.range J, 2 ^ j * V₀ ≤ x ∧ x ≤ 2 ^ (j + 1) * V₀ := by
      by_contra hcon
      push Not at hcon
      have hstep : ∀ j : ℕ, j ≤ J → 2 ^ j * V₀ ≤ x := by
        intro j
        induction j with
        | zero => intro _; simpa using hsmall.le
        | succ m ih =>
          intro hmJ
          have hm : m < J := by omega
          exact (hcon m (Finset.mem_range.2 hm) (ih (by omega))).le
      have hprev : 2 ^ (J - 1) * V₀ ≤ x := hstep (J - 1) (by omega)
      have hlast := hcon (J - 1) (Finset.mem_range.2 (by omega)) hprev
      rw [show J - 1 + 1 = J from by omega] at hlast
      linarith [hlast, hxM, hJ]
    obtain ⟨j, hj, hlow, hhigh⟩ := hex
    have hterm : x ^ 2 ≤ (2 ^ (j + 1) * V₀) ^ 2 := by
      have h0 : (0 : ℝ) ≤ 2 ^ (j + 1) * V₀ := by positivity
      nlinarith [hx, hhigh, h0]
    have hpick : (2 ^ (j + 1) * V₀) ^ 2 * (if 2 ^ j * V₀ ≤ x then (1 : ℝ) else 0)
        ≤ ∑ i ∈ Finset.range J,
            (2 ^ (i + 1) * V₀) ^ 2 * (if 2 ^ i * V₀ ≤ x then (1 : ℝ) else 0) :=
      Finset.single_le_sum hnn hj
    rw [if_pos hlow, mul_one] at hpick
    have hV0sq : (0 : ℝ) ≤ V₀ ^ 2 := by positivity
    linarith [hterm, hpick, hV0sq]

/-- **The mean square split by level sets.** -/
theorem integral_sq_le_levelSplit {E : Set ℝ} {f : ℝ → ℝ}
    (hE : MeasurableSet E) (hmeas : Measurable f)
    (hint : IntegrableOn (fun t => (f t) ^ 2) E)
    (hf0 : ∀ t, 0 ≤ f t) {V₀ M : ℝ} (hV₀ : 0 < V₀) (hM : ∀ t, f t ≤ M)
    {J : ℕ} (hJ : M ≤ 2 ^ J * V₀) (hvol : volume E ≠ ⊤) :
    (∫ t in E, (f t) ^ 2)
      ≤ V₀ ^ 2 * (volume E).toReal
        + ∑ j ∈ Finset.range J,
            (2 ^ (j + 1) * V₀) ^ 2 * (volume ({t | 2 ^ j * V₀ ≤ f t} ∩ E)).toReal := by
  classical
  have hmeasSet : ∀ j : ℕ, MeasurableSet {t : ℝ | 2 ^ j * V₀ ≤ f t} := fun j =>
    measurableSet_le measurable_const hmeas
  set g : ℝ → ℝ := fun t => V₀ ^ 2
    + ∑ j ∈ Finset.range J,
        (2 ^ (j + 1) * V₀) ^ 2 * Set.indicator {t | 2 ^ j * V₀ ≤ f t} (1 : ℝ → ℝ) t with hg
  have hindInt : ∀ j : ℕ,
      IntegrableOn (Set.indicator {t : ℝ | 2 ^ j * V₀ ≤ f t} (1 : ℝ → ℝ)) E := fun j =>
    ((integrableOn_const hvol : IntegrableOn (fun _ : ℝ => (1 : ℝ)) E)).indicator (hmeasSet j)
  have hsumInt : IntegrableOn (fun t => ∑ j ∈ Finset.range J,
      (2 ^ (j + 1) * V₀) ^ 2
        * Set.indicator {t | 2 ^ j * V₀ ≤ f t} (1 : ℝ → ℝ) t) E := by
    refine integrable_finsetSum _ fun j _ => ?_
    exact (hindInt j).const_mul _
  have hconstInt : IntegrableOn (fun _ : ℝ => V₀ ^ 2) E := integrableOn_const hvol
  have hgint : IntegrableOn g E := hconstInt.add hsumInt
  have hpt : ∀ t ∈ E, (f t) ^ 2 ≤ g t := by
    intro t _
    refine le_trans (sq_le_levelSplit (V₀ := V₀) (M := M) (x := f t) hV₀ (hf0 t) (hM t) hJ)
      (le_of_eq ?_)
    rw [hg]
    congr 1
  refine le_trans (setIntegral_mono_on hint hgint hE hpt) (le_of_eq ?_)
  rw [hg, integral_add hconstInt hsumInt, setIntegral_const, integral_finsetSum _
    (fun j _ => (hindInt j).const_mul _)]
  have hterm : ∀ j : ℕ,
      (∫ t in E, (2 ^ (j + 1) * V₀) ^ 2
          * Set.indicator {t | 2 ^ j * V₀ ≤ f t} (1 : ℝ → ℝ) t)
        = (2 ^ (j + 1) * V₀) ^ 2 * (volume ({t | 2 ^ j * V₀ ≤ f t} ∩ E)).toReal := by
    intro j
    rw [integral_const_mul, integral_indicator_one (hmeasSet j)]
    congr 1
    simp [Measure.real, Measure.restrict_apply (hmeasSet j)]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  congr 1
  simp [Measure.real, mul_comm]

/-- **The weighted mean square split by level sets.**  The form a Type II estimate consumes: the
square of the short factor is split against the mean square of the long one. -/
theorem integral_sq_mul_le_levelSplit {E : Set ℝ} {f g : ℝ → ℝ}
    (hE : MeasurableSet E) (hmeas : Measurable f)
    (hint : IntegrableOn (fun t => (f t) ^ 2 * g t) E) (hgint : IntegrableOn g E)
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    {V₀ M : ℝ} (hV₀ : 0 < V₀) (hM : ∀ t, f t ≤ M) {J : ℕ} (hJ : M ≤ 2 ^ J * V₀) :
    (∫ t in E, (f t) ^ 2 * g t)
      ≤ V₀ ^ 2 * (∫ t in E, g t)
        + ∑ j ∈ Finset.range J,
            (2 ^ (j + 1) * V₀) ^ 2 * (∫ t in E ∩ {t | 2 ^ j * V₀ ≤ f t}, g t) := by
  classical
  have hmeasSet : ∀ j : ℕ, MeasurableSet {t : ℝ | 2 ^ j * V₀ ≤ f t} := fun j =>
    measurableSet_le measurable_const hmeas
  have hindInt : ∀ j : ℕ,
      IntegrableOn (Set.indicator {t : ℝ | 2 ^ j * V₀ ≤ f t} g) E := fun j =>
    hgint.indicator (hmeasSet j)
  set G : ℝ → ℝ := fun t => V₀ ^ 2 * g t
    + ∑ j ∈ Finset.range J,
        (2 ^ (j + 1) * V₀) ^ 2 * Set.indicator {t | 2 ^ j * V₀ ≤ f t} g t with hG
  have hsumInt : IntegrableOn (fun t => ∑ j ∈ Finset.range J,
      (2 ^ (j + 1) * V₀) ^ 2 * Set.indicator {t | 2 ^ j * V₀ ≤ f t} g t) E :=
    integrable_finsetSum _ fun j _ => (hindInt j).const_mul _
  have hGint : IntegrableOn G E := (hgint.const_mul _).add hsumInt
  have hpt : ∀ t ∈ E, (f t) ^ 2 * g t ≤ G t := by
    intro t _
    have hbase := sq_le_levelSplit (V₀ := V₀) (M := M) (x := f t) hV₀ (hf0 t) (hM t) hJ
    have hmul := mul_le_mul_of_nonneg_right hbase (hg0 t)
    refine le_trans hmul (le_of_eq ?_)
    rw [hG, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 2 ^ j * V₀ ≤ f t
    · rw [if_pos hc,
        Set.indicator_of_mem (show t ∈ {t : ℝ | 2 ^ j * V₀ ≤ f t} from hc) g]
      ring
    · rw [if_neg hc,
        Set.indicator_of_notMem (show t ∉ {t : ℝ | 2 ^ j * V₀ ≤ f t} from hc) g]
      ring
  refine le_trans (setIntegral_mono_on hint hGint hE hpt) (le_of_eq ?_)
  rw [hG, integral_add (hgint.const_mul _) hsumInt, integral_const_mul,
    integral_finsetSum _ (fun j _ => (hindInt j).const_mul _)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_indicator (hmeasSet j), Measure.restrict_restrict (hmeasSet j)]
  rw [Set.inter_comm]

end

end RHTower.Sieve
