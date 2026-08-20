import GaloisForLFunctions.HTGeometry.KolmogorovMaximalInequality

/-!
# Kolmogorov's lower inequality and the divergence half of the three-series theorem

For a countable product of probability spaces and a series whose `n`-th term reads only the `n`-th
coordinate, with every term centred and uniformly bounded by `C`, the probability that all partial
sums up to `N` stay below `lam` is controlled by the accumulated variance:

```text
( ∑_{n < N} E‖g n‖² ) · P( ∀ n ≤ N, ‖S n‖ < lam )  ≤  (lam + C)² .
```

This is the converse companion of `kolmogorov_maximal_inequality`.  Where the maximal inequality
upgrades summable variance to almost sure convergence, this one turns divergent variance into
almost sure divergence: the partial sums leave every ball almost surely, so the series cannot
converge.  Together the two give the exact dichotomy of Kolmogorov's three-series theorem for
uniformly bounded centred coordinate series.

The proof is the classical stopped second-moment recursion.  Write `B n` for the event that the
partial sums stay below `lam` through index `n`.  On `B n` the increment `g n` is independent of
the past, so

```text
∫_{B n} ‖S (n+1)‖² = ∫_{B n} ‖S n‖² + E‖g n‖² · P(B n),
```

while the part of `B n` lost at step `n` carries `‖S (n+1)‖ < lam + C`.  Telescoping and using
`∫_{B N} ‖S N‖² ≤ lam² P(B N)` gives the displayed bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

variable (g : ∀ n, X n → ℂ)

/-! ### The stopped event -/

/-- The event that every partial sum up to index `n` stays strictly below `lam`. -/
def stayBelow (lam : ℝ) (n : ℕ) : Set (∀ m, X m) :=
  {x | ∀ k ≤ n, ‖coordPartialSum g k x‖ < lam}

theorem measurableSet_stayBelow (hg : ∀ n, Measurable (g n)) (lam : ℝ) (n : ℕ) :
    MeasurableSet (stayBelow g lam n) := by
  have hmeas : ∀ k : ℕ, Measurable fun x : ∀ m, X m => ‖coordPartialSum g k x‖ :=
    fun k => (measurable_coordPartialSum g hg k).norm
  have hsplit : stayBelow g lam n
      = ⋂ (k : ℕ), ⋂ (_ : k ≤ n), {x : ∀ m, X m | ‖coordPartialSum g k x‖ < lam} := by
    ext x; simp [stayBelow]
  rw [hsplit]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_lt (hmeas k) measurable_const

omit [∀ n, MeasurableSpace (X n)] in
theorem stayBelow_subset (lam : ℝ) {m n : ℕ} (h : m ≤ n) :
    stayBelow g lam n ⊆ stayBelow g lam m :=
  fun _ hx k hk => hx k (hk.trans h)

omit [∀ n, MeasurableSpace (X n)] in
/-- The stopped event through index `n` reads only the coordinates below `n`. -/
theorem stayBelow_blockExtend (a : ∀ m, X m) (lam : ℝ) (n : ℕ) (x : ∀ m, X m) :
    (blockExtend a (Finset.range n) ((Finset.range n).restrict x) ∈ stayBelow g lam n)
      ↔ x ∈ stayBelow g lam n := by
  simp only [stayBelow, Set.mem_setOf_eq]
  constructor
  · intro h k hk
    rw [← coordPartialSum_blockExtend_le g a hk x]; exact h k hk
  · intro h k hk
    rw [coordPartialSum_blockExtend_le g a hk x]; exact h k hk

/-! ### The two independence identities at one step -/

variable (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]

/-- **The one-step variance identity.**  A set reading only the coordinates below `n` is
independent of the `n`-th term, so the second moment of that term over the set factors. -/
theorem setIntegral_normSq_coordTerm (a : ∀ m, X m) (hg : ∀ n, Measurable (g n))
    {A : Set (∀ m, X m)} (n : ℕ) (hA : MeasurableSet A)
    (hAblock : ∀ x, (blockExtend a (Finset.range n) ((Finset.range n).restrict x) ∈ A) ↔ x ∈ A) :
    ∫ x in A, ‖g n (x n)‖ ^ 2 ∂(Measure.infinitePi μ)
      = (Measure.infinitePi μ A).toReal * ∫ y, ‖g n y‖ ^ 2 ∂(μ n) := by
  classical
  set ν := Measure.infinitePi μ with hν
  set h : ∀ m, X m → ℂ := fun m y => ((‖g m y‖ ^ 2 : ℝ) : ℂ) with hh
  have hhmeas : ∀ m, Measurable (h m) :=
    fun m => Complex.measurable_ofReal.comp ((hg m).norm.pow_const 2)
  set U : (∀ m, X m) → ℂ := A.indicator (fun _ => (1 : ℂ)) with hU
  set V : (∀ m, X m) → ℂ := fun x => h n (x n) with hV
  have hUmeas : Measurable U := measurable_const.indicator hA
  have hVmeas : Measurable V := (hhmeas n).comp (measurable_pi_apply n)
  have hUblock : ∀ x, U (blockExtend a (Finset.range n) ((Finset.range n).restrict x)) = U x := by
    intro x
    by_cases hx : x ∈ A
    · rw [hU, Set.indicator_of_mem ((hAblock x).mpr hx), Set.indicator_of_mem hx]
    · rw [hU, Set.indicator_of_notMem (fun hmem => hx ((hAblock x).mp hmem)),
        Set.indicator_of_notMem hx]
  have hVblock : ∀ x,
      V (blockExtend a (Finset.Ico n (n + 1)) ((Finset.Ico n (n + 1)).restrict x)) = V x := by
    intro x
    simp [hV, blockExtend, Finset.restrict]
  have hdisj : Disjoint (Finset.range n) (Finset.Ico n (n + 1)) := by
    refine Finset.disjoint_left.mpr fun k hk hk' => ?_
    exact absurd (Finset.mem_range.mp hk) (not_lt.mpr (Finset.mem_Ico.mp hk').1)
  have hindep : IndepFun U V ν :=
    indepFun_of_blockDependence μ a hdisj hUmeas hVmeas hUblock hVblock
  have hmul := hindep.integral_fun_mul_eq_mul_integral hUmeas.aestronglyMeasurable
    hVmeas.aestronglyMeasurable
  have hUV : (fun x => U x * V x) = A.indicator V := by
    funext x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hU, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, hU, Set.indicator_of_notMem hx, zero_mul]
  have hUint : ∫ x, U x ∂ν = ((ν A).toReal : ℂ) := by
    rw [hU, integral_indicator_const (1 : ℂ) hA]
    simp [measureReal_def]
  have hVint : ∫ x, V x ∂ν = ((∫ y, ‖g n y‖ ^ 2 ∂(μ n) : ℝ) : ℂ) := by
    rw [hV, integral_coordTerm h μ hhmeas n, hh]
    exact integral_ofReal
  have hleft : ∫ x, U x * V x ∂ν = ((∫ x in A, ‖g n (x n)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [hUV, integral_indicator hA, hV, hh]
    exact integral_ofReal
  rw [hleft, hUint, hVint] at hmul
  exact_mod_cast hmul

/-- **The one-step cross term vanishes.**  A set reading only the coordinates below `n`, times the
past partial sum, is independent of the centred `n`-th term. -/
theorem setIntegral_crossStep_eq_zero (a : ∀ m, X m) (hg : ∀ n, Measurable (g n))
    (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0)
    {A : Set (∀ m, X m)} (n : ℕ) (hA : MeasurableSet A)
    (hAblock : ∀ x, (blockExtend a (Finset.range n) ((Finset.range n).restrict x) ∈ A) ↔ x ∈ A) :
    ∫ x in A, ((starRingEnd ℂ) (coordPartialSum g n x) * g n (x n)) ∂(Measure.infinitePi μ)
      = 0 := by
  classical
  set ν := Measure.infinitePi μ with hν
  set U : (∀ m, X m) → ℂ := A.indicator (fun x => (starRingEnd ℂ) (coordPartialSum g n x)) with hU
  set V : (∀ m, X m) → ℂ := fun x => g n (x n) with hV
  have hUmeas : Measurable U :=
    Measurable.indicator (continuous_star.measurable.comp (measurable_coordPartialSum g hg n)) hA
  have hVmeas : Measurable V := (hg n).comp (measurable_pi_apply n)
  have hUblock : ∀ x, U (blockExtend a (Finset.range n) ((Finset.range n).restrict x)) = U x := by
    intro x
    by_cases hx : x ∈ A
    · rw [hU, Set.indicator_of_mem ((hAblock x).mpr hx), Set.indicator_of_mem hx,
        coordPartialSum_blockExtend_le g a (le_refl n) x]
    · rw [hU, Set.indicator_of_notMem (fun hmem => hx ((hAblock x).mp hmem)),
        Set.indicator_of_notMem hx]
  have hVblock : ∀ x,
      V (blockExtend a (Finset.Ico n (n + 1)) ((Finset.Ico n (n + 1)).restrict x)) = V x := by
    intro x
    simp [hV, blockExtend, Finset.restrict]
  have hdisj : Disjoint (Finset.range n) (Finset.Ico n (n + 1)) := by
    refine Finset.disjoint_left.mpr fun k hk hk' => ?_
    exact absurd (Finset.mem_range.mp hk) (not_lt.mpr (Finset.mem_Ico.mp hk').1)
  have hindep : IndepFun U V ν :=
    indepFun_of_blockDependence μ a hdisj hUmeas hVmeas hUblock hVblock
  have hmul := hindep.integral_fun_mul_eq_mul_integral hUmeas.aestronglyMeasurable
    hVmeas.aestronglyMeasurable
  have hUV : (fun x => U x * V x)
      = A.indicator fun x => (starRingEnd ℂ) (coordPartialSum g n x) * V x := by
    funext x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hU, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hU, Set.indicator_of_notMem hx, zero_mul]
  have hV0 : ∫ x, V x ∂ν = 0 := by
    rw [hV, integral_coordTerm g μ hg n, hmean n]
  rw [hUV, integral_indicator hA] at hmul
  rw [hmul, hV0, mul_zero]

/-! ### The stopped second-moment recursion -/

variable {c : ℕ → ℝ}

/-- **One step of the stopped second-moment recursion.**  The increment adds its full variance on
the surviving event and loses at most `(lam + C)²` per unit of probability that exits. -/
theorem stopped_secondMoment_step (a : ∀ m, X m) (hg : ∀ n, Measurable (g n))
    (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0)
    {C lam : ℝ} (hcC : ∀ n, c n ≤ C) (n : ℕ) :
    (∫ x in stayBelow g lam n, ‖coordPartialSum g n x‖ ^ 2 ∂(Measure.infinitePi μ))
        + (Measure.infinitePi μ (stayBelow g lam n)).toReal * (∫ y, ‖g n y‖ ^ 2 ∂(μ n))
        - (lam + C) ^ 2 * (Measure.infinitePi μ (stayBelow g lam n)).toReal
        + (lam + C) ^ 2 * (Measure.infinitePi μ (stayBelow g lam (n + 1))).toReal
      ≤ ∫ x in stayBelow g lam (n + 1), ‖coordPartialSum g (n + 1) x‖ ^ 2
          ∂(Measure.infinitePi μ) := by
  classical
  set ν := Measure.infinitePi μ with hν
  set S := fun k => coordPartialSum (X := X) g k with hS
  have hSmeas : ∀ k, Measurable (S k) := fun k => measurable_coordPartialSum g hg k
  have hSbound : ∀ k x, ‖S k x‖ ≤ ∑ j ∈ Finset.range k, c j := fun k =>
    norm_coordPartialSum_le g hbdd k
  set A := stayBelow g lam n with hA
  set A' := stayBelow g lam (n + 1) with hA'
  have hAmeas : MeasurableSet A := measurableSet_stayBelow g hg lam n
  have hA'meas : MeasurableSet A' := measurableSet_stayBelow g hg lam (n + 1)
  have hsub : A' ⊆ A := stayBelow_subset g lam (Nat.le_succ n)
  have hstep : ∀ x : ∀ m, X m, S (n + 1) x = S n x + g n (x n) := by
    intro x
    simp [hS, coordPartialSum, Finset.sum_range_succ]
  have hdec : ∀ x : ∀ m, X m, ‖S (n + 1) x‖ ^ 2
      = ‖S n x‖ ^ 2 + 2 * ((starRingEnd ℂ) (S n x) * g n (x n)).re + ‖g n (x n)‖ ^ 2 := by
    intro x
    rw [hstep x]
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsq : ∀ k, Integrable (fun x => ‖S k x‖ ^ 2) ν := by
    intro k
    refine integrable_of_norm_le_real μ ((hSmeas k).norm.pow_const 2)
      (C := (∑ j ∈ Finset.range k, c j) ^ 2) fun x => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hSbound k x) 2
  have hgsq : Integrable (fun x : ∀ m, X m => ‖g n (x n)‖ ^ 2) ν := by
    refine integrable_of_norm_le_real μ
      (((hg n).comp (measurable_pi_apply n)).norm.pow_const 2) (C := (c n) ^ 2) fun x => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbdd n (x n)) 2
  have hcrossI : Integrable (fun x : ∀ m, X m =>
      (starRingEnd ℂ) (S n x) * g n (x n)) ν := by
    refine integrable_of_norm_le μ ((continuous_star.measurable.comp (hSmeas n)).mul
      ((hg n).comp (measurable_pi_apply n)))
      (C := (∑ j ∈ Finset.range n, c j) * c n) fun x => ?_
    rw [norm_mul, RCLike.norm_conj]
    have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, c j := le_trans (norm_nonneg (S n x)) (hSbound n x)
    exact mul_le_mul (hSbound n x) (hbdd n (x n)) (norm_nonneg _) hnn
  have hcrossR : Integrable (fun x : ∀ m, X m =>
      2 * ((starRingEnd ℂ) (S n x) * g n (x n)).re) ν := by
    refine integrable_of_norm_le_real μ
      ((Complex.measurable_re.comp ((continuous_star.measurable.comp (hSmeas n)).mul
        ((hg n).comp (measurable_pi_apply n)))).const_mul 2)
      (C := 2 * ((∑ j ∈ Finset.range n, c j) * c n)) fun x => ?_
    have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, c j := le_trans (norm_nonneg (S n x)) (hSbound n x)
    have hre : |((starRingEnd ℂ) (S n x) * g n (x n)).re|
        ≤ ‖(starRingEnd ℂ) (S n x)‖ * ‖g n (x n)‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul]
    have hb : ‖(starRingEnd ℂ) (S n x)‖ * ‖g n (x n)‖
        ≤ (∑ j ∈ Finset.range n, c j) * c n := by
      rw [RCLike.norm_conj]
      exact mul_le_mul (hSbound n x) (hbdd n (x n)) (norm_nonneg _) hnn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hsplitA : ∫ x in A, ‖S (n + 1) x‖ ^ 2 ∂ν
      = (∫ x in A, ‖S n x‖ ^ 2 ∂ν)
        + (∫ x in A, 2 * ((starRingEnd ℂ) (S n x) * g n (x n)).re ∂ν)
        + ∫ x in A, ‖g n (x n)‖ ^ 2 ∂ν := by
    have e1 : ∫ x in A, ‖S (n + 1) x‖ ^ 2 ∂ν
        = ∫ x in A, ((‖S n x‖ ^ 2 + 2 * ((starRingEnd ℂ) (S n x) * g n (x n)).re)
            + ‖g n (x n)‖ ^ 2) ∂ν :=
      setIntegral_congr_fun hAmeas fun x _ => hdec x
    rw [e1, integral_add
      (f := fun x => ‖S n x‖ ^ 2 + 2 * ((starRingEnd ℂ) (S n x) * g n (x n)).re)
      (g := fun x => ‖g n (x n)‖ ^ 2) ((hsq n).restrict.add hcrossR.restrict) hgsq.restrict,
      integral_add (f := fun x => ‖S n x‖ ^ 2)
      (g := fun x => 2 * ((starRingEnd ℂ) (S n x) * g n (x n)).re)
      (hsq n).restrict hcrossR.restrict]
  have hcross0 : ∫ x in A, 2 * ((starRingEnd ℂ) (S n x) * g n (x n)).re ∂ν = 0 := by
    rw [integral_const_mul]
    have hre : ∫ x in A, ((starRingEnd ℂ) (S n x) * g n (x n)).re ∂ν
        = (∫ x in A, ((starRingEnd ℂ) (S n x) * g n (x n)) ∂ν).re := by
      have h := integral_re (𝕜 := ℂ) (hcrossI.restrict (s := A))
      simpa using h
    rw [hre, setIntegral_crossStep_eq_zero g μ a hg hmean n hAmeas
      (stayBelow_blockExtend g a lam n)]
    simp
  have hvar : ∫ x in A, ‖g n (x n)‖ ^ 2 ∂ν
      = (ν A).toReal * ∫ y, ‖g n y‖ ^ 2 ∂(μ n) :=
    setIntegral_normSq_coordTerm g μ a hg n hAmeas (stayBelow_blockExtend g a lam n)
  have hunion : A' ∪ (A \ A') = A := Set.union_sdiff_cancel hsub
  have hdisjset : Disjoint A' (A \ A') := Set.disjoint_sdiff_right
  have hsplit2 : ∫ x in A, ‖S (n + 1) x‖ ^ 2 ∂ν
      = (∫ x in A', ‖S (n + 1) x‖ ^ 2 ∂ν) + ∫ x in A \ A', ‖S (n + 1) x‖ ^ 2 ∂ν := by
    have h := setIntegral_union (μ := ν) (f := fun x => ‖S (n + 1) x‖ ^ 2) hdisjset
      (hAmeas.diff hA'meas) (hsq (n + 1)).restrict (hsq (n + 1)).restrict
    rwa [hunion] at h
  have hexit : ∫ x in A \ A', ‖S (n + 1) x‖ ^ 2 ∂ν
      ≤ (lam + C) ^ 2 * (ν A).toReal - (lam + C) ^ 2 * (ν A').toReal := by
    have hbound : ∀ x ∈ A \ A', ‖S (n + 1) x‖ ^ 2 ≤ (lam + C) ^ 2 := by
      intro x hx
      have h1 : ‖S n x‖ < lam := hx.1 n (le_refl n)
      have h2 : ‖g n (x n)‖ ≤ C := le_trans (hbdd n (x n)) (hcC n)
      have h3 : ‖S (n + 1) x‖ ≤ ‖S n x‖ + ‖g n (x n)‖ := by
        rw [hstep x]; exact norm_add_le _ _
      have h4 : ‖S (n + 1) x‖ ≤ lam + C := by linarith
      exact pow_le_pow_left₀ (norm_nonneg _) h4 2
    have hmono : ∫ x in A \ A', ‖S (n + 1) x‖ ^ 2 ∂ν
        ≤ ∫ _x in A \ A', (lam + C) ^ 2 ∂ν :=
      setIntegral_mono_on (hsq (n + 1)).restrict
        (integrableOn_const (C := (lam + C) ^ 2) (by exact measure_ne_top ν _))
        (hAmeas.diff hA'meas) hbound
    have hconst : ∫ _x in A \ A', (lam + C) ^ 2 ∂ν
        = (ν (A \ A')).toReal * (lam + C) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
    have hdiff : (ν (A \ A')).toReal = (ν A).toReal - (ν A').toReal := by
      rw [measure_sdiff hsub hA'meas.nullMeasurableSet (measure_ne_top ν _),
        ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top ν _)]
    rw [hconst, hdiff] at hmono
    calc ∫ x in A \ A', ‖S (n + 1) x‖ ^ 2 ∂ν
        ≤ ((ν A).toReal - (ν A').toReal) * (lam + C) ^ 2 := hmono
      _ = (lam + C) ^ 2 * (ν A).toReal - (lam + C) ^ 2 * (ν A').toReal := by ring
  rw [hsplitA, hcross0, hvar] at hsplit2
  linarith

/-! ### Kolmogorov's lower inequality -/

/-- **Kolmogorov's lower inequality.**  For a centred coordinatewise series with terms uniformly
bounded by `C`, the accumulated variance times the probability of staying below `lam` through
index `N` is at most `(lam + C)²`. -/
theorem kolmogorov_lower_inequality (a : ∀ m, X m) (hg : ∀ n, Measurable (g n))
    (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0)
    {C lam : ℝ} (hcC : ∀ n, c n ≤ C) (hlam : 0 < lam) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n))
        * (Measure.infinitePi μ (stayBelow g lam N)).toReal ≤ (lam + C) ^ 2 := by
  classical
  set ν := Measure.infinitePi μ with hν
  set S := fun k => coordPartialSum (X := X) g k with hS
  set F : ℕ → ℝ := fun k => ∫ x in stayBelow g lam k, ‖S k x‖ ^ 2 ∂ν with hF
  set P : ℕ → ℝ := fun k => (ν (stayBelow g lam k)).toReal with hP
  set V : ℕ → ℝ := fun k => ∫ y, ‖g k y‖ ^ 2 ∂(μ k) with hV
  have hC0 : 0 ≤ C := by
    have hne : Nonempty (X 0) := by
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      have h1 : (μ 0) Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.mpr hemp, measure_empty] at h1
      exact zero_ne_one h1
    obtain ⟨y⟩ := hne
    exact le_trans (norm_nonneg (g 0 y)) (le_trans (hbdd 0 y) (hcC 0))
  have hVnn : ∀ k, 0 ≤ V k := fun k => integral_nonneg fun y => by positivity
  have hPnn : ∀ k, 0 ≤ P k := fun _ => ENNReal.toReal_nonneg
  have hPanti : ∀ {i j : ℕ}, i ≤ j → P j ≤ P i := by
    intro i j hij
    exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (stayBelow_subset g lam hij))
  have hP0 : P 0 ≤ 1 := by
    have hle : ν (stayBelow g lam 0) ≤ 1 := by
      calc ν (stayBelow g lam 0) ≤ ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
  have hF0 : F 0 = 0 := by
    have hzero : ∀ x : ∀ m, X m, ‖S 0 x‖ ^ 2 = 0 := by
      intro x; simp [hS, coordPartialSum]
    show (∫ x in stayBelow g lam 0, ‖S 0 x‖ ^ 2 ∂ν) = 0
    simp [hzero]
  have hrec : ∀ n : ℕ, ∑ k ∈ Finset.range n, P k * V k
      ≤ F n + (lam + C) ^ 2 * P 0 - (lam + C) ^ 2 * P n := by
    intro n
    induction n with
    | zero => simp [hF0]
    | succ m ih =>
        have h1 : F m + P m * V m - (lam + C) ^ 2 * P m + (lam + C) ^ 2 * P (m + 1) ≤ F (m + 1) :=
          stopped_secondMoment_step g μ a hg hbdd hmean hcC (lam := lam) m
        rw [Finset.sum_range_succ]
        linarith
  have hFle : F N ≤ lam ^ 2 * P N := by
    have hsqint : Integrable (fun x => ‖S N x‖ ^ 2) ν := by
      refine integrable_of_norm_le_real μ
        ((measurable_coordPartialSum g hg N).norm.pow_const 2)
        (C := (∑ j ∈ Finset.range N, c j) ^ 2) fun x => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_coordPartialSum_le g hbdd N x) 2
    have hmono : ∫ x in stayBelow g lam N, ‖S N x‖ ^ 2 ∂ν
        ≤ ∫ _x in stayBelow g lam N, lam ^ 2 ∂ν := by
      refine setIntegral_mono_on hsqint.restrict
        (integrableOn_const (C := lam ^ 2) (by exact measure_ne_top ν _))
        (measurableSet_stayBelow g hg lam N) fun x hx => ?_
      have h1 : ‖S N x‖ < lam := hx N (le_refl N)
      nlinarith [norm_nonneg (S N x)]
    have hconst : ∫ _x in stayBelow g lam N, lam ^ 2 ∂ν
        = (ν (stayBelow g lam N)).toReal * lam ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
    rw [hconst] at hmono
    show (∫ x in stayBelow g lam N, ‖S N x‖ ^ 2 ∂ν) ≤ lam ^ 2 * (ν (stayBelow g lam N)).toReal
    linarith
  have hsum : (∑ n ∈ Finset.range N, V n) * P N ≤ ∑ k ∈ Finset.range N, P k * V k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkN : k ≤ N := le_of_lt (Finset.mem_range.mp hk)
    calc V k * P N ≤ V k * P k := mul_le_mul_of_nonneg_left (hPanti hkN) (hVnn k)
      _ = P k * V k := mul_comm _ _
  have hlamC : lam ^ 2 ≤ (lam + C) ^ 2 := by nlinarith
  have hA1 : lam ^ 2 * P N ≤ (lam + C) ^ 2 * P N := mul_le_mul_of_nonneg_right hlamC (hPnn N)
  have hA2 : (lam + C) ^ 2 * P 0 ≤ (lam + C) ^ 2 := by nlinarith [sq_nonneg (lam + C), hPnn 0]
  have hfin := hrec N
  show (∑ n ∈ Finset.range N, V n) * P N ≤ (lam + C) ^ 2
  linarith

/-! ### The divergence half of the three-series theorem -/

/-- **Divergent variance forces almost sure divergence.**  For a centred coordinatewise series
with uniformly bounded terms, if the accumulated variance tends to infinity then the series
diverges almost everywhere. -/
theorem measure_coordSeriesConverges_eq_zero_of_variance_atTop
    (a : ∀ m, X m) (hg : ∀ n, Measurable (g n))
    (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0)
    {C : ℝ} (hcC : ∀ n, c n ≤ C)
    (hdiv : Tendsto (fun N => ∑ n ∈ Finset.range N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n)) atTop atTop) :
    Measure.infinitePi μ (coordSeriesConverges g) = 0 := by
  classical
  set ν := Measure.infinitePi μ with hν
  have hVnn : ∀ N : ℕ, (0 : ℝ) ≤ ∑ n ∈ Finset.range N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n) :=
    fun N => Finset.sum_nonneg fun n _ => integral_nonneg fun y => by positivity
  have hnull : ∀ j : ℕ, ν (⋂ N : ℕ, stayBelow g ((j : ℝ) + 1) N) = 0 := by
    intro j
    set lam : ℝ := (j : ℝ) + 1 with hlamdef
    have hlam : 0 < lam := by positivity
    set T := ⋂ N : ℕ, stayBelow g lam N with hT
    have hTle : ∀ N, (ν T).toReal ≤ (ν (stayBelow g lam N)).toReal := fun N =>
      ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Set.iInter_subset _ N))
    have hzero : (ν T).toReal ≤ 0 := by
      by_contra hpos
      rw [not_le] at hpos
      obtain ⟨N, hN⟩ := (hdiv.eventually_ge_atTop
        (((lam + C) ^ 2 + 1) / (ν T).toReal)).exists
      have hkey := kolmogorov_lower_inequality g μ a hg hbdd hmean hcC hlam N
      have h2 : (lam + C) ^ 2 + 1 ≤ (∑ n ∈ Finset.range N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n))
          * (ν T).toReal := by
        rw [div_le_iff₀ hpos] at hN
        linarith
      have h3 : (∑ n ∈ Finset.range N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n)) * (ν T).toReal
          ≤ (∑ n ∈ Finset.range N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n))
            * (ν (stayBelow g lam N)).toReal :=
        mul_le_mul_of_nonneg_left (hTle N) (hVnn N)
      linarith
    have hz : (ν T).toReal = 0 := le_antisymm hzero ENNReal.toReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top ν _)
  have hsub : coordSeriesConverges g ⊆ ⋃ j : ℕ, ⋂ N : ℕ, stayBelow g ((j : ℝ) + 1) N := by
    intro x hx
    obtain ⟨L, hL⟩ := hx
    obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le).1 hL.cauchySeq.isBounded_range
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine Set.mem_iUnion.mpr ⟨j, Set.mem_iInter.mpr fun N => ?_⟩
    intro k _
    have hk : ‖coordPartialSum g k x‖ ≤ M := hM _ (Set.mem_range_self k)
    linarith
  exact measure_mono_null hsub (measure_iUnion_null hnull)

end GaloisForLFunctions.HTGeometry
