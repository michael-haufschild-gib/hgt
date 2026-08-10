import GaloisForLFunctions.RHTower.BeurlingSystemZetaSeries

/-!
# Partial summation over generalized primes

The generalized primes of a discrete Beurling system inject into its generalized integers, so the
prime counting function `π_P(X) = #{p : |p| ≤ X}` is finite and monotone.

For a differentiable weight the Abel identity

```text
∑_{Y < |p| ≤ X} f(|p|) = π_P(X) f(X) - π_P(Y) f(Y) - ∫_Y^X f'(t) π_P(t) dt
```

converts a prime sum into the counting function.  The proof writes `f(|p|) - f(Y)` as the integral
of `f'` against the indicator of `{t ≤ |p|}`, exchanges the finite sum with the integral, and
identifies the resulting weight with `π_P(X) - π_P(t)`; the strict and non-strict counting
functions differ only on the finite set of prime norms below `X`, which is null.
-/

open scoped BigOperators
open Filter Topology MeasureTheory Set

namespace RHTower

namespace BeurlingSystem

variable (B : BeurlingSystem)

/-- The prime counting function of a Beurling system. -/
noncomputable def primeCount (X : ℝ) : ℕ := Set.ncard {p : B.Label | B.labelNorm p ≤ X}

/-- The strict prime counting function of a Beurling system. -/
noncomputable def primeCountLt (X : ℝ) : ℕ := Set.ncard {p : B.Label | B.labelNorm p < X}

/-- The generalized prime number theorem: `π_P(X) log X / X → 1`. -/
def HasPrimePNT : Prop :=
  Tendsto (fun X : ℝ => (B.primeCount X : ℝ) * Real.log X / X) atTop (nhds 1)

/-- The labels with norm in `(Y, X]`. -/
def primeWindow (Y X : ℝ) : Set B.Label :=
  {p | Y < B.labelNorm p ∧ B.labelNorm p ≤ X}

variable {B}

theorem singleton_injective : Function.Injective fun p : B.Label => ({p} : Multiset B.Label) :=
  fun _ _ hpq => Multiset.singleton_inj.mp hpq

theorem finite_primeBall (hdisc : B.IsDiscrete) (X : ℝ) :
    {p : B.Label | B.labelNorm p ≤ X}.Finite := by
  have hsub : (fun p : B.Label => ({p} : Multiset B.Label)) ''
      {p : B.Label | B.labelNorm p ≤ X} ⊆ {g : Multiset B.Label | B.intNorm g ≤ X} := by
    rintro g ⟨p, hp, rfl⟩
    rw [Set.mem_setOf_eq, intNorm_singleton]
    exact hp
  exact Set.Finite.of_finite_image ((hdisc X).subset hsub) singleton_injective.injOn

theorem finite_primeBallLt (hdisc : B.IsDiscrete) (X : ℝ) :
    {p : B.Label | B.labelNorm p < X}.Finite := by
  refine (finite_primeBall hdisc X).subset fun p hp => ?_
  simp only [Set.mem_setOf_eq] at hp ⊢
  exact hp.le

theorem finite_primeShell (hdisc : B.IsDiscrete) (t X : ℝ) :
    {p : B.Label | t ≤ B.labelNorm p ∧ B.labelNorm p ≤ X}.Finite :=
  (finite_primeBall hdisc X).subset fun _ hp => hp.2

theorem finite_primeWindow (hdisc : B.IsDiscrete) (Y X : ℝ) :
    (B.primeWindow Y X).Finite :=
  (finite_primeBall hdisc X).subset fun _ hp => hp.2

theorem primeCount_mono (hdisc : B.IsDiscrete) {X Y : ℝ} (hXY : X ≤ Y) :
    B.primeCount X ≤ B.primeCount Y :=
  Set.ncard_le_ncard (fun _ hp => le_trans hp hXY) (finite_primeBall hdisc Y)

theorem primeCountLt_mono (hdisc : B.IsDiscrete) {X Y : ℝ} (hXY : X ≤ Y) :
    B.primeCountLt X ≤ B.primeCountLt Y :=
  Set.ncard_le_ncard (fun _ hp => lt_of_lt_of_le hp hXY) (finite_primeBallLt hdisc Y)

/-- Below one there are no generalized primes. -/
theorem primeCount_eq_zero_of_lt_one {X : ℝ} (hX : X < 1) : B.primeCount X = 0 := by
  rw [primeCount]
  have hempty : {p : B.Label | B.labelNorm p ≤ X} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hX (B.one_lt_labelNorm p).le
  rw [hempty, Set.ncard_empty]

/-- Splitting the ball of radius `X` at an interior height `t`. -/
theorem primeCount_eq_primeCountLt_add (hdisc : B.IsDiscrete) {t X : ℝ} (htX : t ≤ X) :
    B.primeCount X
      = B.primeCountLt t + {p : B.Label | t ≤ B.labelNorm p ∧ B.labelNorm p ≤ X}.ncard := by
  have hdisj : Disjoint {p : B.Label | B.labelNorm p < t}
      {p : B.Label | t ≤ B.labelNorm p ∧ B.labelNorm p ≤ X} := by
    rw [Set.disjoint_left]
    intro p hp hp'
    exact absurd hp'.1 (not_le.mpr hp)
  have hunion : {p : B.Label | B.labelNorm p ≤ X}
      = {p : B.Label | B.labelNorm p < t}
        ∪ {p : B.Label | t ≤ B.labelNorm p ∧ B.labelNorm p ≤ X} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hp
      rcases lt_or_ge (B.labelNorm p) t with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hp⟩
    · rintro (h | ⟨_, h⟩)
      · exact h.le.trans htX
      · exact h
  rw [primeCount, hunion, primeCountLt,
    Set.ncard_union_eq hdisj (finite_primeBallLt hdisc t) (finite_primeShell hdisc t X)]

/-- Splitting the ball of radius `X` at the non-strict height `Y`. -/
theorem primeCount_eq_add_ncard_primeWindow (hdisc : B.IsDiscrete) {Y X : ℝ} (hYX : Y ≤ X) :
    B.primeCount X = B.primeCount Y + (B.primeWindow Y X).ncard := by
  have hdisj : Disjoint {p : B.Label | B.labelNorm p ≤ Y} (B.primeWindow Y X) := by
    rw [Set.disjoint_left]
    intro p hp hp'
    exact absurd hp'.1 (not_lt.mpr hp)
  have hunion : {p : B.Label | B.labelNorm p ≤ X}
      = {p : B.Label | B.labelNorm p ≤ Y} ∪ B.primeWindow Y X := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, primeWindow]
    constructor
    · intro hp
      rcases le_or_gt (B.labelNorm p) Y with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hp⟩
    · rintro (h | ⟨_, h⟩)
      · exact h.trans hYX
      · exact h
  rw [primeCount, hunion, primeCount,
    Set.ncard_union_eq hdisj (finite_primeBall hdisc Y) (finite_primeWindow hdisc Y X)]

/-- The number of labels of `S` whose norm is at least `t`. -/
noncomputable def countGe (S : Finset B.Label) (t : ℝ) : ℝ :=
  ∑ p ∈ S, if t ≤ B.labelNorm p then (1 : ℝ) else 0

theorem countGe_eq_card (S : Finset B.Label) (t : ℝ) :
    countGe S t = ((S.filter fun p => t ≤ B.labelNorm p).card : ℝ) := by
  classical
  simp [countGe]

theorem intervalIntegrable_indicator {g : ℝ → ℝ} {a b : ℝ} {s : Set ℝ}
    (h : IntervalIntegrable g volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator g) volume a b :=
  ⟨h.1.indicator hs, h.2.indicator hs⟩

/-- **Partial summation over a finite family of labels.**  Every weight is recovered from the base
value together with the integral of the derivative against the counting function of the family from
above. -/
theorem sum_labelNorm_weight (S : Finset B.Label) {Y X : ℝ} (hYX : Y ≤ X)
    {f g : ℝ → ℝ} (hderiv : ∀ t ∈ Set.Icc Y X, HasDerivAt f (g t) t)
    (hint : IntervalIntegrable g volume Y X)
    (hmem : ∀ p ∈ S, B.labelNorm p ∈ Set.Icc Y X) :
    ∑ p ∈ S, f (B.labelNorm p)
      = (S.card : ℝ) * f Y + ∫ t in Y..X, g t * countGe S t := by
  have huIcc : Set.uIcc Y X = Set.Icc Y X := Set.uIcc_of_le hYX
  have key : ∀ p ∈ S, (∫ t in Y..X, Set.indicator {x : ℝ | x ≤ B.labelNorm p} g t)
      = f (B.labelNorm p) - f Y := by
    intro p hp
    have hmp : B.labelNorm p ∈ Set.Icc Y X := hmem p hp
    rw [intervalIntegral.integral_indicator hmp]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t ?_) ?_
    · rw [Set.uIcc_of_le hmp.1] at ht
      exact ⟨ht.1, ht.2.trans hmp.2⟩
    · exact hint.mono_set (by
        rw [huIcc, Set.uIcc_of_le hmp.1]
        exact Set.Icc_subset_Icc le_rfl hmp.2)
  have hswap : (∫ t in Y..X, g t * countGe S t)
      = ∑ p ∈ S, ∫ t in Y..X, Set.indicator {x : ℝ | x ≤ B.labelNorm p} g t := by
    rw [← intervalIntegral.integral_finsetSum
      (fun p _ => intervalIntegrable_indicator (s := {x : ℝ | x ≤ B.labelNorm p}) hint
        measurableSet_Iic)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [countGe, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : t ≤ B.labelNorm p
    · rw [Set.indicator_of_mem (show t ∈ {x : ℝ | x ≤ B.labelNorm p} from h) g, if_pos h, mul_one]
    · rw [Set.indicator_of_notMem (show t ∉ {x : ℝ | x ≤ B.labelNorm p} from h) g, if_neg h,
        mul_zero]
  have hsum2 : (∑ p ∈ S, ∫ t in Y..X, Set.indicator {x : ℝ | x ≤ B.labelNorm p} g t)
      = ∑ p ∈ S, (f (B.labelNorm p) - f Y) := Finset.sum_congr rfl key
  rw [hswap, hsum2, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- On the window the counting function from above is the difference of the two counting
functions. -/
theorem countGe_primeWindow (hdisc : B.IsDiscrete) {Y X t : ℝ} (hYt : Y < t) (htX : t ≤ X) :
    countGe (finite_primeWindow hdisc Y X).toFinset t
      = (B.primeCount X : ℝ) - (B.primeCountLt t : ℝ) := by
  classical
  have hfilter : ((finite_primeWindow hdisc Y X).toFinset.filter fun p => t ≤ B.labelNorm p)
      = (finite_primeShell hdisc t X).toFinset := by
    ext p
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, primeWindow]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hYt.trans_le h1, h2⟩, h1⟩
  have hncard : {p : B.Label | t ≤ B.labelNorm p ∧ B.labelNorm p ≤ X}.ncard
      = (finite_primeShell hdisc t X).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (finite_primeShell hdisc t X)
  have hsplit := primeCount_eq_primeCountLt_add hdisc htX
  rw [countGe_eq_card, hfilter, hsplit, hncard]
  push_cast
  ring

/-- The two counting functions differ only on the set of prime norms below `X`. -/
theorem primeCountLt_eq_primeCount_of_notMem {t X : ℝ} (htX : t ≤ X)
    (ht : t ∉ B.labelNorm '' {p : B.Label | B.labelNorm p ≤ X}) :
    B.primeCountLt t = B.primeCount t := by
  have hset : {p : B.Label | B.labelNorm p < t} = {p : B.Label | B.labelNorm p ≤ t} := by
    ext p
    simp only [Set.mem_setOf_eq]
    refine ⟨fun h => h.le, fun h => lt_of_le_of_ne h fun hEq => ?_⟩
    exact ht ⟨p, by simp only [Set.mem_setOf_eq]; exact hEq ▸ htX, hEq⟩
  rw [primeCountLt, primeCount, hset]

theorem monotone_primeCount (hdisc : B.IsDiscrete) :
    Monotone fun t : ℝ => (B.primeCount t : ℝ) :=
  fun _ _ hxy => Nat.cast_le.mpr (primeCount_mono hdisc hxy)

theorem monotone_primeCountLt (hdisc : B.IsDiscrete) :
    Monotone fun t : ℝ => (B.primeCountLt t : ℝ) :=
  fun _ _ hxy => Nat.cast_le.mpr (primeCountLt_mono hdisc hxy)

/-- A bounded measurable multiplier preserves interval integrability. -/
theorem intervalIntegrable_mul_of_bounded {Y X : ℝ} (hYX : Y ≤ X) {g h : ℝ → ℝ} {c : ℝ}
    (hint : IntervalIntegrable g volume Y X) (hmeas : Measurable h)
    (hbd : ∀ t ∈ Set.Ioc Y X, ‖h t‖ ≤ c) :
    IntervalIntegrable (fun t => g t * h t) volume Y X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hYX] at hint ⊢
  exact hint.mul_bdd (c := c) hmeas.aestronglyMeasurable
    (Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioc) hbd)

theorem intervalIntegrable_mul_primeCount (hdisc : B.IsDiscrete) {Y X : ℝ} (hYX : Y ≤ X)
    {g : ℝ → ℝ} (hint : IntervalIntegrable g volume Y X) :
    IntervalIntegrable (fun t => g t * (B.primeCount t : ℝ)) volume Y X :=
  intervalIntegrable_mul_of_bounded hYX hint
    ((monotone_primeCount hdisc).measurable) (c := (B.primeCount X : ℝ))
    fun t ht => by
      rw [Real.norm_natCast]
      exact_mod_cast primeCount_mono hdisc ht.2

theorem intervalIntegrable_mul_primeCountLt (hdisc : B.IsDiscrete) {Y X : ℝ} (hYX : Y ≤ X)
    {g : ℝ → ℝ} (hint : IntervalIntegrable g volume Y X) :
    IntervalIntegrable (fun t => g t * (B.primeCountLt t : ℝ)) volume Y X :=
  intervalIntegrable_mul_of_bounded hYX hint
    ((monotone_primeCountLt hdisc).measurable) (c := (B.primeCountLt X : ℝ))
    fun t ht => by
      rw [Real.norm_natCast]
      exact_mod_cast primeCountLt_mono hdisc ht.2

/-- The strict and non-strict counting functions have the same integral. -/
theorem integral_mul_primeCountLt_eq (hdisc : B.IsDiscrete) {Y X : ℝ} (hYX : Y ≤ X) (g : ℝ → ℝ) :
    (∫ t in Y..X, g t * (B.primeCountLt t : ℝ))
      = ∫ t in Y..X, g t * (B.primeCount t : ℝ) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hN : (B.labelNorm '' {p : B.Label | B.labelNorm p ≤ X}).Finite :=
    (finite_primeBall hdisc X).image _
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∉ B.labelNorm '' {p : B.Label | B.labelNorm p ≤ X} :=
    MeasureTheory.compl_mem_ae_iff.mpr (hN.countable.measure_zero volume)
  filter_upwards [hae] with t ht htmem
  rw [Set.uIoc_of_le hYX] at htmem
  rw [primeCountLt_eq_primeCount_of_notMem htmem.2 ht]

/-- **Abel partial summation over the generalized primes of a window.** -/
theorem sum_primeWindow_eq_sub_sub_integral (hdisc : B.IsDiscrete) {Y X : ℝ} (hYX : Y ≤ X)
    {f g : ℝ → ℝ} (hderiv : ∀ t ∈ Set.Icc Y X, HasDerivAt f (g t) t)
    (hint : IntervalIntegrable g volume Y X) :
    ∑ p ∈ (finite_primeWindow hdisc Y X).toFinset, f (B.labelNorm p)
      = (B.primeCount X : ℝ) * f X - (B.primeCount Y : ℝ) * f Y
        - ∫ t in Y..X, g t * (B.primeCount t : ℝ) := by
  have hmem : ∀ p ∈ (finite_primeWindow hdisc Y X).toFinset,
      B.labelNorm p ∈ Set.Icc Y X := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    exact ⟨hp.1.le, hp.2⟩
  have hbase := sum_labelNorm_weight (finite_primeWindow hdisc Y X).toFinset hYX hderiv hint hmem
  have hcard : ((finite_primeWindow hdisc Y X).toFinset.card : ℝ)
      = (B.primeCount X : ℝ) - (B.primeCount Y : ℝ) := by
    have h := primeCount_eq_add_ncard_primeWindow hdisc hYX
    have h2 : (B.primeWindow Y X).ncard = (finite_primeWindow hdisc Y X).toFinset.card :=
      Set.ncard_eq_toFinset_card _ (finite_primeWindow hdisc Y X)
    rw [h2] at h
    have h3 := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at h3
    linarith
  have hcongr : (∫ t in Y..X, g t * countGe (finite_primeWindow hdisc Y X).toFinset t)
      = ∫ t in Y..X, g t * ((B.primeCount X : ℝ) - (B.primeCountLt t : ℝ)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le hYX] at ht
    rw [countGe_primeWindow hdisc ht.1 ht.2]
  have hFTC : (∫ t in Y..X, g t) = f X - f Y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (by rwa [Set.uIcc_of_le hYX] at ht)) hint
  have hsplit : (∫ t in Y..X, g t * ((B.primeCount X : ℝ) - (B.primeCountLt t : ℝ)))
      = (B.primeCount X : ℝ) * (f X - f Y)
        - ∫ t in Y..X, g t * (B.primeCountLt t : ℝ) := by
    have hA : IntervalIntegrable (fun t => g t * (B.primeCount X : ℝ)) volume Y X :=
      hint.mul_const _
    have hB : IntervalIntegrable (fun t => g t * (B.primeCountLt t : ℝ)) volume Y X :=
      intervalIntegrable_mul_primeCountLt hdisc hYX hint
    have hsub : (∫ t in Y..X, (g t * (B.primeCount X : ℝ) - g t * (B.primeCountLt t : ℝ)))
        = (∫ t in Y..X, g t * (B.primeCount X : ℝ))
          - ∫ t in Y..X, g t * (B.primeCountLt t : ℝ) :=
      intervalIntegral.integral_sub hA hB
    rw [show (fun t => g t * ((B.primeCount X : ℝ) - (B.primeCountLt t : ℝ)))
        = fun t => g t * (B.primeCount X : ℝ) - g t * (B.primeCountLt t : ℝ) from
      funext fun t => by ring]
    rw [hsub, intervalIntegral.integral_mul_const, hFTC]
    ring
  rw [hbase, hcongr, hsplit, integral_mul_primeCountLt_eq hdisc hYX, hcard]
  ring

end BeurlingSystem

end RHTower
