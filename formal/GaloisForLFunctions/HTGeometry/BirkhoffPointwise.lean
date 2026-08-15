import GaloisForLFunctions.HTGeometry.MaximalErgodicTheorem

/-!
# Birkhoff's pointwise ergodic theorem

For an ergodic measure-preserving map of a probability space and an integrable observable, the
Birkhoff averages converge almost everywhere to the mean of the observable.

The superlevel sets of the upper limit of the averages are realized as

`⋃ r > a, {x | r n < S_n f x for infinitely many n}`,

which is exactly invariant.  Ergodicity makes each of them null or conull, and the maximal ergodic
theorem pins the resulting threshold to the mean from both sides.
-/

open MeasureTheory Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} {T : α → α} {f : α → ℝ}

/-! ### Frequent excess sets -/

/-- The set where the Birkhoff sums exceed the linear rate `r` infinitely often. -/
def freqAbove (T : α → α) (f : α → ℝ) (r : ℝ) : Set α :=
  ⋂ N : ℕ, ⋃ n ∈ Set.Ici (max N 1), {x | r * n < birkhoffSum T f n x}

theorem mem_freqAbove {r : ℝ} {x : α} :
    x ∈ freqAbove T f r ↔ ∀ N : ℕ, ∃ n, max N 1 ≤ n ∧ r * n < birkhoffSum T f n x := by
  simp [freqAbove, Set.mem_iInter, Set.mem_iUnion, Set.mem_Ici]

/-- The set where the upper limit of the Birkhoff averages exceeds `a`. -/
def limsupGT (T : α → α) (f : α → ℝ) (a : ℝ) : Set α :=
  ⋃ r ∈ {r : ℚ | a < (r : ℝ)}, freqAbove T f (r : ℝ)

theorem mem_limsupGT {a : ℝ} {x : α} :
    x ∈ limsupGT T f a ↔ ∃ r : ℚ, a < (r : ℝ) ∧ x ∈ freqAbove T f (r : ℝ) := by
  simp [limsupGT, Set.mem_iUnion]

theorem limsupGT_mono {a b : ℝ} (hab : a ≤ b) : limsupGT T f b ⊆ limsupGT T f a := by
  intro x hx
  obtain ⟨r, hr, hxr⟩ := mem_limsupGT.1 hx
  exact mem_limsupGT.2 ⟨r, lt_of_le_of_lt hab hr, hxr⟩

/-- The set where some Birkhoff average exceeds `a`. -/
def overSet (T : α → α) (f : α → ℝ) (a : ℝ) : Set α :=
  ⋃ n ∈ Set.Ici 1, {x | a * n < birkhoffSum T f n x}

theorem mem_overSet {a : ℝ} {x : α} :
    x ∈ overSet T f a ↔ ∃ n, 1 ≤ n ∧ a * n < birkhoffSum T f n x := by
  simp [overSet, Set.mem_iUnion, Set.mem_Ici]

theorem limsupGT_subset_overSet {a : ℝ} : limsupGT T f a ⊆ overSet T f a := by
  intro x hx
  obtain ⟨r, hr, hxr⟩ := mem_limsupGT.1 hx
  obtain ⟨n, hn, hlt⟩ := mem_freqAbove.1 hxr 1
  refine mem_overSet.2 ⟨n, le_trans (le_max_right 1 1) hn, ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (le_max_right 1 1) hn
  nlinarith [hlt, hr, hn1]

/-! ### Exact invariance -/

theorem preimage_freqAbove_subset_of_lt {a r : ℝ} (har : a < r) (x : α)
    (hx : x ∈ freqAbove T f r) : T x ∈ freqAbove T f a := by
  refine mem_freqAbove.2 fun N => ?_
  obtain ⟨K, hK⟩ := exists_nat_gt ((f x - a) / (r - a))
  obtain ⟨n, hn, hlt⟩ := mem_freqAbove.1 hx (max (max N 1 + 1) K)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmN : max N 1 ≤ m := by
    have := le_trans (le_max_left (max (max N 1 + 1) K) 1) hn
    have h2 : max N 1 + 1 ≤ m + 1 := le_trans (le_max_left _ _) this
    omega
  have hmK : K ≤ m + 1 := by
    have := le_trans (le_max_left (max (max N 1 + 1) K) 1) hn
    exact le_trans (le_max_right _ _) this
  refine ⟨m, hmN, ?_⟩
  have hsucc : birkhoffSum T f (m + 1) x = f x + birkhoffSum T f m (T x) :=
    birkhoffSum_succ' T f m x
  have hgap : 0 < r - a := sub_pos.2 har
  have hbig : (f x - a) / (r - a) < ((m : ℝ) + 1) := by
    refine lt_of_lt_of_le hK ?_
    exact_mod_cast hmK
  have hbig' : f x - a < (r - a) * ((m : ℝ) + 1) := by
    rw [div_lt_iff₀ hgap] at hbig
    linarith
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hlt
  linarith [hsucc ▸ hlt]

theorem preimage_freqAbove_superset_of_lt {a r : ℝ} (har : a < r) (x : α)
    (hx : T x ∈ freqAbove T f r) : x ∈ freqAbove T f a := by
  refine mem_freqAbove.2 fun N => ?_
  obtain ⟨K, hK⟩ := exists_nat_gt ((a - f x) / (r - a))
  obtain ⟨n, hn, hlt⟩ := mem_freqAbove.1 hx (max N K)
  have hnN : N ≤ n := le_trans (le_trans (le_max_left N K) (le_max_left _ 1)) hn
  have hnK : K ≤ n := le_trans (le_trans (le_max_right N K) (le_max_left _ 1)) hn
  refine ⟨n + 1, by omega, ?_⟩
  have hsucc : birkhoffSum T f (n + 1) x = f x + birkhoffSum T f n (T x) :=
    birkhoffSum_succ' T f n x
  have hgap : 0 < r - a := sub_pos.2 har
  have hbig : (a - f x) / (r - a) < (n : ℝ) := lt_of_lt_of_le hK (by exact_mod_cast hnK)
  have hbig' : a - f x < (r - a) * (n : ℝ) := by
    rw [div_lt_iff₀ hgap] at hbig
    linarith
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, hsucc]
  linarith

theorem preimage_limsupGT (a : ℝ) : T ⁻¹' limsupGT T f a = limsupGT T f a := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hxr⟩ := mem_limsupGT.1 hx
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hr
    exact mem_limsupGT.2 ⟨s, hs1, preimage_freqAbove_superset_of_lt hs2 x hxr⟩
  · intro hx
    obtain ⟨r, hr, hxr⟩ := mem_limsupGT.1 hx
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hr
    exact mem_limsupGT.2 ⟨s, hs1, preimage_freqAbove_subset_of_lt hs2 x hxr⟩

/-! ### The excess set as a limit of maximal sets -/

theorem birkhoffSum_sub_const (a : ℝ) (n : ℕ) (x : α) :
    birkhoffSum T (fun y => f y - a) n x = birkhoffSum T f n x - n * a := by
  simp only [birkhoffSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

theorem maxBirkhoff_pos_iff (g : α → ℝ) (N : ℕ) (x : α) :
    0 < maxBirkhoff T g N x ↔ ∃ n ≤ N, 0 < birkhoffSum T g n x := by
  constructor
  · intro hx
    obtain ⟨n, hn, hEq⟩ := exists_eq_maxBirkhoff T g N x
    exact ⟨n, hn, hEq ▸ hx⟩
  · rintro ⟨n, hn, hpos⟩
    exact lt_of_lt_of_le hpos (birkhoffSum_le_maxBirkhoff T g hn x)

theorem maxBirkhoffPos_eq (a : ℝ) (N : ℕ) :
    {x : α | 0 < maxBirkhoff T (fun y => f y - a) N x}
      = ⋃ n ∈ Set.Icc 1 N, {x : α | a * n < birkhoffSum T f n x} := by
  ext x
  simp only [Set.mem_setOf_eq, maxBirkhoff_pos_iff, Set.mem_iUnion, Set.mem_Icc]
  constructor
  · rintro ⟨n, hn, hpos⟩
    rw [birkhoffSum_sub_const] at hpos
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp [birkhoffSum_zero] at hpos
      · exact h
    exact ⟨n, ⟨hn1, hn⟩, by linarith [hpos]⟩
  · rintro ⟨n, ⟨hn1, hn⟩, hlt⟩
    refine ⟨n, hn, ?_⟩
    rw [birkhoffSum_sub_const]
    linarith

theorem iUnion_maxBirkhoffPos (a : ℝ) :
    ⋃ N : ℕ, {x : α | 0 < maxBirkhoff T (fun y => f y - a) N x} = overSet T f a := by
  ext x
  simp only [Set.mem_iUnion, maxBirkhoffPos_eq, Set.mem_iUnion, Set.mem_Icc, Set.mem_setOf_eq,
    mem_overSet]
  constructor
  · rintro ⟨N, n, ⟨hn1, _⟩, hlt⟩
    exact ⟨n, hn1, hlt⟩
  · rintro ⟨n, hn1, hlt⟩
    exact ⟨n, n, ⟨hn1, le_refl n⟩, hlt⟩

variable [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem measurableSet_freqAbove (hTm : Measurable T) (hfm : Measurable f) (r : ℝ) :
    MeasurableSet (freqAbove T f r) := by
  refine MeasurableSet.iInter fun N => ?_
  refine MeasurableSet.biUnion (Set.to_countable _) fun n _ => ?_
  exact measurableSet_lt measurable_const (measurable_birkhoffSum hTm hfm n)

theorem measurableSet_limsupGT (hTm : Measurable T) (hfm : Measurable f) (a : ℝ) :
    MeasurableSet (limsupGT T f a) :=
  MeasurableSet.biUnion (Set.to_countable _) fun r _ => measurableSet_freqAbove hTm hfm r

theorem measurableSet_overSet (hTm : Measurable T) (hfm : Measurable f) (a : ℝ) :
    MeasurableSet (overSet T f a) := by
  refine MeasurableSet.biUnion (Set.to_countable _) fun n _ => ?_
  exact measurableSet_lt measurable_const (measurable_birkhoffSum hTm hfm n)

/-- **The maximal ergodic theorem in the form of an excess set.** -/
theorem setIntegral_sub_const_nonneg (hT : MeasurePreserving T μ μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) (a : ℝ) :
    0 ≤ ∫ x in overSet T f a, (f x - a) ∂μ := by
  classical
  set g : α → ℝ := fun y => f y - a with hg
  have hgint : Integrable g μ := hf.sub (integrable_const a)
  have hgm : Measurable g := hfm.sub measurable_const
  set s : ℕ → Set α := fun N => {x : α | 0 < maxBirkhoff T g N x} with hs
  have hsmeas : ∀ N, MeasurableSet (s N) := fun N =>
    measurableSet_lt measurable_const (measurable_maxBirkhoff hTm hgm N)
  have hsmono : Monotone s := by
    intro N M hNM x hx
    have hx' : 0 < maxBirkhoff T g N x := hx
    obtain ⟨n, hn, hEq⟩ := exists_eq_maxBirkhoff T g N x
    exact lt_of_lt_of_le (hEq ▸ hx') (birkhoffSum_le_maxBirkhoff T g (hn.trans hNM) x)
  have hunion : ⋃ N, s N = overSet T f a := iUnion_maxBirkhoffPos a
  have hlim := tendsto_setIntegral_of_monotone (f := g) (μ := μ) hsmeas hsmono
    (by rw [hunion]; exact hgint.integrableOn)
  rw [hunion] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards with N
  exact setIntegral_nonneg_of_maxBirkhoff_pos hT hTm hgint hgm N

/-- **The maximal inequality.** -/
theorem measure_overSet_mul_le (hT : MeasurePreserving T μ μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) (a : ℝ) :
    a * μ.real (overSet T f a) ≤ ∫ x, |f x| ∂μ := by
  classical
  have hmeas : MeasurableSet (overSet T f a) := measurableSet_overSet hTm hfm a
  have h0 := setIntegral_sub_const_nonneg hT hTm hf hfm a
  have hsplit : ∫ x in overSet T f a, (f x - a) ∂μ
      = (∫ x in overSet T f a, f x ∂μ) - ∫ _x in overSet T f a, a ∂μ :=
    integral_sub hf.integrableOn (integrable_const a)
  have hconst : ∫ _x in overSet T f a, a ∂μ = μ.real (overSet T f a) * a := by
    rw [setIntegral_const, smul_eq_mul]
  have habs : ∫ x in overSet T f a, f x ∂μ ≤ ∫ x in overSet T f a, |f x| ∂μ :=
    integral_mono hf.integrableOn hf.abs.integrableOn (fun x => le_abs_self (f x))
  have hle : ∫ x in overSet T f a, |f x| ∂μ ≤ ∫ x, |f x| ∂μ :=
    setIntegral_le_integral hf.abs (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
  have := hsplit ▸ h0
  nlinarith [habs, hle, hconst, this]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  {T : α → α} {f : α → ℝ}

theorem measure_limsupGT_eq_zero_or_one (hT : Ergodic T μ) (hTm : Measurable T)
    (hfm : Measurable f) (a : ℝ) :
    μ (limsupGT T f a) = 0 ∨ μ (limsupGT T f a) = 1 :=
  hT.toPreErgodic.prob_eq_zero_or_one (measurableSet_limsupGT hTm hfm a) (preimage_limsupGT a)

omit [MeasurableSpace α] in
/-- Off the upper-limit superlevel set the Birkhoff sums are eventually below every strictly
larger rational rate. -/
theorem exists_eventually_le_of_notMem_limsupGT {a : ℝ} {x : α} (hx : x ∉ limsupGT T f a)
    {r : ℚ} (hr : a < (r : ℝ)) :
    ∃ N : ℕ, ∀ n, N ≤ n → birkhoffSum T f n x ≤ (r : ℝ) * n := by
  have hnot : x ∉ freqAbove T f (r : ℝ) := fun h => hx (mem_limsupGT.2 ⟨r, hr, h⟩)
  rw [mem_freqAbove] at hnot
  push Not at hnot
  obtain ⟨N, hN⟩ := hnot
  exact ⟨max N 1, fun n hn => hN n hn⟩

/-- A level whose superlevel set is conull is at most the mean of the absolute value. -/
theorem le_integral_abs_of_measure_limsupGT_eq_one (hT : Ergodic T μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) {a : ℝ} (ha : μ (limsupGT T f a) = 1) :
    a ≤ ∫ x, |f x| ∂μ := by
  have hsub : μ (limsupGT T f a) ≤ μ (overSet T f a) := measure_mono limsupGT_subset_overSet
  have hle : μ (overSet T f a) ≤ 1 := prob_le_one
  have hone : μ (overSet T f a) = 1 := le_antisymm hle (by rw [← ha]; exact hsub)
  have hreal : μ.real (overSet T f a) = 1 := by
    rw [measureReal_def, hone]; simp
  have := measure_overSet_mul_le hT.toMeasurePreserving hTm hf hfm a
  rw [hreal, mul_one] at this
  exact this

/-- Some level has a conull upper-limit superlevel set. -/
theorem exists_measure_limsupGT_eq_one (hT : Ergodic T μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) :
    ∃ a : ℝ, μ (limsupGT T f a) = 1 := by
  classical
  set K : ℝ := ∫ x, |f x| ∂μ with hK
  set g : α → ℝ := fun y => -f y with hg
  have hgint : Integrable g μ := hf.neg
  have hgm : Measurable g := hfm.neg
  have hKg : ∫ x, |g x| ∂μ = K := by
    simp only [hg, abs_neg, hK]
  have hne : μ (limsupGT T g (K + 1)) ≠ 1 := by
    intro hcon
    have := le_integral_abs_of_measure_limsupGT_eq_one hT hTm hgint hgm hcon
    rw [hKg] at this
    linarith
  have hzero : μ (limsupGT T g (K + 1)) = 0 :=
    (measure_limsupGT_eq_zero_or_one hT hTm hgm (K + 1)).resolve_right hne
  obtain ⟨s, hs⟩ := exists_rat_gt (K + 1)
  refine ⟨((-s - 1 : ℚ) : ℝ), ?_⟩
  set t : ℚ := -s - 1 / 2 with ht
  have hkey : (limsupGT T g (K + 1))ᶜ ⊆ limsupGT T f ((-s - 1 : ℚ) : ℝ) := by
    intro x hx
    obtain ⟨N, hN⟩ := exists_eventually_le_of_notMem_limsupGT (f := g) (a := K + 1) hx hs
    refine mem_limsupGT.2 ⟨t, by push_cast [ht]; linarith, ?_⟩
    refine mem_freqAbove.2 fun M => ?_
    refine ⟨max (max M N) 1, max_le_max (le_max_left M N) (le_refl 1), ?_⟩
    set n : ℕ := max (max M N) 1 with hn
    have hnN : N ≤ n := le_max_of_le_left (le_max_right M N)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := le_max_right _ _
      exact_mod_cast this
    have hgn : birkhoffSum T g n x ≤ (s : ℝ) * n := hN n hnN
    have hfn : -(s : ℝ) * n ≤ birkhoffSum T f n x := by
      have hneg : birkhoffSum T g n x = -birkhoffSum T f n x := by
        simp only [hg, birkhoffSum, Finset.sum_neg_distrib]
      rw [hneg] at hgn
      linarith
    have htlt : ((t : ℚ) : ℝ) < -(s : ℝ) := by push_cast [ht]; linarith
    nlinarith [hfn, htlt, hn1]
  have hcompl : μ (limsupGT T g (K + 1))ᶜ = 1 :=
    (prob_compl_eq_one_iff (measurableSet_limsupGT hTm hgm (K + 1))).2 hzero
  refine le_antisymm prob_le_one ?_
  rw [← hcompl]
  exact measure_mono hkey

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  {T : α → α} {f : α → ℝ}

/-- A level whose upper-limit superlevel set is conull is at most the mean. -/
theorem le_integral_of_measure_limsupGT_eq_one (hT : Ergodic T μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) {a : ℝ} (ha : μ (limsupGT T f a) = 1) :
    a ≤ ∫ x, f x ∂μ := by
  have hsub : μ (limsupGT T f a) ≤ μ (overSet T f a) := measure_mono limsupGT_subset_overSet
  have hone : μ (overSet T f a) = 1 := le_antisymm prob_le_one (by rw [← ha]; exact hsub)
  have hmeas : MeasurableSet (overSet T f a) := measurableSet_overSet hTm hfm a
  have hcompl : μ (overSet T f a)ᶜ = 0 := by
    rw [measure_compl hmeas (measure_ne_top μ _), hone, measure_univ, tsub_self]
  have hae : ∀ᵐ x ∂μ, x ∈ overSet T f a := by
    rw [ae_iff]
    exact hcompl
  have hrestrict : μ.restrict (overSet T f a) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have h0 := setIntegral_sub_const_nonneg hT.toMeasurePreserving hTm hf hfm a
  rw [hrestrict] at h0
  rw [integral_sub hf (integrable_const a), integral_const, probReal_univ,
    smul_eq_mul, one_mul] at h0
  linarith

/-- The set of levels with conull upper-limit superlevel set is a nonempty set bounded above. -/
theorem bddAbove_measureOneLevels (hT : Ergodic T μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) :
    BddAbove {a : ℝ | μ (limsupGT T f a) = 1} :=
  ⟨∫ x, |f x| ∂μ, fun _ ha => le_integral_abs_of_measure_limsupGT_eq_one hT hTm hf hfm ha⟩

theorem measure_limsupGT_eq_one_of_lt_sSup (hT : Ergodic T μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) {a : ℝ}
    (ha : a < sSup {a : ℝ | μ (limsupGT T f a) = 1}) :
    μ (limsupGT T f a) = 1 := by
  obtain ⟨p, hp, hap⟩ := exists_lt_of_lt_csSup (exists_measure_limsupGT_eq_one hT hTm hf hfm) ha
  have hmono : limsupGT T f p ⊆ limsupGT T f a := limsupGT_mono (le_of_lt hap)
  refine le_antisymm prob_le_one ?_
  rw [← hp]
  exact measure_mono hmono

theorem measure_limsupGT_eq_zero_of_sSup_lt (hT : Ergodic T μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) {a : ℝ}
    (ha : sSup {a : ℝ | μ (limsupGT T f a) = 1} < a) :
    μ (limsupGT T f a) = 0 := by
  refine (measure_limsupGT_eq_zero_or_one hT hTm hfm a).resolve_right fun hcon => ?_
  have : a ≤ sSup {a : ℝ | μ (limsupGT T f a) = 1} :=
    le_csSup (bddAbove_measureOneLevels hT hTm hf hfm) hcon
  linarith

theorem sSup_measureOneLevels_le_integral (hT : Ergodic T μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) :
    sSup {a : ℝ | μ (limsupGT T f a) = 1} ≤ ∫ x, f x ∂μ :=
  csSup_le (exists_measure_limsupGT_eq_one hT hTm hf hfm) fun _ ha =>
    le_integral_of_measure_limsupGT_eq_one hT hTm hf hfm ha

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  {T : α → α} {f : α → ℝ}

omit [MeasurableSpace α] in
theorem birkhoffSum_neg (n : ℕ) (x : α) :
    birkhoffSum T (fun y => -f y) n x = -birkhoffSum T f n x := by
  simp only [birkhoffSum, Finset.sum_neg_distrib]

/-- **Birkhoff's pointwise ergodic theorem.**  For an ergodic measure-preserving map of a
probability space the Birkhoff averages of an integrable observable converge almost everywhere to
its mean. -/
theorem ae_tendsto_birkhoffAverage (hT : Ergodic T μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ x, f x ∂μ)) := by
  classical
  set L : ℝ := ∫ x, f x ∂μ with hL
  set g : α → ℝ := fun y => -f y with hg
  have hgint : Integrable g μ := hf.neg
  have hgm : Measurable g := hfm.neg
  have hgL : ∫ x, g x ∂μ = -L := by
    simp only [hg, hL, integral_neg]
  have hcf : sSup {a : ℝ | μ (limsupGT T f a) = 1} ≤ L :=
    sSup_measureOneLevels_le_integral hT hTm hf hfm
  have hcg : sSup {a : ℝ | μ (limsupGT T g a) = 1} ≤ -L := by
    have h := sSup_measureOneLevels_le_integral hT hTm hgint hgm
    rwa [hgL] at h
  have hnullf : ∀ q : ℚ, L < (q : ℝ) → μ (limsupGT T f (q : ℝ)) = 0 := fun q hq =>
    measure_limsupGT_eq_zero_of_sSup_lt hT hTm hf hfm (lt_of_le_of_lt hcf hq)
  have hnullg : ∀ q : ℚ, (q : ℝ) < L → μ (limsupGT T g (-(q : ℝ))) = 0 := fun q hq =>
    measure_limsupGT_eq_zero_of_sSup_lt hT hTm hgint hgm (by linarith)
  have hae : ∀ᵐ x ∂μ, ∀ q : ℚ,
      (L < (q : ℝ) → x ∉ limsupGT T f (q : ℝ)) ∧
        ((q : ℝ) < L → x ∉ limsupGT T g (-(q : ℝ))) := by
    rw [ae_all_iff]
    intro q
    refine Filter.Eventually.and ?_ ?_
    · by_cases hq : L < (q : ℝ)
      · have hz := hnullf q hq
        have : ∀ᵐ x ∂μ, x ∉ limsupGT T f (q : ℝ) := by
          rw [ae_iff]
          simpa using hz
        filter_upwards [this] with x hx using fun _ => hx
      · exact Filter.Eventually.of_forall fun _ h => absurd h hq
    · by_cases hq : (q : ℝ) < L
      · have hz := hnullg q hq
        have : ∀ᵐ x ∂μ, x ∉ limsupGT T g (-(q : ℝ)) := by
          rw [ae_iff]
          simpa using hz
        filter_upwards [this] with x hx using fun _ => hx
      · exact Filter.Eventually.of_forall fun _ h => absurd h hq
  filter_upwards [hae] with x hx
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (show L < L + ε / 2 by linarith)
  obtain ⟨r₁, hr₁a, hr₁b⟩ := exists_rat_btwn (show (q₁ : ℝ) < L + ε by linarith)
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (show L - ε / 2 < L by linarith)
  obtain ⟨u, hua, hub⟩ := exists_rat_btwn (show -(q₂ : ℝ) < -L + ε by linarith)
  obtain ⟨N₁, hN₁⟩ :=
    exists_eventually_le_of_notMem_limsupGT ((hx q₁).1 hq₁a) hr₁a
  obtain ⟨N₂, hN₂⟩ :=
    exists_eventually_le_of_notMem_limsupGT ((hx q₂).2 hq₂b) hua
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ 1) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hupper : birkhoffSum T f n x ≤ (r₁ : ℝ) * n :=
    hN₁ n (le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hn)
  have hlowerg : birkhoffSum T g n x ≤ (u : ℝ) * n :=
    hN₂ n (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hn)
  have hlower : -((u : ℝ) * n) ≤ birkhoffSum T f n x := by
    rw [hg, birkhoffSum_neg] at hlowerg
    linarith
  have havg : birkhoffAverage ℝ T f n x = (n : ℝ)⁻¹ * birkhoffSum T f n x := by
    simp only [birkhoffAverage, smul_eq_mul]
  rw [Real.dist_eq, havg]
  have h1 : (n : ℝ)⁻¹ * birkhoffSum T f n x ≤ (r₁ : ℝ) := by
    rw [inv_mul_le_iff₀ hnpos]
    linarith [hupper]
  have h2 : -(u : ℝ) ≤ (n : ℝ)⁻¹ * birkhoffSum T f n x := by
    rw [le_inv_mul_iff₀ hnpos]
    linarith [hlower]
  rw [abs_lt]
  constructor
  · linarith
  · linarith

end GaloisForLFunctions.HTGeometry
