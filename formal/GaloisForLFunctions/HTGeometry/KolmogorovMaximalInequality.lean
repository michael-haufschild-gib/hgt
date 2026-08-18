import GaloisForLFunctions.HTGeometry.SeriesConvergenceZeroOne
import Mathlib.Probability.Independence.Integration

/-!
# Kolmogorov's maximal inequality for a coordinatewise series

For a countable product of probability spaces and a series whose `n`-th term reads only the `n`-th
coordinate, with every term centred, the partial sums satisfy

```text
λ² · P( max_{n ≤ N} ‖S n‖ ≥ λ )  ≤  E ‖S N‖² .
```

This is strictly stronger than Chebyshev's inequality applied to `S N` alone, and it is the exact
input that upgrades `L²` summability of the terms to almost sure convergence of the series — the
step that neither the three-series theorem nor Itô–Nisio provide in mathlib.

The proof is the classical first-passage decomposition.  On the event that `N` is the first index
where the partial sum reaches `λ`, the future increment is independent of the past, so the cross
term of `‖S N‖² = ‖S n‖² + 2 Re(conj (S n) · (S N - S n)) + ‖S N - S n‖²` integrates to zero, and
the remaining two terms are bounded below by `λ²` on that event.

The independence input is packaged as `indepFun_of_blockDependence`: two functions on a countable
product that depend only on disjoint finite blocks of coordinates are independent.  The device that
makes this painless is `blockExtend`, which rebuilds a point of the product from its restriction to
a finite set using a fixed reference point elsewhere; "depends only on the block `s`" is then the
equation `U (blockExtend a s (s.restrict x)) = U x`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-! ### Dependence on a finite block of coordinates -/

/-- Rebuild a point of a product from its restriction to a finite set, filling in the remaining
coordinates from a fixed reference point. -/
def blockExtend (a : ∀ m, X m) (s : Finset ℕ) (y : ∀ i : s, X i) : ∀ m, X m :=
  fun m => if h : m ∈ s then y ⟨m, h⟩ else a m

theorem measurable_blockExtend (a : ∀ m, X m) (s : Finset ℕ) :
    Measurable (blockExtend (X := X) a s) := by
  refine measurable_pi_lambda _ fun m => ?_
  by_cases hm : m ∈ s
  · have : (fun y : ∀ i : s, X i => blockExtend (X := X) a s y m)
        = fun y : ∀ i : s, X i => y ⟨m, hm⟩ := by
      funext y; simp [blockExtend, hm]
    rw [this]
    exact measurable_pi_apply _
  · have : (fun y : ∀ i : s, X i => blockExtend (X := X) a s y m) = fun _ => a m := by
      funext y; simp [blockExtend, hm]
    rw [this]
    exact measurable_const

/-- **Disjoint coordinate blocks are independent.**  If `U` reads only the coordinates in `s` and
`V` only those in `t`, with `s` and `t` disjoint, then `U` and `V` are independent for any product
probability measure. -/
theorem indepFun_of_blockDependence (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (a : ∀ m, X m) {s t : Finset ℕ} (hst : Disjoint s t)
    {U V : (∀ m, X m) → ℂ} (hU : Measurable U) (hV : Measurable V)
    (hUs : ∀ x, U (blockExtend a s (s.restrict x)) = U x)
    (hVt : ∀ x, V (blockExtend a t (t.restrict x)) = V x) :
    IndepFun U V (Measure.infinitePi μ) := by
  have hbase : IndepFun (fun x : ∀ m, X m => s.restrict x) (fun x : ∀ m, X m => t.restrict x)
      (Measure.infinitePi μ) :=
    ProbabilityTheory.iIndepFun.indepFun_finset s t hst
      (iIndepFun_infinitePi (X := fun (i : ℕ) (ω : X i) => ω) fun _ => measurable_id)
      fun i => measurable_pi_apply i
  have hcomp := hbase.comp (φ := fun y => U (blockExtend a s y))
    (ψ := fun y => V (blockExtend a t y)) (hU.comp (measurable_blockExtend a s))
    (hV.comp (measurable_blockExtend a t))
  have hUeq : (fun y => U (blockExtend a s y)) ∘ (fun x : ∀ m, X m => s.restrict x) = U := by
    funext x; exact hUs x
  have hVeq : (fun y => V (blockExtend a t y)) ∘ (fun x : ∀ m, X m => t.restrict x) = V := by
    funext x; exact hVt x
  rwa [hUeq, hVeq] at hcomp

/-! ### The first-passage decomposition -/

variable (g : ∀ n, X n → ℂ)

/-- The event that `n` is the first index at which the partial sums reach `lam`. -/
def firstPassage (lam : ℝ) (n : ℕ) : Set (∀ m, X m) :=
  {x | (∀ k, k < n → ‖coordPartialSum g k x‖ < lam) ∧ lam ≤ ‖coordPartialSum g n x‖}

theorem measurableSet_firstPassage (hg : ∀ n, Measurable (g n)) (lam : ℝ) (n : ℕ) :
    MeasurableSet (firstPassage g lam n) := by
  have hmeas : ∀ k : ℕ, Measurable fun x : ∀ m, X m => ‖coordPartialSum g k x‖ :=
    fun k => (measurable_coordPartialSum g hg k).norm
  have hsplit : firstPassage g lam n
      = (⋂ (k : ℕ), ⋂ (_ : k < n), {x : ∀ m, X m | ‖coordPartialSum g k x‖ < lam})
        ∩ {x : ∀ m, X m | lam ≤ ‖coordPartialSum g n x‖} := by
    ext x
    simp [firstPassage]
  rw [hsplit]
  refine MeasurableSet.inter ?_ (measurableSet_le measurable_const (hmeas n))
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_lt (hmeas k) measurable_const

omit [∀ n, MeasurableSpace (X n)] in
theorem pairwiseDisjoint_firstPassage (lam : ℝ) :
    Pairwise (Function.onFun Disjoint (firstPassage g lam)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hi hj => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · exact absurd hi.2 (not_le.mpr (hj.1 i h))
  · exact absurd hj.2 (not_le.mpr (hi.1 j h))

omit [∀ n, MeasurableSpace (X n)] in
theorem iUnion_firstPassage (lam : ℝ) (N : ℕ) :
    (⋃ n ∈ Finset.range (N + 1), firstPassage g lam n)
      = {x | ∃ n ≤ N, lam ≤ ‖coordPartialSum g n x‖} := by
  ext x
  constructor
  · rintro hx
    simp only [Set.mem_iUnion, Finset.mem_range] at hx
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨n, Nat.lt_succ_iff.mp hn, hx.2⟩
  · rintro ⟨n, hn, hxn⟩
    classical
    have hex : ∃ k, lam ≤ ‖coordPartialSum g k x‖ := ⟨n, hxn⟩
    set m := Nat.find hex with hm
    have hmspec : lam ≤ ‖coordPartialSum g m x‖ := Nat.find_spec hex
    have hmle : m ≤ n := Nat.find_le hxn
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨m, by omega, ?_, hmspec⟩
    intro k hk
    have := Nat.find_min hex (m := k) (by omega)
    exact not_le.mp this


/-! ### Block dependence of the partial sums -/

omit [∀ n, MeasurableSpace (X n)] in
theorem coordPartialSum_blockExtend_le (a : ∀ m, X m) {k n : ℕ} (hk : k ≤ n) (x : ∀ m, X m) :
    coordPartialSum g k (blockExtend a (Finset.range n) ((Finset.range n).restrict x))
      = coordPartialSum g k x := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ∈ Finset.range n :=
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
  simp [blockExtend, hj', Finset.restrict]

omit [∀ n, MeasurableSpace (X n)] in
theorem firstPassage_blockExtend (a : ∀ m, X m) (lam : ℝ) (n : ℕ) (x : ∀ m, X m) :
    (blockExtend a (Finset.range n) ((Finset.range n).restrict x) ∈ firstPassage g lam n)
      ↔ x ∈ firstPassage g lam n := by
  have h : ∀ k, k ≤ n →
      coordPartialSum g k (blockExtend a (Finset.range n) ((Finset.range n).restrict x))
        = coordPartialSum g k x := fun k hk => coordPartialSum_blockExtend_le g a hk x
  simp only [firstPassage, Set.mem_setOf_eq, h n le_rfl]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hk => by rw [← h k hk.le]; exact h1 k hk, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hk => by rw [h k hk.le]; exact h1 k hk, h2⟩

omit [∀ n, MeasurableSpace (X n)] in
theorem coordPartialSum_sub_eq_sum_Ico {n N : ℕ} (hn : n ≤ N) (x : ∀ m, X m) :
    coordPartialSum g N x - coordPartialSum g n x = ∑ k ∈ Finset.Ico n N, g k (x k) :=
  (Finset.sum_Ico_eq_sub (fun k => g k (x k)) hn).symm

omit [∀ n, MeasurableSpace (X n)] in
theorem coordIncrement_blockExtend (a : ∀ m, X m) {n N : ℕ} (hn : n ≤ N) (x : ∀ m, X m) :
    coordPartialSum g N (blockExtend a (Finset.Ico n N) ((Finset.Ico n N).restrict x))
        - coordPartialSum g n (blockExtend a (Finset.Ico n N) ((Finset.Ico n N).restrict x))
      = coordPartialSum g N x - coordPartialSum g n x := by
  rw [coordPartialSum_sub_eq_sum_Ico g hn, coordPartialSum_sub_eq_sum_Ico g hn]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [blockExtend, hj, Finset.restrict]

/-! ### Integrability and centring -/

variable (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]

theorem integrable_of_norm_le {f : (∀ m, X m) → ℂ} (hf : Measurable f) {C : ℝ}
    (h : ∀ x, ‖f x‖ ≤ C) : Integrable f (Measure.infinitePi μ) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall h)

theorem integrable_of_norm_le_real {f : (∀ m, X m) → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ x, ‖f x‖ ≤ C) : Integrable f (Measure.infinitePi μ) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall h)

variable {c : ℕ → ℝ}

omit [∀ n, MeasurableSpace (X n)] in
theorem norm_coordPartialSum_le (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (N : ℕ) (x : ∀ m, X m) :
    ‖coordPartialSum g N x‖ ≤ ∑ n ∈ Finset.range N, c n :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => hbdd n _)

theorem integrable_coordPartialSum (hg : ∀ n, Measurable (g n)) (hbdd : ∀ n y, ‖g n y‖ ≤ c n)
    (N : ℕ) : Integrable (coordPartialSum g N) (Measure.infinitePi μ) :=
  integrable_of_norm_le μ (measurable_coordPartialSum g hg N)
    (norm_coordPartialSum_le g hbdd N)

/-- The mean of one coordinate term is the mean of its factor. -/
theorem integral_coordTerm (hg : ∀ n, Measurable (g n)) (k : ℕ) :
    ∫ x, g k (x k) ∂(Measure.infinitePi μ) = ∫ y, g k y ∂(μ k) := by
  have hmap : Measure.map (fun x : ∀ m, X m => x k) (Measure.infinitePi μ) = μ k :=
    Measure.infinitePi_map_eval μ k
  have h : ∫ y, g k y ∂(Measure.map (fun x : ∀ m, X m => x k) (Measure.infinitePi μ))
      = ∫ x, g k (x k) ∂(Measure.infinitePi μ) :=
    integral_map (measurable_pi_apply k).aemeasurable
      (by rw [hmap]; exact (hg k).aestronglyMeasurable)
  rw [hmap] at h
  exact h.symm

/-- Centred terms give centred partial sums. -/
theorem integral_coordPartialSum_eq_zero (hg : ∀ n, Measurable (g n))
    (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0) (N : ℕ) :
    ∫ x, coordPartialSum g N x ∂(Measure.infinitePi μ) = 0 := by
  show ∫ x, ∑ k ∈ Finset.range N, g k (x k) ∂(Measure.infinitePi μ) = 0
  rw [integral_finsetSum (f := fun k (x : ∀ m, X m) => g k (x k)) _ fun k _ =>
    integrable_of_norm_le μ ((hg k).comp (measurable_pi_apply k)) fun x => hbdd k (x k)]
  exact Finset.sum_eq_zero fun k _ => by rw [integral_coordTerm g μ hg k, hmean k]


/-! ### The maximal inequality -/

/-- **The cross term of the first-passage decomposition vanishes.**  The past factor reads only the
coordinates below `n`, the future increment only those from `n` on, and the increment is centred. -/
theorem integral_crossTerm_eq_zero (a : ∀ m, X m) (hg : ∀ n, Measurable (g n))
    (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0)
    (lam : ℝ) {n N : ℕ} (hn : n ≤ N) :
    ∫ x in firstPassage g lam n,
        ((starRingEnd ℂ) (coordPartialSum g n x) *
          (coordPartialSum g N x - coordPartialSum g n x)) ∂(Measure.infinitePi μ) = 0 := by
  classical
  set A := firstPassage g lam n with hAdef
  have hA : MeasurableSet A := measurableSet_firstPassage g hg lam n
  set U : (∀ m, X m) → ℂ :=
    A.indicator fun x => (starRingEnd ℂ) (coordPartialSum g n x) with hUdef
  set V : (∀ m, X m) → ℂ :=
    fun x => coordPartialSum g N x - coordPartialSum g n x with hVdef
  have hUmeas : Measurable U :=
    Measurable.indicator (Complex.measurable_conj.comp (measurable_coordPartialSum g hg n)) hA
  have hVmeas : Measurable V :=
    (measurable_coordPartialSum g hg N).sub (measurable_coordPartialSum g hg n)
  have hUblock : ∀ x, U (blockExtend a (Finset.range n) ((Finset.range n).restrict x)) = U x := by
    intro x
    by_cases hx : x ∈ A
    · have hy : blockExtend a (Finset.range n) ((Finset.range n).restrict x) ∈ A :=
        (firstPassage_blockExtend g a lam n x).mpr hx
      rw [hUdef]
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx,
        coordPartialSum_blockExtend_le g a (le_refl n) x]
    · have hy : blockExtend a (Finset.range n) ((Finset.range n).restrict x) ∉ A := fun h =>
        hx ((firstPassage_blockExtend g a lam n x).mp h)
      rw [hUdef, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  have hVblock : ∀ x, V (blockExtend a (Finset.Ico n N) ((Finset.Ico n N).restrict x)) = V x :=
    fun x => coordIncrement_blockExtend g a hn x
  have hdisj : Disjoint (Finset.range n) (Finset.Ico n N) := by
    refine Finset.disjoint_left.mpr fun k hk hk' => ?_
    exact absurd (Finset.mem_range.mp hk) (not_lt.mpr (Finset.mem_Ico.mp hk').1)
  have hindep : IndepFun U V (Measure.infinitePi μ) :=
    indepFun_of_blockDependence μ a hdisj hUmeas hVmeas hUblock hVblock
  have hrewrite : (fun x => U x * V x)
      = A.indicator fun x => (starRingEnd ℂ) (coordPartialSum g n x) * V x := by
    funext x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hUdef, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hUdef, Set.indicator_of_notMem hx, zero_mul]
  have hV0 : ∫ x, V x ∂(Measure.infinitePi μ) = 0 := by
    rw [hVdef, integral_sub (integrable_coordPartialSum g μ hg hbdd N)
      (integrable_coordPartialSum g μ hg hbdd n),
      integral_coordPartialSum_eq_zero g μ hg hbdd hmean N,
      integral_coordPartialSum_eq_zero g μ hg hbdd hmean n, sub_zero]
  rw [← integral_indicator hA, ← hrewrite,
    hindep.integral_fun_mul_eq_mul_integral hUmeas.aestronglyMeasurable
      hVmeas.aestronglyMeasurable, hV0, mul_zero]

/-- **Kolmogorov's maximal inequality.**  For a centred coordinatewise series in a countable
product of probability spaces, the probability that the partial sums up to `N` ever reach `lam`
is at most `lam⁻² E‖S N‖²`. -/
theorem kolmogorov_maximal_inequality (a : ∀ m, X m) (hg : ∀ n, Measurable (g n))
    (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0)
    (N : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * (Measure.infinitePi μ {x | ∃ n ≤ N, lam ≤ ‖coordPartialSum g n x‖}).toReal
      ≤ ∫ x, ‖coordPartialSum g N x‖ ^ 2 ∂(Measure.infinitePi μ) := by
  classical
  set ν := Measure.infinitePi μ with hνdef
  set S := fun n => coordPartialSum (X := X) g n with hSdef
  have hSmeas : ∀ n, Measurable (S n) := fun n => measurable_coordPartialSum g hg n
  have hSbound : ∀ n x, ‖S n x‖ ≤ ∑ k ∈ Finset.range n, c k := fun n =>
    norm_coordPartialSum_le g hbdd n
  have hSint : ∀ n, Integrable (S n) ν := fun n => integrable_coordPartialSum g μ hg hbdd n
  have hsqint : ∀ n, Integrable (fun x => ‖S n x‖ ^ 2) ν := by
    intro n
    refine integrable_of_norm_le_real μ ((hSmeas n).norm.pow_const 2)
      (C := (∑ k ∈ Finset.range n, c k) ^ 2) fun x => ?_
    have h0 : (0 : ℝ) ≤ ‖S n x‖ := norm_nonneg _
    have h1 : ‖S n x‖ ≤ ∑ k ∈ Finset.range n, c k := hSbound n x
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ h0 h1 2
  have hA : ∀ n, MeasurableSet (firstPassage g lam n) := fun n =>
    measurableSet_firstPassage g hg lam n
  -- the first-passage lower bound
  have key : ∀ n, n ≤ N → lam ^ 2 * (ν (firstPassage g lam n)).toReal
      ≤ ∫ x in firstPassage g lam n, ‖S N x‖ ^ 2 ∂ν := by
    intro n hn
    have hdec : ∀ x, ‖S N x‖ ^ 2 = ‖S n x‖ ^ 2
        + 2 * ((starRingEnd ℂ) (S n x) * (S N x - S n x)).re + ‖S N x - S n x‖ ^ 2 := by
      intro x
      have h : S N x = S n x + (S N x - S n x) := by ring
      rw [h]
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
        Complex.sub_im]
      ring
    have hint1 : IntegrableOn (fun x => ‖S n x‖ ^ 2) (firstPassage g lam n) ν :=
      (hsqint n).restrict
    have hint3 : IntegrableOn (fun x => ‖S N x - S n x‖ ^ 2) (firstPassage g lam n) ν := by
      refine Integrable.restrict ?_
      refine integrable_of_norm_le_real μ (((hSmeas N).sub (hSmeas n)).norm.pow_const 2)
        (C := ((∑ k ∈ Finset.range N, c k) + (∑ k ∈ Finset.range n, c k)) ^ 2) fun x => ?_
      have h1 : ‖S N x - S n x‖ ≤ (∑ k ∈ Finset.range N, c k) + (∑ k ∈ Finset.range n, c k) :=
        (norm_sub_le _ _).trans (add_le_add (hSbound N x) (hSbound n x))
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hint2 : IntegrableOn
        (fun x => 2 * ((starRingEnd ℂ) (S n x) * (S N x - S n x)).re)
        (firstPassage g lam n) ν := by
      refine Integrable.restrict ?_
      refine integrable_of_norm_le_real μ ?_
        (C := 2 * ((∑ k ∈ Finset.range n, c k) *
          ((∑ k ∈ Finset.range N, c k) + (∑ k ∈ Finset.range n, c k)))) fun x => ?_
      · exact ((((Complex.measurable_conj.comp (hSmeas n)).mul
          ((hSmeas N).sub (hSmeas n))).re).const_mul 2)
      · have hb1 : ‖(starRingEnd ℂ) (S n x)‖ ≤ ∑ k ∈ Finset.range n, c k := by
          rw [RCLike.norm_conj]; exact hSbound n x
        have hb2 : ‖S N x - S n x‖ ≤ (∑ k ∈ Finset.range N, c k)
            + (∑ k ∈ Finset.range n, c k) :=
          (norm_sub_le _ _).trans (add_le_add (hSbound N x) (hSbound n x))
        have hre : |((starRingEnd ℂ) (S n x) * (S N x - S n x)).re|
            ≤ ‖(starRingEnd ℂ) (S n x)‖ * ‖S N x - S n x‖ := by
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range n, c k := le_trans (norm_nonneg (S n x)) (hSbound n x)
        calc 2 * |((starRingEnd ℂ) (S n x) * (S N x - S n x)).re|
            ≤ 2 * (‖(starRingEnd ℂ) (S n x)‖ * ‖S N x - S n x‖) := by linarith
          _ ≤ 2 * ((∑ k ∈ Finset.range n, c k) *
                ((∑ k ∈ Finset.range N, c k) + (∑ k ∈ Finset.range n, c k))) := by
              have := mul_le_mul hb1 hb2 (norm_nonneg _) hnn
              linarith
    have hsplit : ∫ x in firstPassage g lam n, ‖S N x‖ ^ 2 ∂ν
        = (∫ x in firstPassage g lam n, ‖S n x‖ ^ 2 ∂ν)
          + (∫ x in firstPassage g lam n,
              2 * ((starRingEnd ℂ) (S n x) * (S N x - S n x)).re ∂ν)
          + ∫ x in firstPassage g lam n, ‖S N x - S n x‖ ^ 2 ∂ν := by
      rw [← integral_add (hint1.add hint2) hint3, ← integral_add hint1 hint2]
      exact setIntegral_congr_fun (hA n) fun x _ => hdec x
    have hcross : ∫ x in firstPassage g lam n,
        2 * ((starRingEnd ℂ) (S n x) * (S N x - S n x)).re ∂ν = 0 := by
      rw [integral_const_mul]
      have hI : Integrable (fun x => (starRingEnd ℂ) (S n x) * (S N x - S n x)) ν := by
        refine integrable_of_norm_le μ ((Complex.measurable_conj.comp (hSmeas n)).mul
          ((hSmeas N).sub (hSmeas n)))
          (C := (∑ k ∈ Finset.range n, c k) *
            ((∑ k ∈ Finset.range N, c k) + (∑ k ∈ Finset.range n, c k))) fun x => ?_
        rw [norm_mul, RCLike.norm_conj]
        have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range n, c k := le_trans (norm_nonneg (S n x)) (hSbound n x)
        exact mul_le_mul (hSbound n x)
          ((norm_sub_le _ _).trans (add_le_add (hSbound N x) (hSbound n x))) (norm_nonneg _) hnn
      rw [integral_re hI.restrict, integral_crossTerm_eq_zero g μ a hg hbdd hmean lam hn]
      simp
    have hlow : lam ^ 2 * (ν (firstPassage g lam n)).toReal
        ≤ ∫ x in firstPassage g lam n, ‖S n x‖ ^ 2 ∂ν := by
      have hconst : ∫ _x in firstPassage g lam n, lam ^ 2 ∂ν
          = (ν (firstPassage g lam n)).toReal * lam ^ 2 := by
        rw [setIntegral_const]
        rfl
      rw [← hconst]
      refine le_trans (le_of_eq ?_) (setIntegral_mono_on (integrableOn_const_of_measure_ne_top
        (by exact measure_ne_top ν _)) hint1 (hA n) fun x hx => ?_)
      · rw [hconst]; ring
      · have := hx.2
        nlinarith [norm_nonneg (S n x), this]
    have hpos : 0 ≤ ∫ x in firstPassage g lam n, ‖S N x - S n x‖ ^ 2 ∂ν :=
      setIntegral_nonneg (hA n) fun x _ => by positivity
    rw [hsplit, hcross]
    linarith
  -- assemble
  have hEeq : {x : ∀ m, X m | ∃ n ≤ N, lam ≤ ‖coordPartialSum g n x‖}
      = ⋃ n ∈ Finset.range (N + 1), firstPassage g lam n := (iUnion_firstPassage g lam N).symm
  have hdisjset : Set.Pairwise (↑(Finset.range (N + 1))) (Function.onFun Disjoint
      (firstPassage g lam)) := fun i _ j _ hij => pairwiseDisjoint_firstPassage g lam hij
  have hmeasure : ν {x : ∀ m, X m | ∃ n ≤ N, lam ≤ ‖coordPartialSum g n x‖}
      = ∑ n ∈ Finset.range (N + 1), ν (firstPassage g lam n) := by
    rw [hEeq]
    exact measure_biUnion_finset hdisjset fun n _ => hA n
  have htoReal : (ν {x : ∀ m, X m | ∃ n ≤ N, lam ≤ ‖coordPartialSum g n x‖}).toReal
      = ∑ n ∈ Finset.range (N + 1), (ν (firstPassage g lam n)).toReal := by
    rw [hmeasure, ENNReal.toReal_sum fun n _ => measure_ne_top ν _]
  have hsum : ∑ n ∈ Finset.range (N + 1), ∫ x in firstPassage g lam n, ‖S N x‖ ^ 2 ∂ν
      = ∫ x in ⋃ n ∈ Finset.range (N + 1), firstPassage g lam n, ‖S N x‖ ^ 2 ∂ν :=
    (integral_biUnion_finset _ (fun n _ => hA n) hdisjset fun n _ => (hsqint N).restrict).symm
  have hle : ∫ x in ⋃ n ∈ Finset.range (N + 1), firstPassage g lam n, ‖S N x‖ ^ 2 ∂ν
      ≤ ∫ x, ‖S N x‖ ^ 2 ∂ν :=
    setIntegral_le_integral (hsqint N) (Filter.Eventually.of_forall fun x => by positivity)
  calc lam ^ 2 * (ν {x : ∀ m, X m | ∃ n ≤ N, lam ≤ ‖coordPartialSum g n x‖}).toReal
      = ∑ n ∈ Finset.range (N + 1), lam ^ 2 * (ν (firstPassage g lam n)).toReal := by
        rw [htoReal, Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.range (N + 1), ∫ x in firstPassage g lam n, ‖S N x‖ ^ 2 ∂ν :=
        Finset.sum_le_sum fun n hn => key n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    _ = ∫ x in ⋃ n ∈ Finset.range (N + 1), firstPassage g lam n, ‖S N x‖ ^ 2 ∂ν := hsum
    _ ≤ ∫ x, ‖S N x‖ ^ 2 ∂ν := hle

end GaloisForLFunctions.HTGeometry

end
