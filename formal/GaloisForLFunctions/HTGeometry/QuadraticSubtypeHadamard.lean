/-
# The Hadamard factorization in the quadratic-subtype class

An entire function `f` with `log M_f(r) = o((log r)²)` and `f (0) ≠ 0` is a constant multiple of the
genus-zero canonical product over its own zero divisor.

The three inputs are already available: Jensen's inequality gives `n_f(r) = o(log r)`
(`divisorCount_le_of_quadraticSubtypeZero`), a sublogarithmic divisor has convergence exponent zero
so its genus-zero product converges and carries exactly that divisor
(`analyticOrderAt_genusZeroProductIdx`), and equal divisors force an entire nonvanishing quotient
(`exists_entire_nonvanishing_quotient`).  What is proved here is the bookkeeping that connects them
— the zero-copy count of a disc is the divisor mass of that disc — and the growth argument that
makes the quotient constant: the first main theorem bounds `m(r, h)` by `m(r, f) + m(r, P) + O(1)`,
both of which are `o((log r)²)`, and a zero-free entire function of that proximity is constant.
-/
import GaloisForLFunctions.HTGeometry.EntireZeroDivisorIndex
import GaloisForLFunctions.HTGeometry.EntireQuotientNormalForm
import GaloisForLFunctions.HTGeometry.QuotientProximityBound
import GaloisForLFunctions.HTGeometry.NevanlinnaMaxModulusBridge

noncomputable section

open Filter Topology Set Metric ValueDistribution

namespace GaloisForLFunctions.QuadraticSubtypeHadamard

open GaloisForLFunctions.CountableDivisor GaloisForLFunctions.EntireZeroDivisor
open GaloisForLFunctions.QuadraticSubtypeDivisor GaloisForLFunctions.QuotientProximity
open GaloisForLFunctions.Nevanlinna GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.EntireQuotient

variable {f : ℂ → ℂ}

/-! ## Growth in the class `(1)` bounds the proximity -/

theorem proximity_le_of_growth {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ) {ε : ℝ}
    (hbound : ∀ᶠ r : ℝ in atTop,
      ∀ z : ℂ, ‖z‖ ≤ r → Real.log ‖g z‖ ≤ ε * (Real.log r) ^ (2 : ℕ)) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, proximity g ⊤ r ≤ ε * (Real.log r) ^ (2 : ℕ) := by
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hnn : 0 ≤ ε * (Real.log r) ^ (2 : ℕ) := by positivity
  have hmer : MeromorphicOn g (sphere (0 : ℂ) r) :=
    fun z _ => (hg z (Set.mem_univ z)).meromorphicAt
  have hM : ∀ z : ℂ, ‖z‖ = r → ‖g z‖ ≤ Real.exp (ε * (Real.log r) ^ (2 : ℕ)) := by
    intro z hz
    rcases eq_or_lt_of_le (norm_nonneg (g z)) with h0 | h0
    · rw [← h0]
      exact (Real.exp_pos _).le
    · have h1 := hr z (le_of_eq hz)
      rw [← Real.exp_log h0]
      exact Real.exp_le_exp.mpr h1
  refine le_trans (proximity_top_le_posLog_of_norm hr0 hmer hM) ?_
  rw [Real.posLog, Real.log_exp]
  exact max_le hnn le_rfl

/-! ## The divisor mass of a disc -/

theorem divisor_ball_apply (hf : AnalyticOnNhd ℂ f Set.univ) {r : ℝ} {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) r) :
    (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)) u
      = (MeromorphicOn.divisor f Set.univ) u := by
  have hmer : MeromorphicOn f (Metric.closedBall (0 : ℂ) r) :=
    fun z _ => (hf z (Set.mem_univ z)).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmer hu,
    MeromorphicOn.divisor_apply (fun z _ => (hf z (Set.mem_univ z)).meromorphicAt)
      (Set.mem_univ u)]

theorem divisor_ball_apply_of_notMem {r : ℝ} {u : ℂ}
    (hu : u ∉ Metric.closedBall (0 : ℂ) r) :
    (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)) u = 0 := by
  by_contra h
  exact hu ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)).supportWithinDomain h)

/-- **The zero-copy count is the divisor mass of the disc.** -/
theorem divisorIdxCount_eq (hf : AnalyticOnNhd ℂ f Set.univ) (r : ℝ) :
    ((divisorIdxCount (zeroCopyPoint f) r : ℕ) : ℤ)
      = ∑ᶠ u : ℂ, (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)) u := by
  classical
  have hAfin := finite_zeroSupport_ball hf r
  set T : Finset (ZeroSupport f) := hAfin.toFinset with hT
  have hmemT : ∀ w : ZeroSupport f, w ∈ T ↔ ‖(w : ℂ)‖ ≤ r := by
    intro w
    rw [hT, Set.Finite.mem_toFinset]
    rfl
  have hball : ∀ w : ZeroSupport f, w ∈ T → (w : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
    intro w hw
    simpa [Metric.mem_closedBall, dist_eq_norm] using (hmemT w).mp hw
  have hStep : divisorIdxCount (zeroCopyPoint f) r
      = ∑ w ∈ T, ((MeromorphicOn.divisor f Set.univ) (w : ℂ)).toNat := by
    have hSeq : {p : ZeroCopy f | ‖zeroCopyPoint f p‖ ≤ r} = {p : ZeroCopy f | p.1 ∈ T} := by
      ext p
      simp only [Set.mem_setOf_eq, zeroCopyPoint, hmemT]
    rw [divisorIdxCount, hSeq, ← Nat.card_coe_set_eq]
    show Nat.card {y : ZeroCopy f // y.fst ∈ T} = _
    rw [Nat.card_congr (Equiv.subtypeSigmaEquiv
        (fun w : ZeroSupport f => Fin ((MeromorphicOn.divisor f Set.univ) (w : ℂ)).toNat)
        (fun w => w ∈ T)),
      Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Finset.univ_eq_attach]
    exact Finset.sum_attach T (fun w : ZeroSupport f =>
      ((MeromorphicOn.divisor f Set.univ) (w : ℂ)).toNat)
  have hsupp : Function.support
      (fun u : ℂ => (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)) u)
      ⊆ ↑(T.image (fun w : ZeroSupport f => (w : ℂ))) := by
    intro u hu
    have hune : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)) u ≠ 0 := hu
    have humem : u ∈ Metric.closedBall (0 : ℂ) r := by
      by_contra hcon
      exact hune (divisor_ball_apply_of_notMem hcon)
    have huniv : (MeromorphicOn.divisor f Set.univ) u ≠ 0 := by
      rw [← divisor_ball_apply hf humem]
      exact hune
    have hnorm : ‖u‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using humem
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨u, huniv⟩, ?_, rfl⟩)
    exact (hmemT ⟨u, huniv⟩).mpr hnorm
  have hinjOn : ∀ w ∈ T, ∀ v ∈ T, (w : ℂ) = (v : ℂ) → w = v := by
    intro w _ v _ h
    exact Subtype.ext h
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_image hinjOn, hStep]
  push_cast
  refine Finset.sum_congr rfl (fun w hw => ?_)
  have hnn : 0 ≤ (MeromorphicOn.divisor f Set.univ) (w : ℂ) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf (w : ℂ)
  rw [divisor_ball_apply hf (hball w hw), Int.toNat_of_nonneg hnn]

/-! ## The zero divisor of a quadratic-subtype-zero function is sublogarithmic -/

theorem sublogDensity_zeroCopyPoint (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hq : QuadraticSubtypeZero f) : SublogDensityIdx (zeroCopyPoint f) := by
  rw [SublogDensityIdx]
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (divisorCount_le_of_quadraticSubtypeZero hf hf0 hq (half_pos hε))
  refine ⟨max R 2, fun r hr => ?_⟩
  have hr2 : (2 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hrR : R ≤ r := le_trans (le_max_left _ _) hr
  have hlogpos : 0 < Real.log r := Real.log_pos (by linarith)
  have hcount := hR r hrR
  have hid : ((divisorIdxCount (zeroCopyPoint f) r : ℕ) : ℝ)
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)) u : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (divisorIdxCount_eq hf r)
  have hle : ((divisorIdxCount (zeroCopyPoint f) r : ℕ) : ℝ) ≤ (ε / 2) * Real.log r := by
    rw [hid]; exact hcount
  have hnn : (0 : ℝ) ≤ ((divisorIdxCount (zeroCopyPoint f) r : ℕ) : ℝ) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  rw [div_lt_iff₀ hlogpos]
  have hstrict : (ε / 2) * Real.log r < ε * Real.log r := by nlinarith
  linarith

/-! ## The canonical product realizes the divisor -/

theorem analyticOrderAt_genusZeroProduct_eq (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤) (hq : QuadraticSubtypeZero f) (w : ℂ) :
    analyticOrderAt (genusZeroProductIdx (zeroCopyPoint f)) w = analyticOrderAt f w := by
  have hloc := locallyFinite_zeroCopyPoint hf
  have hden := sublogDensity_zeroCopyPoint hf hf0 hq
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hinv := summable_inv_norm_idx hloc hden
  have hPan := genusZeroProductIdx_analytic hane hinv
  by_cases hw : w = 0
  · subst hw
    rw [(hPan 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr (by
        rw [genusZeroProductIdx_zero]; exact one_ne_zero),
      (hf 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr hf0]
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt f w = (n : ℕ∞) :=
      ⟨(analyticOrderAt f w).toNat, (ENat.coe_toNat (hford w)).symm⟩
    have hdiv : (MeromorphicOn.divisor f Set.univ) w = (n : ℤ) := by
      rw [divisor_univ_eq_analyticOrder hf, hn]
      rfl
    rw [analyticOrderAt_genusZeroProductIdx hane hloc hinv hw, hn]
    congr 1
    have hfib : {p : ZeroCopy f | zeroCopyPoint f p = w}.ncard
        = ((MeromorphicOn.divisor f Set.univ) w).toNat := ncard_zeroCopy_fiber w
    rw [hfib, hdiv]
    simp

/-! ## The forward direction of the quadratic-subtype equivalence -/

/-- **Forward direction.**  An entire function of quadratic subtype zero, nonzero at the origin,
is a constant multiple of the genus-zero canonical product over its own zero divisor. -/
theorem exists_const_mul_genusZeroProduct (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤) (hq : QuadraticSubtypeZero f) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, f z = c * genusZeroProductIdx (zeroCopyPoint f) z := by
  have hloc := locallyFinite_zeroCopyPoint hf
  have hden := sublogDensity_zeroCopyPoint hf hf0 hq
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hinv := summable_inv_norm_idx hloc hden
  have hPan := genusZeroProductIdx_analytic hane hinv
  have horder := analyticOrderAt_genusZeroProduct_eq hf hf0 hford hq
  have hP0 : genusZeroProductIdx (zeroCopyPoint f) 0 ≠ 0 := by
    rw [genusZeroProductIdx_zero]; exact one_ne_zero
  obtain ⟨h, hhdiff, hhne, hfac⟩ :=
    exists_entire_nonvanishing_quotient hf hPan hford (fun z => (horder z).symm) hP0
  have hhan : AnalyticOnNhd ℂ h Set.univ := fun z _ => Differentiable.analyticAt hhdiff z
  -- the quotient has subquadratic-logarithmic proximity
  have hFord : ∀ z, meromorphicOrderAt (genusZeroProductIdx (zeroCopyPoint f)) z ≠ ⊤ := by
    intro z
    rw [(hPan z (Set.mem_univ z)).meromorphicOrderAt_eq, horder z]
    simp [hford z]
  have hGord : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hf z (Set.mem_univ z)).meromorphicOrderAt_eq]
    simp [hford z]
  obtain ⟨K, hK⟩ := proximity_quotient_le hPan hf hhan hFord hGord hfac
  have hprf := proximity_le_of_growth hf (hq (1 / 3) (by norm_num)) (by norm_num)
  have hprP := proximity_le_of_growth hPan
    (quadraticSubtypeZero_genusZeroProductIdx hane hloc hden (by norm_num : (0:ℝ) < 1 / 3))
    (by norm_num)
  have hKo : ∀ᶠ r : ℝ in atTop, K ≤ (1 / 3) * (Real.log r) ^ (2 : ℕ) := by
    have htend : Tendsto (fun r : ℝ => (1 / 3 : ℝ) * (Real.log r) ^ (2 : ℕ)) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop (by norm_num) ?_
      exact (tendsto_pow_atTop (n := 2) (by norm_num)).comp Real.tendsto_log_atTop
    exact htend.eventually_ge_atTop K
  have hproxh : ∀ᶠ R : ℝ in atTop, proximity h ⊤ R ≤ (Real.log R) ^ (2 : ℕ) := by
    filter_upwards [hprf, hprP, hKo, eventually_ge_atTop (1 : ℝ)] with r h1 h2 h3 h4
    have := hK r h4
    linarith
  have hconst := const_of_zeroFree_of_proximity_le_logSq hhan hhne hproxh
  refine ⟨h 0, hhne 0, fun z => ?_⟩
  rw [hfac z, hconst z]

end GaloisForLFunctions.QuadraticSubtypeHadamard

namespace GaloisForLFunctions.QuadraticSubtypeHadamard

open GaloisForLFunctions.CountableDivisor GaloisForLFunctions.EntireZeroDivisor
open GaloisForLFunctions.QuadraticSubtypeDivisor GaloisForLFunctions.QuotientProximity
open GaloisForLFunctions.Nevanlinna GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.EntireQuotient

variable {f : ℂ → ℂ}

/-- Splitting off the monomial at the origin preserves the growth class. -/
theorem quadraticSubtypeZero_of_monomial_quotient {g : ℂ → ℂ} {m : ℕ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hq : QuadraticSubtypeZero f)
    (hfac : ∀ z, f z = z ^ m * g z) :
    QuadraticSubtypeZero g := by
  intro ε hε
  -- a crude bound on the closed unit disc
  have hcont : ContinuousOn (fun z : ℂ => ‖g z‖) (Metric.closedBall (0 : ℂ) 1) := by
    intro w _
    exact ((hg w (Set.mem_univ w)).continuousAt.continuousWithinAt).norm
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont
  set M : ℝ := max 1 M₀ with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMlognn : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hunit : ∀ z : ℂ, ‖z‖ ≤ 1 → Real.log ‖g z‖ ≤ Real.log M := by
    intro z hz
    have hmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    rcases eq_or_lt_of_le (norm_nonneg (g z)) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact hMlognn
    · refine Real.log_le_log h0 ?_
      have hb := hM₀ z hmem
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
      exact le_trans hb (le_max_right _ _)
  -- the eventual bound
  have hMev : ∀ᶠ r : ℝ in atTop, Real.log M ≤ ε * (Real.log r) ^ (2 : ℕ) := by
    have htend : Tendsto (fun r : ℝ => ε * (Real.log r) ^ (2 : ℕ)) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop hε ?_
      exact (tendsto_pow_atTop (n := 2) (by norm_num)).comp Real.tendsto_log_atTop
    exact htend.eventually_ge_atTop (Real.log M)
  filter_upwards [hq ε hε, hMev, eventually_ge_atTop (1 : ℝ)] with r hr hrM hr1 z hz
  by_cases hzu : ‖z‖ ≤ 1
  · exact le_trans (hunit z hzu) hrM
  · have hz1 : (1 : ℝ) < ‖z‖ := lt_of_not_ge hzu
    have hzne : z ≠ 0 := by
      intro h
      rw [h] at hz1
      simp only [norm_zero] at hz1
      linarith
    rcases eq_or_lt_of_le (norm_nonneg (g z)) with h0 | h0
    · rw [← h0, Real.log_zero]
      positivity
    · have hfz : ‖f z‖ = ‖z‖ ^ m * ‖g z‖ := by
        rw [hfac z, norm_mul, norm_pow]
      have hfpos : (0 : ℝ) < ‖f z‖ := by
        rw [hfz]
        have : (0 : ℝ) < ‖z‖ ^ m := by positivity
        positivity
      have hlogf : Real.log ‖f z‖ = (m : ℝ) * Real.log ‖z‖ + Real.log ‖g z‖ := by
        rw [hfz, Real.log_mul (by positivity) h0.ne', Real.log_pow]
      have hlogznn : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz1.le
      have hfle := hr z hz
      nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- **The card's equation (2).**  An entire function of quadratic subtype zero that is nowhere
locally zero is `c · z^m` times the genus-zero canonical product over its nonzero zero divisor. -/
theorem exists_monomial_const_mul_genusZeroProduct (hf : AnalyticOnNhd ℂ f Set.univ)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤) (hq : QuadraticSubtypeZero f) :
    ∃ (m : ℕ) (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g Set.univ ∧ g 0 ≠ 0 ∧
      (∀ z, analyticOrderAt g z = analyticOrderAt f z ∨ z = 0) ∧
      (∀ z, f z = z ^ m * (c * genusZeroProductIdx (zeroCopyPoint g) z)) := by
  obtain ⟨g, hgan, hg0, hgord, hgfac⟩ := exists_monomial_factorization hf hford
  have hgq : QuadraticSubtypeZero g :=
    quadraticSubtypeZero_of_monomial_quotient hgan hq hgfac
  have hgford : ∀ z, analyticOrderAt g z ≠ ⊤ := by
    intro z
    rcases hgord z with h | h
    · rw [h]; exact hford z
    · subst h
      rw [(hgan 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr hg0]
      exact ENat.coe_ne_top 0
  obtain ⟨c, hc, hcfac⟩ := exists_const_mul_genusZeroProduct hgan hg0 hgford hgq
  refine ⟨(analyticOrderAt f 0).toNat, c, g, hc, hgan, hg0, hgord, fun z => ?_⟩
  rw [hgfac z, hcfac z]

end GaloisForLFunctions.QuadraticSubtypeHadamard
