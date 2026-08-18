import GaloisForLFunctions.HTGeometry.KolmogorovMaximalInequality

/-!
# Almost sure convergence of a centred coordinatewise series

If the terms of a coordinatewise series on a countable product of probability spaces are centred,
bounded and square summable in mean, the series converges almost everywhere.

This is Kolmogorov's convergence criterion.  The textbook routes go through the three-series
theorem or through Itô–Nisio; neither exists in mathlib and both need stopping times.  The route
here is the classical one: the maximal inequality of `KolmogorovMaximalInequality` applied to the
tail starting at `M` bounds the probability that the tail oscillation ever reaches `λ` by
`λ⁻²· ∑_{n ≥ M} E‖g n‖²`, and Borel–Cantelli along a sequence of cuts where that tail is
geometrically small makes the partial sums almost surely Cauchy.

The orthogonality identity `E‖S N‖² = ∑_{n < N} E‖g n‖²` is the other ingredient: independent
centred terms have no cross correlation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] (g : ∀ n, X n → ℂ)
variable (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
variable {c : ℕ → ℝ}

/-! ### Orthogonality of centred coordinate terms -/

/-- Distinct centred coordinate terms are uncorrelated. -/
theorem integral_coordTerm_mul_conj (hg : ∀ n, Measurable (g n)) (_hbdd : ∀ n y, ‖g n y‖ ≤ c n)
    (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, g m (x m) * (starRingEnd ℂ) (g n (x n)) ∂(Measure.infinitePi μ) = 0 := by
  have hbase : IndepFun (fun x : ∀ i, X i => x m) (fun x : ∀ i, X i => x n)
      (Measure.infinitePi μ) :=
    (iIndepFun_infinitePi (X := fun (i : ℕ) (ω : X i) => ω) fun _ => measurable_id).indepFun hmn
  have hind : IndepFun (fun x : ∀ i, X i => g m (x m))
      (fun x : ∀ i, X i => (starRingEnd ℂ) (g n (x n))) (Measure.infinitePi μ) :=
    hbase.comp (hg m) (continuous_star.measurable.comp (hg n))
  rw [hind.integral_fun_mul_eq_mul_integral
    ((hg m).comp (measurable_pi_apply m)).aestronglyMeasurable
    ((continuous_star.measurable.comp (hg n)).comp (measurable_pi_apply n)).aestronglyMeasurable]
  rw [integral_coordTerm g μ hg m, hmean m, zero_mul]

/-- The mean square of one coordinate term. -/
theorem integral_coordTerm_normSq (hg : ∀ n, Measurable (g n)) (_hbdd : ∀ n y, ‖g n y‖ ≤ c n)
    (n : ℕ) :
    ∫ x, ‖g n (x n)‖ ^ 2 ∂(Measure.infinitePi μ) = ∫ y, ‖g n y‖ ^ 2 ∂(μ n) := by
  have hmap : Measure.map (fun x : ∀ m, X m => x n) (Measure.infinitePi μ) = μ n :=
    Measure.infinitePi_map_eval μ n
  have h : ∫ y, ‖g n y‖ ^ 2 ∂(Measure.map (fun x : ∀ m, X m => x n) (Measure.infinitePi μ))
      = ∫ x, ‖g n (x n)‖ ^ 2 ∂(Measure.infinitePi μ) :=
    integral_map (measurable_pi_apply n).aemeasurable
      (by rw [hmap]; exact ((hg n).norm.pow_const 2).aestronglyMeasurable)
  rw [hmap] at h
  exact h.symm

/-- **The mean square of the partial sums is the sum of the mean squares.** -/
theorem integral_normSq_coordPartialSum (hg : ∀ n, Measurable (g n))
    (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0) (N : ℕ) :
    ∫ x, ‖coordPartialSum g N x‖ ^ 2 ∂(Measure.infinitePi μ)
      = ∑ n ∈ Finset.range N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n) := by
  classical
  set ν := Measure.infinitePi μ with hν
  have hterm : ∀ k : ℕ, Integrable (fun x : ∀ i, X i => g k (x k)) ν := fun k =>
    integrable_of_norm_le μ ((hg k).comp (measurable_pi_apply k)) fun x => hbdd k (x k)
  have hprod : ∀ k l : ℕ,
      Integrable (fun x : ∀ i, X i => g k (x k) * (starRingEnd ℂ) (g l (x l))) ν := by
    intro k l
    refine integrable_of_norm_le μ (((hg k).comp (measurable_pi_apply k)).mul
      ((continuous_star.measurable.comp (hg l)).comp (measurable_pi_apply l)))
      (C := c k * c l) fun x => ?_
    rw [norm_mul, RCLike.norm_conj]
    have hck : (0 : ℝ) ≤ c k := le_trans (norm_nonneg _) (hbdd k (x k))
    exact mul_le_mul (hbdd k (x k)) (hbdd l (x l)) (norm_nonneg _) hck
  have hexpand : ∀ x : ∀ i, X i, ((‖coordPartialSum g N x‖ ^ 2 : ℝ) : ℂ)
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          g k (x k) * (starRingEnd ℂ) (g l (x l)) := by
    intro x
    have h1 : ((‖coordPartialSum g N x‖ ^ 2 : ℝ) : ℂ)
        = coordPartialSum g N x * (starRingEnd ℂ) (coordPartialSum g N x) := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [h1]
    show (∑ k ∈ Finset.range N, g k (x k)) * (starRingEnd ℂ) (∑ l ∈ Finset.range N, g l (x l)) = _
    rw [map_sum, Finset.sum_mul_sum]
  have hcast : ∫ x, ‖coordPartialSum g N x‖ ^ 2 ∂ν
      = (∫ x, ((‖coordPartialSum g N x‖ ^ 2 : ℝ) : ℂ) ∂ν).re := by
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [hcast, integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  rw [integral_finsetSum (f := fun k (x : ∀ i, X i) =>
      ∑ l ∈ Finset.range N, g k (x k) * (starRingEnd ℂ) (g l (x l))) _
    fun k _ => integrable_finsetSum _ fun l _ => hprod k l]
  have hinner : ∀ k ∈ Finset.range N,
      ∫ x, ∑ l ∈ Finset.range N, g k (x k) * (starRingEnd ℂ) (g l (x l)) ∂ν
        = ((∫ y, ‖g k y‖ ^ 2 ∂(μ k) : ℝ) : ℂ) := by
    intro k hk
    rw [integral_finsetSum (f := fun l (x : ∀ i, X i) =>
      g k (x k) * (starRingEnd ℂ) (g l (x l))) _ fun l _ => hprod k l]
    have hz : ∀ l ∈ Finset.range N,
        ∫ x, g k (x k) * (starRingEnd ℂ) (g l (x l)) ∂ν
          = if l = k then ((∫ y, ‖g k y‖ ^ 2 ∂(μ k) : ℝ) : ℂ) else 0 := by
      intro l _
      rcases eq_or_ne l k with rfl | hlk
      · rw [if_pos rfl]
        have hpt : ∀ x : ∀ i, X i, g l (x l) * (starRingEnd ℂ) (g l (x l))
            = ((‖g l (x l)‖ ^ 2 : ℝ) : ℂ) := by
          intro x
          rw [Complex.mul_conj']
          push_cast
          ring
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal,
          integral_coordTerm_normSq g μ hg hbdd l]
      · rw [if_neg hlk, integral_coordTerm_mul_conj g μ hg hbdd hmean (Ne.symm hlk)]
    rw [Finset.sum_congr rfl hz, Finset.sum_ite_eq' (Finset.range N) k
      (fun _ => ((∫ y, ‖g k y‖ ^ 2 ∂(μ k) : ℝ) : ℂ)), if_pos hk]
  rw [Finset.sum_congr rfl hinner, ← Complex.ofReal_sum]
  simp


/-! ### The tail oscillation bound -/

/-- The series with its first `M` terms deleted. -/
def shiftTerms (g : ∀ n, X n → ℂ) (M : ℕ) : ∀ n, X n → ℂ :=
  fun n => if n < M then 0 else g n

omit [∀ n, MeasurableSpace (X n)] in
theorem coordPartialSum_shiftTerms {M N : ℕ} (hMN : M ≤ N) (x : ∀ m, X m) :
    coordPartialSum (shiftTerms g M) N x
      = coordPartialSum g N x - coordPartialSum g M x := by
  rw [coordPartialSum_sub_eq_sum_Ico g hMN]
  show ∑ n ∈ Finset.range N, shiftTerms g M n (x n) = _
  have hsplit : (∑ n ∈ Finset.Ico 0 M, shiftTerms g M n (x n))
      + ∑ n ∈ Finset.Ico M N, shiftTerms g M n (x n)
      = ∑ n ∈ Finset.Ico 0 N, shiftTerms g M n (x n) :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le M) hMN
  rw [Finset.range_eq_Ico, ← hsplit]
  have hzero : ∑ n ∈ Finset.Ico 0 M, shiftTerms g M n (x n) = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [shiftTerms, if_pos (Finset.mem_Ico.mp hn).2]; rfl
  rw [hzero, zero_add]
  exact Finset.sum_congr rfl fun n hn => by
    rw [shiftTerms, if_neg (not_lt.mpr (Finset.mem_Ico.mp hn).1)]

theorem measurable_shiftTerms (hg : ∀ n, Measurable (g n)) (M : ℕ) :
    ∀ n, Measurable (shiftTerms g M n) := by
  intro n
  rw [shiftTerms]
  by_cases h : n < M
  · rw [if_pos h]; exact measurable_const
  · rw [if_neg h]; exact hg n

omit [∀ n, MeasurableSpace (X n)] in
theorem norm_shiftTerms_le (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hc : ∀ n, 0 ≤ c n) (M : ℕ) :
    ∀ n y, ‖shiftTerms g M n y‖ ≤ c n := by
  intro n y
  rw [shiftTerms]
  by_cases h : n < M
  · rw [if_pos h]; simpa using hc n
  · rw [if_neg h]; exact hbdd n y

omit [∀ n, IsProbabilityMeasure (μ n)] in
theorem integral_shiftTerms (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0) (M : ℕ) :
    ∀ n, ∫ y, shiftTerms g M n y ∂(μ n) = 0 := by
  intro n
  rw [shiftTerms]
  by_cases h : n < M
  · rw [if_pos h]; simp
  · rw [if_neg h]; exact hmean n

omit [∀ n, IsProbabilityMeasure (μ n)] in
theorem integral_normSq_shiftTerms (M : ℕ) (n : ℕ) :
    ∫ y, ‖shiftTerms g M n y‖ ^ 2 ∂(μ n)
      = if n < M then 0 else ∫ y, ‖g n y‖ ^ 2 ∂(μ n) := by
  rw [shiftTerms]
  by_cases h : n < M
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]

/-- **The tail oscillation bound.**  The probability that the tail of the series starting at `M`
ever moves by `lam` is at most `lam⁻²` times the tail of the mean squares. -/
theorem measure_tail_oscillation_le (hg : ∀ n, Measurable (g n)) (hbdd : ∀ n y, ‖g n y‖ ≤ c n)
    (hc : ∀ n, 0 ≤ c n) (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0)
    (hsum : Summable fun n => ∫ y, ‖g n y‖ ^ 2 ∂(μ n)) (a : ∀ m, X m) (M : ℕ)
    {lam : ℝ} (hlam : 0 < lam) :
    Measure.infinitePi μ {x | ∃ n, lam ≤ ‖coordPartialSum (shiftTerms g M) n x‖}
      ≤ ENNReal.ofReal ((∑' k, ∫ y, ‖g (k + M) y‖ ^ 2 ∂(μ (k + M))) / lam ^ 2) := by
  classical
  set ν := Measure.infinitePi μ with hν
  set T := ∑' k, ∫ y, ‖g (k + M) y‖ ^ 2 ∂(μ (k + M)) with hT
  have hnn : ∀ n, 0 ≤ ∫ y, ‖g n y‖ ^ 2 ∂(μ n) := fun n =>
    integral_nonneg fun y => by positivity
  have hsumshift : Summable fun k => ∫ y, ‖g (k + M) y‖ ^ 2 ∂(μ (k + M)) :=
    (summable_nat_add_iff M).mpr hsum
  -- the finite-level bound
  have hlevel : ∀ N : ℕ,
      ν {x | ∃ n ≤ N, lam ≤ ‖coordPartialSum (shiftTerms g M) n x‖} ≤ ENNReal.ofReal (T / lam ^ 2) := by
    intro N
    have hkol := kolmogorov_maximal_inequality (shiftTerms g M) μ a
      (measurable_shiftTerms g hg M) (norm_shiftTerms_le g hbdd hc M)
      (integral_shiftTerms g μ hmean M) N hlam
    have hms := integral_normSq_coordPartialSum (shiftTerms g M) μ
      (measurable_shiftTerms g hg M) (norm_shiftTerms_le g hbdd hc M)
      (integral_shiftTerms g μ hmean M) N
    have hsumeq : ∑ n ∈ Finset.range N, ∫ y, ‖shiftTerms g M n y‖ ^ 2 ∂(μ n)
        = ∑ n ∈ Finset.Ico M N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n) := by
      rcases le_or_gt M N with hMN | hMN
      · have hsplit : (∑ n ∈ Finset.Ico 0 M, ∫ y, ‖shiftTerms g M n y‖ ^ 2 ∂(μ n))
            + ∑ n ∈ Finset.Ico M N, ∫ y, ‖shiftTerms g M n y‖ ^ 2 ∂(μ n)
            = ∑ n ∈ Finset.Ico 0 N, ∫ y, ‖shiftTerms g M n y‖ ^ 2 ∂(μ n) :=
          Finset.sum_Ico_consecutive _ (Nat.zero_le M) hMN
        rw [Finset.range_eq_Ico, ← hsplit]
        have hzero : ∑ n ∈ Finset.Ico 0 M, ∫ y, ‖shiftTerms g M n y‖ ^ 2 ∂(μ n) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            rw [integral_normSq_shiftTerms g μ M n, if_pos (Finset.mem_Ico.mp hn).2]
        rw [hzero, zero_add]
        exact Finset.sum_congr rfl fun n hn => by
          rw [integral_normSq_shiftTerms g μ M n, if_neg (not_lt.mpr (Finset.mem_Ico.mp hn).1)]
      · rw [Finset.Ico_eq_empty_of_le (le_of_lt hMN), Finset.sum_empty]
        exact Finset.sum_eq_zero fun n hn => by
          rw [integral_normSq_shiftTerms g μ M n,
            if_pos (lt_trans (Finset.mem_range.mp hn) hMN)]
    have hbound : ∑ n ∈ Finset.Ico M N, ∫ y, ‖g n y‖ ^ 2 ∂(μ n) ≤ T := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm M k])) ?_
      exact hsumshift.sum_le_tsum _ (fun k _ => hnn _)
    have hfinal : lam ^ 2 * (ν {x | ∃ n ≤ N, lam ≤ ‖coordPartialSum (shiftTerms g M) n x‖}).toReal
        ≤ T := by
      refine le_trans hkol ?_
      rw [hms, hsumeq]
      exact hbound
    have hmle : (ν {x | ∃ n ≤ N, lam ≤ ‖coordPartialSum (shiftTerms g M) n x‖}).toReal
        ≤ T / lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hfinal]
    have hfin : ν {x | ∃ n ≤ N, lam ≤ ‖coordPartialSum (shiftTerms g M) n x‖} ≠ ⊤ :=
      measure_ne_top ν _
    rwa [← ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)]
  -- pass to the limit
  have hmono : Monotone fun N : ℕ =>
      {x : ∀ m, X m | ∃ n ≤ N, lam ≤ ‖coordPartialSum (shiftTerms g M) n x‖} := by
    intro N N' hNN' x hx
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨n, hn.trans hNN', hx⟩
  have hunion : (⋃ N : ℕ, {x : ∀ m, X m | ∃ n ≤ N, lam ≤ ‖coordPartialSum (shiftTerms g M) n x‖})
      = {x | ∃ n, lam ≤ ‖coordPartialSum (shiftTerms g M) n x‖} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun ⟨_, n, _, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n, n, le_refl n, h⟩⟩
  have htend := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hunion] at htend
  exact le_of_tendsto htend (Filter.Eventually.of_forall hlevel)


/-! ### Almost sure convergence -/

/-- **Kolmogorov's convergence criterion.**  A centred, bounded, mean-square summable
coordinatewise series on a countable product of probability spaces converges almost everywhere. -/
theorem measure_coordSeriesConverges_eq_one (hg : ∀ n, Measurable (g n))
    (hbdd : ∀ n y, ‖g n y‖ ≤ c n) (hc : ∀ n, 0 ≤ c n)
    (hmean : ∀ n, ∫ y, g n y ∂(μ n) = 0)
    (hsum : Summable fun n => ∫ y, ‖g n y‖ ^ 2 ∂(μ n)) (a : ∀ m, X m) :
    Measure.infinitePi μ (coordSeriesConverges g) = 1 := by
  classical
  set ν := Measure.infinitePi μ with hν
  set T : ℕ → ℝ := fun M => ∑' k, ∫ y, ‖g (k + M) y‖ ^ 2 ∂(μ (k + M)) with hTdef
  have hT0 : Tendsto T atTop (𝓝 0) := by
    rw [hTdef]
    exact tendsto_sum_nat_add fun n => ∫ y, ‖g n y‖ ^ 2 ∂(μ n)
  have hchoice : ∀ k : ℕ, ∃ M : ℕ, T M ≤ (1 / 8 : ℝ) ^ k := by
    intro k
    obtain ⟨M, hM⟩ := (hT0.eventually (gt_mem_nhds (by positivity : (0:ℝ) < (1/8:ℝ) ^ k))).exists
    exact ⟨M, le_of_lt hM⟩
  choose m hm using hchoice
  set B : ℕ → Set (∀ i, X i) := fun k =>
    {x | ∃ n, (1 / 2 : ℝ) ^ k ≤ ‖coordPartialSum (shiftTerms g (m k)) n x‖} with hBdef
  have hBle : ∀ k, ν (B k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    refine le_trans (measure_tail_oscillation_le g μ hg hbdd hc hmean hsum a (m k)
      (by positivity : (0:ℝ) < (1/2:ℝ) ^ k)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (by positivity)]
    calc T (m k) ≤ (1 / 8 : ℝ) ^ k := hm k
      _ = (1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k) ^ 2 := by
          rw [← pow_mul, ← pow_add, show (1/8:ℝ) = (1/2:ℝ) ^ (3:ℕ) by norm_num, ← pow_mul]
          congr 1
          omega
  have hfin : ∑' k, ν (B k) ≠ ⊤ := by
    have hgeo : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hle : ∑' k, ν (B k) ≤ ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
      ENNReal.tsum_le_tsum hBle
    have heq : ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k)
        = ENNReal.ofReal (∑' k, (1 / 2 : ℝ) ^ k) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeo).symm
    rw [heq] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hlimsup : ν (Filter.limsup B atTop) = 0 := measure_limsup_atTop_eq_zero hfin
  have hae : ∀ᵐ x ∂ν, x ∈ coordSeriesConverges g := by
    have hnotmem : ∀ᵐ x ∂ν, x ∉ Filter.limsup B atTop := by
      rw [ae_iff]
      simpa using hlimsup
    filter_upwards [hnotmem] with x hx
    have hev : ∀ᶠ k in atTop, x ∉ B k :=
      Filter.not_frequently.mp fun h => hx (Filter.mem_limsup_iff_frequently_mem.mpr h)
    obtain ⟨k₀, hk₀⟩ := hev.exists_forall_of_atTop
    have hcauchy : CauchySeq fun N => coordPartialSum g N x := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      obtain ⟨k, hk2, hk1⟩ :=
        ((hpow.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop k₀)).exists
      refine ⟨m k, fun n hn => ?_⟩
      have hxB : x ∉ B k := hk₀ k hk1
      have hlt : ‖coordPartialSum (shiftTerms g (m k)) n x‖ < (1 / 2 : ℝ) ^ k := by
        by_contra hcon
        exact hxB ⟨n, not_lt.mp hcon⟩
      rw [coordPartialSum_shiftTerms g hn] at hlt
      rw [dist_eq_norm]
      exact lt_trans hlt hk2
    exact cauchySeq_tendsto_of_complete hcauchy
  exact (prob_compl_eq_zero_iff (measurableSet_coordSeriesConverges g hg)).mp (ae_iff.mp hae)

end GaloisForLFunctions.HTGeometry

end
