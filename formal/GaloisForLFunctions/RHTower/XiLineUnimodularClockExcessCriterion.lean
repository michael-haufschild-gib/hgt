import GaloisForLFunctions.RHTower.XiHolomorphicTwoPrimePencilGrowthDichotomy

/-!
# Every entire clock unimodular on the critical line: the excess criterion

Let `Λ` be entire with `‖Λ(1/2 + it)‖ = 1` for all real `t`.  The function
`s ↦ Λ(s) · conj Λ(1 − conj s)` is entire and equals `‖Λ‖² = 1` on the critical line, so by the
identity theorem

`Λ(s) · conj Λ(1 − conj s) = 1`  for every `s`.

Hence the two partners of a reflection orbit have reciprocal clock moduli, and if one of them is
unimodular they have the same clock value.

For a finite strip window of Xi zeros put `P(n) = Σ_ρ m_ρ Λ(ρ)^n` and let the excess be the Cesàro
mean of `‖P(n)‖²` minus the local square sum `Σ_ρ m_ρ²`.  Then:

* if some zero of the window has `‖Λ(ρ)‖ ≠ 1`, the excess is not eventually bounded;
* if every zero is `Λ`-unimodular, the excess converges to the aliasing charge
  `Σ_u (Σ_{Λ(ρ)=u} m_ρ)² − Σ_ρ m_ρ²`, and every off-line zero adds at least `2` to it.

So for every such clock an eventual excess bound below `2` forces the whole window onto the critical
line.  The collision quantum survives exactly on the unimodular set `{‖Λ‖ = 1}`; off that set a free
orbit becomes exponential growth.  For the prime clocks `p^{s−1/2}` that set is the critical line.
-/

open Complex Set Metric Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The reflection law for line-unimodular entire clocks -/

theorem lineReflect_eq_conj_one_sub (s : ℂ) : lineReflect s = starRingEnd ℂ (1 - s) := by
  simp [lineReflect, map_sub, map_one]

theorem lineReflect_half_add_mul_I (t : ℝ) :
    lineReflect ((1 / 2 : ℂ) + t * I) = (1 / 2 : ℂ) + t * I := by
  apply Complex.ext <;> simp [lineReflect] <;> norm_num

/-- **Reflection law.**  An entire clock of modulus one on the critical line satisfies
`Λ(s) · conj Λ(1 − conj s) = 1` everywhere. -/
theorem lineUnimodularClock_mul_conj_lineReflect {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hline : ∀ t : ℝ, ‖Λ ((1 / 2 : ℂ) + t * I)‖ = 1) (s : ℂ) :
    Λ s * starRingEnd ℂ (Λ (lineReflect s)) = 1 := by
  let g : ℂ → ℂ := fun s => Λ s * starRingEnd ℂ (Λ (lineReflect s))
  have hstar : Differentiable ℂ (fun w => starRingEnd ℂ (Λ (starRingEnd ℂ w))) := by
    intro w
    have h := (hΛ (starRingEnd ℂ w)).conj_conj
    simpa [Function.comp_def] using h
  have hg : Differentiable ℂ g := by
    have hcomp : Differentiable ℂ (fun s : ℂ => starRingEnd ℂ (Λ (starRingEnd ℂ (1 - s)))) :=
      hstar.comp ((differentiable_const 1).sub differentiable_id)
    have heq : (fun s : ℂ => starRingEnd ℂ (Λ (lineReflect s))) =
        fun s : ℂ => starRingEnd ℂ (Λ (starRingEnd ℂ (1 - s))) := by
      funext s
      rw [lineReflect_eq_conj_one_sub]
    have hcomp' : Differentiable ℂ (fun s : ℂ => starRingEnd ℂ (Λ (lineReflect s))) := by
      rw [heq]
      exact hcomp
    exact hΛ.mul hcomp'
  have hline_g : ∀ t : ℝ, g ((1 / 2 : ℂ) + t * I) = 1 := by
    intro t
    simp only [g]
    rw [lineReflect_half_add_mul_I, Complex.mul_conj, Complex.normSq_eq_norm_sq, hline t]
    norm_num
  have hanalytic : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) univ := fun z _ => analyticAt_const
  have hseq : Tendsto (fun n : ℕ => (1 / 2 : ℂ) + (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) * I)
      atTop (𝓝[≠] (1 / 2 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun n : ℕ => ((((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) * I)) atTop
          (𝓝 ((0 : ℂ) * I)) :=
        ((Complex.continuous_ofReal.tendsto 0).comp h0).mul tendsto_const_nhds
      simpa using tendsto_const_nhds.add h1
    · refine Eventually.of_forall fun n => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left, mul_eq_zero,
        Complex.ofReal_eq_zero, Complex.I_ne_zero, or_false]
      positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 / 2 : ℂ), g z = (fun _ : ℂ => (1 : ℂ)) z :=
    hseq.frequently (Frequently.of_forall fun n => hline_g _)
  exact hanalytic.eqOn_of_preconnected_of_frequently_eq hconst isPreconnected_univ
    (mem_univ _) hfreq (mem_univ s)

/-- Reflection partners have reciprocal clock moduli. -/
theorem norm_lineUnimodularClock_mul_lineReflect {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hline : ∀ t : ℝ, ‖Λ ((1 / 2 : ℂ) + t * I)‖ = 1) (s : ℂ) :
    ‖Λ s‖ * ‖Λ (lineReflect s)‖ = 1 := by
  have h := congrArg norm (lineUnimodularClock_mul_conj_lineReflect hΛ hline s)
  rwa [norm_mul, Complex.norm_conj, norm_one] at h

/-- A unimodular point and its reflection partner carry the same clock value. -/
theorem lineUnimodularClock_lineReflect_eq_of_norm_eq_one {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hline : ∀ t : ℝ, ‖Λ ((1 / 2 : ℂ) + t * I)‖ = 1) {s : ℂ} (hs : ‖Λ s‖ = 1) :
    Λ (lineReflect s) = Λ s := by
  have h1 := lineUnimodularClock_mul_conj_lineReflect hΛ hline s
  have h2 : Λ s * starRingEnd ℂ (Λ s) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hs]
    norm_num
  have hne : Λ s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hs
    exact zero_ne_one hs
  have hc : starRingEnd ℂ (Λ (lineReflect s)) = starRingEnd ℂ (Λ s) :=
    mul_left_cancel₀ hne (h1.trans h2.symm)
  simpa using congrArg (starRingEnd ℂ) hc

/-! ## Window pencils of an arbitrary clock -/

/-- The one-clock window pencil `P(n) = Σ_ρ m_ρ Λ(ρ)^n`. -/
def xiClockPencil (Λ : ℂ → ℂ) (T : ℝ) (n : ℕ) : ℂ :=
  finiteExponentialPencil (stripZeros_finite T).toFinset
    (fun rho => ((analyticOrderAt xi rho).toNat : ℂ)) Λ n

/-- Cesàro energy of the clock pencil minus the local square sum. -/
def xiClockExcess (Λ : ℂ → ℂ) (T : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖xiClockPencil Λ T n‖ ^ (2 : ℕ) -
    xiStripWindowLocalSquareSum T

theorem one_le_xi_order_toNat_of_mem_stripZeros {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ (stripZeros_finite T).toFinset) :
    1 ≤ (analyticOrderAt xi rho).toNat :=
  Nat.one_le_iff_ne_zero.mpr
    (xi_order_toNat_ne_zero ((stripZeros_finite T).mem_toFinset.mp hrho).2)

/-- **Off the unimodular set: growth.**  If some zero of the window has clock modulus different
from one, the clock excess is not eventually bounded. -/
theorem not_eventually_bounded_xiClockExcess {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hline : ∀ t : ℝ, ‖Λ ((1 / 2 : ℂ) + t * I)‖ = 1) {T : ℝ}
    (hoff : ∃ rho ∈ (stripZeros_finite T).toFinset, ‖Λ rho‖ ≠ 1) :
    ¬ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, xiClockExcess Λ T N ≤ C := by
  classical
  set S := (stripZeros_finite T).toFinset with hS
  let c : ℂ → ℂ := fun rho => ((analyticOrderAt xi rho).toNat : ℂ)
  obtain ⟨rho₀, hrho₀S, hrho₀⟩ := hoff
  have hbig : ∃ rho ∈ S, 1 < ‖Λ rho‖ := by
    rcases lt_or_gt_of_ne hrho₀ with hlt | hgt
    · refine ⟨lineReflect rho₀, ?_, ?_⟩
      · rw [hS, Set.Finite.mem_toFinset]
        exact lineReflect_mem_stripZeros ((stripZeros_finite T).mem_toFinset.mp hrho₀S)
      · have hprod := norm_lineUnimodularClock_mul_lineReflect hΛ hline rho₀
        by_contra hle
        push Not at hle
        have := mul_le_of_le_one_right (norm_nonneg (Λ rho₀)) hle
        linarith
    · exact ⟨rho₀, hrho₀S, hgt⟩
  obtain ⟨rho₁, hrho₁S, hrho₁⟩ := hbig
  obtain ⟨rmax, hrmaxS, hrmax⟩ := S.exists_max_image (fun rho => ‖Λ rho‖) ⟨rho₁, hrho₁S⟩
  set r := ‖Λ rmax‖ with hr
  have hr1 : 1 < r := lt_of_lt_of_le hrho₁ (hrmax rho₁ hrho₁S)
  have hr0 : 0 < r := by linarith
  have hfiber : ∃ u ∈ (S.filter fun i => ‖Λ i‖ = r).image (fun i => Λ i / (r : ℂ)),
      finiteExponentialFiberCoefficient (S.filter fun i => ‖Λ i‖ = r) c
        (fun i => Λ i / (r : ℂ)) u ≠ 0 := by
    refine ⟨Λ rmax / (r : ℂ), Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hrmaxS, rfl⟩), ?_⟩
    unfold finiteExponentialFiberCoefficient
    have hcast : (∑ i ∈ (S.filter fun i => ‖Λ i‖ = r) with
          Λ i / (r : ℂ) = Λ rmax / (r : ℂ), c i) =
        (((∑ i ∈ (S.filter fun i => ‖Λ i‖ = r) with
          Λ i / (r : ℂ) = Λ rmax / (r : ℂ), (analyticOrderAt xi i).toNat : ℕ) : ℂ)) := by
      push_cast
      rfl
    rw [hcast, Nat.cast_ne_zero]
    have hmem : rmax ∈ (S.filter fun i => ‖Λ i‖ = r).filter
        (fun i => Λ i / (r : ℂ) = Λ rmax / (r : ℂ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hrmaxS, rfl⟩, rfl⟩
    have hpos := one_le_xi_order_toNat_of_mem_stripZeros hrmaxS
    have hle := Finset.single_le_sum
      (f := fun i => (analyticOrderAt xi i).toNat) (fun i _ => Nat.zero_le _) hmem
    omega
  have hnot := not_tendsto_normalized_finitePencil_of_dominantFiber S c Λ hr0
    (fun i hi => hrmax i hi) hfiber
  have hfreq : ∃ ε > 0, ∃ᶠ n : ℕ in atTop,
      ε ≤ ‖∑ i ∈ S, c i * (Λ i / (r : ℂ)) ^ n‖ := by
    by_contra hcon
    push Not at hcon
    apply hnot
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(hcon ε hε).mono fun n hn => hn] with n hn
    simpa [dist_zero_right] using hn
  obtain ⟨ε, hε, hfreqε⟩ := hfreq
  have hscale (n : ℕ) : ‖xiClockPencil Λ T n‖ =
      r ^ n * ‖∑ i ∈ S, c i * (Λ i / (r : ℂ)) ^ n‖ := by
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have : xiClockPencil Λ T n = (r : ℂ) ^ n * ∑ i ∈ S, c i * (Λ i / (r : ℂ)) ^ n := by
      unfold xiClockPencil finiteExponentialPencil
      rw [Finset.mul_sum, ← hS]
      apply Finset.sum_congr rfl
      intro i _
      rw [div_pow]
      field_simp
      exact mul_comm _ _
    rw [this, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hexcess (n : ℕ) : ((n + 1 : ℕ) : ℝ)⁻¹ * ‖xiClockPencil Λ T n‖ ^ 2 -
      xiStripWindowLocalSquareSum T ≤ xiClockExcess Λ T (n + 1) := by
    unfold xiClockExcess
    have h1 : ‖xiClockPencil Λ T n‖ ^ 2 ≤
        ∑ k ∈ Finset.range (n + 1), ‖xiClockPencil Λ T k‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun k => ‖xiClockPencil Λ T k‖ ^ (2 : ℕ))
        (fun k _ => sq_nonneg _) (Finset.self_mem_range_succ n)
    have hw : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left h1 hw
    linarith
  rintro ⟨C, hC⟩
  set L : ℝ := (xiStripWindowLocalSquareSum T : ℝ)
  have hr2 : 1 < r ^ 2 := by nlinarith
  have hpoly : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (r ^ 2) ^ n) atTop (nhds 0) := by
    have hbase := tendsto_pow_const_div_const_pow_of_one_lt 1 hr2
    have hshift := hbase.comp (tendsto_add_atTop_nat 1)
    have hmul := hshift.const_mul (r ^ 2)
    rw [mul_zero] at hmul
    refine hmul.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_one]
    field_simp
    ring
  have hK : 0 < ε ^ 2 / (|C| + |L| + 1) := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) / (r ^ 2) ^ n < ε ^ 2 / (|C| + |L| + 1) :=
    (tendsto_order.mp hpoly).2 _ hK
  have hCshift : ∀ᶠ n : ℕ in atTop, xiClockExcess Λ T (n + 1) ≤ C :=
    (tendsto_add_atTop_nat 1).eventually hC
  obtain ⟨n, hnε, hnsmall, hnC⟩ := (hfreqε.and_eventually (hsmall.and hCshift)).exists
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hlower : ε ^ 2 * (r ^ 2) ^ n ≤ ‖xiClockPencil Λ T n‖ ^ 2 := by
    rw [hscale, mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]
    have := pow_le_pow_left₀ hε.le hnε 2
    nlinarith [pow_pos hr0 n, sq_nonneg (r ^ n)]
  have hbig : |C| + |L| + 1 < ε ^ 2 * (r ^ 2) ^ n / ((n : ℝ) + 1) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hnsmall
    rw [lt_div_iff₀ hden]
    nlinarith
  have hex := hexcess n
  have hcastn : ((n + 1 : ℕ) : ℝ)⁻¹ = 1 / ((n : ℝ) + 1) := by
    push_cast
    rw [one_div]
  rw [hcastn] at hex
  have hdivle : ε ^ 2 * (r ^ 2) ^ n / ((n : ℝ) + 1) ≤
      1 / ((n : ℝ) + 1) * ‖xiClockPencil Λ T n‖ ^ 2 := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hlower hden.le
  have hCabs : C ≤ |C| := le_abs_self C
  have hLabs : L ≤ |L| := le_abs_self L
  linarith

/-! ## On the unimodular set: the aliasing charge -/

/-- Aliasing charge of the window: squared clock-fibre multiplicities minus local squares. -/
def xiClockAliasingCharge (Λ : ℂ → ℂ) (T : ℝ) : ℝ :=
  ∑ u ∈ (stripZeros_finite T).toFinset.image Λ,
      ‖finiteExponentialFiberCoefficient (stripZeros_finite T).toFinset
        (fun rho => ((analyticOrderAt xi rho).toNat : ℂ)) Λ u‖ ^ (2 : ℕ) -
    xiStripWindowLocalSquareSum T

/-- **On the unimodular set: convergence.**  If every zero of the window is `Λ`-unimodular, the
clock excess converges to the aliasing charge. -/
theorem tendsto_xiClockExcess_aliasingCharge {Λ : ℂ → ℂ} {T : ℝ}
    (hunit : ∀ rho ∈ (stripZeros_finite T).toFinset, ‖Λ rho‖ = 1) :
    Tendsto (xiClockExcess Λ T) atTop (nhds (xiClockAliasingCharge Λ T)) := by
  classical
  set S := (stripZeros_finite T).toFinset with hS
  let c : ℂ → ℂ := fun rho => ((analyticOrderAt xi rho).toNat : ℂ)
  have himage := tendsto_finiteExponentialPencil_cesaro_norm_sq (S.image Λ)
    (finiteExponentialFiberCoefficient S c Λ) id
    (by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact hunit i hi)
    (fun u _ v _ huv => huv)
  have hlim := himage.sub (tendsto_const_nhds (x := (xiStripWindowLocalSquareSum T : ℝ)))
  have hpen (n : ℕ) : xiClockPencil Λ T n =
      finiteExponentialPencil (S.image Λ) (finiteExponentialFiberCoefficient S c Λ) id n :=
    (finiteExponentialPencil_image_eq S c Λ n).symm
  refine hlim.congr' (Eventually.of_forall fun N => ?_)
  simp only [xiClockExcess, hpen]

/-- Two distinct members of one finite fibre contribute a cross term. -/
theorem sq_sum_ge_sum_sq_add_two_mul {ι : Type*} [DecidableEq ι] (F : Finset ι) (a : ι → ℕ)
    {i j : ι} (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j) :
    ∑ k ∈ F, a k ^ 2 + 2 * (a i * a j) ≤ (∑ k ∈ F, a k) ^ 2 := by
  have hjF : j ∈ F.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  set G := (F.erase i).erase j
  have hsum : ∑ k ∈ F, a k = a i + (a j + ∑ k ∈ G, a k) := by
    rw [← Finset.add_sum_erase F a hi, ← Finset.add_sum_erase (F.erase i) a hjF]
  have hsq : ∑ k ∈ F, a k ^ 2 = a i ^ 2 + (a j ^ 2 + ∑ k ∈ G, a k ^ 2) := by
    rw [← Finset.add_sum_erase F (fun k => a k ^ 2) hi,
      ← Finset.add_sum_erase (F.erase i) (fun k => a k ^ 2) hjF]
  have hG : ∑ k ∈ G, a k ^ 2 ≤ (∑ k ∈ G, a k) ^ 2 := by
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := G) (f := fun k => (a k : ℕ))
      (fun k _ => Nat.zero_le _)
    exact this
  rw [hsum, hsq]
  nlinarith [Nat.zero_le (∑ k ∈ G, a k), Nat.zero_le (a i), Nat.zero_le (a j)]

/-- **Universal quantum.**  If every zero of the window is `Λ`-unimodular and one of them is off
the critical line, the aliasing charge is at least `2`. -/
theorem two_le_xiClockAliasingCharge {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hline : ∀ t : ℝ, ‖Λ ((1 / 2 : ℂ) + t * I)‖ = 1) {T : ℝ}
    (hunit : ∀ rho ∈ (stripZeros_finite T).toFinset, ‖Λ rho‖ = 1)
    {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset) (hoff : rho.re ≠ 1 / 2) :
    2 ≤ xiClockAliasingCharge Λ T := by
  classical
  set S := (stripZeros_finite T).toFinset with hS
  let m : ℂ → ℕ := fun z => (analyticOrderAt xi z).toNat
  have hpartnerS : lineReflect rho ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]
    exact lineReflect_mem_stripZeros ((stripZeros_finite T).mem_toFinset.mp hrho)
  have hne : lineReflect rho ≠ rho := by
    intro h
    apply hoff
    have := congrArg Complex.re h
    rw [lineReflect_re] at this
    linarith
  have halias : Λ (lineReflect rho) = Λ rho :=
    lineUnimodularClock_lineReflect_eq_of_norm_eq_one hΛ hline (hunit rho hrho)
  -- fibre coefficients are natural casts
  have hfib (u : ℂ) : finiteExponentialFiberCoefficient S (fun rho => ((analyticOrderAt xi rho).toNat : ℂ)) Λ u =
      ((∑ z ∈ S with Λ z = u, m z : ℕ) : ℂ) := by
    unfold finiteExponentialFiberCoefficient
    push_cast
    rfl
  have hnorm (u : ℂ) : ‖finiteExponentialFiberCoefficient S (fun rho => ((analyticOrderAt xi rho).toNat : ℂ)) Λ u‖ ^ (2 : ℕ) =
      ((∑ z ∈ S with Λ z = u, m z : ℕ) : ℝ) ^ 2 := by
    rw [hfib, Complex.norm_natCast]
  -- local squares regroup by fibres
  have hlocal : (xiStripWindowLocalSquareSum T : ℝ) =
      ∑ u ∈ S.image Λ, ((∑ z ∈ S with Λ z = u, m z ^ 2 : ℕ) : ℝ) := by
    unfold xiStripWindowLocalSquareSum
    rw [← hS]
    push_cast
    exact (Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem Λ hz)
      (fun z => ((m z : ℝ) ^ 2))).symm
  unfold xiClockAliasingCharge
  rw [← hS]
  simp_rw [hnorm]
  rw [hlocal, ← Finset.sum_sub_distrib]
  -- every fibre term is nonnegative; the fibre of `Λ rho` gains `2 m_ρ m_ρ'`
  have hterm (u : ℂ) : (0 : ℝ) ≤ ((∑ z ∈ S with Λ z = u, m z : ℕ) : ℝ) ^ 2 -
      ((∑ z ∈ S with Λ z = u, m z ^ 2 : ℕ) : ℝ) := by
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := S.filter fun z => Λ z = u)
      (f := fun z => m z) (fun z _ => Nat.zero_le _)
    have h' : ((∑ z ∈ S with Λ z = u, m z ^ 2 : ℕ) : ℝ) ≤
        ((∑ z ∈ S with Λ z = u, m z : ℕ) : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  have hmemu : Λ rho ∈ S.image Λ := Finset.mem_image_of_mem Λ hrho
  have hkey : (2 : ℝ) ≤ ((∑ z ∈ S with Λ z = Λ rho, m z : ℕ) : ℝ) ^ 2 -
      ((∑ z ∈ S with Λ z = Λ rho, m z ^ 2 : ℕ) : ℝ) := by
    have hi : rho ∈ S.filter fun z => Λ z = Λ rho := Finset.mem_filter.mpr ⟨hrho, rfl⟩
    have hj : lineReflect rho ∈ S.filter fun z => Λ z = Λ rho :=
      Finset.mem_filter.mpr ⟨hpartnerS, halias⟩
    have h := sq_sum_ge_sum_sq_add_two_mul (S.filter fun z => Λ z = Λ rho) m hi hj hne.symm
    have hm1 := one_le_xi_order_toNat_of_mem_stripZeros hrho
    have hm2 := one_le_xi_order_toNat_of_mem_stripZeros hpartnerS
    have hprod : 1 ≤ m rho * m (lineReflect rho) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hm1) (Nat.one_le_iff_ne_zero.mp hm2))
    have hR : ((∑ z ∈ S with Λ z = Λ rho, m z ^ 2 : ℕ) : ℝ) + 2 * ((m rho * m (lineReflect rho) : ℕ) : ℝ) ≤
        ((∑ z ∈ S with Λ z = Λ rho, m z : ℕ) : ℝ) ^ 2 := by exact_mod_cast h
    have hprodR : (1 : ℝ) ≤ ((m rho * m (lineReflect rho) : ℕ) : ℝ) := by exact_mod_cast hprod
    linarith
  calc (2 : ℝ) ≤ ((∑ z ∈ S with Λ z = Λ rho, m z : ℕ) : ℝ) ^ 2 -
        ((∑ z ∈ S with Λ z = Λ rho, m z ^ 2 : ℕ) : ℝ) := hkey
    _ ≤ _ := Finset.single_le_sum (f := fun u => ((∑ z ∈ S with Λ z = u, m z : ℕ) : ℝ) ^ 2 -
        ((∑ z ∈ S with Λ z = u, m z ^ 2 : ℕ) : ℝ)) (fun u _ => hterm u) hmemu

/-- **Sub-quantum bounds force the window onto the line, for every clock.**  If the clock excess is
eventually bounded by a constant below `2`, every zero of the window is critical. -/
theorem re_eq_half_of_xiClockExcess_eventually_lt_two {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hline : ∀ t : ℝ, ‖Λ ((1 / 2 : ℂ) + t * I)‖ = 1) {T C : ℝ} (hC : C < 2)
    (hbound : ∀ᶠ N : ℕ in atTop, xiClockExcess Λ T N ≤ C)
    {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset) : rho.re = 1 / 2 := by
  have hunit : ∀ z ∈ (stripZeros_finite T).toFinset, ‖Λ z‖ = 1 := by
    by_contra hcon
    push Not at hcon
    exact not_eventually_bounded_xiClockExcess hΛ hline hcon ⟨C, hbound⟩
  by_contra hoff
  have h2 := two_le_xiClockAliasingCharge hΛ hline hunit hrho hoff
  have hle := le_of_tendsto (tendsto_xiClockExcess_aliasingCharge hunit) hbound
  linarith

end

end RHTower
