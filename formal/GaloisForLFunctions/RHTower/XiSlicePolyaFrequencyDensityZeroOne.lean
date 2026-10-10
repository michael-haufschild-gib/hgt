import GaloisForLFunctions.RHTower.XiSingleHeightPolyaFrequencyCriterion
import GaloisForLFunctions.RHTower.WeightedScrewPoleContradiction
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyDensity

/-!
# A zero–one law for the densities of Pólya-frequency slices

Let `c_n(t)` be the Taylor coefficients of `g_t(x) = ξ(½+x+it) ξ(½−x+it)` at `x = 0` and
`A_k = {t : (c_{2n}(t))_n is PF_k}`.  On a bounded window `[a, b]` the sets `A_k ∩ [a, b]` decrease
in `k`, and

* under RH every `A_k` is all of `ℝ`;
* if RH fails, `|A_k ∩ [a, b]| → 0` as `k → ∞`, for every window
  (`tendsto_volume_pfSeq_xiSliceCoeff_of_not_riemannHypothesis`).

So RH holds iff some window carries `PF_k` slices on a set whose measure is bounded below uniformly
in `k` (`riemannHypothesis_iff_exists_uniform_pfSeq_density`): a positive-density theorem for
`PF_k` slices proves RH exactly when its constant does not depend on `k`.

At the level of single coefficients the dichotomy is sharper still.  The bad set
`{t : c_{2n}(t) < 0 for some n}` is open, so it is null iff it is empty, and RH holds iff slice
positivity holds at almost every height (`riemannHypothesis_iff_ae_xiSliceCoeff_nonneg`).  The
positive-density bounds on the bad set (at most a fixed fraction of `[T, 2T]`) are therefore the
strongest form a density statement can take short of RH.

Large windows cannot see finitely many exceptions.  If every off-line zero has `|Im ρ| ≤ H`, then
every height `t ≥ H + cot(π/(2k+2))/2` carries a `PF_k` slice
(`pfSeq_xiSliceCoeff_above_offLine_height`), so `|A_k ∩ [0, V]| ≥ V − H − cot(π/(2k+2))/2` for
every `k` (`volume_pfSeq_xiSliceCoeff_ge_of_offLine_height`).  Positive-density theorems on growing
windows with fixed `k` are blind to every finite set of off-line zeros; only `k`-uniformity on a
fixed window decides RH.

The sets `A_k` are closed, because the slice coefficients are continuous in `t` (Cauchy's formula
on the unit circle).  Their intersection consists of the heights at which the slice is `PF_∞`, and
`PF_∞` at a single height `t` with `Ξ(t) ≠ 0` is RH
(`riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff_at`).  The real zeros of `Ξ` are countable, so
without RH the intersection is null and continuity from above gives the limit `0`.
-/

open Complex Filter Topology MeasureTheory
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The slice coefficients depend continuously on the height. -/
theorem continuous_xiSliceCoeff (n : ℕ) : Continuous fun t : ℝ => xiSliceCoeff t n := by
  have hxi : Continuous xi := xi_differentiable.continuous
  have hf : Continuous (Function.uncurry fun (t θ : ℝ) =>
      Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I)
        * xiSliceProduct t (((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))) := by
    unfold xiSliceProduct Function.uncurry
    fun_prop
  have hI := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hf 0 (2 * Real.pi)
  have e : (fun t : ℝ => xiSliceCoeff t n) = fun t =>
      ((2 * Real.pi * (1 : ℝ) ^ n : ℝ) : ℂ)⁻¹
        * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I)
          * xiSliceProduct t (((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
    funext fun t => xiSliceCoeff_eq_circle t n one_pos
  rw [e]
  exact continuous_const.mul hI

/-- Every Toeplitz minor of the even slice coefficients depends continuously on the height. -/
theorem continuous_toeplitzMinor_xiSliceCoeff (m : ℕ) (i j : Fin m → ℕ) :
    Continuous fun t : ℝ => toeplitzMinor (fun n => (xiSliceCoeff t (2 * n)).re) m i j := by
  unfold toeplitzMinor
  refine Continuous.matrix_det ?_
  refine continuous_pi fun r => continuous_pi fun c => ?_
  simp only [Matrix.of_apply, zext]
  split_ifs
  · exact Complex.continuous_re.comp (continuous_xiSliceCoeff _)
  · exact continuous_const

/-- The heights at which the slice is `PF_k` form a closed set. -/
theorem isClosed_setOf_pfSeq_xiSliceCoeff (k : ℕ) :
    IsClosed {t : ℝ | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)} := by
  unfold PFSeq
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun m => isClosed_iInter fun _ => isClosed_iInter fun i =>
    isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_toeplitzMinor_xiSliceCoeff m i j)

/-- The real zeros of `Ξ` are countable. -/
theorem countable_setOf_XiC_ofReal_eq_zero : {t : ℝ | XiC (t : ℂ) = 0}.Countable := by
  have huniv : (Set.univ : Set XiZeroCopy).Countable := by
    have hsub : (Set.univ : Set XiZeroCopy) ⊆
        ⋃ N : ℕ, {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ N} := fun q _ => by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖xiSpectralPoint q‖
      exact Set.mem_iUnion.mpr ⟨N, hN⟩
    exact (Set.countable_iUnion fun N : ℕ => (finite_xiZeroCopy_norm_le (N : ℝ)).countable).mono hsub
  have himg := Set.Countable.image huniv (fun q : XiZeroCopy => (xiSpectralPoint q).re)
  refine himg.mono fun t ht => ?_
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp ht
  refine ⟨q, Set.mem_univ q, ?_⟩
  show (xiSpectralPoint q).re = t
  rw [hq, Complex.ofReal_re]

/-- **Without RH, the `PF_k`-slice densities of every window tend to zero.** -/
theorem tendsto_volume_pfSeq_xiSliceCoeff_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) (a b : ℝ) :
    Tendsto (fun k : ℕ =>
      volume {t ∈ Set.Icc a b | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)})
      atTop (𝓝 0) := by
  set B : ℕ → Set ℝ := fun k =>
    {t ∈ Set.Icc a b | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)} with hB
  have hBeq : ∀ k, B k = Set.Icc a b ∩ {t | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)} :=
    fun k => rfl
  have hmeas : ∀ k, NullMeasurableSet (B k) volume := fun k => by
    rw [hBeq]
    exact (isClosed_Icc.inter (isClosed_setOf_pfSeq_xiSliceCoeff k)).measurableSet
      |>.nullMeasurableSet
  have hanti : Antitone B := fun k k' hkk' t ht => ⟨ht.1, PFSeq.of_le hkk' ht.2⟩
  have hfin : ∃ k, volume (B k) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top (measure_Icc_lt_top (a := a) (b := b)).ne
      (measure_mono fun t ht => ht.1)⟩
  have hlim := tendsto_measure_iInter_atTop hmeas hanti hfin
  have hnull : volume (⋂ k, B k) = 0 := by
    refine measure_mono_null (fun t ht => ?_)
      (countable_setOf_XiC_ofReal_eq_zero.measure_zero volume)
    by_contra h0
    exact hRH ((riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff_at h0).mpr fun k =>
      (Set.mem_iInter.mp ht k).2)
  rw [hnull] at hlim
  exact hlim

/-- **Zero–one law for `PF_k` slices.**  RH holds iff, on some window `[a, b]`, the heights at which
the slice coefficients are `PF_k` have measure at least a fixed `c > 0` for every `k`. -/
theorem riemannHypothesis_iff_exists_uniform_pfSeq_density :
    RiemannHypothesis ↔ ∃ a b c : ℝ, 0 < c ∧ ∀ k : ℕ,
      ENNReal.ofReal c ≤
        volume {t ∈ Set.Icc a b | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)} := by
  constructor
  · intro hRH
    refine ⟨0, 1, 1, one_pos, fun k => ?_⟩
    have hall : {t ∈ Set.Icc (0 : ℝ) 1 | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)} =
        Set.Icc 0 1 :=
      Set.sep_eq_self_iff_mem_true.mpr fun t _ =>
        riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff.mp hRH t k
    rw [hall, Real.volume_Icc, sub_zero]
  · rintro ⟨a, b, c, hc, h⟩
    by_contra hRH
    obtain ⟨k, hk⟩ := ((tendsto_volume_pfSeq_xiSliceCoeff_of_not_riemannHypothesis hRH a b).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.mpr hc))).exists
    exact absurd (h k) (not_le.mpr hk)

/-- **Off-line zeros below a height are invisible above it.**  If every off-line zero has
`|Im ρ| ≤ H`, then the slice at every height `t ≥ H + cot(π/(2k+2))/2` is `PF_k`: the critical zeros
lie on the axis of every visibility cone, and the low off-line zeros are far enough below `t`. -/
theorem pfSeq_xiSliceCoeff_above_offLine_height {H : ℝ}
    (hH : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → |(q.1 : ℂ).im| ≤ H) {k : ℕ} (hk : 1 ≤ k)
    {t : ℝ} (ht : H + Real.cot (Real.pi / (2 * ((k : ℝ) + 1))) / 2 ≤ t) :
    PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re) := by
  refine xiSliceCoeff_pfSeq_of_cone hk fun q => ?_
  set c := Real.cos (Real.pi / ((k : ℝ) + 1)) with hc
  set κ := Real.cot (Real.pi / (2 * ((k : ℝ) + 1))) with hκ
  have hk1 : (2 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hc0 : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by
      have : 0 ≤ Real.pi / ((k : ℝ) + 1) := by positivity
      linarith [Real.pi_pos], by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_pos]⟩
  have hc1 : c ≤ 1 := Real.cos_le_one _
  have hκ0 : 0 ≤ κ := RHTower.DeBruijn.cot_pi_div_nonneg k
  have hκc : κ ^ 2 * (1 - c) = 1 + c := RHTower.DeBruijn.cot_sq_mul_one_sub_cos k
  by_cases hre : (q.1 : ℂ).re = 1 / 2
  · rw [hre, sub_self]
    nlinarith [sq_nonneg ((q.1 : ℂ).im - t)]
  · have him := abs_le.mp (hH q hre)
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have hv : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith [hstrip.1, hstrip.2]
    have hu : κ / 2 ≤ t - (q.1 : ℂ).im := by linarith [him.2]
    have hu2 : κ ^ 2 / 4 ≤ ((q.1 : ℂ).im - t) ^ 2 := by
      have h0 : 0 ≤ κ / 2 := by positivity
      have := pow_le_pow_left₀ h0 hu 2
      nlinarith
    have hgain : (1 + c) / 4 ≤ ((q.1 : ℂ).im - t) ^ 2 * (1 - c) := by
      have := mul_le_mul_of_nonneg_right hu2 (by linarith : (0 : ℝ) ≤ 1 - c)
      nlinarith
    have hloss : ((q.1 : ℂ).re - 1 / 2) ^ 2 * (1 + c) ≤ (1 + c) / 4 := by
      have := mul_le_mul_of_nonneg_right hv (by linarith : (0 : ℝ) ≤ 1 + c)
      linarith
    nlinarith

/-- **Density blindness.**  If every off-line zero has `|Im ρ| ≤ H` (`H ≥ 0`), then for every
`k ≥ 1` the `PF_k` slices fill `[0, V]` up to the initial segment of length
`H + cot(π/(2k+2))/2`. -/
theorem volume_pfSeq_xiSliceCoeff_ge_of_offLine_height {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → |(q.1 : ℂ).im| ≤ H) {k : ℕ} (hk : 1 ≤ k)
    (V : ℝ) :
    ENNReal.ofReal (V - (H + Real.cot (Real.pi / (2 * ((k : ℝ) + 1))) / 2)) ≤
      volume {t ∈ Set.Icc (0 : ℝ) V | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)} := by
  have hκ0 := RHTower.DeBruijn.cot_pi_div_nonneg k
  rw [← Real.volume_Icc]
  refine measure_mono fun t ht => ⟨⟨by linarith [ht.1], ht.2⟩, ?_⟩
  exact pfSeq_xiSliceCoeff_above_offLine_height hH hk ht.1

/-- **RH is slice positivity at almost every height.**  The set of heights where some even slice
coefficient is negative is open (the coefficients are continuous in `t`), so it is null iff it is
empty. -/
theorem riemannHypothesis_iff_ae_xiSliceCoeff_nonneg :
    RiemannHypothesis ↔ volume {t : ℝ | ∃ n, (xiSliceCoeff t (2 * n)).re < 0} = 0 := by
  constructor
  · intro hRH
    have hempty : {t : ℝ | ∃ n, (xiSliceCoeff t (2 * n)).re < 0} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
      intro n
      have h := riemannHypothesis_iff_xiSliceCoeff_nonneg.mp hRH t (2 * n)
      exact (Complex.nonneg_iff.mp h).1
    rw [hempty, measure_empty]
  · intro hnull
    have hopen : IsOpen {t : ℝ | ∃ n, (xiSliceCoeff t (2 * n)).re < 0} := by
      have : {t : ℝ | ∃ n, (xiSliceCoeff t (2 * n)).re < 0} =
          ⋃ n, {t : ℝ | (xiSliceCoeff t (2 * n)).re < 0} := by
        ext t; simp
      rw [this]
      exact isOpen_iUnion fun n =>
        isOpen_lt (Complex.continuous_re.comp (continuous_xiSliceCoeff _)) continuous_const
    have hempty : {t : ℝ | ∃ n, (xiSliceCoeff t (2 * n)).re < 0} = ∅ := by
      by_contra hne
      exact (hopen.measure_ne_zero volume (Set.nonempty_iff_ne_empty.mpr hne)) hnull
    refine riemannHypothesis_iff_xiSliceCoeff_nonneg.mpr fun t n => ?_
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hre : 0 ≤ (xiSliceCoeff t (2 * m)).re := by
        by_contra hlt
        push Not at hlt
        have : t ∈ {t : ℝ | ∃ n, (xiSliceCoeff t (2 * n)).re < 0} := ⟨m, hlt⟩
        rw [hempty] at this
        exact this
      exact Complex.nonneg_iff.mpr ⟨hre, (xiSliceCoeff_im_eq_zero t (2 * m)).symm⟩
    · rw [xiSliceCoeff_odd_eq_zero]

end

end RHTower
