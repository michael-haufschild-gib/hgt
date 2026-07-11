import GaloisForLFunctions.RHTower.ClockEscape
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

namespace RHTower

open Complex Filter Topology Set Metric

lemma tendsto_intFloor_mul_of_pos_of_tendsto_zero
    (T : ℕ → ℝ) (hTpos : ∀ n, 0 < T n)
    (hTzero : Tendsto T atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n : ℕ => ((⌊t / T n⌋ : ℤ) : ℝ) * T n) atTop (𝓝 t) := by
  have hlo : ∀ n : ℕ, 0 ≤ t - ((⌊t / T n⌋ : ℤ) : ℝ) * T n := by
    intro n
    have hfloor := Int.floor_le (t / T n)
    have hmul : ((⌊t / T n⌋ : ℤ) : ℝ) * T n ≤ t :=
      (le_div_iff₀ (hTpos n)).mp hfloor
    linarith
  have hhi : ∀ n : ℕ, t - ((⌊t / T n⌋ : ℤ) : ℝ) * T n ≤ T n := by
    intro n
    have hfloor := Int.lt_floor_add_one (t / T n)
    have hmul : t < (((⌊t / T n⌋ : ℤ) : ℝ) + 1) * T n :=
      (div_lt_iff₀ (hTpos n)).mp hfloor
    linarith
  have hdiff : Tendsto
      (fun n : ℕ => t - ((⌊t / T n⌋ : ℤ) : ℝ) * T n) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall hlo) (Eventually.of_forall hhi) hTzero
  have h :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).sub hdiff
  have hfun :
      (fun n : ℕ => t - (t - ((⌊t / T n⌋ : ℤ) : ℝ) * T n)) =
        fun n : ℕ => ((⌊t / T n⌋ : ℤ) : ℝ) * T n := by
    funext n
    ring
  rw [hfun] at h
  simpa using h

theorem periodic_zero_limit_of_period_tendsto {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn Fn F atTop Ω)
    (hFc : ContinuousOn F Ω)
    {z : ℂ} (hz : z ∈ Ω)
    {zn : ℕ → ℂ} (hzn : Tendsto zn atTop (𝓝 z)) (hznΩ : ∀ n, zn n ∈ Ω)
    {Tn : ℕ → ℝ} {T : ℝ} (hTn : Tendsto Tn atTop (𝓝 T))
    (hper : ∀ n, ∀ k : ℤ, Fn n (zn n + (k * Tn n) * Complex.I) = 0) :
    ∀ k : ℤ, F (z + (k * T) * Complex.I) = 0 := by
  intro k
  have hTc : Tendsto (fun n : ℕ => (Tn n : ℂ)) atTop (𝓝 (T : ℂ)) :=
    (Complex.continuous_ofReal.tendsto T).comp hTn
  have hstep : Tendsto
      (fun n : ℕ => (k : ℂ) * (Tn n : ℂ) * Complex.I) atTop
      (𝓝 ((k : ℂ) * (T : ℂ) * Complex.I)) :=
    (tendsto_const_nhds.mul hTc).mul tendsto_const_nhds
  have harg : Tendsto
      (fun n => zn n + (k : ℂ) * (Tn n : ℂ) * Complex.I) atTop
      (𝓝 (z + (k : ℂ) * (T : ℂ) * Complex.I)) := hzn.add hstep
  have htargetΩ : z + (k : ℂ) * (T : ℂ) * Complex.I ∈ Ω := by
    simpa only [ofReal_intCast, ofReal_mul] using hΩshift z hz ((k : ℝ) * T)
  have hargsΩ : ∀ n, zn n + (k : ℂ) * (Tn n : ℂ) * Complex.I ∈ Ω := by
    intro n
    simpa only [ofReal_intCast, ofReal_mul] using
      hΩshift (zn n) (hznΩ n) ((k : ℝ) * Tn n)
  have hargWithin : Tendsto
      (fun n => zn n + (k : ℂ) * (Tn n : ℂ) * Complex.I) atTop
      (𝓝[Ω] (z + (k : ℂ) * (T : ℂ) * Complex.I)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨harg, Eventually.of_forall hargsΩ⟩
  have hcomp := hconv.tendsto_comp (hFc _ htargetΩ) htargetΩ hargWithin
  have hzero : Tendsto
      (fun n => Fn n (zn n + (k : ℂ) * (Tn n : ℂ) * Complex.I)) atTop (𝓝 0) := by
    have heq : ∀ n, Fn n (zn n + (k : ℂ) * (Tn n : ℂ) * Complex.I) = 0 :=
      fun n => hper n k
    simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have := tendsto_nhds_unique hcomp hzero
  exact this

theorem shrinking_periodic_zero_limit_vertical {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn Fn F atTop Ω)
    (hFc : ContinuousOn F Ω)
    {z : ℂ} (hz : z ∈ Ω)
    {zn : ℕ → ℂ} (hzn : Tendsto zn atTop (𝓝 z)) (hznΩ : ∀ n, zn n ∈ Ω)
    {Tn : ℕ → ℝ} (hTpos : ∀ n, 0 < Tn n)
    (hTzero : Tendsto Tn atTop (𝓝 0))
    (hper : ∀ n, ∀ k : ℤ, Fn n (zn n + (k * Tn n) * Complex.I) = 0) :
    ∀ t : ℝ, F (z + (t : ℂ) * Complex.I) = 0 := by
  intro t
  let kn : ℕ → ℤ := fun n => ⌊t / Tn n⌋
  have hgrid : Tendsto (fun n => ((kn n : ℤ) : ℝ) * Tn n) atTop (𝓝 t) :=
    tendsto_intFloor_mul_of_pos_of_tendsto_zero Tn hTpos hTzero t
  have hstep : Tendsto (fun n : ℕ => ((((kn n : ℤ) : ℝ) * Tn n : ℝ) : ℂ)) atTop
      (𝓝 (t : ℂ)) := (Complex.continuous_ofReal.tendsto t).comp hgrid
  have harg : Tendsto
      (fun n => zn n + (((((kn n : ℤ) : ℝ) * Tn n : ℝ) : ℂ)) * Complex.I) atTop
      (𝓝 (z + (t : ℂ) * Complex.I)) := hzn.add (hstep.mul tendsto_const_nhds)
  have htargetΩ : z + (t : ℂ) * Complex.I ∈ Ω := hΩshift z hz t
  have hargsΩ : ∀ n,
      zn n + (((((kn n : ℤ) : ℝ) * Tn n : ℝ) : ℂ)) * Complex.I ∈ Ω :=
    fun n => hΩshift (zn n) (hznΩ n) (((kn n : ℤ) : ℝ) * Tn n)
  have hargWithin : Tendsto
      (fun n => zn n + (((((kn n : ℤ) : ℝ) * Tn n : ℝ) : ℂ)) * Complex.I) atTop
      (𝓝[Ω] (z + (t : ℂ) * Complex.I)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨harg, Eventually.of_forall hargsΩ⟩
  have hcomp := hconv.tendsto_comp (hFc _ htargetΩ) htargetΩ hargWithin
  have hzero : Tendsto
      (fun n => Fn n
        (zn n + (((((kn n : ℤ) : ℝ) * Tn n : ℝ) : ℂ)) * Complex.I)) atTop (𝓝 0) := by
    have heq : ∀ n, Fn n
        (zn n + (((((kn n : ℤ) : ℝ) * Tn n : ℝ) : ℂ)) * Complex.I) = 0 := by
      intro n
      simpa only [ofReal_intCast, ofReal_mul] using hper n (kn n)
    simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hcomp hzero

/-- Periodic zero fibres with positive periods in a bounded interval have a periodic limit zero,
unless the limit carrier vanishes on the entire vertical line through that zero. -/
theorem bounded_periodic_zero_limit {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn Fn F atTop Ω)
    (hFc : ContinuousOn F Ω)
    {z : ℂ} (hz : z ∈ Ω)
    {zn : ℕ → ℂ} (hzn : Tendsto zn atTop (𝓝 z)) (hznΩ : ∀ n, zn n ∈ Ω)
    {Tn : ℕ → ℝ} {B : ℝ} (hTpos : ∀ n, 0 < Tn n) (hTle : ∀ n, Tn n ≤ B)
    (hper : ∀ n, ∀ k : ℤ, Fn n (zn n + (k * Tn n) * Complex.I) = 0)
    (hnotVertical : ¬ ∀ t : ℝ, F (z + (t : ℂ) * Complex.I) = 0) :
    ∃ T : ℝ, 0 < T ∧ T ≤ B ∧
      ∀ k : ℤ, F (z + (k * T) * Complex.I) = 0 := by
  have hmem : ∀ n, Tn n ∈ Set.Icc (0 : ℝ) B :=
    fun n => ⟨(hTpos n).le, hTle n⟩
  obtain ⟨T, hTmem, φ, hφmono, hTlim⟩ :=
    isCompact_Icc.isSeqCompact.subseq_of_frequently_in
      (Eventually.frequently (Eventually.of_forall hmem))
  have hφtends : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hconv' : TendstoLocallyUniformlyOn (fun m => Fn (φ m)) F atTop Ω := by
    intro u hu x hx
    obtain ⟨s, hs, H⟩ := hconv u hu x hx
    exact ⟨s, hs, hφtends.eventually H⟩
  have hzn' : Tendsto (fun m => zn (φ m)) atTop (𝓝 z) := hzn.comp hφtends
  have hznΩ' : ∀ m, zn (φ m) ∈ Ω := fun m => hznΩ (φ m)
  have hTpos' : ∀ m, 0 < Tn (φ m) := fun m => hTpos (φ m)
  have hper' : ∀ m, ∀ k : ℤ,
      Fn (φ m) (zn (φ m) + (k * Tn (φ m)) * Complex.I) = 0 :=
    fun m k => hper (φ m) k
  by_cases hTzero : T = 0
  · exfalso
    apply hnotVertical
    apply shrinking_periodic_zero_limit_vertical hΩshift hconv' hFc hz hzn' hznΩ'
      hTpos'
    · simpa [hTzero] using hTlim
    · exact hper'
  · have hTstrict : 0 < T := lt_of_le_of_ne hTmem.1 (Ne.symm hTzero)
    refine ⟨T, hTstrict, hTmem.2, ?_⟩
    exact periodic_zero_limit_of_period_tendsto hΩshift hconv' hFc hz hzn' hznΩ'
      hTlim hper'

/-- `XiC` has no vertical arithmetic progression of zeros. In the original `s`-coordinate such a
progression is horizontal, and one direction eventually enters the zero-free half-plane
`Re s ≥ 1`. -/
theorem xiC_no_vertical_zero_progression (z : ℂ) {T : ℝ} (hT : 0 < T) :
    ¬ ∀ k : ℤ, XiC (z + (k * T) * Complex.I) = 0 := by
  intro hall
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((z.im + 1 / 2) / T)
  let k : ℤ := -(n : ℤ)
  have hre : 1 ≤ (1 / 2 + (z + (k * T) * Complex.I) * Complex.I).re := by
    have hre_eq :
        (1 / 2 + (z + (k * T) * Complex.I) * Complex.I).re =
          (1 : ℝ) / 2 - z.im + n * T := by
      dsimp [k]
      push_cast
      simp [Complex.mul_re]
      ring
    rw [hre_eq]
    have hmul : z.im + 1 / 2 < n * T := (div_lt_iff₀ hT).mp hn
    linarith
  exact xi_ne_zero_of_one_le_re hre (by simpa only [XiC] using hall k)

/-- A cofinal analytic approximation whose off-real `XiC` zero fibres carry uniformly bounded
positive vertical clocks forces RH. These are horizontal clocks in the original `s`-coordinate,
so their limiting positive-period branch is excluded by `xiC_no_vertical_zero_progression`; the
shrinking-period branch is excluded by analyticity. -/
theorem riemannHypothesis_of_bounded_clock_zero_approximants
    {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hzeroClock : ∀ z : ℂ, XiC z = 0 → z.im ≠ 0 →
      ∃ (zn : ℕ → ℂ) (Tn : ℕ → ℝ) (B : ℝ),
        Tendsto zn atTop (𝓝 z) ∧
        (∀ n, 0 < Tn n) ∧ (∀ n, Tn n ≤ B) ∧
        ∀ n, ∀ k : ℤ, Fn n (zn n + (k * Tn n) * Complex.I) = 0) :
    RiemannHypothesis := by
  have hXiCZeroReal : ∀ z : ℂ, XiC z = 0 → z.im = 0 := by
    intro z hz
    by_contra hzim
    obtain ⟨zn, Tn, B, hzn, hTpos, hTle, hper⟩ := hzeroClock z hz hzim
    have hnotVertical : ¬ ∀ t : ℝ, XiC (z + (t : ℂ) * Complex.I) = 0 := by
      intro hall
      exact xiC_no_vertical_zero_progression z zero_lt_one fun k => by
        simpa using hall (k : ℝ)
    obtain ⟨T, hTpos', -, hprog⟩ := bounded_periodic_zero_limit
      (Ω := Set.univ) (fun w _ t => Set.mem_univ (w + (t : ℂ) * Complex.I))
      (hconv.tendstoLocallyUniformlyOn) XiC_analytic.continuousOn
      (Set.mem_univ z) hzn (fun _ => Set.mem_univ _) hTpos hTle hper hnotVertical
    exact xiC_no_vertical_zero_progression z hTpos' hprog
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-Complex.I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * Complex.I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
        rw [neg_mul, Complex.I_mul_I]
        ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have him : z.im = 0 := hXiCZeroReal z hXiC
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  have hre : ρ.re = 1 / 2 := by linarith [him, hzIm]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) hre

/-- Hurwitz selection along a cofinal subsequence: every `XiC` zero is approached by zeros of
locally uniformly convergent eventually-entire approximants. -/
theorem exists_XiC_zero_approximating_subsequence
    {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    {z : ℂ} (hz : XiC z = 0) :
    ∃ (φ : ℕ → ℕ) (zn : ℕ → ℂ),
      StrictMono φ ∧ Tendsto zn atTop (𝓝 z) ∧ ∀ n, Fn (φ n) (zn n) = 0 := by
  have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 z, XiC w = 0 := by
    intro hev
    have hall := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ 0)
    exact XiC_zero_ne hall
  have hpunct : ∀ᶠ w in 𝓝[≠] z, XiC w ≠ 0 :=
    (XiC_analytic z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hnotEventuallyZero
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  let c : ℝ := δ / 2
  have hc : 0 < c := half_pos hδ
  let r : ℕ → ℝ := fun n => c / (n + 1 : ℕ)
  have hrpos : ∀ n, 0 < r n := by
    intro n
    exact div_pos hc (by positivity)
  have hrlt : ∀ n, r n < δ := by
    intro n
    have hden : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    have hrc : r n ≤ c := div_le_self hc.le hden
    exact hrc.trans_lt (half_lt_self hδ)
  have hsphere : ∀ n, ∀ w ∈ sphere z (r n), XiC w ≠ 0 := by
    intro n w hw
    apply hδsub
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt (hrlt n))
    · exact Set.mem_compl_singleton_iff.mpr
        (Metric.ne_of_mem_sphere hw (hrpos n).ne')
  have hlocal : ∀ n, ∀ᶠ m in atTop, ∃ w ∈ closedBall z (r n), Fn m w = 0 := by
    intro n
    exact eventually_exists_zero_closedBall_of_tendstoLocallyUniformly hconv
      (fun w => (XiC_analytic w (Set.mem_univ w)).differentiableAt) hFn
      (hrpos n) hz (hsphere n)
  obtain ⟨φ, hφmono, hφspec⟩ := Filter.extraction_forall_of_eventually hlocal
  let zn : ℕ → ℂ := fun n => Classical.choose (hφspec n)
  have hznspec : ∀ n, zn n ∈ closedBall z (r n) ∧ Fn (φ n) (zn n) = 0 := by
    intro n
    exact Classical.choose_spec (hφspec n)
  refine ⟨φ, zn, hφmono, ?_, fun n => (hznspec n).2⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hrzero : Tendsto r atTop (𝓝 0) := by
    simpa [r, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat c).comp
      (tendsto_add_atTop_nat 1)
  exact squeeze_zero' (Eventually.of_forall fun n => dist_nonneg)
    (Eventually.of_forall fun n => Metric.mem_closedBall.mp (hznspec n).1) hrzero

/-- Every off-real zero rides a vertical arithmetic progression whose positive period is bounded
by `B`. This is a finite-stage source property; it does not refer to the limit divisor. -/
def BoundedVerticalClockDichotomy (B : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f z = 0 → z.im = 0 ∨
    ∃ T : ℝ, 0 < T ∧ T ≤ B ∧ ∀ k : ℤ, f (z + (k * T) * Complex.I) = 0

/-- Locally uniform eventually-entire approximants with an eventually uniform bounded vertical
clock dichotomy force RH. Hurwitz zero selection is internal. -/
theorem riemannHypothesis_of_bounded_vertical_clock_dichotomy_approximants
    {Fn : ℕ → ℂ → ℂ} {B : ℝ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hclock : ∀ᶠ n in atTop, BoundedVerticalClockDichotomy B (Fn n)) :
    RiemannHypothesis := by
  have hXiCZeroReal : ∀ z : ℂ, XiC z = 0 → z.im = 0 := by
    intro z hz
    by_contra hzim
    obtain ⟨φ, zn, hφmono, hzn, hzeros⟩ :=
      exists_XiC_zero_approximating_subsequence hconv hFn hz
    have hφtends : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have hclockφ : ∀ᶠ n in atTop, BoundedVerticalClockDichotomy B (Fn (φ n)) :=
      hφtends.eventually hclock
    have hsmall : ∀ᶠ n in atTop, dist (zn n) z < |z.im| / 2 :=
      eventually_atTop.2 ((Metric.tendsto_atTop.mp hzn) (|z.im| / 2)
        (half_pos (abs_pos.mpr hzim)))
    have hznIm : ∀ᶠ n in atTop, (zn n).im ≠ 0 := by
      filter_upwards [hsmall] with n hn
      intro hzeroIm
      have himdist : |z.im| ≤ dist (zn n) z := by
        calc
          |z.im| = |(z - zn n).im| := by simp [hzeroIm]
          _ ≤ ‖z - zn n‖ := Complex.abs_im_le_norm _
          _ = dist (zn n) z := by rw [dist_comm, dist_eq_norm]
      nlinarith [abs_pos.mpr hzim]
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hclockφ.and hznIm)
    let ψ : ℕ → ℕ := fun n => φ (n + N)
    let w : ℕ → ℂ := fun n => zn (n + N)
    have hψtends : Tendsto ψ atTop atTop := by
      exact hφtends.comp (tendsto_add_atTop_nat N)
    have hconv' : TendstoLocallyUniformly (fun n => Fn (ψ n)) XiC atTop := by
      intro u hu x
      obtain ⟨t, ht, H⟩ := hconv u hu x
      exact ⟨t, ht, hψtends.eventually H⟩
    have hw : Tendsto w atTop (𝓝 z) := hzn.comp (tendsto_add_atTop_nat N)
    have hwzero : ∀ n, Fn (ψ n) (w n) = 0 := fun n => hzeros (n + N)
    have hclockw : ∀ n, ∃ T : ℝ, 0 < T ∧ T ≤ B ∧
        ∀ k : ℤ, Fn (ψ n) (w n + (k * T) * Complex.I) = 0 := by
      intro n
      have hgood := hN (n + N) (by omega)
      rcases hgood.1 (w n) (hwzero n) with honline | hperiod
      · exact False.elim (hgood.2 honline)
      · exact hperiod
    choose Tn hTpos hTle hper using hclockw
    have hnotVertical : ¬ ∀ t : ℝ, XiC (z + (t : ℂ) * Complex.I) = 0 := by
      intro hall
      exact xiC_no_vertical_zero_progression z zero_lt_one fun k => by
        simpa using hall (k : ℝ)
    obtain ⟨T, hTpos', -, hprog⟩ := bounded_periodic_zero_limit
      (Ω := Set.univ) (fun q _ t => Set.mem_univ (q + (t : ℂ) * Complex.I))
      (hconv'.tendstoLocallyUniformlyOn) XiC_analytic.continuousOn
      (Set.mem_univ z) hw (fun _ => Set.mem_univ _) hTpos hTle hper hnotVertical
    exact xiC_no_vertical_zero_progression z hTpos' hprog
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-Complex.I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * Complex.I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
        rw [neg_mul, Complex.I_mul_I]
        ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have him : z.im = 0 := hXiCZeroReal z hXiC
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  have hre : ρ.re = 1 / 2 := by linarith [him, hzIm]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) hre


end RHTower
