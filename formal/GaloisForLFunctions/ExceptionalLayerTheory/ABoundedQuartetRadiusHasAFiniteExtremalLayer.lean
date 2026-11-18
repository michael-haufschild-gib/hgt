import GaloisForLFunctions.ExceptionalLayerTheory.IncommensurableTopOrdinatesExcludeTheQuartetRadius
import GaloisForLFunctions.ExceptionalLayerTheory.DistinctExtremalOrdinatesHaveDistinctQuarterStepPhases
import GaloisForLFunctions.RHTower.GaussHodgeVerticalExtraction
import GaloisForLFunctions.HTGeometry.ExponentialSeriesFiberwise
import GaloisForLFunctions.HTGeometry.BohrPowerBoundary

/-!
# A bounded quartet radius and the extremal layer

A finite number of ordinates can share each sampled phase. The component of a
boundary increment at that phase is therefore analytic. An exact return on
all lattice translates of an open interval determines all its components.
-/

noncomputable section
open Complex Filter Topology RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry
open _root_.HTGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A summable discrete pencil with all moments zero has zero mass at each phase. -/
private theorem phase_mass_zero {ι : Type*} {c w : ι → ℂ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, ‖w i‖ = 1)
    (hm : ∀ k : ℕ, (∑' i, c i * w i ^ k) = 0) (z : ℂ) (hz : ‖z‖ = 1) :
    (∑' i, if w i = z then c i else 0) = 0 := by
  classical
  let u := fun i => w i / z
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; exact zero_lt_one)
  have hu (i : ι) : ‖u i‖ = 1 := by simp only [u, norm_div, hw, hz, div_self one_ne_zero]
  have hu1 (i : ι) : u i = 1 ↔ w i = z := div_eq_one_iff_eq hz0
  have hs (k : ℕ) : Summable (fun i => c i * u i ^ k) := by
    apply Summable.of_norm_bounded hc
    intro i
    rw [norm_mul, norm_pow, hu, one_pow, mul_one]
  have hm' (k : ℕ) : (∑' i, c i * u i ^ k) = 0 := by
    simp only [u, div_pow, ← mul_div_assoc, tsum_div_const, hm, zero_div]
  let A := fun (N : ℕ) (v : ℂ) => ((N : ℝ)⁻¹ : ℂ) * ∑ k ∈ Finset.range N, v^k
  have hzero (N : ℕ) : (∑' i, c i * A N (u i)) = 0 := by
    calc _ = ((N : ℝ)⁻¹ : ℂ) * ∑' i, ∑ k ∈ Finset.range N, c i * u i^k := by
               rw [← tsum_mul_left]
               apply tsum_congr
               intro i
               simp only [A, ← Finset.mul_sum]
               ring
      _ = ((N : ℝ)⁻¹ : ℂ) * ∑ k ∈ Finset.range N, ∑' i, c i * u i^k := by
            rw [Summable.tsum_finsetSum fun k _ => hs k]
      _ = 0 := by simp only [hm', Finset.sum_const_zero, mul_zero]
  have hpoint (i : ι) : Tendsto (fun N => c i * A N (u i)) atTop
      (𝓝 (if w i = z then c i else 0)) := by
    have h := (tendsto_complex_geom_cesaro_of_norm_eq_one (u i) (hu i)).const_mul (c i)
    by_cases he : w i = z
    · simpa only [A, if_pos he, if_pos ((hu1 i).mpr he), mul_one] using h
    · simpa only [A, if_neg he, if_neg (fun h => he ((hu1 i).mp h)), mul_zero] using h
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ i, ‖c i * A N (u i)‖ ≤ ‖c i‖ := by
    refine .of_forall fun N i => ?_
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_cesaro_geom_le_one (hu i) N)
      (norm_nonneg (c i))).trans_eq (mul_one _)
  have hlim := tendsto_tsum_of_dominated_convergence hc hpoint hdom
  simp only [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem char_time_add (ω t p : ℝ) :
    expChar ω (t+p) = expChar ω t * expChar ω p := by
  simp only [expChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem char_time_nat (ω p : ℝ) (n : ℕ) :
    expChar ω (n*p) = expChar ω p ^ n := by
  induction n with
  | zero => simp [expChar]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, char_time_add, ih, pow_succ]

private theorem analytic_finite_sum {ι : Type*} (S : Finset ι) (a : ι → ℂ) (ω : ι → ℝ) :
    AnalyticOnNhd ℝ (fun t => ∑ i ∈ S, a i * expChar (ω i) t) Set.univ := by
  intro x _
  apply Finset.analyticAt_fun_sum
  intro i _
  have hlin : AnalyticAt ℝ (fun t : ℝ => ω i * t) x := analyticAt_const.mul analyticAt_id
  exact analyticAt_const.mul (analyticAt_cexp.restrictScalars.comp
    (((Complex.ofRealCLM.analyticAt _).comp hlin).mul analyticAt_const))

/-- With finite occupied fibres for the sampled phases, vanishing on all lattice
translates of one open interval determines the entire exponential series. -/
private theorem zero_of_vanishing_on_translated_interval {ι : Type*}
    (a : ι → ℂ) (ω : ι → ℝ) (ha : Summable fun i => ‖a i‖) (p t₀ : ℝ)
    (hfinite : ∀ z : ℂ, {i | a i ≠ 0 ∧ expChar (ω i) p = z}.Finite)
    (hzero : ∀ᶠ t in 𝓝 t₀, ∀ n : ℕ, expSeriesCarrier a ω (t+n*p) = 0) :
    ∀ t, expSeriesCarrier a ω t = 0 := by
  classical
  let w := fun i => expChar (ω i) p
  have hsum (t : ℝ) : Summable fun i => ‖a i * expChar (ω i) t‖ := by
    simpa only [norm_mul, norm_expChar, mul_one] using ha
  have hpiece (z : ℂ) : ∀ t, (∑' i, if w i = z then a i * expChar (ω i) t else 0) = 0 := by
    let S := (hfinite z).toFinset
    have hform (t : ℝ) : (∑' i, if w i = z then a i * expChar (ω i) t else 0) =
        ∑ i ∈ S, a i * expChar (ω i) t := by
      rw [tsum_eq_sum (s := S) (fun j hj => by
        by_cases he : w j = z
        · have hz : a j = 0 := by
            by_contra hn
            exact hj ((hfinite z).mem_toFinset.mpr ⟨hn,he⟩)
          simp only [he, if_true, hz, zero_mul]
        · exact if_neg he)]
      apply Finset.sum_congr rfl
      intro j hj
      exact if_pos ((hfinite z).mem_toFinset.mp hj).2
    have hloc : (fun t => ∑ i ∈ S, a i * expChar (ω i) t) =ᶠ[𝓝 t₀] (fun _ => 0) := by
      filter_upwards [hzero] with t ht
      rw [← hform]
      by_cases hz : ‖z‖ = 1
      · apply phase_mass_zero (hsum t) (fun i => norm_expChar (ω i) p) _ z hz
        intro n
        simpa only [expSeriesCarrier, char_time_add, char_time_nat, w, mul_assoc] using ht n
      · have he (i : ι) : w i ≠ z := fun h => hz (h ▸ norm_expChar (ω i) p)
        simp only [if_neg (he _), tsum_zero]
    have hpoly := analytic_finite_sum S a ω
    have hglobal := hpoly.eq_of_eventuallyEq analyticOnNhd_const hloc
    intro t
    exact (hform t).trans (congrFun hglobal t)
  intro t
  let f := fun i => a i * expChar (ω i) t
  have hf : Summable f := Summable.of_norm (hsum t)
  have hsub (z : ℂ) : (∑' i : {i // w i = z}, f i.val) = 0 := by
    refine (tsum_subtype {i : ι | w i = z} f).trans ?_
    simpa only [Set.indicator, Set.mem_setOf_eq, f] using hpiece z t
  have hs : Summable (fun r : Σ z : ℂ, {i : ι // w i = z} => f r.2.val) :=
    ((Equiv.sigmaFiberEquiv w).summable_iff (f := f)).mpr hf
  calc expSeriesCarrier a ω t = ∑' r : Σ z : ℂ, {i : ι // w i = z}, f r.2.val :=
         ((Equiv.sigmaFiberEquiv w).tsum_eq f).symm
    _ = ∑' z : ℂ, ∑' i : {i : ι // w i = z}, f i.val := hs.tsum_sigma
    _ = 0 := by simp only [hsub, tsum_zero]

/-- Finite phase fibres prevent independent sign choices on successive periods of |D|. -/
private theorem periodic_multiple_of_finite_phase_fibers {ι : Type*} {D : ℝ → ℝ}
    (hc : Continuous D) (a : ι → ℂ) (ω : ι → ℝ) (ha : Summable fun i => ‖a i‖)
    (hrep : ∀ t : ℝ, (D t : ℂ) = expSeriesCarrier a ω t) (p : ℝ)
    (hper : Function.Periodic (fun t => |D t|) p)
    (hreturn : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∀ t, |D (t+n*p)-D t| ≤ ε)
    (hfinite : ∀ z : ℂ, {i | a i ≠ 0 ∧ expChar (ω i) p = z}.Finite) :
    ∃ n : ℕ, 0 < n ∧ Function.Periodic D (n*p) := by
  classical
  by_cases h0 : ∀ t, D t = 0
  · exact ⟨1, Nat.one_pos, fun t => (h0 _).trans (h0 t).symm⟩
  push Not at h0
  obtain ⟨t₀, h0⟩ := h0
  obtain ⟨n,hn,hclose⟩ := hreturn (|D t₀|/2) (half_pos (abs_pos.mpr h0))
  let b := fun i => a i * (expChar (ω i) (n*p)-1)
  have hb : Summable fun i => ‖b i‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) (ha.mul_right 2)
    rw [show ‖b i‖ = ‖a i‖ * ‖expChar (ω i) (n*p)-1‖ from norm_mul _ _]
    have hm : ‖expChar (ω i) (n*p) - 1‖ ≤ 2 := by
      simpa only [norm_expChar, norm_one, one_add_one_eq_two] using
        (norm_sub_le (expChar (ω i) (n*p)) (1 : ℂ))
    exact mul_le_mul_of_nonneg_left hm (norm_nonneg _)
  have hdiff (t : ℝ) : ((D (t+n*p)-D t : ℝ) : ℂ) = expSeriesCarrier b ω t := by
    rw [Complex.ofReal_sub, hrep, hrep]
    simp only [expSeriesCarrier]
    rw [← (summable_expSeries ha ω (t+n*p)).tsum_sub (summable_expSeries ha ω t)]
    apply tsum_congr
    intro i
    rw [char_time_add]
    dsimp only [b]
    ring
  have hbf (z : ℂ) : {i | b i ≠ 0 ∧ expChar (ω i) p = z}.Finite :=
    (hfinite z).subset fun i hi => ⟨fun h => hi.1 (by simp only [b,h,zero_mul]), hi.2⟩
  have hloc : ∀ᶠ t in 𝓝 t₀, |D t₀|/2 < |D t| :=
    hc.abs.continuousAt.eventually (lt_mem_nhds (half_lt_self (abs_pos.mpr h0)))
  have hzero : ∀ᶠ t in 𝓝 t₀, ∀ k : ℕ, expSeriesCarrier b ω (t+k*p) = 0 := by
    filter_upwards [hloc] with t ht
    intro k
    rw [← hdiff]
    apply Complex.ofReal_eq_zero.mpr
    apply sub_eq_zero.mpr
    have he := hper.nat_mul n (t+k*p)
    change |D (t+k*p+n*p)| = |D (t+k*p)| at he
    rcases abs_eq_abs.mp he with he | he
    · exact he
    · have h := hclose (t+k*p)
      have hk : |D (t+k*p)| = |D t| := hper.nat_mul k t
      rw [he, show -D (t+k*p) - D (t+k*p) = -(2*D (t+k*p)) by ring,
        abs_neg, abs_mul, abs_of_pos zero_lt_two, hk] at h
      linarith only [ht,h, abs_nonneg (D t)]
  refine ⟨n,hn,fun t => sub_eq_zero.mp (Complex.ofReal_eq_zero.mp ?_)⟩
  rw [hdiff]
  exact zero_of_vanishing_on_translated_interval b ω hb p t₀ hbf hzero t

private theorem top_phase_of_step_eigenvalue {β h p : ℝ} (hβ : 1/2 < β) (hh : 0 < h)
    (c : ℂ) (he : ∀ t, (boundaryStep β h (primeErrorBoundaryTrace β) (t+p) : ℂ) =
      c * (boundaryStep β h (primeErrorBoundaryTrace β) t : ℂ))
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re = β) : expChar (xiCopyOrdinate q) p = c := by
  let D := boundaryStep β h (primeErrorBoundaryTrace β)
  obtain ⟨hc,ha,hf⟩ := boundaryStep_coefficient hβ hh
  have hcC : Continuous (fun t => (D t : ℂ)) := Complex.continuous_ofReal.comp hc
  have haC : IsBohrAlmostPeriodic (fun t => (D t : ℂ)) := by
    simpa only [IsBohrAlmostPeriodic, ← Complex.ofReal_sub, Complex.norm_real] using ha
  have htr := bohrCoefficient_comp_add_const hcC haC p (xiCopyOrdinate q)
  change bohrCoefficient (fun t => (D (t+p) : ℂ)) _ = _ at htr
  rw [show (fun t => (D (t+p) : ℂ)) = (fun t => c*(D t : ℂ)) from funext he,
    bohrCoefficient_const_mul c hcC haC] at htr
  exact mul_right_cancel₀ (hf q hq) htr.symm

private theorem stepAmplitude_ne_zero_only_on_line {β h : ℝ} {q : XiZeroCopy}
    (hq : stepAmplitude β h q ≠ 0) : (q.1 : ℂ).re = β := by
  by_contra he
  exact hq (by simp only [stepAmplitude, primeErrorBoundaryAmplitude, if_neg he, mul_zero])

/-- A bounded ordinary-prime radius forces finitely many extremal zeros, with
multiplicity. No bound on the other right zeros is assumed. -/
theorem finite_top_of_bounded_thetaRadial {γ : ℝ} {m : ℕ} (hΘ : 1/2 < zetaZeroAbscissa)
    (hγ : γ ≠ 0) (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    {q : XiZeroCopy | (q.1 : ℂ).re = zetaZeroAbscissa}.Finite := by
  let β := zetaZeroAbscissa
  let h := quarterPeriodStep γ
  let p := 2*h
  let D := boundaryStep β h (primeErrorBoundaryTrace β)
  let a := stepAmplitude β h
  have hh : 0 < h := quarterPeriodStep_pos hγ
  obtain ⟨hc,ha,_⟩ := boundaryStep_coefficient hΘ hh
  have hfinite (z : ℂ) : {q | a q ≠ 0 ∧ expChar (xiCopyOrdinate q) p = z}.Finite :=
    (finite_top_double_step_fiber hΘ hγ hb z).subset fun q hq =>
      ⟨stepAmplitude_ne_zero_only_on_line hq.1,hq.2⟩
  obtain ⟨n,hn,hper⟩ := periodic_multiple_of_finite_phase_fibers hc a xiCopyOrdinate
    (stepAmplitude_summable hΘ h) (stepAmplitude_carrier hΘ h) p
    (boundaryStep_abs_periodic hΘ hb)
    (fun ε hε => lattice_almost_period (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hc ha) p hε)
    hfinite
  have hchar (q : XiZeroCopy) (hq : (q.1 : ℂ).re = β) :
      expChar (xiCopyOrdinate q) p ^ n = 1 := by
    rw [← char_time_nat]
    exact top_phase_of_step_eigenvalue hΘ hh 1
      (fun t => (congrArg Complex.ofReal (hper t)).trans (one_mul _).symm) q hq
  refine ((finite_setOf_pow_eq_one hn.ne').biUnion fun z _ => finite_top_double_step_fiber hΘ hγ hb z).subset ?_
  intro q hq
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hchar q hq, hq,rfl⟩⟩

private theorem analytic_boundaryStep {β h : ℝ} (hβ : 1/2 < β)
    (hf : {q : XiZeroCopy | (q.1 : ℂ).re = β}.Finite) :
    AnalyticOnNhd ℝ (fun t => (boundaryStep β h (primeErrorBoundaryTrace β) t : ℂ)) Set.univ := by
  classical
  have he : (fun t => (boundaryStep β h (primeErrorBoundaryTrace β) t : ℂ)) =
      fun t => ∑ q ∈ hf.toFinset, stepAmplitude β h q * expChar (xiCopyOrdinate q) t := by
    funext t
    rw [stepAmplitude_carrier hβ, expSeriesCarrier]
    apply tsum_eq_sum
    intro q hq
    have he : (q.1 : ℂ).re ≠ β := fun h => hq (hf.mem_toFinset.mpr h)
    simp only [stepAmplitude, primeErrorBoundaryAmplitude, if_neg he, mul_zero, zero_mul]
  rw [he]
  exact analytic_finite_sum _ _ _

/-- For an analytic real function periodic in modulus, the sign under a period
is global. If the positive sign fails somewhere, the negative sign holds on a
neighborhood and hence on the entire real line. -/
private theorem eigenvalue_of_analytic_periodic_abs {D : ℝ → ℝ} (p : ℝ)
    (hc : AnalyticOnNhd ℝ (fun t => (D t : ℂ)) Set.univ)
    (hp : Function.Periodic (fun t => |D t|) p) :
    ∃ c : ℂ, ∀ t, (D (t+p) : ℂ) = c * (D t : ℂ) := by
  let F := fun t => (D t : ℂ)
  have hshift : AnalyticOnNhd ℝ (fun t => F (t+p)) Set.univ :=
    hc.comp (analyticOnNhd_id.add analyticOnNhd_const) (fun _ _ => Set.mem_univ _)
  by_cases he : ∀ t, D (t+p) = D t
  · exact ⟨1,fun t => (congrArg Complex.ofReal (he t)).trans (one_mul _).symm⟩
  push Not at he
  obtain ⟨t₀,h₀⟩ := he
  have hne : ∀ᶠ t in 𝓝 t₀, F (t+p) ≠ F t :=
    ((hshift t₀ (Set.mem_univ _)).continuousAt.ne_iff_eventually_ne
      (hc t₀ (Set.mem_univ _)).continuousAt).mp (fun h => h₀ (Complex.ofReal_injective h))
  have he : (fun t => F (t+p)) =ᶠ[𝓝 t₀] (fun t => -F t) := by
    filter_upwards [hne] with t ht
    rcases abs_eq_abs.mp (hp t) with he | he
    · exact (ht (congrArg Complex.ofReal he)).elim
    · exact (congrArg Complex.ofReal he).trans (Complex.ofReal_neg _)
  have hglobal := hshift.eq_of_eventuallyEq hc.neg he
  exact ⟨-1,fun t => (congrFun hglobal t).trans (neg_one_mul _).symm⟩

/-- Two different positive ordinates on the extremal line exclude every trial
radius, including with infinitely many zeros below or on the extremal line. -/
theorem thetaRadial_unbounded_of_distinct_abs_top_ordinates (hΘ : 1/2 < zetaZeroAbscissa)
    (q r : XiZeroCopy) (hq : (q.1 : ℂ).re = zetaZeroAbscissa)
    (hr : (r.1 : ℂ).re = zetaZeroAbscissa) (hne : |xiCopyOrdinate q| ≠ |xiCopyOrdinate r|)
    {γ : ℝ} (hγ : γ ≠ 0) (m : ℕ) :
    IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m) := by
  by_contra hb
  let h := quarterPeriodStep γ
  have hh : 0 < h := quarterPeriodStep_pos hγ
  obtain ⟨c, hc⟩ := eigenvalue_of_analytic_periodic_abs (2*h)
    (analytic_boundaryStep hΘ (finite_top_of_bounded_thetaRadial hΘ hγ hb))
    (boundaryStep_abs_periodic hΘ hb)
  let w := fun p : XiZeroCopy => expChar (xiCopyOrdinate p) h
  have hs (p : XiZeroCopy) (hp : (p.1 : ℂ).re = zetaZeroAbscissa) : w p ^ 2 = c := by
    rw [show w p ^ 2 = expChar (xiCopyOrdinate p) (2*h) by rw [two_mul, char_time_add, sq]]
    exact top_phase_of_step_eigenvalue hΘ hh c hc p hp
  let r' := xiZeroCopyConjEquiv r
  have hr' : (r'.1 : ℂ).re = zetaZeroAbscissa := (Complex.conj_re _).trans hr
  have him : xiCopyOrdinate r' = -xiCopyOrdinate r := Complex.conj_im _
  have hneg : w r' = -w r := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((hs r' hr').trans (hs r hr).symm) with he | he
    · have h := top_step_phase_separates_ordinates hΘ hγ hb r' r hr' hr he
      rw [him] at h
      have hz : xiCopyOrdinate r = 0 := by linarith only [h]
      have hpos := four_lt_abs_xiCopyOrdinate r
      rw [hz, abs_zero] at hpos
      exact ((by norm_num : ¬ (4 : ℝ) < 0) hpos).elim
    · exact he
  apply hne
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((hs q hq).trans (hs r hr).symm) with he | he
  · exact congrArg abs (top_step_phase_separates_ordinates hΘ hγ hb q r hq hr he)
  · have he' := top_step_phase_separates_ordinates hΘ hγ hb q r' hq hr' (he.trans hneg.symm)
    rw [he',him,abs_neg]

/-- At every supercritical extremal abscissa, either the trial radius fails or
the extremal line has precisely one absolute ordinate. -/
theorem extremal_radial_exclusion_or_one_top_pair (hΘ : 1/2 < zetaZeroAbscissa)
    {γ : ℝ} (hγ : γ ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m) ∨
      ∃ q : XiZeroCopy, (q.1 : ℂ).re = zetaZeroAbscissa ∧
        ∀ r : XiZeroCopy, (r.1 : ℂ).re = zetaZeroAbscissa → |xiCopyOrdinate r| = |xiCopyOrdinate q| := by
  by_cases hb : IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)
  · exact Or.inl hb
  obtain ⟨⟨q,hq⟩,_⟩ := (extremal_radial_exclusion_or_commensurable_top hΘ hγ hm).resolve_left hb
  refine Or.inr ⟨q,hq,fun r hr => ?_⟩
  by_contra he
  exact hb (thetaRadial_unbounded_of_distinct_abs_top_ordinates hΘ r q hr hq he hγ m)

#print axioms finite_top_of_bounded_thetaRadial
#print axioms thetaRadial_unbounded_of_distinct_abs_top_ordinates
#print axioms extremal_radial_exclusion_or_one_top_pair

end GaloisForLFunctions.ExceptionalLayerTheory
