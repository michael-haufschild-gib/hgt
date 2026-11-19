import GaloisForLFunctions.HilbertMetric.Dynamics.AffineCompositionConditionNumber
import GaloisForLFunctions.FiniteFreeProbability.ImaginaryPartDichotomy
import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeHardyTheorem

/-!
# Which affine normalizations preserve the extreme Jensen root test?

For the reversed unshifted Jensen polynomials of Ξ, composition with a
positive real slope `p_d` divides all imaginary heights by `p_d`.
A bounded upper height along infinitely many degrees detects RH exactly
when the slopes have no linearly growing subsequence. At linear scale
the affine coordinate itself produces a bounded strip unconditionally.
-/

noncomputable section
open Complex Polynomial Filter Topology Metric
open GaloisForLFunctions.HTGeometry RHTower
open GaloisForLFunctions.HilbertMetric.Dynamics.AffineComposition
namespace FiniteFreeProbability

/-- A compact zero-free neighborhood of the origin excludes Jensen roots
beyond a fixed multiple of the degree. -/
theorem eventually_linear_norm_jensen_xi :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop, ∀ z : ℂ,
      (jensenRev d xiSeries).IsRoot z → ‖z‖ ≤ C*d := by
  have hs (z : ℂ) : HasSum (fun k => xiCoeff k*z^k) (XiC z) := by
    simpa only [xiCoeff, xiSeries, PowerSeries.coeff_mk] using hasSum_xiSeries z
  have hloc := tendstoLocallyUniformly_scaledJensen
    (summable_norm_mul_pow_of_summable fun z => (hs z).summable) (ψ := id) tendsto_id
  have hfun : (fun z => ∑' k, xiCoeff k*z^k) = XiC := funext fun z => (hs z).tsum_eq
  rw [hfun] at hloc
  have hp := norm_pos_iff.mpr XiC_zero_ne
  have hv : ∀ᶠ z in 𝓝 (0 : ℂ), ‖XiC 0‖/2 < ‖XiC z‖ :=
    XiC_differentiable.continuous.continuousAt.norm.tendsto.eventually_const_lt (by linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hv
  have hclose := (tendstoLocallyUniformly_iff_forall_isCompact.mp hloc)
    (closedBall 0 r) (isCompact_closedBall 0 r)
  have hu := Metric.tendstoUniformlyOn_iff.mp hclose (‖XiC 0‖/2) (by linarith)
  refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
  filter_upwards [hu, eventually_gt_atTop 0] with d hd hd0 z hz
  by_contra! hbig
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  have hzpos : 0 < ‖z‖ := (mul_pos (inv_pos.mpr hr) hdpos).trans hbig
  have hz0 := norm_pos_iff.mp hzpos
  let u := (d : ℂ)/z
  have hu0 : u ≠ 0 := div_ne_zero (by exact_mod_cast hd0.ne') hz0
  have hu_norm : ‖u‖ < r := by
    rw [show ‖u‖ = d/‖z‖ by simp [u], div_lt_iff₀ hzpos]
    have h := (div_lt_iff₀ hr).mp (by simpa [div_eq_inv_mul] using hbig : (d : ℝ)/r < ‖z‖)
    linarith only [h]
  have hzu : (d : ℂ)/u = z := by dsimp [u]; field_simp [hz0, (by exact_mod_cast hd0.ne' : (d:ℂ) ≠ 0)]
  have he := eval_jensenRev_div xiCoeff hd0 hu0
  rw [mk_xiCoeff, hzu, hz] at he
  have hzero := (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hz0)
  have hh := hd u (mem_closedBall_zero_iff.mpr hu_norm.le)
  change dist (XiC u) (scaledJensen xiCoeff d u) < _ at hh
  rw [hzero, dist_zero_right] at hh
  exact (hball (by simpa using hu_norm)).not_gt hh

private theorem linear_height_obstruction (h : ¬RiemannHypothesis) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ d : ℕ in atTop, ∃ z : ℂ,
      (jensenRev d xiSeries).IsRoot z ∧ κ*d ≤ z.im := by
  have he : expSeries (0 : ℂ) = 1 := by
    ext k
    rw [expSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    cases k <;> simp
  have hm : mollifiedXiSeries ∅ 1 0 = xiSeries := by
    rw [mollifiedXiSeries, translatedMobiusProduct, Finset.prod_empty, mul_one,
      Complex.ofReal_zero, mul_zero, he, mul_one]
  simpa only [hm] using exists_linear_im_of_not_riemannHypothesis h ∅ (σ := 1) one_pos 0

private theorem chart_strip_iff (d : ℕ) {p : ℝ} (hp : 0 < p) (K : ℝ) :
    (∀ z : ℂ, ((jensenRev d xiSeries).comp (chart p)).IsRoot z → z.im ≤ K) ↔
    ∀ z : ℂ, (jensenRev d xiSeries).IsRoot z → z.im ≤ K*p := by
  simpa only [mul_div_cancel_right₀ _ hp.ne'] using root_height_window (jensenRev d xiSeries) hp (K*p)

private theorem chart_upper_of_scale {c : ℝ} (hc : 0 < c) {C : ℝ} (d : ℕ) {p : ℝ} (hp : 0 < p)
    (hroot : ∀ z : ℂ, (jensenRev d xiSeries).IsRoot z → ‖z‖ ≤ C*d)
    (hC : 0 ≤ C) (hscale : c*d ≤ p) :
    ∀ z : ℂ, ((jensenRev d xiSeries).comp (chart p)).IsRoot z → z.im ≤ C/c := by
  apply (chart_strip_iff d hp _).mpr
  intro z hz
  refine ((Complex.im_le_norm z).trans (hroot z hz)).trans ?_
  calc C*d = C/c*(c*d) := by field_simp [hc.ne']
       _ ≤ _ := mul_le_mul_of_nonneg_left hscale (div_nonneg hC hc.le)

/-- Exact classification for an arbitrary positive sequence of chart slopes,
including oscillatory choices with no asymptotic scale. -/
theorem bounded_chart_jensen_heights_iff (p : ℕ → ℝ) (hp : ∀ d, 0 < p d) :
    (∃ K : ℝ, ∃ᶠ d : ℕ in atTop, ∀ z : ℂ,
      ((jensenRev d xiSeries).comp (chart (p d))).IsRoot z → z.im ≤ K) ↔
    RiemannHypothesis ∨ ∃ c : ℝ, 0 < c ∧ ∃ᶠ d : ℕ in atTop, c*d ≤ p d := by
  constructor
  · rintro ⟨K,hK⟩
    by_cases h : RiemannHypothesis
    · exact Or.inl h
    obtain ⟨κ,hκ,hbad⟩ := linear_height_obstruction h
    let B := max K 1
    have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine Or.inr ⟨κ/B, div_pos hκ hB, (hK.and_eventually hbad).mono ?_⟩
    rintro d ⟨hd,z,hz,hgain⟩
    have he := ((chart_strip_iff d (hp d) K).mp hd z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left K 1) (hp d).le)
    rw [div_mul_eq_mul_div, div_le_iff₀ hB, mul_comm (p d)]
    exact hgain.trans he
  · rintro (h | ⟨c,hc,hscale⟩)
    · refine ⟨0, Frequently.of_forall fun d => (chart_strip_iff d (hp d) 0).mpr ?_⟩
      intro z hz
      rw [im_eq_zero_of_isRoot_jensenRev_xiSeries h d hz, zero_mul]
    · obtain ⟨C,hC,hev⟩ := eventually_linear_norm_jensen_xi
      refine ⟨C/c, (hscale.and_eventually hev).mono ?_⟩
      rintro d ⟨hd,hz⟩
      exact chart_upper_of_scale hc d (hp d) hz hC.le hd

/-- A slope equal to the degree gives bounded chart heights for every
sufficiently large degree, independently of the zeta zeros. -/
theorem linear_chart_hides_extreme_heights :
    ∃ K : ℝ, ∀ᶠ d : ℕ in atTop, ∀ z : ℂ,
      ((jensenRev d xiSeries).comp (chart (d:ℝ))).IsRoot z → z.im ≤ K := by
  obtain ⟨C,hC,hev⟩ := eventually_linear_norm_jensen_xi
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_gt_atTop 0] with d hd hd0
  simpa using chart_upper_of_scale (c := 1) one_pos d (Nat.cast_pos.mpr hd0) hd hC.le
    (by simp : (1:ℝ)*d ≤ d)

#print axioms eventually_linear_norm_jensen_xi
#print axioms bounded_chart_jensen_heights_iff
#print axioms linear_chart_hides_extreme_heights
end FiniteFreeProbability
