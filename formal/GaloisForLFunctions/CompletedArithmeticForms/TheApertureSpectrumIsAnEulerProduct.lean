import GaloisForLFunctions.CompletedArithmeticForms.EisensteinDivisorTrace
import GaloisForLFunctions.CompletedArithmeticForms.TwoAtomApertureSpectrum
import GaloisForLFunctions.CompletedArithmeticForms.WignerSpectralBand
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinSignedMaassWhittakerTail

/-!
# The full-theta aperture spectrum is an Euler product of second-difference inverses

Each ordered pair contributes `cos(b log(n/m)) A(log nm)` with one universal amplitude `A`. Grouping
by the product `N = nm` gives

`S(a, b) = Σ_N τ_b(N) A(log N)`, with `τ_b(N) = N^{ib} Σ_{d∣N} d^{−2ib}`,

so `S` pairs `A` with the Fourier coefficients of `E*(z, ½ + ib)`. Let `σ_p` be the shift by `log p`
and `T_p = (1 − 2 cos(b log p) σ_p + σ_p²)⁻¹ = Σ_k U_k(cos(b log p)) σ_p^k`. Then:

* `thetaFullApertureTail_eq_tsum_trace`: the expansion of `S` over `N`;
* `thetaCenterTail_eq_tsum_trace`: the center tail is the same sum over the Bessel density;
* `eisensteinTrace_eq_whittakerCoefficient`, `signedSqrtWhittakerTail_eq_tsum_trace`: `τ_b` is the
  coefficient of the cusp tail of `E*`;
* `thetaCuspWignerProductFiber_eq_trace_mul_bessel`: each product fibre of the Wigner transform is that
  coefficient times an explicit Bessel profile;
* `primeInsertion_second_difference`: `T_p` inverts `1 − 2 cos(b log p) σ_p + σ_p²`;
* `eulerPartial_insert`, `tendsto_eulerPartial_primesBelow`: `S = Π_p T_p A` at `x = 0`;
* `eulerPartial_exp`: exponentials are eigenfunctions with positive eigenvalue
  `Π_p ‖1 − p^{−s+ib}‖⁻²`;
* `thetaApertureAmplitude_not_laplaceMixture`: `A` is not a positive mixture of those exponentials, so
  the eigenvalue positivity does not reach `S`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped BigOperators
open _root_.RHTower

namespace GaloisForLFunctions.CompletedArithmeticForms

noncomputable section

/-! ## The universal amplitude -/

/-- The amplitude `A(x)` of the aperture spectrum at logarithmic product scale `x`. -/
def thetaApertureAmplitude (a b x : ℝ) : ℝ :=
  Real.exp (-x / 2) * ∫ s in Ioi (0 : ℝ),
    thetaCuspCenterTailWeight a (max 0 (s - x)) * thetaPairCenterTailSpectrum 1 1 s b

/-- Each ordered pair is the ratio cosine times the amplitude at its product scale. -/
theorem thetaPairApertureSpectrum_eq_cos_mul_amplitude {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℝ) :
    thetaPairApertureSpectrum n m a b =
      Real.cos (b * (Real.log n - Real.log m)) *
        thetaApertureAmplitude a b (Real.log ((n : ℝ) * m)) := by
  rw [thetaPairApertureSpectrum_eq_shifted hn hm, thetaApertureAmplitude, mul_assoc]

private theorem integral_weight_max_eq (a h : ℝ) (F : ℝ → ℝ) (hh : 0 ≤ h) :
    (∫ s in Ioi (0 : ℝ), thetaCuspCenterTailWeight a (max 0 (s - h)) * F s) =
      ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r * F (r + h) := by
  have he : (fun s : ℝ => thetaCuspCenterTailWeight a (max 0 (s - h)) * F s) =
      (Ioi h).indicator (fun s => thetaCuspCenterTailWeight a (s - h) * F s) := by
    funext s
    by_cases hs : h < s
    · rw [Set.indicator_of_mem (show s ∈ Ioi h from hs), max_eq_right (sub_nonneg.mpr hs.le)]
    · rw [Set.indicator_of_notMem (show s ∉ Ioi h from hs),
        max_eq_left (sub_nonpos.mpr (not_lt.mp hs))]
      simp only [thetaCuspCenterTailWeight, mul_zero, Real.sinh_zero, Real.cosh_zero,
        zero_mul, add_zero]
  rw [he, integral_indicator measurableSet_Ioi]
  change (∫ s, _ ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi h))) = _
  rw [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hh]
  have ht := GaloisForLFunctions.RHTower.setIntegral_Ioi_comp_add_right
    (fun s : ℝ => thetaCuspCenterTailWeight a (s - h) * F s) h h
  rw [sub_self] at ht
  simp only [add_sub_cancel_right] at ht
  exact ht.symm

private theorem exp_scale_decay {r k : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k) :
    Real.exp (-(Real.pi * Real.exp r * k)) ≤
      Real.exp (-(Real.pi * k)) * Real.exp (-3 * r) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hpk : 3 ≤ Real.pi * k :=
    Real.pi_gt_three.le.trans (le_mul_of_one_le_right Real.pi_pos.le hk)
  have hx := mul_le_mul_of_nonneg_left (Real.add_one_le_exp r)
    (mul_nonneg Real.pi_pos.le hk0)
  have hy := mul_le_mul_of_nonneg_right hpk hr
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith only [hx, hy])

/-- The first-atom tail, frozen at the unit pair, decays doubly exponentially in the center. -/
private theorem abs_unit_tail_le {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) (b : ℝ) :
    |thetaPairCenterTailSpectrum 1 1 (r + x) b| ≤
      4 * besselFirstAtomTailCost 0 * Real.exp (-(Real.pi * Real.exp x)) * Real.exp (-3 * r) := by
  have h := abs_thetaPairCenterTailSpectrum_uniform_le (n := 1) (m := 1) one_pos one_pos
    (add_nonneg hr hx) b
  have he : Real.exp (r + x) = Real.exp r * Real.exp x := Real.exp_add r x
  have hd := exp_scale_decay hr (Real.one_le_exp hx)
  have hC : 0 ≤ 4 * besselFirstAtomTailCost 0 :=
    mul_nonneg (by norm_num) (besselFirstAtomTailCost_nonneg 0)
  refine h.trans ?_
  simp only [Nat.cast_one, mul_one, he]
  rw [show Real.pi * (Real.exp r * Real.exp x) = Real.pi * Real.exp r * Real.exp x by ring,
    mul_assoc (4 * besselFirstAtomTailCost 0)]
  exact mul_le_mul_of_nonneg_left hd hC

/-- The constant of the double-exponential envelope. -/
def thetaApertureEnvelope (a : ℝ) : ℝ :=
  4 * besselFirstAtomTailCost 0 * (18 * a / (9 - a ^ 2) ^ 2)

theorem thetaApertureEnvelope_nonneg {a : ℝ} (ha0 : 0 ≤ a) : 0 ≤ thetaApertureEnvelope a := by
  have := besselFirstAtomTailCost_nonneg 0
  unfold thetaApertureEnvelope
  positivity

/-- **Double-exponential envelope.** `|A(x)| ≤ D e^{−π e^x}` for `x ≥ 0`, uniformly in the frequency. -/
theorem abs_thetaApertureAmplitude_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) {x : ℝ}
    (hx : 0 ≤ x) :
    |thetaApertureAmplitude a b x| ≤
      thetaApertureEnvelope a * Real.exp (-(Real.pi * Real.exp x)) := by
  let K := 4 * besselFirstAtomTailCost 0 * Real.exp (-(Real.pi * Real.exp x))
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) (besselFirstAtomTailCost_nonneg 0))
    (Real.exp_pos _).le
  have hint := (integrableOn_thetaCenterWeight_exp_three ha0 ha).const_mul K
  have hI : |∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r *
      thetaPairCenterTailSpectrum 1 1 (r + x) b| ≤
      K * ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r * Real.exp (-3 * r) := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hw := thetaCuspCenterTailWeight_nonneg ha0 (le_of_lt hr)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    have hb := mul_le_mul_of_nonneg_left (abs_unit_tail_le (le_of_lt hr) hx b) hw
    calc
      _ ≤ _ := hb
      _ = K * (thetaCuspCenterTailWeight a r * Real.exp (-3 * r)) := by
        dsimp only [K]
        ring
  rw [integral_thetaCenterWeight_exp_three ha0 ha] at hI
  have he : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hx])
  unfold thetaApertureAmplitude
  rw [integral_weight_max_eq a x _ hx, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hval : thetaApertureEnvelope a * Real.exp (-(Real.pi * Real.exp x)) =
      K * (18 * a / (9 - a ^ 2) ^ 2) := by
    unfold thetaApertureEnvelope
    dsimp only [K]
    ring
  rw [hval]
  calc
    _ ≤ 1 * |∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r *
        thetaPairCenterTailSpectrum 1 1 (r + x) b| :=
      mul_le_mul_of_nonneg_right he (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hI

/-- `A` is strictly positive on the half-line at every frequency. -/
theorem thetaApertureAmplitude_pos {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (b : ℝ) {x : ℝ}
    (hx : 0 ≤ x) : 0 < thetaApertureAmplitude a b x := by
  unfold thetaApertureAmplitude
  refine mul_pos (Real.exp_pos _) ?_
  rw [integral_weight_max_eq a x _ hx]
  have hF (r : ℝ) (hr : 0 ≤ r) : 0 < thetaPairCenterTailSpectrum 1 1 (r + x) b :=
    thetaPairCenterTailSpectrum_diagonal_pos one_pos (add_nonneg hr hx) b
  have hw : Continuous (thetaCuspCenterTailWeight a) := by
    unfold thetaCuspCenterTailWeight
    fun_prop
  let K := 4 * besselFirstAtomTailCost 0 * Real.exp (-(Real.pi * Real.exp x))
  have hint : IntegrableOn (fun r => thetaCuspCenterTailWeight a r *
      thetaPairCenterTailSpectrum 1 1 (r + x) b) (Ioi 0) := by
    refine ((integrableOn_thetaCenterWeight_exp_three ha0.le ha).const_mul K).mono'
      (hw.stronglyMeasurable.mul ((stronglyMeasurable_thetaPairCenterTailSpectrum 1 1 b).comp_measurable
        (measurable_add_const x))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hw0 := thetaCuspCenterTailWeight_nonneg ha0.le (le_of_lt hr)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    have hb := mul_le_mul_of_nonneg_left (abs_unit_tail_le (le_of_lt hr) hx b) hw0
    calc
      _ ≤ _ := hb
      _ = K * (thetaCuspCenterTailWeight a r * Real.exp (-3 * r)) := by
        dsimp only [K]
        ring
  have hn : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ thetaCuspCenterTailWeight a r *
      thetaPairCenterTailSpectrum 1 1 (r + x) b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (thetaCuspCenterTailWeight_nonneg ha0.le (le_of_lt hr)) (hF r (le_of_lt hr)).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn hint]
  have hs : (Function.support fun r => thetaCuspCenterTailWeight a r *
      thetaPairCenterTailSpectrum 1 1 (r + x) b) ∩ Ioi (0 : ℝ) = Ioi 0 := by
    ext r
    exact ⟨fun h => h.2, fun h => ⟨(mul_pos (thetaCuspCenterTailWeight_pos ha0 h)
      (hF r (le_of_lt h))).ne', h⟩⟩
  rw [hs, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-! ## Grouping over the product -/

private theorem exp_neg_pi_mul_le (p : ℕ × ℕ) :
    Real.exp (-(Real.pi * (((p.1 + 1 : ℕ) : ℝ) * ((p.2 + 1 : ℕ) : ℝ)))) ≤
      Real.exp (-Real.pi) ^ p.1 * Real.exp (-Real.pi) ^ p.2 := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
  have hprod : (p.1 : ℝ) + p.2 ≤ (((p.1 + 1 : ℕ) : ℝ) * ((p.2 + 1 : ℕ) : ℝ)) := by
    push_cast
    nlinarith only [mul_nonneg h1 h2]
  have := mul_le_mul_of_nonneg_left hprod Real.pi_pos.le
  nlinarith only [this]

/-- The pair spectrum is absolutely summable. -/
theorem summable_thetaPairApertureSpectrum {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    Summable fun p : ℕ × ℕ => thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b := by
  set q := Real.exp (-Real.pi) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos)
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hmajor : Summable fun p : ℕ × ℕ => thetaApertureEnvelope a * (q ^ p.1 * q ^ p.2) :=
    (hg.mul_of_nonneg hg (fun n => pow_nonneg hq0 n) (fun n => pow_nonneg hq0 n)).mul_left _
  refine Summable.of_norm_bounded hmajor fun p => ?_
  have hn : 0 < p.1 + 1 := Nat.succ_pos _
  have hm : 0 < p.2 + 1 := Nat.succ_pos _
  have hN : (1 : ℝ) ≤ ((p.1 + 1 : ℕ) : ℝ) * ((p.2 + 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((p.1 + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ ((p.2 + 1 : ℕ) : ℝ) := by exact_mod_cast hm
    exact one_le_mul_of_one_le_of_one_le h1 h2
  rw [thetaPairApertureSpectrum_eq_cos_mul_amplitude hn hm, Real.norm_eq_abs, abs_mul]
  have hA := abs_thetaApertureAmplitude_le ha0 ha b (Real.log_nonneg hN)
  rw [Real.exp_log (by linarith only [hN])] at hA
  have hD := thetaApertureEnvelope_nonneg ha0
  calc
    _ ≤ 1 * |thetaApertureAmplitude a b (Real.log (((p.1 + 1 : ℕ) : ℝ) * ((p.2 + 1 : ℕ) : ℝ)))| :=
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact hA.trans (mul_le_mul_of_nonneg_left (exp_neg_pi_mul_le p) hD)

private theorem tendsto_rectangles :
    Tendsto (fun M : ℕ => Finset.range M ×ˢ Finset.range M) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun M N hMN => ?_) fun p => ?_
  · exact Finset.product_subset_product (Finset.range_mono hMN) (Finset.range_mono hMN)
  · refine ⟨max p.1 p.2 + 1, ?_⟩
    simp only [Finset.mem_product, Finset.mem_range]
    omega

/-- The pair series sums to the literal full-source aperture tail. -/
theorem hasSum_thetaPairApertureSpectrum {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    HasSum (fun p : ℕ × ℕ => thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b)
      (thetaFullApertureTail a b) := by
  have hs := summable_thetaPairApertureSpectrum ha0 ha b
  convert hs.hasSum using 1
  have h1 := hs.hasSum.comp tendsto_rectangles
  refine tendsto_nhds_unique ?_ h1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hK : 0 ≤ 144 * a * besselFirstAtomTailCost 0 /
      ((9 - a ^ 2) ^ 2 * (1 - Real.exp (-Real.pi)) ^ 2) := by
    have := besselFirstAtomTailCost_nonneg 0
    positivity
  have hdecay : Tendsto (fun M : ℕ => 144 * a * besselFirstAtomTailCost 0 /
      ((9 - a ^ 2) ^ 2 * (1 - Real.exp (-Real.pi)) ^ 2) * Real.exp (-Real.pi * ((M : ℝ) + 1)))
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun M : ℕ => Real.exp (-Real.pi * ((M : ℝ) + 1))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      refine Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos Real.pi_pos) ?_
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using hexp.const_mul _
  refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) hdecay
  have hr := thetaFullApertureTail_remainder_le ha0 ha b M
  rw [Function.comp_apply, norm_sub_rev, Real.norm_eq_abs]
  calc
    _ ≤ _ := hr
    _ = _ := by ring

private theorem sum_factorPairs_eq (k : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ q ∈ thetaPositiveFactorPairs k, f (q.1 + 1) (q.2 + 1) =
      ∑ p ∈ k.divisorsAntidiagonal, f p.1 p.2 := by
  refine Finset.sum_nbij' (fun q => (q.1 + 1, q.2 + 1)) (fun p => (p.1 - 1, p.2 - 1)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨hq', fun h0 => by
      rw [h0] at hq'
      exact (Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)) hq'⟩
  · intro p hp
    obtain ⟨hmul, hk⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have h1 : 0 < p.1 := Nat.pos_of_ne_zero fun h => hk (by rw [← hmul, h, zero_mul])
    have h2 : 0 < p.2 := Nat.pos_of_ne_zero fun h => hk (by rw [← hmul, h, mul_zero])
    have h1le : p.1 ≤ k := by
      rw [← hmul]
      exact Nat.le_mul_of_pos_right _ h2
    have h2le : p.2 ≤ k := by
      rw [← hmul]
      exact Nat.le_mul_of_pos_left _ h1
    simp only [thetaPositiveFactorPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2, hmul]
  · intro q _
    simp
  · intro p hp
    obtain ⟨hmul, hk⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have h1 : 0 < p.1 := Nat.pos_of_ne_zero fun h => hk (by rw [← hmul, h, zero_mul])
    have h2 : 0 < p.2 := Nat.pos_of_ne_zero fun h => hk (by rw [← hmul, h, mul_zero])
    simp only [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  · intro q _
    rfl

/-- The fibre of the pair series over `N` is the trace times the amplitude. -/
private theorem sum_fibre_eq (a b : ℝ) (k : ℕ) :
    ∑ q ∈ thetaPositiveFactorPairs k, thetaPairApertureSpectrum (q.1 + 1) (q.2 + 1) a b =
      eisensteinTrace b k * thetaApertureAmplitude a b (Real.log k) := by
  have hterm : ∀ q ∈ thetaPositiveFactorPairs k,
      thetaPairApertureSpectrum (q.1 + 1) (q.2 + 1) a b =
        Real.cos (b * (Real.log ((q.1 + 1 : ℕ) : ℝ) - Real.log ((q.2 + 1 : ℕ) : ℝ))) *
          thetaApertureAmplitude a b (Real.log k) := by
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    rw [thetaPairApertureSpectrum_eq_cos_mul_amplitude (Nat.succ_pos _) (Nat.succ_pos _)]
    have hprod : ((q.1 + 1 : ℕ) : ℝ) * ((q.2 + 1 : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hq'
    rw [hprod]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    sum_factorPairs_eq k (fun n m => Real.cos (b * (Real.log (n : ℝ) - Real.log (m : ℝ))))]
  rfl

/-- **The spectrum is Eisenstein coefficients paired with one amplitude.**
`S(a, b) = Σ_N τ_b(N) A(log N)`. -/
theorem thetaFullApertureTail_eq_tsum_trace {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    thetaFullApertureTail a b =
      ∑' N : ℕ, eisensteinTrace b N * thetaApertureAmplitude a b (Real.log N) := by
  rw [← (hasSum_thetaPairApertureSpectrum ha0 ha b).tsum_eq,
    tsum_eq_tsum_thetaPositiveFactorPairs _ (summable_thetaPairApertureSpectrum ha0 ha b)]
  exact tsum_congr (sum_fibre_eq a b)

/-- The center tail carries the same trace, paired with the explicit Bessel density. -/
theorem thetaCenterTail_eq_tsum_trace {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    (∫ s in Ioi r, (thetaWignerDistribution thetaCuspComplexSource (s / 2) b).re) =
      ∑' N : ℕ, eisensteinTrace b N * thetaPairCenterTailAmplitude N 1 r b := by
  have hs := summable_thetaPairCenterTailSpectrum hr b
  rw [← thetaPairCenterTailSum_eq_fullSource, thetaPairCenterTailSum,
    tsum_eq_tsum_thetaPositiveFactorPairs _ hs]
  refine tsum_congr fun k => ?_
  have hterm : ∀ q ∈ thetaPositiveFactorPairs k,
      thetaPairCenterTailSpectrum (q.1 + 1) (q.2 + 1) r b =
        Real.cos (b * (Real.log ((q.1 + 1 : ℕ) : ℝ) - Real.log ((q.2 + 1 : ℕ) : ℝ))) *
          thetaPairCenterTailAmplitude k 1 r b := by
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    rw [thetaPairCenterTailSpectrum_eq (Nat.succ_pos _) (Nat.succ_pos _) hr]
    congr 1
    have hprod : ((q.1 + 1 : ℕ) : ℝ) * ((q.2 + 1 : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hq'
    unfold thetaPairCenterTailAmplitude
    simp only [Nat.cast_one, mul_one]
    rw [mul_assoc Real.pi, hprod]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    sum_factorPairs_eq k (fun n m => Real.cos (b * (Real.log (n : ℝ) - Real.log (m : ℝ))))]
  rfl

/-! ## The Eisenstein identification -/

/-- `τ_b(N)` is the arithmetic coefficient of the completed Eisenstein series at `u = ib`. -/
theorem eisensteinTrace_eq_whittakerCoefficient (b : ℝ) {N : ℕ} (hN : 0 < N) :
    (eisensteinTrace b N : ℂ) =
      d4BMCompletedEisensteinWhittakerCoefficient ((b : ℂ) * Complex.I) ⟨N, hN⟩ := by
  rw [eisensteinTrace_eq_cpow_sum b hN.ne', d4BMCompletedEisensteinWhittakerCoefficient]

/-- The scalar cusp tail of `E*` on the imaginary axis has the trace as coefficient:
`√Y Σ_N τ_b(N) K_{ib}(2πNY)`. -/
theorem signedSqrtWhittakerTail_eq_tsum_trace (b : ℝ) (Y : ℝ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail ((b : ℂ) * Complex.I) ((b : ℂ) * Complex.I)
        false 0 0 0 Y =
      ∑' N : ℕ, (eisensteinTrace b (N + 1) : ℂ) * (Real.sqrt Y : ℂ) *
        HTGeometry.modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y)
          ((b : ℂ) * Complex.I) := by
  unfold d4BMCompletedEisensteinSignedSqrtWhittakerTail
  refine tsum_congr fun N => ?_
  rw [eisensteinTrace_eq_whittakerCoefficient b (Nat.succ_pos N)]
  simp [d4BMCompletedEisensteinFourierPhase]

/-- The ratio-phase trace of the corpus is `τ_b`. -/
theorem thetaCuspWignerProductFiberDivisorTrace_eq (k : ℕ) (b : ℝ) :
    thetaCuspWignerProductFiberDivisorTrace k b = (eisensteinTrace b k : ℂ) := by
  have hre : ∀ q : ℕ × ℕ, thetaCuspWignerDivisorRatioPhase (q.1 + 1) (q.2 + 1) b =
      ((Real.cos (b * (Real.log ((q.1 + 1 : ℕ) : ℝ) - Real.log ((q.2 + 1 : ℕ) : ℝ))) : ℝ) : ℂ) -
        ((Real.sin (b * (Real.log ((q.1 + 1 : ℕ) : ℝ) - Real.log ((q.2 + 1 : ℕ) : ℝ))) : ℝ) : ℂ) *
          Complex.I := by
    intro q
    unfold thetaCuspWignerDivisorRatioPhase
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  unfold thetaCuspWignerProductFiberDivisorTrace
  simp_rw [hre]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hcos := sum_factorPairs_eq k (fun n m => Real.cos (b * (Real.log (n : ℝ) - Real.log (m : ℝ))))
  have hsin := sum_factorPairs_eq k (fun n m => Real.sin (b * (Real.log (n : ℝ) - Real.log (m : ℝ))))
  rw [sum_sin_eq_zero] at hsin
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, hsin, hcos]
  simp [eisensteinTrace]

/-- **Each Wigner fibre is the Eisenstein coefficient times an explicit Bessel profile.** With
`a = 2πN e^{2u}`, the fibre is `τ_b(N) e^u a² ((a²+9) K_{ib}(a) + 6a K′_{ib}(a))`. -/
theorem thetaCuspWignerProductFiber_eq_trace_mul_bessel {N : ℕ} (hN : 0 < N) (u b : ℝ) :
    thetaCuspWignerProductFiber N u b =
      (Real.exp u : ℂ) * (eisensteinTrace b N : ℂ) *
        (((2 * Real.pi * N * Real.exp (2 * u) : ℝ) : ℂ) ^ 2 *
          ((((2 * Real.pi * N * Real.exp (2 * u) : ℝ) : ℂ) ^ 2 + 9) *
              HTGeometry.modifiedBesselKOrder (2 * Real.pi * N * Real.exp (2 * u))
                ((b : ℂ) * Complex.I) +
            6 * ((2 * Real.pi * N * Real.exp (2 * u) : ℝ) : ℂ) *
              besselArgDeriv ((b : ℂ) * Complex.I) (2 * Real.pi * N * Real.exp (2 * u)))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < 2 * Real.pi * N * Real.exp (2 * u) := by positivity
  rw [thetaCuspWignerProductFiber_eq_divisorTrace_mul_radial,
    thetaCuspWignerProductFiberDivisorTrace_eq, thetaCuspWignerRadialTransform_eq_bessel ha]

/-! ## The prime-insertion operators -/

/-- The operator `T_p = Σ_k U_k(cos(b log p)) σ_p^k`, with `σ_p` the shift by `log p`. -/
def primeInsertion (b : ℝ) (p : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, eisensteinTrace b (p ^ k) * f (x + k * Real.log p)

/-- The partial Euler product on a finite set of primes, as a sum over integers it factors. -/
def eulerPartial (b : ℝ) (P : Finset ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : Nat.factoredNumbers P, eisensteinTrace b n * f (x + Real.log (n : ℕ))

/-- The decay class on which the operators are composed. -/
def DoubleExpBound (f : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → |f x| ≤ C * Real.exp (-(Real.pi * Real.exp x))

theorem thetaApertureAmplitude_doubleExpBound {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    DoubleExpBound (thetaApertureAmplitude a b) (thetaApertureEnvelope a) :=
  fun _ hx => abs_thetaApertureAmplitude_le ha0 ha b hx

/-- The amplitude series over all integers converges absolutely at every nonnegative base point. -/
theorem summable_trace_mul_of_bound (b : ℝ) {f : ℝ → ℝ} {C : ℝ} (hf : DoubleExpBound f C)
    (hC : 0 ≤ C) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun n : ℕ => eisensteinTrace b n * f (x + Real.log n) := by
  have hmajor : Summable fun n : ℕ => C * ((n : ℝ) ^ 1 * Real.exp (-Real.pi * n)) :=
    (Real.summable_pow_mul_exp_neg_nat_mul 1 Real.pi_pos).mul_left C
  refine Summable.of_norm_bounded hmajor fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [eisensteinTrace_zero, zero_mul, norm_zero]
    positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn1
  rw [Real.norm_eq_abs, abs_mul]
  have hb := hf _ (add_nonneg hx hlog)
  have hexp : (n : ℝ) ≤ Real.exp (x + Real.log n) := by
    rw [Real.exp_add, Real.exp_log (by linarith only [hn1])]
    exact le_mul_of_one_le_left (by linarith only [hn1]) (Real.one_le_exp hx)
  have hd : Real.exp (-(Real.pi * Real.exp (x + Real.log n))) ≤ Real.exp (-Real.pi * n) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hexp Real.pi_pos.le]
  calc
    _ ≤ (n : ℝ) * (C * Real.exp (-Real.pi * n)) :=
      mul_le_mul (abs_eisensteinTrace_le b n) (hb.trans (mul_le_mul_of_nonneg_left hd hC))
        (abs_nonneg _) (by linarith only [hn1])
    _ = _ := by ring

/-- Over the empty set of primes, the partial product is evaluation. -/
theorem eulerPartial_empty (b : ℝ) (f : ℝ → ℝ) (x : ℝ) : eulerPartial b ∅ f x = f x := by
  unfold eulerPartial
  rw [tsum_subtype (Nat.factoredNumbers ∅)
    (fun n : ℕ => eisensteinTrace b n * f (x + Real.log n)), Nat.factoredNumbers_empty,
    tsum_eq_single 1]
  · simp
  · intro n hn
    simp [hn]

/-- **Inserting one prime applies `T_p`.** -/
theorem eulerPartial_insert (b : ℝ) {p : ℕ} (hp : p.Prime) {P : Finset ℕ} (hs : p ∉ P) {f : ℝ → ℝ}
    {C : ℝ} (hf : DoubleExpBound f C) (hC : 0 ≤ C) {x : ℝ} (hx : 0 ≤ x) :
    eulerPartial b (insert p P) f x = primeInsertion b p (eulerPartial b P f) x := by
  let e := Nat.equivProdNatFactoredNumbers hp hs
  let G : Nat.factoredNumbers (insert p P) → ℝ :=
    fun m => eisensteinTrace b m * f (x + Real.log (m : ℕ))
  have hG : Summable G := (summable_trace_mul_of_bound b hf hC hx).subtype _
  have hG' : Summable (G ∘ e) := e.summable_iff.mpr hG
  unfold eulerPartial primeInsertion
  rw [← e.tsum_eq G, hG'.tsum_prod]
  refine tsum_congr fun k => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hn : (n : ℕ) ≠ 0 := Nat.ne_zero_of_mem_factoredNumbers n.2
  have hcop : (p ^ k).Coprime (n : ℕ) := Nat.Coprime.pow_left _ (hp.factoredNumbers_coprime hs n.2)
  have happ : ((e (k, n) : Nat.factoredNumbers (insert p P)) : ℕ) = p ^ k * n :=
    Nat.equivProdNatFactoredNumbers_apply' hp hs (k, n)
  have hlog : Real.log ((p ^ k * n : ℕ) : ℝ) = k * Real.log p + Real.log (n : ℕ) := by
    push_cast
    rw [Real.log_mul (by exact_mod_cast (pow_ne_zero k hp.ne_zero)) (by exact_mod_cast hn),
      Real.log_pow]
  change eisensteinTrace b ((e (k, n) : Nat.factoredNumbers (insert p P)) : ℕ) *
    f (x + Real.log (((e (k, n) : Nat.factoredNumbers (insert p P)) : ℕ) : ℝ)) = _
  rw [happ, eisensteinTrace_mul_of_coprime b hcop, hlog, mul_assoc, add_assoc]

/-- A double-exponential function has a summable insertion series at every point right of `0`. -/
private theorem summable_insertion (b : ℝ) {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ} {C : ℝ}
    (hf : DoubleExpBound f C) (hC : 0 ≤ C) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun k : ℕ => eisensteinTrace b (p ^ k) * f (x + k * Real.log p) := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hmajor : Summable fun k : ℕ => C * (((k + 1 : ℕ) : ℝ) ^ 1 *
      Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ))) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul 1 Real.pi_pos)).mul_left C
  refine Summable.of_norm_bounded hmajor fun k => ?_
  have hpow : ((k + 1 : ℕ) : ℝ) ≤ Real.exp (x + k * Real.log p) := by
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ k := by
      have := Nat.lt_pow_self (n := k) hp.one_lt
      exact_mod_cast this
    have h2 : (p : ℝ) ^ k = Real.exp (k * Real.log p) := by
      rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hp.pos)]
    rw [Real.exp_add]
    calc
      _ ≤ Real.exp (k * Real.log p) := h2 ▸ h1
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp hx)
  have hb := hf _ (add_nonneg hx (mul_nonneg (Nat.cast_nonneg k) hlogp))
  have hd : Real.exp (-(Real.pi * Real.exp (x + k * Real.log p))) ≤
      Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hpow Real.pi_pos.le]
  rw [Real.norm_eq_abs, abs_mul]
  have hU := abs_eisensteinTrace_prime_pow_le b hp k
  calc
    _ ≤ ((k : ℝ) + 1) * (C * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ))) :=
      mul_le_mul hU (hb.trans (mul_le_mul_of_nonneg_left hd hC)) (abs_nonneg _) (by positivity)
    _ = _ := by
      push_cast
      ring

/-- **`T_p` inverts `1 − 2 cos(b log p) σ_p + σ_p²`.** -/
theorem primeInsertion_second_difference (b : ℝ) {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ} {C : ℝ}
    (hf : DoubleExpBound f C) (hC : 0 ≤ C) {x : ℝ} (hx : 0 ≤ x) :
    primeInsertion b p f x -
        2 * Real.cos (b * Real.log p) * primeInsertion b p f (x + Real.log p) +
        primeInsertion b p f (x + 2 * Real.log p) = f x := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have h := tsum_trace_second_difference b hp (g := fun k => f (x + k * Real.log p))
    (summable_insertion b hp hf hC hx)
    (by
      have := summable_insertion b hp hf hC (add_nonneg hx hlogp)
      refine this.congr fun k => ?_
      congr 2
      push_cast
      ring)
    (by
      have := summable_insertion b hp hf hC (add_nonneg hx (mul_nonneg (by norm_num) hlogp))
      refine this.congr fun k => ?_
      congr 2
      push_cast
      ring)
  unfold primeInsertion
  have e1 : (∑' k : ℕ, eisensteinTrace b (p ^ k) * f (x + Real.log p + k * Real.log p)) =
      ∑' k : ℕ, eisensteinTrace b (p ^ k) * f (x + ((k + 1 : ℕ) : ℝ) * Real.log p) := by
    refine tsum_congr fun k => ?_
    congr 2
    push_cast
    ring
  have e2 : (∑' k : ℕ, eisensteinTrace b (p ^ k) * f (x + 2 * Real.log p + k * Real.log p)) =
      ∑' k : ℕ, eisensteinTrace b (p ^ k) * f (x + ((k + 2 : ℕ) : ℝ) * Real.log p) := by
    refine tsum_congr fun k => ?_
    congr 2
    push_cast
    ring
  rw [e1, e2]
  simpa using h

/-- The partial products of the amplitude converge to the full spectrum. -/
theorem tendsto_eulerPartial_primesBelow (b : ℝ) {f : ℝ → ℝ} {C : ℝ} (hf : DoubleExpBound f C)
    (hC : 0 ≤ C) :
    Tendsto (fun N : ℕ => eulerPartial b N.primesBelow f 0) atTop
      (𝓝 (∑' n : ℕ, eisensteinTrace b n * f (Real.log n))) := by
  have hs := summable_trace_mul_of_bound b hf hC le_rfl
  simp only [zero_add] at hs
  have hrew (N : ℕ) : eulerPartial b N.primesBelow f 0 =
      ∑' n : ℕ, (Nat.factoredNumbers N.primesBelow).indicator
        (fun n : ℕ => eisensteinTrace b n * f (Real.log n)) n := by
    unfold eulerPartial
    simp only [zero_add]
    exact tsum_subtype _ (fun n : ℕ => eisensteinTrace b n * f (Real.log n))
  simp_rw [hrew]
  refine tendsto_tsum_of_dominated_convergence hs.norm (fun n => ?_)
    (Eventually.of_forall fun N n => ?_)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop n] with N hN
    have hmem : n ∈ Nat.factoredNumbers N.primesBelow := by
      rw [Nat.mem_factoredNumbers]
      refine ⟨hn.ne', fun q hq => ?_⟩
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqd := Nat.dvd_of_mem_primeFactorsList hq
      exact Nat.mem_primesBelow.mpr ⟨(Nat.le_of_dvd hn hqd).trans_lt hN, hqp⟩
    rw [Set.indicator_of_mem hmem]
  · by_cases hmem : n ∈ Nat.factoredNumbers N.primesBelow
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact norm_nonneg _

/-- **`S = Π_p T_p A` at the origin.** -/
theorem tendsto_eulerPartial_thetaApertureAmplitude {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    Tendsto (fun N : ℕ => eulerPartial b N.primesBelow (thetaApertureAmplitude a b) 0) atTop
      (𝓝 (thetaFullApertureTail a b)) := by
  rw [thetaFullApertureTail_eq_tsum_trace ha0 ha b]
  exact tendsto_eulerPartial_primesBelow b (thetaApertureAmplitude_doubleExpBound ha0 ha b)
    (thetaApertureEnvelope_nonneg ha0)

/-! ## Exponentials are eigenfunctions -/

private theorem exp_neg_mul_log {s : ℝ} {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-s * Real.log n) = (n : ℝ) ^ (-s) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn), mul_comm]

private theorem exp_shift_eq (s x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-s * (x + Real.log n)) = Real.exp (-s * x) * (n : ℝ) ^ (-s) := by
  rw [mul_add, Real.exp_add, exp_neg_mul_log hn]

/-- The multiplicative function whose Euler product computes the eigenvalue. -/
private def tiltedTrace (b s : ℝ) (n : ℕ) : ℝ := eisensteinTrace b n * (n : ℝ) ^ (-s)

private theorem tiltedTrace_prime_pow (b s : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    tiltedTrace b s (p ^ k) = eisensteinTrace b (p ^ k) * ((p : ℝ) ^ (-s)) ^ k := by
  unfold tiltedTrace
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), mul_comm]

private theorem base_rpow_bounds {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ) ^ (-s) ∧ (p : ℝ) ^ (-s) < 1 :=
  ⟨Real.rpow_nonneg (by positivity) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)⟩

/-- **Exponentials are eigenfunctions of every partial product.** The eigenvalue is
`Π_{p ∈ P} (1 − 2 cos(b log p) p^{−s} + p^{−2s})⁻¹ = Π_{p ∈ P} ‖1 − p^{−s+ib}‖⁻²`. -/
theorem eulerPartial_exp (b : ℝ) (P : Finset ℕ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    eulerPartial b P (fun y => Real.exp (-s * y)) x =
      Real.exp (-s * x) * ∏ p ∈ P with p.Prime,
        (1 - 2 * Real.cos (b * Real.log p) * (p : ℝ) ^ (-s) + ((p : ℝ) ^ (-s)) ^ 2)⁻¹ := by
  have hone : tiltedTrace b s 1 = 1 := by simp [tiltedTrace]
  have hmul : ∀ {m n : ℕ}, m.Coprime n →
      tiltedTrace b s (m * n) = tiltedTrace b s m * tiltedTrace b s n := by
    intro m n h
    unfold tiltedTrace
    rw [eisensteinTrace_mul_of_coprime b h]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    ring
  have hsum : ∀ {p : ℕ}, p.Prime → Summable fun k : ℕ => ‖tiltedTrace b s (p ^ k)‖ := by
    intro p hp
    obtain ⟨h0, h1⟩ := base_rpow_bounds hs hp
    have hm := (summable_trace_mul_pow b hp h0 h1).norm
    exact hm.congr fun k => by rw [tiltedTrace_prime_pow b s hp]
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hone hmul hsum P).2
  unfold eulerPartial
  have hterm : ∀ n : Nat.factoredNumbers P,
      eisensteinTrace b n * Real.exp (-s * (x + Real.log (n : ℕ))) =
        Real.exp (-s * x) * tiltedTrace b s n := by
    intro n
    rw [exp_shift_eq s x (Nat.ne_zero_of_mem_factoredNumbers n.2)]
    unfold tiltedTrace
    ring
  rw [tsum_congr hterm, tsum_mul_left, hE.tsum_eq]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := (Finset.mem_filter.mp hp).2
  obtain ⟨h0, h1⟩ := base_rpow_bounds hs hpp
  simp_rw [tiltedTrace_prime_pow b s hpp]
  exact tsum_trace_mul_pow b hpp h0 h1

/-- The eigenvalue is strictly positive. -/
theorem eulerPartial_exp_pos (b : ℝ) (P : Finset ℕ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 < eulerPartial b P (fun y => Real.exp (-s * y)) x := by
  rw [eulerPartial_exp b P hs x]
  refine mul_pos (Real.exp_pos _) (Finset.prod_pos fun p hp => inv_pos.mpr ?_)
  obtain ⟨h0, h1⟩ := base_rpow_bounds hs (Finset.mem_filter.mp hp).2
  exact eulerDenominator_pos _ h0 h1

/-! ## The amplitude is outside the eigencone -/

/-- A nonnegative Laplace mixture is log-convex along integer points. -/
private theorem mixture_log_convex {μ : Measure ℝ} {A : ℝ → ℝ}
    (hμ : ∀ x : ℝ, 0 ≤ x → Integrable (fun s => Real.exp (-s * x)) μ)
    (hA : ∀ x : ℝ, 0 ≤ x → A x = ∫ s, Real.exp (-s * x) ∂μ) {x : ℝ} (hx : 0 ≤ x) (l : ℝ) :
    0 ≤ A x - 2 * l * A (x + 1) + l ^ 2 * A (x + 2) := by
  have h0 := hμ x hx
  have h1 := hμ (x + 1) (by linarith only [hx])
  have h2 := hμ (x + 2) (by linarith only [hx])
  rw [hA x hx, hA (x + 1) (by linarith only [hx]), hA (x + 2) (by linarith only [hx]),
    ← integral_const_mul, ← integral_const_mul,
    ← integral_sub h0 (h1.const_mul _), ← integral_add (h0.sub (h1.const_mul _)) (h2.const_mul _)]
  refine integral_nonneg fun s => ?_
  have he : Real.exp (-s * x) - 2 * l * Real.exp (-s * (x + 1)) + l ^ 2 * Real.exp (-s * (x + 2)) =
      Real.exp (-s * x) * (1 - l * Real.exp (-s)) ^ 2 := by
    have e1 : Real.exp (-s * (x + 1)) = Real.exp (-s * x) * Real.exp (-s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-s * (x + 2)) = Real.exp (-s * x) * Real.exp (-s) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    ring
  change 0 ≤ Real.exp (-s * x) - 2 * l * Real.exp (-s * (x + 1)) + l ^ 2 * Real.exp (-s * (x + 2))
  rw [he]
  positivity

/-- **The amplitude is not a positive Laplace mixture.** Mixtures are log-convex, so they decay at most
exponentially, while `A` decays doubly exponentially. So `A` lies outside the cone on which every `T_p`
acts with positive eigenvalues. -/
theorem thetaApertureAmplitude_not_laplaceMixture {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (b : ℝ) :
    ¬ ∃ μ : Measure ℝ, (∀ x : ℝ, 0 ≤ x → Integrable (fun s => Real.exp (-s * x)) μ) ∧
      ∀ x : ℝ, 0 ≤ x → thetaApertureAmplitude a b x = ∫ s, Real.exp (-s * x) ∂μ := by
  rintro ⟨μ, hμ, hA⟩
  set A : ℕ → ℝ := fun n => thetaApertureAmplitude a b n with hAdef
  have hpos (n : ℕ) : 0 < A n := thetaApertureAmplitude_pos ha0 ha b (Nat.cast_nonneg n)
  have hconv (n : ℕ) : A (n + 1) ^ 2 ≤ A n * A (n + 2) := by
    have hl := mixture_log_convex hμ hA (Nat.cast_nonneg n) (A (n + 1) / A (n + 2))
    have e1 : thetaApertureAmplitude a b ((n : ℝ) + 1) = A (n + 1) := by
      simp only [hAdef]
      push_cast
      rfl
    have e2 : thetaApertureAmplitude a b ((n : ℝ) + 2) = A (n + 2) := by
      simp only [hAdef]
      push_cast
      rfl
    rw [e1, e2] at hl
    have hd := hpos (n + 2)
    have heq : A n - 2 * (A (n + 1) / A (n + 2)) * A (n + 1) +
        (A (n + 1) / A (n + 2)) ^ 2 * A (n + 2) = A n - A (n + 1) ^ 2 / A (n + 2) := by
      field_simp
      ring
    change 0 ≤ A n - 2 * (A (n + 1) / A (n + 2)) * A (n + 1) +
        (A (n + 1) / A (n + 2)) ^ 2 * A (n + 2) at hl
    rw [heq, sub_nonneg, div_le_iff₀ hd] at hl
    exact hl
  -- The ratio is nondecreasing, so `A n ≥ A 0 ρ^n`.
  set ρ := A 1 / A 0 with hρ
  have hρ0 : 0 < ρ := div_pos (hpos 1) (hpos 0)
  have hratio (n : ℕ) : ρ * A n ≤ A (n + 1) := by
    induction n with
    | zero =>
        simp only [hρ]
        rw [div_mul_cancel₀ _ (hpos 0).ne']
    | succ k ih =>
        have h := hconv k
        have hk := hpos k
        have hm := mul_le_mul_of_nonneg_right ih (hpos (k + 1)).le
        have : ρ * A (k + 1) * A k ≤ A (k + 1 + 1) * A k := by
          calc
            _ = (ρ * A k) * A (k + 1) := by ring
            _ ≤ A (k + 1) * A (k + 1) := hm
            _ = A (k + 1) ^ 2 := by ring
            _ ≤ A k * A (k + 2) := h
            _ = _ := by ring
        exact le_of_mul_le_mul_right this hk
  have hlower (n : ℕ) : A 0 * ρ ^ n ≤ A n := by
    induction n with
    | zero => simp
    | succ k ih =>
        calc
          _ = ρ * (A 0 * ρ ^ k) := by rw [pow_succ]; ring
          _ ≤ ρ * A k := mul_le_mul_of_nonneg_left ih hρ0.le
          _ ≤ _ := hratio k
  -- The doubly exponential envelope contradicts the geometric lower bound.
  have hD := thetaApertureEnvelope_nonneg ha0.le (a := a)
  have hupper (n : ℕ) : A n ≤ thetaApertureEnvelope a * Real.exp (-(Real.pi * Real.exp n)) :=
    (le_abs_self _).trans (abs_thetaApertureAmplitude_le ha0.le ha b (Nat.cast_nonneg n))
  have hlim : Tendsto (fun n : ℕ => thetaApertureEnvelope a *
      Real.exp (-(Real.pi * Real.exp n)) / (A 0 * ρ ^ n)) atTop (𝓝 0) := by
    have hquot (n : ℕ) : thetaApertureEnvelope a * Real.exp (-(Real.pi * Real.exp n)) /
        (A 0 * ρ ^ n) = (thetaApertureEnvelope a / A 0) *
          Real.exp (-(Real.pi * Real.exp n) - n * Real.log ρ) := by
      have hρpow : ρ ^ n = Real.exp (n * Real.log ρ) := by
        rw [Real.exp_nat_mul, Real.exp_log hρ0]
      rw [hρpow, sub_eq_add_neg, Real.exp_add, Real.exp_neg (n * Real.log ρ)]
      field_simp
    simp_rw [hquot]
    have hexp : Tendsto (fun n : ℕ => -(Real.pi * Real.exp n) - n * Real.log ρ) atTop atBot := by
      have hbound (n : ℕ) : -(Real.pi * Real.exp n) - n * Real.log ρ ≤
          -((n : ℝ) ^ 2) + |Real.log ρ| * n := by
        have hq := Real.quadratic_le_exp_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        have hsq := sq_nonneg (n : ℝ)
        have hp : (n : ℝ) ^ 2 ≤ Real.pi * Real.exp n := by
          have h3 := Real.pi_gt_three
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith only [hq, hsq, h3, hn0, Real.exp_pos (n : ℝ)]
        have hl := neg_abs_le (Real.log ρ)
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith only [hp, mul_le_mul_of_nonneg_right hl hn0]
      refine tendsto_atBot_mono hbound ?_
      have hq : Tendsto (fun x : ℝ => -(x ^ 2) + |Real.log ρ| * x) atTop atBot := by
        have hh : Tendsto (fun x : ℝ => x * (-x + |Real.log ρ|)) atTop atBot := by
          refine Tendsto.atTop_mul_atBot₀ tendsto_id ?_
          exact tendsto_atBot_add_const_right _ _ tendsto_neg_atTop_atBot
        refine hh.congr fun x => ?_
        ring
      exact hq.comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using (Real.tendsto_exp_atBot.comp hexp).const_mul
      (thetaApertureEnvelope a / A 0)
  have hsmall := hlim.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))
  obtain ⟨n, hn⟩ := hsmall.exists
  have hden : 0 < A 0 * ρ ^ n := mul_pos (hpos 0) (pow_pos hρ0 n)
  rw [div_lt_one hden] at hn
  exact absurd ((hlower n).trans (hupper n)) (not_le.mpr hn)

end

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.thetaFullApertureTail_eq_tsum_trace
#print axioms GaloisForLFunctions.CompletedArithmeticForms.thetaCenterTail_eq_tsum_trace
#print axioms GaloisForLFunctions.CompletedArithmeticForms.signedSqrtWhittakerTail_eq_tsum_trace
#print axioms GaloisForLFunctions.CompletedArithmeticForms.thetaCuspWignerProductFiber_eq_trace_mul_bessel
#print axioms GaloisForLFunctions.CompletedArithmeticForms.eulerPartial_insert
#print axioms GaloisForLFunctions.CompletedArithmeticForms.primeInsertion_second_difference
#print axioms GaloisForLFunctions.CompletedArithmeticForms.tendsto_eulerPartial_thetaApertureAmplitude
#print axioms GaloisForLFunctions.CompletedArithmeticForms.eulerPartial_exp
#print axioms GaloisForLFunctions.CompletedArithmeticForms.thetaApertureAmplitude_not_laplaceMixture
