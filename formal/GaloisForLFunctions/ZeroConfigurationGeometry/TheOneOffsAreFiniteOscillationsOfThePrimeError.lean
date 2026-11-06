import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound
import GaloisForLFunctions.RHTower.LiEvenCrossInfiniteCriticalAmplitudeSchattenBoundaryNoGo
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimeErrorExpansionLocatesZeros

/-!
# The failure of the asymptotic abscissa law is a finite oscillation of the prime error

`AsymptoticAbscissaLaw` fails exactly when there are `β > ½`, `η > 0` and a nonzero real
trigonometric polynomial `T` with

`ψ(x) − x = x^β T(log x) + O(x^{β−η})`

(`not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation`).

**From an expansion to a one-off.**  The Mellin transform of the remainder locates all zeros right of
`β − η` on the finite set `β + iω` and forces a zero at each nonzero frequency
(`ThePrimeErrorExpansionLocatesZeros`).

**From a one-off to an expansion.**  Let `β` be the top abscissa and `β₁ < β` the abscissa of all the
other zeros.  The genus-kernel explicit formula squeezes `ψ(x)` between window averages of width
`H = x^{(β+β₁)/2}`.  A top zero contributes `−x^ρ/ρ` up to `2H`.  Every other window term is at most
both `2x^{β₁}/|ρ|` and `16 x^{β₁}(x/H)/(|ρ||1−ρ|)`; interpolating with exponent `θ = (β−β₁)/4` and
using that the zeros have convergence exponent one gives a total of `≪ x^{β₁+θ}`.
-/

open Complex Filter Topology MeasureTheory Set
open RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ### The statement -/

/-- A real trigonometric polynomial `T(u) = Re Σ_{ω∈S} c(ω) e^{iωu}`. -/
def finiteOscillation (S : Finset ℝ) (c : ℝ → ℂ) (u : ℝ) : ℝ :=
  (∑ ω ∈ S, c ω * cexp (I * ω * u)).re

/-- **The prime error is a single finite oscillation at leading order.** -/
def PrimeErrorIsFiniteOscillation : Prop :=
  ∃ β η : ℝ, 1 / 2 < β ∧ 0 < η ∧ ∃ (S : Finset ℝ) (c : ℝ → ℂ), (∃ u, finiteOscillation S c u ≠ 0) ∧
    ∃ C x₀ : ℝ, ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ (β - η)

/-! ### Convergence exponent one -/

theorem summable_abs_im_inv_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun q : XiZeroCopy => |(q.1 : ℂ).im|⁻¹ ^ p) := by
  rw [← xiOrderedSignedZeroCopyEquiv.summable_iff]
  have h := summable_xiOrderedPositiveOrdinate_inv_rpow hp
  have hpos : ∀ n, 0 < xiOrderedPositiveOrdinate n := xiOrderedPositiveOrdinate_pos
  have hl : Summable ((fun q : XiZeroCopy => |(q.1 : ℂ).im|⁻¹ ^ p)
      ∘ xiOrderedSignedZeroCopyEquiv ∘ Sum.inl) := by
    refine h.congr fun n => ?_
    have him : ((xiOrderedSignedZeroCopyEquiv (Sum.inl n)).1 : ℂ).im
        = xiOrderedPositiveOrdinate n := xiOrderedPositiveZeroCopyEquiv_im n
    simp only [Function.comp, him, abs_of_pos (hpos n)]
  have hr : Summable ((fun q : XiZeroCopy => |(q.1 : ℂ).im|⁻¹ ^ p)
      ∘ xiOrderedSignedZeroCopyEquiv ∘ Sum.inr) := by
    refine h.congr fun n => ?_
    have him : ((xiOrderedSignedZeroCopyEquiv (Sum.inr n)).1 : ℂ).im
        = -xiOrderedPositiveOrdinate n :=
      (xiZeroCopyConjEquiv_im _).trans (by rw [xiOrderedPositiveZeroCopyEquiv_im n])
    simp only [Function.comp, him, abs_neg, abs_of_pos (hpos n)]
  exact (hl.hasSum.sum hr.hasSum).summable

/-- The summable weight `1/(|ρ||1−ρ|^θ)`. -/
def zeroWeight (θ : ℝ) (q : XiZeroCopy) : ℝ :=
  ‖(q.1 : ℂ)‖⁻¹ * (‖1 - (q.1 : ℂ)‖ ^ θ)⁻¹

theorem zeroWeight_nonneg (θ : ℝ) (q : XiZeroCopy) : 0 ≤ zeroWeight θ q :=
  mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (inv_nonneg.mpr (Real.rpow_nonneg (norm_nonneg _) _))

theorem summable_zeroWeight {θ : ℝ} (hθ : 0 < θ) : Summable (zeroWeight θ) := by
  refine Summable.of_nonneg_of_le (zeroWeight_nonneg θ) (fun q => ?_)
    (summable_abs_im_inv_rpow (p := 1 + θ) (by linarith))
  have him : 0 < |(q.1 : ℂ).im| := abs_pos.mpr (xiSupport_im_ne_zero q.1)
  have h1 : |(q.1 : ℂ).im| ≤ ‖(q.1 : ℂ)‖ := Complex.abs_im_le_norm _
  have h2 : |(q.1 : ℂ).im| ≤ ‖1 - (q.1 : ℂ)‖ := by
    have := Complex.abs_im_le_norm (1 - (q.1 : ℂ))
    simpa using this
  rw [zeroWeight, Real.rpow_add (inv_pos.mpr him), Real.rpow_one, ← Real.inv_rpow him.le]
  exact mul_le_mul (inv_anti₀ him h1)
    (inv_anti₀ (Real.rpow_pos_of_pos him _) (Real.rpow_le_rpow him.le h2 hθ.le))
    (inv_nonneg.mpr (Real.rpow_nonneg (norm_nonneg _) _)) (inv_nonneg.mpr him.le)

/-! ### Window terms -/

/-- **Mean bound.**  `−ρT(ρ; a, b)` is a `t^{−2}`-weighted mean of `t^ρ`, so `|ρT| ≤ b^{Re ρ}`. -/
theorem norm_mul_lagWindowZeroTerm_le {a b : ℝ} (ha : 0 < a) (hab : a < b) {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖ρ * lagWindowZeroTerm ρ a b‖ ≤ b ^ ρ.re := by
  have hb : 0 < b := lt_trans ha hab
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : 1 - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hρm1 : ρ - 1 ≠ 0 := fun h => hρ1ne (by rw [← neg_sub, h, neg_zero])
  have hw : 0 < 1 / a - 1 / b := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha hab
  have hwC : ((1 / a - 1 / b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]
    intro h
    linarith [h.1]
  have hI := integral_cpow (a := a) (b := b) (r := ρ - 2)
    (Or.inr ⟨fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith, h0⟩)
  rw [show ρ - 2 + 1 = ρ - 1 by ring] at hI
  have hrep : ρ * lagWindowZeroTerm ρ a b
      = -(∫ t in a..b, (t : ℂ) ^ (ρ - 2)) / ((1 / a - 1 / b : ℝ) : ℂ) := by
    rw [hI, lagWindowZeroTerm]
    generalize ((1 / a - 1 / b : ℝ) : ℂ) = W at hwC ⊢
    field_simp
    ring
  have hpt : ∀ t ∈ Set.Ioc a b, ‖(t : ℂ) ^ (ρ - 2)‖ ≤ b ^ ρ.re * t ^ (-2 : ℤ) := by
    intro t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (ρ - 2).re = ρ.re + ((-2 : ℤ) : ℝ) := by
      simp [sub_eq_add_neg]
    rw [hre, Real.rpow_add ht0, Real.rpow_intCast]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht0.le ht.2 hρ0.le)
      (zpow_nonneg ht0.le _)
  have hgint : IntervalIntegrable (fun t : ℝ => b ^ ρ.re * t ^ (-2 : ℤ)) volume a b :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab.le (ae_of_all _ hpt) hgint
  rw [intervalIntegral.integral_const_mul, integral_zpow_neg_two ha hab.le] at hnorm
  rw [hrep, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw,
    div_le_iff₀ hw]
  exact hnorm

/-- `t ≤ A` and `t ≤ AR` give `t ≤ A R^θ` for `0 ≤ θ ≤ 1`. -/
theorem le_mul_rpow_of_le_of_le {t A R θ : ℝ} (ht : 0 ≤ t) (hA : t ≤ A) (hAR : t ≤ A * R)
    (hR : 0 ≤ R) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : t ≤ A * R ^ θ := by
  rcases ht.eq_or_lt with h | hpos
  · rw [← h]
    exact mul_nonneg (ht.trans hA) (Real.rpow_nonneg hR _)
  have hA0 : 0 < A := lt_of_lt_of_le hpos hA
  have h1 : t ^ (1 - θ) ≤ A ^ (1 - θ) := Real.rpow_le_rpow ht hA (by linarith)
  have h2 : t ^ θ ≤ (A * R) ^ θ := Real.rpow_le_rpow ht hAR hθ0
  calc t = t ^ (1 - θ) * t ^ θ := by
        rw [← Real.rpow_add hpos]
        simp
    _ ≤ A ^ (1 - θ) * (A * R) ^ θ := mul_le_mul h1 h2 (Real.rpow_nonneg ht _)
        (Real.rpow_nonneg hA0.le _)
    _ = A * R ^ θ := by
        rw [Real.mul_rpow hA0.le hR, ← mul_assoc, ← Real.rpow_add hA0]
        simp

/-- **Interpolated window bound** for a zero of abscissa at most `β₁`, on a window of width `H`
inside `[x/2, 2x]`. -/
theorem norm_lagWindowZeroTerm_le_interpolated {x H a b β₁ θ : ℝ} (hx : 1 ≤ x) (hH : 0 < H)
    (hxa : x / 2 ≤ a) (hab : b - a = H) (hb : b ≤ 2 * x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hxH : H ≤ x) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hr : ρ.re ≤ β₁) :
    ‖lagWindowZeroTerm ρ a b‖
      ≤ 16 * x ^ β₁ * (x / H) ^ θ * (‖ρ‖⁻¹ * (‖1 - ρ‖ ^ θ)⁻¹) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hablt : a < b := by linarith
  have hb0 : 0 < b := by linarith
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : 1 - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hn1 : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hρ1ne
  have hxr : x ^ ρ.re ≤ x ^ β₁ := Real.rpow_le_rpow_of_exponent_le hx hr
  have hxr0 : 0 < x ^ ρ.re := Real.rpow_pos_of_pos hx0 _
  set K : ℝ := 16 * x ^ β₁ with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  -- the mean bound
  have hA : ‖lagWindowZeroTerm ρ a b‖ ≤ K * ‖ρ‖⁻¹ := by
    have h := norm_mul_lagWindowZeroTerm_le ha0 hablt hρ0 hρ1
    rw [norm_mul] at h
    have hb2 : b ^ ρ.re ≤ (2 * x) ^ ρ.re := Real.rpow_le_rpow hb0.le hb hρ0.le
    have h2 : (2 * x) ^ ρ.re ≤ 2 * x ^ ρ.re := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
      refine mul_le_mul_of_nonneg_right ?_ hxr0.le
      calc (2 : ℝ) ^ ρ.re ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hρ1.le
        _ = 2 := Real.rpow_one 2
    rw [← div_eq_mul_inv, le_div_iff₀ hn, mul_comm]
    have : 2 * x ^ ρ.re ≤ K := by
      rw [hK]
      nlinarith
    linarith
  -- the long-range bound
  have hB : ‖lagWindowZeroTerm ρ a b‖ ≤ K * ‖ρ‖⁻¹ * ((x / H) / ‖1 - ρ‖) := by
    have h := norm_lagWindowZeroTerm_le ha0 hablt ρ
    have hw : 1 / a - 1 / b = H / (a * b) := by
      rw [← hab]
      field_simp
    have hwpos : 0 < H / (a * b) := by positivity
    have hab4 : a * b ≤ 4 * x ^ 2 := by
      have ha2 : a ≤ 2 * x := by linarith
      nlinarith
    have hra : a ^ (ρ.re - 1) ≤ 2 * x ^ (ρ.re - 1) := by
      have h1 : a ^ (ρ.re - 1) ≤ (x / 2) ^ (ρ.re - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hxa (by linarith)
      rw [Real.div_rpow hx0.le (by norm_num)] at h1
      have h2 : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (ρ.re - 1) := by
        have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (ρ.re - 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rwa [Real.rpow_neg_one, ← one_div] at this
      have hxp : 0 < x ^ (ρ.re - 1) := Real.rpow_pos_of_pos hx0 _
      refine h1.trans ?_
      rw [div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
      nlinarith
    have hrb : b ^ (ρ.re - 1) ≤ a ^ (ρ.re - 1) :=
      Real.rpow_le_rpow_of_nonpos ha0 hablt.le (by linarith)
    have hsum : a ^ (ρ.re - 1) + b ^ (ρ.re - 1) ≤ 4 * x ^ (ρ.re - 1) := by linarith
    have hxp : x ^ (ρ.re - 1) * x = x ^ ρ.re := by
      rw [← Real.rpow_add_one hx0.ne']
      ring_nf
    rw [hw] at h
    refine h.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hexp : K * ‖ρ‖⁻¹ * ((x / H) / ‖1 - ρ‖) * (‖ρ‖ * ‖1 - ρ‖ * (H / (a * b)))
        = K * x / (a * b) := by
      field_simp
    rw [hexp, le_div_iff₀ (by positivity)]
    calc (a ^ (ρ.re - 1) + b ^ (ρ.re - 1)) * (a * b)
        ≤ (4 * x ^ (ρ.re - 1)) * (4 * x ^ 2) := by
          apply mul_le_mul hsum hab4 (by positivity)
          positivity
      _ = 16 * (x ^ (ρ.re - 1) * x) * x := by ring
      _ = 16 * x ^ ρ.re * x := by rw [hxp]
      _ ≤ K * x := by
          rw [hK]
          gcongr
  have hR : 0 ≤ (x / H) / ‖1 - ρ‖ := by positivity
  have hint := le_mul_rpow_of_le_of_le (norm_nonneg _) hA hB hR hθ0 hθ1
  rw [Real.div_rpow (by positivity) hn1.le] at hint
  refine hint.trans (le_of_eq ?_)
  rw [div_eq_mul_inv ((x / H) ^ θ)]
  ring

/-- A top zero contributes `−x^ρ/ρ` up to `2H`. -/
theorem norm_lagWindowZeroTerm_add_cpow_div_le {x H a b : ℝ} (ha : 1 ≤ a) (hax : a ≤ x)
    (hxa : x - a ≤ H) (hab : b - a = H) (hH : 0 < H) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖lagWindowZeroTerm ρ a b + (x : ℂ) ^ ρ / ρ‖ ≤ 2 * H := by
  have ha0 : 0 < a := by linarith
  have hablt : a < b := by linarith
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hp : a ^ (ρ.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  have hp0 : 0 ≤ a ^ (ρ.re - 1) := Real.rpow_nonneg ha0.le _
  have h1 := norm_mul_lagWindowZeroTerm_add_cpow_le ha0 le_rfl hablt hρ0 hρ1
  have h2 := norm_ofReal_cpow_sub_cpow_le ha0 hax hρ0 hρ1.le
  have hrep : ρ * (lagWindowZeroTerm ρ a b + (x : ℂ) ^ ρ / ρ)
      = (ρ * lagWindowZeroTerm ρ a b + (a : ℂ) ^ ρ) + ((x : ℂ) ^ ρ - (a : ℂ) ^ ρ) := by
    field_simp
    ring
  have hmain : ‖ρ‖ * ‖lagWindowZeroTerm ρ a b + (x : ℂ) ^ ρ / ρ‖ ≤ ‖ρ‖ * (2 * H) := by
    rw [← norm_mul, hrep]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖ρ‖ * (b - a) * a ^ (ρ.re - 1) ≤ ‖ρ‖ * H := by
      rw [hab]
      exact mul_le_of_le_one_right (by positivity) hp
    have e2 : ‖ρ‖ * (x - a) * a ^ (ρ.re - 1) ≤ ‖ρ‖ * H := by
      calc ‖ρ‖ * (x - a) * a ^ (ρ.re - 1) ≤ ‖ρ‖ * H * a ^ (ρ.re - 1) := by gcongr
        _ ≤ ‖ρ‖ * H := mul_le_of_le_one_right (by positivity) hp
    nlinarith
  exact le_of_mul_le_mul_left hmain hn

/-! ### The zero sum of a window -/

/-- The zero sum of a window of width `H` near `x` is the top sum, up to `2H` per top zero and the
interpolated contribution of all others. -/
theorem norm_tsum_window_add_topSum_le {top : Finset XiZeroCopy} {β₁ θ x H a b : ℝ}
    (hnon : ∀ q : XiZeroCopy, q ∉ top → (q.1 : ℂ).re ≤ β₁) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hx : 1 ≤ x) (hH : 0 < H) (hHx : H ≤ x) (hxa : x / 2 ≤ a) (ha : 1 ≤ a) (hax : a ≤ x)
    (hxa' : x - a ≤ H) (hab : b - a = H) (hb : b ≤ 2 * x) :
    ‖(∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b)
        + ∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖
      ≤ top.card * (2 * H) + 16 * x ^ β₁ * (x / H) ^ θ * ∑' q, zeroWeight θ q := by
  classical
  have hx0 : 0 < x := by linarith
  have hablt : a < b := by linarith
  have hsT := Summable.of_norm (summable_norm_lagWindowZeroTerm ha hablt)
  set K : ℝ := 16 * x ^ β₁ * (x / H) ^ θ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set g : XiZeroCopy → ℂ := fun q => if q ∈ top then (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) else 0 with hg
  have hgs : Summable g := summable_of_ne_finset_zero (s := top) fun q hq => by simp [hg, hq]
  have hgt : ∑' q, g q = ∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) := by
    rw [tsum_eq_sum (s := top) fun q hq => by simp [hg, hq]]
    exact Finset.sum_congr rfl fun q hq => by simp [hg, hq]
  set e : XiZeroCopy → ℝ := fun q => (if q ∈ top then 2 * H else 0) + K * zeroWeight θ q with he
  have hes1 : Summable (fun q : XiZeroCopy => if q ∈ top then 2 * H else (0 : ℝ)) :=
    summable_of_ne_finset_zero (s := top) fun q hq => by simp [hq]
  have hes : Summable e := hes1.add ((summable_zeroWeight hθ0).mul_left K)
  have het : ∑' q, e q = top.card * (2 * H) + K * ∑' q, zeroWeight θ q := by
    rw [hes1.tsum_add ((summable_zeroWeight hθ0).mul_left K), tsum_mul_left,
      tsum_eq_sum (s := top) fun q hq => by simp [hq]]
    congr 1
    rw [Finset.sum_congr rfl fun q hq => if_pos hq, Finset.sum_const, nsmul_eq_mul]
  have hbd : ∀ q, ‖lagWindowZeroTerm (q.1 : ℂ) a b + g q‖ ≤ e q := by
    intro q
    have hq0 := xiZeroCopy_re_pos q
    have hq1 := xiZeroCopy_re_lt_one q
    by_cases hq : q ∈ top
    · simp only [hg, he, hq, if_true]
      have h := norm_lagWindowZeroTerm_add_cpow_div_le ha hax hxa' hab hH hq0 hq1
      have hw : 0 ≤ K * zeroWeight θ q := mul_nonneg hK0 (zeroWeight_nonneg θ q)
      linarith
    · simp only [hg, he, hq, if_false, add_zero, zero_add]
      exact norm_lagWindowZeroTerm_le_interpolated hx hH hxa hab hb hθ0.le hθ1 hHx hq0 hq1
        (hnon q hq)
  have hsum : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b)
      + ∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)
      = ∑' q, (lagWindowZeroTerm (q.1 : ℂ) a b + g q) := by
    rw [hsT.tsum_add hgs, hgt]
  have hsn : Summable (fun q => ‖lagWindowZeroTerm (q.1 : ℂ) a b + g q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hes
  rw [hsum, ← het]
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hbd hes)

/-- The trivial-zero term of a window is at most `4/(x h)`. -/
theorem trivialWindowTerm_le {x h : ℝ} (hx : 2 ≤ x) (hh : 0 < h) :
    (trivialZeroSeriesReal x / x - trivialZeroSeriesReal (x + h) / (x + h))
        / (1 / x - 1 / (x + h)) ≤ 4 / (x * h) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hb0 : 0 < x + h := by linarith
  have hw : 0 < 1 / x - 1 / (x + h) := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hx0 (by linarith)
  have hEb := trivialZeroSeriesReal_nonneg (show 1 ≤ x + h by linarith)
  have hEx := trivialZeroSeriesReal_le_two_div_sq hx
  have hnum : trivialZeroSeriesReal x / x - trivialZeroSeriesReal (x + h) / (x + h)
      ≤ 2 / x ^ 2 / x := by
    have h1 : 0 ≤ trivialZeroSeriesReal (x + h) / (x + h) := div_nonneg hEb hb0.le
    have h2 : trivialZeroSeriesReal x / x ≤ 2 / x ^ 2 / x :=
      div_le_div_of_nonneg_right hEx hx0.le
    linarith
  have hweq : 1 / x - 1 / (x + h) = h / (x * (x + h)) := by
    field_simp
    ring
  rw [div_le_iff₀ hw, hweq]
  refine hnum.trans ?_
  rw [show 4 / (x * h) * (h / (x * (x + h))) = 4 / (x ^ 2 * (x + h)) by field_simp, div_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The two-sided squeeze.**  `ψ(x) − x + Re Σ_top x^ρ/ρ` is at most the window width, the top
errors and the interpolated sum of all other zeros, up to a constant. -/
theorem abs_psi_sub_add_re_topSum_le {top : Finset XiZeroCopy} {β₁ θ x H : ℝ}
    (hnon : ∀ q : XiZeroCopy, q ∉ top → (q.1 : ℂ).re ≤ β₁) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hx : 4 ≤ x) (hH1 : 1 ≤ H) (hHx : H ≤ x / 2) :
    |Chebyshev.psi x - x + (∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re|
      ≤ H + 1 + Real.log (2 * Real.pi) + top.card * (2 * H)
        + 16 * x ^ β₁ * (x / H) ^ θ * ∑' q, zeroWeight θ q := by
  have hH : 0 < H := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  set Err : ℝ := top.card * (2 * H) + 16 * x ^ β₁ * (x / H) ^ θ * ∑' q, zeroWeight θ q with hErr
  set Tp : ℂ := ∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) with hTp
  -- the right window `[x, x + H]`
  have hU := norm_tsum_window_add_topSum_le (a := x) (b := x + H) hnon hθ0 hθ1 (by linarith) hH
    (by linarith) (by linarith) (by linarith) le_rfl (by linarith) (by ring) (by linarith)
  have hwU : 0 < 1 / x - 1 / (x + H) := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hx0 (by linarith)
  have hψU : Chebyshev.psi x ≤ chebyshevLagWindow x (x + H) / (1 / x - 1 / (x + H)) := by
    rw [le_div_iff₀ hwU]
    exact (chebyshevLagWindow_bounds hx0 (by linarith)).1
  rw [chebyshevLagWindow_div_eq (by linarith) (by linarith)] at hψU
  have hLU : Real.log ((x + H) / x) / (1 / x - 1 / (x + H)) ≤ x + H := by
    rw [div_le_iff₀ hwU]
    exact (log_div_le_mul_inv_sub hx0 (by linarith)).2
  have hEU := trivialWindowTerm_le (show 2 ≤ x by linarith) hH
  have hE1 : 4 / (x * H) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hReU : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x (x + H)).re + Tp.re ≤ Err := by
    rw [← Complex.add_re]
    exact (Complex.re_le_norm _).trans hU
  -- the left window `[x − H, x]`
  have hL := norm_tsum_window_add_topSum_le (a := x - H) (b := x) hnon hθ0 hθ1 (by linarith) hH
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by ring) (by linarith)
  have ha0 : 0 < x - H := by linarith
  have hwL : 0 < 1 / (x - H) - 1 / x := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha0 (by linarith)
  have hψL : chebyshevLagWindow (x - H) x / (1 / (x - H) - 1 / x) ≤ Chebyshev.psi x := by
    rw [div_le_iff₀ hwL]
    exact (chebyshevLagWindow_bounds ha0 (by linarith)).2
  rw [chebyshevLagWindow_div_eq (by linarith) (by linarith)] at hψL
  have hLL : x - H ≤ Real.log (x / (x - H)) / (1 / (x - H) - 1 / x) := by
    rw [le_div_iff₀ hwL]
    exact (log_div_le_mul_inv_sub ha0 (by linarith)).1
  have hEL : 0 ≤ (trivialZeroSeriesReal (x - H) / (x - H) - trivialZeroSeriesReal x / x)
      / (1 / (x - H) - 1 / x) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti (by linarith) (by linarith))) hwL.le
  have hReL : -Err ≤ (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) (x - H) x).re + Tp.re := by
    rw [← Complex.add_re]
    have h := Complex.abs_re_le_norm
      ((∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) (x - H) x) + Tp)
    have h' := neg_le_of_abs_le (h.trans hL)
    exact h'
  have hcard : 0 ≤ Err := by
    rw [hErr]
    have := summable_zeroWeight hθ0
    have hW : 0 ≤ ∑' q, zeroWeight θ q := tsum_nonneg (zeroWeight_nonneg θ)
    positivity
  rw [abs_le]
  constructor <;> linarith

/-! ### The expansion from a one-off -/

theorem cpow_add_I_mul_eq {x : ℝ} (hx : 0 < x) (β ω : ℝ) :
    (x : ℂ) ^ ((β : ℂ) + I * ω) = ((x ^ β : ℝ) : ℂ) * cexp (I * ω * Real.log x) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_add _ _ hxC, Complex.ofReal_cpow hx.le,
    Complex.cpow_def_of_ne_zero hxC ((I : ℂ) * ω), ← Complex.ofReal_log hx.le]
  congr 2
  ring

/-- **The top sum as a trigonometric polynomial.** -/
theorem rpow_mul_finiteOscillation_top {top : Finset XiZeroCopy} {β x : ℝ} (hx : 0 < x)
    (htop : ∀ q ∈ top, (q.1 : ℂ).re = β) :
    x ^ β * finiteOscillation (top.image fun q => (q.1 : ℂ).im)
        (fun ω => -((top.filter fun q => (q.1 : ℂ).im = ω).card : ℂ) / ((β : ℂ) + I * ω))
        (Real.log x)
      = -(∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re := by
  classical
  have hval : ∀ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)
      = ((x ^ β : ℝ) : ℂ) * (cexp (I * ((q.1 : ℂ).im : ℝ) * Real.log x)
          / ((β : ℂ) + I * ((q.1 : ℂ).im : ℝ))) := by
    intro q hq
    have hq' : (q.1 : ℂ) = (β : ℂ) + I * ((q.1 : ℂ).im : ℝ) := by
      apply Complex.ext <;> simp [htop q hq]
    rw [hq', cpow_add_I_mul_eq hx]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add]
    rw [mul_div_assoc]
  set F : ℝ → ℂ := fun ω => ((x ^ β : ℝ) : ℂ) * (cexp (I * ω * Real.log x) / ((β : ℂ) + I * ω)) with hF
  have hsum : ∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)
      = ∑ ω ∈ top.image (fun q => (q.1 : ℂ).im),
          ((top.filter fun q => (q.1 : ℂ).im = ω).card : ℂ) * F ω := by
    rw [Finset.sum_congr rfl hval]
    have h := Finset.sum_comp (s := top) (g := fun q : XiZeroCopy => (q.1 : ℂ).im) F
    rw [h]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [nsmul_eq_mul]
  rw [finiteOscillation, hsum, ← Complex.re_ofReal_mul, Finset.mul_sum, ← Complex.neg_re,
    Finset.sum_neg_distrib.symm ▸ rfl]
  sorry

end

end GaloisForLFunctions.ZeroConfigurationGeometry
