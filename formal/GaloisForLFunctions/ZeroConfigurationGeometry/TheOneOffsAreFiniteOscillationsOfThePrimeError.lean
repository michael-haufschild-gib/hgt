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

/-- The reciprocal ordinates of the zeros are in every `ℓ^p`, `p > 1`: the positive half is
`summable_xiOrderedPositiveOrdinate_inv_rpow`, and conjugation carries the rest into it. -/
theorem summable_abs_im_inv_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun q : XiZeroCopy => |(q.1 : ℂ).im|⁻¹ ^ p) := by
  have h := summable_xiOrderedPositiveOrdinate_inv_rpow hp
  have hP : Summable (fun q : XiPositiveZeroCopy => |(q.1.1 : ℂ).im|⁻¹ ^ p) := by
    rw [← xiOrderedPositiveZeroCopyEquiv.summable_iff]
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, xiOrderedPositiveZeroCopyEquiv_im n,
      abs_of_pos (xiOrderedPositiveOrdinate_pos n)]
  let s : Set XiZeroCopy := {q | 0 < (q.1 : ℂ).im}
  have hneg : ∀ q : ↑sᶜ, 0 < ((xiZeroCopyConjEquiv q.1).1 : ℂ).im := by
    intro q
    rw [xiZeroCopyConjEquiv_im]
    have hq : ¬ 0 < (q.1.1 : ℂ).im := q.2
    have hlt : (q.1.1 : ℂ).im < 0 :=
      lt_of_le_of_ne (not_lt.mp hq) (xiSupport_im_ne_zero q.1.1)
    linarith
  let ι : ↑sᶜ → XiPositiveZeroCopy := fun q => ⟨xiZeroCopyConjEquiv q.1, hneg q⟩
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (xiZeroCopyConjEquiv.injective (congrArg Subtype.val hab))
  have hN : Summable (fun q : ↑sᶜ => |(q.1.1 : ℂ).im|⁻¹ ^ p) := by
    refine (hP.comp_injective hι).congr fun q => ?_
    simp only [Function.comp_apply, ι, xiZeroCopyConjEquiv_im, abs_neg]
  exact summable_subtype_and_compl.mp ⟨hP, hN⟩

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
  rw [zeroWeight, Real.rpow_add (inv_pos.mpr him), Real.rpow_one, Real.inv_rpow him.le]
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
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hr : ρ.re ≤ β₁) :
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
    (hx : 1 ≤ x) (hH : 0 < H) (hxa : x / 2 ≤ a) (ha : 1 ≤ a) (hax : a ≤ x)
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
      exact norm_lagWindowZeroTerm_le_interpolated hx hH hxa hab hb hθ0.le hθ1 hq0 hq1
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
theorem trivialWindowTerm_le {x h : ℝ} (hx : 2 ≤ x) (hh : 0 < h) (hhx : h ≤ x) :
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
  nlinarith [mul_le_mul_of_nonneg_left hhx (sq_nonneg x)]

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
  have hU := norm_tsum_window_add_topSum_le (x := x) (H := H) (a := x) (b := x + H) hnon hθ0 hθ1
    (by linarith) hH (by linarith) (by linarith) le_rfl (by linarith) (by ring) (by linarith)
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
  have hEU := trivialWindowTerm_le (show 2 ≤ x by linarith) hH (by linarith)
  have hE1 : 4 / (x * H) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hReU : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x (x + H)).re + Tp.re ≤ Err := by
    rw [← Complex.add_re]
    exact (Complex.re_le_norm _).trans hU
  -- the left window `[x − H, x]`
  have hL := norm_tsum_window_add_topSum_le (x := x) (H := H) (a := x - H) (b := x) hnon hθ0 hθ1
    (by linarith) hH (by linarith) (by linarith) (by linarith) (by linarith) (by ring) (by linarith)
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
  rw [finiteOscillation, hsum, ← Complex.re_ofReal_mul, Finset.mul_sum,
    ← Complex.neg_re, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  dsimp [F]
  ring

/-- **The expansion from an isolated top layer.** -/
theorem exists_expansion_of_top {top : Finset XiZeroCopy} {β β₁ : ℝ} (hβ₁ : 1 / 2 ≤ β₁)
    (hβ₁β : β₁ < β) (hβ1 : β < 1) (hnon : ∀ q : XiZeroCopy, q ∉ top → (q.1 : ℂ).re ≤ β₁) :
    ∃ C x₀ : ℝ, ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x + (∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re|
        ≤ C * x ^ ((β + β₁) / 2) := by
  set E : ℝ := (β + β₁) / 2 with hE
  set θ : ℝ := (β - β₁) / 4 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hE0 : 0 < E := by rw [hE]; linarith
  have hE1 : E < 1 := by rw [hE]; linarith
  have hgap : 0 < 1 - E := by linarith
  set W : ℝ := ∑' q, zeroWeight θ q with hW
  have hW0 : 0 ≤ W := tsum_nonneg (zeroWeight_nonneg θ)
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨2 + Real.log (2 * Real.pi) + 2 * top.card + 16 * W,
    max 4 ((2 : ℝ) ^ (1 / (1 - E))), fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx2 : (2 : ℝ) ^ (1 / (1 - E)) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set H : ℝ := x ^ E with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hx1 hE0.le
  have hH0 : 0 < H := by linarith
  have h2 : 2 ≤ x ^ (1 - E) := by
    have h := Real.rpow_le_rpow (by positivity) hx2 hgap.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hgap.ne', Real.rpow_one] at h
  have hsplit : H * x ^ (1 - E) = x := by
    rw [hH, ← Real.rpow_add hx0]
    simp
  have hHx : H ≤ x / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hmain := abs_psi_sub_add_re_topSum_le (x := x) (H := H) hnon hθ0 hθ1 hx4 hH1 hHx
  refine hmain.trans ?_
  have hratio : (x / H) ^ θ ≤ x ^ θ := by
    refine Real.rpow_le_rpow (by positivity) ?_ hθ0.le
    exact div_le_self hx0.le hH1
  have hβθ : x ^ β₁ * x ^ θ ≤ H := by
    rw [← Real.rpow_add hx0, hH]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    rw [hE, hθ]
    linarith
  have hxβ : 0 ≤ x ^ β₁ := Real.rpow_nonneg hx0.le _
  have hlast : 16 * x ^ β₁ * (x / H) ^ θ * W ≤ 16 * W * H := by
    calc 16 * x ^ β₁ * (x / H) ^ θ * W ≤ 16 * x ^ β₁ * x ^ θ * W := by gcongr
      _ = 16 * W * (x ^ β₁ * x ^ θ) := by ring
      _ ≤ 16 * W * H := by gcongr
  have hc : (top.card : ℝ) * (2 * H) = 2 * top.card * H := by ring
  rw [hc]
  nlinarith [mul_nonneg hlog (sub_nonneg.mpr hH1)]

/-- **A one-off gives a finite oscillation.** -/
theorem primeErrorIsFiniteOscillation_of_not_asymptoticAbscissaLaw
    (h : ¬ AsymptoticAbscissaLaw) : PrimeErrorIsFiniteOscillation := by
  classical
  unfold AsymptoticAbscissaLaw at h
  push Not at h
  obtain ⟨h₀, hh0, hfin, q₀, hq₀⟩ := h
  set F : Finset XiZeroCopy := hfin.toFinset with hFdef
  have hmemF : ∀ q : XiZeroCopy, q ∈ F ↔ 1 / 2 + h₀ < (q.1 : ℂ).re := fun q => by
    simp [hFdef]
  have hF : F.Nonempty := ⟨q₀, (hmemF q₀).2 hq₀⟩
  obtain ⟨qt, hqtF, hqt⟩ := F.exists_max_image (fun q : XiZeroCopy => (q.1 : ℂ).re) hF
  set β : ℝ := (qt.1 : ℂ).re with hβ
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one qt
  set top : Finset XiZeroCopy := F.filter (fun q => (q.1 : ℂ).re = β) with htopdef
  set A : Finset ℝ := insert (1 / 2 + h₀)
    ((F.filter (fun q : XiZeroCopy => (q.1 : ℂ).re < β)).image (fun q => (q.1 : ℂ).re)) with hA
  have hAne : A.Nonempty := Finset.insert_nonempty _ _
  set β₁ : ℝ := A.max' hAne with hβ₁
  have hβ₁lt : β₁ < β := by
    have hmem : β₁ ∈ A := A.max'_mem hAne
    rcases Finset.mem_insert.mp hmem with hm | hm
    · rw [hm]
      exact lt_of_lt_of_le hq₀ (hqt q₀ ((hmemF q₀).2 hq₀))
    · obtain ⟨q, hq, hv⟩ := Finset.mem_image.mp hm
      rw [← hv]
      exact (Finset.mem_filter.mp hq).2
  have hβ₁half : 1 / 2 ≤ β₁ := by
    have hle : 1 / 2 + h₀ ≤ β₁ := A.le_max' _ (Finset.mem_insert_self _ _)
    linarith
  have htop : ∀ q ∈ top, (q.1 : ℂ).re = β := fun q hq => (Finset.mem_filter.mp hq).2
  have hnon : ∀ q : XiZeroCopy, q ∉ top → (q.1 : ℂ).re ≤ β₁ := by
    intro q hq
    by_cases hqF : 1 / 2 + h₀ < (q.1 : ℂ).re
    · have hF' := (hmemF q).2 hqF
      have hle := hqt q hF'
      have hne : (q.1 : ℂ).re ≠ β := fun he => hq (Finset.mem_filter.mpr ⟨hF', he⟩)
      exact A.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨hF', lt_of_le_of_ne hle hne⟩, rfl⟩))
    · exact (not_lt.mp hqF).trans (A.le_max' _ (Finset.mem_insert_self _ _))
  obtain ⟨C, x₀, hC⟩ := exists_expansion_of_top hβ₁half hβ₁lt hβ1 hnon
  set S : Finset ℝ := top.image fun q => (q.1 : ℂ).im with hS
  set c : ℝ → ℂ := fun ω =>
    -((top.filter fun q => (q.1 : ℂ).im = ω).card : ℂ) / ((β : ℂ) + I * ω) with hc
  have hexp : ∀ x, max x₀ 1 ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)|
        ≤ C * x ^ ((β + β₁) / 2) := by
    intro x hx
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    have hx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
    have hT := rpow_mul_finiteOscillation_top (top := top) (β := β) (x := x) (by linarith) htop
    rw [hT, sub_neg_eq_add]
    exact hC x hx₀
  refine ⟨β, (β - β₁) / 2, by linarith, by linarith, S, c, ?_, C, max x₀ 1, ?_⟩
  · by_contra hall
    push Not at hall
    have hb : ∀ x, max x₀ 1 ≤ x →
        ‖oscillationError β ∅ 0 x‖ ≤ C * x ^ ((β + β₁) / 2) := by
      intro x hx
      have h := hexp x hx
      rw [hall, mul_zero, sub_zero] at h
      have hrep : oscillationError β ∅ 0 x = ((Chebyshev.psi x - x : ℝ) : ℂ) := by
        simp [oscillationError]
      rwa [hrep, Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨ω, hω, -⟩ := eq_of_zeta_eq_zero_of_expansion hb (ρ := (qt.1 : ℂ))
      (by change (β + β₁) / 2 < β; linarith) (xiZeroCopy_ne_one qt)
      (riemannZeta_eq_zero_of_xiZeroCopy qt)
    simp at hω
  · intro x hx
    have h := hexp x hx
    rwa [show β - (β - β₁) / 2 = (β + β₁) / 2 by ring]

/-! ### The converse -/

/-- The coefficient of `e^{iμu}` in the real trigonometric polynomial. -/
def oscillationCoeff (S : Finset ℝ) (c : ℝ → ℂ) (μ : ℝ) : ℂ :=
  (if μ ∈ S then c μ else 0) / 2 + (if -μ ∈ S then (starRingEnd ℂ) (c (-μ)) else 0) / 2

/-- The frequency set of the real trigonometric polynomial. -/
def oscillationFrequencies (S : Finset ℝ) : Finset ℝ :=
  S ∪ S.image fun ω => -ω

/-- **Exponential form of a real trigonometric polynomial.** -/
theorem finiteOscillation_eq_sum (S : Finset ℝ) (c : ℝ → ℂ) (u : ℝ) :
    (finiteOscillation S c u : ℂ)
      = ∑ μ ∈ oscillationFrequencies S, oscillationCoeff S c μ * cexp (I * μ * u) := by
  classical
  set e : ℝ → ℂ := fun μ => cexp (I * μ * u) with he
  have hA : ∑ μ ∈ oscillationFrequencies S, (if μ ∈ S then c μ else 0) * e μ
      = ∑ ω ∈ S, c ω * e ω := by
    have h1 := Finset.sum_subset (s₁ := S) (s₂ := oscillationFrequencies S)
      (f := fun μ : ℝ => (if μ ∈ S then c μ else 0) * e μ) Finset.subset_union_left
      (fun μ _ hμ => by simp [hμ])
    exact h1.symm.trans (Finset.sum_congr rfl fun ω hω => by simp [hω])
  have hB : ∑ μ ∈ oscillationFrequencies S,
        (if -μ ∈ S then (starRingEnd ℂ) (c (-μ)) else 0) * e μ
      = ∑ ω ∈ S, (starRingEnd ℂ) (c ω) * e (-ω) := by
    have h1 := Finset.sum_subset (s₁ := S.image fun ω => -ω) (s₂ := oscillationFrequencies S)
      (f := fun μ : ℝ => (if -μ ∈ S then (starRingEnd ℂ) (c (-μ)) else 0) * e μ)
      Finset.subset_union_right (fun μ _ hμ => by
        have hnot : -μ ∉ S := fun h => hμ (Finset.mem_image.mpr ⟨-μ, h, neg_neg μ⟩)
        simp [hnot])
    refine h1.symm.trans ?_
    rw [Finset.sum_image fun a _ b _ hab => neg_injective hab]
    exact Finset.sum_congr rfl fun ω hω => by simp [hω]
  have hconj : (starRingEnd ℂ) (∑ ω ∈ S, c ω * cexp (I * ω * u))
      = ∑ ω ∈ S, (starRingEnd ℂ) (c ω) * e (-ω) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have hsum : ∑ μ ∈ oscillationFrequencies S, oscillationCoeff S c μ * e μ
      = (∑ μ ∈ oscillationFrequencies S, (if μ ∈ S then c μ else 0) * e μ) / 2
        + (∑ μ ∈ oscillationFrequencies S,
            (if -μ ∈ S then (starRingEnd ℂ) (c (-μ)) else 0) * e μ) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [oscillationCoeff]
    ring
  rw [hsum, hA, hB, ← hconj, finiteOscillation, Complex.re_eq_add_conj]
  ring

/-- A nonzero real trigonometric polynomial has a nonzero exponential coefficient. -/
theorem exists_oscillationCoeff_ne_zero {S : Finset ℝ} {c : ℝ → ℂ} {u : ℝ}
    (hu : finiteOscillation S c u ≠ 0) :
    ∃ μ ∈ oscillationFrequencies S, oscillationCoeff S c μ ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hu
  have h := finiteOscillation_eq_sum S c u
  rw [Finset.sum_eq_zero fun μ hμ => by rw [hall μ hμ, zero_mul]] at h
  exact_mod_cast h

/-- Only finitely many zeros have bounded ordinate. -/
theorem finite_abs_im_le (M : ℝ) : {q : XiZeroCopy | |(q.1 : ℂ).im| ≤ M}.Finite := by
  have hs := summable_abs_im_inv_rpow (p := 2) one_lt_two
  have hM : 0 < |M| + 1 := by positivity
  have hε : 0 < (|M| + 1)⁻¹ ^ (2 : ℝ) := Real.rpow_pos_of_pos (inv_pos.mpr hM) _
  have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun q hq => ?_
  have hq0 : 0 < |(q.1 : ℂ).im| := abs_pos.mpr (xiSupport_im_ne_zero q.1)
  have hqM : |(q.1 : ℂ).im| ≤ |M| + 1 := by
    have h1 : |(q.1 : ℂ).im| ≤ M := hq
    have h2 := le_abs_self M
    linarith
  simp only [Set.mem_setOf_eq, not_lt]
  exact Real.rpow_le_rpow (inv_nonneg.mpr hM.le) (inv_anti₀ hq0 hqM) (by norm_num)

/-- **A finite oscillation gives a one-off.** -/
theorem not_asymptoticAbscissaLaw_of_primeErrorIsFiniteOscillation
    (h : PrimeErrorIsFiniteOscillation) : ¬ AsymptoticAbscissaLaw := by
  obtain ⟨β, η, hβ, hη, S, c, ⟨u₀, hu₀⟩, C, x₀, hC⟩ := h
  intro hAAL
  set S' := oscillationFrequencies S with hS'
  set d := oscillationCoeff S c with hd
  set σ₀ : ℝ := max (β - η) ((β + 1 / 2) / 2) with hσ₀
  have hσβ : σ₀ < β := max_lt (by linarith) (by linarith)
  have hσhalf : 1 / 2 < σ₀ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hb : ∀ x, max x₀ 1 ≤ x → ‖oscillationError β S' d x‖ ≤ |C| * x ^ σ₀ := by
    intro x hx
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    have hx0 : 0 < x := by linarith
    have hrep : oscillationError β S' d x
        = ((Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x) : ℝ) : ℂ) := by
      have hsum : ∑ ω ∈ S', d ω * (x : ℂ) ^ ((β : ℂ) + I * ω)
          = ((x ^ β * finiteOscillation S c (Real.log x) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, finiteOscillation_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [cpow_add_I_mul_eq hx0]
        ring
      rw [oscillationError, hsum]
      push_cast
      ring
    rw [hrep, Complex.norm_real, Real.norm_eq_abs]
    refine (hC x ((le_max_left _ _).trans hx)).trans ?_
    calc C * x ^ (β - η) ≤ |C| * x ^ (β - η) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)
      _ ≤ |C| * x ^ σ₀ := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
          exact Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  obtain ⟨μ₀, hμ₀, hne⟩ := exists_oscillationCoeff_ne_zero hu₀
  have hζ := zeta_eq_zero_of_coeff_ne_zero hb hμ₀ hne hσβ (by linarith)
  set ρ₀ : ℂ := (β : ℂ) + I * μ₀ with hρ₀
  have hre : ρ₀.re = β := by simp [hρ₀]
  have hβ1 : β < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith) hζ
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ (by rw [hre]; linarith)
    (by rw [hre]; exact hβ1)
  set M : ℝ := ∑ μ ∈ S', |μ| with hM
  have hfin : {q : XiZeroCopy | 1 / 2 + (σ₀ - 1 / 2) < (q.1 : ℂ).re}.Finite := by
    refine (finite_abs_im_le M).subset fun q hq => ?_
    have hq' : σ₀ < (q.1 : ℂ).re := by
      have : 1 / 2 + (σ₀ - 1 / 2) < (q.1 : ℂ).re := hq
      linarith
    obtain ⟨ω, hω, heq⟩ := eq_of_zeta_eq_zero_of_expansion hb hq' (xiZeroCopy_ne_one q)
      (riemannZeta_eq_zero_of_xiZeroCopy q)
    have him : (q.1 : ℂ).im = ω := by
      rw [heq]
      simp
    have hle : |ω| ≤ M := Finset.single_le_sum (f := fun μ : ℝ => |μ|)
      (fun _ _ => abs_nonneg _) hω
    change |(q.1 : ℂ).im| ≤ M
    rwa [him]
  have hall := hAAL (σ₀ - 1 / 2) (by linarith) hfin q₀
  rw [hq₀, hre] at hall
  linarith

/-- **The exact prime-side form of a one-off zero.**  The asymptotic abscissa law fails exactly when
the prime number theorem error is a single finite oscillation at leading order. -/
theorem not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation :
    ¬ AsymptoticAbscissaLaw ↔ PrimeErrorIsFiniteOscillation :=
  ⟨primeErrorIsFiniteOscillation_of_not_asymptoticAbscissaLaw,
    not_asymptoticAbscissaLaw_of_primeErrorIsFiniteOscillation⟩

end

end GaloisForLFunctions.ZeroConfigurationGeometry
