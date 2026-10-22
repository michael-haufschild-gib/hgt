import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionBorel
import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionDensityTail
import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionMeasure
import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionEndpointComparison
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field

/-!
# Order-of-limits boundary for the paired-eta partition clock versus its contiguous comparison

The finite paired-eta source is the union of the logarithmic intervals
`(log(2n+1), log(2n+2)]`, `n < N`, and its contiguous comparison is `(0, log 2N]`; both are
tilted by `e^{-u/2}` with normalizers `A_N` and `U_{log 2N}`, and the infinite and half-line
versions have normalizers `A_∞` and `U_∞ = 2`. From two independent half-tilted copies one forms
difference densities, their ratio `ρ_N(x)`, even difference moments, and Borel kernels
`G(t) = ∑ⱼ m_{2j} t^{2j} / ((2j)!)²`. This module compares the regimes `N → ∞` and `x, t, j → ∞`.
The endpoint scale `κ_N = (U_{log 2N}/A_N)²` tends to `4/A_∞²` with error `O((2N)^{-1/2})`,
whereas in the spatial bulk `ρ_N(x)` tends to `c_∞ = 2 log 2 / A_∞²`. Since
`c_∞ < 1 < 4/A_∞²`, the two iterated limits differ. For the Borel kernels, in the window
`t ≤ c log 2N` with `0 < c < 1/16`, `e^{-2t} G_N(t) → c_∞/2` while the contiguous kernel gives
`1/2`, so `G_N - G^{cont} → -∞` there, whereas for each fixed `N ≥ 2` the same difference tends
to `+∞` as `t → ∞`.

## Main results

- `liClockPairedEtaPartitionComparisonScale_tendsto` and
  `liClockPairedEtaPartitionComparisonScale_error_le`: `κ_N → 4/A_∞²`, with an explicit
  `O(e^{-log(2N)/2})` error.
- `liClockPairedEtaInfinitePartitionSpatialBulk_uniform`: for every `ε > 0` there is `K > 0` with
  `|ρ_N(x) - c_∞| < ε` for all `N ≥ 1` and `K ≤ x ≤ log 2N - K`.
- `liClockPairedEtaInfinitePartitionSpatialBulk_joint_limits`: if `N, x → ∞` and
  `log 2N - x → ∞`, then `e^{x/2}` times the raw difference density tends to `log 2 / 2` and
  `ρ_N(x) → c_∞`.
- `liClockPairedEtaPartitionRawDifferenceDensity_iterated_limits`: the iterated limits of the
  scaled raw density in `x` and `N` are `0` and `log 2 / 2`, which differ.
- `liClockPairedEtaInfinitePartitionBorel_qualified_joint_limits`: in the window above,
  `e^{-2t} G_N(t) → c_∞/2`, `e^{-2t} G^{cont}(t) → 1/2`, `G_N/G^{cont} → c_∞` and
  `G_N - G^{cont} → -∞`.
- `liClockPairedEtaInfinitePartitionBorel_uniform_negative_gap`: eventually in `N`,
  `G_N(t) - G^{cont}(t) ≤ -1/2` for `T ≤ t ≤ c log 2N`.
- `liClockPairedEtaInfinitePartition_comparison_limits_distinct`: `c_∞ < 1 < 4/A_∞²`.
- `liClockPairedEtaInfinitePartition_moment_ratio_order_boundary` and
  `liClockPairedEtaInfinitePartition_Borel_ratio_order_boundary`: the moment and Borel ratios have
  iterated limits `4/A_∞²` (first `j` or `t`, then `N`) and `c_∞` (first `N`), which differ.
- `liClockPairedEtaInfinitePartition_Borel_opposite_boundary_escapes`: for fixed `N ≥ 2`,
  `G_N - G^{cont} → +∞` as `t → ∞`, but `→ -∞` along the joint window.

## Hypotheses

Unconditional. Statements take `0 < N` (or `2 ≤ N`), window hypotheses such as `0 < c < 1/16` and
`0 ≤ t ≤ c log 2N`, and divergence hypotheses on the sequences `N`, `x`, `t`; no zero-location,
functional-equation or Riemann-hypothesis premise is used.
-/

open Filter Topology

namespace RHTower

private theorem boundary_scaled_perturbation
    {f g t : ℕ → ℝ} {L : ℝ}
    (ht : Tendsto t atTop atTop)
    (herr : Tendsto (fun n => f n - g n) atTop (𝓝 0))
    (hg : Tendsto (fun n => Real.exp (-2 * t n) * g n) atTop (𝓝 L)) :
    Tendsto (fun n => Real.exp (-2 * t n) * f n) atTop (𝓝 L) := by
  have hexp : Tendsto (fun n => Real.exp (-2 * t n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (by norm_num))
  have h := (hexp.mul herr).add hg
  simp only [zero_mul, zero_add] at h
  exact h.congr (fun n => by ring)

private theorem boundary_scaled_ratio
    {A U t : ℕ → ℝ} {a b : ℝ}
    (ha : Tendsto (fun n => Real.exp (-2 * t n) * A n) atTop (𝓝 a))
    (hb : Tendsto (fun n => Real.exp (-2 * t n) * U n) atTop (𝓝 b))
    (hb0 : b ≠ 0) :
    Tendsto (fun n => A n / U n) atTop (𝓝 (a / b)) := by
  exact (ha.div hb hb0).congr (fun n =>
    mul_div_mul_left (A n) (U n) (Real.exp_ne_zero _))

private theorem boundary_negative_gap
    {A U t : ℕ → ℝ} {a b : ℝ}
    (ht : Tendsto t atTop atTop)
    (ha : Tendsto (fun n => Real.exp (-2 * t n) * A n) atTop (𝓝 a))
    (hb : Tendsto (fun n => Real.exp (-2 * t n) * U n) atTop (𝓝 b))
    (hab : a < b) :
    Tendsto (fun n => A n - U n) atTop atBot := by
  have hd : Tendsto (fun n => Real.exp (-2 * t n) * (A n - U n)) atTop
      (𝓝 (a - b)) := (ha.sub hb).congr (fun n => by ring)
  have he : Tendsto (fun n => Real.exp (2 * t n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (ht.const_mul_atTop (by norm_num))
  exact (he.atTop_mul_neg (sub_neg.mpr hab) hd).congr (fun n => by
    rw [← mul_assoc, ← Real.exp_add]
    have hx : 2 * t n + -2 * t n = 0 := by ring
    rw [hx]
    simp)

/-- Abstract kernel comparison: if `t → ∞`, `A - A_∞ → 0`, `U - U_∞ → 0`,
`e^{-2t} A_∞ → ℓ/2`, `e^{-2t} U_∞ → 1/2` and `ℓ < 1`, then `A/U → ℓ` and `A - U → -∞`. -/
private theorem boundary_qualified_kernel_limits
    {A U Ainf Uinf t : ℕ → ℝ} {ell : ℝ}
    (ht : Tendsto t atTop atTop)
    (hAerr : Tendsto (fun n => A n - Ainf n) atTop (𝓝 0))
    (hUerr : Tendsto (fun n => U n - Uinf n) atTop (𝓝 0))
    (hAinf : Tendsto (fun n => Real.exp (-2 * t n) * Ainf n) atTop (𝓝 (ell / 2)))
    (hUinf : Tendsto (fun n => Real.exp (-2 * t n) * Uinf n) atTop (𝓝 (1 / 2)))
    (hlimit : ell < 1) :
    Tendsto (fun n => Real.exp (-2 * t n) * A n) atTop (𝓝 (ell / 2)) ∧
    Tendsto (fun n => Real.exp (-2 * t n) * U n) atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun n => A n / U n) atTop (𝓝 ell) ∧
    Tendsto (fun n => A n - U n) atTop atBot := by
  have ha := boundary_scaled_perturbation ht hAerr hAinf
  have hu := boundary_scaled_perturbation ht hUerr hUinf
  have hratio := boundary_scaled_ratio ha hu (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hconst : (ell / 2) / (1 / 2) = ell := by ring
  rw [hconst] at hratio
  exact ⟨ha, hu, hratio, boundary_negative_gap ht ha hu (by linarith)⟩

end RHTower

namespace RHTower
noncomputable section

private theorem boundary_firstMass_pos : 0 < 2-Real.sqrt 2 := by
  nlinarith [Real.sqrt_nonneg (2:ℝ),Real.sq_sqrt (by norm_num : 0≤(2:ℝ))]

private theorem boundary_logEndpoint_pos {N:ℕ} (hN:0<N) :
    0<Real.log (2*(N:ℝ)) := by
  apply Real.log_pos
  have hn : (1:ℝ)≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
  linarith

private theorem boundary_inverse_square_error {s a b E:ℝ}
    (hs:0<s) (hsa:s≤a) (hab:a≤b) (hb:b≤2) (hE:0≤E) (hd:b-a≤2*E) :
    0≤1/a^2-1/b^2 ∧ 1/a^2-1/b^2≤8*E/s^4 := by
  have ha:0<a:=hs.trans_le hsa
  have hbp:0<b:=ha.trans_le hab
  have hn:(b-a)*(b+a)≤8*E := by
    calc
      _≤(2*E)*(b+a):=mul_le_mul_of_nonneg_right hd (by positivity)
      _≤(2*E)*4:=mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _=_:=by ring
  have hden:s^4≤a^2*b^2 := by
    rw [show s^4=s^2*s^2 by ring]
    exact mul_le_mul (by nlinarith : s^2≤a^2) (by nlinarith : s^2≤b^2)
      (sq_nonneg _) (sq_nonneg _)
  have he:1/a^2-1/b^2=(b-a)*(b+a)/(a^2*b^2) := by field_simp; ring
  rw [he]
  refine ⟨div_nonneg (mul_nonneg (sub_nonneg.mpr hab) (by positivity)) (by positivity),?_⟩
  exact (div_le_div_of_nonneg_right hn (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)

private theorem boundary_normalizationScale_error {s a b u E:ℝ}
    (hs:0<s) (hsa:s≤a) (hab:a≤b) (hb:b≤2) (hu0:0≤u) (hu:u≤2)
    (hE:0≤E) (hd:b-a≤2*E) (hdu:2-u≤2*E) :
    |(u/a)^2-4/b^2|≤(8/s^2+32/s^4)*E := by
  have ha:0<a:=hs.trans_le hsa
  have hbp:0<b:=ha.trans_le hab
  have hi:=boundary_inverse_square_error hs hsa hab hb hE hd
  have hsq:s^2≤a^2:=by nlinarith
  have hn:4-u^2≤8*E := by
    have hprod: (2-u)*(2+u)≤(2*E)*4 :=
      (mul_le_mul_of_nonneg_right hdu (by positivity)).trans
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    nlinarith
  have he:(u/a)^2-4/b^2=(u^2-4)/a^2+4*(1/a^2-1/b^2) := by
    rw [div_pow]
    ring
  rw [he]
  calc
    _≤|(u^2-4)/a^2|+|4*(1/a^2-1/b^2)|:=abs_add_le _ _
    _=(4-u^2)/a^2+4*(1/a^2-1/b^2):=by
      rw [abs_div,abs_of_nonpos (by nlinarith : u^2-4≤0),abs_of_pos (sq_pos_of_pos ha),
        abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤4),abs_of_nonneg hi.1]
      ring
    _≤8*E/s^2+4*(8*E/s^4):=add_le_add
      ((div_le_div_of_nonneg_right hn (sq_nonneg a)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq))
      (mul_le_mul_of_nonneg_left hi.2 (by norm_num))
    _=_:=by ring

/-- The endpoint comparison scale `κ_N = (U_{log 2N}/A_N)²` tends to `4/A_∞²`. -/
theorem liClockPairedEtaPartitionComparisonScale_tendsto :
    Tendsto liClockPairedEtaPartitionComparisonScale atTop
      (𝓝 (4/liClockPairedEtaInfinitePartitionNormalizer^2)) := by
  change Tendsto (fun N:ℕ=>(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
    liClockPairedEtaPartitionNormalizer N)^2) atTop
      (𝓝 (4/liClockPairedEtaInfinitePartitionNormalizer^2))
  have h:=(tendsto_liClockPairedEtaHalfLinePartitionNormalizer.div
    tendsto_liClockPairedEtaInfinitePartitionNormalizer
    liClockPairedEtaInfinitePartitionNormalizer_pos.ne').pow 2
  simpa only [Pi.div_apply,div_pow,
    show (2:ℝ)^2=4 by norm_num] using h

/-- For `N ≥ 1`, `κ_N ≤ 4/(2 - √2)²`. -/
theorem liClockPairedEtaPartitionComparisonScale_le_halfLine {N:ℕ} (hN:0<N) :
    liClockPairedEtaPartitionComparisonScale N≤4/(2-Real.sqrt 2)^2 := by
  have hs:=boundary_firstMass_pos
  have ha:=liClockPairedEtaPartitionNormalizer_ge_first hN
  have hL:=boundary_logEndpoint_pos hN
  have hu0:0≤liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ))):=
    (liClockPairedEtaContiguousPartitionNormalizer_pos hL).le
  have hu:liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))≤2 := by
    have h:=liClockPairedEtaHalfLinePartitionNormalizer_sub_contiguous hL.le
    rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two] at h
    linarith [Real.exp_pos (-Real.log (2*(N:ℝ))/2)]
  unfold liClockPairedEtaPartitionComparisonScale
  rw [div_pow]
  exact (div_le_div_of_nonneg_right (by nlinarith :
    liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2≤4) (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith))

/-- For `N ≥ 1`, `|κ_N - 4/A_∞²| ≤ (8/(2-√2)² + 32/(2-√2)⁴) e^{-log(2N)/2}`. -/
theorem liClockPairedEtaPartitionComparisonScale_error_le {N:ℕ} (hN:0<N) :
    |liClockPairedEtaPartitionComparisonScale N-4/liClockPairedEtaInfinitePartitionNormalizer^2|≤
      (8/(2-Real.sqrt 2)^2+32/(2-Real.sqrt 2)^4)*
        Real.exp (-Real.log (2*(N:ℝ))/2) := by
  have hL:=boundary_logEndpoint_pos hN
  have hu:=liClockPairedEtaHalfLinePartitionNormalizer_sub_contiguous hL.le
  rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two] at hu
  exact boundary_normalizationScale_error boundary_firstMass_pos
    (liClockPairedEtaPartitionNormalizer_ge_first hN)
    (liClockPairedEtaPartitionNormalizer_le_infinite N)
    liClockPairedEtaInfinitePartitionNormalizer_lt_two.le
    (liClockPairedEtaContiguousPartitionNormalizer_pos hL).le
    (by linarith [Real.exp_pos (-Real.log (2*(N:ℝ))/2)])
    (Real.exp_pos _).le (liClockPairedEtaInfinitePartitionNormalizer_sub_finite_le hN).2 hu.le

/-- For each fixed `N`, `e^{x/2}` times the finite raw difference density tends to `0` as
`x → ∞` (it vanishes for `|x| ≥ log 2N`). -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_scaled_tendsto_zero (N:ℕ) :
    Tendsto (fun x:ℝ=>Real.exp (x/2)*liClockPairedEtaPartitionRawDifferenceDensity N x)
      atTop (𝓝 0) := by
  apply (tendsto_const_nhds (x:=(0:ℝ))).congr'
  filter_upwards [eventually_ge_atTop (Real.log (2*(N:ℝ))),eventually_ge_atTop (0:ℝ)] with x hL hx
  rw [liClockPairedEtaPartitionRawDifferenceDensity_zero_of_log_le_abs (by simpa only [abs_of_nonneg hx] using hL),mul_zero]

/-- For `N ≥ 1` and `0 ≤ x ≤ log 2N`, the scaled deficit `e^{x/2}(raw_∞(x) - raw_N(x))` lies in
`[0, e^{x - log 2N}]`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_deficit_le
    {N:ℕ} (hN:0<N) {x:ℝ} (hx:0≤x) (hxL:x≤Real.log (2*(N:ℝ))) :
    0≤Real.exp (x/2)*(liClockPairedEtaInfinitePartitionRawDifferenceDensity x-
      liClockPairedEtaPartitionRawDifferenceDensity N x) ∧
    Real.exp (x/2)*(liClockPairedEtaInfinitePartitionRawDifferenceDensity x-
      liClockPairedEtaPartitionRawDifferenceDensity N x)≤Real.exp (x-Real.log (2*(N:ℝ))) := by
  have h:=liClockPairedEtaInfinitePartitionRawDifferenceDensity_sub_finite_le hN x
  have href:=liClockPairedEtaHalfLineRawDifferenceDensity_sub_contiguous (Real.log (2*(N:ℝ))) x
  rw [abs_of_nonneg hx] at href
  have hbound:liClockPairedEtaHalfLineRawDifferenceDensity x-
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x=
      Real.exp (x/2-Real.log (2*(N:ℝ))) := by
    rw [href]
    by_cases hlt:x<Real.log (2*(N:ℝ))
    · rw [if_pos hlt]
    · have he:x=Real.log (2*(N:ℝ)):=le_antisymm hxL (le_of_not_gt hlt)
      rw [if_neg hlt,he]
      congr 1
      ring
  refine ⟨mul_nonneg (Real.exp_pos _).le h.1,?_⟩
  calc
    _≤Real.exp (x/2)*Real.exp (x/2-Real.log (2*(N:ℝ))):=
      mul_le_mul_of_nonneg_left (h.2.trans_eq hbound) (Real.exp_pos _).le
    _=_:=by rw [←Real.exp_add]; congr 1; ring

/-- For `N ≥ 1` and `0 ≤ x < log 2N`, `ρ_N(x) = κ_N · e^{x/2} raw_N(x) / (1 - e^{x - log 2N})`. -/
theorem liClockPairedEtaPartitionDensityRatio_eq_scaled
    {N:ℕ} (hN:0<N) {x:ℝ} (hx:0≤x) (hxL:x<Real.log (2*(N:ℝ))) :
    liClockPairedEtaPartitionDensityRatio N x=
      liClockPairedEtaPartitionComparisonScale N*
        (Real.exp (x/2)*liClockPairedEtaPartitionRawDifferenceDensity N x)/
          (1-Real.exp (x-Real.log (2*(N:ℝ)))) := by
  have hA:=liClockPairedEtaPartitionNormalizer_pos hN
  have hU:=liClockPairedEtaContiguousPartitionNormalizer_pos (boundary_logEndpoint_pos hN)
  have hden:0<1-Real.exp (x-Real.log (2*(N:ℝ))) := by
    have h:=Real.exp_lt_one_iff.mpr (sub_neg.mpr hxL)
    linarith
  unfold liClockPairedEtaPartitionDensityRatio liClockPairedEtaPartitionDifferenceDensity
    liClockPairedEtaContiguousDifferenceDensity liClockPairedEtaPartitionComparisonScale
  rw [liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg hx hxL,
    show -x/2= -(x/2) by ring,Real.exp_neg]
  field_simp

/-- For each fixed `j`, the ratio of finite to contiguous even difference moments tends, as
`N → ∞`, to the ratio of infinite to half-line moments. -/
theorem tendsto_liClockPairedEtaPartitionEvenMomentRatio (j:ℕ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j)
      atTop (𝓝 (liClockPairedEtaInfiniteSymmetrizedEvenMoment j/
        liClockPairedEtaHalfLineSymmetrizedEvenMoment j)) := by
  exact (tendsto_liClockPairedEtaInfiniteSymmetrizedEvenMoment j).div
    (tendsto_liClockPairedEtaHalfLineSymmetrizedEvenMoment j)
    (liClockPairedEtaHalfLineSymmetrizedEvenMoment_pos j).ne'

/-- The endpoint limit scale exceeds one: `1 < 4/A_∞²`. -/
theorem liClockPairedEtaInfinitePartitionEndpointScale_gt_one :
    1<4/liClockPairedEtaInfinitePartitionNormalizer^2 := by
  have hp:=liClockPairedEtaInfinitePartitionNormalizer_pos
  have hlt:=liClockPairedEtaInfinitePartitionNormalizer_lt_two
  apply (lt_div_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith

/-- For each fixed `x`, `e^{x/2} raw_N(x) → e^{x/2} raw_∞(x)` as `N → ∞`. -/
theorem tendsto_liClockPairedEtaPartitionRawDifferenceDensity_scaled_fixed (x:ℝ) :
    Tendsto (fun N:ℕ=>Real.exp (x/2)*liClockPairedEtaPartitionRawDifferenceDensity N x)
      atTop (𝓝 (Real.exp (x/2)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x)) :=
  (tendsto_liClockPairedEtaInfinitePartitionRawDifferenceDensity x).const_mul _

end
end RHTower

namespace RHTower

/-- Uniform transfer of a diverging negative gap: if `A_n`, `U_n` are uniformly `E_n`-close to
`A_∞`, `U_∞` on `[0, W_n]` with `E_n → 0` and `A_∞ - U_∞ → -∞`, then eventually
`A_n - U_n ≤ -1/2` on `[T, W_n]`. -/
private theorem boundary_uniform_negative_gap
    {A U : ℕ → ℝ → ℝ} {Ainf Uinf : ℝ → ℝ} {E W : ℕ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hA : ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ W n → |A n t - Ainf t| ≤ E n)
    (hU : ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ W n → |U n t - Uinf t| ≤ E n)
    (hgap : Tendsto (fun t => Ainf t - Uinf t) atTop atBot) :
    ∃ T : ℝ, 0 < T ∧
      ∀ᶠ n in atTop, ∀ t : ℝ, T ≤ t → t ≤ W n → A n t - U n t ≤ -(1 / 2) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hgap.eventually_le_atBot (-1))
  have hsmall := hE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  refine ⟨max T 1, ?_, ?_⟩
  · have h := le_max_right T (1 : ℝ)
    linarith
  · filter_upwards [hsmall, hA, hU] with n he ha hu
    intro t ht hw
    have ht0 : 0 ≤ t := by
      have h := le_max_right T (1 : ℝ)
      linarith
    have hga := (le_abs_self (A n t - Ainf t)).trans (ha t ht0 hw)
    have hgu := (neg_le_abs (U n t - Uinf t)).trans (hu t ht0 hw)
    have hgt := hT t ((le_max_left T 1).trans ht)
    linarith

end RHTower

namespace RHTower

private theorem boundary_ratio_competition {κ H G δ q e c0:ℝ}
    (hκ:0≤κ) (hq0:0≤q) (hq:q<1) (hδ0:0≤δ) (hδ:δ≤q)
    (hc0:0≤c0) (hc:c0≤1) (hH:H=G-δ) (he:|G-c0|≤e) :
    |κ*H/(1-q)-κ*c0|≤κ*(e+q)/(1-q) := by
  have hden:0<1-q:=by linarith
  have hsmall:|c0*q-δ|≤q := by
    have hmul:0≤c0*q:=mul_nonneg hc0 hq0
    have hmul':c0*q≤q:=by nlinarith
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hn:|H-c0*(1-q)|≤e+q := by
    rw [hH,show G-δ-c0*(1-q)=(G-c0)+(c0*q-δ) by ring]
    exact (abs_add_le _ _).trans (add_le_add he hsmall)
  have heq:κ*H/(1-q)-κ*c0=κ*(H-c0*(1-q))/(1-q) := by
    field_simp
  rw [heq,abs_div,abs_mul,abs_of_nonneg hκ,abs_of_pos hden]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hκ) hden.le

private theorem boundary_ratio_target_error {r κ κinf c0 K C e q E:ℝ}
    (hc0:0≤c0) (_hK:0≤K) (he:0≤e) (hq0:0≤q) (hq:q<1)
    (hκ:κ≤K) (hscale:|κ-κinf|≤C*E)
    (hr:|r-κ*c0|≤κ*(e+q)/(1-q)) :
    |r-c0*κinf|≤K*(e+q)/(1-q)+c0*C*E := by
  have hden:0<1-q:=by linarith
  have hdecomp:r-c0*κinf=(r-κ*c0)+c0*(κ-κinf):=by ring
  rw [hdecomp]
  calc
    _≤|r-κ*c0|+|c0*(κ-κinf)|:=abs_add_le _ _
    _≤κ*(e+q)/(1-q)+c0*(C*E):=add_le_add hr (by
      rw [abs_mul,abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left hscale hc0)
    _≤K*(e+q)/(1-q)+c0*(C*E):=add_le_add
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hκ (add_nonneg he hq0)) hden.le) (le_refl _)
    _=_:=by ring

private theorem boundary_bulk_error {C0 c0 Kscale Cnorm K x L:ℝ}
    (hC0:0≤C0) (hc0:0≤c0) (hKscale:0≤Kscale) (hCnorm:0≤Cnorm)
    (hK:0<K) (hx:K≤x) (hxL:x≤L-K) :
    Kscale*(C0*Real.exp (-x)+Real.exp (x-L))/(1-Real.exp (x-L))+
      c0*Cnorm*Real.exp (-L/2)≤
    Kscale*(C0+1)*Real.exp (-K)/(1-Real.exp (-K))+
      c0*Cnorm*Real.exp (-K) := by
  have hq:Real.exp (x-L)≤Real.exp (-K):=Real.exp_le_exp.mpr (by linarith)
  have he:Real.exp (-x)≤Real.exp (-K):=Real.exp_le_exp.mpr (by linarith)
  have hL:2*K≤L:=by linarith
  have hnorm:Real.exp (-L/2)≤Real.exp (-K):=Real.exp_le_exp.mpr (by linarith)
  have hden:0<1-Real.exp (-K):=by
    have h:=Real.exp_lt_one_iff.mpr (by linarith : -K<0)
    linarith
  apply add_le_add
  · calc
      _≤Kscale*((C0+1)*Real.exp (-K))/(1-Real.exp (x-L)):=by
        apply div_le_div_of_nonneg_right _ (by linarith)
        apply mul_le_mul_of_nonneg_left _ hKscale
        nlinarith [mul_le_mul_of_nonneg_left he hC0]
      _≤_:=by
        rw [←mul_assoc]
        exact div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  · exact mul_le_mul_of_nonneg_left hnorm (mul_nonneg hc0 hCnorm)

end RHTower

namespace RHTower
noncomputable section

private theorem boundary_mean_bounds : 0 ≤ Real.log 2 / 2 ∧ Real.log 2 / 2 ≤ 1 := by
  have hp := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hu := liClockPairedEtaInfinitePartition_log_two_lt_seven_div_ten
  constructor <;> linarith

private theorem boundary_comparisonScale_nonneg (N:ℕ) :
    0≤liClockPairedEtaPartitionComparisonScale N := by
  unfold liClockPairedEtaPartitionComparisonScale
  exact sq_nonneg _

private theorem boundary_comparisonLimit_eq :
    liClockPairedEtaInfinitePartitionComparisonLimit=
      (Real.log 2/2)*(4/liClockPairedEtaInfinitePartitionNormalizer^2) := by
  unfold liClockPairedEtaInfinitePartitionComparisonLimit
  ring

/-- For `N ≥ 1` and `0 ≤ x ≤ log 2N`,
`|e^{x/2} raw_N(x) - log 2 / 2| ≤ (π²/16) e^{-x} + e^{x - log 2N}`. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_scaled_error_le
    {N:ℕ} (hN:0<N) {x:ℝ} (hx:0≤x) (hxL:x≤Real.log (2*(N:ℝ))) :
    |Real.exp (x/2)*liClockPairedEtaPartitionRawDifferenceDensity N x-Real.log 2/2|≤
      (Real.pi^2/16)*Real.exp (-x)+Real.exp (x-Real.log (2*(N:ℝ))) := by
  have hd:=liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_deficit_le hN hx hxL
  have he:=liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_error_le hx
  rw [show Real.exp (x/2)*liClockPairedEtaPartitionRawDifferenceDensity N x-Real.log 2/2=
    (Real.exp (x/2)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x-Real.log 2/2)-
      Real.exp (x/2)*(liClockPairedEtaInfinitePartitionRawDifferenceDensity x-
        liClockPairedEtaPartitionRawDifferenceDensity N x) by ring]
  calc
    _ ≤ |Real.exp (x/2)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x-Real.log 2/2|+
        |Real.exp (x/2)*(liClockPairedEtaInfinitePartitionRawDifferenceDensity x-
          liClockPairedEtaPartitionRawDifferenceDensity N x)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le
        (Real.exp (x/2)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x-Real.log 2/2)
        (-(Real.exp (x/2)*(liClockPairedEtaInfinitePartitionRawDifferenceDensity x-
          liClockPairedEtaPartitionRawDifferenceDensity N x)))
    _≤_ := add_le_add he (by rw [abs_of_nonneg hd.1]; exact hd.2)

/-- For `N ≥ 1` and `0 ≤ x < log 2N`, explicit bound on `|ρ_N(x) - κ_N log 2 / 2|` by
`κ_N ((π²/16) e^{-x} + e^{x - log 2N}) / (1 - e^{x - log 2N})`. -/
theorem liClockPairedEtaPartitionDensityRatio_scaled_error_le
    {N:ℕ} (hN:0<N) {x:ℝ} (hx:0≤x) (hxL:x<Real.log (2*(N:ℝ))) :
    |liClockPairedEtaPartitionDensityRatio N x-
      liClockPairedEtaPartitionComparisonScale N*(Real.log 2/2)|≤
      liClockPairedEtaPartitionComparisonScale N*
        ((Real.pi^2/16)*Real.exp (-x)+Real.exp (x-Real.log (2*(N:ℝ))))/
          (1-Real.exp (x-Real.log (2*(N:ℝ)))) := by
  rw [liClockPairedEtaPartitionDensityRatio_eq_scaled hN hx hxL]
  have hd:=liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_deficit_le hN hx hxL.le
  exact boundary_ratio_competition (boundary_comparisonScale_nonneg N)
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (sub_neg.mpr hxL))
    hd.1 hd.2 boundary_mean_bounds.1 boundary_mean_bounds.2
    (by ring) (liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_error_le hx)

/-- For `N ≥ 1` and `0 ≤ x < log 2N`, explicit bound on `|ρ_N(x) - c_∞|` combining the
spatial error and the endpoint-scale error. -/
theorem liClockPairedEtaPartitionDensityRatio_bulk_error_le
    {N:ℕ} (hN:0<N) {x:ℝ} (hx:0≤x) (hxL:x<Real.log (2*(N:ℝ))) :
    |liClockPairedEtaPartitionDensityRatio N x-liClockPairedEtaInfinitePartitionComparisonLimit|≤
      (4/(2-Real.sqrt 2)^2)*
        ((Real.pi^2/16)*Real.exp (-x)+Real.exp (x-Real.log (2*(N:ℝ))))/
          (1-Real.exp (x-Real.log (2*(N:ℝ))))+
      (Real.log 2/2)*(8/(2-Real.sqrt 2)^2+32/(2-Real.sqrt 2)^4)*
        Real.exp (-Real.log (2*(N:ℝ))/2) := by
  rw [boundary_comparisonLimit_eq]
  exact boundary_ratio_target_error boundary_mean_bounds.1 (by positivity) (by positivity)
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (sub_neg.mpr hxL))
    (liClockPairedEtaPartitionComparisonScale_le_halfLine hN)
    (liClockPairedEtaPartitionComparisonScale_error_le hN)
    (liClockPairedEtaPartitionDensityRatio_scaled_error_le hN hx hxL)

/-- Explicit bulk error at distance `K` from both ends of `[0, log 2N]`; it is `O(e^{-K})`. -/
def liClockPairedEtaPartitionSpatialBulkError (K:ℝ) : ℝ :=
  (4/(2-Real.sqrt 2)^2)*(Real.pi^2/16+1)*Real.exp (-K)/(1-Real.exp (-K))+
    (Real.log 2/2)*(8/(2-Real.sqrt 2)^2+32/(2-Real.sqrt 2)^4)*Real.exp (-K)

/-- For `N ≥ 1`, `K > 0` and `K ≤ x ≤ log 2N - K`, `|ρ_N(x) - c_∞|` is at most the bulk error
at `K`, uniformly in `N`. -/
theorem liClockPairedEtaPartitionDensityRatio_uniform_bulk_error_le
    {N:ℕ} (hN:0<N) {K x:ℝ} (hK:0<K) (hx:K≤x)
    (hxL:x≤Real.log (2*(N:ℝ))-K) :
    |liClockPairedEtaPartitionDensityRatio N x-liClockPairedEtaInfinitePartitionComparisonLimit|≤
      liClockPairedEtaPartitionSpatialBulkError K := by
  exact (liClockPairedEtaPartitionDensityRatio_bulk_error_le hN (by linarith) (by linarith)).trans
    (boundary_bulk_error (by positivity) boundary_mean_bounds.1 (by positivity) (by positivity) hK hx hxL)

/-- The bulk error tends to `0` as `K → ∞`. -/
theorem tendsto_liClockPairedEtaPartitionSpatialBulkError_zero :
    Tendsto liClockPairedEtaPartitionSpatialBulkError atTop (𝓝 0) := by
  have he : Tendsto (fun K:ℝ=>Real.exp (-K)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h := ((he.const_mul ((4/(2-Real.sqrt 2)^2)*(Real.pi^2/16+1))).div
    (tendsto_const_nhds.sub he) (by norm_num : (1:ℝ)-0≠0)).add
      (he.const_mul ((Real.log 2/2)*(8/(2-Real.sqrt 2)^2+32/(2-Real.sqrt 2)^4)))
  simp only [mul_zero,sub_zero,zero_div,zero_add] at h
  exact h.congr (fun K=>by unfold liClockPairedEtaPartitionSpatialBulkError; simp only [Pi.div_apply])

end
end RHTower

namespace RHTower

/-- If `N → ∞`, `x → ∞` and `log 2N - x → ∞`, then `e^{x/2} raw_N(x) → log 2 / 2` and
`ρ_N(x) → c_∞ = 2 log 2 / A_∞²`. -/
theorem liClockPairedEtaInfinitePartitionSpatialBulk_joint_limits
    {N:ℕ→ℕ} {x:ℕ→ℝ} (hN:Tendsto N atTop atTop) (hx:Tendsto x atTop atTop)
    (hbulk:Tendsto (fun n=>Real.log (2*(N n:ℝ))-x n) atTop atTop) :
    Tendsto (fun n=>Real.exp (x n/2)*liClockPairedEtaPartitionRawDifferenceDensity (N n) (x n))
      atTop (𝓝 (Real.log 2/2)) ∧
    Tendsto (fun n=>liClockPairedEtaPartitionDensityRatio (N n) (x n))
      atTop (𝓝 liClockPairedEtaInfinitePartitionComparisonLimit) := by
  have hnpos : ∀ᶠ n in atTop,0<N n := by
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
    omega
  have hxpos := hx.eventually (eventually_ge_atTop (0:ℝ))
  have hinside : ∀ᶠ n in atTop,x n<Real.log (2*(N n:ℝ)) := by
    filter_upwards [hbulk.eventually (eventually_ge_atTop (1:ℝ))] with n hn
    linarith
  have he : Tendsto (fun n=>Real.exp (-x n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hx)
  have hq : Tendsto (fun n=>Real.exp (x n-Real.log (2*(N n:ℝ)))) atTop (𝓝 0) := by
    have h:=Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hbulk)
    exact h.congr (fun n=>by simp only [neg_sub,Function.comp_def])
  have hbound : Tendsto (fun n=>(Real.pi^2/16)*Real.exp (-x n)+
      Real.exp (x n-Real.log (2*(N n:ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using (he.const_mul (Real.pi^2/16)).add hq
  have hzero : Tendsto (fun n=>Real.exp (x n/2)*
      liClockPairedEtaPartitionRawDifferenceDensity (N n) (x n)-Real.log 2/2) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [hnpos,hxpos,hinside] with n hn hxn hxnL
    simpa only [Real.norm_eq_abs] using
      liClockPairedEtaPartitionRawDifferenceDensity_scaled_error_le hn hxn hxnL.le
  have hraw : Tendsto (fun n=>Real.exp (x n/2)*
      liClockPairedEtaPartitionRawDifferenceDensity (N n) (x n)) atTop (𝓝 (Real.log 2/2)) := by
    simpa only [sub_add_cancel,zero_add] using hzero.add_const (Real.log 2/2)
  refine ⟨hraw,?_⟩
  have hk:=liClockPairedEtaPartitionComparisonScale_tendsto.comp hN
  have hd : Tendsto (fun n=>1-Real.exp (x n-Real.log (2*(N n:ℝ)))) atTop (𝓝 (1:ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub hq
  have hr := (hk.mul hraw).div hd (by norm_num : (1:ℝ)≠0)
  have hconst : (4/liClockPairedEtaInfinitePartitionNormalizer^2*(Real.log 2/2))/1=
      liClockPairedEtaInfinitePartitionComparisonLimit := by
    rw [boundary_comparisonLimit_eq]
    ring
  rw [hconst] at hr
  apply hr.congr'
  filter_upwards [hnpos,hxpos,hinside] with n hn hxn hxnL
  exact (liClockPairedEtaPartitionDensityRatio_eq_scaled hn hxn hxnL).symm

/-- Non-commuting iterated limits of `e^{x/2} raw_N(x)`: `x → ∞` at fixed `N` gives `0`;
`N → ∞` at fixed `x` gives `e^{x/2} raw_∞(x)`, which tends to `log 2 / 2 ≠ 0` as `x → ∞`. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_iterated_limits :
    (∀N:ℕ,Tendsto (fun x:ℝ=>Real.exp (x/2)*liClockPairedEtaPartitionRawDifferenceDensity N x)
      atTop (𝓝 0)) ∧
    (∀x:ℝ,Tendsto (fun N:ℕ=>Real.exp (x/2)*liClockPairedEtaPartitionRawDifferenceDensity N x)
      atTop (𝓝 (Real.exp (x/2)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x))) ∧
    Tendsto (fun x:ℝ=>Real.exp (x/2)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x)
      atTop (𝓝 (Real.log 2/2)) ∧ (0:ℝ)≠Real.log 2/2 := by
  refine ⟨liClockPairedEtaPartitionRawDifferenceDensity_scaled_tendsto_zero,
    tendsto_liClockPairedEtaPartitionRawDifferenceDensity_scaled_fixed,
    liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_tendsto,?_⟩
  have hp:=Real.log_pos (by norm_num : (1:ℝ)<2)
  linarith

end RHTower

namespace RHTower

/-- Uniform spatial bulk law: for every `ε > 0` there is `K > 0` such that
`|ρ_N(x) - c_∞| < ε` for all `N ≥ 1` and all `K ≤ x ≤ log 2N - K`. -/
theorem liClockPairedEtaInfinitePartitionSpatialBulk_uniform
    {ε:ℝ} (hε:0<ε) :
    ∃K:ℝ,0<K ∧ ∀N:ℕ,0<N→∀x:ℝ,K≤x→x≤Real.log (2*(N:ℝ))-K→
      |liClockPairedEtaPartitionDensityRatio N x-liClockPairedEtaInfinitePartitionComparisonLimit|<ε := by
  obtain ⟨K0,hbound⟩:=eventually_atTop.mp
    (tendsto_liClockPairedEtaPartitionSpatialBulkError_zero.eventually (gt_mem_nhds hε))
  refine ⟨max K0 1,?_,?_⟩
  · have h:=le_max_right K0 (1:ℝ)
    linarith
  · intro N hN x hx hxL
    have hK : 0 < max K0 (1:ℝ) := by
      have h:=le_max_right K0 (1:ℝ)
      linarith
    exact (liClockPairedEtaPartitionDensityRatio_uniform_bulk_error_le hN hK hx hxL).trans_lt
      (hbound _ (le_max_left K0 1))

end RHTower

namespace RHTower

private theorem boundary_actual_kernel_error {c:ℝ} (hc0:0≤c) (hc:c<1/16)
    {N:ℕ} (hN:0<N) {t:ℝ} (ht:0≤t) (hw:t≤c*Real.log (2*(N:ℝ))) :
    |liClockPairedEtaPartitionBorelKernel N t-liClockPairedEtaInfinitePartitionBorelKernel t|≤
      liClockPairedEtaInfinitePartitionGrowingDiskError c N := by
  have h:=norm_liClockPairedEtaPartitionBorelKernelComplex_sub_infinite_le hc0 hc hN
    (z:=(t:ℂ)) (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] using hw)
  simpa only [liClockPairedEtaPartitionBorelKernelComplex_ofReal hN,
    liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using h

private theorem boundary_reference_kernel_error {c:ℝ} (hc0:0≤c) (hc:c<1/16)
    {N:ℕ} (hN:0<N) {t:ℝ} (ht:0≤t) (hw:t≤c*Real.log (2*(N:ℝ))) :
    |liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t-
      liClockPairedEtaHalfLineBorelKernel t|≤liClockPairedEtaInfinitePartitionGrowingDiskError c N := by
  have h:=norm_liClockPairedEtaContiguousBorelKernelComplex_sub_halfLine_le hc0 hc hN
    (z:=(t:ℂ)) (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] using hw)
  simpa only [liClockPairedEtaContiguousBorelKernelComplex_ofReal (boundary_logEndpoint_pos hN),
    liClockPairedEtaHalfLineBorelKernelComplex_ofReal,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using h

/-- The half-line Borel kernel satisfies `e^{-2t} G^{half}(t) → 1/2` as `t → ∞`. -/
theorem tendsto_liClockPairedEtaHalfLineBorelKernel_scaled :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*liClockPairedEtaHalfLineBorelKernel t)
      atTop (𝓝 (1/2)) := by
  have h:=tendsto_liClockPairedEtaHalfLineBorelKernel_sub_infinite_scaled.add
    tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled
  have heq : (1-liClockPairedEtaInfinitePartitionComparisonLimit)/2+
      liClockPairedEtaInfinitePartitionComparisonLimit/2=(1/2:ℝ) := by ring
  rw [heq] at h
  exact h.congr (fun t=>by ring)

/-- For `0 < c < 1/16`, if `N, t → ∞` with eventually `0 ≤ t ≤ c log 2N`, then
`e^{-2t} G_N(t) → c_∞/2`, `e^{-2t} G^{cont}(t) → 1/2`, `G_N/G^{cont} → c_∞` and
`G_N - G^{cont} → -∞`. -/
theorem liClockPairedEtaInfinitePartitionBorel_qualified_joint_limits
    {c:ℝ} (hc0:0<c) (hc:c<1/16) {N:ℕ→ℕ} {t:ℕ→ℝ}
    (hN:Tendsto N atTop atTop) (ht:Tendsto t atTop atTop)
    (hwindow:∀ᶠ n in atTop,0≤t n ∧ t n≤c*Real.log (2*(N n:ℝ))) :
    Tendsto (fun n=>Real.exp (-2*t n)*liClockPairedEtaPartitionBorelKernel (N n) (t n))
      atTop (𝓝 (liClockPairedEtaInfinitePartitionComparisonLimit/2)) ∧
    Tendsto (fun n=>Real.exp (-2*t n)*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N n:ℝ))) (t n)) atTop (𝓝 (1/2)) ∧
    Tendsto (fun n=>liClockPairedEtaPartitionBorelKernel (N n) (t n)/
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N n:ℝ))) (t n))
      atTop (𝓝 liClockPairedEtaInfinitePartitionComparisonLimit) ∧
    Tendsto (fun n=>liClockPairedEtaPartitionBorelKernel (N n) (t n)-
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N n:ℝ))) (t n)) atTop atBot := by
  have hnpos : ∀ᶠ n in atTop,0<N n := by
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
    omega
  have he:=(tendsto_liClockPairedEtaInfinitePartitionGrowingDiskError_zero hc0.le hc).comp hN
  have ha : Tendsto (fun n=>liClockPairedEtaPartitionBorelKernel (N n) (t n)-
      liClockPairedEtaInfinitePartitionBorelKernel (t n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [hnpos,hwindow] with n hn hw
    simpa only [Real.norm_eq_abs,Function.comp_def] using boundary_actual_kernel_error hc0.le hc hn hw.1 hw.2
  have hu : Tendsto (fun n=>liClockPairedEtaContiguousBorelKernel (Real.log (2*(N n:ℝ))) (t n)-
      liClockPairedEtaHalfLineBorelKernel (t n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [hnpos,hwindow] with n hn hw
    simpa only [Real.norm_eq_abs,Function.comp_def] using boundary_reference_kernel_error hc0.le hc hn hw.1 hw.2
  exact boundary_qualified_kernel_limits ht ha hu
    (tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled.comp ht)
    (tendsto_liClockPairedEtaHalfLineBorelKernel_scaled.comp ht)
    liClockPairedEtaInfinitePartitionComparisonLimit_lt_one

/-- For `0 < c < 1/16` there is `T > 0` such that, for all large `N`,
`G_N(t) - G^{cont}(t) ≤ -1/2` whenever `T ≤ t ≤ c log 2N`. -/
theorem liClockPairedEtaInfinitePartitionBorel_uniform_negative_gap
    {c:ℝ} (hc0:0<c) (hc:c<1/16) :
    ∃T:ℝ,0<T ∧ ∀ᶠ N:ℕ in atTop,∀t:ℝ,T≤t→t≤c*Real.log (2*(N:ℝ))→
      liClockPairedEtaPartitionBorelKernel N t-
        liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t≤-(1/2) := by
  have hg : Tendsto (fun t:ℝ=>liClockPairedEtaInfinitePartitionBorelKernel t-
      liClockPairedEtaHalfLineBorelKernel t) atTop atBot := by
    have h:=tendsto_neg_atTop_atBot.comp tendsto_liClockPairedEtaHalfLineBorelKernel_sub_infinite
    exact h.congr (fun t=>by simp only [Function.comp_def,neg_sub])
  refine boundary_uniform_negative_gap
    (tendsto_liClockPairedEtaInfinitePartitionGrowingDiskError_zero hc0.le hc) ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop 1] with N hN
    intro t ht hw
    exact boundary_actual_kernel_error hc0.le hc (by omega) ht hw
  · filter_upwards [eventually_ge_atTop 1] with N hN
    intro t ht hw
    exact boundary_reference_kernel_error hc0.le hc (by omega) ht hw

/-- For fixed `t`, the finite Borel kernel `G_N(t)` tends to the infinite kernel `G_∞(t)`. -/
theorem tendsto_liClockPairedEtaPartitionBorelKernel_fixed (t:ℝ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaPartitionBorelKernel N t) atTop
      (𝓝 (liClockPairedEtaInfinitePartitionBorelKernel t)) := by
  have hz : (t:ℂ)∈Metric.closedBall 0 |t| := by
    simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact le_rfl
  have h:=(Complex.reCLM.continuous.tendsto
    (liClockPairedEtaInfinitePartitionBorelKernelComplex (t:ℂ))).comp
      ((tendstoUniformlyOn_liClockPairedEtaPartitionBorelKernelComplex |t|).tendsto_at hz)
  simp only [Function.comp_def,Complex.reCLM_apply,liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal,
    Complex.ofReal_re] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [liClockPairedEtaPartitionBorelKernelComplex_ofReal (by omega),Complex.ofReal_re]

/-- For fixed `t`, the contiguous Borel kernel on `(0, log 2N]` tends to the half-line kernel. -/
theorem tendsto_liClockPairedEtaContiguousBorelKernel_fixed (t:ℝ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) atTop
      (𝓝 (liClockPairedEtaHalfLineBorelKernel t)) := by
  have hz : (t:ℂ)∈Metric.closedBall 0 |t| := by
    simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact le_rfl
  have h:=(Complex.reCLM.continuous.tendsto
    (liClockPairedEtaHalfLineBorelKernelComplex (t:ℂ))).comp
      ((tendstoUniformlyOn_liClockPairedEtaContiguousBorelKernelComplex |t|).tendsto_at hz)
  simp only [Function.comp_def,Complex.reCLM_apply,liClockPairedEtaHalfLineBorelKernelComplex_ofReal,
    Complex.ofReal_re] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [liClockPairedEtaContiguousBorelKernelComplex_ofReal (boundary_logEndpoint_pos (by omega)),
    Complex.ofReal_re]

/-- For fixed `t`, `G_N(t)/G^{cont}(t) → G_∞(t)/G^{half}(t)` as `N → ∞`. -/
theorem tendsto_liClockPairedEtaPartitionBorelRatio_fixed (t:ℝ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaPartitionBorelKernel N t/
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) atTop
        (𝓝 (liClockPairedEtaInfinitePartitionBorelKernel t/liClockPairedEtaHalfLineBorelKernel t)) := by
  have hp : 0<liClockPairedEtaHalfLineBorelKernel t := by
    rw [liClockPairedEtaHalfLineBorelKernel_eq_cosh]
    exact Real.cosh_pos _
  exact (tendsto_liClockPairedEtaPartitionBorelKernel_fixed t).div
    (tendsto_liClockPairedEtaContiguousBorelKernel_fixed t) hp.ne'

/-- The bulk and endpoint limits are separated: `c_∞ < 1 < 4/A_∞²`, so `4/A_∞² ≠ c_∞`. -/
theorem liClockPairedEtaInfinitePartition_comparison_limits_distinct :
    liClockPairedEtaInfinitePartitionComparisonLimit<1 ∧
    1<4/liClockPairedEtaInfinitePartitionNormalizer^2 ∧
    4/liClockPairedEtaInfinitePartitionNormalizer^2≠liClockPairedEtaInfinitePartitionComparisonLimit :=
  ⟨liClockPairedEtaInfinitePartitionComparisonLimit_lt_one,
    liClockPairedEtaInfinitePartitionEndpointScale_gt_one,
    ne_of_gt (liClockPairedEtaInfinitePartitionComparisonLimit_lt_one.trans
      liClockPairedEtaInfinitePartitionEndpointScale_gt_one)⟩

/-- Order-of-limits boundary for even moment ratios: `j → ∞` then `N → ∞` gives `4/A_∞²`, while
`N → ∞` then `j → ∞` gives `c_∞`, and these differ. -/
theorem liClockPairedEtaInfinitePartition_moment_ratio_order_boundary :
    (∀N:ℕ,0<N→Tendsto (fun j:ℕ=>liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j) atTop
        (𝓝 (liClockPairedEtaPartitionComparisonScale N))) ∧
    Tendsto liClockPairedEtaPartitionComparisonScale atTop
      (𝓝 (4/liClockPairedEtaInfinitePartitionNormalizer^2)) ∧
    (∀j:ℕ,Tendsto (fun N:ℕ=>liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j) atTop
        (𝓝 (liClockPairedEtaInfiniteSymmetrizedEvenMoment j/liClockPairedEtaHalfLineSymmetrizedEvenMoment j))) ∧
    Tendsto (fun j:ℕ=>liClockPairedEtaInfiniteSymmetrizedEvenMoment j/
      liClockPairedEtaHalfLineSymmetrizedEvenMoment j) atTop (𝓝 liClockPairedEtaInfinitePartitionComparisonLimit) ∧
    4/liClockPairedEtaInfinitePartitionNormalizer^2≠liClockPairedEtaInfinitePartitionComparisonLimit := by
  exact ⟨fun N hN=>liClockPairedEtaPartitionEndpoint_evenMoment_ratio_tendsto hN,
    liClockPairedEtaPartitionComparisonScale_tendsto,tendsto_liClockPairedEtaPartitionEvenMomentRatio,
    tendsto_liClockPairedEtaInfinitePartitionMomentRatio,
    liClockPairedEtaInfinitePartition_comparison_limits_distinct.2.2⟩

/-- Order-of-limits boundary for Borel kernel ratios: `t → ∞` then `N → ∞` gives `4/A_∞²`, while
`N → ∞` then `t → ∞` gives `c_∞`, and these differ. -/
theorem liClockPairedEtaInfinitePartition_Borel_ratio_order_boundary :
    (∀N:ℕ,0<N→Tendsto (fun t:ℝ=>liClockPairedEtaPartitionBorelKernel N t/
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) atTop
        (𝓝 (liClockPairedEtaPartitionComparisonScale N))) ∧
    Tendsto liClockPairedEtaPartitionComparisonScale atTop
      (𝓝 (4/liClockPairedEtaInfinitePartitionNormalizer^2)) ∧
    (∀t:ℝ,Tendsto (fun N:ℕ=>liClockPairedEtaPartitionBorelKernel N t/
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) atTop
        (𝓝 (liClockPairedEtaInfinitePartitionBorelKernel t/liClockPairedEtaHalfLineBorelKernel t))) ∧
    Tendsto (fun t:ℝ=>liClockPairedEtaInfinitePartitionBorelKernel t/
      liClockPairedEtaHalfLineBorelKernel t) atTop (𝓝 liClockPairedEtaInfinitePartitionComparisonLimit) ∧
    4/liClockPairedEtaInfinitePartitionNormalizer^2≠liClockPairedEtaInfinitePartitionComparisonLimit := by
  exact ⟨fun N hN=>liClockPairedEtaPartitionEndpoint_borel_ratio_tendsto hN,
    liClockPairedEtaPartitionComparisonScale_tendsto,tendsto_liClockPairedEtaPartitionBorelRatio_fixed,
    tendsto_liClockPairedEtaInfinitePartitionBorelKernel_div_halfLine,
    liClockPairedEtaInfinitePartition_comparison_limits_distinct.2.2⟩

/-- At `N = 1` the source coincides with the contiguous interval `(0, log 2]`: equal moments,
equal Borel kernels, and `κ_1 = 1`. -/
theorem liClockPairedEtaInfinitePartition_first_prefix_equalities :
    (∀j:ℕ,liClockPairedEtaSymmetrizedEvenMoment 1 j=
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log 2) j) ∧
    (∀t:ℝ,liClockPairedEtaPartitionBorelKernel 1 t=
      liClockPairedEtaContiguousBorelKernel (Real.log 2) t) ∧
    liClockPairedEtaPartitionComparisonScale 1=1 :=
  ⟨liClockPairedEtaSymmetrizedEvenMoment_one_eq_contiguous,
    liClockPairedEtaBorelKernel_one_eq_contiguous,liClockPairedEtaPartitionComparisonScale_one⟩

/-- Opposite escapes: for each fixed `N ≥ 2`, `G_N(t) - G^{cont}(t) → +∞` as `t → ∞`, while for
`0 < c < 1/16` along any joint window `0 ≤ t ≤ c log 2N` with `N, t → ∞` it tends to `-∞`. -/
theorem liClockPairedEtaInfinitePartition_Borel_opposite_boundary_escapes
    {c:ℝ} (hc0:0<c) (hc:c<1/16) :
    (∀N:ℕ,2≤N→Tendsto (fun t:ℝ=>liClockPairedEtaPartitionBorelKernel N t-
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) atTop atTop) ∧
    (∀(N:ℕ→ℕ)(t:ℕ→ℝ),Tendsto N atTop atTop→Tendsto t atTop atTop→
      (∀ᶠ n in atTop,0≤t n ∧ t n≤c*Real.log (2*(N n:ℝ)))→
      Tendsto (fun n=>liClockPairedEtaPartitionBorelKernel (N n) (t n)-
        liClockPairedEtaContiguousBorelKernel (Real.log (2*(N n:ℝ))) (t n)) atTop atBot) := by
  refine ⟨fun N hN=>liClockPairedEtaPartitionEndpoint_borel_sub_contiguous_tendsto_atTop hN,?_⟩
  intro N t hN ht hwindow
  exact (liClockPairedEtaInfinitePartitionBorel_qualified_joint_limits hc0 hc hN ht hwindow).2.2.2

end RHTower
