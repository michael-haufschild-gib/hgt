import GaloisForLFunctions.RHTower.CHMDOddHarmonicIdentityAndPolarDoobAbsorption
import GaloisForLFunctions.RHTower.CHMDPrimeChainSourceFactorization

/-!
# Secondary Odd-Profile Archimedean Collar Absorption, Prime-Chain Bridge, and Collar Duality

This module executes **Option 1** of the `CHMD + HF + EWU` synthesis (`docs/notes.md`), bridging the
secondary odd-sector Doob ground-state factorization `f(x) = m_a(x) w(x)` (`w` even) from
`CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean` with the complete divisor-chain variance
factorization (`N = m d n`) in `CHMDPrimeChainSourceFactorization.lean` and the reflected-prime
singular structure in `CHMDReflectedPrimeSingularPart.lean`.

## Mathematical Overview

1. **Midpoint Folding and Exact Integral Collar Absorption in `oddProfile a` Coordinates**:
   - The origin-crossing collar difference integrand
     $$\operatorname{oddProfileCollarDiffSq}(a, w, t, x)
       := m_a(x)\,m_a(t - x)\,(w(x) - w(t - x))^2$$
     is symmetric under midpoint reflection `x ↦ t - x` on `(0, t)` and coincides with the shifted
     forward jump `oddProfileShiftJump a w (t - 2x) x`.
   - Consequently, the collar integral on `(0, t)` folds onto twice the half-collar `(0, t / 2)`
     (`integral_oddProfileCollarDiffSq_eq_two_mul_half`), and for every even compactly supported
     continuous profile `w`,
     $$\int_{\mathbb{R}} \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx
       = 2 \int_0^\infty \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx
         - 2 \int_0^{t/2} \operatorname{oddProfileShiftJump}(a, w, t - 2x, x)\,dx$$
     (`integral_oddProfileShiftJump_eq_two_mul_Ioi_sub_two_mul_half`).
   - For each fixed `x > 0`, translating `t = 2x + s` (`s > 0`) maps the archimedean collar integral
     over `t ∈ (2x, ∞)` onto `(0, ∞)` (`integral_arch_collar_shift_eq`) and absorbs it into the
     direct half-line archimedean integral via the nonnegative kernel
     `absorbedArchIntegrand a w s x = (ω(s) - ω(2x + s)) oddProfileShiftJump a w s x ≥ 0`
     (`integral_arch_direct_sub_collar_eq_absorbed`, `integral_arch_direct_sub_collar_nonneg`).

2. **Exact Bridge Between `oddProfileTest a w` and the `Θ`-Doob Divisor-Chain Factorization**:
   - Every secondary odd-profile test `oddProfileTest a w x = m_a(x) w(x)` equals the primary
     `Θ`-Doob test `phiDoobTest (oddPolarWeight a w) x` where
     `oddPolarWeight a w x = Ψ_a(x) w(x)` (`phiDoobTest_oddPolarWeight_eq_oddProfileTest`).
   - When `w` is even, `oddPolarWeight a w` is odd, smooth (`ContDiff ℝ 2`), and compactly
     supported (`oddPolarWeight_odd_of_even`, `contDiff_oddPolarWeight`,
     `hasCompactSupport_oddPolarWeight`), so `markovEnergy (oddProfileTest a w)` admits the
     complete nonnegative divisor-chain expansion (`oddProfileTest_markovEnergy_eq_chain_variances_sub_cosh`)
     and the reflected-prime collar compensation (`oddPolarWeight_reflected_compensation_hasSum_chains`).

3. **Universal Origin-Crossing Collar Duality (`collar_sumSq_add_oddProfile_diffSq_eq_mixed`)**:
   - On the origin-crossing collar `x ∈ (0, t)`, the positive `Θ`-Doob crossing sum-of-values
     `(Ψ_a(x) w(x) + Ψ_a(t - x) w(t - x))²` and the positive `m_a`-Doob collar difference square
     `Ψ_a(x) Ψ_a(t - x) (w(x) - w(t - x))²` satisfy the universal algebraic duality
     $$(\psi_1 w_1 + \psi_2 w_2)^2 + \psi_1 \psi_2 (w_1 - w_2)^2
       = (\psi_1 + \psi_2)(\psi_1 w_1^2 + \psi_2 w_2^2).$$
   - Multiplying by `Θ(x) Θ(t - x)` and summing over all prime powers `d` relates the complete
     divisor-chain variance sum `∑' q : ChainIndex, chainIntegral (Ψ_a w) q` directly to the
     `m_a`-Doob prime collar (`primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed`,
     `chainIntegral_tsum_add_oddProfilePrimeCollar_eq_mixed`).

4. **Short-Support / Reflection-Symmetric Collar Vanishing and Convex Gauge Interpolation**:
   - Whenever `w` vanishes on `(0, t)` or is symmetric across the collar midpoint `t / 2`
     (`w(t - x) = w(x)` on `(0, t)`), the negative `m_a`-Doob collar integral vanishes identically
     (`integral_oddProfileCollarDiffSq_eq_zero_of_symmetric`,
     `integral_oddProfileShiftJump_nonneg_of_collar_symmetric`).
   - Taking a convex combination `(1 - θ)` of the `Θ`-Doob divisor-chain decomposition and `θ` of
     the `m_a`-Doob positive-`sinh` potential identity yields the exact gauge-interpolated energy
     law (`convex_doob_chain_sinh_interpolation`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph ThetaSourceWard PhiDivisorEnergy CHMDPrimeCuts CHMDPrimeChainSource

/-! ## Section 1: Midpoint Folding and Exact Integral Collar Absorption in `oddProfile a` Coordinates -/

/-- The origin-crossing collar Dirichlet difference integrand in `oddProfile a` coordinates on `(0, t)`:
`oddProfileCollarDiffSq a w t x = m_a(x) m_a(t - x) (w(x) - w(t - x))²`. -/
def oddProfileCollarDiffSq (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) : ℝ :=
  oddProfile a x * oddProfile a (t - x) * (w x - w (t - x)) ^ 2

theorem oddProfileCollarDiffSq_nonneg {a t x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo (0 : ℝ) t) (w : ℝ → ℝ) :
    0 ≤ oddProfileCollarDiffSq a w t x := by
  unfold oddProfileCollarDiffSq
  exact mul_nonneg
    (mul_nonneg (oddProfile_pos ha hx.1).le (oddProfile_pos ha (sub_pos.mpr hx.2)).le)
    (sq_nonneg _)

theorem oddProfileCollarDiffSq_reflect (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) :
    oddProfileCollarDiffSq a w t (t - x) = oddProfileCollarDiffSq a w t x := by
  unfold oddProfileCollarDiffSq
  rw [show t - (t - x) = x by ring]
  ring

theorem oddProfileCollarDiffSq_eq_oddProfileShiftJump (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) :
    oddProfileCollarDiffSq a w t x = oddProfileShiftJump a w (t - 2 * x) x := by
  unfold oddProfileCollarDiffSq oddProfileShiftJump
  rw [show x + (t - 2 * x) = t - x by ring]

/-- **Midpoint Folding of the Odd-Profile Collar (`(0, t)` to `2 × (0, t / 2)`)**:
for any continuous `w : ℝ → ℝ` and `t ≥ 0`,
`∫_{x ∈ (0, t)} m_a(x) m_a(t - x) (w(x) - w(t - x))² dx = 2 ∫_{x ∈ (0, t / 2)} oddProfileShiftJump a w (t - 2x) x dx`. -/
theorem integral_oddProfileCollarDiffSq_eq_two_mul_half (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) =
      2 * ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w (t - 2 * x) x := by
  have hint : IntegrableOn (oddProfileCollarDiffSq a w t) (Icc (0 : ℝ) t) := by
    unfold oddProfileCollarDiffSq
    exact (((continuous_oddProfile a).mul
      ((continuous_oddProfile a).comp (continuous_const.sub continuous_id))).mul
      ((hw.sub (hw.comp (continuous_const.sub continuous_id))).pow 2)).continuousOn.integrableOn_Icc
  have hunion : Ioc (0 : ℝ) (t / 2) ∪ Ioc (t / 2) t = Ioc (0 : ℝ) t :=
    Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hdisj : Disjoint (Ioc (0 : ℝ) (t / 2)) (Ioc (t / 2) t) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  rw [← integral_Ioc_eq_integral_Ioo, ← hunion,
    setIntegral_union hdisj measurableSet_Ioc
      (hint.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))
      (hint.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl))),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    setIntegral_Ioo_reflect_midpoint (oddProfileCollarDiffSq a w t) t]
  have hrefl : (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t (t - x)) =
      ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t x :=
    setIntegral_congr_fun measurableSet_Ioo fun x _ => oddProfileCollarDiffSq_reflect a w t x
  have hcongr : (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t x) =
      ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w (t - 2 * x) x :=
    setIntegral_congr_fun measurableSet_Ioo fun x _ =>
      oddProfileCollarDiffSq_eq_oddProfileShiftJump a w t x
  rw [hrefl, hcongr]
  ring

/-- **Exact Half-Line Shift-by-Shift Decomposition in `oddProfile a` Coordinates**:
for any even continuous compactly supported `w : ℝ → ℝ` and `t ≥ 0`, both the direct half-line
jump on `(0, ∞)` and the reflected half-collar jump on `(0, t / 2)` carry a factor of `2` and the
identical Dirichlet difference kernel `oddProfileShiftJump`:
`∫_ℝ oddProfileShiftJump a w t x = 2 ∫_{x > 0} oddProfileShiftJump a w t x - 2 ∫_{x ∈ (0, t / 2)} oddProfileShiftJump a w (t - 2x) x`. -/
theorem integral_oddProfileShiftJump_eq_two_mul_Ioi_sub_two_mul_half (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, oddProfileShiftJump a w t x) =
      2 * (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w t x) -
        2 * ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w (t - 2 * x) x := by
  rw [integral_oddProfileShiftJump_eq_halfLine_of_even a hw hwc heven ht]
  have hcol : (∫ x in Ioo (0 : ℝ) t,
      oddProfile a x * oddProfile a (t - x) * (w x - w (t - x)) ^ 2) =
      ∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x := rfl
  rw [hcol, integral_oddProfileCollarDiffSq_eq_two_mul_half a hw ht]

/-- **Fixed-`x` Archimedean Collar Translation Identity (`t = 2x + s`)**:
for any fixed `x : ℝ`, translating `s ↦ s + 2x` identifies the archimedean collar integral over
`t ∈ (2x, ∞)` with the half-line integral over `s ∈ (0, ∞)` of `ω(2x + s) oddProfileShiftJump a w s x`. -/
theorem integral_arch_collar_shift_eq (a : ℝ) (w : ℝ → ℝ) (x : ℝ) :
    (∫ t in Ioi (2 * x), archLevyDensity t * oddProfileCollarDiffSq a w t x) =
      ∫ s in Ioi (0 : ℝ), archLevyDensity (2 * x + s) * oddProfileShiftJump a w s x := by
  have hmp : MeasurePreserving (fun s : ℝ => s + 2 * x) volume volume :=
    measurePreserving_add_right volume (2 * x)
  have hemb : MeasurableEmbedding (fun s : ℝ => s + 2 * x) :=
    (Homeomorph.addRight (2 * x)).measurableEmbedding
  have hpre : (fun s : ℝ => s + 2 * x) ⁻¹' Ioi (2 * x) = Ioi (0 : ℝ) := by
    ext s; simp
  have htr := hmp.setIntegral_preimage_emb hemb
    (fun t : ℝ => archLevyDensity t * oddProfileCollarDiffSq a w t x) (Ioi (2 * x))
  rw [hpre] at htr
  rw [← htr]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [oddProfileCollarDiffSq_eq_oddProfileShiftJump,
    show s + 2 * x - 2 * x = s by ring, show s + 2 * x = 2 * x + s by ring]

/-- **Dominated Integrability of the Shifted Archimedean Collar Kernel**:
for `a > 0` and `x > 0`, because `0 < ω(2x + s) < ω(s)` on `s ∈ (0, ∞)`, integrability of the
direct archimedean jump `s ↦ ω(s) oddProfileShiftJump a w s x` on `(0, ∞)` automatically implies
integrability of the shifted collar kernel `s ↦ ω(2x + s) oddProfileShiftJump a w s x`. -/
theorem integrableOn_arch_collar_shift_of_direct {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hdir : IntegrableOn (fun s : ℝ => archLevyDensity s * oddProfileShiftJump a w s x) (Ioi 0)) :
    IntegrableOn (fun s : ℝ => archLevyDensity (2 * x + s) * oddProfileShiftJump a w s x) (Ioi 0) := by
  have hcont : ContinuousOn
      (fun s : ℝ => archLevyDensity (2 * x + s) * oddProfileShiftJump a w s x) (Ioi 0) := by
    have hden : ContinuousOn (fun s : ℝ => archLevyDensity (2 * x + s)) (Ioi 0) := by
      unfold archLevyDensity
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => ?_
      have hs0 : 0 < s := mem_Ioi.mp hs
      exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
    have hjump : Continuous (fun s : ℝ => oddProfileShiftJump a w s x) := by
      unfold oddProfileShiftJump
      exact ((continuous_const.mul
        ((continuous_oddProfile a).comp (continuous_const.add continuous_id))).mul
        ((continuous_const.sub (hw.comp (continuous_const.add continuous_id))).pow 2))
    exact hden.mul hjump.continuousOn
  refine hdir.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := mem_Ioi.mp hs
  have hpos_shift : 0 < archLevyDensity (2 * x + s) := archLevyDensity_pos (by linarith)
  have hj_nonneg : 0 ≤ oddProfileShiftJump a w s x :=
    oddProfileShiftJump_nonneg_of_pos ha hx hs0.le w
  have hlt : archLevyDensity (2 * x + s) ≤ archLevyDensity s :=
    (strictAntiOn_archLevyDensity_Ioi hs (mem_Ioi.mpr (by linarith)) (by linarith)).le
  rw [Real.norm_of_nonneg (mul_nonneg hpos_shift.le hj_nonneg)]
  exact mul_le_mul_of_nonneg_right hlt hj_nonneg

/-- **Exact Integral Archimedean Collar Absorption for Fixed `x > 0`**:
subtracting the origin-crossing archimedean collar integral over `t ∈ (2x, ∞)` from the direct
half-line archimedean integral over `s ∈ (0, ∞)` yields the integral of `absorbedArchIntegrand a w s x`,
which is strictly nonnegative. -/
theorem integral_arch_direct_sub_collar_eq_absorbed {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hdir : IntegrableOn (fun s : ℝ => archLevyDensity s * oddProfileShiftJump a w s x) (Ioi 0)) :
    (∫ s in Ioi (0 : ℝ), archLevyDensity s * oddProfileShiftJump a w s x) -
        (∫ t in Ioi (2 * x), archLevyDensity t * oddProfileCollarDiffSq a w t x) =
      ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s x := by
  have hcol := integrableOn_arch_collar_shift_of_direct ha hx hw hdir
  rw [integral_arch_collar_shift_eq, ← integral_sub hdir hcol]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  unfold absorbedArchIntegrand
  ring

theorem integral_arch_direct_sub_collar_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hdir : IntegrableOn (fun s : ℝ => archLevyDensity s * oddProfileShiftJump a w s x) (Ioi 0)) :
    0 ≤ (∫ s in Ioi (0 : ℝ), archLevyDensity s * oddProfileShiftJump a w s x) -
        (∫ t in Ioi (2 * x), archLevyDensity t * oddProfileCollarDiffSq a w t x) := by
  rw [integral_arch_direct_sub_collar_eq_absorbed ha hx hw hdir]
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  exact absorbedArchIntegrand_nonneg ha (mem_Ioi.mp hs) hx w

/-! ## Section 2: Exact Bridge Between `oddProfileTest a w` and the `Θ`-Doob Divisor-Chain Factorization -/

/-- The primary `Θ`-Doob gauge profile `v(x) = Ψ_a(x) w(x)` corresponding to the secondary
odd-profile test `f(x) = m_a(x) w(x)`. -/
def oddPolarWeight (a : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  oddPolarFunction a x * w x

/-- **Gauge Compatibility Identity**:
the primary `Θ`-Doob test of `oddPolarWeight a w` is identically the secondary odd-profile test
`oddProfileTest a w`. -/
theorem phiDoobTest_oddPolarWeight_eq_oddProfileTest (a : ℝ) (w : ℝ → ℝ) (x : ℝ) :
    phiDoobTest (oddPolarWeight a w) x = oddProfileTest a w x := by
  unfold phiDoobTest oddPolarWeight oddProfileTest
  rw [oddPolarFunction_eq_oddProfile_div, ← mul_assoc,
    mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']

theorem phiDoobTest_oddPolarWeight_fun_eq (a : ℝ) (w : ℝ → ℝ) :
    phiDoobTest (oddPolarWeight a w) = oddProfileTest a w :=
  funext (phiDoobTest_oddPolarWeight_eq_oddProfileTest a w)

/-- When `w` is even (`w(-x) = w(x)`), `oddPolarWeight a w` is odd (`v(-x) = -v(x)`). -/
theorem oddPolarWeight_odd_of_even (a : ℝ) {w : ℝ → ℝ} (heven : ∀ x, w (-x) = w x) (x : ℝ) :
    oddPolarWeight a w (-x) = -oddPolarWeight a w x := by
  unfold oddPolarWeight
  rw [oddPolarFunction_neg, heven, neg_mul]

theorem continuous_oddPolarWeight (a : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (oddPolarWeight a w) :=
  (continuous_oddPolarFunction a).mul hw

theorem hasCompactSupport_oddPolarWeight (a : ℝ) {w : ℝ → ℝ} (hwc : HasCompactSupport w) :
    HasCompactSupport (oddPolarWeight a w) :=
  hwc.mul_left

theorem contDiff_oddProfile {n : ℕ∞} (a : ℝ) : ContDiff ℝ n (oddProfile a) := by
  unfold oddProfile
  exact ((contDiff_riemannKernelReal.comp (contDiff_id.sub contDiff_const)).sub
    (contDiff_riemannKernelReal.comp (contDiff_id.add contDiff_const))).div_const _

theorem contDiff_oddPolarFunction {n : ℕ∞} (a : ℝ) : ContDiff ℝ n (oddPolarFunction a) := by
  have heq : oddPolarFunction a = fun x => oddProfile a x / riemannKernelReal x :=
    funext (oddPolarFunction_eq_oddProfile_div a)
  rw [heq]
  exact (contDiff_oddProfile a).div contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne'

theorem contDiff_oddPolarWeight {n : ℕ∞} (a : ℝ) {w : ℝ → ℝ} (hw : ContDiff ℝ n w) :
    ContDiff ℝ n (oddPolarWeight a w) :=
  (contDiff_oddPolarFunction a).mul hw

/-- **Complete Divisor-Chain Variance Decomposition of `markovEnergy (oddProfileTest a w)`**:
for any `C²` compactly supported even profile `w`, the full Markov energy of `f(x) = m_a(x) w(x)`
decomposes into the nonnegative archimedean `Θ`-Doob jump energy, twice the nonnegative same-side
prime jump energy, and the countable sum of nonnegative bipartite divisor-chain variances
`∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q`, minus the `cosh(x / 2)` mass. -/
theorem oddProfileTest_markovEnergy_eq_chain_variances_sub_cosh (a : ℝ) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    markovEnergy (fun x => (oddProfileTest a w x : ℂ)) =
      phiDoobArchJumpEnergy (oddPolarWeight a w) +
        2 * sameSide (oddPolarWeight a w) +
        (∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q) -
        phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) := by
  have hfun : (fun x => (oddProfileTest a w x : ℂ)) =
      fun x => (phiDoobTest (oddPolarWeight a w) x : ℂ) := by
    funext x
    rw [phiDoobTest_oddPolarWeight_eq_oddProfileTest]
  have hs : sameSide (fun x => oddPolarWeight a w (-x)) = sameSide (oddPolarWeight a w) := by
    apply tsum_congr fun d => setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [phiDoobPrimeJump, oddPolarWeight_odd_of_even a heven]
    ring
  rw [hfun, doob_source_eq_chain_variances_sub_cosh
    (contDiff_oddPolarWeight a hw) (hasCompactSupport_oddPolarWeight a hwc), hs]
  ring

/-- **Reflected-Prime Collar Compensation Sum for `oddPolarWeight a w`**:
for any continuous compactly supported even `w`, the complete divisor-chain variance family
`chainIntegral (oddPolarWeight a w)` sums to the compensated reflected-prime series. -/
theorem oddPolarWeight_reflected_compensation_hasSum_chains (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    HasSum (chainIntegral (oddPolarWeight a w))
      (∑' d : ℕ, (vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        phiDoobCollarKillingDensity (oddPolarWeight a w) (Real.log d) x) -
          2 * CHMDReflectedPrime.reflectedDifference (oddPolarWeight a w) d)) :=
  reflected_compensation_hasSum_chains
    (continuous_oddPolarWeight a hw)
    (hasCompactSupport_oddPolarWeight a hwc)
    (oddPolarWeight_odd_of_even a heven)

/-! ## Section 3: Universal Origin-Crossing Collar Duality (`Θ`-Doob Crossing + `m_a`-Doob Collar Difference = Collar Mixed Pairing) -/

/-- **Fundamental Algebraic Origin-Crossing Collar Duality**:
at any origin-crossing pair with positive ground weights `ψ₁, ψ₂` and even profile values `w₁, w₂`,
the sum of the `Θ`-Doob crossing sum-of-values square `(ψ₁ w₁ + ψ₂ w₂)²` and the `m_a`-Doob
collar difference square `ψ₁ ψ₂ (w₁ - w₂)²` equals the ground-state collar mixed product
`(ψ₁ + ψ₂)(ψ₁ w₁² + ψ₂ w₂²)`. -/
theorem collar_sumSq_add_oddProfile_diffSq_eq_mixed (ψ₁ ψ₂ w₁ w₂ : ℝ) :
    (ψ₁ * w₁ + ψ₂ * w₂) ^ 2 + ψ₁ * ψ₂ * (w₁ - w₂) ^ 2 =
      (ψ₁ + ψ₂) * (ψ₁ * w₁ ^ 2 + ψ₂ * w₂ ^ 2) := by
  ring

/-- The ground-state collar mixed pairing density on `(0, t)`:
`oddProfileCollarMixed a w t x = Θ(x) Θ(t - x) (Ψ_a(x) + Ψ_a(t - x)) (Ψ_a(x) w(x)² + Ψ_a(t - x) w(t - x)²)`. -/
def oddProfileCollarMixed (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * riemannKernelReal (t - x) *
    (oddPolarFunction a x + oddPolarFunction a (t - x)) *
    (oddPolarFunction a x * w x ^ 2 + oddPolarFunction a (t - x) * w (t - x) ^ 2)

theorem oddProfileCollarMixed_nonneg {a t x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo (0 : ℝ) t) (w : ℝ → ℝ) :
    0 ≤ oddProfileCollarMixed a w t x := by
  unfold oddProfileCollarMixed
  have h1 : 0 < oddPolarFunction a x := oddPolarFunction_pos ha hx.1
  have h2 : 0 < oddPolarFunction a (t - x) := oddPolarFunction_pos ha (sub_pos.mpr hx.2)
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (riemannKernelReal_pos x).le (riemannKernelReal_pos (t - x)).le)
      (add_pos h1 h2).le)
    (add_nonneg (mul_nonneg h1.le (sq_nonneg _)) (mul_nonneg h2.le (sq_nonneg _)))

/-- **Pointwise Origin-Crossing Collar Duality (`phiDoobCollarSumSq + oddProfileCollarDiffSq = oddProfileCollarMixed`)**:
for every `a, t, x : ℝ` and `w : ℝ → ℝ`, the sum of the `Θ`-Doob collar sum-of-values density
`phiDoobCollarSumSq (oddPolarWeight a w) t x` and the `m_a`-Doob collar difference square
`oddProfileCollarDiffSq a w t x` equals `oddProfileCollarMixed a w t x`. -/
theorem phiDoobCollarSumSq_oddPolarWeight_add_oddProfileCollarDiffSq_eq (a : ℝ)
    (w : ℝ → ℝ) (t x : ℝ) :
    phiDoobCollarSumSq (oddPolarWeight a w) t x + oddProfileCollarDiffSq a w t x =
      oddProfileCollarMixed a w t x := by
  unfold phiDoobCollarSumSq oddPolarWeight oddProfileCollarDiffSq oddProfileCollarMixed
  have h1 : oddProfile a x = riemannKernelReal x * oddPolarFunction a x := by
    rw [oddPolarFunction_eq_oddProfile_div, mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']
  have h2 : oddProfile a (t - x) = riemannKernelReal (t - x) * oddPolarFunction a (t - x) := by
    rw [oddPolarFunction_eq_oddProfile_div, mul_div_cancel₀ _ (riemannKernelReal_pos (t - x)).ne']
  rw [h1, h2]
  ring

/-- For even `w`, `primeCrossing (oddPolarWeight a w) d` equals the `Θ`-Doob collar integral
`vonMangoldtAtom d * ∫_{x ∈ (0, log d)} phiDoobCollarSumSq (oddPolarWeight a w) (log d) x`. -/
theorem primeCrossing_oddPolarWeight_eq_collarSumSq (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) (d : ℕ) :
    primeCrossing (oddPolarWeight a w) d =
      vonMangoldtAtom d * ∫ x in Ioo (0 : ℝ) (Real.log d),
        phiDoobCollarSumSq (oddPolarWeight a w) (Real.log d) x := by
  set v := oddPolarWeight a w
  have hv : Continuous v := continuous_oddPolarWeight a hw
  have hvc : HasCompactSupport v := hasCompactSupport_oddPolarWeight a hwc
  have hodd : ∀ x, v (-x) = -v x := oddPolarWeight_odd_of_even a heven
  have hj (x : ℝ) : phiDoobPrimeJump (fun y => v (-y)) d x = phiDoobPrimeJump v d x := by
    simp only [phiDoobPrimeJump, hodd]
    ring
  have hs := integral_primeJump_split hv hvc d
  simp_rw [hj] at hs
  have hf := integral_phiDoobPrimeJump_eq_halfLine_of_odd hv hvc hodd d
  change (∫ x, phiDoobPrimeJump v d x) =
    2 * (∫ x in Ioi (0 : ℝ), phiDoobPrimeJump v d x) +
      vonMangoldtAtom d * ∫ x in Ioo (0 : ℝ) (Real.log d),
        phiDoobCollarSumSq v (Real.log d) x at hf
  linarith

/-- **Per-Prime Crossing + Odd-Profile Collar Duality**:
for any continuous compactly supported even `w` and any `d : ℕ`, adding the `m_a`-Doob prime
collar difference integral to the `Θ`-Doob crossing energy `primeCrossing (oddPolarWeight a w) d`
yields the exact ground-state collar mixed integral. -/
theorem primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) (d : ℕ) :
    primeCrossing (oddPolarWeight a w) d +
        vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
          oddProfileCollarDiffSq a w (Real.log d) x) =
      vonMangoldtAtom d * ∫ x in Ioo (0 : ℝ) (Real.log d),
        oddProfileCollarMixed a w (Real.log d) x := by
  rw [primeCrossing_oddPolarWeight_eq_collarSumSq a hw hwc heven d, ← mul_add]
  congr 1
  have h1 : IntegrableOn (phiDoobCollarSumSq (oddPolarWeight a w) (Real.log d))
      (Ioo (0 : ℝ) (Real.log d)) := by
    unfold phiDoobCollarSumSq
    have hv := continuous_oddPolarWeight a hw
    exact ((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      ((hv.add (hv.comp (continuous_const.sub continuous_id))).pow 2)).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
  have h2 : IntegrableOn (oddProfileCollarDiffSq a w (Real.log d))
      (Ioo (0 : ℝ) (Real.log d)) := by
    unfold oddProfileCollarDiffSq
    exact (((continuous_oddProfile a).mul
      ((continuous_oddProfile a).comp (continuous_const.sub continuous_id))).mul
      ((hw.sub (hw.comp (continuous_const.sub continuous_id))).pow 2)).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
  rw [← integral_add h1 h2]
  exact setIntegral_congr_fun measurableSet_Ioo fun x _ =>
    phiDoobCollarSumSq_oddPolarWeight_add_oddProfileCollarDiffSq_eq a w (Real.log d) x

/-! ## Section 4: Short-Support / Reflection-Symmetric Collar Vanishing and Convex Gauge Interpolation -/

/-- **Exact Vanishing of the `m_a`-Doob Collar Integral Under Midpoint Symmetry**:
whenever `w(t - x) = w(x)` for all `x ∈ (0, t)` (in particular, if `w` is constant on `(0, t)` or
if `supp(w) ∩ (0, t) = ∅`), the negative `m_a`-Doob collar integral vanishes identically. -/
theorem integral_oddProfileCollarDiffSq_eq_zero_of_symmetric (a : ℝ) {w : ℝ → ℝ} {t : ℝ}
    (hsym : ∀ x ∈ Ioo (0 : ℝ) t, w (t - x) = w x) :
    (∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
  unfold oddProfileCollarDiffSq
  rw [hsym x hx, sub_self, sq, mul_zero, mul_zero]

/-- **Full-Line Nonnegativity of `oddProfileShiftJump` Under Collar Symmetry**:
if `a > 0`, `t ≥ 0`, `w` is even, continuous, compactly supported, and satisfies `w(t - x) = w(x)`
on `(0, t)`, then the full-line shift jump equals twice the half-line shift jump and is nonnegative. -/
theorem integral_oddProfileShiftJump_nonneg_of_collar_symmetric {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsym : ∀ x ∈ Ioo (0 : ℝ) t, w (t - x) = w x) :
    0 ≤ ∫ x : ℝ, oddProfileShiftJump a w t x := by
  rw [integral_oddProfileShiftJump_eq_halfLine_of_even a hw hwc heven ht]
  have hcol : (∫ x in Ioo (0 : ℝ) t,
      oddProfile a x * oddProfile a (t - x) * (w x - w (t - x)) ^ 2) =
      ∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x := rfl
  rw [hcol, integral_oddProfileCollarDiffSq_eq_zero_of_symmetric a hsym, sub_zero]
  exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun x hx =>
    oddProfileShiftJump_nonneg_of_pos ha (mem_Ioi.mp hx) ht w)

/-- **Convex Gauge Interpolation Between `Θ`-Doob Divisor-Chain Variances and the `m_a`-Doob `sinh` Potential**:
for any `θ : ℝ` and any `C²` compactly supported even `w`, rewriting `markovEnergy (oddProfileTest a w)`
by adding and subtracting `θ` times the odd polar ground-state pairing
`sourcePair (oddPolarVectorAt a ha) p = 2 ∫_{x > 0} m_a(x) sinh(x / 2) w(x)² dx` combines the
nonnegative divisor-chain variance sum `∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q`
with `+2 θ ∫_{x > 0} m_a(x) sinh(x / 2) w(x)² dx`. -/
theorem convex_doob_chain_sinh_interpolation {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (θ : ℝ)
    {p : SourceGraph} {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv (oddProfileTest a (fun y => w y ^ 2))) :
    markovEnergy (fun x => (oddProfileTest a w x : ℂ)) =
      phiDoobArchJumpEnergy (oddPolarWeight a w) +
        2 * sameSide (oddPolarWeight a w) +
        (∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q) +
        2 * θ * (∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2) -
        (phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) +
          θ * sourcePair (oddPolarVectorAt a ha) p) := by
  rw [oddProfileTest_markovEnergy_eq_chain_variances_sub_cosh a hw hwc heven,
    sourcePair_oddPolarVectorAt_oddProfileTest_sq hane ha hw.continuous hwc heven hp]
  ring

end RHTower.CHMDPolar
