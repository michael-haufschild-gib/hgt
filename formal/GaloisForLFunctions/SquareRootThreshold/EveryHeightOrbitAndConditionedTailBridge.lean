import GaloisForLFunctions.SquareRootThreshold.PrimeTailCouplingCriterion
import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneZeroWidth
import GaloisForLFunctions.RHTower.HeadConditionedRoughDecoupling

/-!
# Every-Height Orbit Recurrence and the Head-Conditioned Prime-Tail Bridge

This module resolves Research Topic 7 of the Square-Root Threshold programme by establishing the
exact bridge between the Bagchi/Voronin vertical-shift orbit lane (`τ ↦ ζ(· + iτ)` on closed discs
of the right half-strip `1/2 < Re s < 1`) and the localized Weil explicit formula (`W_ζ(S_ξ f, S_ξ f)
= A_f(ξ) − Π_f(ξ)` at height `2πξ`), together with the smooth–rough decomposition of the prime-side
Dirichlet polynomial under head-conditioned decoupling (`HeadConditionedRoughDecoupling`):

1. **Pointwise disc recurrence at every height vs. the coupled prime–archimedean criterion and the
   one-parameter lag family** (`forall_strip_exists_zetaDiscStronglyRecurrentOn_iff_riemannHypothesis`,
   `forall_strip_exists_zetaDiscStronglyRecurrentOn_iff_primePolynomial_le_archPart`,
   `forall_strip_exists_zetaDiscStronglyRecurrentOn_iff_poleCompression`,
   `forall_right_exists_zetaDiscStronglyRecurrentOn_iff_lag_primeWindow_ge_neg_exp`):
   A point `z₀` in `1/2 < Re z₀ < 1` carries a strongly recurrent closed disc iff `ζ(z₀) ≠ 0`
   (`exists_zetaDiscStronglyRecurrentOn_iff_ne_zero`). Consequently, strong disc recurrence at
   every point of `1/2 < Re z₀ < 1` is equivalent to `RiemannHypothesis`, to the coupled explicit-
   formula inequality `Re Π_f(ξ) ≤ Re A_f(ξ)` at every aperture and height, and to the rank-two
   pole compression `|ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a`; at width `σ ≥ 0`, strong disc
   recurrence right of `1/2 + σ` is equivalent to the one-parameter lag bound
   `Re P_{w,v} ≥ −C e^{σv}`.

2. **Unconditional recurrence modulo the local zero divisor and the self-return dichotomy**
   (`every_strip_point_recurrence_and_dichotomy`,
   `every_vertical_line_full_measure_recurrence_and_bad_height_bound`):
   At every point `z₀` in `1/2 < Re z₀ < 1`, without any zero-free premise, `ζ` factors on a
   closed disc `closedBall z₀ r` as `(∏_{u ∈ S} (z − u)^{D(u)}) g(z)` with `g` nonvanishing, and
   both `ζ(· + iτ)` and all large Dirichlet heads `∑_{n ≤ M} n^{−z−iτ}` return to `g` at positive
   lower density of heights (`exists_zeta_recurrence_modulo_zeros`,
   `exists_uniform_pos_density_headTarget_cofactor`). Either `ζ(z₀) ≠ 0` and `z₀` carries a
   strongly recurrent disc for `ζ` itself, or `ζ(z₀) = 0` belongs to the local divisor `S` with
   `|Re z₀ − 1/2| ≤ zetaZeroWidth` while self-returns around `z₀` fail. On every vertical line
   `Re z = σ ∈ (1/2, 1)`, all but countably many heights (hence full measure `T` on `[0, T]`)
   carry a strongly recurrent disc, while on the explicit-formula side the bad heights with
   `Re W_ζ(S_ξ f, S_ξ f) < 0` have measure `O((log X / log T)²)`.

3. **Smooth–rough decomposition of the prime polynomial and head-conditioned rough decoupling**
   (`smoothPrimeIndexSet`, `roughPrimeIndexSet`, `primePolynomial_eq_smooth_add_rough`,
   `primeVariance_eq_smooth_add_rough`, `le_minFac_of_mem_roughPrimeIndexSet`,
   `roughPrimeIndexSet_eq_empty_of_lt`, `roughPrimePolynomial_eq_zero_of_lt`,
   `tendsto_primeReturnKernel_weighted_roughPosPrime_meanSquare`,
   `norm_integral_primeReturnKernel_mul_roughPosPrime_sub_diag_le`,
   `le_setIntegral_primeReturnKernel_goodHeights_roughPosPrime`):
   Splitting `[2, N]` at a prime cutoff `y` decomposes `primePolynomial f N` into its `y`-smooth
   head `smoothPrimePolynomial f y N` and its `y`-rough tail `roughPrimePolynomial f y N`. Every
   `m ∈ roughPrimeIndexSet y N` satisfies `y ≤ m.minFac ≤ m`: when `N < y` the rough tail vanishes
   identically (`roughPrimePolynomial_eq_zero_of_lt`), whereas once `N ≥ y` exceeds the head
   cutoff, conditioning the height `τ` by `primeReturnKernel P τ` for any `P ⊆ Nat.primesBelow y`
   leaves the rough positive-frequency polynomial's mean square unchanged (`roughPosPrimeVariance`),
   with an effective horizon-free bracket error and at least `(1 − 1/λ)` of the return kernel's
   mass sitting at heights where the rough polynomial stays below `λ` times its diagonal variance.

4. **Bandwidth-zero strip damping vs. critical-line variance persistence**
   (`rough_strip_variance_le_rpow_neg_mul_roughPosPrimeVariance`):
   On `roughPrimeIndexSet y N` (`y ≥ 1`), weighting the rough coefficients by `m^{−δ}` (`δ ≥ 0`,
   corresponding to `Re s = 1/2 + δ` in the strip) contracts the rough variance by at least
   `y^{−2δ}`. For `δ > 0` (the fixed-disc orbit regime) the tail variance decays as `y^{−2δ} → 0`
   with the head cutoff `y`, whereas on the critical line `δ = 0` (the localized explicit-formula
   regime) `y^{−2δ} = 1` and the `y`-rough prime tail retains its full unweighted variance.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real BigOperators ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ## 1. Pointwise disc recurrence vs. the coupled explicit-formula and lag criteria -/

/-- **Pointwise disc recurrence at every point of the strip is equivalent to RH.** Every point `z₀`
in `1/2 < Re z₀ < 1` carries a closed disc on which `ζ` is strongly recurrent if and only if
`RiemannHypothesis` holds. -/
theorem forall_strip_exists_zetaDiscStronglyRecurrentOn_iff_riemannHypothesis :
    (∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z r)) ↔ RiemannHypothesis := by
  have h0 := zetaZeroWidth_le_iff_forall_exists_zetaDiscStronglyRecurrentOn (σ := 0) le_rfl
  simp only [add_zero] at h0
  have heq : zetaZeroWidth = 0 ↔ zetaZeroWidth ≤ 0 :=
    ⟨fun h => h.le, fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  exact h0.symm.trans (heq.symm.trans riemannHypothesis_iff_zetaZeroWidth_eq_zero.symm)

/-- **Orbit–explicit-formula equivalence.** Pointwise strong disc recurrence of `ζ` at every point
of the strip `1/2 < Re z < 1` is equivalent to the coupled localized explicit-formula inequality
`Re Π_f(ξ) ≤ Re A_f(ξ)` at every aperture `a`, profile `f`, and height `ξ`. -/
theorem forall_strip_exists_zetaDiscStronglyRecurrentOn_iff_primePolynomial_le_archPart :
    (∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z r)) ↔
    (∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      ∀ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ (archPart f ξ).re) :=
  forall_strip_exists_zetaDiscStronglyRecurrentOn_iff_riemannHypothesis.trans
    riemannHypothesis_iff_primePolynomial_le_archPart

/-- **Orbit–pole-compression equivalence.** Pointwise strong disc recurrence of `ζ` at every point
of the strip `1/2 < Re z < 1` is equivalent to the rank-two `2 × 2` prime–Gamma pole compression
`|ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a` at every positive aperture. -/
theorem forall_strip_exists_zetaDiscStronglyRecurrentOn_iff_poleCompression :
    (∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z r)) ↔
    (∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) :=
  forall_strip_exists_zetaDiscStronglyRecurrentOn_iff_primePolynomial_le_archPart.trans
    primePolynomial_le_archPart_iff_poleCompression

/-- **Width-`σ` disc recurrence vs. one-parameter lag growth.** For all but countably many widths
`w ∈ (0, ½ log 2)` and every `σ ≥ 0`, every point `z` with `1/2 + σ < Re z < 1` carries a strongly
recurrent closed disc if and only if the one-parameter prime-window functional satisfies
`Re P_{w,v} ≥ −C e^{σv}` for all large lags `v`. -/
theorem forall_right_exists_zetaDiscStronglyRecurrentOn_iff_lag_primeWindow_ge_neg_exp :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E → ∀ σ : ℝ, 0 ≤ σ →
      ((∀ z : ℂ, 1 / 2 + σ < z.re → z.re < 1 →
          ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z r)) ↔
        ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
          (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
            (twoBump (modScaledBump w 0) v (-1)))).re) := by
  obtain ⟨E, hE, hlaw⟩ := zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp
  refine ⟨E, hE, fun w hw hw2 hwE σ hσ => ?_⟩
  exact (zetaZeroWidth_le_iff_forall_exists_zetaDiscStronglyRecurrentOn hσ).symm.trans
    (hlaw w hw hw2 hwE σ hσ)

/-! ## 2. Unconditional recurrence modulo the local zero divisor and the self-return dichotomy -/

/-- **Unconditional cofactor recurrence and self-return dichotomy at every point of the strip.**
At every `z₀` with `1/2 < Re z₀ < 1`:
1. Without any zero-free hypothesis, `ζ` factors on a closed disc `closedBall z₀ r` (`r > 0`) as
   `ζ(z) = (∏_{u ∈ S} (z − u)^{D(u)}) g(z)` with `g` nonvanishing, and for every `ε > 0` both the
   shifts `ζ(· + iτ)` and all large Dirichlet heads `∑_{n ≤ M} n^{−z−iτ}` return within `ε` of the
   zero-erased cofactor `g` on `closedBall z₀ r` at positive lower density of heights.
2. Either `ζ(z₀) ≠ 0` and `z₀` carries a strongly recurrent closed disc for `ζ` itself, or
   `ζ(z₀) = 0` is an off-line zero in `zetaZeroConfig.carrier` with `0 < z₀.re - 1/2 ≤ zetaZeroWidth`
   for which self-returns fail (`¬ ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall z₀ r)`). -/
theorem every_strip_point_recurrence_and_dichotomy {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) :
    (∃ r > 0, ∃ (S : Finset ℂ) (D : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ u ∈ S, riemannZeta u = 0 ∧ 1 ≤ D u) ∧
      (∀ z ∈ Metric.closedBall z₀ r, g z ≠ 0 ∧
        riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z) ∧
      ∀ ε > 0, ∃ c > 0, ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
        ENNReal.ofReal (c * T) ≤ volume ({τ : ℝ | ∀ z ∈ Metric.closedBall z₀ r,
          ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - g z‖ < ε} ∩ Icc 0 T)) ∧
    ((riemannZeta z₀ ≠ 0 ∧ ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z₀ r)) ∨
      (riemannZeta z₀ = 0 ∧ z₀ ∈ zetaZeroConfig.carrier ∧ z₀.re - 1 / 2 ≤ zetaZeroWidth ∧
        ¬ ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z₀ r))) := by
  refine ⟨exists_uniform_pos_density_headTarget_cofactor h1 h2, ?_⟩
  by_cases hz : riemannZeta z₀ = 0
  · right
    have hmem : z₀ ∈ zetaZeroConfig.carrier :=
      show IsNontrivialZero z₀ from ⟨hz, by linarith, h2⟩
    have hw : z₀.re - 1 / 2 ≤ zetaZeroWidth :=
      (le_abs_self _).trans (abs_re_sub_half_le_zetaZeroWidth hmem)
    have hnot : ¬ ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z₀ r) := by
      intro hrec
      exact (exists_zetaDiscStronglyRecurrentOn_iff_ne_zero h1 h2).mp hrec hz
    exact ⟨hz, hmem, hw, hnot⟩
  · left
    exact ⟨hz, (exists_zetaDiscStronglyRecurrentOn_iff_ne_zero h1 h2).mpr hz⟩

/-- **Unconditional vertical-line full-measure recurrence and explicit-formula bad-height bound.**
On every vertical line `Re z = σ ∈ (1/2, 1)` and height window `[0, T₀]`, the heights `t ∈ [0, T₀]`
carrying a strongly recurrent closed disc about `σ + it` have full measure `T₀` (with countable
complement), while for every `C²` test `f` of aperture `a ≥ 0` and window `η` of aperture `r` in
the sub-threshold regime `2r e^{2a} ≤ 1`, the heights in `U` where `Re A_f(ξ + ξ₀) ≥ A₀ > 0` and
`Re W_ζ(S_{ξ+ξ₀} f, S_{ξ+ξ₀} f) < 0` carry window weight at most `‖η‖² V_f / A₀²`. -/
theorem every_vertical_line_full_measure_recurrence_and_bad_height_bound {σ : ℝ}
    (h1 : 1 / 2 < σ) (h2 : σ < 1) (T₀ : ℝ) :
    {t : ℝ | ¬ ∃ r > 0,
      ZetaDiscStronglyRecurrentOn (Metric.closedBall ((σ : ℂ) + t * I) r)}.Countable ∧
    volume ({t : ℝ | ∃ r > 0,
      ZetaDiscStronglyRecurrentOn (Metric.closedBall ((σ : ℂ) + t * I) r)} ∩ Icc 0 T₀) =
      ENNReal.ofReal T₀ ∧
    ∀ {a r A₀ : ℝ} {f η : ℝ → ℂ} {U : Set ℝ} (ξ₀ : ℝ),
      0 ≤ a → ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      ContDiff ℝ 2 η → tsupport η ⊆ Icc (-r) r → 2 * r * Real.exp (2 * a) ≤ 1 →
      0 < A₀ → (∀ ξ ∈ U, A₀ ≤ (archPart f (ξ + ξ₀)).re) →
      ∫⁻ ξ, (U ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
          (heightShift (ξ + ξ₀) f)).re < 0}).indicator
          (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
        ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ / A₀ ^ 2) :=
  ⟨countable_setOf_not_exists_zetaDiscStronglyRecurrentOn h1 h2,
    volume_setOf_exists_zetaDiscStronglyRecurrentOn_inter_Icc h1 h2 T₀,
    fun ξ₀ ha hf hfs hη hηs hX hA₀ hU =>
      lintegral_bad_heights_le ha hf hfs hη hηs hX ξ₀ hA₀ hU⟩

/-! ## 3. Smooth–rough decomposition of the prime-side Dirichlet polynomial -/

/-- The `y`-rough index set in `[2, N]`: integers `m ∈ [2, N]` divisible by no prime `< y`. -/
def roughPrimeIndexSet (y N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun m => ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m

/-- The `y`-smooth-divisible head index set in `[2, N]`: integers `m ∈ [2, N]` having at least one
prime factor `< y`. -/
def smoothPrimeIndexSet (y N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun m => ¬ ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m

theorem mem_roughPrimeIndexSet {y N m : ℕ} :
    m ∈ roughPrimeIndexSet y N ↔ (2 ≤ m ∧ m ≤ N) ∧ ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m := by
  simp [roughPrimeIndexSet, Finset.mem_filter, Finset.mem_Icc]

theorem two_le_of_mem_roughPrimeIndexSet {y N m : ℕ} (hm : m ∈ roughPrimeIndexSet y N) :
    2 ≤ m :=
  (mem_roughPrimeIndexSet.mp hm).1.1

theorem ne_zero_of_mem_roughPrimeIndexSet {y N m : ℕ} (hm : m ∈ roughPrimeIndexSet y N) :
    m ≠ 0 := by
  have := two_le_of_mem_roughPrimeIndexSet hm
  omega

theorem not_dvd_of_mem_roughPrimeIndexSet {y N m : ℕ} (hm : m ∈ roughPrimeIndexSet y N) :
    ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m :=
  (mem_roughPrimeIndexSet.mp hm).2

/-- **Every element of `roughPrimeIndexSet y N` has least prime factor `≥ y`, hence `m ≥ y`.** -/
theorem le_minFac_of_mem_roughPrimeIndexSet {y N m : ℕ} (hm : m ∈ roughPrimeIndexSet y N) :
    y ≤ m.minFac := by
  obtain ⟨⟨hm2, -⟩, hnd⟩ := mem_roughPrimeIndexSet.mp hm
  by_contra hlt
  have hlt' : m.minFac < y := not_le.mp hlt
  have hprime : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hmem : m.minFac ∈ Nat.primesBelow y := Nat.mem_primesBelow.mpr ⟨hlt', hprime⟩
  exact hnd m.minFac hmem (Nat.minFac_dvd m)

theorem le_of_mem_roughPrimeIndexSet {y N m : ℕ} (hm : m ∈ roughPrimeIndexSet y N) :
    y ≤ m := by
  have h2 := two_le_of_mem_roughPrimeIndexSet hm
  exact (le_minFac_of_mem_roughPrimeIndexSet hm).trans (Nat.minFac_le (by omega))

/-- **Below the head cutoff `y`, the `y`-rough index set is empty.** -/
theorem roughPrimeIndexSet_eq_empty_of_lt {y N : ℕ} (hNy : N < y) :
    roughPrimeIndexSet y N = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  have h1 := le_of_mem_roughPrimeIndexSet hm
  have h2 := (mem_roughPrimeIndexSet.mp hm).1.2
  omega

/-- **Every prime `p ∈ [max 2 y, N]` belongs to `roughPrimeIndexSet y N`.** -/
theorem mem_roughPrimeIndexSet_of_prime {y N p : ℕ} (hp : p.Prime) (hyp : y ≤ p) (hpN : p ≤ N) :
    p ∈ roughPrimeIndexSet y N := by
  rw [mem_roughPrimeIndexSet]
  refine ⟨⟨hp.two_le, hpN⟩, fun q hq hqp => ?_⟩
  rw [Nat.mem_primesBelow] at hq
  rcases hp.eq_one_or_self_of_dvd q hqp with rfl | rfl
  · exact hq.2.ne_one rfl
  · omega

theorem disjoint_smoothPrimeIndexSet_roughPrimeIndexSet (y N : ℕ) :
    Disjoint (smoothPrimeIndexSet y N) (roughPrimeIndexSet y N) := by
  rw [smoothPrimeIndexSet, roughPrimeIndexSet]
  exact Finset.disjoint_filter.mpr fun _ _ h1 h2 => h1 h2

theorem smoothPrimeIndexSet_union_roughPrimeIndexSet (y N : ℕ) :
    smoothPrimeIndexSet y N ∪ roughPrimeIndexSet y N = Finset.Icc 2 N := by
  rw [smoothPrimeIndexSet, roughPrimeIndexSet, Finset.union_comm]
  exact Finset.filter_union_filter_not_eq _ _

/-- The `y`-smooth-divisible head part of `primePolynomial f N`. -/
def smoothPrimePolynomial (f : ℝ → ℂ) (y N : ℕ) (ξ : ℝ) : ℂ :=
  expSum (smoothPrimeIndexSet y N ×ˢ (Finset.univ : Finset Bool)) (primeCoeff f) primeFreq ξ

/-- The `y`-rough tail part of `primePolynomial f N`. -/
def roughPrimePolynomial (f : ℝ → ℂ) (y N : ℕ) (ξ : ℝ) : ℂ :=
  expSum (roughPrimeIndexSet y N ×ˢ (Finset.univ : Finset Bool)) (primeCoeff f) primeFreq ξ

/-- The diagonal energy of `smoothPrimePolynomial f y N`. -/
def smoothPrimeVariance (f : ℝ → ℂ) (y N : ℕ) : ℝ :=
  ∑ n ∈ smoothPrimeIndexSet y N, (ArithmeticFunction.vonMangoldt n) ^ 2 / n *
    (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)

/-- The diagonal energy of `roughPrimePolynomial f y N`. -/
def roughPrimeVariance (f : ℝ → ℂ) (y N : ℕ) : ℝ :=
  ∑ n ∈ roughPrimeIndexSet y N, (ArithmeticFunction.vonMangoldt n) ^ 2 / n *
    (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)

/-- **Head–tail decomposition of `primePolynomial`.** At any head cutoff `y`, `primePolynomial f N`
is the sum of `smoothPrimePolynomial f y N` and `roughPrimePolynomial f y N`. -/
theorem primePolynomial_eq_smooth_add_rough (f : ℝ → ℂ) (y N : ℕ) (ξ : ℝ) :
    primePolynomial f N ξ = smoothPrimePolynomial f y N ξ + roughPrimePolynomial f y N ξ := by
  unfold primePolynomial smoothPrimePolynomial roughPrimePolynomial expSum
  have hdisj : Disjoint (smoothPrimeIndexSet y N ×ˢ (Finset.univ : Finset Bool))
      (roughPrimeIndexSet y N ×ˢ (Finset.univ : Finset Bool)) :=
    Finset.disjoint_product.mpr (Or.inl (disjoint_smoothPrimeIndexSet_roughPrimeIndexSet y N))
  rw [← Finset.sum_union hdisj, ← Finset.union_product,
    smoothPrimeIndexSet_union_roughPrimeIndexSet]

/-- **Head–tail decomposition of `primeVariance`.** -/
theorem primeVariance_eq_smooth_add_rough (f : ℝ → ℂ) (y N : ℕ) :
    primeVariance f N = smoothPrimeVariance f y N + roughPrimeVariance f y N := by
  unfold primeVariance smoothPrimeVariance roughPrimeVariance
  rw [← Finset.sum_union (disjoint_smoothPrimeIndexSet_roughPrimeIndexSet y N),
    smoothPrimeIndexSet_union_roughPrimeIndexSet]

/-- **When the prime cutoff `N` lies below the head cutoff `y`, the rough tail vanishes.** -/
theorem roughPrimePolynomial_eq_zero_of_lt (f : ℝ → ℂ) {y N : ℕ} (hNy : N < y) (ξ : ℝ) :
    roughPrimePolynomial f y N ξ = 0 := by
  simp [roughPrimePolynomial, expSum, roughPrimeIndexSet_eq_empty_of_lt hNy]

theorem primePolynomial_eq_smoothPrimePolynomial_of_lt (f : ℝ → ℂ) {y N : ℕ} (hNy : N < y)
    (ξ : ℝ) :
    primePolynomial f N ξ = smoothPrimePolynomial f y N ξ := by
  rw [primePolynomial_eq_smooth_add_rough f y N ξ, roughPrimePolynomial_eq_zero_of_lt f hNy ξ,
    add_zero]

/-! ## 4. Head-conditioned decoupling of the `y`-rough prime-power tail and strip damping -/

/-- The positive-frequency prime-power coefficient `(Λ(m)/√m) k_f(log m)`. -/
def posPrimeCoeff (f : ℝ → ℂ) (m : ℕ) : ℂ :=
  primeCoeff f (m, true)

/-- The `y`-rough positive-frequency prime-power Dirichlet polynomial on the height line `τ`:
`Σ_{m ∈ roughPrimeIndexSet y N} (Λ(m)/√m) k_f(log m) m^{iτ}`. -/
def roughPosPrimePoly (f : ℝ → ℂ) (y N : ℕ) (τ : ℝ) : ℂ :=
  integerHeightPoly (roughPrimeIndexSet y N) (posPrimeCoeff f) τ

/-- The diagonal energy of `roughPosPrimePoly f y N`. -/
def roughPosPrimeVariance (f : ℝ → ℂ) (y N : ℕ) : ℝ :=
  ∑ m ∈ roughPrimeIndexSet y N, ‖posPrimeCoeff f m‖ ^ 2

theorem roughPosPrimeVariance_le_roughPrimeVariance (f : ℝ → ℂ) (y N : ℕ) :
    roughPosPrimeVariance f y N ≤ roughPrimeVariance f y N := by
  unfold roughPosPrimeVariance roughPrimeVariance posPrimeCoeff
  refine Finset.sum_le_sum fun m _ => ?_
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  simp only [primeCoeff, primeFreq, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, div_pow, Real.sq_sqrt hm0]
  have hnn : 0 ≤ (ArithmeticFunction.vonMangoldt m) ^ 2 / (m : ℝ) *
      ‖EF.weilTest f f (-Real.log m)‖ ^ 2 := by positivity
  linarith

/-- **Head-conditioned decoupling of the `y`-rough prime-power polynomial.** For any finite set
`P` of primes below `y`, weighting the height `τ` by `primeReturnKernel P τ` leaves the mean
square of `roughPosPrimePoly f y N` unchanged: as `T → ∞`, the return-kernel-weighted mean square
converges to `roughPosPrimeVariance f y N`. -/
theorem tendsto_primeReturnKernel_weighted_roughPosPrime_meanSquare {y N : ℕ} {P : Finset ℕ}
    (f : ℝ → ℂ) (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y) :
    Tendsto (fun T : ℝ =>
        (∫ τ in (0 : ℝ)..T, primeReturnKernel P τ * ‖roughPosPrimePoly f y N τ‖ ^ 2) /
          (∫ τ in (0 : ℝ)..T, primeReturnKernel P τ))
      atTop (𝓝 (roughPosPrimeVariance f y N)) :=
  tendsto_primeReturnKernel_weighted_roughMeanSquare hP
    (fun _ hm => ne_zero_of_mem_roughPrimeIndexSet hm)
    (fun _ hm => not_dvd_of_mem_roughPrimeIndexSet hm)

/-- **Effective return-kernel bracket for the `y`-rough prime-power polynomial.** -/
theorem norm_integral_primeReturnKernel_mul_roughPosPrime_sub_diag_le {y N : ℕ} {P : Finset ℕ}
    (f : ℝ → ℂ) (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y) (T : ℝ) :
    |(∫ τ in (0 : ℝ)..T, primeReturnKernel P τ * ‖roughPosPrimePoly f y N τ‖ ^ 2)
        - T * ((2 : ℝ) ^ P.card * roughPosPrimeVariance f y N)|
      ≤ 4 * (returnKernelCutoff P (roughPrimeIndexSet y N) : ℝ) *
          (1 + Real.log (returnKernelCutoff P (roughPrimeIndexSet y N))) *
          ((2 : ℝ) ^ P.card * roughPosPrimeVariance f y N) :=
  norm_integral_primeReturnKernel_mul_rough_sub_diag_le hP
    (fun _ hm => ne_zero_of_mem_roughPrimeIndexSet hm)
    (fun _ hm => not_dvd_of_mem_roughPrimeIndexSet hm) T

/-- **Return and smallness of the `y`-rough prime-power polynomial.** For every `P ⊆ primesBelow y`
and `λ > 0`, the heights in `(0, T]` where `‖roughPosPrimePoly f y N τ‖² < λ · roughPosPrimeVariance f y N`
carry at least `((T − C) − (T + C)/λ) 2^{|P|}` of the return kernel's mass, where `C` is the
horizon-free decoupling cutoff error. -/
theorem le_setIntegral_primeReturnKernel_goodHeights_roughPosPrime {y N : ℕ} {P : Finset ℕ}
    {f : ℝ → ℂ} (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y)
    (hvar : 0 < roughPosPrimeVariance f y N) {lam T : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) :
    (T - 4 * (returnKernelCutoff P (roughPrimeIndexSet y N) : ℝ) *
          (1 + Real.log (returnKernelCutoff P (roughPrimeIndexSet y N)))) * (2 : ℝ) ^ P.card
        - (T + 4 * (returnKernelCutoff P (roughPrimeIndexSet y N) : ℝ) *
            (1 + Real.log (returnKernelCutoff P (roughPrimeIndexSet y N)))) *
            (2 : ℝ) ^ P.card / lam
      ≤ ∫ τ in {σ : ℝ | ‖roughPosPrimePoly f y N σ‖ ^ 2 < lam * roughPosPrimeVariance f y N} ∩
          Set.Ioc 0 T, primeReturnKernel P τ :=
  le_setIntegral_primeReturnKernel_goodHeights hP
    (fun _ hm => ne_zero_of_mem_roughPrimeIndexSet hm)
    (fun _ hm => not_dvd_of_mem_roughPrimeIndexSet hm) hvar hlam hT

/-- **Bandwidth-zero strip damping vs. critical-line rough variance persistence.**
For `1 ≤ y` and `0 ≤ δ`, every `m ∈ roughPrimeIndexSet y N` satisfies `y ≤ m`, so weighting the
rough coefficients by `m^{−δ}` (corresponding to `Re s = 1/2 + δ` in the strip) contracts the
rough variance by at least `y^{−2δ}`:
`Σ_{m ∈ roughPrimeIndexSet y N} m^{−2δ} ‖posPrimeCoeff f m‖² ≤ y^{−2δ} roughPosPrimeVariance f y N`.
In the fixed-disc orbit regime (`δ > 0`) this factor decays as `y^{−2δ} → 0` with the head cutoff
`y`, whereas on the critical line (`δ = 0`, the localized explicit-formula regime) `y^{−2δ} = 1`
and the rough prime tail retains its full unweighted variance. -/
theorem rough_strip_variance_le_rpow_neg_mul_roughPosPrimeVariance (f : ℝ → ℂ) {y N : ℕ}
    (hy : 1 ≤ y) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑ m ∈ roughPrimeIndexSet y N, (m : ℝ) ^ (-(2 * δ)) * ‖posPrimeCoeff f m‖ ^ 2 ≤
      (y : ℝ) ^ (-(2 * δ)) * roughPosPrimeVariance f y N := by
  rw [roughPosPrimeVariance, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hym : (y : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_mem_roughPrimeIndexSet hm
  have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := hy0.le.trans hym
  have hpow : (m : ℝ) ^ (-(2 * δ)) ≤ (y : ℝ) ^ (-(2 * δ)) := by
    rw [Real.rpow_neg hm0, Real.rpow_neg hy0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hy0 (2 * δ))
      (Real.rpow_le_rpow hy0.le hym (by linarith))
  exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)

end GaloisForLFunctions.SquareRootThreshold
