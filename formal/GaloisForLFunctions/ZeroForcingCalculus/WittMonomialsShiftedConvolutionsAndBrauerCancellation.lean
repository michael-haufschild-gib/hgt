import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyZeroCascade
import GaloisForLFunctions.RHTower.Artin.ArtinClassFunctionInduction
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.EveryRulerCarriesTheSeedAndEveryLever

/-!
# Witt monomials, the squarefree ruler, shifted convolutions, and Brauer cancellation

This module formalizes the three structural obstructions to unconditional zero forcing from rational
Euler-product identities, shifted Rankin–Selberg convolutions, and Brauer virtual permutation
relations, together with the exact positive ruler salvaged from the squarefree Euler ratio:

1. **Witt Euler-product monomials** (`wittZetaMonomial`, `meromorphicOrderAt_wittZetaMonomial`,
   `meromorphicOrderAt_wittZetaMonomial_of_half_lt_re`):
   Every finite rational identity `∏_{j=1}^K (1 - X^j)^{-e_j}` in `1 + X ℚ[[X]]` specializes at
   `X = p^{-s}` to the Witt monomial `W_e(s) = ∏_{j=1}^K ζ(j s)^{e_j}`. Globally on `ℂ`,
   `ord_s W_e = ∑_{j=1}^K e_j ord_{j s} ζ`. At any `ρ` with `Re ρ > 1/2`, every dilated point
   `j ρ` (`j ≥ 2`) lies strictly inside the Euler-product half-plane `Re w > 1`, so
   `ord_ρ W_e = e_1 ord_ρ ζ`: higher Witt factors cannot cancel an off-line zero at `s = ρ`, and at
   `s = ρ / k` (`k ≥ 2`) cancellation requires assuming `W_e` is pole-free across `Re s > Re ρ / k`.

2. **The unconditional `[1/2, 9/16)` squarefree pole-abscissa ruler**
   (`squarefreePowerQuotient`, `squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le`,
   `isRuler_squarefreePowerQuotient`, `squarefreePowerQuotient_poleFree_quarter_iff_riemannHypothesis`):
   Although `ζ(s) / ζ(2s)` does not unconditionally force zeros, combining the `2/3`
   halving-reflection cascade with the unconditional `7/8` zero-free half-plane (`1 - (7/8)/2 = 9/16`)
   makes pole-freeness of `((s - 1) ζ(s))^m / ζ(2s)` on `{Re s > β / 2}` an exact unconditional
   ruler for `zetaZeroAbscissa ≤ β` throughout `β ∈ [1/2, 9/16)` (and for `zetaZeroWidth` on
   `[0, 1/16)`), with `β = 1/4` equivalent to `RiemannHypothesis`.

3. **Shifted Rankin–Selberg / divisor-convolution barrier** (`ramanujan_shift_margin_ge`,
   `ramanujan_shift_margin_zeta_zero_ge_nine_sixteenths`):
   In Ramanujan's identity
   `∑ σ_a(n) σ_b(n) n^{-s} = ζ(s) ζ(s - a) ζ(s - b) ζ(s - a - b) / ζ(2s - a - b)`, the
   denominator zero `s_* = (ρ + a + b)/2` lies at distance `1 - Re ρ / 2` to the left of the polar
   abscissa `σ_pole = 1 + max(0, Re a, Re b, Re(a + b))`. For every nontrivial zero of `ζ`, the
   `7/8` zero-free region forces `σ_pole - Re s_* ≥ 9/16`.

4. **Frobenius reciprocity cancellation of Brauer permutation relations**
   (`sum_inducedFunction_one`, `brauer_permutation_relation_sum_eq`,
   `brauer_permutation_relation_sum_eq_zero`):
   For every finite group `G`, `∑_{g ∈ G} Ind_H^G(1_H)(g) = |G|` is independent of `H ≤ G`. Hence
   any virtual permutation identity `∑_i c_i Ind_{H_i}^G(1_{H_i}) = m · 1_G` satisfies `∑_i c_i = m`;
   in particular, every Brauer relation (`m = 0`) cancels the `1_G` (`ζ(s)`) multiplicity
   identically (`∑_i c_i = 0`).
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set
open scoped BigOperators Classical

namespace GaloisForLFunctions.ZeroForcingCalculus

/-! ## 1. Global meromorphy and order of `riemannZeta` and Witt monomials -/

/-- `riemannZeta` is complex-analytic at every point `s ≠ 1`. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hdiff : DifferentiableOn ℂ riemannZeta ({1}ᶜ) := fun z hz =>
    (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_compl_singleton) s (by simpa using hs)

/-- On a punctured neighborhood of `1`, `riemannZeta w = (w - 1)⁻¹ * zetaResidueUnit w`. -/
theorem riemannZeta_eventuallyEq_inv_mul_unit :
    riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)] fun w : ℂ => (w - 1)⁻¹ * RHTower.zetaResidueUnit w := by
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw1 : w ≠ 1 := by simpa using hw
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  rw [RHTower.zetaResidueUnit, Function.update_of_ne hw1, inv_mul_cancel_left₀ hsub]

/-- `riemannZeta` is meromorphic at every point of `ℂ` (including the simple pole `s = 1`). -/
theorem meromorphicAt_riemannZeta (s : ℂ) : MeromorphicAt riemannZeta s := by
  by_cases hs : s = 1
  · subst hs
    have hm : MeromorphicAt (fun w : ℂ => (w - 1)⁻¹ * RHTower.zetaResidueUnit w) 1 :=
      (((analyticAt_id.sub analyticAt_const).meromorphicAt).inv).mul
        (RHTower.analyticAt_zetaResidueUnit 1).meromorphicAt
    exact hm.congr riemannZeta_eventuallyEq_inv_mul_unit.symm
  · exact (analyticAt_riemannZeta hs).meromorphicAt

/-- `riemannZeta` never vanishes identically on a punctured neighborhood of any `s : ℂ`. -/
theorem meromorphicOrderAt_riemannZeta_ne_top (s : ℂ) :
    meromorphicOrderAt riemannZeta s ≠ ⊤ := by
  intro htop
  have hz0 : riemannZeta =ᶠ[𝓝[≠] s] 0 := meromorphicOrderAt_eq_top_iff.mp htop
  have hw1 : ∀ᶠ w : ℂ in 𝓝[≠] s, w ≠ 1 := by
    by_cases hs : s = 1
    · subst hs; simpa using self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hs)
  have hu_ne : RHTower.zetaResidueUnit =ᶠ[𝓝[≠] s] 0 := by
    filter_upwards [hz0, hw1] with w hwz hne
    change Function.update (fun z => (z - 1) * riemannZeta z) 1 1 w = 0
    rw [Function.update_of_ne hne, hwz, mul_zero]
  have hu_nhds : RHTower.zetaResidueUnit =ᶠ[𝓝 s] (fun _ => (0 : ℂ)) :=
    (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (RHTower.analyticAt_zetaResidueUnit s).continuousAt continuousAt_const).mpr hu_ne
  have han : AnalyticOnNhd ℂ RHTower.zetaResidueUnit Set.univ :=
    fun z _ => RHTower.analyticAt_zetaResidueUnit z
  have h10 : RHTower.zetaResidueUnit 1 = 0 :=
    han.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
      isPreconnected_univ (Set.mem_univ s) hu_nhds (Set.mem_univ 1)
  exact one_ne_zero (RHTower.zetaResidueUnit_one.symm.trans h10)

/-- At an analytic nonzero point, the meromorphic order vanishes. -/
theorem meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hne : f s ≠ 0) :
    meromorphicOrderAt f s = 0 :=
  (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hf.meromorphicAt).mp
    ⟨f s, hne, hf.continuousAt.continuousWithinAt.tendsto⟩

/-- At an analytic zero, the meromorphic order is strictly positive. -/
theorem meromorphicOrderAt_pos_of_analyticAt_eq_zero {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hz : f s = 0) :
    0 < meromorphicOrderAt f s := by
  refine (tendsto_zero_iff_meromorphicOrderAt_pos hf.meromorphicAt).mp ?_
  rw [← hz]
  exact hf.continuousAt.continuousWithinAt.tendsto

/-- At `s = 1`, `riemannZeta` has meromorphic order `-1`. -/
theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = -1 := by
  have heq : riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)]
      fun w : ℂ => (w - 1) ^ (-1 : ℤ) * RHTower.zetaResidueUnit w := by
    filter_upwards [riemannZeta_eventuallyEq_inv_mul_unit] with w hw
    rw [hw, zpow_neg_one]
  have hm1 : MeromorphicAt (fun w : ℂ => (w - 1) ^ (-1 : ℤ)) 1 :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).zpow (-1)
  have hm2 : MeromorphicAt RHTower.zetaResidueUnit 1 :=
    (RHTower.analyticAt_zetaResidueUnit 1).meromorphicAt
  have ho2 : meromorphicOrderAt RHTower.zetaResidueUnit 1 = 0 :=
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (RHTower.analyticAt_zetaResidueUnit 1)
      (by rw [RHTower.zetaResidueUnit_one]; exact one_ne_zero)
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_fun_mul hm1 hm2,
    meromorphicOrderAt_fun_zpow_id_sub_const, ho2, add_zero]
  rfl

/-- Meromorphic order of `w ↦ riemannZeta (c * w)` for any nonzero multiplier `c ≠ 0`. -/
theorem meromorphicOrderAt_riemannZeta_const_mul {c : ℂ} (hc : c ≠ 0) (s : ℂ) :
    MeromorphicAt (fun w : ℂ => riemannZeta (c * w)) s ∧
      meromorphicOrderAt (fun w : ℂ => riemannZeta (c * w)) s =
        meromorphicOrderAt riemannZeta (c * s) := by
  set g : ℂ → ℂ := fun w => c * w
  have hg : AnalyticAt ℂ g s := analyticAt_const.mul analyticAt_id
  have hderiv : HasDerivAt g c s := by
    simpa [g, mul_one] using (hasDerivAt_id s).const_mul c
  have hg' : deriv g s ≠ 0 := by rwa [hderiv.deriv]
  refine ⟨(meromorphicAt_comp_iff_of_deriv_ne_zero hg hg').mpr (meromorphicAt_riemannZeta (g s)),
    meromorphicOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) hg hg'⟩

/-- **Witt Euler-product monomial** `W_e(s) = ∏_{j=0}^{K-1} ζ((j + 1) s)^{e_j}` associated to an
integer exponent vector `e : Fin K → ℤ`. -/
def wittZetaMonomial (K : ℕ) (e : Fin K → ℤ) (s : ℂ) : ℂ :=
  ∏ j : Fin K, riemannZeta (((j.1 + 1 : ℕ) : ℂ) * s) ^ e j

/-- **Exact global order identity for Witt monomials.** For every `s : ℂ` (including poles of
individual factors), `ord_s W_e = ∑_{j=0}^{K-1} e_j · ord_{(j+1)s} ζ`. -/
theorem meromorphicOrderAt_wittZetaMonomial (K : ℕ) (e : Fin K → ℤ) (s : ℂ) :
    meromorphicOrderAt (wittZetaMonomial K e) s =
      ∑ j : Fin K, (e j : WithTop ℤ) *
        meromorphicOrderAt riemannZeta (((j.1 + 1 : ℕ) : ℂ) * s) := by
  have hc : ∀ j : Fin K, ((j.1 + 1 : ℕ) : ℂ) ≠ 0 :=
    fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j.1)
  have hm : ∀ j ∈ (Finset.univ : Finset (Fin K)),
      MeromorphicAt (fun w : ℂ => riemannZeta (((j.1 + 1 : ℕ) : ℂ) * w) ^ e j) s :=
    fun j _ => ((meromorphicOrderAt_riemannZeta_const_mul (hc j) s).1).zpow (e j)
  unfold wittZetaMonomial
  rw [meromorphicOrderAt_fun_prod hm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := meromorphicOrderAt_riemannZeta_const_mul (hc j) s
  rw [meromorphicOrderAt_fun_zpow hj.1, hj.2]

/-- **Higher Witt factors are invisible on `Re ρ > 1/2`.** At every point `ρ` with `Re ρ > 1/2`, all
dilated factors `ζ((j + 1) ρ)` with `j ≥ 1` have `Re((j + 1) ρ) ≥ 2 Re ρ > 1`, hence are analytic
and nonzero. Consequently `ord_ρ W_e = e_0 · ord_ρ ζ`: no choice of higher Witt exponents can cancel
or alter the order of `ζ` at `ρ` unless `e_0 = 0`. -/
theorem meromorphicOrderAt_wittZetaMonomial_of_half_lt_re {ρ : ℂ} (hre : 1 / 2 < ρ.re)
    (K : ℕ) (hK : 0 < K) (e : Fin K → ℤ) :
    meromorphicOrderAt (wittZetaMonomial K e) ρ =
      (e ⟨0, hK⟩ : WithTop ℤ) * meromorphicOrderAt riemannZeta ρ := by
  rw [meromorphicOrderAt_wittZetaMonomial]
  rw [Finset.sum_eq_single ⟨0, hK⟩]
  · simp
  · intro j _ hj0
    have hj1 : 1 ≤ j.1 := Nat.one_le_iff_ne_zero.mpr fun h => hj0 (Fin.ext h)
    have hmul_re : (((j.1 + 1 : ℕ) : ℂ) * ρ).re = ((j.1 + 1 : ℕ) : ℝ) * ρ.re := by
      simpa using Complex.re_ofReal_mul ((j.1 + 1 : ℕ) : ℝ) ρ
    have hj_ge : (2 : ℝ) ≤ ((j.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj1
    have hgt1 : 1 < (((j.1 + 1 : ℕ) : ℂ) * ρ).re := by
      rw [hmul_re]
      nlinarith
    have hne1 : ((j.1 + 1 : ℕ) : ℂ) * ρ ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hgt1
      exact lt_irrefl 1 hgt1
    have ho0 : meromorphicOrderAt riemannZeta (((j.1 + 1 : ℕ) : ℂ) * ρ) = 0 :=
      meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (analyticAt_riemannZeta hne1)
        (riemannZeta_ne_zero_of_one_le_re hgt1.le)
    rw [ho0, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ ⟨0, hK⟩) hmem

/-! ## 2. The unconditional `[1/2, 9/16)` squarefree pole-abscissa ruler -/

/-- Pole-cleared Euler quotient `((s - 1) ζ(s))^m / ζ(2s)`. For `m = 1` this is `(s - 1)` times the
squarefree Dirichlet series `∑ μ(n)² n^{-s} = ζ(s) / ζ(2s)`; for `m = 2` it is `(s - 1)²` times
`∑ 2^{ω(n)} n^{-s} = ζ(s)² / ζ(2s)`. -/
def squarefreePowerQuotient (m : ℕ) (s : ℂ) : ℂ :=
  ((s - 1) * riemannZeta s) ^ m / riemannZeta (2 * s)

/-- On a punctured neighborhood of **every** `s : ℂ` (including `s = 1` and `s = 1/2`),
`squarefreePowerQuotient m` agrees with the entire-numerator quotient
`zetaResidueUnit(w)^m * (2w - 1) / zetaResidueUnit(2w)`. -/
theorem squarefreePowerQuotient_eventuallyEq_unit (m : ℕ) (s : ℂ) :
    squarefreePowerQuotient m =ᶠ[𝓝[≠] s]
      fun w : ℂ => RHTower.zetaResidueUnit w ^ m * (2 * w - 1) /
        RHTower.zetaResidueUnit (2 * w) := by
  have hw1 : ∀ᶠ w : ℂ in 𝓝[≠] s, w ≠ 1 := by
    by_cases hs : s = 1
    · subst hs; simpa using self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hs)
  have hw_half : ∀ᶠ w : ℂ in 𝓝[≠] s, w ≠ (1 / 2 : ℂ) := by
    by_cases hs : s = (1 / 2 : ℂ)
    · subst hs; simpa using self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hs)
  filter_upwards [hw1, hw_half] with w hne1 hneh
  have h2w1 : 2 * w ≠ 1 := by
    intro h
    apply hneh
    linear_combination (1 / 2 : ℂ) * h
  have h2sub : 2 * w - 1 ≠ 0 := sub_ne_zero.mpr h2w1
  unfold squarefreePowerQuotient
  change ((w - 1) * riemannZeta w) ^ m / riemannZeta (2 * w) =
    Function.update (fun z => (z - 1) * riemannZeta z) 1 1 w ^ m * (2 * w - 1) /
      Function.update (fun z => (z - 1) * riemannZeta z) 1 1 (2 * w)
  rw [Function.update_of_ne hne1, Function.update_of_ne h2w1]
  by_cases hz : riemannZeta (2 * w) = 0
  · simp [hz]
  · field_simp [h2sub, hz]

/-- `squarefreePowerQuotient m` is meromorphic at every `s : ℂ`. -/
theorem meromorphicAt_squarefreePowerQuotient (m : ℕ) (s : ℂ) :
    MeromorphicAt (squarefreePowerQuotient m) s := by
  have hnum : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * (2 * w - 1)) s :=
    ((RHTower.analyticAt_zetaResidueUnit s).pow m).mul
      ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
  have hden : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit (2 * w)) s :=
    (RHTower.analyticAt_zetaResidueUnit (2 * s)).comp (analyticAt_const.mul analyticAt_id)
  exact (hnum.meromorphicAt.div hden.meromorphicAt).congr
    (squarefreePowerQuotient_eventuallyEq_unit m s).symm

/-- **Unconditional `[1/2, 9/16)` pole-abscissa theorem.** For every `m : ℕ` and every
`β ∈ [1/2, 9/16)`, `((s - 1) ζ(s))^m / ζ(2s)` has nonnegative meromorphic order throughout
`{Re s > β / 2}` if and only if `zetaZeroAbscissa ≤ β`.
- Forward (`Transmits`): if `zetaZeroAbscissa ≤ β`, then `ζ(2s) ≠ 0` whenever `Re(2s) > β` and
  `2s ≠ 1`, while the pole of `ζ(2s)` at `s = 1/2` gives a zero of `1 / ζ(2s)`.
- Converse (`Receives`): if `((s - 1) ζ(s))^m / ζ(2s)` is pole-free on `{Re s > β / 2}`, then every
  zero `ρ` with `β < Re ρ < 1` must satisfy `ζ(ρ / 2) = 0`; for any zero `ρ` in the strip, the
  unconditional `7/8` zero-free half-plane gives `1 - Re ρ / 2 ≥ 9/16 > β`, so the `2/3`
  halving-reflection cascade contradicts `ζ(2/3) ≠ 0`. -/
theorem squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le (m : ℕ) {β : ℝ}
    (hβ : β ∈ Set.Ico (1 / 2 : ℝ) (9 / 16)) :
    (∀ s : ℂ, β / 2 < s.re → 0 ≤ meromorphicOrderAt (squarefreePowerQuotient m) s) ↔
      RHTower.zetaZeroAbscissa ≤ β := by
  obtain ⟨hβ_lo, hβ_hi⟩ := hβ
  constructor
  · intro hpole
    have hhalf : ∀ ρ : ℂ, riemannZeta ρ = 0 → 2 * (β / 2) < ρ.re → ρ.re < 1 →
        riemannZeta (ρ / 2) = 0 := by
      intro ρ hζ hre1 hre2
      by_contra hnhalf
      have hs_re : (ρ / 2).re = ρ.re / 2 := by
        have h := congrArg Complex.re (show ((2 : ℝ) : ℂ) * (ρ / 2) = ρ by push_cast; ring)
        rw [Complex.re_ofReal_mul] at h
        linarith
      have hs_gt : β / 2 < (ρ / 2).re := by linarith
      have hs_ne1 : ρ / 2 ≠ 1 := by
        intro h
        rw [h, Complex.one_re] at hs_re
        linarith
      have hρ_ne1 : ρ ≠ 1 := by
        intro h
        rw [h, Complex.one_re] at hre2
        exact lt_irrefl 1 hre2
      set u : ℂ → ℂ := fun w => ((w - 1) * riemannZeta w) ^ m
      set v : ℂ → ℂ := fun w => riemannZeta (2 * w)
      have hu_an : AnalyticAt ℂ u (ρ / 2) :=
        ((analyticAt_id.sub analyticAt_const).mul (analyticAt_riemannZeta hs_ne1)).pow m
      have hu_ne : u (ρ / 2) ≠ 0 :=
        pow_ne_zero m (mul_ne_zero (sub_ne_zero.mpr hs_ne1) hnhalf)
      have hu_ord : meromorphicOrderAt u (ρ / 2) = 0 :=
        meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hu_an hu_ne
      have hv_pair := meromorphicOrderAt_riemannZeta_const_mul (two_ne_zero) (ρ / 2)
      have h2half : (2 : ℂ) * (ρ / 2) = ρ := by ring
      have hv_ord : meromorphicOrderAt v (ρ / 2) = meromorphicOrderAt riemannZeta ρ := by
        simpa [v, h2half] using hv_pair.2
      have hρ_pos : 0 < meromorphicOrderAt riemannZeta ρ :=
        meromorphicOrderAt_pos_of_analyticAt_eq_zero (analyticAt_riemannZeta hρ_ne1) hζ
      have hρ_ntop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ :=
        meromorphicOrderAt_riemannZeta_ne_top ρ
      lift meromorphicOrderAt riemannZeta ρ to ℤ using hρ_ntop with n hn
      have hn_pos : 0 < n := by exact_mod_cast hn ▸ hρ_pos
      have hq_ord : meromorphicOrderAt (squarefreePowerQuotient m) (ρ / 2) =
          ((-n : ℤ) : WithTop ℤ) := by
        change meromorphicOrderAt (u / v) (ρ / 2) = _
        rw [meromorphicOrderAt_div hu_an.meromorphicAt hv_pair.1, hu_ord, hv_ord, ← hn, zero_sub]
        rfl
      have hnonneg := hpole (ρ / 2) hs_gt
      rw [hq_ord] at hnonneg
      have hle : (0 : ℤ) ≤ -n := by exact_mod_cast hnonneg
      omega
    have hσ : 0 ≤ β - 1 / 2 := by linarith
    have hle : RHTower.zetaZeroAbscissa ≤ 1 / 2 + (β - 1 / 2) := by
      rw [SquareRootThreshold.zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ]
      intro ρ hρ
      obtain ⟨hζ, h0, _⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
      have h78 : ρ.re ≤ 7 / 8 :=
        (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_quasiRH_strip h0 hζ).2
      by_contra hgt
      rw [not_le] at hgt
      exact RHTower.SquarefreeDiscrepancy.riemannZeta_ne_zero_of_halving
        (by linarith : (0 : ℝ) ≤ β / 2) hhalf (by linarith) (by linarith) hζ
    linarith only [hle]
  · intro habs s hs
    rw [meromorphicOrderAt_congr (squarefreePowerQuotient_eventuallyEq_unit m s)]
    have h2s_re : (2 * s).re = 2 * s.re := by
      simpa using Complex.re_ofReal_mul (2 : ℝ) s
    have hden_ne : RHTower.zetaResidueUnit (2 * s) ≠ 0 := by
      by_cases h2s1 : 2 * s = 1
      · rw [h2s1, RHTower.zetaResidueUnit_one]
        exact one_ne_zero
      · rw [RHTower.zetaResidueUnit, Function.update_of_ne h2s1]
        refine mul_ne_zero (sub_ne_zero.mpr h2s1) ?_
        intro hζ2
        have hle := (RHTower.re_le_zetaZeroAbscissa hζ2).trans habs
        linarith
    have han : AnalyticAt ℂ
        (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * (2 * w - 1) /
          RHTower.zetaResidueUnit (2 * w)) s := by
      have hnum : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * (2 * w - 1)) s :=
        ((RHTower.analyticAt_zetaResidueUnit s).pow m).mul
          ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
      have hden : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit (2 * w)) s :=
        (RHTower.analyticAt_zetaResidueUnit (2 * s)).comp (analyticAt_const.mul analyticAt_id)
      exact hnum.div hden hden_ne
    exact han.meromorphicOrderAt_nonneg

/-- **Squarefree quotient ruler for `zetaZeroWidth` on `[0, 1/16)`.** In the language of
`ExponentDynamicsOfTheCriticalStrip`, pole-freeness of `((s - 1) ζ(s))^m / ζ(2s)` on
`{Re s > (1/2 + w)/2}` is an unconditional ruler for `zetaZeroWidth` across `w ∈ [0, 1/16)`. -/
theorem isRuler_squarefreePowerQuotient (m : ℕ) :
    ExponentDynamicsOfTheCriticalStrip.IsRuler SquareRootThreshold.zetaZeroWidth
      (Set.Ico (0 : ℝ) (1 / 16))
      (fun w => ∀ s : ℂ, (1 / 2 + w) / 2 < s.re →
        0 ≤ meromorphicOrderAt (squarefreePowerQuotient m) s) := by
  intro w hw
  have hβ : 1 / 2 + w ∈ Set.Ico (1 / 2 : ℝ) (9 / 16) :=
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  exact (SquareRootThreshold.zetaZeroWidth_le_iff_zetaZeroAbscissa_le hw.1).trans
    (squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le m hβ).symm

/-- **Quarter-abscissa equivalence with the Riemann hypothesis.** For every `m : ℕ` (in particular
for `m = 1`, `(s - 1) ζ(s) / ζ(2s)`, and `m = 2`, `((s - 1) ζ(s))² / ζ(2s)`), pole-freeness on
`{Re s > 1/4}` holds if and only if `RiemannHypothesis` holds. -/
theorem squarefreePowerQuotient_poleFree_quarter_iff_riemannHypothesis (m : ℕ) :
    (∀ s : ℂ, (1 / 4 : ℝ) < s.re → 0 ≤ meromorphicOrderAt (squarefreePowerQuotient m) s) ↔
      RiemannHypothesis := by
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (1 / 16) := ⟨le_rfl, by norm_num⟩
  have hr := isRuler_squarefreePowerQuotient m 0 h0
  rw [show ((1 / 2 + (0 : ℝ)) / 2 : ℝ) = 1 / 4 by norm_num] at hr
  refine hr.symm.trans ?_
  rw [le_antisymm_iff]
  exact ⟨fun h => SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
      (le_antisymm h SquareRootThreshold.zetaZeroWidth_nonneg),
    fun h => (SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp h).le⟩

/-- Specialization of the `[1/2, 9/16)` ruler to the literal pole-cleared squarefree Dirichlet
series `(s - 1) ζ(s) / ζ(2s)` (`m = 1`). -/
theorem squarefreeQuotient_poleFree_iff_zetaZeroAbscissa_le {β : ℝ}
    (hβ : β ∈ Set.Ico (1 / 2 : ℝ) (9 / 16)) :
    (∀ s : ℂ, β / 2 < s.re →
        0 ≤ meromorphicOrderAt (fun w => ((w - 1) * riemannZeta w) / riemannZeta (2 * w)) s) ↔
      RHTower.zetaZeroAbscissa ≤ β := by
  simpa [squarefreePowerQuotient, pow_one] using
    squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le 1 hβ

/-! ## 3. The shifted Rankin–Selberg / Ramanujan divisor-convolution barrier -/

/-- **Universal shift-margin inequality for Ramanujan's identity**
`∑ σ_a(n) σ_b(n) n^{-s} = ζ(s) ζ(s - a) ζ(s - b) ζ(s - a - b) / ζ(2s - a - b)`.
The numerator poles lie at `{1, 1 + a, 1 + b, 1 + a + b}` with maximum real part
`σ_pole(a, b) = 1 + max(0, Re a, Re b, Re(a + b))`, while a zero `ρ` of `ζ` places a denominator
zero at `s_* = (ρ + a + b) / 2`. For **every** `(a, b) ∈ ℂ²`, the gap `σ_pole(a, b) - Re s_*` is
bounded below by `1 - Re ρ / 2`, with equality when `Re a = Re b = 0`: shifting `(a, b)` never
brings `s_*` closer to or to the right of the polar abscissa. -/
theorem ramanujan_shift_margin_ge (a b ρ : ℂ) :
    1 - ρ.re / 2 ≤
      (1 + max (max (0 : ℝ) a.re) (max b.re (a + b).re)) - ((ρ + a + b) / 2).re := by
  have hs_re : ((ρ + a + b) / 2).re = (ρ.re + a.re + b.re) / 2 := by
    have h := congrArg Complex.re
      (show ((2 : ℝ) : ℂ) * ((ρ + a + b) / 2) = ρ + a + b by push_cast; ring)
    rw [Complex.re_ofReal_mul, Complex.add_re, Complex.add_re] at h
    linarith
  have h0 : (0 : ℝ) ≤ max (max (0 : ℝ) a.re) (max b.re (a + b).re) :=
    le_trans (le_max_left 0 a.re) (le_max_left _ _)
  have hab : (a + b).re ≤ max (max (0 : ℝ) a.re) (max b.re (a + b).re) :=
    le_trans (le_max_right b.re (a + b).re) (le_max_right _ _)
  have havg : (a.re + b.re) / 2 ≤ max (max (0 : ℝ) a.re) (max b.re (a + b).re) := by
    rw [Complex.add_re] at hab
    linarith
  rw [hs_re]
  linarith

/-- For every nontrivial zero `ρ` of `riemannZeta` (`Re ρ > 0`) and every shift pair `(a, b) ∈ ℂ²`,
the denominator zero `s_* = (ρ + a + b) / 2` lies at least `9/16` to the left of the polar abscissa
`σ_pole(a, b)` of `ζ(s) ζ(s - a) ζ(s - b) ζ(s - a - b) / ζ(2s - a - b)`. -/
theorem ramanujan_shift_margin_zeta_zero_ge_nine_sixteenths (a b : ℂ) {ρ : ℂ}
    (h0 : 0 < ρ.re) (hζ : riemannZeta ρ = 0) :
    (9 / 16 : ℝ) ≤
      (1 + max (max (0 : ℝ) a.re) (max b.re (a + b).re)) - ((ρ + a + b) / 2).re := by
  have h78 : ρ.re ≤ 7 / 8 :=
    (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_quasiRH_strip h0 hζ).2
  have hm := ramanujan_shift_margin_ge a b ρ
  linarith

/-! ## 4. Frobenius reciprocity cancellation of Brauer permutation relations -/

/-- **Frobenius reciprocity for the trivial character `⟨Ind_H^G 1_H, 1_G⟩_G = 1`.**
Summing the induced trivial character `Ind_H^G(1_H)` over a finite group `G` yields `|G|` for every
subgroup `H ≤ G`, independent of `H`. -/
theorem sum_inducedFunction_one {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    ∑ g : G, inducedFunction H (fun _ => 1) g = (Fintype.card G : ℂ) := by
  unfold inducedFunction
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hconj : ∀ x : G,
      ∑ g : G, extendByZero H (fun _ => (1 : ℂ)) (x * g * x⁻¹) =
        ∑ h : G, extendByZero H (fun _ => (1 : ℂ)) h := by
    intro x
    let e : G ≃ G :=
      { toFun := fun g => x * g * x⁻¹
        invFun := fun g => x⁻¹ * g * x
        left_inv := fun g => by group
        right_inv := fun g => by group }
    exact Equiv.sum_comp e (extendByZero H (fun _ => (1 : ℂ)))
  simp_rw [hconj]
  have hsumH : ∑ h : G, extendByZero H (fun _ => (1 : ℂ)) h = (Nat.card H : ℂ) := by
    have hite : ∀ h : G, extendByZero H (fun _ => (1 : ℂ)) h = if h ∈ H then 1 else 0 := by
      intro h
      by_cases hh : h ∈ H
      · rw [extendByZero_of_mem H _ hh, if_pos hh]
      · rw [extendByZero_of_notMem H _ hh, if_neg hh]
    simp_rw [hite]
    rw [Finset.sum_boole]
    have hcard : (Finset.univ.filter (· ∈ H)).card = Fintype.card H := by
      refine Finset.card_bij (fun a ha => (⟨a, (Finset.mem_filter.mp ha).2⟩ : H))
        (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h) ?_
      intro b _
      exact ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, rfl⟩
    rw [hcard, ← Nat.card_eq_fintype_card]
  rw [hsumH, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  haveI : Nonempty H := ⟨⟨1, H.one_mem⟩⟩
  have hHpos : 0 < Nat.card H := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hHpos.ne'
  rw [mul_comm (Fintype.card G : ℂ) (Nat.card H : ℂ), ← mul_assoc, inv_mul_cancel₀ hH0, one_mul]

/-- **Multiplicity of `1_G` in any virtual permutation character.** If
`∑_i c_i Ind_{H_i}^G(1_{H_i}) = m · 1_G` on a finite group `G`, then `∑_i c_i = m`. In Artin–Dedekind
`L`-factorizations `∏_i ζ_{K_i}(s)^{c_i}`, the net exponent of `ζ(s)` equals `∑_i c_i = m`. -/
theorem brauer_permutation_relation_sum_eq {G : Type*} [Group G] [Fintype G]
    {ι : Type*} [Fintype ι] (c : ι → ℤ) (H : ι → Subgroup G) (m : ℤ)
    (h : ∀ g : G, ∑ i : ι, (c i : ℂ) * inducedFunction (H i) (fun _ => 1) g = (m : ℂ)) :
    ∑ i : ι, c i = m := by
  have hsum : ∑ g : G, ∑ i : ι, (c i : ℂ) * inducedFunction (H i) (fun _ => 1) g =
      ∑ g : G, (m : ℂ) := Finset.sum_congr rfl fun g _ => h g
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.mul_sum, sum_inducedFunction_one] at hsum
  rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm (Fintype.card G : ℂ) (m : ℂ)] at hsum
  have hG0 : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have heqC : ∑ i : ι, (c i : ℂ) = (m : ℂ) := mul_right_cancel₀ hG0 hsum
  exact_mod_cast heqC

/-- **Brauer cancellation law (`m = 0`).** Every virtual permutation relation
`∑_i c_i Ind_{H_i}^G(1_{H_i}) = 0` satisfies `∑_i c_i = 0`: the `1_G` (`ζ(s)`) factor cancels
identically from the corresponding Dedekind zeta identity `∏_i ζ_{K_i}(s)^{c_i} = 1`. -/
theorem brauer_permutation_relation_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    {ι : Type*} [Fintype ι] (c : ι → ℤ) (H : ι → Subgroup G)
    (h : ∀ g : G, ∑ i : ι, (c i : ℂ) * inducedFunction (H i) (fun _ => 1) g = 0) :
    ∑ i : ι, c i = 0 := by
  exact brauer_permutation_relation_sum_eq c H 0 (by simpa using h)

end GaloisForLFunctions.ZeroForcingCalculus

#print axioms GaloisForLFunctions.ZeroForcingCalculus.meromorphicAt_riemannZeta
#print axioms GaloisForLFunctions.ZeroForcingCalculus.meromorphicOrderAt_riemannZeta_ne_top
#print axioms GaloisForLFunctions.ZeroForcingCalculus.meromorphicOrderAt_riemannZeta_one
#print axioms GaloisForLFunctions.ZeroForcingCalculus.meromorphicOrderAt_wittZetaMonomial
#print axioms GaloisForLFunctions.ZeroForcingCalculus.meromorphicOrderAt_wittZetaMonomial_of_half_lt_re
#print axioms GaloisForLFunctions.ZeroForcingCalculus.squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le
#print axioms GaloisForLFunctions.ZeroForcingCalculus.isRuler_squarefreePowerQuotient
#print axioms GaloisForLFunctions.ZeroForcingCalculus.squarefreePowerQuotient_poleFree_quarter_iff_riemannHypothesis
#print axioms GaloisForLFunctions.ZeroForcingCalculus.squarefreeQuotient_poleFree_iff_zetaZeroAbscissa_le
#print axioms GaloisForLFunctions.ZeroForcingCalculus.ramanujan_shift_margin_ge
#print axioms GaloisForLFunctions.ZeroForcingCalculus.ramanujan_shift_margin_zeta_zero_ge_nine_sixteenths
#print axioms GaloisForLFunctions.ZeroForcingCalculus.sum_inducedFunction_one
#print axioms GaloisForLFunctions.ZeroForcingCalculus.brauer_permutation_relation_sum_eq
#print axioms GaloisForLFunctions.ZeroForcingCalculus.brauer_permutation_relation_sum_eq_zero
