import GaloisForLFunctions.ArithmeticIncidencePositivity.SharedDerivativeEnergyAndGlobalAllocationSynthesis
import GaloisForLFunctions.SquareRootThreshold.TheIncidenceLedgerGradedByTheZeroWidth
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.SquareRootThreshold.TheReceiverDampingReadsTheZeroWidth

/-!
# The Compensated Remainder of the Full Ledger and the Zero-Free Strip Equivalence

`ThePrimePolarResidualHasTheDeLaValleePoussinSaving` bounds the one-dimensional prime–polar lag
residual on a single translate `x` of a compactly supported `C¹` test. To pass from a single
translate to the **complete quadratic incidence ledger** `fullZeroForm F` with its favorable prime
even strip gains (`evenStripGain`), its archimedean gamma/gauge budget (`surplusPool`,
`crossingPotentialTerm`, `gaugeRemainder`), and its pole square (`poleCharge`) retained, and to
characterize when the compensated remainder has a sub-trivial exponent `< 1/2`, one must reconcile
two phenomena:

1. **Spatial compression at fixed aperture (`SharedDerivativeEnergyAndGlobalAllocationSynthesis`):**
   Compressing `F ↦ F(a ·)` (`a ≥ 1`) inside a fixed interval `[−r, r]` scales `∫ F²` by `a⁻¹` and
   `∫ (F′)²` by `a`, so any bound on the compensated remainder `reflectedPrimePolarCost F r` across
   *all* odd `C²_c[−r, r]` tests with an aperture rate `< 1` must be graded by the Sobolev energy
   `∫ (F′)²` (specifically, the first-order norm `∫ F² + ½ ∫ (F′)²` or the second-order pole-tilted
   norm `¼ ∫ F² + ∫ (F′)²`).
2. **Uniform regularity of the arithmetic lag family (`boundedDirichletCone_twoBump_modScaledBump_re`):**
   The difference lag tests `f_v(u) = κ_{w,0}(u + v/2) − κ_{w,0}(u − v/2)` that read the zero width
   at aperture `r = v/2 + w` translate a fixed bump without compressing it. Their real part satisfies
   `∫ (F_v′)² ≤ (bumpDirichletRatio w)² ∫ F_v²` with a regularity ratio `bumpDirichletRatio w`
   depending only on the bump width `w` and completely independent of the lag `v` and aperture `r`.

Combining these two facts yields a complete, unconditional solution for the compensated remainder of
the full ledger:

* **Complete compensated ledger identities and unconditional de la Vallée Poussin floor (§1):**
  For every `0 < r < R` and every real odd `F ∈ C²_c[−r, r]`,
  `fullZeroForm F = archimedeanLedgerBudget r R F − reflectedPrimePolarCost F r`
  (`fullZeroForm_eq_archimedeanLedgerBudget_sub_reflectedPrimePolarCost`), where
  `archimedeanLedgerBudget r R F = surplusPool + crossingPotentialTerm + gaugeRemainder ≥ −(27/5) ∫ F²`
  and `reflectedPrimePolarCost F r = (∑ oddStripCost) − (∑ evenStripGain) + poleCharge` equals both
  the first-order Chebyshev-defect integral on `(0, 2r]`
  (`fullZeroForm_eq_completeCompensatedLedger_firstOrder`) and the second-order critical-scale
  prefix integral on `(0, 2r]` (`fullZeroForm_eq_completeCompensatedLedger_secondOrder`), yielding
  the unconditional all-aperture de la Vallée Poussin floor
  `fullZeroForm F ≥ −K e^r exp(−c√r) (¼ ∫ F² + ∫ (F′)²)`
  (`exists_fullZeroForm_ge_deLaValleePoussin_poleTiltedSobolev`).
* **The arithmetic test class: bounded-Dirichlet-ratio and sub-envelope cones (§2):**
  On the exponentially wide arithmetic cone `SubEnvelopeDirichletCone c r F` (`∫ (F′)² ≤ 2 e^{c√r} ∫ F²`),
  which contains every fixed-regularity cone `BoundedDirichletCone Λ F` (`∫ (F′)² ≤ Λ² ∫ F²`) above
  a finite scale, the complete ledger satisfies the pure-`L²` de la Vallée Poussin floor
  `fullZeroForm F ≥ −K e^r exp(−c√r) ∫ F²`
  (`exists_fullZeroForm_ge_deLaValleePoussin_of_subEnvelopeDirichletCone`). Moreover, every disjoint
  difference lag test `Re(twoBump (modScaledBump w 0) v (−1))` (`v > 2w`) belongs to
  `BoundedDirichletCone (bumpDirichletRatio w)` uniformly in `v`
  (`boundedDirichletCone_twoBump_modScaledBump_re`).
* **Forward bridge from the zero width to the complete ledger (§3):**
  For every `σ > zetaZeroWidth`, the generalized von Koch bound in the Chebyshev gauge eliminates all
  polynomial aperture factors `(1 + r)` by absorbing `2r` into half of the gap `σ − zetaZeroWidth`,
  proving that `∫_0^{2r} 2e^{−s/2}|E(s)| ds ≤ K_σ e^{2σ r}` and
  `∫_0^{2r} 2e^{−s/2}|D(s) + s²/2 − s| ds ≤ K′_σ e^{2σ r}`, whence
  `|reflectedPrimePolarCost F r| ≤ K_σ e^{2σ r} (¼ ∫ F² + ∫ (F′)²)` and the complete ledger obeys
  `SobolevGradedIncidenceAllocation σ K_σ` (`exists_sobolevGradedIncidenceAllocation_of_zetaZeroWidth_lt`).
* **Converse bridge and exact equivalences (§4–§5):**
  Evaluating any pole-tilted Sobolev floor on `fullZeroForm F`, any `SobolevGradedIncidenceAllocation σ C`,
  or any pure-`L²` floor on the bounded-Dirichlet-ratio cones `BoundedDirichletCone Λ` against the
  difference lag family forces `zetaZeroWidth ≤ σ`. Consequently, for every `σ₀ ≥ 0`,
  `zetaZeroWidth ≤ σ₀` is unconditionally equivalent to each of these complete-ledger bounds at
  every rate `σ > σ₀`; an exponent `σ < 1/2` for the compensated remainder of the complete ledger is
  unconditionally equivalent to a zero-free strip `zetaZeroAbscissa < 1` (and to
  `receiverDampingRate < 1/2`); and every exponent `σ > 0` holds if and only if `RiemannHypothesis`
  holds.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real
open _root_.Zeta23 _root_.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## §1. The Complete Incidence Ledger and its Compensated Remainder -/

/-- **The archimedean budget of the complete incidence ledger** at aperture `r` and plateau radius
`R`: the sum of the archimedean strip surplus pool, the boundary crossing potential term, and the
plateau gauge remainder (which retains the gamma factor). -/
def archimedeanLedgerBudget (r R : ℝ) (F : ℝ → ℝ) : ℝ :=
  surplusPool (aperturePlateau r R) F +
    crossingPotentialTerm (aperturePlateau r R) F +
    gaugeRemainder (aperturePlateau r R) F

/-- The archimedean ledger budget is bounded below by `−(27/5) ∫ F²` uniformly across all apertures
`0 < r < R` and all `F ∈ C²_c[−r, r]`, because `surplusPool ≥ 0`, `crossingPotentialTerm ≥ 0`, and
`gaugeRemainder ≥ −(27/5) ∫ F²`. -/
theorem archimedeanLedgerBudget_ge_neg_const_mul_sq {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    -(27 / 5 * ∫ x, F x ^ 2) ≤ archimedeanLedgerBudget r R F := by
  unfold archimedeanLedgerBudget
  have hP0 : ∀ y, 0 ≤ aperturePlateau r R y :=
    fun y => plateauGauge_nonneg R (R - r) y
  have hpool := surplusPool_nonneg (F := F) hP0
  have hcross := crossingPotentialTerm_nonneg (F := F) hP0
  have hrem := gaugeRemainder_ge_neg_const_mul_sq hF hFc hsupp hrR
  linarith

/-- **Complete incidence ledger decomposition.** For every real odd `F ∈ C²_c[−r, r]` (`0 < r < R`),
the complete quadratic Weil zero form `fullZeroForm F` equals the archimedean ledger budget minus
the compensated reflected-prime/polar remainder `reflectedPrimePolarCost F r =
(∑ oddStripCost) − (∑ evenStripGain) + poleCharge F`. -/
theorem fullZeroForm_eq_archimedeanLedgerBudget_sub_reflectedPrimePolarCost {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F = archimedeanLedgerBudget r R F - reflectedPrimePolarCost F r := by
  unfold archimedeanLedgerBudget
  exact fullZeroForm_eq_reflectedPrimePolarLedger hF hFc hodd hr hsupp hrR

/-- **First-order Chebyshev-defect identity for the complete ledger.** On every real odd
`F ∈ C²_c[−r, r]` (`0 < r < R`), the prime and polar rate-`1` main terms cancel identically inside
the complete ledger, leaving the horizon-localized Chebyshev-defect integral on `(0, 2r]`. -/
theorem fullZeroForm_eq_completeCompensatedLedger_firstOrder {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F =
      archimedeanLedgerBudget r R F -
        ∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  rw [fullZeroForm_eq_archimedeanLedgerBudget_sub_reflectedPrimePolarCost hF hFc hodd hr hsupp hrR,
    reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc (hF.of_le (by norm_num)) hFc hodd hr hsupp]

/-- **Second-order critical-scale prefix identity for the complete ledger.** On every real odd
`F ∈ C²_c[−r, r]` (`0 < r < R`), integrating by parts a second time in the lag variable expresses
the compensated remainder of the complete ledger as the pairing of `D(s) + s²/2 − s` against the
pole-tilted self-convolution `autoCorrelation (deriv F) s + crossCorrelation F s − autoCorrelation F s / 4`
on `(0, 2r]`. -/
theorem fullZeroForm_eq_completeCompensatedLedger_secondOrder {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F =
      archimedeanLedgerBudget r R F -
        ∫ s in Ioc (0 : ℝ) (2 * r),
          (criticalScalePrefix s + s ^ 2 / 2 - s) *
            (2 * Real.exp (-s / 2) *
              (autoCorrelation (deriv F) s + crossCorrelation F s - autoCorrelation F s / 4)) := by
  rw [fullZeroForm_eq_archimedeanLedgerBudget_sub_reflectedPrimePolarCost hF hFc hodd hr hsupp hrR,
    reflectedPrimePolarCost_eq_criticalScalePrefix_Ioc hF hFc hodd hr hsupp]

/-- **Unconditional all-aperture de la Vallée Poussin floor for the complete ledger.**
With universal constants `c > 0` and `K > 0`, for every aperture `r > 0` and every real odd
`F ∈ C²_c[−r, r]`, the complete quadratic Weil zero form satisfies
`fullZeroForm F ≥ −K e^r exp(−c√r) ((1/4) ∫ F² + ∫ (deriv F)²)`. -/
theorem exists_fullZeroForm_ge_deLaValleePoussin_poleTiltedSobolev :
    ∃ c > 0, ∃ K > 0, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
      ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(K * Real.exp r * Real.exp (-c * Real.sqrt r) *
          ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) ≤ fullZeroForm F := by
  obtain ⟨c, hc, K, hK, halloc⟩ :=
    exists_globalIncidenceAllocation_with_poleTilted_deLaValleePoussin_deficit
  refine ⟨c, hc, K, hK, fun r F hr hF hFc hodd hsupp => ?_⟩
  rw [fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp (lt_add_one r)]
  have h := halloc r (r + 1) F hr (lt_add_one r) hF hFc hodd hsupp
  linarith

/-! ## §2. The Arithmetic Test Class: Bounded-Dirichlet-Ratio and Sub-Envelope Cones -/

/-- **The bounded-Dirichlet-ratio test cone** `BoundedDirichletCone Λ F`: tests whose derivative
energy is at most `Λ²` times their `L²` mass. -/
def BoundedDirichletCone (Λ : ℝ) (F : ℝ → ℝ) : Prop :=
  (∫ x, deriv F x ^ 2) ≤ Λ ^ 2 * ∫ x, F x ^ 2

/-- **The sub-envelope arithmetic Sobolev cone** `SubEnvelopeDirichletCone c r F`: tests at aperture
`r` whose Dirichlet ratio is at most `2 exp(c√r)`, so that half of the de la Vallée Poussin saving
absorbs the derivative reserve automatically. -/
def SubEnvelopeDirichletCone (c r : ℝ) (F : ℝ → ℝ) : Prop :=
  (∫ x, deriv F x ^ 2) ≤ 2 * Real.exp (c * Real.sqrt r) * ∫ x, F x ^ 2

/-- Every bounded-Dirichlet-ratio cone `BoundedDirichletCone Λ` is contained in the sub-envelope
cone `SubEnvelopeDirichletCone c r` as soon as `Λ² ≤ 2 exp(c√r)` (and in particular for all
`Λ² ≤ 2` at every aperture `r ≥ 0`). -/
theorem subEnvelopeDirichletCone_of_boundedDirichletCone {Λ c r : ℝ} {F : ℝ → ℝ}
    (hΛ : Λ ^ 2 ≤ 2 * Real.exp (c * Real.sqrt r)) (hF : BoundedDirichletCone Λ F) :
    SubEnvelopeDirichletCone c r F := by
  unfold SubEnvelopeDirichletCone BoundedDirichletCone at *
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact hF.trans (mul_le_mul_of_nonneg_right hΛ hI0)

/-- **Pure-`L²` de la Vallée Poussin bound for the complete ledger on the sub-envelope arithmetic
cone.** With universal constants `c > 0` and `K > 0`, for every aperture `r > 0` and every real odd
`F ∈ C²_c[−r, r]` in `SubEnvelopeDirichletCone c r F`, both `|reflectedPrimePolarCost F r|` and the
complete ledger deficit `−fullZeroForm F` are bounded in pure `L²` mass by
`K e^r exp(−c√r) ∫ F²`. -/
theorem exists_fullZeroForm_ge_deLaValleePoussin_of_subEnvelopeDirichletCone :
    ∃ c > 0, ∃ K > 0, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
      ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      SubEnvelopeDirichletCone c r F →
      |reflectedPrimePolarCost F r| ≤
        K * Real.exp r * Real.exp (-c * Real.sqrt r) * (∫ x, F x ^ 2) ∧
      -(K * Real.exp r * Real.exp (-c * Real.sqrt r) * ∫ x, F x ^ 2) ≤ fullZeroForm F := by
  obtain ⟨c, hc, K₀, hK₀, hcost⟩ := exists_abs_reflectedPrimePolarCost_le_sub_envelope_of_dirichlet_le
  set K := K₀ + 27 / 5 * Real.exp (c ^ 2 / 4)
  have hK : 0 < K := by positivity
  refine ⟨c, hc, K, hK, fun r F hr hF hFc hodd hsupp hcone => ?_⟩
  have hc1 := hcost r F hr (hF.of_le (by norm_num)) hFc hodd hsupp hcone
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hK₀_le : K₀ ≤ K := by simp only [K]; linarith [Real.exp_pos (c ^ 2 / 4)]
  have hcost_K : |reflectedPrimePolarCost F r| ≤
      K * Real.exp r * Real.exp (-c * Real.sqrt r) * ∫ x, F x ^ 2 := by
    refine hc1.trans (mul_le_mul_of_nonneg_right ?_ hI0)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK₀_le (Real.exp_nonneg _)) (Real.exp_nonneg _)
  refine ⟨hcost_K, ?_⟩
  rw [fullZeroForm_eq_archimedeanLedgerBudget_sub_reflectedPrimePolarCost
    hF hFc hodd hr hsupp (lt_add_one r)]
  have hbud := archimedeanLedgerBudget_ge_neg_const_mul_sq hF hFc hsupp (lt_add_one r)
  have hsq_r : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hcomplete : 0 ≤ c ^ 2 / 4 + r - c * Real.sqrt r := by
    have := sq_nonneg (Real.sqrt r - c / 2)
    linarith
  have hexp_floor : 1 ≤ Real.exp (c ^ 2 / 4) * (Real.exp r * Real.exp (-c * Real.sqrt r)) := by
    rw [← Real.exp_add, ← Real.exp_add,
      show c ^ 2 / 4 + (r + -c * Real.sqrt r) = c ^ 2 / 4 + r - c * Real.sqrt r by ring]
    exact Real.one_le_exp hcomplete
  have hrem' : 27 / 5 * ∫ x, F x ^ 2 ≤
      (27 / 5 * Real.exp (c ^ 2 / 4)) * Real.exp r * Real.exp (-c * Real.sqrt r) *
        ∫ x, F x ^ 2 := by
    calc 27 / 5 * ∫ x, F x ^ 2
        = 27 / 5 * 1 * ∫ x, F x ^ 2 := by ring
      _ ≤ 27 / 5 * (Real.exp (c ^ 2 / 4) * (Real.exp r * Real.exp (-c * Real.sqrt r))) *
            ∫ x, F x ^ 2 := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp_floor (by norm_num)) hI0
      _ = (27 / 5 * Real.exp (c ^ 2 / 4)) * Real.exp r * Real.exp (-c * Real.sqrt r) *
            ∫ x, F x ^ 2 := by ring
  have hc_upper := (le_abs_self _).trans hc1
  have hsum_K : K * Real.exp r * Real.exp (-c * Real.sqrt r) * (∫ x, F x ^ 2) =
      K₀ * Real.exp r * Real.exp (-c * Real.sqrt r) * (∫ x, F x ^ 2) +
      (27 / 5 * Real.exp (c ^ 2 / 4)) * Real.exp r * Real.exp (-c * Real.sqrt r) *
        (∫ x, F x ^ 2) := by
    simp only [K]; ring
  linarith

/-- Uniform derivative energy bound for a real two-bump difference test `g(u + v/2) − g(u − v/2)`:
its Dirichlet energy is at most `4 ∫ (g′)²` for every lag `v ∈ ℝ`. -/
theorem integral_deriv_twoBump_diff_sq_le {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : ℝ) :
    ∫ u, deriv (fun x => g (x + v / 2) - g (x - v / 2)) u ^ 2 ≤ 4 * ∫ u, deriv g u ^ 2 := by
  have hgd_cont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hgd_cs : HasCompactSupport (deriv g) := hgc.deriv
  have hgd_sq_int : Integrable (fun u => deriv g u ^ 2) volume :=
    ((hgd_cont.mul hgd_cont).integrable_of_hasCompactSupport hgd_cs.mul_left).congr
      (Filter.Eventually.of_forall fun u => (sq (deriv g u)).symm)
  have hderiv : ∀ u, deriv (fun x => g (x + v / 2) - g (x - v / 2)) u =
      deriv g (u + v / 2) - deriv g (u - v / 2) := fun u => by
    have hd1 : HasDerivAt (fun x => g (x + v / 2)) (deriv g (u + v / 2)) u :=
      HasDerivAt.comp_add_const u (v / 2) ((hg.differentiable one_ne_zero (u + v / 2)).hasDerivAt)
    have hd2 : HasDerivAt (fun x => g (x - v / 2)) (deriv g (u - v / 2)) u :=
      HasDerivAt.comp_sub_const u (v / 2) ((hg.differentiable one_ne_zero (u - v / 2)).hasDerivAt)
    exact (hd1.sub hd2).deriv
  have hgd1_int : Integrable (fun u => deriv g (u + v / 2) ^ 2) volume :=
    hgd_sq_int.comp_add_right (v / 2)
  have hgd2_int : Integrable (fun u => deriv g (u - v / 2) ^ 2) volume :=
    hgd_sq_int.comp_sub_right (v / 2)
  have hdiff_int : Integrable (fun u => (deriv g (u + v / 2) - deriv g (u - v / 2)) ^ 2) volume := by
    have hcont : Continuous fun u => deriv g (u + v / 2) - deriv g (u - v / 2) :=
      (hgd_cont.comp (continuous_id.add continuous_const)).sub
        (hgd_cont.comp (continuous_id.sub continuous_const))
    have hcs1 : HasCompactSupport fun u => deriv g (u + v / 2) :=
      hgd_cs.comp_homeomorph (Homeomorph.addRight (v / 2))
    have hcs2 : HasCompactSupport fun u => deriv g (u - v / 2) :=
      hgd_cs.comp_homeomorph (Homeomorph.subRight (v / 2))
    exact ((hcont.mul hcont).integrable_of_hasCompactSupport (hcs1.sub hcs2).mul_left).congr
      (Filter.Eventually.of_forall fun u => (sq _).symm)
  have hcongr : (∫ u, deriv (fun x => g (x + v / 2) - g (x - v / 2)) u ^ 2) =
      ∫ u, (deriv g (u + v / 2) - deriv g (u - v / 2)) ^ 2 := by
    congr 1; funext u; rw [hderiv u]
  rw [hcongr]
  have hmono : (∫ u, (deriv g (u + v / 2) - deriv g (u - v / 2)) ^ 2) ≤
      ∫ u, (2 * deriv g (u + v / 2) ^ 2 + 2 * deriv g (u - v / 2) ^ 2) := by
    refine integral_mono hdiff_int ((hgd1_int.const_mul 2).add (hgd2_int.const_mul 2)) fun u => ?_
    have := sq_nonneg (deriv g (u + v / 2) + deriv g (u - v / 2))
    linarith
  rw [integral_add (hgd1_int.const_mul 2) (hgd2_int.const_mul 2),
    integral_const_mul, integral_const_mul,
    integral_add_right_eq_self (fun u => deriv g u ^ 2) (v / 2),
    integral_sub_right_eq_self (fun u => deriv g u ^ 2) (v / 2)] at hmono
  linarith

/-- The lag-independent regularity ratio `bumpDirichletRatio w` of the unmodulated bump
`modScaledBump w 0`. -/
def bumpDirichletRatio (w : ℝ) : ℝ :=
  Real.sqrt
    ((2 * ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2) /
      ∫ t, ‖modScaledBump w 0 t‖ ^ 2)

theorem bumpDirichletRatio_nonneg (w : ℝ) : 0 ≤ bumpDirichletRatio w :=
  Real.sqrt_nonneg _

/-- **The arithmetic lag family belongs to a fixed-regularity Dirichlet cone uniformly across all
lags.** For every bump width `w > 0` and every disjoint lag `v > 2w`, the real difference test
`F_v(u) = (twoBump (modScaledBump w 0) v (−1) u).re` lies in
`BoundedDirichletCone (bumpDirichletRatio w)`, with `bumpDirichletRatio w` independent of `v`. -/
theorem boundedDirichletCone_twoBump_modScaledBump_re {w v : ℝ} (hw : 0 < w) (hv : 2 * w < v) :
    BoundedDirichletCone (bumpDirichletRatio w)
      (fun u => (twoBump (modScaledBump w 0) v (-1) u).re) := by
  unfold BoundedDirichletCone bumpDirichletRatio
  set f : ℝ → ℂ := twoBump (modScaledBump w 0) v (-1) with hf_def
  have hg : ContDiff ℝ 2 (fun u => (modScaledBump w 0 u).re) :=
    Complex.reCLM.contDiff.comp (contDiff_modScaledBump_two w 0)
  have hgc : HasCompactSupport (fun u => (modScaledBump w 0 u).re) :=
    (hasCompactSupport_of_support_subset_abs (modScaledBump_support hw 0)).comp_left
      (g := fun z : ℂ => z.re) (by simp)
  have him0 : (fun u => (f u).im) = fun _ => 0 := by
    funext u
    exact Complex.conj_eq_iff_im.mp (twoBump_modScaledBump_zero_conj w v u)
  have hF_mass : (∫ u, (f u).re ^ 2) = ∫ u, ‖f u‖ ^ 2 := by
    congr 1; funext u
    have hu : (f u).im = 0 := congrFun him0 u
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hu]
    ring
  have hRe_eq : (fun u => (f u).re) =
      fun u => (modScaledBump w 0 (u + v / 2)).re - (modScaledBump w 0 (u - v / 2)).re := by
    funext u
    rw [hf_def, twoBump_apply, neg_one_mul, ← sub_eq_add_neg, Complex.sub_re]
  have hF_deriv_sq : (∫ u, deriv (fun x => (f x).re) u ^ 2) ≤
      4 * ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2 := by
    rw [hRe_eq]
    exact integral_deriv_twoBump_diff_sq_le (hg.of_le (by norm_num)) hgc v
  have hpos : 0 < ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := integral_norm_sq_modScaledBump_pos hw
  have hd0 : 0 ≤ ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hsq : Real.sqrt
        ((2 * ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2) /
          ∫ t, ‖modScaledBump w 0 t‖ ^ 2) ^ 2 =
      (2 * ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2) /
        ∫ t, ‖modScaledBump w 0 t‖ ^ 2 :=
    Real.sq_sqrt (div_nonneg (by positivity) hpos.le)
  rw [hsq, hF_mass, integral_norm_sq_twoBump_modScaledBump_eq hw hv]
  have hrhs : (2 * ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2) /
        (∫ t, ‖modScaledBump w 0 t‖ ^ 2) *
        (2 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2) =
      4 * ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2 := by
    have hne : (∫ t, ‖modScaledBump w 0 t‖ ^ 2) ≠ 0 := hpos.ne'
    field_simp
    ring
  rw [hrhs]
  exact hF_deriv_sq

/-! ## §3. Forward Bridge: From Zero Width `zetaZeroWidth` to the Compensated Remainder of the Full Ledger -/

/-- **Pointwise exponential bound on `2 e^{−s/2} |chebyshevTwoPoleDefect s|` above `zetaZeroWidth`.**
For every rate `σ > zetaZeroWidth`, there exists `C > 0` such that for all `s ≥ 0`,
`2 e^{−s/2} |chebyshevTwoPoleDefect s| ≤ C e^{σ s}`. -/
theorem exists_exp_neg_half_mul_abs_chebyshevTwoPoleDefect_le_of_zetaZeroWidth_lt {σ : ℝ}
    (hσ : zetaZeroWidth < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
      2 * Real.exp (-s / 2) * |chebyshevTwoPoleDefect s| ≤ C * Real.exp (σ * s) := by
  have hσ0 : 0 < σ := lt_of_le_of_lt zetaZeroWidth_nonneg hσ
  obtain ⟨C₀, hC₀0, hE⟩ :=
    exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound zetaZeroWidth_nonneg hσ
      xiZeroHalfPlaneBound_zetaZeroWidth
  refine ⟨2 * (C₀ + 2), by positivity, fun s hs => ?_⟩
  have hnorm := hE s hs
  rw [normalizedLogError, SignedPrimePolar.logError, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_sub_comm] at hnorm
  have hdef : chebyshevTwoPoleDefect s = (Real.exp s - Chebyshev.psi (Real.exp s)) + (s - 1) := by
    rw [chebyshevTwoPoleDefect_eq_error_add, ArithmeticIncidencePositivity.chebyshevError,
      lagChebyshev_eq_chebyshevPsi]
  have hlin : Real.exp (-s / 2) * |s - 1| ≤ 2 * Real.exp (σ * s) := by
    have h1 : |s - 1| ≤ s + 2 := by rw [abs_le]; constructor <;> linarith
    have h2 : s / 2 + 1 ≤ Real.exp (s / 2) := Real.add_one_le_exp (s / 2)
    have h3 : s + 2 ≤ 2 * Real.exp (s / 2) := by linarith
    have h4 : Real.exp (-s / 2) * |s - 1| ≤ Real.exp (-s / 2) * (2 * Real.exp (s / 2)) :=
      mul_le_mul_of_nonneg_left (h1.trans h3) (Real.exp_pos _).le
    have h5 : Real.exp (-s / 2) * (2 * Real.exp (s / 2)) = 2 := by
      rw [mul_left_comm, ← Real.exp_add, show -s / 2 + s / 2 = 0 by ring, Real.exp_zero, mul_one]
    have h6 : (1 : ℝ) ≤ Real.exp (σ * s) := Real.one_le_exp (by positivity)
    linarith
  rw [hdef]
  have htri : |Real.exp s - Chebyshev.psi (Real.exp s) + (s - 1)| ≤
      |Real.exp s - Chebyshev.psi (Real.exp s)| + |s - 1| := abs_add_le _ _
  have hm := mul_le_mul_of_nonneg_left htri (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-s / 2))
  calc 2 * Real.exp (-s / 2) * |Real.exp s - Chebyshev.psi (Real.exp s) + (s - 1)|
      ≤ 2 * (Real.exp (-s / 2) * |Real.exp s - Chebyshev.psi (Real.exp s)|) +
          2 * (Real.exp (-s / 2) * |s - 1|) := by linarith
    _ ≤ 2 * (C₀ * Real.exp (σ * s)) + 2 * (2 * Real.exp (σ * s)) := by linarith
    _ = 2 * (C₀ + 2) * Real.exp (σ * s) := by ring

/-- **Horizon `L¹` bound on `2 e^{−s/2} |chebyshevTwoPoleDefect s|` above `zetaZeroWidth` (with no
factor `r`).** For every `σ > zetaZeroWidth`, there exists `K > 0` such that for all `r > 0`,
`∫_{s ∈ (0, 2r]} 2 e^{−s/2} |chebyshevTwoPoleDefect s| ds ≤ K e^{2σ r}`. -/
theorem exists_integral_Ioc_exp_mul_abs_chebyshevTwoPoleDefect_le_of_zetaZeroWidth_lt {σ : ℝ}
    (hσ : zetaZeroWidth < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r →
      (∫ s in Ioc (0 : ℝ) (2 * r), 2 * Real.exp (-s / 2) * |chebyshevTwoPoleDefect s|) ≤
        K * Real.exp (2 * σ * r) := by
  set β := (zetaZeroWidth + σ) / 2 with hβ_def
  have hβ : zetaZeroWidth < β := by rw [hβ_def]; linarith
  have hβ0 : 0 < β := lt_of_le_of_lt zetaZeroWidth_nonneg hβ
  have hδ : 0 < σ - β := by rw [hβ_def]; linarith
  obtain ⟨C, hC0, hpt⟩ :=
    exists_exp_neg_half_mul_abs_chebyshevTwoPoleDefect_le_of_zetaZeroWidth_lt hβ
  refine ⟨C / (σ - β), by positivity, fun r hr => ?_⟩
  have h2r : 0 < 2 * r := by linarith
  set M := C * Real.exp (2 * β * r)
  have hM : ∀ s ∈ Ioc (0 : ℝ) (2 * r),
      2 * Real.exp (-s / 2) * |chebyshevTwoPoleDefect s| ≤ M := fun s hs => by
    refine (hpt s hs.1.le).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hs.2])) hC0.le
  have hint := integrableOn_Ioc_exp_mul_abs_chebyshevTwoPoleDefect h2r
  have hmono : (∫ s in Ioc (0 : ℝ) (2 * r), 2 * Real.exp (-s / 2) * |chebyshevTwoPoleDefect s|) ≤
      ∫ _s in Ioc (0 : ℝ) (2 * r), M :=
    setIntegral_mono_on hint (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      measurableSet_Ioc hM
  have hconst : (∫ _s in Ioc (0 : ℝ) (2 * r), M) = 2 * r * M := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal h2r.le, smul_eq_mul]
  have hlin_exp : 2 * r ≤ 1 / (σ - β) * Real.exp (2 * (σ - β) * r) := by
    have h1 := Real.add_one_le_exp (2 * (σ - β) * r)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
    linarith
  calc (∫ s in Ioc (0 : ℝ) (2 * r), 2 * Real.exp (-s / 2) * |chebyshevTwoPoleDefect s|)
      ≤ 2 * r * (C * Real.exp (2 * β * r)) := hmono.trans hconst.le
    _ ≤ (1 / (σ - β) * Real.exp (2 * (σ - β) * r)) * (C * Real.exp (2 * β * r)) :=
        mul_le_mul_of_nonneg_right hlin_exp (by positivity)
    _ = C / (σ - β) * (Real.exp (2 * (σ - β) * r) * Real.exp (2 * β * r)) := by ring
    _ = C / (σ - β) * Real.exp (2 * σ * r) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Horizon `L¹` bound on the second-order critical-scale prefix `2 e^{−s/2} |D(s) + s²/2 − s|`
above `zetaZeroWidth` (with no factor `r`).** For every `σ > zetaZeroWidth`, there exists `K > 0`
such that for all `r > 0`,
`∫_{s ∈ (0, 2r]} 2 e^{−s/2} |criticalScalePrefix s + s²/2 − s| ds ≤ K e^{2σ r}`. -/
theorem exists_integral_Ioc_exp_mul_abs_criticalScalePrefix_le_of_zetaZeroWidth_lt {σ : ℝ}
    (hσ : zetaZeroWidth < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r →
      (∫ s in Ioc (0 : ℝ) (2 * r),
        2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s|) ≤
        K * Real.exp (2 * σ * r) := by
  set β := (zetaZeroWidth + σ) / 2 with hβ_def
  have hβ : zetaZeroWidth < β := by rw [hβ_def]; linarith
  have hδ : 0 < σ - β := by rw [hβ_def]; linarith
  obtain ⟨K₀, hK₀0, hL1⟩ :=
    exists_integral_Ioc_exp_mul_abs_chebyshevTwoPoleDefect_le_of_zetaZeroWidth_lt hβ
  refine ⟨K₀ / (σ - β), by positivity, fun r hr => ?_⟩
  have hdom := integral_Ioc_exp_mul_abs_criticalScalePrefix_le_two_mul_r hr.le
  have h1 := hL1 r hr
  have hlin_exp : 2 * r ≤ 1 / (σ - β) * Real.exp (2 * (σ - β) * r) := by
    have h2 := Real.add_one_le_exp (2 * (σ - β) * r)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
    linarith
  calc (∫ s in Ioc (0 : ℝ) (2 * r),
          2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s|)
      ≤ 2 * r * (K₀ * Real.exp (2 * β * r)) :=
        hdom.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    _ ≤ (1 / (σ - β) * Real.exp (2 * (σ - β) * r)) * (K₀ * Real.exp (2 * β * r)) :=
        mul_le_mul_of_nonneg_right hlin_exp (by positivity)
    _ = K₀ / (σ - β) * (Real.exp (2 * (σ - β) * r) * Real.exp (2 * β * r)) := by ring
    _ = K₀ / (σ - β) * Real.exp (2 * σ * r) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **First-order Sobolev bound on `|reflectedPrimePolarCost F r|` above `zetaZeroWidth`.**
For every `σ > zetaZeroWidth`, there exists `K > 0` such that for all `r > 0` and all real odd
`F ∈ C¹_c[−r, r]`,
`|reflectedPrimePolarCost F r| ≤ K e^{2σ r} (∫ F² + ½ ∫ (deriv F)²)`. -/
theorem exists_abs_reflectedPrimePolarCost_le_firstOrderSobolev_of_zetaZeroWidth_lt {σ : ℝ}
    (hσ : zetaZeroWidth < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 1 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤
        K * Real.exp (2 * σ * r) * ((∫ x, F x ^ 2) + (1 / 2) * ∫ x, deriv F x ^ 2) := by
  obtain ⟨K, hK0, hL1⟩ :=
    exists_integral_Ioc_exp_mul_abs_chebyshevTwoPoleDefect_le_of_zetaZeroWidth_lt hσ
  refine ⟨K, hK0, fun r F hr hF hFc hodd hsupp => ?_⟩
  have h1 := abs_reflectedPrimePolarCost_le_chebyshevTwoPoleDefect_L1_mul_sobolev hF hFc hodd hr hsupp
  have h2 := hL1 r hr
  have hsob : 0 ≤ (∫ x, F x ^ 2) + (1 / 2) * ∫ x, deriv F x ^ 2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _)
      (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hsob)

/-- **Second-order pole-tilted Sobolev bound on `|reflectedPrimePolarCost F r|` above
`zetaZeroWidth`.** For every `σ > zetaZeroWidth`, there exists `K > 0` such that for all `r > 0`
and all real odd `F ∈ C²_c[−r, r]`,
`|reflectedPrimePolarCost F r| ≤ K e^{2σ r} ((1/4) ∫ F² + ∫ (deriv F)²)`. -/
theorem exists_abs_reflectedPrimePolarCost_le_poleTiltedSobolev_of_zetaZeroWidth_lt {σ : ℝ}
    (hσ : zetaZeroWidth < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤
        K * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
  obtain ⟨K, hK0, hL1⟩ :=
    exists_integral_Ioc_exp_mul_abs_criticalScalePrefix_le_of_zetaZeroWidth_lt hσ
  refine ⟨K, hK0, fun r F hr hF hFc hodd hsupp => ?_⟩
  have h1 := abs_reflectedPrimePolarCost_le_criticalScalePrefix_L1_mul_sobolev hF hFc hodd hr hsupp
  have h2 := hL1 r hr
  have hsob : 0 ≤ (1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2 :=
    add_nonneg (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hsob)

/-- **The pole-tilted Sobolev-graded global incidence allocation condition at rate `2σ`.**
The odd strip costs and the pole charge are paid by `surplusPool + crossingPotentialTerm +
evenStripGain + gaugeRemainder` up to `C e^{2σ r} ((1/4) ∫ F² + ∫ (deriv F)²)` at every aperture
`0 < r < R`. -/
def SobolevGradedIncidenceAllocation (σ C : ℝ) : Prop :=
  ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R → ContDiff ℝ 2 F → HasCompactSupport F →
    (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
    (∑ n ∈ relevantShifts r, oddStripCost F r n) + poleCharge F ≤
      surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F +
        (∑ n ∈ relevantShifts r, evenStripGain F r n) +
        gaugeRemainder (aperturePlateau r R) F +
        C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)

/-- Every upper bound `reflectedPrimePolarCost F r ≤ C e^{2σ r} ((1/4) ∫ F² + ∫ (deriv F)²)` at a
nonnegative rate `σ ≥ 0` implies `SobolevGradedIncidenceAllocation σ (max C 0 + 108 / 5)` for the
complete ledger (retaining `evenStripGain`, `surplusPool`, `crossingPotentialTerm`, and
`gaugeRemainder`). -/
theorem sobolevGradedIncidenceAllocation_of_reflectedPrimePolarCost_le {σ C : ℝ} (hσ : 0 ≤ σ)
    (hcost : ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      reflectedPrimePolarCost F r ≤
        C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) :
    SobolevGradedIncidenceAllocation σ (max C 0 + 108 / 5) := by
  intro r R F hr hrR hF hFc hodd hsupp
  have hc1 := hcost r F hr hF hFc hodd hsupp
  unfold reflectedPrimePolarCost at hc1
  have hP0 : ∀ y, 0 ≤ aperturePlateau r R y :=
    fun y => plateauGauge_nonneg R (R - r) y
  have hpool := surplusPool_nonneg (F := F) hP0
  have hcross := crossingPotentialTerm_nonneg (F := F) hP0
  have hrem := gaugeRemainder_ge_neg_const_mul_sq hF hFc hsupp hrR
  have hexp1 : 1 ≤ Real.exp (2 * σ * r) := Real.one_le_exp (by positivity)
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hd0 : 0 ≤ ∫ x, deriv F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsob0 : 0 ≤ (1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2 := by positivity
  have hc_max : C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) ≤
      max C 0 * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _)) hsob0
  have hrem' : 27 / 5 * ∫ x, F x ^ 2 ≤
      (108 / 5) * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
    calc 27 / 5 * ∫ x, F x ^ 2
        = (108 / 5) * 1 * ((1 / 4) * ∫ x, F x ^ 2) := by ring
      _ ≤ (108 / 5) * Real.exp (2 * σ * r) *
            ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hexp1 (by norm_num))
            (by linarith) (by positivity) (by positivity)
  have hadd : (max C 0 + 108 / 5) * Real.exp (2 * σ * r) *
        ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) =
      max C 0 * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) +
      (108 / 5) * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
    ring
  linarith

/-- **Forward bridge to `SobolevGradedIncidenceAllocation`.** For every `σ > zetaZeroWidth`, there
exists `K > 0` such that `SobolevGradedIncidenceAllocation σ K` holds across all apertures
`0 < r < R` and all real odd `F ∈ C²_c[−r, r]`. -/
theorem exists_sobolevGradedIncidenceAllocation_of_zetaZeroWidth_lt {σ : ℝ}
    (hσ : zetaZeroWidth < σ) :
    ∃ K : ℝ, 0 < K ∧ SobolevGradedIncidenceAllocation σ K := by
  have hσ0 : 0 ≤ σ := le_trans zetaZeroWidth_nonneg hσ.le
  obtain ⟨C, hC0, hcost⟩ :=
    exists_abs_reflectedPrimePolarCost_le_poleTiltedSobolev_of_zetaZeroWidth_lt hσ
  refine ⟨max C 0 + 108 / 5, by positivity,
    sobolevGradedIncidenceAllocation_of_reflectedPrimePolarCost_le hσ0
      fun r F hr hF hFc hodd hsupp => (le_abs_self _).trans (hcost r F hr hF hFc hodd hsupp)⟩

/-- **Forward bridge to the pole-tilted Sobolev floor of `fullZeroForm`.** For every
`σ > zetaZeroWidth`, there exists `K > 0` such that for all `r > 0` and all real odd
`F ∈ C²_c[−r, r]`,
`−(K e^{2σ r} ((1/4) ∫ F² + ∫ (deriv F)²)) ≤ fullZeroForm F`. -/
theorem exists_fullZeroForm_ge_poleTiltedSobolev_of_zetaZeroWidth_lt {σ : ℝ}
    (hσ : zetaZeroWidth < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(K * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) ≤
        fullZeroForm F := by
  obtain ⟨K, hK0, halloc⟩ := exists_sobolevGradedIncidenceAllocation_of_zetaZeroWidth_lt hσ
  refine ⟨K, hK0, fun r F hr hF hFc hodd hsupp => ?_⟩
  rw [fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp (lt_add_one r)]
  have h := halloc r (r + 1) F hr (lt_add_one r) hF hFc hodd hsupp
  linarith

/-- **Forward bridge on every bounded-Dirichlet-ratio test cone `BoundedDirichletCone Λ`.**
For every `σ > zetaZeroWidth` and every `Λ ≥ 0`, there exists `C > 0` such that for all `r > 0`
and all real odd `F ∈ C²_c[−r, r]` with `BoundedDirichletCone Λ F`, the complete ledger satisfies
the pure-`L²` floor `−(C e^{2σ r} ∫ F²) ≤ fullZeroForm F`. -/
theorem exists_boundedDirichletCone_fullZeroForm_floor_of_zetaZeroWidth_lt {σ Λ : ℝ}
    (hσ : zetaZeroWidth < σ) (_ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) → BoundedDirichletCone Λ F →
      -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F := by
  obtain ⟨K, hK0, hfloor⟩ := exists_fullZeroForm_ge_poleTiltedSobolev_of_zetaZeroWidth_lt hσ
  refine ⟨K * (1 / 4 + Λ ^ 2), by positivity, fun r F hr hF hFc hodd hsupp hcone => ?_⟩
  have h1 := hfloor r F hr hF hFc hodd hsupp
  unfold BoundedDirichletCone at hcone
  have h2 : K * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) ≤
      K * (1 / 4 + Λ ^ 2) * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by
    calc K * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)
        ≤ K * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + Λ ^ 2 * ∫ x, F x ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = K * (1 / 4 + Λ ^ 2) * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by ring
  linarith

/-! ## §4. Converse Bridge: From the Compensated Remainder of the Full Ledger to the Zero-Free Strip -/

/-- **Converse bridge on bounded-Dirichlet-ratio cones (`BoundedDirichletCone Λ`).**
If `0 ≤ σ` and for every regularity constant `Λ ≥ 0` there exists `C : ℝ` such that every real odd
`F ∈ C²_c[−r, r]` in `BoundedDirichletCone Λ F` satisfies
`−(C e^{2σ r} ∫ F²) ≤ fullZeroForm F`, then `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_boundedDirichletCone_fullZeroForm_floor {σ : ℝ} (hσ : 0 ≤ σ)
    (hfloor : ∀ Λ : ℝ, 0 ≤ Λ → ∃ C : ℝ, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
      ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      BoundedDirichletCone Λ F → -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F) :
    zetaZeroWidth ≤ σ := by
  obtain ⟨E, hE, hlaw⟩ := zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp
  obtain ⟨w, ⟨hw, hwlt⟩, hwE⟩ :=
    exists_mem_Ioo_notMem_of_countable (half_pos (Real.log_pos one_lt_two)) hE
  have hw2 : 2 * w < Real.log 2 := by linarith
  refine (hlaw w hw hw2 hwE σ hσ).mpr ?_
  obtain ⟨C, hC⟩ := hfloor (bumpDirichletRatio w) (bumpDirichletRatio_nonneg w)
  refine ⟨2 * max C 0 * Real.exp (2 * σ * w) * ∫ t, ‖modScaledBump w 0 t‖ ^ 2, 2 * w + 1,
    by positivity, fun v hv => ?_⟩
  have hvw : 2 * w < v := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hr : 0 < v / 2 + w := by linarith
  set f : ℝ → ℂ := twoBump (modScaledBump w 0) v (-1) with hf_def
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]
  have hfc : HasCompactSupport f :=
    hasCompactSupport_twoBump
      (hasCompactSupport_of_support_subset_abs (modScaledBump_support hw 0)) v (-1)
  have hfs : tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) :=
    tsupport_twoBump_modScaledBump_subset hw hv0
  have hodd : ∀ x, f (-x) = -f x := twoBump_modScaledBump_zero_neg w v
  have hzero : ∀ x, v / 2 + w < |x| → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have hmem' := hfs hmem
      rw [Set.mem_Icc] at hmem'
      exact absurd (abs_le.mpr hmem') (not_le.mpr hx)
  have hRe : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hRec : HasCompactSupport (fun u => (f u).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have him0 : (fun u => (f u).im) = fun _ => 0 := by
    funext u
    exact Complex.conj_eq_iff_im.mp (twoBump_modScaledBump_zero_conj w v u)
  have hcone_re : BoundedDirichletCone (bumpDirichletRatio w) (fun u => (f u).re) :=
    boundedDirichletCone_twoBump_modScaledBump_re hw hvw
  have hcone_zero : BoundedDirichletCone (bumpDirichletRatio w) (fun _ => 0) := by
    simp [BoundedDirichletCone]
  have hflF := hC (v / 2 + w) (fun u => (f u).re) hr hRe hRec
    (fun x => by simp [hodd x]) (fun x hx => by simp [hzero x hx]) hcone_re
  have hfl0 := hC (v / 2 + w) (fun _ => 0) hr contDiff_const HasCompactSupport.zero
    (fun _ => by simp) (fun _ _ => rfl) hcone_zero
  have hfl0' : 0 ≤ fullZeroForm (fun u => (f u).im) := by
    rw [him0]
    simpa using hfl0
  have hF_mass : (∫ u, (f u).re ^ 2) = ∫ u, ‖f u‖ ^ 2 := by
    congr 1; funext u
    have hu : (f u).im = 0 := congrFun him0 u
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hu]
    ring
  have hmass0 : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hW : -(max C 0 * Real.exp (2 * σ * (v / 2 + w)) * ∫ u, ‖f u‖ ^ 2) ≤
      (zetaZeroConfig.W f f).re := by
    rw [zeta_W_re_eq_fullZeroForm_re_add_im hf hfc]
    rw [hF_mass] at hflF
    have hC_le : C * Real.exp (2 * σ * (v / 2 + w)) * (∫ u, ‖f u‖ ^ 2) ≤
        max C 0 * Real.exp (2 * σ * (v / 2 + w)) * ∫ u, ‖f u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _)) hmass0
    linarith [hflF, hfl0', hC_le]
  rw [integral_norm_sq_twoBump_modScaledBump_eq hw hvw,
    zeta_W_eq_literatureRHS (f := f) hf hfc,
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv0] at hW
  have hexp : Real.exp (2 * σ * (v / 2 + w)) = Real.exp (σ * v) * Real.exp (2 * σ * w) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp] at hW
  calc -(2 * max C 0 * Real.exp (2 * σ * w) * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * Real.exp (σ * v))
      = -(max C 0 * (Real.exp (σ * v) * Real.exp (2 * σ * w)) *
          (2 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2)) := by ring
    _ ≤ _ := hW

/-- **Converse bridge from a pole-tilted Sobolev floor on `fullZeroForm`.**
If `0 ≤ σ` and every real odd `F ∈ C²_c[−r, r]` satisfies
`−(C e^{2σ r} ((1/4) ∫ F² + ∫ (deriv F)²)) ≤ fullZeroForm F`, then `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_poleTiltedSobolev_fullZeroForm_floor {σ C : ℝ} (hσ : 0 ≤ σ)
    (hfloor : ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) ≤
        fullZeroForm F) :
    zetaZeroWidth ≤ σ := by
  refine zetaZeroWidth_le_of_boundedDirichletCone_fullZeroForm_floor hσ fun Λ _ => ?_
  refine ⟨max C 0 * (1 / 4 + Λ ^ 2), fun r F hr hF hFc hodd hsupp hcone => ?_⟩
  have h1 := hfloor r F hr hF hFc hodd hsupp
  unfold BoundedDirichletCone at hcone
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hd0 : 0 ≤ ∫ x, deriv F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsob0 : 0 ≤ (1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2 := by positivity
  have h2 : C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) ≤
      max C 0 * (1 / 4 + Λ ^ 2) * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by
    calc C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)
        ≤ max C 0 * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _)) hsob0
      _ ≤ max C 0 * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + Λ ^ 2 * ∫ x, F x ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = max C 0 * (1 / 4 + Λ ^ 2) * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by ring
  linarith

/-- **Converse bridge from `SobolevGradedIncidenceAllocation`.**
If `0 ≤ σ` and `SobolevGradedIncidenceAllocation σ C` holds, then `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_sobolevGradedIncidenceAllocation {σ C : ℝ} (hσ : 0 ≤ σ)
    (h : SobolevGradedIncidenceAllocation σ C) : zetaZeroWidth ≤ σ := by
  refine zetaZeroWidth_le_of_poleTiltedSobolev_fullZeroForm_floor (C := C) hσ
    fun r F hr hF hFc hodd hsupp => ?_
  rw [fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp (lt_add_one r)]
  have hal := h r (r + 1) F hr (lt_add_one r) hF hFc hodd hsupp
  linarith

/-- **Converse bridge from an upper bound on `reflectedPrimePolarCost F r`.**
If `0 ≤ σ` and every real odd `F ∈ C²_c[−r, r]` satisfies
`reflectedPrimePolarCost F r ≤ C e^{2σ r} ((1/4) ∫ F² + ∫ (deriv F)²)`, then `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_reflectedPrimePolarCost_le_poleTiltedSobolev {σ C : ℝ} (hσ : 0 ≤ σ)
    (hcost : ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      reflectedPrimePolarCost F r ≤
        C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) :
    zetaZeroWidth ≤ σ :=
  zetaZeroWidth_le_of_sobolevGradedIncidenceAllocation hσ
    (sobolevGradedIncidenceAllocation_of_reflectedPrimePolarCost_le hσ hcost)

/-! ## §5. Exact Equivalences: Sub-Trivial Exponents `< 1/2`, Zero-Free Strips, and `RiemannHypothesis` -/

/-- **Exact equivalence between `zetaZeroWidth ≤ σ₀` and `SobolevGradedIncidenceAllocation` at
every rate `σ > σ₀`.** -/
theorem zetaZeroWidth_le_iff_forall_gt_sobolevGradedIncidenceAllocation {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) :
    zetaZeroWidth ≤ σ₀ ↔
      ∀ σ : ℝ, σ₀ < σ → ∃ C : ℝ, 0 < C ∧ SobolevGradedIncidenceAllocation σ C := by
  constructor
  · intro hle σ hσ
    exact exists_sobolevGradedIncidenceAllocation_of_zetaZeroWidth_lt (lt_of_le_of_lt hle hσ)
  · intro halloc
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, -, hC⟩ := halloc (σ₀ + ε) (by linarith)
    exact zetaZeroWidth_le_of_sobolevGradedIncidenceAllocation (by linarith) hC

/-- **Exact equivalence between `zetaZeroWidth ≤ σ₀` and the pole-tilted Sobolev bound on the
compensated remainder `|reflectedPrimePolarCost F r|` at every rate `σ > σ₀`.** -/
theorem zetaZeroWidth_le_iff_forall_gt_reflectedPrimePolarCost_le_poleTiltedSobolev {σ₀ : ℝ}
    (hσ₀ : 0 ≤ σ₀) :
    zetaZeroWidth ≤ σ₀ ↔
      ∀ σ : ℝ, σ₀ < σ → ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
        ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        |reflectedPrimePolarCost F r| ≤
          C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
  constructor
  · intro hle σ hσ
    exact exists_abs_reflectedPrimePolarCost_le_poleTiltedSobolev_of_zetaZeroWidth_lt
      (lt_of_le_of_lt hle hσ)
  · intro hcost
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, -, hC⟩ := hcost (σ₀ + ε) (by linarith)
    exact zetaZeroWidth_le_of_reflectedPrimePolarCost_le_poleTiltedSobolev (by linarith)
      fun r F hr hF hFc hodd hsupp => (le_abs_self _).trans (hC r F hr hF hFc hodd hsupp)

/-- **Exact equivalence between `zetaZeroWidth ≤ σ₀` and the pure-`L²` floor of the complete ledger
on every bounded-Dirichlet-ratio cone `BoundedDirichletCone Λ` at every rate `σ > σ₀`.** -/
theorem zetaZeroWidth_le_iff_forall_gt_boundedDirichletCone_fullZeroForm_floor {σ₀ : ℝ}
    (hσ₀ : 0 ≤ σ₀) :
    zetaZeroWidth ≤ σ₀ ↔
      ∀ σ : ℝ, σ₀ < σ → ∀ Λ : ℝ, 0 ≤ Λ → ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
        ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        BoundedDirichletCone Λ F → -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F := by
  constructor
  · intro hle σ hσ Λ hΛ
    exact exists_boundedDirichletCone_fullZeroForm_floor_of_zetaZeroWidth_lt
      (lt_of_le_of_lt hle hσ) hΛ
  · intro hfloor
    refine le_of_forall_pos_le_add fun ε hε => ?_
    refine zetaZeroWidth_le_of_boundedDirichletCone_fullZeroForm_floor (by linarith) fun Λ hΛ => ?_
    obtain ⟨C, -, hC⟩ := hfloor (σ₀ + ε) (by linarith) Λ hΛ
    exact ⟨C, hC⟩

/-- **Exact equivalence between a sub-trivial exponent `< 1/2` of the complete ledger and
`zetaZeroWidth < 1/2`.** -/
theorem exists_lt_half_sobolevGradedIncidenceAllocation_iff_zetaZeroWidth_lt_half :
    (∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ ∃ C : ℝ, SobolevGradedIncidenceAllocation σ C) ↔
      zetaZeroWidth < 1 / 2 := by
  constructor
  · rintro ⟨σ, hσ0, hσ_lt, C, hC⟩
    exact lt_of_le_of_lt (zetaZeroWidth_le_of_sobolevGradedIncidenceAllocation hσ0 hC) hσ_lt
  · intro hlt
    set σ := (zetaZeroWidth + 1 / 2) / 2
    have hσ0 : 0 ≤ σ := by simp only [σ]; linarith [zetaZeroWidth_nonneg]
    have hσ_lt : σ < 1 / 2 := by simp only [σ]; linarith
    have hgt : zetaZeroWidth < σ := by simp only [σ]; linarith
    obtain ⟨K, -, hK⟩ := exists_sobolevGradedIncidenceAllocation_of_zetaZeroWidth_lt hgt
    exact ⟨σ, hσ0, hσ_lt, K, hK⟩

/-- **Exact equivalence between a sub-trivial exponent `σ < 1/2` for the compensated remainder
`reflectedPrimePolarCost F r` and a zero-free strip `zetaZeroAbscissa < 1`.** -/
theorem exists_lt_half_reflectedPrimePolarCost_exponent_iff_zetaZeroAbscissa_lt_one :
    (∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ ∃ C : ℝ, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
      ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤
        C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) ↔
      zetaZeroAbscissa < 1 := by
  have habs : zetaZeroAbscissa < 1 ↔ zetaZeroWidth < 1 / 2 := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    constructor <;> intro h <;> linarith
  rw [habs]
  constructor
  · rintro ⟨σ, hσ0, hσ_lt, C, hC⟩
    refine lt_of_le_of_lt ?_ hσ_lt
    exact zetaZeroWidth_le_of_reflectedPrimePolarCost_le_poleTiltedSobolev hσ0
      fun r F hr hF hFc hodd hsupp => (le_abs_self _).trans (hC r F hr hF hFc hodd hsupp)
  · intro hlt
    set σ := (zetaZeroWidth + 1 / 2) / 2
    have hσ0 : 0 ≤ σ := by simp only [σ]; linarith [zetaZeroWidth_nonneg]
    have hσ_lt : σ < 1 / 2 := by simp only [σ]; linarith
    have hgt : zetaZeroWidth < σ := by simp only [σ]; linarith
    obtain ⟨K, -, hK⟩ := exists_abs_reflectedPrimePolarCost_le_poleTiltedSobolev_of_zetaZeroWidth_lt hgt
    exact ⟨σ, hσ0, hσ_lt, K, hK⟩

/-- **Exact equivalence between a sub-trivial exponent `σ < 1/2` for the compensated remainder
`reflectedPrimePolarCost F r` and `receiverDampingRate < 1/2`.** -/
theorem exists_lt_half_reflectedPrimePolarCost_exponent_iff_receiverDampingRate_lt_half :
    (∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ ∃ C : ℝ, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
      ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤
        C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) ↔
      receiverDampingRate < 1 / 2 := by
  rw [exists_lt_half_reflectedPrimePolarCost_exponent_iff_zetaZeroAbscissa_lt_one,
    receiverDampingRate_eq_zetaZeroWidth, zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  constructor <;> intro h <;> linarith

/-- **Exact equivalence between a sub-trivial exponent `σ < 1/2` on the bounded-Dirichlet-ratio
test cones `BoundedDirichletCone Λ` and a zero-free strip `zetaZeroAbscissa < 1`.** -/
theorem exists_lt_half_boundedDirichletCone_fullZeroForm_floor_iff_zetaZeroAbscissa_lt_one :
    (∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ ∀ Λ : ℝ, 0 ≤ Λ → ∃ C : ℝ, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
      ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      BoundedDirichletCone Λ F → -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F) ↔
      zetaZeroAbscissa < 1 := by
  have habs : zetaZeroAbscissa < 1 ↔ zetaZeroWidth < 1 / 2 := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    constructor <;> intro h <;> linarith
  rw [habs]
  constructor
  · rintro ⟨σ, hσ0, hσ_lt, hfloor⟩
    exact lt_of_le_of_lt (zetaZeroWidth_le_of_boundedDirichletCone_fullZeroForm_floor hσ0 hfloor) hσ_lt
  · intro hlt
    set σ := (zetaZeroWidth + 1 / 2) / 2
    have hσ0 : 0 ≤ σ := by simp only [σ]; linarith [zetaZeroWidth_nonneg]
    have hσ_lt : σ < 1 / 2 := by simp only [σ]; linarith
    have hgt : zetaZeroWidth < σ := by simp only [σ]; linarith
    refine ⟨σ, hσ0, hσ_lt, fun Λ hΛ => ?_⟩
    obtain ⟨C, -, hC⟩ := exists_boundedDirichletCone_fullZeroForm_floor_of_zetaZeroWidth_lt hgt hΛ
    exact ⟨C, hC⟩

/-- **Endpoint equivalence: `RiemannHypothesis` holds if and only if every positive exponent
`σ > 0` holds for `SobolevGradedIncidenceAllocation`.** -/
theorem riemannHypothesis_iff_forall_pos_sobolevGradedIncidenceAllocation :
    RiemannHypothesis ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, 0 < C ∧ SobolevGradedIncidenceAllocation σ C := by
  have h0 : zetaZeroWidth = 0 ↔ zetaZeroWidth ≤ 0 :=
    ⟨le_of_eq, fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero, h0,
    zetaZeroWidth_le_iff_forall_gt_sobolevGradedIncidenceAllocation le_rfl]

/-- **Endpoint equivalence: `RiemannHypothesis` holds if and only if every positive exponent
`σ > 0` holds for the compensated remainder `|reflectedPrimePolarCost F r|`.** -/
theorem riemannHypothesis_iff_forall_pos_reflectedPrimePolarCost_le_poleTiltedSobolev :
    RiemannHypothesis ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r →
        ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        |reflectedPrimePolarCost F r| ≤
          C * Real.exp (2 * σ * r) * ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
  have h0 : zetaZeroWidth = 0 ↔ zetaZeroWidth ≤ 0 :=
    ⟨le_of_eq, fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero, h0,
    zetaZeroWidth_le_iff_forall_gt_reflectedPrimePolarCost_le_poleTiltedSobolev le_rfl]

end GaloisForLFunctions.ArithmeticCompensationTheory

end
