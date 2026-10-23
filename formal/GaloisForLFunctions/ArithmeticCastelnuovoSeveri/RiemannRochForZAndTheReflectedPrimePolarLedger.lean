import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SchurLendingOddHodgeIndexPastFirstPrime
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.BezoutEffectivityAndTheBeurlingObstruction
import GaloisForLFunctions.ArithmeticIncidencePositivity.ReflectedPrimePolarAllocation

/-!
# Riemann–Roch for `ℤ`, the Strict Coupled Arithmetic Cone, and the Reflected-Prime/Polar Ledger

Rank–trace inertia can only bound a *proportion* of critical-line zeros because it applies
Cauchy–Schwarz to the trace and Frobenius norm of a resonant Gram matrix rather than proving that
the Castelnuovo–Severi defect form `δ(f, f) = weilPair f f` is globally positive semidefinite on
the scaling surface of `ℤ`. By the Pontryagin law (`zeta_hodgeDefect_iff`,
`iSup_hodgeDefectAt`, `scalingSurface_hodgeIndex_iff`), the number of negative squares of `δ`
equals the exact cardinality of `rightZeros zetaZeroConfig` (`Re ρ > 1/2`), so **exact `100%` of
the nontrivial zeros of `ζ` lie on the critical line (zero off-line zeros)** if and only if
`scalingSurface.HodgeIndex` holds.

In Open Problem 1 of the Arithmetic Castelnuovo–Severi programme (*Riemann–Roch for `ℤ`*), the goal
is to construct an arithmetic cone of effective cycles on the scaling surface whose **ampleness is
proved unconditionally without assuming the sign of `W`**, so that the entire Hodge index theorem
reduces to the Riemann–Roch axiom for that cone.

This file establishes three unconditional results:

1. **Duality of the Closed and Open Positive Cones & Unconditional Ampleness of the Strict Coupled
   Arithmetic Cone** (`PolarSurface.positiveCone_riemannRoch`,
   `PolarSurface.openPositiveCone_ample`, `PolarSurface.openPositiveCone_riemannRoch_iff_hodgeIndex`,
   `strictCoupledArithmeticCone`, `strictCoupledArithmeticCone_ample`,
   `strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex`):
   * On any abstract polar surface `S`, the closed positive cone `S.positiveCone` satisfies
     `S.RiemannRochAxiom` unconditionally, while `S.AmpleAxiom S.positiveCone` is equivalent to
     `S.HodgeIndex`.
   * Dually, the open positive cone `S.openPositiveCone = {x | 0 < x · x ∧ 0 < x · (H + V)}`
     satisfies **`S.AmpleAxiom` unconditionally without assuming `S.HodgeIndex` or the sign of `δ`**,
     and `S.RiemannRochAxiom S.openPositiveCone` is unconditionally equivalent to `S.HodgeIndex`
     (and implies `S.BezoutAxiom S.openPositiveCone`).
   * On `scalingSubsurface V`, the **strict coupled arithmetic cone**
     `strictCoupledArithmeticCone V` therefore satisfies `AmpleAxiom` unconditionally for every
     test submodule `V ≤ realTests` without assuming the sign of `weilPair`. On the odd reflection
     sector `oddRealTestsAt r`, opposite pole residues `B(f) = -A(f)` cancel in the ample pairing,
     so the degree condition `x · (H + V) > 0` reduces purely to the pole-plane inequality
     `a + b > 0` (`mem_strictCoupledArithmeticCone_odd_iff`).

2. **Exact Lorentz–Polar Identity and the All-Aperture Reflected-Prime/Polar Castelnuovo–Severi
   Ledger** (`weilPair_self_eq_fullZeroForm`, `poleB_eq_evenPoleMoment_sub_oddPoleMoment`,
   `poleA_eq_evenPoleMoment_add_oddPoleMoment`, `two_mul_poleB_mul_poleA_eq_lorentz_moments`,
   `poleCharge_eq_two_mul_poleA_sq_of_odd`, `localPair_self_eq_neg_poleCharge_sub_fullZeroForm_of_odd`,
   `scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger`,
   `scalingSubsurface_odd_defect_eq_chebyshevDefectLedger`,
   `scalingSubsurface_odd_primitive_self_eq_reflectedPrimePolarLedger`,
   `scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp`,
   `scalingSubsurface_odd_primitive_self_le_seventy_eight_mul_exp`,
   `exists_scalingSubsurface_odd_defect_ge_neg_eight_add_eps_mul_exp`,
   `exists_scalingSubsurface_odd_primitive_self_le_eight_add_eps_mul_exp`,
   `scalingSubsurface_odd_defect_eq_criticalScalePrefixLedger`):
   * For every real `C²_c` test `F`, the pole-plane hyperbolic form `2 B(F) A(F)` on
     `scalingSurface` is the Lorentz moment form `2 evenPoleMoment(F)² − 2 oddPoleMoment(F)²`, and
     the Castelnuovo–Severi defect `weilPair F F` equals `fullZeroForm F`.
   * On the odd sector (`evenPoleMoment F = 0`), the incidence-ledger `poleCharge F = 2 S(F)²` is
     literally `2 A(F)² = −2 B(F) A(F)`, the negative self-intersection of the polar projection
     `A(F)(H − V)` of `(0, 0, F)` onto the pole plane `ℝH ⊕ ℝV`.
   * At **every** degree `r > 0` and plateau radius `R > r`, the Castelnuovo–Severi defect of any
     cycle `x = (a, b, f)` on `scalingSubsurface (oddRealTestsAt r)` decomposes into the archimedean
     gauge budget minus `reflectedPrimePolarCost f r` (or equivalently minus the horizon-localized
     two-pole Chebyshev-defect integral on `(0, 2r]` or the second-order critical-scale receiver
     integral), and satisfies both the coarse rate-`1/2` bound `δ(x, x) ≥ −78 e^r ∫ f²` and the
     sharp PNT bound `δ(x, x) ≥ −((8 + ε) e^r + C) ∫ f²`.

3. **Graded Zero-Width Law, Self-Improving Bootstrap, and Master Unconditional Equivalence for Exact
   `100%` Critical-Line Zeros**
   (`zetaZeroWidth_le_of_scalingSubsurface_odd_defect_floor`,
   `rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor`,
   `rightZeros_zeta_eq_empty_iff_bddBelow_scalingSubsurface_odd_defect`,
   `rightZeros_zeta_eq_empty_of_subexponential_reflectedPrimePolarCost`,
   `rightZeros_zeta_eq_empty_of_subexponential_chebyshevTwoPoleDefect_integral`,
   `riemannHypothesis_iff_rightZeros_zeta_eq_empty`,
   `rightZeros_zeta_eq_empty_iff_forall_odd_strictCoupled_riemannRoch`,
   `rightZeros_zeta_eq_empty_iff_forall_odd_reflectedPrimePolarAllocation`,
   `rightZeros_zeta_eq_empty_iff_forall_odd_chebyshevDefectAllocation`,
   `rightZeros_zeta_eq_empty_iff_forall_odd_criticalScalePrefixAllocation`,
   `strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths`):
   * Establishes the **graded Castelnuovo–Severi defect law**: any all-aperture floor
     `δ(x, x) ≥ −C e^{2σ r} ∫ f²` on `scalingSubsurface (oddRealTestsAt r)` forces the zero-free
     strip `zetaZeroWidth ≤ σ` (`|Re ρ − 1/2| ≤ σ`).
   * Establishes the **self-improving bootstrap law**: closing the gap from rate `σ = 1/2` to exact
     positivity `δ(x, x) ≥ 0` does *not* require proving `δ(x, x) ≥ 0` directly at every `r`. Any
     subexponential defect floor (`∀ σ > 0, ∃ C_σ, δ(x, x) ≥ −C_σ e^{2σ r} ∫ f²`) or uniform
     constant floor (`δ(x, x) ≥ −C ∫ f²`) forces `zetaZeroWidth = 0` and automatically self-improves
     to exact positivity `δ(x, x) ≥ 0` (`C = 0, σ = 0`) across all degrees `r > 0`.
   * Establishes the complete chain of unconditional equivalences between:
     * `rightZeros zetaZeroConfig = ∅` (exact `100%` of the nontrivial zeros of `ζ` on `Re s = 1/2`,
       with zero exceptions),
     * `RiemannHypothesis`,
     * `scalingSurface.HodgeIndex`,
     * `scalingSurface.RiemannRochAxiom scalingSurface.openPositiveCone`,
     * `∀ r > 0, (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom (strictCoupledArithmeticCone (oddRealTestsAt r))`,
     * subexponential or constant-floor Castelnuovo–Severi defect bounds across all degrees `r > 0`,
     * all-aperture reflected-prime/polar allocation on `oddRealTestsAt r`, and
     * all-aperture two-pole Chebyshev-defect allocation on `oddRealTestsAt r`,
     together with the unconditional proof of `RiemannRochAxiom`, `AmpleAxiom`, and `BezoutAxiom` for
     `strictCoupledArithmeticCone (oddRealTestsAt r)` past the first prime (`r ≤ 181/500`).
-/

open Complex MeasureTheory Set Zeta23
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Duality of the Closed and Open Positive Cones & Unconditional Ampleness -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **Unconditional Riemann–Roch for the closed positive cone.** On any polar surface `S` (without
assuming `S.HodgeIndex`), every class `x` of positive self-intersection satisfies
`x ∈ S.positiveCone ∨ -x ∈ S.positiveCone`. -/
theorem positiveCone_riemannRoch : S.RiemannRochAxiom S.positiveCone := by
  intro x hx
  rcases le_total 0 (S.pair x S.ample) with h0 | h0
  · exact Or.inl ⟨hx.le, h0⟩
  · exact Or.inr ⟨by simpa using hx.le, by simpa using h0⟩

/-- On the closed positive cone `S.positiveCone`, the ample axiom alone is equivalent to the Hodge
index theorem. -/
theorem positiveCone_ample_iff_hodgeIndex :
    S.AmpleAxiom S.positiveCone ↔ S.HodgeIndex :=
  ⟨fun hA => S.hodgeIndex_iff_ampleHodgeIndex.mpr
    (S.ampleHodgeIndex_of_effectivity S.positiveCone_riemannRoch hA),
   fun hH => (S.positiveCone_axioms hH).2⟩

/-- **Unconditional ampleness of the open positive cone without assuming the sign of `δ`.** Because
every class in `S.openPositiveCone` has strictly positive degree `x · (H + V) > 0`, no class in
`S.openPositiveCone` is orthogonal to `H + V`, so `S.AmpleAxiom S.openPositiveCone` holds on every
polar surface unconditionally. -/
theorem openPositiveCone_ample : S.AmpleAxiom S.openPositiveCone := by
  intro x hx hxA
  exfalso
  exact ne_of_gt hx.2 hxA

/-- Under the Hodge index, the open positive cone satisfies the Bézout axiom. -/
theorem openPositiveCone_bezout (hH : S.HodgeIndex) : S.BezoutAxiom S.openPositiveCone :=
  fun _ hx _ hy => (S.pair_pos_of_openPositiveCone hH hx hy).le

/-- **Riemann–Roch for the open positive cone is unconditionally equivalent to the Hodge index.**
Because `S.AmpleAxiom S.openPositiveCone` holds without assuming the sign of the defect form, the
entire Hodge index theorem on `S` is equivalent to the single property
`S.RiemannRochAxiom S.openPositiveCone`. -/
theorem openPositiveCone_riemannRoch_iff_hodgeIndex :
    S.RiemannRochAxiom S.openPositiveCone ↔ S.HodgeIndex := by
  constructor
  · intro hRR
    exact S.hodgeIndex_iff_ampleHodgeIndex.mpr
      (S.ampleHodgeIndex_of_effectivity hRR S.openPositiveCone_ample)
  · intro hH x hx
    have hA : S.AmpleHodgeIndex := S.hodgeIndex_iff_ampleHodgeIndex.mp hH
    have hne : S.pair x S.ample ≠ 0 := fun h0 => not_le_of_gt hx (hA x h0)
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · refine Or.inr ⟨by simpa using hx, ?_⟩
      simp only [map_neg, LinearMap.neg_apply, Left.neg_pos_iff]
      exact hneg
    · exact Or.inl ⟨hx, hpos⟩

end PolarSurface

/-- **The strict coupled pole–test arithmetic cone** on `scalingSubsurface V`: classes `aH + bV + f`
of strictly positive self-intersection and strictly positive degree against `H + V`. -/
def strictCoupledArithmeticCone (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  {x | 0 < 2 * (x.2.1 + poleB (x.2.2.1 : ℝ → ℝ)) * (x.1 + poleA (x.2.2.1 : ℝ → ℝ)) -
      weilPair (x.2.2.1 : ℝ → ℝ) (x.2.2.1 : ℝ → ℝ) ∧
    0 < x.1 + x.2.1 + poleB (x.2.2.1 : ℝ → ℝ) + poleA (x.2.2.1 : ℝ → ℝ)}

theorem strictCoupledArithmeticCone_eq_openPositiveCone (V : Submodule ℝ realTests) :
    strictCoupledArithmeticCone V = (scalingSubsurface V).openPositiveCone := by
  ext x
  simp only [strictCoupledArithmeticCone, PolarSurface.openPositiveCone, Set.mem_setOf_eq,
    scalingSubsurface_pair_self, scalingSubsurface_pair_ample]

/-- **Unconditional ampleness of `strictCoupledArithmeticCone V` without assuming the sign of `W`.**
For every test submodule `V ≤ realTests`, `strictCoupledArithmeticCone V` satisfies `AmpleAxiom` on
`scalingSubsurface V` unconditionally. -/
theorem strictCoupledArithmeticCone_ample (V : Submodule ℝ realTests) :
    (scalingSubsurface V).AmpleAxiom (strictCoupledArithmeticCone V) := by
  rw [strictCoupledArithmeticCone_eq_openPositiveCone]
  exact (scalingSubsurface V).openPositiveCone_ample

/-- **Riemann–Roch for `strictCoupledArithmeticCone V` is equivalent to `HodgeIndex` on
`scalingSubsurface V`.** -/
theorem strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex (V : Submodule ℝ realTests) :
    (scalingSubsurface V).RiemannRochAxiom (strictCoupledArithmeticCone V) ↔
      (scalingSubsurface V).HodgeIndex := by
  rw [strictCoupledArithmeticCone_eq_openPositiveCone]
  exact (scalingSubsurface V).openPositiveCone_riemannRoch_iff_hodgeIndex

/-- On any test submodule `V ≤ realTests`, `scalingSubsurface V` satisfies `HodgeIndex` if and only
if `weilPair f f ≥ 0` for all `f ∈ V`. -/
theorem scalingSubsurface_hodgeIndex_iff_weilPair_nonneg (V : Submodule ℝ realTests) :
    (scalingSubsurface V).HodgeIndex ↔
      ∀ f : V, 0 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) := by
  rw [(scalingSubsurface V).hodgeIndex_iff_defect_nonneg]
  constructor
  · intro h f
    have := h (0, 0, f)
    rwa [scalingSubsurface_defect_self] at this
  · intro h x
    rw [scalingSubsurface_defect_self]
    exact h x.2.2

/-- On the odd reflection sector `oddRealTestsAt r`, opposite pole residues `B(f) = -A(f)` cancel
in the degree against `H + V`, so membership in `strictCoupledArithmeticCone (oddRealTestsAt r)`
depends only on `a + b > 0` and positive self-intersection. -/
theorem mem_strictCoupledArithmeticCone_odd_iff {r : ℝ}
    (x : ℝ × ℝ × oddRealTestsAt r) :
    x ∈ strictCoupledArithmeticCone (oddRealTestsAt r) ↔
      0 < 2 * (x.2.1 - poleA (x.2.2.1 : ℝ → ℝ)) * (x.1 + poleA (x.2.2.1 : ℝ → ℝ)) -
          weilPair (x.2.2.1 : ℝ → ℝ) (x.2.2.1 : ℝ → ℝ) ∧
        0 < x.1 + x.2.1 := by
  have hB : poleB (x.2.2.1 : ℝ → ℝ) = -poleA (x.2.2.1 : ℝ → ℝ) :=
    poleB_eq_neg_poleA_of_odd x.2.2.2.2
  simp only [strictCoupledArithmeticCone, Set.mem_setOf_eq, hB]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-! ### 2. Exact Lorentz–Polar Identity and the All-Aperture Reflected-Prime/Polar Ledger -/

/-- **Castelnuovo–Severi defect equals `fullZeroForm`.** For every real `C²_c` test `F`, the
scaling-surface defect `weilPair F F` coincides identically with `fullZeroForm F`. -/
theorem weilPair_self_eq_fullZeroForm {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    weilPair F F = fullZeroForm F := by
  rw [weilPair_self_eq_zeta_W_re hF hFc]
  unfold cx
  exact (GaloisForLFunctions.ArithmeticPositivityTheory.fullZeroForm_eq_zeta_W_re hF hFc).symm

/-- The pole coordinate `poleB F = ∫ F(x) e^{-x/2} dx` decomposes into `evenPoleMoment F - oddPoleMoment F`. -/
theorem poleB_eq_evenPoleMoment_sub_oddPoleMoment {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    poleB F = evenPoleMoment F - oddPoleMoment F := by
  have hc : Integrable fun x => F x * Real.cosh (x / 2) :=
    (hF.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hs : Integrable fun x => F x * Real.sinh (x / 2) :=
    (hF.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hpt : (fun x => F x * Real.exp (-x / 2)) =
      fun x => F x * Real.cosh (x / 2) - F x * Real.sinh (x / 2) := by
    funext x
    rw [show -x / 2 = -(x / 2) by ring, Real.cosh_eq, Real.sinh_eq]
    ring
  unfold poleB evenPoleMoment oddPoleMoment
  rw [hpt, integral_sub hc hs]

/-- The pole coordinate `poleA F = ∫ F(x) e^{x/2} dx` decomposes into `evenPoleMoment F + oddPoleMoment F`. -/
theorem poleA_eq_evenPoleMoment_add_oddPoleMoment {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    poleA F = evenPoleMoment F + oddPoleMoment F := by
  have hc : Integrable fun x => F x * Real.cosh (x / 2) :=
    (hF.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hs : Integrable fun x => F x * Real.sinh (x / 2) :=
    (hF.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hpt : (fun x => F x * Real.exp (x / 2)) =
      fun x => F x * Real.cosh (x / 2) + F x * Real.sinh (x / 2) := by
    funext x
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  unfold poleA evenPoleMoment oddPoleMoment
  rw [hpt, integral_add hc hs]

/-- **Lorentz–Polar Identity on `scalingSurface`.** For every real `C⁰_c` test `F`, the hyperbolic
polar form `2 B(F) A(F)` on the pole plane `ℝH ⊕ ℝV` equals `2 evenPoleMoment(F)² - poleCharge F`. -/
theorem two_mul_poleB_mul_poleA_eq_lorentz_moments {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    2 * poleB F * poleA F = 2 * evenPoleMoment F ^ 2 - poleCharge F := by
  rw [poleB_eq_evenPoleMoment_sub_oddPoleMoment hF hFc,
    poleA_eq_evenPoleMoment_add_oddPoleMoment hF hFc, poleCharge]
  ring

/-- For an odd real `C⁰_c` test `F`, `poleA F` equals `oddPoleMoment F` and `poleB F` equals
`-oddPoleMoment F`. -/
theorem poleA_eq_oddPoleMoment_of_odd {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) :
    poleA F = oddPoleMoment F ∧ poleB F = -oddPoleMoment F := by
  rw [poleA_eq_evenPoleMoment_add_oddPoleMoment hF hFc,
    poleB_eq_evenPoleMoment_sub_oddPoleMoment hF hFc,
    evenPoleMoment_eq_zero_of_odd hodd, zero_add, zero_sub]
  exact ⟨rfl, rfl⟩

/-- **Geometric Meaning of `poleCharge` on `scalingSurface`.** For every odd real `C⁰_c` test `F`,
the incidence-ledger pole charge `poleCharge F = 2 S(F)²` equals `2 A(F)² = -2 B(F) A(F)`, the
negative self-intersection of the polar projection `A(F)(H - V)` of `(0, 0, F)` onto `ℝH ⊕ ℝV`. -/
theorem poleCharge_eq_two_mul_poleA_sq_of_odd {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) :
    poleCharge F = 2 * poleA F ^ 2 ∧ 2 * poleB F * poleA F = -poleCharge F := by
  obtain ⟨hA, hB⟩ := poleA_eq_oddPoleMoment_of_odd hF hFc hodd
  rw [poleCharge, hA, hB]
  exact ⟨rfl, by ring⟩

/-- On `scalingSurface`, the local self-intersection `localPair F F` of a pure odd test cycle
`(0, 0, F)` equals `-poleCharge F - fullZeroForm F`. -/
theorem localPair_self_eq_neg_poleCharge_sub_fullZeroForm_of_odd {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) :
    localPair F F = -poleCharge F - fullZeroForm F := by
  have hp := (poleCharge_eq_two_mul_poleA_sq_of_odd hF.continuous hFc hodd).2
  have hw := weilPair_self_eq_fullZeroForm hF hFc
  unfold localPair
  linarith

/-- Every test `f ∈ oddRealTestsAt r` vanishes outside `[-r, r]`. -/
theorem apply_eq_zero_of_mem_oddRealTestsAt {r : ℝ} (f : oddRealTestsAt r) {x : ℝ}
    (hx : r < |x|) : (f.1 : ℝ → ℝ) x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem =>
    not_le_of_gt hx (abs_le.mpr (f.2.1 hmem))

/-- **All-Aperture Reflected-Prime/Polar Castelnuovo–Severi Defect Ledger.** For every degree
`r > 0`, every plateau radius `R > r`, and every cycle `x = (a, b, f)` on
`scalingSubsurface (oddRealTestsAt r)`, the Castelnuovo–Severi defect decomposes into the
archimedean gauge budget minus `reflectedPrimePolarCost`:
`δ(x, x) = surplusPool + crossingPotentialTerm + gaugeRemainder - reflectedPrimePolarCost f r`. -/
theorem scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (x : ℝ × ℝ × oddRealTestsAt r) :
    (scalingSubsurface (oddRealTestsAt r)).defect x x =
      surplusPool (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
        crossingPotentialTerm (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
        gaugeRemainder (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) -
        reflectedPrimePolarCost (x.2.2.1 : ℝ → ℝ) r := by
  rw [scalingSubsurface_defect_self,
    weilPair_self_eq_fullZeroForm x.2.2.1.2.1 x.2.2.1.2.2]
  exact fullZeroForm_eq_reflectedPrimePolarLedger x.2.2.1.2.1 x.2.2.1.2.2 x.2.2.2.2 hr
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt x.2.2 hu) hrR

/-- **All-Aperture Two-Pole Chebyshev-Defect Castelnuovo–Severi Ledger.** For every degree `r > 0`,
every plateau radius `R > r`, and every cycle `x = (a, b, f)` on
`scalingSubsurface (oddRealTestsAt r)`, the leading exponential prime and polar charges cancel,
leaving the two-pole Chebyshev defect `E(s) = e^s + s - 1 - ψ(e^s)` integrated against the lag
derivative on `(0, 2r]`. -/
theorem scalingSubsurface_odd_defect_eq_chebyshevDefectLedger {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (x : ℝ × ℝ × oddRealTestsAt r) :
    (scalingSubsurface (oddRealTestsAt r)).defect x x =
      surplusPool (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
        crossingPotentialTerm (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
        gaugeRemainder (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) -
        ∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) *
            (crossCorrelation (x.2.2.1 : ℝ → ℝ) s -
              autoCorrelation (x.2.2.1 : ℝ → ℝ) s / 2)) := by
  rw [scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr hrR x,
    reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc
      (x.2.2.1.2.1.of_le (by norm_num)) x.2.2.1.2.2 x.2.2.2.2 hr
      (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt x.2.2 hu)]

/-- **Primitive Self-Intersection Ledger on `(H + V)⊥`.** For every degree `r > 0`, every plateau
radius `R > r`, and every primitive cycle `x = (a, -a, f)` on
`scalingSubsurface (oddRealTestsAt r)` orthogonal to `H + V`,
`x · x = -2(a + A(f))² - (surplusPool + crossingPotentialTerm + gaugeRemainder) + reflectedPrimePolarCost f r`. -/
theorem scalingSubsurface_odd_primitive_self_eq_reflectedPrimePolarLedger {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (x : ℝ × ℝ × oddRealTestsAt r)
    (horth : (scalingSubsurface (oddRealTestsAt r)).pair x
      (scalingSubsurface (oddRealTestsAt r)).ample = 0) :
    (scalingSubsurface (oddRealTestsAt r)).pair x x =
      -2 * (x.1 + poleA (x.2.2.1 : ℝ → ℝ)) ^ 2 -
        (surplusPool (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
          crossingPotentialTerm (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
          gaugeRemainder (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ)) +
        reflectedPrimePolarCost (x.2.2.1 : ℝ → ℝ) r := by
  have horth' : scalingSurface.pair (x.1, x.2.1, x.2.2.1) scalingSurface.ample = 0 := horth
  have hself := scalingPair_odd_self_of_orthogonal_ample (x.1, x.2.1, x.2.2.1) x.2.2.2.2 horth'
  have hled := scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr hrR x
  rw [scalingSubsurface_defect_self] at hled
  change scalingSurface.pair (x.1, x.2.1, x.2.2.1) (x.1, x.2.1, x.2.2.1) = _
  linarith

/-- **Unconditional All-Aperture Rate-`1/2` Lower Bound on the Castelnuovo–Severi Defect.** For
every degree `r > 0` and every cycle `x = (a, b, f)` on `scalingSubsurface (oddRealTestsAt r)`,
`δ(x, x) ≥ -78 e^r ∫ f²`. -/
theorem scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp {r : ℝ} (hr : 0 < r)
    (x : ℝ × ℝ × oddRealTestsAt r) :
    -(78 * Real.exp r * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
      (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  have hled := scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr (by linarith : r < r + 1) x
  have hgia := gradedIncidenceAllocation_half r (r + 1) (x.2.2.1 : ℝ → ℝ) hr (by linarith)
    x.2.2.1.2.1 x.2.2.1.2.2 x.2.2.2.2
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt x.2.2 hu)
  have hrate : 2 * (1 / 2 : ℝ) * r = r := by ring
  rw [hrate] at hgia
  unfold reflectedPrimePolarCost at hled
  linarith

/-- **Unconditional All-Aperture Rate-`1/2` Upper Bound on Primitive Self-Intersections.** For
every degree `r > 0` and every cycle `x = (a, -a, f)` on `scalingSubsurface (oddRealTestsAt r)`
orthogonal to `H + V`,
`x · x ≤ -2(a + A(f))² + 78 e^r ∫ f²`. -/
theorem scalingSubsurface_odd_primitive_self_le_seventy_eight_mul_exp {r : ℝ} (hr : 0 < r)
    (x : ℝ × ℝ × oddRealTestsAt r)
    (horth : (scalingSubsurface (oddRealTestsAt r)).pair x
      (scalingSubsurface (oddRealTestsAt r)).ample = 0) :
    (scalingSubsurface (oddRealTestsAt r)).pair x x ≤
      -2 * (x.1 + poleA (x.2.2.1 : ℝ → ℝ)) ^ 2 +
        78 * Real.exp r * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 := by
  have horth' : scalingSurface.pair (x.1, x.2.1, x.2.2.1) scalingSurface.ample = 0 := horth
  have hself := scalingPair_odd_self_of_orthogonal_ample (x.1, x.2.1, x.2.2.1) x.2.2.2.2 horth'
  have hdef := scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp hr x
  rw [scalingSubsurface_defect_self] at hdef
  change scalingSurface.pair (x.1, x.2.1, x.2.2.1) (x.1, x.2.1, x.2.2.1) ≤ _
  linarith

/-- **Sharp PNT `(8 + ε) e^r + C` Lower Bound on the Castelnuovo–Severi Defect.** Replacing the
coarse Chebyshev prime-sum constant by the asymptotic Prime Number Theorem lowers the exponential
prefactor on `scalingSubsurface (oddRealTestsAt r)` from `78` to `8 + ε` across all degrees `r > 0`. -/
theorem exists_scalingSubsurface_odd_defect_ge_neg_eight_add_eps_mul_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
      -(((8 + ε) * Real.exp r + C) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
        (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_reflectedPrimePolarCost_le_eight_add_eps_mul_exp hε
  refine ⟨C₀ + 27 / 5, by linarith, fun r hr x => ?_⟩
  have hled := scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr (by linarith : r < r + 1) x
  have hP0 : ∀ y, 0 ≤ aperturePlateau r (r + 1) y :=
    fun y => plateauGauge_nonneg (r + 1) (r + 1 - r) y
  have hpool := surplusPool_nonneg (F := (x.2.2.1 : ℝ → ℝ)) hP0
  have hcross := crossingPotentialTerm_nonneg (F := (x.2.2.1 : ℝ → ℝ)) hP0
  have hrem := gaugeRemainder_ge_neg_const_mul_sq x.2.2.1.2.1 x.2.2.1.2.2
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt x.2.2 hu) (by linarith : r < r + 1)
  have hcost := hC₀ r (x.2.2.1 : ℝ → ℝ) hr x.2.2.1.2.1.continuous x.2.2.1.2.2 x.2.2.2.2
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt x.2.2 hu)
  linarith

/-- **Sharp PNT `(8 + ε) e^r + C` Upper Bound on Primitive Self-Intersections.** For every `ε > 0`,
there exists `C ≥ 0` such that for every degree `r > 0` and every primitive cycle `x = (a, -a, f)` on
`scalingSubsurface (oddRealTestsAt r)` orthogonal to `H + V`,
`x · x ≤ -2(a + A(f))² + ((8 + ε) e^r + C) ∫ f²`. -/
theorem exists_scalingSubsurface_odd_primitive_self_le_eight_add_eps_mul_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
      (scalingSubsurface (oddRealTestsAt r)).pair x
        (scalingSubsurface (oddRealTestsAt r)).ample = 0 →
      (scalingSubsurface (oddRealTestsAt r)).pair x x ≤
        -2 * (x.1 + poleA (x.2.2.1 : ℝ → ℝ)) ^ 2 +
          ((8 + ε) * Real.exp r + C) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_scalingSubsurface_odd_defect_ge_neg_eight_add_eps_mul_exp hε
  refine ⟨C, hC0, fun r hr x horth => ?_⟩
  have horth' : scalingSurface.pair (x.1, x.2.1, x.2.2.1) scalingSurface.ample = 0 := horth
  have hself := scalingPair_odd_self_of_orthogonal_ample (x.1, x.2.1, x.2.2.1) x.2.2.2.2 horth'
  have hdef := hC r hr x
  rw [scalingSubsurface_defect_self] at hdef
  change scalingSurface.pair (x.1, x.2.1, x.2.2.1) (x.1, x.2.1, x.2.2.1) ≤ _
  linarith

/-- **Second-Order Critical-Scale Receiver Castelnuovo–Severi Ledger.** Integrating by parts a
second time replaces `chebyshevTwoPoleDefect` by the critical-scale prefix functional
`criticalScalePrefix s + s²/2 - s` paired against the derivative autocorrelation
`autoCorrelation (deriv f) s + crossCorrelation f s - autoCorrelation f s / 4` on `(0, ∞)`. -/
theorem scalingSubsurface_odd_defect_eq_criticalScalePrefixLedger {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (x : ℝ × ℝ × oddRealTestsAt r) :
    (scalingSubsurface (oddRealTestsAt r)).defect x x =
      surplusPool (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
        crossingPotentialTerm (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
        gaugeRemainder (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) -
        ∫ s in Ioi (0 : ℝ),
          (criticalScalePrefix s + s ^ 2 / 2 - s) *
            (2 * Real.exp (-s / 2) *
              (autoCorrelation (deriv (x.2.2.1 : ℝ → ℝ)) s +
                crossCorrelation (x.2.2.1 : ℝ → ℝ) s -
                autoCorrelation (x.2.2.1 : ℝ → ℝ) s / 4)) := by
  rw [scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr hrR x,
    reflectedPrimePolarCost_eq_criticalScalePrefix_autoCorrelation_deriv
      x.2.2.1.2.1 x.2.2.1.2.2 x.2.2.2.2 hr
      (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt x.2.2 hu)]

/-! ### 3. Graded Zero-Width Law, Self-Improving Bootstrap, and Master Unconditional Equivalence -/

/-- **Exact `100%` critical-line zeros (`rightZeros zetaZeroConfig = ∅`) is unconditionally
equivalent to `RiemannHypothesis`.** -/
theorem riemannHypothesis_iff_rightZeros_zeta_eq_empty :
    RiemannHypothesis ↔ rightZeros zetaZeroConfig = ∅ := by
  rw [GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine,
    Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h ρ ⟨hρ, hgt⟩
    linarith [h ρ hρ]
  · intro h ρ hρ
    have h1 : ¬ 1 / 2 < ρ.re := fun hgt => h ρ ⟨hρ, hgt⟩
    have h2 : ¬ 1 / 2 < (1 - ρ).re := fun hgt =>
      h (1 - ρ) ⟨(fesSymmetric_zetaZeroConfig ρ hρ).1, hgt⟩
    simp only [Complex.sub_re, Complex.one_re, not_lt] at h1 h2
    linarith

/-- Any real odd `C²_c` test `F` vanishing outside `[-r, r]` defines an element of
`oddRealTestsAt r`. -/
def mkOddRealTestsAt {r : ℝ} (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, r < |x| → F x = 0) : oddRealTestsAt r :=
  ⟨⟨F, hF, hFc⟩,
    closure_minimal (fun u hu => abs_le.mp (not_lt.mp fun hlt => hu (hsupp u hlt))) isClosed_Icc,
    hodd⟩

/-- **Graded Castelnuovo–Severi Defect Law.** Any all-aperture floor
`δ(x, x) ≥ -C e^{2σ r} ∫ f²` on `scalingSubsurface (oddRealTestsAt r)` (`σ ≥ 0`) forces the
zero-free strip `zetaZeroWidth ≤ σ` (every nontrivial zero `ρ` of `ζ` satisfies
`|Re ρ - 1/2| ≤ σ`). -/
theorem zetaZeroWidth_le_of_scalingSubsurface_odd_defect_floor {σ C : ℝ} (hσ : 0 ≤ σ)
    (hfloor : ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
      -(C * Real.exp (2 * σ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
        (scalingSubsurface (oddRealTestsAt r)).defect x x) :
    GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth ≤ σ := by
  refine GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor
    (C := C) hσ ?_
  intro r hr F hF hFc hodd hsupp
  let f := mkOddRealTestsAt F hF hFc hodd hsupp
  have hf := hfloor r hr (0, 0, f)
  rwa [scalingSubsurface_defect_self,
    show (f.1 : ℝ → ℝ) = F from rfl,
    weilPair_self_eq_fullZeroForm hF hFc] at hf

/-- **Self-Improving Bootstrap Theorem for Closing the Rate-`1/2` Gap to Exact `δ(x, x) ≥ 0`.**
Closing the gap between the unconditional rate-`σ = 1/2` floor `δ(x, x) ≥ -78 e^r ∫ f²` and exact
positivity `δ(x, x) ≥ 0` does *not* require proving `δ(x, x) ≥ 0` directly at every degree `r`.
Any subexponential floor (`∀ σ > 0, ∃ C_σ, δ(x, x) ≥ -C_σ e^{2σ r} ∫ f²`) forces `zetaZeroWidth = 0`
(`rightZeros zetaZeroConfig = ∅`) and automatically self-improves to exact positivity
`δ(x, x) ≥ 0` (`C = 0, σ = 0`) at every degree `r > 0`. -/
theorem rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor :
    rightZeros zetaZeroConfig = ∅ ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
        -(C * Real.exp (2 * σ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  rw [← riemannHypothesis_iff_rightZeros_zeta_eq_empty]
  constructor
  · intro hRH σ _
    refine ⟨0, fun r _ x => ?_⟩
    rw [zero_mul, zero_mul, neg_zero, scalingSubsurface_defect_self,
      weilPair_self_eq_fullZeroForm x.2.2.1.2.1 x.2.2.1.2.2]
    exact riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg.mp hRH
      (x.2.2.1 : ℝ → ℝ) x.2.2.1.2.1 x.2.2.1.2.2 x.2.2.2.2
  · intro hsub
    refine GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_of_subexponential_odd_floor ?_
    intro σ hσ
    obtain ⟨C, hC⟩ := hsub σ hσ
    refine ⟨C, fun r hr F hF hFc hodd hsupp => ?_⟩
    let f := mkOddRealTestsAt F hF hFc hodd hsupp
    have hf := hC r hr (0, 0, f)
    rwa [scalingSubsurface_defect_self,
      show (f.1 : ℝ → ℝ) = F from rfl,
      weilPair_self_eq_fullZeroForm hF hFc] at hf

/-- **Constant-Floor Self-Improvement (`σ = 0`).** A uniform constant additive lower bound
`δ(x, x) ≥ -C ∫ f²` across all degrees `r > 0` is unconditionally equivalent to exact positivity
`δ(x, x) ≥ 0` (`C = 0`) and `rightZeros zetaZeroConfig = ∅`. -/
theorem rightZeros_zeta_eq_empty_iff_bddBelow_scalingSubsurface_odd_defect :
    rightZeros zetaZeroConfig = ∅ ↔
      ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
        -(C * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  rw [← riemannHypothesis_iff_rightZeros_zeta_eq_empty]
  constructor
  · intro hRH
    refine ⟨0, fun r _ x => ?_⟩
    rw [zero_mul, neg_zero, scalingSubsurface_defect_self,
      weilPair_self_eq_fullZeroForm x.2.2.1.2.1 x.2.2.1.2.2]
    exact riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg.mp hRH
      (x.2.2.1 : ℝ → ℝ) x.2.2.1.2.1 x.2.2.1.2.2 x.2.2.2.2
  · rintro ⟨C, hC⟩
    refine GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_of_odd_fullZeroForm_bddBelow
      (C := C) fun F hF hFc hodd => ?_
    obtain ⟨r, hr1, hsupp⟩ :=
      GaloisForLFunctions.ArithmeticCriticalityTheory.exists_support_radius hFc
    have hr0 : 0 < r := by linarith
    let f := mkOddRealTestsAt F hF hFc hodd hsupp
    have hf := hC r hr0 (0, 0, f)
    rwa [scalingSubsurface_defect_self,
      show (f.1 : ℝ → ℝ) = F from rfl,
      weilPair_self_eq_fullZeroForm hF hFc] at hf

/-- **Subexponential Reflected-Prime/Polar Cost Allocation Closes the Gap to `100%` Critical-Line
Zeros.** Because `gaugeRemainder` is bounded below at rate `0` (`-27/5 ∫ f²`) across all apertures,
any subexponential bound on `reflectedPrimePolarCost f r` modulo `surplusPool + crossingPotentialTerm`
forces `rightZeros zetaZeroConfig = ∅` and exact positivity `δ(x, x) ≥ 0` at every degree `r > 0`. -/
theorem rightZeros_zeta_eq_empty_of_subexponential_reflectedPrimePolarCost
    (hcost : ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ f : oddRealTestsAt r,
      reflectedPrimePolarCost (f.1 : ℝ → ℝ) r ≤
        surplusPool (aperturePlateau r (r + 1)) (f.1 : ℝ → ℝ) +
          crossingPotentialTerm (aperturePlateau r (r + 1)) (f.1 : ℝ → ℝ) +
          C * Real.exp (2 * σ * r) * ∫ u, (f.1 : ℝ → ℝ) u ^ 2) :
    rightZeros zetaZeroConfig = ∅ := by
  rw [rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor]
  intro σ hσ
  obtain ⟨C, hC⟩ := hcost σ hσ
  refine ⟨|C| + 27 / 5, fun r hr x => ?_⟩
  have hled := scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr (by linarith : r < r + 1) x
  have hrem := gaugeRemainder_ge_neg_const_mul_sq x.2.2.1.2.1 x.2.2.1.2.2
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt x.2.2 hu) (by linarith : r < r + 1)
  have hc := hC r hr x.2.2
  have hexp1 : 1 ≤ Real.exp (2 * σ * r) := Real.one_le_exp (by positivity)
  have hI0 : 0 ≤ ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hCle : C * Real.exp (2 * σ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 ≤
      |C| * Real.exp (2 * σ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_nonneg _)) hI0
  have hrem' : 27 / 5 * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 ≤
      27 / 5 * Real.exp (2 * σ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hI0
  linarith

/-- **Subexponential Two-Pole Chebyshev-Defect Allocation Closes the Gap to `100%` Critical-Line
Zeros.** Any subexponential bound on the horizon-localized two-pole Chebyshev-defect integral on
`(0, 2r]` modulo `surplusPool + crossingPotentialTerm` forces `rightZeros zetaZeroConfig = ∅` and
exact positivity `δ(x, x) ≥ 0` across all degrees `r > 0`. -/
theorem rightZeros_zeta_eq_empty_of_subexponential_chebyshevTwoPoleDefect_integral
    (hcheb : ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ f : oddRealTestsAt r,
      (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) *
            (crossCorrelation (f.1 : ℝ → ℝ) s -
              autoCorrelation (f.1 : ℝ → ℝ) s / 2))) ≤
        surplusPool (aperturePlateau r (r + 1)) (f.1 : ℝ → ℝ) +
          crossingPotentialTerm (aperturePlateau r (r + 1)) (f.1 : ℝ → ℝ) +
          C * Real.exp (2 * σ * r) * ∫ u, (f.1 : ℝ → ℝ) u ^ 2) :
    rightZeros zetaZeroConfig = ∅ := by
  refine rightZeros_zeta_eq_empty_of_subexponential_reflectedPrimePolarCost fun σ hσ => ?_
  obtain ⟨C, hC⟩ := hcheb σ hσ
  refine ⟨C, fun r hr f => ?_⟩
  rw [reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc
    (f.1.2.1.of_le (by norm_num)) f.1.2.2 f.2.2 hr
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt f hu)]
  exact hC r hr f

/-- **Exact `100%` critical-line zeros is equivalent to the Hodge index on
`scalingSubsurface (oddRealTestsAt r)` at every degree `r > 0`.** -/
theorem rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex :
    rightZeros zetaZeroConfig = ∅ ↔
      ∀ r : ℝ, 0 < r → (scalingSubsurface (oddRealTestsAt r)).HodgeIndex := by
  rw [← riemannHypothesis_iff_rightZeros_zeta_eq_empty,
    riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg]
  constructor
  · intro h r _
    rw [scalingSubsurface_hodgeIndex_iff_weilPair_nonneg]
    intro f
    rw [weilPair_self_eq_fullZeroForm f.1.2.1 f.1.2.2]
    exact h (f.1 : ℝ → ℝ) f.1.2.1 f.1.2.2 f.2.2
  · intro h F hF hFc hodd
    obtain ⟨r, hr1, hsupp⟩ :=
      GaloisForLFunctions.ArithmeticCriticalityTheory.exists_support_radius hFc
    have hr0 : 0 < r := by linarith
    have hH := (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg (oddRealTestsAt r)).mp (h r hr0)
    have hf := hH (mkOddRealTestsAt F hF hFc hodd hsupp)
    rwa [show ((mkOddRealTestsAt F hF hFc hodd hsupp).1 : ℝ → ℝ) = F from rfl,
      weilPair_self_eq_fullZeroForm hF hFc] at hf

/-- **Exact `100%` critical-line zeros is equivalent to `RiemannRochAxiom` for
`strictCoupledArithmeticCone (oddRealTestsAt r)` across all degrees `r > 0`.** Since
`strictCoupledArithmeticCone` satisfies `AmpleAxiom` unconditionally at every degree `r` without
assuming the sign of `W`, `RiemannRochAxiom` for `strictCoupledArithmeticCone (oddRealTestsAt r)`
is the single necessary and sufficient condition for `100%` of the zeros of `ζ` to lie on the
critical line. -/
theorem rightZeros_zeta_eq_empty_iff_forall_odd_strictCoupled_riemannRoch :
    rightZeros zetaZeroConfig = ∅ ↔
      ∀ r : ℝ, 0 < r →
        (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
          (strictCoupledArithmeticCone (oddRealTestsAt r)) := by
  rw [rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex]
  exact forall₂_congr fun r _ =>
    (strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex (oddRealTestsAt r)).symm

/-- **Exact `100%` critical-line zeros is equivalent to all-aperture reflected-prime/polar
allocation on `oddRealTestsAt r`.** -/
theorem rightZeros_zeta_eq_empty_iff_forall_odd_reflectedPrimePolarAllocation :
    rightZeros zetaZeroConfig = ∅ ↔
      ∀ (r R : ℝ), 0 < r → r < R → ∀ f : oddRealTestsAt r,
        reflectedPrimePolarCost (f.1 : ℝ → ℝ) r ≤
          surplusPool (aperturePlateau r R) (f.1 : ℝ → ℝ) +
            crossingPotentialTerm (aperturePlateau r R) (f.1 : ℝ → ℝ) +
            gaugeRemainder (aperturePlateau r R) (f.1 : ℝ → ℝ) := by
  rw [rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex]
  constructor
  · intro h r R hr hrR f
    have hH := (scalingSubsurface (oddRealTestsAt r)).hodgeIndex_iff_defect_nonneg.mp (h r hr)
      (0, 0, f)
    rw [scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr hrR (0, 0, f)] at hH
    linarith
  · intro h r hr
    rw [(scalingSubsurface (oddRealTestsAt r)).hodgeIndex_iff_defect_nonneg]
    intro x
    have hle := h r (r + 1) hr (by linarith) x.2.2
    rw [scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr (by linarith : r < r + 1) x]
    linarith

/-- **Exact `100%` critical-line zeros is equivalent to all-aperture two-pole Chebyshev-defect
allocation on `oddRealTestsAt r`.** -/
theorem rightZeros_zeta_eq_empty_iff_forall_odd_chebyshevDefectAllocation :
    rightZeros zetaZeroConfig = ∅ ↔
      ∀ (r R : ℝ), 0 < r → r < R → ∀ f : oddRealTestsAt r,
        (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
            (2 * Real.exp (-s / 2) *
              (crossCorrelation (f.1 : ℝ → ℝ) s -
                autoCorrelation (f.1 : ℝ → ℝ) s / 2))) ≤
          surplusPool (aperturePlateau r R) (f.1 : ℝ → ℝ) +
            crossingPotentialTerm (aperturePlateau r R) (f.1 : ℝ → ℝ) +
            gaugeRemainder (aperturePlateau r R) (f.1 : ℝ → ℝ) := by
  rw [rightZeros_zeta_eq_empty_iff_forall_odd_reflectedPrimePolarAllocation]
  refine forall₄_congr fun r R hr _ => forall_congr' fun f => ?_
  rw [reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc
    (f.1.2.1.of_le (by norm_num)) f.1.2.2 f.2.2 hr
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt f hu)]

/-- **Exact `100%` critical-line zeros is equivalent to all-aperture second-order critical-scale
receiver allocation on `oddRealTestsAt r`.** -/
theorem rightZeros_zeta_eq_empty_iff_forall_odd_criticalScalePrefixAllocation :
    rightZeros zetaZeroConfig = ∅ ↔
      ∀ (r R : ℝ), 0 < r → r < R → ∀ f : oddRealTestsAt r,
        (∫ s in Ioi (0 : ℝ),
            (criticalScalePrefix s + s ^ 2 / 2 - s) *
              (2 * Real.exp (-s / 2) *
                (autoCorrelation (deriv (f.1 : ℝ → ℝ)) s +
                  crossCorrelation (f.1 : ℝ → ℝ) s -
                  autoCorrelation (f.1 : ℝ → ℝ) s / 4))) ≤
          surplusPool (aperturePlateau r R) (f.1 : ℝ → ℝ) +
            crossingPotentialTerm (aperturePlateau r R) (f.1 : ℝ → ℝ) +
            gaugeRemainder (aperturePlateau r R) (f.1 : ℝ → ℝ) := by
  rw [rightZeros_zeta_eq_empty_iff_forall_odd_reflectedPrimePolarAllocation]
  refine forall₄_congr fun r R hr _ => forall_congr' fun f => ?_
  rw [reflectedPrimePolarCost_eq_criticalScalePrefix_autoCorrelation_deriv
    f.1.2.1 f.1.2.2 f.2.2 hr
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt f hu)]

/-- **Unconditional Riemann–Roch, Ampleness, and Bézout Positivity for `strictCoupledArithmeticCone`
past the first prime (`r ≤ 181/500`).** For every degree `r ≤ 181/500 = 0.362` (strictly past the
first prime threshold `(log 2)/2 ≈ 0.34657`), `strictCoupledArithmeticCone (oddRealTestsAt r)`
unconditionally satisfies `RiemannRochAxiom`, `AmpleAxiom`, and `BezoutAxiom` on
`scalingSubsurface (oddRealTestsAt r)`. -/
theorem strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths
    {r : ℝ} (hr : r ≤ 181 / 500) :
    (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
      (strictCoupledArithmeticCone (oddRealTestsAt r)) ∧
    (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom
      (strictCoupledArithmeticCone (oddRealTestsAt r)) ∧
    (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom
      (strictCoupledArithmeticCone (oddRealTestsAt r)) := by
  have hH : (scalingSubsurface (oddRealTestsAt r)).HodgeIndex :=
    scalingSubsurface_odd_hodgeIndex hr
  refine ⟨(strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex (oddRealTestsAt r)).mpr hH,
    strictCoupledArithmeticCone_ample (oddRealTestsAt r), ?_⟩
  rw [strictCoupledArithmeticCone_eq_openPositiveCone]
  exact (scalingSubsurface (oddRealTestsAt r)).openPositiveCone_bezout hH

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
