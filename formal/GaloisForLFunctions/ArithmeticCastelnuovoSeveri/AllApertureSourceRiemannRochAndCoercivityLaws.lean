import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.ArithmeticCriticalityTheory.GaussianCriticalityRestrictedWeilGroundEnergy
import GaloisForLFunctions.ArithmeticCriticalityTheory.OddFormCriticality
import GaloisForLFunctions.ArithmeticCriticalityTheory.PrimitiveHyperplaneCriticality
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarStrictDomain

/-!
# All-Aperture Source Riemann–Roch, Compensated Polar Surfaces, and Aperture-Dependent Coercivity Laws

This module establishes the complete classification and positive structural laws for source-defined
effectivity cones across all apertures `r > 0` on polar and scaling surfaces:

1. **Universal Rigidity of Ampleness and Graded Source Cones on Polar Surfaces (§1):**
   For any polar surface `S : PolarSurface C` and source functional `Φ : C → ℝ`, we define the
   graded source cone `S.gradedSourceCone Φ = {x | 0 ≤ x · (H + V) ∧ Φ(x) ≤ S.polar x x}` and prove:
   * **Exact Fibre-Invariant `RiemannRochAxiom` Equivalence (`gradedSourceCone_riemannRoch_iff_le_defect`,
     `sourceCone_riemannRoch_iff_le_defect`):** Whenever `Φ(-x) = Φ(x)` and `Φ` is invariant under
     adding multiples of `H` and `V`, `S.RiemannRochAxiom (S.gradedSourceCone Φ) ↔ ∀ x, Φ(x) ≤ S.defect x x`
     (with no auxiliary positivity premise required), and when `0 ≤ Φ`, this is also equivalent to
     `S.RiemannRochAxiom (S.sourceCone Φ)`.
   * **Strict Ampleness Rigidity and Collapse of Graded Cones (`strictAmple_sourceCone_iff_pos_on_primitive`,
     `strictAmple_gradedSourceCone_iff_pos_on_primitive`, `gradedSourceCone_eq_sourceCone_of_strictAmple`):**
     For any fibre-invariant `Φ` with `Φ(0) = 0`, strict ampleness (`x ∈ E ∧ x · (H + V) = 0 ⟹ x = 0`)
     holds on `S.gradedSourceCone Φ` if and only if it holds on `S.sourceCone Φ`, if and only if
     `0 < Φ(x)` on every nonzero primitive cycle (`x · H = x · V = 0`, `x ≠ 0`). Whenever this holds,
     `0 ≤ Φ(x)` for all `x : C` and `S.gradedSourceCone Φ = S.sourceCone Φ` identically.

2. **Exact Ampleness vs. Coercivity Dichotomy for `l2SourceCone` and `gradedL2SourceCone` (§2):**
   On `scalingSubsurface V` (`V ≤ realTests`):
   * For **every** `c ∈ ℝ` (positive, zero, or negative),
     `(scalingSubsurface V).RiemannRochAxiom (gradedL2SourceCone c V) ↔ ∀ f ∈ V, c ∫ f² ≤ weilPair f f`
     (`gradedL2SourceCone_riemannRoch_iff_weilPair_ge`).
   * Whenever `c ≤ 0`, every primitive cycle `(-poleA f, -poleB f, f)` lies in both `l2SourceCone c V`
     and `gradedL2SourceCone c V` with `x · (H + V) = 0` (`primitive_mem_l2SourceCone_of_nonpos`).
     Consequently, whenever `∃ f ∈ V, weilPair f f ≠ 0`, `AmpleAxiom` holds on `l2SourceCone c V`
     (or `gradedL2SourceCone c V`) if and only if `0 < c` (`l2SourceCone_ampleAxiom_iff_pos`,
     `gradedL2SourceCone_ampleAxiom_iff_pos`), and simultaneous `RiemannRochAxiom` + `AmpleAxiom`
     holds if and only if `0 < c ∧ ∀ f ∈ V, c ∫ f² ≤ weilPair f f` (`l2SourceCone_effectivity_iff`,
     `gradedL2SourceCone_effectivity_iff`).

3. **Renormalized / Compensated Polar Surfaces and Unconditional All-Aperture Ample Source Cones (§3):**
   For any polar surface `S : PolarSurface C` and symmetric bilinear source reserve
   `B : C →ₗ[ℝ] C →ₗ[ℝ] ℝ` vanishing on `H` and `V`, the **compensated polar surface**
   `S.compensatedSurface B` retains the **exact same** cycle space `C`, fibres `H, V`, ample class
   `H + V`, fibre degrees `x · H, x · V`, hyperbolic capacity `polar`, primitive projection `prim`,
   source section spaces `sourceSections Φ x`, and source cones `sourceCone Φ`, `strictSourceCone Φ`
   as identical sets of cycles, while shifting the Castelnuovo–Severi defect to `S.defect x y + B x y`.
   Specializing to `l2CompensatedScalingSubsurface κ V` with the explicit Chebyshev reserve
   `κ = 10 + 72 e^r + c` on the **entire unrestricted `realTestsAt r`** (and `10 + 68 e^r + c` on
   `evenRealTestsAt r` and `polarFreeSmoothRealTestsAt r`, `10 + 78 e^r + c` on
   `primitiveSmoothRealTestsAt r`, and `78 e^r + c` on `oddRealTestsAt r`):
   * For **every** aperture `r > 0` and **every** `c > 0`, the **unmodified convex, Hecke-stable cone
     `l2SourceCone c V`** satisfies `RiemannRochAxiom`, **non-vacuous `AmpleAxiom`**,
     `SurfaceRiemannRochAxiom 0 0`, `BezoutAxiom` (on `strictL2SourceCone c V`), and `HodgeIndex`
     **unconditionally at all apertures `r > 0`** (`l2CompensatedScalingSubsurface_realTestsAt_all_apertures`).
   * At `c = 0`, `(S.compensatedSurface B).HodgeIndex` is unconditionally equivalent (`↔`) to the
     source-derived Weil floor `-B x x ≤ S.defect x x` on the uncompensated surface `S`
     (`compensatedSurface_hodgeIndex_iff`).

4. **Aperture-Dependent `L²` Coercivity Laws (`μ(r)` and `μ₀(r)`), Unconditional No-Hardy-Weight Law,
   Doubly-Exponential Gaussian Ceiling, and Strict-Monotonicity Self-Upgrade (§4):**
   * **No Aperture-Independent Weighted `L²` Hardy Cone Exists (`not_forall_aperture_weightedL2SourceCone_odd_riemannRoch`,
     `not_forall_aperture_weightedL2SourceCone_realTestsAt_riemannRoch`):**
     For every locally integrable weight `W ≥ 0` positive on a set of positive measure, there exists
     a finite aperture `r > 0` at which the weighted `L²` source cone fails `RiemannRochAxiom` on
     `oddRealTestsAt r` and on `realTestsAt r` unconditionally (even under RH).
   * **Unconditional Doubly-Exponential Gaussian Ceiling (`exists_l2SourceCone_realTestsAt_coercivity_le_doubleExp`,
     `not_forall_aperture_l2SourceCone_realTestsAt_riemannRoch`, `le_floorLoss_of_l2SourceCone_riemannRoch`):**
     There exists `K > 0` such that for every `r ≥ 3` and `c ∈ ℝ`, if `RiemannRochAxiom` holds for
     `gradedL2SourceCone c (realTestsAt r)` (or `l2SourceCone c (realTestsAt r)`), then
     `c ≤ K exp((11/2) r - π e^{2(r - 2)})`.
   * **Exact Closed-Aperture Polar Ground-Energy Coercivity Equivalence and Strict-Monotonicity
     Self-Upgrade (`polarFreeSmooth_gradedL2SourceCone_riemannRoch_iff`,
     `polarFreeSmooth_l2SourceCone_riemannRoch_iff`, `all_aperture_polarFreeSmooth_hodgeIndex_iff_ample_l2SourceCone`):**
     On `polarFreeSmoothRealTestsAt r` (`r > 0`), `RiemannRochAxiom` for `gradedL2SourceCone c`
     (and for `l2SourceCone c` when `c > 0`) holds **if and only if**
     `c ≤ ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩`. Because `r ↦ ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩`
     is strictly decreasing (`strictAnti_ccmRestrictedWeilPolarGroundEnergy`), all-aperture
     `HodgeIndex` (`0 ≤ μ₀(r)`) **unconditionally self-upgrades** to strict positivity `0 < μ₀(r)` at
     every finite aperture `r > 0`, making `RiemannHypothesis`, all-aperture `HodgeIndex` on
     `polarFreeSmoothRealTestsAt r`, and all-aperture simultaneous `RiemannRochAxiom` + non-vacuous
     `AmpleAxiom` + `SurfaceRiemannRochAxiom 0 0` + `BezoutAxiom` for the canonical aperture-dependent
     cone `l2SourceCone (ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩) (polarFreeSmoothRealTestsAt r)`
     **unconditionally equivalent**!

5. **Sobolev Source Cones and the Unconditional Zero-Width Equivalence Across All Apertures (§5):**
   For `sobolevSourceCone c V` and `gradedSobolevSourceCone c V` (`sobolevSourceEnergy c V x = c (∫ f² + ∫ (f')²)`),
   we prove non-vacuous `AmpleAxiom` for `c > 0`, the exact `RiemannRochAxiom` equivalence for all
   `c ∈ ℝ`, and the **unconditional exact `↔` equivalence at every strip width `σ ≥ 0`**
   (`zetaZeroWidth_le_iff_gradedSobolevSourceCone_riemannRoch`,
   `zetaZeroWidth_le_of_polarFreeSmooth_gradedL2SourceCone_riemannRoch`):
   `zetaZeroWidth ≤ σ` if and only if for every `β > σ` there exists `C > 0` such that
   `gradedSobolevSourceCone (-C e^{2β r})` satisfies `RiemannRochAxiom` across all apertures `r > 0`
   on `realTestsAt r` (and equivalently on `oddRealTestsAt r`).
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  GaloisForLFunctions.SquareRootThreshold

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Universal Rigidity of Ampleness and Graded Source Cones on Polar Surfaces -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **The Graded Source Cone (`gradedSourceCone`):**
For a source functional `Φ : C → ℝ`, `S.gradedSourceCone Φ` consists of cycles `x : C` in the
ample half-space `0 ≤ x · (H + V)` whose hyperbolic pole capacity `S.polar x x = 2(x · H)(x · V)`
pays the source energy `Φ(x)`. -/
def gradedSourceCone (Φ : C → ℝ) : Set C :=
  {x : C | 0 ≤ S.pair x S.ample ∧ Φ x ≤ S.polar x x}

theorem mem_gradedSourceCone_iff (Φ : C → ℝ) (x : C) :
    x ∈ S.gradedSourceCone Φ ↔ 0 ≤ S.pair x S.ample ∧ Φ x ≤ S.polar x x :=
  Iff.rfl

theorem sourceCone_subset_gradedSourceCone (Φ : C → ℝ) :
    S.sourceCone Φ ⊆ S.gradedSourceCone Φ := by
  intro x hx
  rw [S.mem_sourceCone_iff] at hx
  refine ⟨?_, hx.2.2⟩
  rw [S.pair_ample]
  linarith [hx.1, hx.2.1]

/-- When `0 ≤ Φ x` for all `x`, `S.sourceCone Φ` coincides identically with `S.gradedSourceCone Φ`. -/
theorem sourceCone_eq_gradedSourceCone_of_nonneg {Φ : C → ℝ} (hΦ : ∀ x : C, 0 ≤ Φ x) :
    S.sourceCone Φ = S.gradedSourceCone Φ := by
  ext x
  rw [S.mem_sourceCone_iff, S.mem_gradedSourceCone_iff]
  constructor
  · rintro ⟨hH, hV, hE⟩
    refine ⟨?_, hE⟩
    rw [S.pair_ample]
    linarith
  · rintro ⟨hA, hE⟩
    have hsum : 0 ≤ S.pair x S.H + S.pair x S.V := by rwa [S.pair_ample] at hA
    have hprod : 0 ≤ 2 * S.pair x S.H * S.pair x S.V := by
      rw [← S.polar_self]
      exact (hΦ x).trans hE
    have hH : 0 ≤ S.pair x S.H := by
      by_contra hlt
      push Not at hlt
      have hV : 0 < S.pair x S.V := by linarith
      nlinarith
    have hV : 0 ≤ S.pair x S.V := by
      by_contra hlt
      push Not at hlt
      have hH' : 0 < S.pair x S.H := by linarith
      nlinarith
    exact ⟨hH, hV, hE⟩

/-- Every primitive cycle `x` (`x · H = 0`, `x · V = 0`) with `Φ x ≤ 0` belongs to both
`S.sourceCone Φ` and `S.gradedSourceCone Φ` with vanishing ample degree `x · (H + V) = 0`. -/
theorem mem_sourceCone_of_primitive_of_nonpos {Φ : C → ℝ} {x : C}
    (hH : S.pair x S.H = 0) (hV : S.pair x S.V = 0) (hΦ : Φ x ≤ 0) :
    x ∈ S.sourceCone Φ ∧ x ∈ S.gradedSourceCone Φ ∧ S.pair x S.ample = 0 := by
  have hpol : S.polar x x = 0 := by
    rw [S.polar_self, hH, mul_zero, zero_mul]
  have hA : S.pair x S.ample = 0 := by
    rw [S.pair_ample, hH, hV, add_zero]
  have hsrc : x ∈ S.sourceCone Φ := by
    rw [S.mem_sourceCone_iff, hH, hV, hpol]
    exact ⟨le_rfl, le_rfl, hΦ⟩
  exact ⟨hsrc, S.sourceCone_subset_gradedSourceCone Φ hsrc, hA⟩

/-- **Exact Characterization of Strict Ampleness for `S.sourceCone Φ`:**
Every cycle in `S.sourceCone Φ` orthogonal to `ample = H + V` is `0` if and only if `0 < Φ x` on
every nonzero primitive cycle (`x · H = x · V = 0`, `x ≠ 0`). -/
theorem strictAmple_sourceCone_iff_pos_on_primitive (Φ : C → ℝ) :
    (∀ x ∈ S.sourceCone Φ, S.pair x S.ample = 0 → x = 0) ↔
      ∀ x : C, S.pair x S.H = 0 → S.pair x S.V = 0 → x ≠ 0 → 0 < Φ x := by
  constructor
  · intro hA x hH hV hne
    by_contra hle
    push Not at hle
    obtain ⟨hmem, -, hample⟩ := S.mem_sourceCone_of_primitive_of_nonpos hH hV hle
    exact hne (hA x hmem hample)
  · intro hpos x hx hample
    rw [S.mem_sourceCone_iff] at hx
    rcases hx with ⟨hH, hV, hE⟩
    have hsum : S.pair x S.H + S.pair x S.V = 0 := by rwa [← S.pair_ample]
    have hH0 : S.pair x S.H = 0 := by linarith
    have hV0 : S.pair x S.V = 0 := by linarith
    have hpol : S.polar x x = 0 := by rw [S.polar_self, hH0, mul_zero, zero_mul]
    have hΦ0 : Φ x ≤ 0 := hE.trans hpol.le
    by_contra hne
    exact not_lt_of_ge hΦ0 (hpos x hH0 hV0 hne)

/-- **Universal Rigidity of Strict Ampleness for Graded Source Cones (`gradedSourceCone`):**
For any fibre-invariant `Φ : C → ℝ` (`∀ x, Φ (S.prim x) = Φ x`) with `Φ 0 = 0`, strict ampleness
holds on `S.gradedSourceCone Φ` if and only if `0 < Φ x` on every nonzero primitive cycle, in which
case `0 ≤ Φ x` for all `x : C` and `S.gradedSourceCone Φ = S.sourceCone Φ` identically. -/
theorem strictAmple_gradedSourceCone_iff_pos_on_primitive {Φ : C → ℝ}
    (hΦ0 : Φ 0 = 0) (hprim : ∀ x : C, Φ (S.prim x) = Φ x) :
    (∀ x ∈ S.gradedSourceCone Φ, S.pair x S.ample = 0 → x = 0) ↔
      ∀ x : C, S.pair x S.H = 0 → S.pair x S.V = 0 → x ≠ 0 → 0 < Φ x := by
  constructor
  · intro hA x hH hV hne
    by_contra hle
    push Not at hle
    obtain ⟨-, hmem, hample⟩ := S.mem_sourceCone_of_primitive_of_nonpos hH hV hle
    exact hne (hA x hmem hample)
  · intro hpos x hx hample
    rw [S.mem_gradedSourceCone_iff] at hx
    rcases hx with ⟨-, hE⟩
    have hsum : S.pair x S.H + S.pair x S.V = 0 := by rwa [← S.pair_ample]
    have hV_eq : S.pair x S.V = -S.pair x S.H := by linarith
    have hpol : S.polar x x = -2 * S.pair x S.H ^ 2 := by
      rw [S.polar_self, hV_eq]
      ring
    have hprim_le : Φ (S.prim x) ≤ -2 * S.pair x S.H ^ 2 := by
      rw [hprim x]
      exact hE.trans hpol.le
    have hsq_nonpos : -2 * S.pair x S.H ^ 2 ≤ 0 := by nlinarith [sq_nonneg (S.pair x S.H)]
    have hprim_eq_zero : S.prim x = 0 := by
      by_contra hne
      have hgt := hpos (S.prim x) (S.pair_prim_H x) (S.pair_prim_V x) hne
      linarith
    have hΦ_prim_zero : Φ (S.prim x) = 0 := by rw [hprim_eq_zero, hΦ0]
    have hH0 : S.pair x S.H = 0 := by
      have h0 : S.pair x S.H ^ 2 ≤ 0 := by linarith
      nlinarith [sq_nonneg (S.pair x S.H)]
    have hV0 : S.pair x S.V = 0 := by linarith
    have hx_prim : x - S.pair x S.V • S.H - S.pair x S.H • S.V = 0 := hprim_eq_zero
    rw [hH0, hV0, zero_smul, zero_smul, sub_zero, sub_zero] at hx_prim
    exact hx_prim

theorem gradedSourceCone_eq_sourceCone_of_strictAmple {Φ : C → ℝ}
    (hΦ0 : Φ 0 = 0) (hprim : ∀ x : C, Φ (S.prim x) = Φ x)
    (hA : ∀ x ∈ S.gradedSourceCone Φ, S.pair x S.ample = 0 → x = 0) :
    (∀ x : C, 0 ≤ Φ x) ∧ S.gradedSourceCone Φ = S.sourceCone Φ := by
  have hpos := (S.strictAmple_gradedSourceCone_iff_pos_on_primitive hΦ0 hprim).mp hA
  have hnn : ∀ x : C, 0 ≤ Φ x := by
    intro x
    rw [← hprim x]
    by_cases h0 : S.prim x = 0
    · rw [h0, hΦ0]
    · exact (hpos (S.prim x) (S.pair_prim_H x) (S.pair_prim_V x) h0).le
  exact ⟨hnn, (S.sourceCone_eq_gradedSourceCone_of_nonneg hnn).symm⟩

/-- **Universal Fibre-Invariant `RiemannRochAxiom` Equivalence for `S.gradedSourceCone Φ`:**
For any even fibre-invariant functional `Φ : C → ℝ` (`Φ(-x) = Φ(x)` and `Φ(x + aH + bV) = Φ(x)`),
`S.RiemannRochAxiom (S.gradedSourceCone Φ)` holds if and only if `∀ x : C, Φ x ≤ S.defect x x`. -/
theorem gradedSourceCone_riemannRoch_iff_le_defect {Φ : C → ℝ}
    (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.RiemannRochAxiom (S.gradedSourceCone Φ) ↔ ∀ x : C, Φ x ≤ S.defect x x := by
  constructor
  · intro hRR x
    by_contra hlt
    push Not at hlt
    set M : ℝ := (Φ x + S.defect x x) / 2
    have hdef_lt_M : S.defect x x < M := by dsimp [M]; linarith
    have hM_lt_Φ : M < Φ x := by dsimp [M]; linarith
    set a₀ : ℝ := 1 / 2 - S.pair x S.V
    set b₀ : ℝ := M - S.pair x S.H
    let y : C := x + a₀ • S.H + b₀ • S.V
    have hyH : S.pair y S.H = M := by
      simp only [y, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        S.pair_H_H, S.pair_V_H]
      dsimp [b₀]
      ring
    have hyV : S.pair y S.V = 1 / 2 := by
      simp only [y, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        S.pair_H_V, S.pair_V_V]
      dsimp [a₀]
      ring
    have hpol : S.polar y y = M := by
      rw [S.polar_self, hyH, hyV]
      ring
    have hprim_y : S.prim y = S.prim x := by
      simp only [PolarSurface.prim, hyH, hyV, y, a₀, b₀]
      module
    have hdef_y : S.defect y y = S.defect x x := by
      rw [← S.defect_prim y y, ← S.defect_prim x x, hprim_y]
    have hpair_y : 0 < S.pair y y := by
      have hd : S.defect y y = S.polar y y - S.pair y y := rfl
      linarith
    have hΦ_y : Φ y = Φ x := hfib x a₀ b₀
    rcases hRR y hpair_y with hy | hny
    · have hle : Φ y ≤ S.polar y y := hy.2
      linarith
    · have hle : Φ (-y) ≤ S.polar (-y) (-y) := hny.2
      rw [heven y, S.polar_neg_self] at hle
      linarith
  · intro hle x hx
    have hpol : Φ x ≤ S.polar x x := by
      have hd : S.defect x x = S.polar x x - S.pair x x := rfl
      linarith [hle x]
    rcases le_total 0 (S.pair x S.ample) with hA | hA
    · exact Or.inl ⟨hA, hpol⟩
    · right
      refine ⟨?_, ?_⟩
      · rw [S.pair_neg_left]
        linarith
      · rw [heven x, S.polar_neg_self]
        exact hpol

/-- **Universal Fibre-Invariant `RiemannRochAxiom` Equivalence for `S.sourceCone Φ` (`0 ≤ Φ`):**
Removes the auxiliary hypothesis `∃ x₀` from `riemannRoch_sourceCone_iff_le_defect_of_pos_defect`. -/
theorem sourceCone_riemannRoch_iff_le_defect {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x) (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.RiemannRochAxiom (S.sourceCone Φ) ↔ ∀ x : C, Φ x ≤ S.defect x x := by
  rw [S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
  exact S.gradedSourceCone_riemannRoch_iff_le_defect heven hfib

end PolarSurface

/-! ### 2. Exact Ampleness vs. Coercivity Dichotomy for `l2SourceCone` and `gradedL2SourceCone` -/

theorem gradedL2SourceCone_eq_gradedSourceCone (c : ℝ) (V : Submodule ℝ realTests) :
    gradedL2SourceCone c V = (scalingSubsurface V).gradedSourceCone (l2SourceEnergy c V) :=
  rfl

theorem l2SourceEnergy_add_fibres (c : ℝ) (V : Submodule ℝ realTests)
    (x : ℝ × ℝ × V) (a b : ℝ) :
    l2SourceEnergy c V (x + a • (scalingSubsurface V).H + b • (scalingSubsurface V).V) =
      l2SourceEnergy c V x := by
  simp [l2SourceEnergy, scalingSubsurface, scalingSurface]

/-- **Exact Quantitative Equivalence of `RiemannRochAxiom` for `gradedL2SourceCone c V` (All `c ∈ ℝ`):**
For every `c ∈ ℝ` (positive, zero, or negative) and every submodule `V ≤ realTests`,
`(scalingSubsurface V).RiemannRochAxiom (gradedL2SourceCone c V)` holds if and only if
`∀ f ∈ V, c ∫ f(u)² du ≤ weilPair f f`. -/
theorem gradedL2SourceCone_riemannRoch_iff_weilPair_ge (c : ℝ) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).RiemannRochAxiom (gradedL2SourceCone c V) ↔
      ∀ f : V, c * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1 := by
  rw [gradedL2SourceCone_eq_gradedSourceCone,
    (scalingSubsurface V).gradedSourceCone_riemannRoch_iff_le_defect
      (l2SourceEnergy_neg c V) (l2SourceEnergy_add_fibres c V)]
  constructor
  · intro h f
    have hx := h (0, 0, f)
    rwa [scalingSubsurface_defect_self] at hx
  · intro h x
    rw [scalingSubsurface_defect_self]
    exact h x.2.2

/-- When `c ≤ 0`, for every `f ∈ V`, the primitive cycle `x_f = (-poleA f, -poleB f, f)` lies in
both `l2SourceCone c V` and `gradedL2SourceCone c V` and satisfies `x_f · (H + V) = 0`. -/
theorem primitive_mem_l2SourceCone_of_nonpos {c : ℝ} (hc : c ≤ 0) (V : Submodule ℝ realTests)
    (f : V) :
    let x : ℝ × ℝ × V := (-poleA f.1.1, -poleB f.1.1, f)
    x ∈ l2SourceCone c V ∧ x ∈ gradedL2SourceCone c V ∧
      (scalingSubsurface V).pair x (scalingSubsurface V).ample = 0 := by
  intro x
  let S := scalingSubsurface V
  have hH : S.pair x S.H = 0 := by
    rw [scalingSubsurface_pair_H]
    simp [x]
  have hV : S.pair x S.V = 0 := by
    rw [scalingSubsurface_pair_V]
    simp [x]
  have hE : l2SourceEnergy c V x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc (integral_nonneg fun _ => sq_nonneg _)
  exact S.mem_sourceCone_of_primitive_of_nonpos hH hV hE

/-- When `c ≤ 0` and `V` contains a test `f` with `weilPair f f ≠ 0`, both `l2SourceCone c V` and
`gradedL2SourceCone c V` fail `AmpleAxiom`. -/
theorem not_ampleAxiom_l2SourceCone_of_nonpos {c : ℝ} (hc : c ≤ 0) (V : Submodule ℝ realTests)
    {f : V} (hf : weilPair f.1.1 f.1.1 ≠ 0) :
    ¬ (scalingSubsurface V).AmpleAxiom (l2SourceCone c V) ∧
      ¬ (scalingSubsurface V).AmpleAxiom (gradedL2SourceCone c V) := by
  let S := scalingSubsurface V
  let x : ℝ × ℝ × V := (-poleA f.1.1, -poleB f.1.1, f)
  obtain ⟨hx_l2, hx_grad, hx_ample⟩ := primitive_mem_l2SourceCone_of_nonpos hc V f
  have hH : S.pair x S.H = 0 := by rw [scalingSubsurface_pair_H]; simp [x]
  have hpol : S.polar x x = 0 := by rw [S.polar_self, hH, mul_zero, zero_mul]
  have hpair_ne : S.pair x x ≠ 0 := by
    have hd : S.defect x x = S.polar x x - S.pair x x := rfl
    rw [scalingSubsurface_defect_self, hpol, zero_sub] at hd
    intro h0
    rw [h0, neg_zero] at hd
    exact hf hd
  exact ⟨fun hA => hpair_ne (hA x hx_l2 hx_ample x),
    fun hA => hpair_ne (hA x hx_grad hx_ample x)⟩

/-- **Exact Ampleness Equivalence for `l2SourceCone c V` and `gradedL2SourceCone c V`:**
Whenever `∃ f ∈ V, weilPair f f ≠ 0`, `AmpleAxiom` holds on `l2SourceCone c V` (and on
`gradedL2SourceCone c V`) if and only if `0 < c`. -/
theorem l2SourceCone_ampleAxiom_iff_pos (c : ℝ) (V : Submodule ℝ realTests)
    (hV : ∃ f : V, weilPair f.1.1 f.1.1 ≠ 0) :
    (scalingSubsurface V).AmpleAxiom (l2SourceCone c V) ↔ 0 < c := by
  refine ⟨fun hA => ?_, fun hc => l2SourceCone_ample hc V⟩
  by_contra hle
  push Not at hle
  rcases hV with ⟨f, hf⟩
  exact (not_ampleAxiom_l2SourceCone_of_nonpos hle V hf).1 hA

theorem gradedL2SourceCone_ampleAxiom_iff_pos (c : ℝ) (V : Submodule ℝ realTests)
    (hV : ∃ f : V, weilPair f.1.1 f.1.1 ≠ 0) :
    (scalingSubsurface V).AmpleAxiom (gradedL2SourceCone c V) ↔ 0 < c := by
  refine ⟨fun hA => ?_, fun hc => ?_⟩
  · by_contra hle
    push Not at hle
    rcases hV with ⟨f, hf⟩
    exact (not_ampleAxiom_l2SourceCone_of_nonpos hle V hf).2 hA
  · rw [← l2SourceCone_eq_gradedL2SourceCone hc.le V]
    exact l2SourceCone_ample hc V

/-- **Master Effectivity Equivalence for `l2SourceCone c V` and `gradedL2SourceCone c V`:**
Whenever `∃ f ∈ V, weilPair f f ≠ 0`, simultaneous `RiemannRochAxiom` and `AmpleAxiom` hold on
`gradedL2SourceCone c V` if and only if they hold on `l2SourceCone c V`, if and only if
`0 < c ∧ ∀ f ∈ V, c ∫ f(u)² du ≤ weilPair f f`. -/
theorem gradedL2SourceCone_effectivity_iff (c : ℝ) (V : Submodule ℝ realTests)
    (hV : ∃ f : V, weilPair f.1.1 f.1.1 ≠ 0) :
    ((scalingSubsurface V).RiemannRochAxiom (gradedL2SourceCone c V) ∧
        (scalingSubsurface V).AmpleAxiom (gradedL2SourceCone c V)) ↔
      (0 < c ∧ ∀ f : V, c * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1) := by
  rw [gradedL2SourceCone_riemannRoch_iff_weilPair_ge, gradedL2SourceCone_ampleAxiom_iff_pos c V hV,
    and_comm]

theorem l2SourceCone_effectivity_iff (c : ℝ) (V : Submodule ℝ realTests)
    (hV : ∃ f : V, weilPair f.1.1 f.1.1 ≠ 0) :
    ((scalingSubsurface V).RiemannRochAxiom (l2SourceCone c V) ∧
        (scalingSubsurface V).AmpleAxiom (l2SourceCone c V)) ↔
      (0 < c ∧ ∀ f : V, c * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1) := by
  constructor
  · rintro ⟨hRR, hA⟩
    have hc : 0 < c := (l2SourceCone_ampleAxiom_iff_pos c V hV).mp hA
    exact ⟨hc, (l2SourceCone_riemannRoch_iff_weilPair_ge hc V).mp hRR⟩
  · rintro ⟨hc, hfl⟩
    exact ⟨(l2SourceCone_riemannRoch_iff_weilPair_ge hc V).mpr hfl, l2SourceCone_ample hc V⟩

/-! ### 3. Renormalized / Compensated Polar Surfaces and Unconditional All-Aperture Ample Source Cones -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **The Compensated Polar Surface (`compensatedSurface`):**
Given a symmetric bilinear source reserve `B : C →ₗ[ℝ] C →ₗ[ℝ] ℝ` that vanishes on the pole fibres
`H` and `V`, `S.compensatedSurface B` equips `C` with the compensated intersection pairing
`pair_B x y = S.pair x y - B x y` while retaining `H` and `V`. -/
def compensatedSurface (B : C →ₗ[ℝ] C →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y : C, B x y = B y x)
    (hH : ∀ x : C, B x S.H = 0) (hV : ∀ x : C, B x S.V = 0) : PolarSurface C where
  pair := S.pair - B
  pair_comm x y := by simp [LinearMap.sub_apply, S.pair_comm x y, hsymm x y]
  H := S.H
  V := S.V
  pair_H_H := by simp [LinearMap.sub_apply, S.pair_H_H, hH S.H]
  pair_V_V := by simp [LinearMap.sub_apply, S.pair_V_V, hV S.V]
  pair_H_V := by simp [LinearMap.sub_apply, S.pair_H_V, hV S.H]

variable {B : C →ₗ[ℝ] C →ₗ[ℝ] ℝ} {hsymm : ∀ x y : C, B x y = B y x}
  {hH : ∀ x : C, B x S.H = 0} {hV : ∀ x : C, B x S.V = 0}

@[simp]
theorem compensatedSurface_H : (S.compensatedSurface B hsymm hH hV).H = S.H := rfl

@[simp]
theorem compensatedSurface_V : (S.compensatedSurface B hsymm hH hV).V = S.V := rfl

@[simp]
theorem compensatedSurface_ample : (S.compensatedSurface B hsymm hH hV).ample = S.ample := rfl

@[simp]
theorem compensatedSurface_pair_H (x : C) :
    (S.compensatedSurface B hsymm hH hV).pair x S.H = S.pair x S.H := by
  simp [compensatedSurface, LinearMap.sub_apply, hH x]

@[simp]
theorem compensatedSurface_pair_V (x : C) :
    (S.compensatedSurface B hsymm hH hV).pair x S.V = S.pair x S.V := by
  simp [compensatedSurface, LinearMap.sub_apply, hV x]

@[simp]
theorem compensatedSurface_pair_ample (x : C) :
    (S.compensatedSurface B hsymm hH hV).pair x S.ample = S.pair x S.ample := by
  change ((S.compensatedSurface B hsymm hH hV).pair x) (S.H + S.V) = S.pair x (S.H + S.V)
  rw [map_add, map_add, S.compensatedSurface_pair_H, S.compensatedSurface_pair_V]

@[simp]
theorem compensatedSurface_polar (x y : C) :
    (S.compensatedSurface B hsymm hH hV).polar x y = S.polar x y := by
  simp [PolarSurface.polar, S.compensatedSurface_pair_H, S.compensatedSurface_pair_V]

@[simp]
theorem compensatedSurface_prim (x : C) :
    (S.compensatedSurface B hsymm hH hV).prim x = S.prim x := by
  simp [PolarSurface.prim, S.compensatedSurface_pair_H, S.compensatedSurface_pair_V]

/-- The source section spaces, closed source cone, strict source cone, and graded source cone on
`S.compensatedSurface B` are **identical as sets** to those on `S`. -/
@[simp]
theorem compensatedSurface_sourceSections (Φ : C → ℝ) (x : C) :
    (S.compensatedSurface B hsymm hH hV).sourceSections Φ x = S.sourceSections Φ x := by
  ext p
  simp [PolarSurface.sourceSections]

@[simp]
theorem compensatedSurface_sourceCone (Φ : C → ℝ) :
    (S.compensatedSurface B hsymm hH hV).sourceCone Φ = S.sourceCone Φ := by
  ext x
  simp [PolarSurface.sourceCone]

@[simp]
theorem compensatedSurface_strictSourceCone (Φ : C → ℝ) :
    (S.compensatedSurface B hsymm hH hV).strictSourceCone Φ = S.strictSourceCone Φ := by
  ext x
  simp [PolarSurface.strictSourceCone, PolarSurface.strictSourceSections]

@[simp]
theorem compensatedSurface_gradedSourceCone (Φ : C → ℝ) :
    (S.compensatedSurface B hsymm hH hV).gradedSourceCone Φ = S.gradedSourceCone Φ := by
  ext x
  simp [PolarSurface.gradedSourceCone]

/-- The Castelnuovo–Severi defect of `S.compensatedSurface B` is `S.defect x y + B x y`. -/
theorem compensatedSurface_defect (x y : C) :
    (S.compensatedSurface B hsymm hH hV).defect x y = S.defect x y + B x y := by
  change (S.compensatedSurface B hsymm hH hV).polar x y - (S.pair x y - B x y) =
    (S.polar x y - S.pair x y) + B x y
  rw [S.compensatedSurface_polar]
  ring

/-- **Exact Equivalence Between Compensated `HodgeIndex` and the Source-Derived Weil Floor:**
`(S.compensatedSurface B).HodgeIndex` holds if and only if `-B x x ≤ S.defect x x` for all `x : C`. -/
theorem compensatedSurface_hodgeIndex_iff :
    (S.compensatedSurface B hsymm hH hV).HodgeIndex ↔ ∀ x : C, -B x x ≤ S.defect x x := by
  rw [(S.compensatedSurface B hsymm hH hV).hodgeIndex_iff_defect_nonneg]
  refine forall_congr' fun x => ?_
  rw [S.compensatedSurface_defect]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

end PolarSurface

/-- Symmetric bilinear `L²` reserve `κ ∫ f(u) g(u) du` on `ℝ × ℝ × V`. -/
def l2ReserveBilinear (κ : ℝ) (V : Submodule ℝ realTests) :
    (ℝ × ℝ × V) →ₗ[ℝ] (ℝ × ℝ × V) →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => κ * ∫ u : ℝ, (x.2.2.1.1 u) * (y.2.2.1.1 u)
      map_add' := fun y₁ y₂ => by
        have h1 : Integrable (fun u : ℝ => x.2.2.1.1 u * y₁.2.2.1.1 u) :=
          integrable_mul_of_mem_realTests x.2.2.1.2 y₁.2.2.1.2
        have h2 : Integrable (fun u : ℝ => x.2.2.1.1 u * y₂.2.2.1.1 u) :=
          integrable_mul_of_mem_realTests x.2.2.1.2 y₂.2.2.1.2
        change κ * ∫ u : ℝ, x.2.2.1.1 u * (y₁.2.2.1.1 u + y₂.2.2.1.1 u) = _
        have hadd : (fun u : ℝ => x.2.2.1.1 u * (y₁.2.2.1.1 u + y₂.2.2.1.1 u)) =
            fun u : ℝ => x.2.2.1.1 u * y₁.2.2.1.1 u + x.2.2.1.1 u * y₂.2.2.1.1 u := by
          ext u; ring
        rw [hadd, integral_add h1 h2, mul_add]
      map_smul' := fun c y => by
        change κ * ∫ u : ℝ, x.2.2.1.1 u * (c * y.2.2.1.1 u) =
          c * (κ * ∫ u : ℝ, x.2.2.1.1 u * y.2.2.1.1 u)
        have hsmul : (fun u : ℝ => x.2.2.1.1 u * (c * y.2.2.1.1 u)) =
            fun u : ℝ => c * (x.2.2.1.1 u * y.2.2.1.1 u) := by
          ext u; ring
        rw [hsmul, integral_const_mul]
        ring }
  map_add' x₁ x₂ := by
    refine LinearMap.ext fun y => ?_
    have h1 : Integrable (fun u : ℝ => x₁.2.2.1.1 u * y.2.2.1.1 u) :=
      integrable_mul_of_mem_realTests x₁.2.2.1.2 y.2.2.1.2
    have h2 : Integrable (fun u : ℝ => x₂.2.2.1.1 u * y.2.2.1.1 u) :=
      integrable_mul_of_mem_realTests x₂.2.2.1.2 y.2.2.1.2
    change κ * ∫ u : ℝ, (x₁.2.2.1.1 u + x₂.2.2.1.1 u) * y.2.2.1.1 u =
      κ * (∫ u : ℝ, x₁.2.2.1.1 u * y.2.2.1.1 u) + κ * ∫ u : ℝ, x₂.2.2.1.1 u * y.2.2.1.1 u
    have hadd : (fun u : ℝ => (x₁.2.2.1.1 u + x₂.2.2.1.1 u) * y.2.2.1.1 u) =
        fun u : ℝ => x₁.2.2.1.1 u * y.2.2.1.1 u + x₂.2.2.1.1 u * y.2.2.1.1 u := by
      ext u; ring
    rw [hadd, integral_add h1 h2, mul_add]
  map_smul' c x := by
    refine LinearMap.ext fun y => ?_
    change κ * ∫ u : ℝ, (c * x.2.2.1.1 u) * y.2.2.1.1 u =
      c * (κ * ∫ u : ℝ, x.2.2.1.1 u * y.2.2.1.1 u)
    have hsmul : (fun u : ℝ => (c * x.2.2.1.1 u) * y.2.2.1.1 u) =
        fun u : ℝ => c * (x.2.2.1.1 u * y.2.2.1.1 u) := by
      ext u; ring
    rw [hsmul, integral_const_mul]
    ring

theorem l2ReserveBilinear_symm (κ : ℝ) (V : Submodule ℝ realTests) (x y : ℝ × ℝ × V) :
    l2ReserveBilinear κ V x y = l2ReserveBilinear κ V y x := by
  change κ * ∫ u : ℝ, x.2.2.1.1 u * y.2.2.1.1 u = κ * ∫ u : ℝ, y.2.2.1.1 u * x.2.2.1.1 u
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)

theorem l2ReserveBilinear_H (κ : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    l2ReserveBilinear κ V x (scalingSubsurface V).H = 0 := by
  change κ * ∫ u : ℝ, x.2.2.1.1 u * (0 : ℝ) = 0
  simp

theorem l2ReserveBilinear_V (κ : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    l2ReserveBilinear κ V x (scalingSubsurface V).V = 0 := by
  change κ * ∫ u : ℝ, x.2.2.1.1 u * (0 : ℝ) = 0
  simp

theorem l2ReserveBilinear_self (κ : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    l2ReserveBilinear κ V x x = l2SourceEnergy κ V x := by
  change κ * ∫ u : ℝ, x.2.2.1.1 u * x.2.2.1.1 u = κ * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun u => (sq (x.2.2.1.1 u)).symm)

/-- **The `L²`-Compensated Scaling Subsurface (`l2CompensatedScalingSubsurface κ V`):**
Equips `ℝ × ℝ × V` with the compensated intersection pairing `scalingPair x y - κ ∫ f g` while
retaining `H`, `V`, `ample = H + V`, and the exact same source cones `l2SourceCone c V` and
`strictL2SourceCone c V`. -/
def l2CompensatedScalingSubsurface (κ : ℝ) (V : Submodule ℝ realTests) :
    PolarSurface (ℝ × ℝ × V) :=
  (scalingSubsurface V).compensatedSurface (l2ReserveBilinear κ V)
    (l2ReserveBilinear_symm κ V) (l2ReserveBilinear_H κ V) (l2ReserveBilinear_V κ V)

/-- On `l2CompensatedScalingSubsurface κ V`, every cycle `x ∈ l2SourceCone c V` (`c > 0`) orthogonal
to `ample = H + V` is `0`, so `AmpleAxiom` holds **non-vacuously** for all `κ ∈ ℝ` and `c > 0`. -/
theorem l2CompensatedScalingSubsurface_ample (κ : ℝ) {c : ℝ} (hc : 0 < c)
    (V : Submodule ℝ realTests) :
    (l2CompensatedScalingSubsurface κ V).AmpleAxiom (l2SourceCone c V) ∧
      (∀ x ∈ l2SourceCone c V,
        (l2CompensatedScalingSubsurface κ V).pair x
          (l2CompensatedScalingSubsurface κ V).ample = 0 → x = 0) := by
  have hzero : ∀ x ∈ l2SourceCone c V,
      (l2CompensatedScalingSubsurface κ V).pair x
        (l2CompensatedScalingSubsurface κ V).ample = 0 → x = 0 := by
    intro x hx hA
    rw [l2CompensatedScalingSubsurface, PolarSurface.compensatedSurface_ample,
      PolarSurface.compensatedSurface_pair_ample] at hA
    exact eq_zero_of_mem_l2SourceCone_of_pair_ample_eq_zero hc V hx hA
  refine ⟨fun x hx hA y => ?_, hzero⟩
  rw [hzero x hx hA]
  simp

/-- If `-(κ - c) ∫ f² ≤ weilPair f f` on `V` with `0 < c`, then `l2SourceCone c V` and
`strictL2SourceCone c V` on `l2CompensatedScalingSubsurface κ V` satisfy `RiemannRochAxiom`,
non-vacuous `AmpleAxiom`, `SurfaceRiemannRochAxiom 0 0`, and `HodgeIndex`. -/
theorem l2CompensatedScalingSubsurface_effectivity_of_floor {κ c : ℝ} (hc : 0 < c)
    (V : Submodule ℝ realTests)
    (hfloor : ∀ x : ℝ × ℝ × V,
      -(κ - c) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (scalingSubsurface V).defect x x) :
    let S' := l2CompensatedScalingSubsurface κ V
    S'.RiemannRochAxiom (l2SourceCone c V) ∧
      S'.AmpleAxiom (l2SourceCone c V) ∧
      S'.SurfaceRiemannRochAxiom 0 0 (l2SourceCone c V) ∧
      S'.RiemannRochAxiom (strictL2SourceCone c V) ∧
      S'.AmpleAxiom (strictL2SourceCone c V) ∧
      S'.HodgeIndex := by
  intro S'
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S'.defect x x := by
    intro x
    have hd : S'.defect x x = (scalingSubsurface V).defect x x + l2SourceEnergy κ V x := by
      dsimp only [S', l2CompensatedScalingSubsurface]
      rw [PolarSurface.compensatedSurface_defect, l2ReserveBilinear_self]
    rw [hd]
    have hf := hfloor x
    unfold l2SourceEnergy
    linarith
  have hsrc : l2SourceCone c V = S'.sourceCone (l2SourceEnergy c V) := by
    dsimp only [S', l2CompensatedScalingSubsurface]
    rw [PolarSurface.compensatedSurface_sourceCone]
    rfl
  have hstrict : strictL2SourceCone c V = S'.strictSourceCone (l2SourceEnergy c V) := by
    dsimp only [S', l2CompensatedScalingSubsurface]
    rw [PolarSurface.compensatedSurface_strictSourceCone]
    rfl
  have hRR : S'.RiemannRochAxiom (l2SourceCone c V) := by
    rw [hsrc]
    exact S'.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc.le V) hle
  have hA : S'.AmpleAxiom (l2SourceCone c V) :=
    (l2CompensatedScalingSubsurface_ample κ hc V).1
  have hSRR : S'.SurfaceRiemannRochAxiom 0 0 (l2SourceCone c V) := by
    rw [hsrc]
    exact S'.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc.le V) hle
  have hRR_s : S'.RiemannRochAxiom (strictL2SourceCone c V) := by
    rw [hstrict]
    exact S'.strictSourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc.le V) hle
  have hA_s : S'.AmpleAxiom (strictL2SourceCone c V) := by
    rw [hstrict]
    exact S'.strictSourceCone_ample (l2SourceEnergy c V)
  exact ⟨hRR, hA, hSRR, hRR_s, hA_s, S'.exists_effectivity_iff_hodgeIndex.mpr ⟨_, hRR, hA⟩⟩

/-- **Unconditional All-Aperture Ample + Riemann–Roch + HodgeIndex Theorem on the Entire
Unrestricted `realTestsAt r` (`r > 0`, `c > 0`):**
With the explicit Chebyshev reserve `κ(r, c) = 10 + 72 e^r + c`, the unmodified convex,
Hecke-stable source cone `l2SourceCone c (realTestsAt r)` and its strict interior
`strictL2SourceCone c (realTestsAt r)` satisfy `RiemannRochAxiom`, **non-vacuous `AmpleAxiom`**
(`x ∈ l2SourceCone c (realTestsAt r) ∧ x · (H + V) = 0 ⟹ x = 0`), `SurfaceRiemannRochAxiom 0 0`,
and `HodgeIndex` unconditionally at **every** aperture `r > 0`. -/
theorem l2CompensatedScalingSubsurface_realTestsAt_all_apertures {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) :
    let S' := l2CompensatedScalingSubsurface (10 + 72 * Real.exp r + c) (realTestsAt r)
    S'.RiemannRochAxiom (l2SourceCone c (realTestsAt r)) ∧
      S'.AmpleAxiom (l2SourceCone c (realTestsAt r)) ∧
      S'.SurfaceRiemannRochAxiom 0 0 (l2SourceCone c (realTestsAt r)) ∧
      S'.RiemannRochAxiom (strictL2SourceCone c (realTestsAt r)) ∧
      S'.AmpleAxiom (strictL2SourceCone c (realTestsAt r)) ∧
      S'.HodgeIndex := by
  refine l2CompensatedScalingSubsurface_effectivity_of_floor hc (realTestsAt r) fun x => ?_
  have h := realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp hr x
  linarith [show -(10 + 72 * Real.exp r + c - c) = -(10 + 72 * Real.exp r) by ring]

/-- **Unconditional All-Aperture Ample + Riemann–Roch + HodgeIndex on `evenRealTestsAt r`
and `polarFreeSmoothRealTestsAt r` (`r > 0`, `c > 0`, Reserve `10 + 68 e^r + c`):** -/
theorem l2CompensatedScalingSubsurface_even_and_polarFree_all_apertures {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) :
    ((l2CompensatedScalingSubsurface (10 + 68 * Real.exp r + c) (evenRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (evenRealTestsAt r)) ∧
      (l2CompensatedScalingSubsurface (10 + 68 * Real.exp r + c) (evenRealTestsAt r)).AmpleAxiom
        (l2SourceCone c (evenRealTestsAt r)) ∧
      (l2CompensatedScalingSubsurface (10 + 68 * Real.exp r + c) (evenRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (evenRealTestsAt r)) ∧
      (l2CompensatedScalingSubsurface (10 + 68 * Real.exp r + c) (evenRealTestsAt r)).HodgeIndex) ∧
    ((l2CompensatedScalingSubsurface (10 + 68 * Real.exp r + c) (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ∧
      (l2CompensatedScalingSubsurface (10 + 68 * Real.exp r + c) (polarFreeSmoothRealTestsAt r)).AmpleAxiom
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ∧
      (l2CompensatedScalingSubsurface (10 + 68 * Real.exp r + c) (polarFreeSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ∧
      (l2CompensatedScalingSubsurface (10 + 68 * Real.exp r + c) (polarFreeSmoothRealTestsAt r)).HodgeIndex) := by
  constructor
  · obtain ⟨hRR, hA, hSRR, -, -, hH⟩ :=
      l2CompensatedScalingSubsurface_effectivity_of_floor (κ := 10 + 68 * Real.exp r + c) hc
        (evenRealTestsAt r) fun x => by
          have h := even_scalingSubsurface_defect_ge_neg_ten_add_sixty_eight_exp r x
          linarith [show -(10 + 68 * Real.exp r + c - c) = -(10 + 68 * Real.exp r) by ring]
    exact ⟨hRR, hA, hSRR, hH⟩
  · obtain ⟨hRR, hA, hSRR, -, -, hH⟩ :=
      l2CompensatedScalingSubsurface_effectivity_of_floor (κ := 10 + 68 * Real.exp r + c) hc
        (polarFreeSmoothRealTestsAt r) fun x => by
          have h := polarFreeSmooth_scalingSubsurface_defect_ge_neg_ten_add_sixty_eight_exp hr x
          linarith [show -(10 + 68 * Real.exp r + c - c) = -(10 + 68 * Real.exp r) by ring]
    exact ⟨hRR, hA, hSRR, hH⟩

/-! ### 4. Aperture-Dependent Coercivity Laws, Unconditional No-Hardy-Weight Law, Doubly-Exponential Ceiling, and Strict-Monotonicity Self-Upgrade -/

/-- Weighted `L²` source energy `∫ W(u) f(u)² du` on `scalingSubsurface V`. -/
def weightedL2SourceEnergy (W : ℝ → ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) : ℝ :=
  ∫ u : ℝ, W u * (x.2.2.1.1 u) ^ 2

/-- Weighted `L²` source cone `{x | 0 ≤ x · H ∧ 0 ≤ x · V ∧ ∫ W(u) f(u)² du ≤ S.polar x x}`. -/
def weightedL2SourceCone (W : ℝ → ℝ) (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  (scalingSubsurface V).sourceCone (weightedL2SourceEnergy W V)

theorem riemannKernelReal_neg_eq (x : ℝ) : riemannKernelReal (-x) = riemannKernelReal x := by
  rw [← riemannKernelReal_abs' (-x), abs_neg, riemannKernelReal_abs' x]

/-- **Unconditional No-Hardy-Weight Law for Source-Defined Cones (`oddRealTestsAt r` and `realTestsAt r`):**
For **every** locally integrable weight `W : ℝ → ℝ` with `W ≥ 0` and `0 < volume {x | 0 < W x}`,
there exists a finite aperture `r > 0` at which `weightedL2SourceCone W (oddRealTestsAt r)` and
`weightedL2SourceCone W (realTestsAt r)` unconditionally fail `RiemannRochAxiom` (even under RH). -/
theorem not_forall_aperture_weightedL2SourceCone_riemannRoch {W : ℝ → ℝ}
    (hW0 : ∀ x : ℝ, 0 ≤ W x) (hWi : LocallyIntegrable W) (hWpos : 0 < volume {x | 0 < W x}) :
    (∃ r : ℝ, 0 < r ∧
        ¬ (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
          (weightedL2SourceCone W (oddRealTestsAt r))) ∧
      (∃ r : ℝ, 0 < r ∧
        ¬ (scalingSubsurface (realTestsAt r)).RiemannRochAxiom
          (weightedL2SourceCone W (realTestsAt r))) := by
  obtain ⟨v, hv, hvc, hodd_v, hlt⟩ :=
    exists_odd_markovEnergy_lt_integral_weight_mul_sq hW0 hWi hWpos
  let F : ℝ → ℝ := phiDoobTest v
  have hF2 : ContDiff ℝ 2 F := contDiff_phiDoobTest hv
  have hFc : HasCompactSupport F := hasCompactSupport_phiDoobTest hvc
  have hF_odd : ∀ x : ℝ, F (-x) = -F x := fun x => by
    unfold F phiDoobTest
    rw [riemannKernelReal_neg_eq, hodd_v x]
    ring
  obtain ⟨R, -, hR_supp⟩ := exists_support_radius hFc
  set r : ℝ := max R 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have htsupp : tsupport F ⊆ Icc (-r) r := by
    refine tsupport_subset_Icc_of_vanish_outside fun u hu => ?_
    exact hR_supp u (lt_of_le_of_lt (le_max_left R 1) hu)
  have hweil_le : weilPair F F < ∫ x : ℝ, W x * F x ^ 2 := by
    rw [weilPair_self_eq_fullZeroForm hF2 hFc]
    have heven0 : evenPoleMoment F = 0 := evenPoleMoment_eq_zero_of_odd hF_odd
    have heven0_sq : evenPoleMoment F ^ 2 = 0 := by rw [heven0]; ring
    have hfull_le : fullZeroForm F ≤ _root_.RHTower.markovEnergy (fun x => (F x : ℂ)) := by
      unfold fullZeroForm
      linarith [sq_nonneg (oddPoleMoment F)]
    exact hfull_le.trans_lt hlt
  have hnn : ∀ (V : Submodule ℝ realTests) (x : ℝ × ℝ × V),
      0 ≤ weightedL2SourceEnergy W V x :=
    fun V x => integral_nonneg fun u => mul_nonneg (hW0 u) (sq_nonneg _)
  have heven_E : ∀ (V : Submodule ℝ realTests) (x : ℝ × ℝ × V),
      weightedL2SourceEnergy W V (-x) = weightedL2SourceEnergy W V x := by
    intro V x
    simp [weightedL2SourceEnergy]
  have hfib_E : ∀ (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) (a b : ℝ),
      weightedL2SourceEnergy W V
        (x + a • (scalingSubsurface V).H + b • (scalingSubsurface V).V) =
      weightedL2SourceEnergy W V x := by
    intro V x a b
    simp [weightedL2SourceEnergy, scalingSubsurface, scalingSurface]
  constructor
  · refine ⟨r, hr, fun hRR => ?_⟩
    have hle := ((scalingSubsurface (oddRealTestsAt r)).sourceCone_riemannRoch_iff_le_defect
      (hnn _) (heven_E _) (hfib_E _)).mp hRR
      (0, 0, ⟨⟨F, hF2, hFc⟩, htsupp, hF_odd⟩)
    rw [scalingSubsurface_defect_self] at hle
    exact not_lt_of_ge hle hweil_le
  · refine ⟨r, hr, fun hRR => ?_⟩
    have hle := ((scalingSubsurface (realTestsAt r)).sourceCone_riemannRoch_iff_le_defect
      (hnn _) (heven_E _) (hfib_E _)).mp hRR
      (0, 0, ⟨⟨F, hF2, hFc⟩, htsupp⟩)
    rw [scalingSubsurface_defect_self] at hle
    exact not_lt_of_ge hle hweil_le

/-- **Unconditional Doubly-Exponential Gaussian Ceiling on `L²` Source Coercivity (`r ≥ 3`):**
There exists a universal constant `K > 0` such that for every aperture `r ≥ 3` and every `c ∈ ℝ`,
if `(scalingSubsurface (realTestsAt r)).RiemannRochAxiom (gradedL2SourceCone c (realTestsAt r))`
(or `(scalingSubsurface (evenRealTestsAt r)).RiemannRochAxiom (gradedL2SourceCone c (evenRealTestsAt r))`,
or for `c > 0`, `RiemannRochAxiom (l2SourceCone c (realTestsAt r))`) holds, then
`c ≤ K exp((11/2) r - π e^{2(r - 2)})`. -/
theorem exists_l2SourceCone_realTestsAt_coercivity_le_doubleExp :
    ∃ K : ℝ, 0 < K ∧ ∀ {r : ℝ}, 3 ≤ r → ∀ (c : ℝ),
      ((scalingSubsurface (realTestsAt r)).RiemannRochAxiom
          (gradedL2SourceCone c (realTestsAt r)) ∨
        (scalingSubsurface (evenRealTestsAt r)).RiemannRochAxiom
          (gradedL2SourceCone c (evenRealTestsAt r))) →
      c ≤ K * Real.exp (11 / 2 * r - Real.pi * Real.exp (2 * (r - 2))) := by
  obtain ⟨K₁, hK₁, hZ⟩ := exists_fullZeroForm_thetaPlateau_le
  set W := ∫ x, riemannKernelReal x * (Real.cosh (x / 2) + primeShiftConstant)
  set E := ∫ x : ℝ, Real.exp (-|1 / 2 * x|)
  have hW0 : 0 ≤ W := le_trans (tailWeight_nonneg 0) (tailWeight_le_total 0)
  have hE0 : 0 ≤ E := integral_nonneg fun x => (Real.exp_pos _).le
  have hκ := primeShiftConstant_nonneg
  have hm := riemannKernelReal_pos 1
  set m₀ := 2 * riemannKernelReal 1 ^ 2
  have hm₀ : 0 < m₀ := by positivity
  set C₀ := cuspDecayConst (riemannKernelPoly 0)
  have hC₀ : 0 ≤ C₀ := cuspDecayConst_nonneg (riemannKernelPoly 0)
  set K : ℝ := ((K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / m₀) * C₀ + 1
  have hK_pos : 0 < K := by positivity
  refine ⟨K, hK_pos, fun {r} hr c hRR => ?_⟩
  set L := r - 2
  have hL1 : 1 ≤ L := by linarith
  have hlog : Real.log 2 / 2 ≤ L := by linarith [Real.log_two_lt_d9]
  let F : ℝ → ℝ := thetaPlateau L
  have hF_top : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_thetaPlateau L
  have hF2 : ContDiff ℝ 2 F := hF_top.of_le (WithTop.coe_le_coe.mpr le_top)
  have hFc : HasCompactSupport F := hasCompactSupport_thetaPlateau L
  have htsupp : tsupport F ⊆ Icc (-r) r :=
    (tsupport_thetaPlateau_subset L).trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have heven : ∀ u : ℝ, F (-u) = F u := fun u => by
    unfold F thetaPlateau
    rw [riemannKernelReal_neg_eq, smoothPlateau_neg]
  have hle_F : c * ∫ u : ℝ, F u ^ 2 ≤ fullZeroForm F := by
    rw [← weilPair_self_eq_fullZeroForm hF2 hFc]
    rcases hRR with hRR_all | hRR_ev
    · exact (gradedL2SourceCone_riemannRoch_iff_weilPair_ge c (realTestsAt r)).mp hRR_all
        ⟨⟨F, hF2, hFc⟩, htsupp⟩
    · exact (gradedL2SourceCone_riemannRoch_iff_weilPair_ge c (evenRealTestsAt r)).mp hRR_ev
        ⟨⟨F, hF2, hFc⟩, htsupp, heven⟩
  have hmass : m₀ ≤ ∫ u : ℝ, F u ^ 2 := two_mul_sq_riemannKernelReal_one_le hL1
  have hmass_pos : 0 < ∫ u : ℝ, F u ^ 2 := lt_of_lt_of_le hm₀ hmass
  have hτ := tailWeight_le hlog
  have hτ0 := tailWeight_nonneg L
  have hτW := tailWeight_le_total L
  have hZL := hZ L
  have hexp : Real.exp L ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
  have hΦL := (riemannKernelReal_pos L).le
  have hZτ : fullZeroForm F ≤ (K₁ + 2 * W) * tailWeight L := by nlinarith
  have hbound1 : fullZeroForm F ≤
      (K₁ + 2 * W) * ((1 + primeShiftConstant) * E) * (Real.exp r * riemannKernelReal L) := by
    have h1 : tailWeight L ≤ (1 + primeShiftConstant) * E * (Real.exp r * riemannKernelReal L) :=
      hτ.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hΦL) (by positivity))
    calc fullZeroForm F ≤ (K₁ + 2 * W) * tailWeight L := hZτ
      _ ≤ (K₁ + 2 * W) * ((1 + primeShiftConstant) * E * (Real.exp r * riemannKernelReal L)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hdiv : c ≤ ((K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / m₀) *
      (Real.exp r * riemannKernelReal L) := by
    have hc_div : c ≤ fullZeroForm F / ∫ u : ℝ, F u ^ 2 := (le_div_iff₀ hmass_pos).mpr hle_F
    refine hc_div.trans ?_
    rw [div_le_iff₀ hmass_pos]
    set R₀ := (K₁ + 2 * W) * ((1 + primeShiftConstant) * E) * (Real.exp r * riemannKernelReal L)
    have hR₀ : 0 ≤ R₀ := by positivity
    have hq : 1 ≤ (∫ u : ℝ, F u ^ 2) / m₀ := by rw [le_div_iff₀ hm₀, one_mul]; exact hmass
    have heq : ((K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / m₀) *
        (Real.exp r * riemannKernelReal L) * ∫ u : ℝ, F u ^ 2 =
        R₀ * ((∫ u : ℝ, F u ^ 2) / m₀) := by dsimp [R₀]; ring
    rw [heq]
    nlinarith
  have hG := riemannKernelReal_le_gaussian L
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ L)] at hG
  have hexp2 : Real.exp r * (Real.exp (9 / 2 * L) * Real.exp (-Real.pi * Real.exp (2 * L))) ≤
      Real.exp (11 / 2 * r - Real.pi * Real.exp (2 * (r - 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by dsimp [L]; nlinarith)
  have hK0 : 0 ≤ (K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / m₀ := by positivity
  calc c ≤ ((K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / m₀) *
        (Real.exp r * riemannKernelReal L) := hdiv
    _ ≤ ((K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / m₀) *
        (Real.exp r * (C₀ * Real.exp (9 / 2 * L) * Real.exp (-Real.pi * Real.exp (2 * L)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG (Real.exp_pos r).le) hK0
    _ = ((K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / m₀) * C₀ *
        (Real.exp r * (Real.exp (9 / 2 * L) * Real.exp (-Real.pi * Real.exp (2 * L)))) := by ring
    _ ≤ ((K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / m₀) * C₀ *
        Real.exp (11 / 2 * r - Real.pi * Real.exp (2 * (r - 2))) :=
        mul_le_mul_of_nonneg_left hexp2 (mul_nonneg hK0 hC₀)
    _ ≤ K * Real.exp (11 / 2 * r - Real.pi * Real.exp (2 * (r - 2))) :=
        mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (Real.exp_pos _).le

/-- **No Fixed Positive Global `L²` Coercivity Floor Across All Apertures (`c > 0`):**
For every fixed `c > 0`, there exists `r₀ ≥ 3` such that for all `r ≥ r₀`, `l2SourceCone c (realTestsAt r)`
and `l2SourceCone c (evenRealTestsAt r)` unconditionally fail `RiemannRochAxiom` (even under RH). -/
theorem not_forall_aperture_l2SourceCone_realTestsAt_riemannRoch {c : ℝ} (hc : 0 < c) :
    ∃ r₀ : ℝ, 3 ≤ r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
      ¬ (scalingSubsurface (realTestsAt r)).RiemannRochAxiom (l2SourceCone c (realTestsAt r)) ∧
      ¬ (scalingSubsurface (evenRealTestsAt r)).RiemannRochAxiom (l2SourceCone c (evenRealTestsAt r)) := by
  obtain ⟨K, hK, hceil⟩ := exists_l2SourceCone_realTestsAt_coercivity_le_doubleExp
  have hlim : Tendsto (fun r : ℝ => K * Real.exp (11 / 2 * r - Real.pi * Real.exp (2 * (r - 2))))
      atTop (𝓝 0) := by
    have hexp_bot : Tendsto (fun r : ℝ => 11 / 2 * r - Real.pi * Real.exp (2 * (r - 2)))
        atTop atBot := by
      refine tendsto_atBot_mono' atTop ?_
        (f₁ := fun r : ℝ => 11 / 2 * r - 2 * Real.pi * (r - 2) ^ 2) ?_
      · filter_upwards [eventually_ge_atTop 2] with r hr
        have hq := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (r - 2))
        have hπ := Real.pi_pos
        nlinarith [mul_le_mul_of_nonneg_left hq hπ.le, sq_nonneg (r - 2)]
      · refine tendsto_atBot.mpr fun b => ?_
        filter_upwards [eventually_ge_atTop (|b| + 10)] with r hr
        have hπ : 3 < Real.pi := Real.pi_gt_three
        have hb := le_abs_self b
        have hb' := neg_abs_le b
        nlinarith [sq_nonneg (r - 2), mul_le_mul_of_nonneg_left
          (show (r - 2) * 8 ≤ (r - 2) ^ 2 by nlinarith) (by linarith : (0 : ℝ) ≤ 2 * Real.pi)]
    simpa using (Real.tendsto_exp_atBot.comp hexp_bot).const_mul K
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hc))
  refine ⟨max r₁ 3, le_max_right r₁ 3, fun r hr => ?_⟩
  have hr3 : 3 ≤ r := (le_max_right r₁ 3).trans hr
  have hlt : K * Real.exp (11 / 2 * r - Real.pi * Real.exp (2 * (r - 2))) < c :=
    hr₁ r ((le_max_left r₁ 3).trans hr)
  rw [l2SourceCone_eq_gradedL2SourceCone hc.le (realTestsAt r),
    l2SourceCone_eq_gradedL2SourceCone hc.le (evenRealTestsAt r)]
  exact ⟨fun h => not_lt_of_ge (hceil hr3 c (Or.inl h)) hlt,
    fun h => not_lt_of_ge (hceil hr3 c (Or.inr h)) hlt⟩

/-- **Doubly-Exponential Decay Rate Forced on Any Positive Aperture Coercivity Profile:**
If an aperture-dependent `L²` source cone `l2SourceCone (m₀ e^{-B(r)}) (realTestsAt r)` (`m₀ > 0`)
satisfies `RiemannRochAxiom` at `r ≥ 3`, then its decay exponent `B(r)` must satisfy
`B(r) ≥ π e^{2(r - 2)} - (11/2) r + log(m₀ / K)`. -/
theorem exists_le_floorLoss_of_l2SourceCone_riemannRoch :
    ∃ K : ℝ, 0 < K ∧ ∀ {r m₀ : ℝ} (B : ℝ), 3 ≤ r → 0 < m₀ →
      (scalingSubsurface (realTestsAt r)).RiemannRochAxiom
        (l2SourceCone (m₀ * Real.exp (-B)) (realTestsAt r)) →
      Real.pi * Real.exp (2 * (r - 2)) - 11 / 2 * r + Real.log (m₀ / K) ≤ B := by
  obtain ⟨K, hK, hceil⟩ := exists_l2SourceCone_realTestsAt_coercivity_le_doubleExp
  refine ⟨K, hK, fun {r m₀} B hr hm₀ hRR => ?_⟩
  have hc : 0 < m₀ * Real.exp (-B) := mul_pos hm₀ (Real.exp_pos _)
  rw [l2SourceCone_eq_gradedL2SourceCone hc.le] at hRR
  have hle := hceil hr (m₀ * Real.exp (-B)) (Or.inl hRR)
  have hdiv : m₀ / K ≤ Real.exp (11 / 2 * r - Real.pi * Real.exp (2 * (r - 2)) + B) := by
    rw [div_le_iff₀ hK, Real.exp_add]
    have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_pos B).le
    have h1 : m₀ * Real.exp (-B) * Real.exp B = m₀ := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    linarith
  have hlog := Real.log_le_log (div_pos hm₀ hK) hdiv
  rw [Real.log_exp] at hlog
  linarith

/-- For a polar-constrained smooth interior source `u` at aperture `A`, both `Re u` and `Im u` have
vanishing even pole moment (`evenPoleMoment (Re u) = 0 ∧ evenPoleMoment (Im u) = 0`). -/
theorem evenPoleMoment_re_im_eq_zero_of_isPolarConstrained {A : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource A) (hu : IsPolarConstrained A u.toCCMFormVector) :
    evenPoleMoment (fun x => (u x).re) = 0 ∧ evenPoleMoment (fun x => (u x).im) = 0 := by
  have hp := hu.1
  have hm := hu.2
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector] at hp hm
  have hre_c : Continuous fun x => (u x).re := Complex.continuous_re.comp u.smooth.continuous
  have him_c : Continuous fun x => (u x).im := Complex.continuous_im.comp u.smooth.continuous
  have hre_cs : HasCompactSupport fun x => (u x).re := u.hasCompactSupport.comp_left Complex.zero_re
  have him_cs : HasCompactSupport fun x => (u x).im := u.hasCompactSupport.comp_left Complex.zero_im
  have hip : Integrable fun x : ℝ => (Real.exp (1 / 2 * x) : ℂ) * u x :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).mul u.smooth.continuous).integrable_of_hasCompactSupport
      u.hasCompactSupport.mul_left
  have him' : Integrable fun x : ℝ => (Real.exp (-1 / 2 * x) : ℂ) * u x :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).mul u.smooth.continuous).integrable_of_hasCompactSupport
      u.hasCompactSupport.mul_left
  have hre_p : expHalfMoment (fun x => (u x).re) = 0 := by
    have h := (integral_re hip).symm
    simp only [hp, map_zero, RCLike.re_to_complex] at h
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h.symm
    show (u x).re * Real.exp (x / 2) = (((Real.exp (1 / 2 * x) : ℂ) * u x).re)
    rw [Complex.re_ofReal_mul, show 1 / 2 * x = x / 2 by ring, mul_comm]
  have hre_m : expNegHalfMoment (fun x => (u x).re) = 0 := by
    have h := (integral_re him').symm
    simp only [hm, map_zero, RCLike.re_to_complex] at h
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h.symm
    show (u x).re * Real.exp (-(x / 2)) = (((Real.exp (-1 / 2 * x) : ℂ) * u x).re)
    rw [Complex.re_ofReal_mul, show -1 / 2 * x = -(x / 2) by ring, mul_comm]
  have him_p : expHalfMoment (fun x => (u x).im) = 0 := by
    have h := (integral_im hip).symm
    simp only [hp, map_zero, RCLike.im_to_complex] at h
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h.symm
    show (u x).im * Real.exp (x / 2) = (((Real.exp (1 / 2 * x) : ℂ) * u x).im)
    rw [Complex.im_ofReal_mul, show 1 / 2 * x = x / 2 by ring, mul_comm]
  have him_m : expNegHalfMoment (fun x => (u x).im) = 0 := by
    have h := (integral_im him').symm
    simp only [hm, map_zero, RCLike.im_to_complex] at h
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h.symm
    show (u x).im * Real.exp (-(x / 2)) = (((Real.exp (-1 / 2 * x) : ℂ) * u x).im)
    rw [Complex.im_ofReal_mul, show -1 / 2 * x = -(x / 2) by ring, mul_comm]
  have h1 := expHalfMoment_eq hre_c hre_cs
  have h2 := expNegHalfMoment_eq hre_c hre_cs
  have h3 := expHalfMoment_eq him_c him_cs
  have h4 := expNegHalfMoment_eq him_c him_cs
  exact ⟨by linarith, by linarith⟩

/-- **Exact Closed-Aperture Polar Ground-Energy Coercivity Equivalence (`polarFreeSmoothRealTestsAt r`):**
For every aperture `r > 0` and every `c ∈ ℝ`, `(scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom (gradedL2SourceCone c (polarFreeSmoothRealTestsAt r))`
holds if and only if `c ≤ ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩`. -/
theorem polarFreeSmooth_gradedL2SourceCone_riemannRoch_iff {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
        (gradedL2SourceCone c (polarFreeSmoothRealTestsAt r)) ↔
      c ≤ ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩ := by
  rw [gradedL2SourceCone_riemannRoch_iff_weilPair_ge]
  let A : SuzukiPositiveAperture := ⟨r, hr⟩
  constructor
  · intro hfl
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨u, hu, hune, hlt⟩ := exists_polarConstrained_smooth_rayleigh_lt A hε
    have hpos : 0 < ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ ^ (2 : ℕ) :=
      pow_pos (norm_pos_iff.mpr hune) 2
    have hu_top : ContDiff ℝ (⊤ : ℕ∞) (u : ℝ → ℂ) := u.smooth
    have hu2 : ContDiff ℝ 2 (u : ℝ → ℂ) := hu_top.of_le (WithTop.coe_le_coe.mpr le_top)
    have hre_top : ContDiff ℝ (⊤ : ℕ∞) (fun x => (u x).re) := Complex.reCLM.contDiff.comp hu_top
    have him_top : ContDiff ℝ (⊤ : ℕ∞) (fun x => (u x).im) := Complex.imCLM.contDiff.comp hu_top
    have hre2 : ContDiff ℝ 2 (fun x => (u x).re) := Complex.reCLM.contDiff.comp hu2
    have him2 : ContDiff ℝ 2 (fun x => (u x).im) := Complex.imCLM.contDiff.comp hu2
    have hrec : HasCompactSupport (fun x => (u x).re) :=
      u.hasCompactSupport.comp_left Complex.zero_re
    have himc : HasCompactSupport (fun x => (u x).im) :=
      u.hasCompactSupport.comp_left Complex.zero_im
    have hus : tsupport (u : ℝ → ℂ) ⊆ Icc (-r) r := u.tsupport_subset.trans Ioo_subset_Icc_self
    have hre_supp : tsupport (fun x => (u x).re) ⊆ Icc (-r) r := by
      refine closure_minimal (fun x hx => ?_) isClosed_Icc
      exact hus (subset_tsupport (u : ℝ → ℂ) fun h0 => hx (by simp [h0]))
    have him_supp : tsupport (fun x => (u x).im) ⊆ Icc (-r) r := by
      refine closure_minimal (fun x hx => ?_) isClosed_Icc
      exact hus (subset_tsupport (u : ℝ → ℂ) fun h0 => hx (by simp [h0]))
    obtain ⟨hCre, hCim⟩ := evenPoleMoment_re_im_eq_zero_of_isPolarConstrained u hu
    obtain ⟨hSre, hSim⟩ := oddPoleMoment_re_im_eq_zero_of_isPolarConstrained u hu
    have h1 : c * ∫ x, (u x).re ^ 2 ≤ fullZeroForm (fun x => (u x).re) := by
      rw [← weilPair_self_eq_fullZeroForm hre2 hrec]
      exact hfl ⟨⟨fun x => (u x).re, hre2, hrec⟩, hre_top, hre_supp, hCre, hSre⟩
    have h2 : c * ∫ x, (u x).im ^ 2 ≤ fullZeroForm (fun x => (u x).im) := by
      rw [← weilPair_self_eq_fullZeroForm him2 himc]
      exact hfl ⟨⟨fun x => (u x).im, him2, himc⟩, him_top, him_supp, hCim, hSim⟩
    have hsplit := zeta_W_re_eq_fullZeroForm_re_add_im hu2 u.hasCompactSupport
    have i1 : Integrable (fun x => (u x).re ^ 2) :=
      (hre2.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
    have i2 : Integrable (fun x => (u x).im ^ 2) :=
      (him2.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
    have hnorm : (∫ x, ‖u x‖ ^ 2) = (∫ x, (u x).re ^ 2) + ∫ x, (u x).im ^ 2 := by
      rw [← integral_add i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hquad : c * ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ ^ (2 : ℕ) ≤
        ccmRestrictedWeilSourceQuadratic A u.toCCMFormVector := by
      rw [norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector,
        ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hsplit, hnorm, mul_add]
      linarith
    exact lt_of_le_of_lt ((le_div_iff₀ hpos).mpr hquad) hlt
  · intro hle f
    rw [weilPair_self_eq_fullZeroForm f.1.2.1 f.1.2.2]
    have h1 := polarGroundEnergy_mul_le_fullZeroForm_Icc A f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2
    have h2 : c * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤
        ccmRestrictedWeilPolarGroundEnergy A * ∫ u : ℝ, (f.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hle (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1

/-- **Exact Closed-Aperture Polar Ground-Energy Coercivity Equivalence for `l2SourceCone c` (`c > 0`):** -/
theorem polarFreeSmooth_l2SourceCone_riemannRoch_iff {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ↔
      c ≤ ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩ := by
  rw [l2SourceCone_eq_gradedL2SourceCone hc.le]
  exact polarFreeSmooth_gradedL2SourceCone_riemannRoch_iff hr c

/-- **Exact Equivalence Between `HodgeIndex` on `polarFreeSmoothRealTestsAt r` and `0 ≤ μ₀(r)`:** -/
theorem polarFreeSmooth_scalingSubsurface_hodgeIndex_iff {r : ℝ} (hr : 0 < r) :
    (scalingSubsurface (polarFreeSmoothRealTestsAt r)).HodgeIndex ↔
      0 ≤ ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩ := by
  rw [(scalingSubsurface (polarFreeSmoothRealTestsAt r)).hodgeIndex_iff_defect_nonneg,
    ← polarFreeSmooth_gradedL2SourceCone_riemannRoch_iff hr 0,
    gradedL2SourceCone_riemannRoch_iff_weilPair_ge]
  constructor
  · intro h f
    have hx := h (0, 0, f)
    rw [scalingSubsurface_defect_self] at hx
    linarith
  · intro h x
    rw [scalingSubsurface_defect_self]
    have hf := h x.2.2
    linarith

/-- **Strict-Monotonicity Self-Upgrade: All-Aperture `HodgeIndex` on `polarFreeSmoothRealTestsAt r`
Is Unconditionally Equivalent to Strictly Positive Aperture-Dependent `L²` Source Riemann–Roch,
Non-Vacuous Ampleness, and `RiemannHypothesis`:**
Because `r ↦ ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩` is strictly decreasing
(`strictAnti_ccmRestrictedWeilPolarGroundEnergy`), nonnegativity `0 ≤ μ₀(r)` across all apertures
automatically forces strict positivity `0 < μ₀(r + 1) ≤ μ₀(r)` at every finite aperture `r > 0`,
supplying simultaneous `RiemannRochAxiom`, non-vacuous `AmpleAxiom`, and `SurfaceRiemannRochAxiom 0 0`
for `l2SourceCone (ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩) (polarFreeSmoothRealTestsAt r)`. -/
theorem all_aperture_polarFreeSmooth_hodgeIndex_iff_ample_l2SourceCone :
    RiemannHypothesis ↔
      (∀ r : ℝ, 0 < r → (scalingSubsurface (polarFreeSmoothRealTestsAt r)).HodgeIndex) ∧
      (∀ (r : ℝ) (hr : 0 < r),
        0 < ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩ ∧
        (scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
          (l2SourceCone (ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩)
            (polarFreeSmoothRealTestsAt r)) ∧
        (scalingSubsurface (polarFreeSmoothRealTestsAt r)).AmpleAxiom
          (l2SourceCone (ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩)
            (polarFreeSmoothRealTestsAt r)) ∧
        (scalingSubsurface (polarFreeSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
          (l2SourceCone (ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩)
            (polarFreeSmoothRealTestsAt r))) := by
  rw [riemannHypothesis_iff_ccmRestrictedWeilPolarGroundEnergy_nonneg]
  constructor
  · intro hnn
    refine ⟨fun r hr => (polarFreeSmooth_scalingSubsurface_hodgeIndex_iff hr).mpr (hnn ⟨r, hr⟩),
      fun r hr => ?_⟩
    let A : SuzukiPositiveAperture := ⟨r, hr⟩
    let B : SuzukiPositiveAperture := ⟨r + 1, by linarith⟩
    have hlt : ccmRestrictedWeilPolarGroundEnergy B < ccmRestrictedWeilPolarGroundEnergy A :=
      strictAnti_ccmRestrictedWeilPolarGroundEnergy (show A < B by change r < r + 1; linarith)
    have hpos : 0 < ccmRestrictedWeilPolarGroundEnergy A :=
      lt_of_le_of_lt (hnn B) hlt
    have hRR : (scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone (ccmRestrictedWeilPolarGroundEnergy A) (polarFreeSmoothRealTestsAt r)) :=
      (polarFreeSmooth_l2SourceCone_riemannRoch_iff hr hpos).mpr le_rfl
    have hA : (scalingSubsurface (polarFreeSmoothRealTestsAt r)).AmpleAxiom
        (l2SourceCone (ccmRestrictedWeilPolarGroundEnergy A) (polarFreeSmoothRealTestsAt r)) :=
      l2SourceCone_ample hpos (polarFreeSmoothRealTestsAt r)
    have hle_def : ∀ x : ℝ × ℝ × polarFreeSmoothRealTestsAt r,
        l2SourceEnergy (ccmRestrictedWeilPolarGroundEnergy A) (polarFreeSmoothRealTestsAt r) x ≤
          (scalingSubsurface (polarFreeSmoothRealTestsAt r)).defect x x := by
      intro x
      rw [scalingSubsurface_defect_self]
      exact (l2SourceCone_riemannRoch_iff_weilPair_ge hpos _).mp hRR x.2.2
    have hSRR : (scalingSubsurface (polarFreeSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone (ccmRestrictedWeilPolarGroundEnergy A) (polarFreeSmoothRealTestsAt r)) :=
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).sourceCone_surfaceRiemannRoch_of_le_defect
        (l2SourceEnergy_neg _ _) (l2SourceEnergy_nonneg hpos.le _) hle_def
    exact ⟨hpos, hRR, hA, hSRR⟩
  · rintro ⟨hH, -⟩ A
    exact (polarFreeSmooth_scalingSubsurface_hodgeIndex_iff A.2).mp (hH A.1 A.2)

/-! ### 5. Sobolev Source Cones and the Unconditional Zero-Width Equivalence Across All Apertures -/

/-- **The `H¹` Sobolev Source Energy (`sobolevSourceEnergy c V`):**
`sobolevSourceEnergy c V (a, b, f) = c * (∫ f(u)² du + ∫ f'(u)² du)`, defined purely from the
source function `f` and its derivative `f'`. -/
def sobolevSourceEnergy (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) : ℝ :=
  c * ((∫ u : ℝ, (x.2.2.1.1 u) ^ 2) + ∫ u : ℝ, deriv x.2.2.1.1 u ^ 2)

/-- **The Closed `H¹` Sobolev Source Cone (`sobolevSourceCone c V`):** -/
def sobolevSourceCone (c : ℝ) (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  (scalingSubsurface V).sourceCone (sobolevSourceEnergy c V)

/-- **The Graded `H¹` Sobolev Source Cone (`gradedSobolevSourceCone c V`):** -/
def gradedSobolevSourceCone (c : ℝ) (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  (scalingSubsurface V).gradedSourceCone (sobolevSourceEnergy c V)

theorem sobolevSourceEnergy_neg (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    sobolevSourceEnergy c V (-x) = sobolevSourceEnergy c V x := by
  change c * ((∫ u : ℝ, (-x.2.2.1.1 u) ^ 2) + ∫ u : ℝ, deriv (-x.2.2.1.1) u ^ 2) =
    c * ((∫ u : ℝ, (x.2.2.1.1 u) ^ 2) + ∫ u : ℝ, deriv x.2.2.1.1 u ^ 2)
  have hd : ∀ u : ℝ, deriv (-x.2.2.1.1) u ^ 2 = deriv x.2.2.1.1 u ^ 2 := fun u => by
    rw [deriv.neg, neg_sq]
  simp_rw [neg_sq, hd]

theorem sobolevSourceEnergy_add_fibres (c : ℝ) (V : Submodule ℝ realTests)
    (x : ℝ × ℝ × V) (a b : ℝ) :
    sobolevSourceEnergy c V (x + a • (scalingSubsurface V).H + b • (scalingSubsurface V).V) =
      sobolevSourceEnergy c V x := by
  simp [sobolevSourceEnergy, scalingSubsurface, scalingSurface]

theorem sobolevSourceEnergy_nonneg {c : ℝ} (hc : 0 ≤ c) (V : Submodule ℝ realTests)
    (x : ℝ × ℝ × V) : 0 ≤ sobolevSourceEnergy c V x :=
  mul_nonneg hc (add_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _))

/-- For every `c > 0`, `sobolevSourceCone c V` is contained in `l2SourceCone c V` and hence
satisfies `(scalingSubsurface V).AmpleAxiom` **unconditionally and non-vacuously**. -/
theorem sobolevSourceCone_subset_l2SourceCone {c : ℝ} (hc : 0 ≤ c) (V : Submodule ℝ realTests) :
    sobolevSourceCone c V ⊆ l2SourceCone c V := by
  intro x hx
  rw [sobolevSourceCone, (scalingSubsurface V).mem_sourceCone_iff] at hx
  rw [l2SourceCone, (scalingSubsurface V).mem_sourceCone_iff]
  refine ⟨hx.1, hx.2.1, ?_⟩
  have h1 : l2SourceEnergy c V x ≤ sobolevSourceEnergy c V x := by
    unfold l2SourceEnergy sobolevSourceEnergy
    have hd : 0 ≤ ∫ u : ℝ, deriv x.2.2.1.1 u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    nlinarith
  exact h1.trans hx.2.2

theorem sobolevSourceCone_ample {c : ℝ} (hc : 0 < c) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).AmpleAxiom (sobolevSourceCone c V) := by
  intro x hx hA y
  exact l2SourceCone_ample hc V x (sobolevSourceCone_subset_l2SourceCone hc.le V hx) hA y

/-- **Exact Quantitative Equivalence of `RiemannRochAxiom` for `gradedSobolevSourceCone c V` (All `c ∈ ℝ`):** -/
theorem gradedSobolevSourceCone_riemannRoch_iff_weilPair_ge (c : ℝ) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).RiemannRochAxiom (gradedSobolevSourceCone c V) ↔
      ∀ f : V, c * ((∫ u : ℝ, (f.1.1 u) ^ 2) + ∫ u : ℝ, deriv f.1.1 u ^ 2) ≤
        weilPair f.1.1 f.1.1 := by
  rw [gradedSobolevSourceCone,
    (scalingSubsurface V).gradedSourceCone_riemannRoch_iff_le_defect
      (sobolevSourceEnergy_neg c V) (sobolevSourceEnergy_add_fibres c V)]
  constructor
  · intro h f
    have hx := h (0, 0, f)
    rwa [scalingSubsurface_defect_self] at hx
  · intro h x
    rw [scalingSubsurface_defect_self]
    exact h x.2.2

/-- **Unconditional Exact Equivalence Between `zetaZeroWidth ≤ σ` and All-Aperture Graded Sobolev
Source Riemann–Roch (`realTestsAt r` and `oddRealTestsAt r`, All `σ ≥ 0`):**
For every strip width `σ ≥ 0`, `zetaZeroWidth ≤ σ` (every nontrivial zero `ρ` of `ζ` satisfies
`|Re ρ - 1/2| ≤ σ`) if and only if for every rate `β > σ` there exists `C ≥ 0` such that
`gradedSobolevSourceCone (-C e^{2β r})` satisfies `RiemannRochAxiom` across all apertures `r > 0`
on `realTestsAt r` (and equivalently on `oddRealTestsAt r`). -/
theorem zetaZeroWidth_le_iff_gradedSobolevSourceCone_riemannRoch {σ : ℝ} (hσ : 0 ≤ σ) :
    (zetaZeroWidth ≤ σ ↔
      ∀ β : ℝ, σ < β → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
        (scalingSubsurface (realTestsAt r)).RiemannRochAxiom
          (gradedSobolevSourceCone (-C * Real.exp (2 * β * r)) (realTestsAt r))) ∧
    (zetaZeroWidth ≤ σ ↔
      ∀ β : ℝ, σ < β → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
        (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
          (gradedSobolevSourceCone (-C * Real.exp (2 * β * r)) (oddRealTestsAt r))) := by
  constructor
  · rw [zetaZeroWidth_le_iff_scalingSubsurface_sobolev_defect_floor hσ]
    refine forall_congr' fun β => imp_congr_right fun _ => exists_congr fun C =>
      and_congr_right fun _ => forall_congr' fun r => imp_congr_right fun _ => ?_
    rw [gradedSobolevSourceCone_riemannRoch_iff_weilPair_ge]
    constructor
    · intro h f
      have hx := h (0, 0, f)
      rw [scalingSubsurface_defect_self] at hx
      linarith
    · intro h x
      rw [scalingSubsurface_defect_self]
      have hf := h x.2.2
      linarith
  · rw [zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor hσ]
    refine forall_congr' fun β => imp_congr_right fun _ => exists_congr fun C =>
      and_congr_right fun _ => forall_congr' fun r => imp_congr_right fun _ => ?_
    rw [gradedSobolevSourceCone_riemannRoch_iff_weilPair_ge]
    constructor
    · intro h f
      have hx := h (0, 0, f)
      rw [scalingSubsurface_defect_self] at hx
      linarith
    · intro h x
      rw [scalingSubsurface_defect_self]
      have hf := h x.2.2
      linarith

/-- **Zero-Width Bound from Graded `L²` Source Riemann–Roch on `polarFreeSmoothRealTestsAt r`:**
For every `σ ≥ 0`, if `gradedL2SourceCone (-C e^{2σ r}) (polarFreeSmoothRealTestsAt r)` satisfies
`RiemannRochAxiom` for all `r ≥ r₀`, then every nontrivial zero `ρ ∈ zetaZeroConfig.carrier`
satisfies `|ρ.re - 1/2| ≤ σ` (`zetaZeroWidth ≤ σ`). -/
theorem zetaZeroWidth_le_of_polarFreeSmooth_gradedL2SourceCone_riemannRoch {σ C r₀ : ℝ}
    (hσ : 0 ≤ σ)
    (hRR : ∀ (r : ℝ), 0 < r → r₀ ≤ r →
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
        (gradedL2SourceCone (-C * Real.exp (2 * σ * r)) (polarFreeSmoothRealTestsAt r))) :
    zetaZeroWidth ≤ σ ∧ ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ σ := by
  have hge : ∀ A : SuzukiPositiveAperture, r₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilPolarGroundEnergy A := by
    intro A hA
    have h := (polarFreeSmooth_gradedL2SourceCone_riemannRoch_iff A.2 _).mp (hRR A.1 A.2 hA)
    linarith
  have hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ σ :=
    fun ρ hρ => abs_re_sub_half_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp hσ hge hρ
  refine ⟨?_, hstrip⟩
  rw [zetaZeroWidth_le_iff_zetaZeroAbscissa_le hσ, zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ]
  exact fun ρ hρ => by linarith [(abs_le.mp (hstrip ρ hρ)).2]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
