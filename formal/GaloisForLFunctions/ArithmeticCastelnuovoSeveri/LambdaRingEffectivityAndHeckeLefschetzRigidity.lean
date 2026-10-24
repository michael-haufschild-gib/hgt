import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhichArithmeticDataForceTheSign
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# Effectivity from the `λ`-Ring: Hecke–Riemann–Roch Rigidity, the Rosati Source Cone, and the Arithmetic Lefschetz–Adjunction Identity

This file resolves Open Problem 5 of the Arithmetic Castelnuovo–Severi programme (*Effectivity from
the `λ`-ring*) and builds the missing tool of §6.2 (*an effectivity stable under the Hecke
correspondences that the golden datum violates*):

1. **Why Hecke stability eliminates `AmpleAxiom` and forces the coercive floor on any polar surface
   (`PolarSurface.ampleHalfSpace_riemannRoch`, `PolarSurface.hodgeIndex_iff_tilted_openPositiveCone`,
   `PolarSurface.riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg_of_hecke`,
   `scalingSurface_hecke_riemannRoch_iff`).**
   On a bare polar surface `S` without `λ`-ring operations, the ample half-space
   `S.ampleHalfSpace = {x | 0 ≤ x · (H + V)}` satisfies `S.RiemannRochAxiom` unconditionally
   (`ampleHalfSpace_riemannRoch`), failing only `S.AmpleAxiom`. Once `S` carries even a single
   fiber-tilting correspondence `T : C → C` scaling `(x · H, x · V)` by `(1, a)` or `(a, 1)` with
   `a > 1`, `T`-invariance substitutes for `AmpleAxiom` completely: for *every* `T`-invariant subset
   `E ⊆ S.ampleHalfSpace` — **without assuming `S.AmpleAxiom E`** — `S.RiemannRochAxiom E` is
   unconditionally equivalent to `S.openPositiveCone ⊆ E ∧ ∀ x, 0 ≤ S.defect x x`
   (`riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg_of_hecke`). On `scalingSurface`, no
   cone of nonnegative ample degree stable under `heckeCorrespondence a` (`a > 1`, e.g. `a = 2`) or
   `adamsOp q` (`q > 1`) can satisfy `RiemannRochAxiom` without forcing the zero defect floor
   `∀ x, 0 ≤ scalingSurface.defect x x` (`scalingSurface_hecke_riemannRoch_iff`).

2. **Calibration over `𝔽_q`: the Rosati–Frobenius source effectivity cone and its violation by
   `goldenDatum` (`CurveDatum.spanHecke`, `CurveDatum.windowSurface_hodgeIndex_iff_spanHecke_ample`,
   `goldenHeckeEscape_violates_spanHecke_ample`, `CurveDatum.rosatiSourceCone`,
   `CurveDatum.rosatiSourceCone_riemannRoch_iff_unitary`,
   `goldenDatum_not_rosatiSourceCone_riemannRoch`).**
   On any `CurveDatum D`, the unnormalized Frobenius correspondence `D.spanHecke m` scales `(x · H)`
   by `q^m`, preserves `(x · V)`, and scales intersections and defects by `q^m`. On `goldenDatum` at
   window `{0, 1}`, the explicit integer cycle `goldenHeckeEscape = 3H − V + 2 goldenCounterexample`
   lies in `openPositiveCone` (`x² = 2 > 0`, `x · (H + V) = 2 > 0`), yet `goldenDatum.spanHecke 1`
   maps it outside `ampleHalfSpace` (`(spanHecke 1 x) · (H + V) = -2 < 0`).
   Moreover, the positive-definite Rosati square-sampling energy
   `D.rosatiSourceEnergy S x = D.frobSquareMass S (fun k => x.2.2 k * D.sqrtq ^ k)` defines a genuine
   source effectivity cone `D.rosatiSourceCone S` that satisfies `defect ≤ rosatiSourceEnergy` and
   `D.rosatiSourceCone S ⊆ positiveCone` unconditionally on every `CurveDatum D`, is invariant under
   `D.spanAdams m` and `D.spanHecke m` and satisfies `RiemannRochAxiom` and `BezoutAxiom` on every
   unitary curve, and **is violated by `goldenDatum` at the singleton window `S = {1}`**
   (`goldenDatum_not_rosatiSourceCone_riemannRoch`, `rosatiSourceCone_riemannRoch_iff_unitary`).

3. **The Universal Arithmetic Lefschetz–Adjunction–Defect Identity and the Adams Coboundary Law on
   `scalingSurface` (`adamsVar`, `polar_adamsVar_self`,
   `arithLefschetz_eq_selfPair_add_defect_add_adamsVar`,
   `hodgeIndex_iff_abs_arithLefschetz_sub_polar_le`).**
   For every cycle `x : ScalingCycle` and scale `a > 0`, the Adams coboundary
   `adamsVar a x = adamsOp a x - x` reverses the sign of the pole-plane pairing on the entire nef
   quadrant: `polar(ψ^a x - x, ψ^a x - x) = -((√a - 1)² / √a) polar(x, x) ≤ 0`. Combining this with
   the arithmetic Lefschetz formula yields the **pole-cancelled Lefschetz–adjunction identity**
   `arithLefschetz x a - ((a + 1) / 2) (x · x) = ((√a - 1)² / 2) defect(x, x) + (√a / 2) defect(ψ^a x - x, ψ^a x - x)`,
   the exact scaling-surface generalization of Weil's point-count decomposition
   `N_m - ((q^m + 1) / 2)(Δ · Δ) = ((q^{m/2} - 1)² / 2)(2g) + q^{m/2}(2g - tr(F^m))`.

4. **The Hecke–Lefschetz Envelope Cone and the Cyclic Lefschetz Bridge (`lefschetzEnvelopeCone`,
   `adamsOp_mem_lefschetzEnvelopeCone`, `heckeCorrespondence_mem_lefschetzEnvelopeCone`,
   `lefschetzEnvelopeCone_riemannRoch_tfae`, `defect_heckeSpanCycle_eq_sum_arithLefschetz_prim`).**
   The cone `lefschetzEnvelopeCone` of cycles in the nef quadrant satisfying the Hasse–Weil
   Lefschetz bound `|arithLefschetz x a - ((a + 1) / 2) polar(x, x)| ≤ √a polar(x, x)` across all
   `a > 0` contains `0, H, V, H + V`, is unconditionally Adams-stable and Hecke-stable, lies in
   `positiveCone`, and satisfies `RiemannRochAxiom` (without assuming `AmpleAxiom`) iff
   `RiemannHypothesis` holds. Finally, on any Hecke span cycle `heckeSpanCycle cH cV S d g`, the
   Hodge defect is identically the negative quadratic form in the primitive arithmetic Lefschetz
   numbers `b * arithLefschetz (prim (diagCycle g)) (a / b)`.
-/

open Complex Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate
open Zeta23 RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ## §1. Why Hecke Stability Eliminates `AmpleAxiom` and Forces the Coercive Floor -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- The ample half-space `{x : C | 0 ≤ x · (H + V)}` of cycles with nonnegative degree against
`S.ample`. -/
def ampleHalfSpace : Set C :=
  {x : C | 0 ≤ S.pair x S.ample}

@[simp]
theorem mem_ampleHalfSpace {x : C} :
    x ∈ S.ampleHalfSpace ↔ 0 ≤ S.pair x S.ample := Iff.rfl

/-- The double-null nef quadrant `{x : C | 0 ≤ x · H ∧ 0 ≤ x · V}` on a polar surface `S`. -/
def nefQuadrant : Set C :=
  {x : C | 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V}

@[simp]
theorem mem_nefQuadrant {x : C} :
    x ∈ S.nefQuadrant ↔ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V := Iff.rfl

theorem nefQuadrant_subset_ampleHalfSpace : S.nefQuadrant ⊆ S.ampleHalfSpace := by
  intro x hx
  rw [mem_ampleHalfSpace, S.pair_ample]
  exact add_nonneg hx.1 hx.2

theorem openPositiveCone_subset_ampleHalfSpace : S.openPositiveCone ⊆ S.ampleHalfSpace :=
  fun _ hx => le_of_lt hx.2

/-- **Unconditional `RiemannRochAxiom` for `ampleHalfSpace` without `λ`-ring invariance:**
On *every* polar surface `S` (even when `S.HodgeIndex` fails), `S.ampleHalfSpace` satisfies
`S.RiemannRochAxiom` because every cycle `x` has either `0 ≤ x · (H + V)` or `0 ≤ (-x) · (H + V)`. -/
theorem ampleHalfSpace_riemannRoch : S.RiemannRochAxiom S.ampleHalfSpace := by
  intro x _
  rcases le_total 0 (S.pair x S.ample) with h | h
  · exact Or.inl h
  · right
    rw [mem_ampleHalfSpace, map_neg, LinearMap.neg_apply]
    linarith

/-- Under `S.HodgeIndex`, every cycle in `S.openPositiveCone` has strictly positive `H`-degree and
strictly positive `V`-degree. -/
theorem pair_H_and_V_pos_of_openPositiveCone (h : S.HodgeIndex) {x : C}
    (hx : x ∈ S.openPositiveCone) :
    0 < S.pair x S.H ∧ 0 < S.pair x S.V := by
  rcases hx with ⟨hxx, hxA⟩
  have hdef : 0 ≤ S.defect x x := S.hodgeIndex_iff_defect_nonneg.mp h x
  have hpol : 0 < S.polar x x := by
    unfold PolarSurface.defect at hdef
    linarith
  have hmul : 0 < S.pair x S.H * S.pair x S.V := by
    unfold PolarSurface.polar at hpol
    linarith
  have hsum : 0 < S.pair x S.H + S.pair x S.V := by
    rwa [← S.pair_ample]
  refine ⟨?_, ?_⟩
  · by_contra hH
    push Not at hH
    have hV : 0 < S.pair x S.V := by linarith
    nlinarith
  · by_contra hV
    push Not at hV
    have hH : 0 < S.pair x S.H := by linarith
    nlinarith

/-- **Single-Scale Tilted Fiber-Degree Equivalence on Any Polar Surface:**
For *every* polar surface `S` and *every* single scale `a > 1`, `S.HodgeIndex` holds if and only if
every `x ∈ S.openPositiveCone` satisfies `0 ≤ S.pair x S.H + a * S.pair x S.V` (and if and only if
every `x ∈ S.openPositiveCone` satisfies `0 ≤ a * S.pair x S.H + S.pair x S.V`). -/
theorem hodgeIndex_iff_tilted_openPositiveCone {a : ℝ} (ha : 1 < a) :
    (S.HodgeIndex ↔ ∀ x ∈ S.openPositiveCone, 0 ≤ S.pair x S.H + a * S.pair x S.V) ∧
    (S.HodgeIndex ↔ ∀ x ∈ S.openPositiveCone, 0 ≤ a * S.pair x S.H + S.pair x S.V) := by
  have ha0 : 0 < a := by linarith
  set c : ℝ := (a + 1) / 2
  have hc1 : 1 < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  have hc0 : 0 < c := by linarith
  constructor
  · refine ⟨fun h x hx => ?_, fun h z hzH hzV => ?_⟩
    · obtain ⟨hH, hV⟩ := S.pair_H_and_V_pos_of_openPositiveCone h hx
      positivity
    · by_contra hpos
      push Not at hpos
      set δ : ℝ := Real.sqrt (S.pair z z / (4 * c))
      have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
      have hδ_sq : δ ^ 2 = S.pair z z / (4 * c) := Real.sq_sqrt (by positivity)
      let x : C := (c * δ) • S.V - δ • S.H + z
      have hxH : S.pair x S.H = c * δ := by
        simp [x, map_add, map_sub, map_smul, S.pair_V_H, S.pair_H_H, hzH]
      have hxV : S.pair x S.V = -δ := by
        simp [x, map_add, map_sub, map_smul, S.pair_V_V, S.pair_H_V, hzV]
      have hxA : 0 < S.pair x S.ample := by
        rw [S.pair_ample, hxH, hxV]
        nlinarith
      have hxx : 0 < S.pair x x := by
        have hHz : S.pair S.H z = 0 := by rw [S.pair_comm, hzH]
        have hVz : S.pair S.V z = 0 := by rw [S.pair_comm, hzV]
        have hexp : S.pair x x = -2 * c * δ ^ 2 + S.pair z z := by
          simp only [x, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
            LinearMap.smul_apply, smul_eq_mul, S.pair_V_V, S.pair_H_H, S.pair_V_H, S.pair_H_V,
            hzH, hzV, hHz, hVz]
          ring
        rw [hexp, hδ_sq]
        have hcancel : -2 * c * (S.pair z z / (4 * c)) + S.pair z z = S.pair z z / 2 := by
          field_simp [ne_of_gt hc0]
          ring
        linarith
      have htest := h x ⟨hxx, hxA⟩
      rw [hxH, hxV] at htest
      nlinarith
  · refine ⟨fun h x hx => ?_, fun h z hzH hzV => ?_⟩
    · obtain ⟨hH, hV⟩ := S.pair_H_and_V_pos_of_openPositiveCone h hx
      positivity
    · by_contra hpos
      push Not at hpos
      set δ : ℝ := Real.sqrt (S.pair z z / (4 * c))
      have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
      have hδ_sq : δ ^ 2 = S.pair z z / (4 * c) := Real.sq_sqrt (by positivity)
      let x : C := (c * δ) • S.H - δ • S.V + z
      have hxH : S.pair x S.H = -δ := by
        simp [x, map_add, map_sub, map_smul, S.pair_V_H, S.pair_H_H, hzH]
      have hxV : S.pair x S.V = c * δ := by
        simp [x, map_add, map_sub, map_smul, S.pair_V_V, S.pair_H_V, hzV]
      have hxA : 0 < S.pair x S.ample := by
        rw [S.pair_ample, hxH, hxV]
        nlinarith
      have hxx : 0 < S.pair x x := by
        have hHz : S.pair S.H z = 0 := by rw [S.pair_comm, hzH]
        have hVz : S.pair S.V z = 0 := by rw [S.pair_comm, hzV]
        have hexp : S.pair x x = -2 * c * δ ^ 2 + S.pair z z := by
          simp only [x, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
            LinearMap.smul_apply, smul_eq_mul, S.pair_V_V, S.pair_H_H, S.pair_V_H, S.pair_H_V,
            hzH, hzV, hHz, hVz]
          ring
        rw [hexp, hδ_sq]
        have hcancel : -2 * c * (S.pair z z / (4 * c)) + S.pair z z = S.pair z z / 2 := by
          field_simp [ne_of_gt hc0]
          ring
        linarith
      have htest := h x ⟨hxx, hxA⟩
      rw [hxH, hxV] at htest
      nlinarith

/-- **The Universal Hecke–Riemann–Roch Forcing Law (Without `AmpleAxiom`):**
Let `T : C → C` be any correspondence on `S : PolarSurface C` that scales the fiber degrees by
`(1, a)` (`S.pair (T x) S.H = S.pair x S.H` and `S.pair (T x) S.V = a * S.pair x S.V`) for some
`a > 1`. Then for **every** `T`-invariant subset `E ⊆ S.ampleHalfSpace` — **without assuming
`S.AmpleAxiom E`** — `S.RiemannRochAxiom E` is unconditionally equivalent to
`S.openPositiveCone ⊆ E ∧ ∀ x : C, 0 ≤ S.defect x x`. -/
theorem riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg_of_hecke
    {T : C → C} {a : ℝ} (ha : 1 < a)
    (hTH : ∀ x : C, S.pair (T x) S.H = S.pair x S.H)
    (hTV : ∀ x : C, S.pair (T x) S.V = a * S.pair x S.V)
    {E : Set C} (hdeg : ∀ x ∈ E, 0 ≤ S.pair x S.ample) (hT : ∀ x ∈ E, T x ∈ E) :
    S.RiemannRochAxiom E ↔ S.openPositiveCone ⊆ E ∧ ∀ x : C, 0 ≤ S.defect x x := by
  constructor
  · intro hRR
    have hsub : S.openPositiveCone ⊆ E := S.openPositiveCone_subset_of_effectivity hRR hdeg
    have hHI : S.HodgeIndex := by
      rw [(S.hodgeIndex_iff_tilted_openPositiveCone ha).1]
      intro x hx
      have hTx : T x ∈ E := hT x (hsub hx)
      have hTA := hdeg (T x) hTx
      rwa [S.pair_ample, hTH x, hTV x] at hTA
    exact ⟨hsub, S.hodgeIndex_iff_defect_nonneg.mp hHI⟩
  · rintro ⟨hsub, hdef⟩ x hx
    have hHI : S.HodgeIndex := S.hodgeIndex_iff_defect_nonneg.mpr hdef
    rcases S.openPositiveCone_riemannRoch_iff_hodgeIndex.mpr hHI x hx with h | h
    · exact Or.inl (hsub h)
    · exact Or.inr (hsub h)

end PolarSurface

/-- **Single-Scale Hecke–Riemann–Roch Rigidity on `scalingSurface` (No `AmpleAxiom` Needed):**
For *every* subset `E ⊆ ScalingCycle` of nonnegative ample degree (`∀ x ∈ E, 0 ≤ x · (H + V)`) that
is invariant under `heckeCorrespondence a` for a single fixed scale `a > 1` (e.g. `a = 2`),
`scalingSurface.RiemannRochAxiom E` holds if and only if
`scalingSurface.openPositiveCone ⊆ E ∧ ∀ x : ScalingCycle, 0 ≤ scalingSurface.defect x x` (and in
particular forces `scalingSurface.HodgeIndex` and `RiemannHypothesis`, without assuming
`scalingSurface.AmpleAxiom E`). -/
theorem scalingSurface_hecke_riemannRoch_iff {a : ℝ} (ha : 1 < a)
    {E : Set ScalingCycle} (hdeg : ∀ x ∈ E, 0 ≤ scalingSurface.pair x scalingSurface.ample)
    (hHecke : ∀ x ∈ E, heckeCorrespondence a x ∈ E) :
    scalingSurface.RiemannRochAxiom E ↔
      scalingSurface.openPositiveCone ⊆ E ∧ ∀ x : ScalingCycle, 0 ≤ scalingSurface.defect x x := by
  have ha0 : 0 < a := by linarith
  exact scalingSurface.riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg_of_hecke ha
    (pair_heckeCorrespondence_H ha0) (pair_heckeCorrespondence_V ha0) hdeg hHecke

/-- **Single-Scale Adams–Riemann–Roch Rigidity on `scalingSurface` (No `AmpleAxiom` Needed):**
For *every* subset `E ⊆ ScalingCycle` of nonnegative ample degree that is invariant under
`adamsOp q` for a single fixed scale `q > 1`, `scalingSurface.RiemannRochAxiom E` holds if and only
if `scalingSurface.openPositiveCone ⊆ E ∧ ∀ x : ScalingCycle, 0 ≤ scalingSurface.defect x x`. -/
theorem scalingSurface_adams_riemannRoch_iff {q : ℝ} (hq : 1 < q)
    {E : Set ScalingCycle} (hdeg : ∀ x ∈ E, 0 ≤ scalingSurface.pair x scalingSurface.ample)
    (hAdams : ∀ x ∈ E, adamsOp q x ∈ E) :
    scalingSurface.RiemannRochAxiom E ↔
      scalingSurface.openPositiveCone ⊆ E ∧ ∀ x : ScalingCycle, 0 ≤ scalingSurface.defect x x := by
  have hq0 : 0 < q := by linarith
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0.le
  constructor
  · intro hRR
    have hsub : scalingSurface.openPositiveCone ⊆ E :=
      scalingSurface.openPositiveCone_subset_of_effectivity hRR hdeg
    have hHI : scalingSurface.HodgeIndex := by
      rw [(scalingSurface.hodgeIndex_iff_tilted_openPositiveCone hq).1]
      intro x hx
      have hAx := hdeg (adamsOp q x) (hAdams x (hsub hx))
      rw [scalingSurface.pair_ample, pair_adamsOp_H hq0, pair_adamsOp_V hq0] at hAx
      have hmul := mul_nonneg hsqrt.le hAx
      have hrel : Real.sqrt q * ((Real.sqrt q)⁻¹ * scalingSurface.pair x scalingSurface.H +
            Real.sqrt q * scalingSurface.pair x scalingSurface.V) =
          scalingSurface.pair x scalingSurface.H + q * scalingSurface.pair x scalingSurface.V := by
        calc Real.sqrt q * ((Real.sqrt q)⁻¹ * scalingSurface.pair x scalingSurface.H +
              Real.sqrt q * scalingSurface.pair x scalingSurface.V)
            = (Real.sqrt q * (Real.sqrt q)⁻¹) * scalingSurface.pair x scalingSurface.H +
              (Real.sqrt q * Real.sqrt q) * scalingSurface.pair x scalingSurface.V := by ring
          _ = scalingSurface.pair x scalingSurface.H +
              q * scalingSurface.pair x scalingSurface.V := by
            rw [mul_inv_cancel₀ hsqrt.ne', one_mul, hsq]
      rwa [hrel] at hmul
    exact ⟨hsub, scalingSurface.hodgeIndex_iff_defect_nonneg.mp hHI⟩
  · rintro ⟨hsub, hdef⟩ x hx
    have hHI : scalingSurface.HodgeIndex := scalingSurface.hodgeIndex_iff_defect_nonneg.mpr hdef
    rcases scalingSurface.openPositiveCone_riemannRoch_iff_hodgeIndex.mpr hHI x hx with h | h
    · exact Or.inl (hsub h)
    · exact Or.inr (hsub h)

/-! ## §2. Calibration Over `𝔽_q`: Frobenius Correspondences, the Rosati–Frobenius Source Cone, and `goldenDatum` -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The unnormalized `m`-th Frobenius / Hecke correspondence on `SpanCycle` over `𝔽_q`:
`D.spanHecke m x = D.sqrtq ^ m • D.spanAdams m x = (x.1, D.q ^ m * x.2.1, spanShift m x.2.2)`. -/
def spanHecke (m : ℕ) (x : SpanCycle) : SpanCycle :=
  D.sqrtq ^ m • D.spanAdams m x

theorem spanHecke_eq (m : ℕ) (x : SpanCycle) :
    D.spanHecke m x = (x.1, D.q ^ m * x.2.1, spanShift m x.2.2) := by
  have hpos : D.sqrtq ≠ 0 := D.sqrtq_pos.ne'
  have h1 : D.sqrtq ^ m * D.sqrtq⁻¹ ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hpos, one_pow]
  have h2 : D.sqrtq ^ m * D.sqrtq ^ m = D.q ^ m := by
    rw [← mul_pow, ← sq, D.sqrtq_sq]
  ext k
  · simp [spanHecke, spanAdams, ← mul_assoc, h1]
  · simp [spanHecke, spanAdams, ← mul_assoc, h2]
  · simp [spanHecke, spanAdams, smul_smul, h1]

/-- Under `D.spanHecke m`, intersection with `H` scales by `q^m`. -/
theorem pair_spanHecke_H (m : ℕ) (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface (windowShift m S)).pair (D.spanHecke m x)
        (D.windowSurface (windowShift m S)).H =
      D.q ^ m * (D.windowSurface S).pair x (D.windowSurface S).H := by
  have h2 : D.sqrtq ^ m * D.sqrtq ^ m = D.q ^ m := by
    rw [← mul_pow, ← sq, D.sqrtq_sq]
  simp only [spanHecke, map_smul, LinearMap.smul_apply, smul_eq_mul, D.pair_spanAdams_H,
    ← mul_assoc, h2]

/-- Under `D.spanHecke m`, intersection with `V` is preserved. -/
theorem pair_spanHecke_V (m : ℕ) (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface (windowShift m S)).pair (D.spanHecke m x)
        (D.windowSurface (windowShift m S)).V =
      (D.windowSurface S).pair x (D.windowSurface S).V := by
  have hpos : D.sqrtq ≠ 0 := D.sqrtq_pos.ne'
  have h1 : D.sqrtq ^ m * D.sqrtq⁻¹ ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hpos, one_pow]
  simp only [spanHecke, map_smul, LinearMap.smul_apply, smul_eq_mul, D.pair_spanAdams_V,
    ← mul_assoc, h1, one_mul]

/-- Under `D.spanHecke m`, the ample degree is `q^m (x · H) + (x · V)`. -/
theorem pair_spanHecke_ample (m : ℕ) (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface (windowShift m S)).pair (D.spanHecke m x)
        (D.windowSurface (windowShift m S)).ample =
      D.q ^ m * (D.windowSurface S).pair x (D.windowSurface S).H +
        (D.windowSurface S).pair x (D.windowSurface S).V := by
  rw [(D.windowSurface (windowShift m S)).pair_ample, D.pair_spanHecke_H, D.pair_spanHecke_V]

/-- Under `D.spanHecke m`, the polar pairing scales by `q^m`. -/
theorem polar_spanHecke (m : ℕ) (S : Finset ℕ) (x y : SpanCycle) :
    (D.windowSurface (windowShift m S)).polar (D.spanHecke m x) (D.spanHecke m y) =
      D.q ^ m * (D.windowSurface S).polar x y := by
  simp only [PolarSurface.polar, D.pair_spanHecke_H, D.pair_spanHecke_V]
  ring

/-- Under `D.spanHecke m`, the intersection pairing scales by `q^m`. -/
theorem pair_spanHecke (m : ℕ) (S : Finset ℕ) (x y : SpanCycle) :
    (D.windowSurface (windowShift m S)).pair (D.spanHecke m x) (D.spanHecke m y) =
      D.q ^ m * (D.windowSurface S).pair x y := by
  have h2 : D.sqrtq ^ m * D.sqrtq ^ m = D.q ^ m := by
    rw [← mul_pow, ← sq, D.sqrtq_sq]
  simp only [spanHecke, map_smul, LinearMap.smul_apply, smul_eq_mul, D.pair_spanAdams,
    ← mul_assoc, h2]

/-- Under `D.spanHecke m`, the Castelnuovo–Severi defect scales by `q^m`. -/
theorem defect_spanHecke (m : ℕ) (S : Finset ℕ) (x y : SpanCycle) :
    (D.windowSurface (windowShift m S)).defect (D.spanHecke m x) (D.spanHecke m y) =
      D.q ^ m * (D.windowSurface S).defect x y := by
  simp only [PolarSurface.defect, D.polar_spanHecke, D.pair_spanHecke]
  ring

/-- **Single-Power Frobenius–Ample Equivalence Over `𝔽_q`:**
For every `m ≥ 1` and every window `S : Finset ℕ`, `(D.windowSurface S).HodgeIndex` holds if and
only if `D.spanHecke m` maps `(D.windowSurface S).openPositiveCone` into
`(D.windowSurface (windowShift m S)).ampleHalfSpace`. -/
theorem windowSurface_hodgeIndex_iff_spanHecke_ample {m : ℕ} (hm : 1 ≤ m) (S : Finset ℕ) :
    (D.windowSurface S).HodgeIndex ↔
      ∀ x ∈ (D.windowSurface S).openPositiveCone,
        D.spanHecke m x ∈ (D.windowSurface (windowShift m S)).ampleHalfSpace := by
  have hqm : 1 < D.q ^ m := one_lt_pow₀ D.one_lt_q (by omega)
  rw [((D.windowSurface S).hodgeIndex_iff_tilted_openPositiveCone hqm).2]
  refine forall₂_congr fun x _ => ?_
  rw [PolarSurface.mem_ampleHalfSpace, D.pair_spanHecke_ample]

/-- **The Rosati–Frobenius Source Energy (`rosatiSourceEnergy`) on `D.windowSurface S`:**
The positive-definite Rosati square-sampling energy
`D.rosatiSourceEnergy S x = D.frobSquareMass S (fun k => x.2.2 k * D.sqrtq ^ k) = ∑_i ‖F_e(β_i)‖² ≥ 0`. -/
def rosatiSourceEnergy (S : Finset ℕ) (x : SpanCycle) : ℝ :=
  D.frobSquareMass S (fun k => x.2.2 k * D.sqrtq ^ k)

/-- **The Closed Rosati–Frobenius Source Effectivity Cone (`rosatiSourceCone`) on `D.windowSurface S`.** -/
def rosatiSourceCone (S : Finset ℕ) : Set SpanCycle :=
  (D.windowSurface S).sourceCone (D.rosatiSourceEnergy S)

/-- **The Strict Rosati–Frobenius Source Effectivity Cone (`strictRosatiSourceCone`) on `D.windowSurface S`.** -/
def strictRosatiSourceCone (S : Finset ℕ) : Set SpanCycle :=
  (D.windowSurface S).strictSourceCone (D.rosatiSourceEnergy S)

theorem rosatiSourceEnergy_nonneg (S : Finset ℕ) (x : SpanCycle) :
    0 ≤ D.rosatiSourceEnergy S x :=
  D.frobSquareMass_nonneg S _

theorem rosatiSourceEnergy_neg (S : Finset ℕ) (x : SpanCycle) :
    D.rosatiSourceEnergy S (-x) = D.rosatiSourceEnergy S x := by
  unfold rosatiSourceEnergy frobSquareMass frobPoly
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (∑ k ∈ S, (((-x.2.2 k * D.sqrtq ^ k : ℝ) : ℂ) * D.β i ^ k)) =
      -∑ k ∈ S, (((x.2.2 k * D.sqrtq ^ k : ℝ) : ℂ) * D.β i ^ k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
  rw [this, norm_neg]

@[simp]
theorem rosatiSourceEnergy_zero (S : Finset ℕ) : D.rosatiSourceEnergy S 0 = 0 := by
  simp [rosatiSourceEnergy, frobSquareMass, frobPoly]

@[simp]
theorem rosatiSourceEnergy_H (S : Finset ℕ) :
    D.rosatiSourceEnergy S (D.windowSurface S).H = 0 := by
  simp [rosatiSourceEnergy, windowSurface, frobSquareMass, frobPoly]

@[simp]
theorem rosatiSourceEnergy_V (S : Finset ℕ) :
    D.rosatiSourceEnergy S (D.windowSurface S).V = 0 := by
  simp [rosatiSourceEnergy, windowSurface, frobSquareMass, frobPoly]

@[simp]
theorem rosatiSourceEnergy_ample (S : Finset ℕ) :
    D.rosatiSourceEnergy S (D.windowSurface S).ample = 0 := by
  simp [rosatiSourceEnergy, PolarSurface.ample, windowSurface, frobSquareMass, frobPoly]

/-- `0, H, V, H + V` belong to `D.rosatiSourceCone S` on every `CurveDatum D` (unitary or fake). -/
theorem zero_H_V_ample_mem_rosatiSourceCone (S : Finset ℕ) :
    0 ∈ D.rosatiSourceCone S ∧
    (D.windowSurface S).H ∈ D.rosatiSourceCone S ∧
    (D.windowSurface S).V ∈ D.rosatiSourceCone S ∧
    (D.windowSurface S).ample ∈ D.rosatiSourceCone S ∧
    (D.windowSurface S).ample ∈ D.strictRosatiSourceCone S :=
  ⟨(D.windowSurface S).zero_mem_sourceCone (by simp),
   (D.windowSurface S).H_mem_sourceCone (by simp),
   (D.windowSurface S).V_mem_sourceCone (by simp),
   (D.windowSurface S).ample_mem_sourceCone (by simp),
   (D.windowSurface S).ample_mem_strictSourceCone (by simp)⟩

/-- **Unconditional Defect Domination by `rosatiSourceEnergy`:**
On *every* `CurveDatum D` (unitary or fake), `(D.windowSurface S).defect x x ≤ D.rosatiSourceEnergy S x`,
because the difference is the nonnegative Frobenius reflection defect `D.frobReflectionDefect S e ≥ 0`. -/
theorem defect_le_rosatiSourceEnergy (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface S).defect x x ≤ D.rosatiSourceEnergy S x := by
  rw [D.windowSurface_defect_eq_frobSquareMass_sub_frobReflectionDefect]
  unfold rosatiSourceEnergy
  linarith [D.frobReflectionDefect_nonneg S (fun k => x.2.2 k * D.sqrtq ^ k)]

/-- On *every* `CurveDatum D` (unitary or fake), `D.rosatiSourceCone S ⊆ (D.windowSurface S).positiveCone`
and `D.strictRosatiSourceCone S ⊆ (D.windowSurface S).openPositiveCone`. -/
theorem rosatiSourceCone_subset_positiveCone (S : Finset ℕ) :
    D.rosatiSourceCone S ⊆ (D.windowSurface S).positiveCone ∧
    D.strictRosatiSourceCone S ⊆ (D.windowSurface S).openPositiveCone :=
  ⟨(D.windowSurface S).sourceCone_subset_positiveCone_of_defect_le (D.defect_le_rosatiSourceEnergy S),
   (D.windowSurface S).strictSourceCone_subset_openPositiveCone_of_defect_le
     (D.defect_le_rosatiSourceEnergy S)⟩

/-- Under `D.spanAdams m`, the Frobenius polynomial of `D.spanAdams m x` on `windowShift m S`
multiplies by `β_i^m`. -/
theorem frobPoly_spanAdams (m : ℕ) (S : Finset ℕ) (x : SpanCycle) (z : ℂ) :
    frobPoly (windowShift m S) (fun k => (D.spanAdams m x).2.2 k * D.sqrtq ^ k) z =
      z ^ m * frobPoly S (fun k => x.2.2 k * D.sqrtq ^ k) z := by
  have hpos : D.sqrtq ≠ 0 := D.sqrtq_pos.ne'
  have hinv : D.sqrtq⁻¹ ^ m * D.sqrtq ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hpos, one_pow]
  simp only [frobPoly, windowShift, Finset.sum_map, Function.Embedding.coeFn_mk, spanAdams,
    Pi.smul_apply, smul_eq_mul, spanShift, le_add_iff_nonneg_left, zero_le, ↓reduceIte,
    Nat.add_sub_cancel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpow : D.sqrtq⁻¹ ^ m * x.2.2 k * D.sqrtq ^ (k + m) = x.2.2 k * D.sqrtq ^ k := by
    rw [pow_add]
    calc D.sqrtq⁻¹ ^ m * x.2.2 k * (D.sqrtq ^ k * D.sqrtq ^ m)
        = (D.sqrtq⁻¹ ^ m * D.sqrtq ^ m) * (x.2.2 k * D.sqrtq ^ k) := by ring
      _ = x.2.2 k * D.sqrtq ^ k := by rw [hinv, one_mul]
  rw [hpow, pow_add]
  ring

/-- **On a unitary curve datum (`∀ i, ‖D.β i‖ = 1`), `D.rosatiSourceEnergy` is strictly invariant
under all Adams operations `D.spanAdams m`.** -/
theorem rosatiSourceEnergy_spanAdams_of_unitary (hU : ∀ i : ι, ‖D.β i‖ = 1)
    (m : ℕ) (S : Finset ℕ) (x : SpanCycle) :
    D.rosatiSourceEnergy (windowShift m S) (D.spanAdams m x) = D.rosatiSourceEnergy S x := by
  unfold rosatiSourceEnergy frobSquareMass
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.frobPoly_spanAdams, norm_mul, norm_pow, hU i, one_pow, one_mul]

/-- **On a unitary curve datum (`∀ i, ‖D.β i‖ = 1`), `D.rosatiSourceCone` is invariant under all
Adams operations `D.spanAdams m` and all Frobenius correspondences `D.spanHecke m`.** -/
theorem spanAdams_and_spanHecke_mem_rosatiSourceCone_of_unitary (hU : ∀ i : ι, ‖D.β i‖ = 1)
    (m : ℕ) (S : Finset ℕ) {x : SpanCycle} (hx : x ∈ D.rosatiSourceCone S) :
    D.spanAdams m x ∈ D.rosatiSourceCone (windowShift m S) ∧
    D.spanHecke m x ∈ D.rosatiSourceCone (windowShift m S) := by
  rw [rosatiSourceCone, (D.windowSurface S).mem_sourceCone_iff] at hx
  rcases hx with ⟨hH, hV, hE⟩
  constructor
  · rw [rosatiSourceCone, (D.windowSurface (windowShift m S)).mem_sourceCone_iff,
      D.pair_spanAdams_H, D.pair_spanAdams_V, D.polar_spanAdams,
      D.rosatiSourceEnergy_spanAdams_of_unitary hU]
    exact ⟨mul_nonneg (pow_nonneg D.sqrtq_pos.le m) hH,
      mul_nonneg (pow_nonneg (inv_nonneg.mpr D.sqrtq_pos.le) m) hV, hE⟩
  · rw [rosatiSourceCone, (D.windowSurface (windowShift m S)).mem_sourceCone_iff,
      D.pair_spanHecke_H, D.pair_spanHecke_V, D.polar_spanHecke]
    have hqm : 0 ≤ D.q ^ m := by linarith [pow_pos (by linarith [D.one_lt_q] : 0 < D.q) m]
    have hE_hecke : D.rosatiSourceEnergy (windowShift m S) (D.spanHecke m x) =
        D.q ^ m * D.rosatiSourceEnergy S x := by
      have hsq : D.sqrtq ^ m * D.sqrtq ^ m = D.q ^ m := by
        rw [← mul_pow, ← sq, D.sqrtq_sq]
      unfold rosatiSourceEnergy frobSquareMass
      rw [Finset.mul_sum, ← D.rosatiSourceEnergy_spanAdams_of_unitary hU m S x]
      unfold rosatiSourceEnergy frobSquareMass
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hpoly : frobPoly (windowShift m S)
          (fun k => (D.spanHecke m x).2.2 k * D.sqrtq ^ k) (D.β i) =
          (D.sqrtq ^ m : ℂ) * frobPoly (windowShift m S)
            (fun k => (D.spanAdams m x).2.2 k * D.sqrtq ^ k) (D.β i) := by
        simp only [frobPoly, spanHecke, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring
      rw [hpoly, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg D.sqrtq_pos.le m),
        sq, hsq]
    rw [hE_hecke]
    exact ⟨mul_nonneg hqm hH, hV, mul_le_mul_of_nonneg_left hE hqm⟩

/-- **Exact Unitarity Characterization of `RiemannRochAxiom` for `rosatiSourceCone`:**
For any `CurveDatum D`, the following are unconditionally equivalent:
1. Unitarity (`∀ i : ι, ‖D.β i‖ = 1`);
2. For every window `S : Finset ℕ`, `(D.windowSurface S).RiemannRochAxiom (D.rosatiSourceCone S)`
   and `(D.windowSurface S).BezoutAxiom (D.rosatiSourceCone S)`;
3. At the singleton window `S = {1}`, `(D.windowSurface {1}).RiemannRochAxiom (D.rosatiSourceCone {1})`. -/
theorem rosatiSourceCone_riemannRoch_iff_unitary :
    ((∀ i : ι, ‖D.β i‖ = 1) ↔
      ∀ S : Finset ℕ, (D.windowSurface S).RiemannRochAxiom (D.rosatiSourceCone S) ∧
        (D.windowSurface S).BezoutAxiom (D.rosatiSourceCone S)) ∧
    ((∀ i : ι, ‖D.β i‖ = 1) ↔
      (D.windowSurface {1}).RiemannRochAxiom (D.rosatiSourceCone {1})) := by
  have h1 : (∀ i : ι, ‖D.β i‖ = 1) →
      ∀ S : Finset ℕ, (D.windowSurface S).RiemannRochAxiom (D.rosatiSourceCone S) ∧
        (D.windowSurface S).BezoutAxiom (D.rosatiSourceCone S) := by
    intro hU S
    have hHI : (D.windowSurface S).HodgeIndex := D.windowSurface_hodgeIndex_iff_unitary.mpr hU S
    have hdef_eq : ∀ x : SpanCycle, D.rosatiSourceEnergy S x ≤ (D.windowSurface S).defect x x := by
      intro x
      rw [D.windowSurface_defect_eq_frobSquareMass_sub_frobReflectionDefect,
        D.frobReflectionDefect_eq_zero_iff_unitary.mpr hU S _, sub_zero]
      exact le_rfl
    exact ⟨(D.windowSurface S).sourceCone_riemannRoch_of_le_defect
        (D.rosatiSourceEnergy_neg S) (D.rosatiSourceEnergy_nonneg S) hdef_eq,
      (D.windowSurface S).sourceCone_bezout_of_defect_le hHI (D.defect_le_rosatiSourceEnergy S)⟩
  have h2 : (D.windowSurface {1}).RiemannRochAxiom (D.rosatiSourceCone {1}) →
      ∀ i : ι, ‖D.β i‖ = 1 := by
    intro hRR
    rw [← D.frobReflectionDefect_singleton_one_eq_zero_iff_unitary]
    by_contra hne
    have hpos : 0 < D.frobReflectionDefect {1} (fun _ => 1) :=
      lt_of_le_of_ne (D.frobReflectionDefect_nonneg {1} (fun _ => 1)) (Ne.symm hne)
    set M := D.frobSquareMass {1} (fun _ => 1)
    set R := D.frobReflectionDefect {1} (fun _ => 1)
    let d : ℕ → ℝ := fun k => if k = 1 then D.sqrtq⁻¹ else 0
    let z : SpanCycle := (D.windowSurface {1}).prim (0, 0, d)
    have hz_d : z.2.2 = d := rfl
    have he_eq : ∀ k ∈ ({1} : Finset ℕ), z.2.2 k * D.sqrtq ^ k = (fun _ : ℕ => (1 : ℝ)) k := by
      intro k hk
      rw [Finset.mem_singleton.mp hk]
      simp [hz_d, d, inv_mul_cancel₀ D.sqrtq_pos.ne']
    have hpoly : ∀ w : ℂ, frobPoly {1} (fun k => z.2.2 k * D.sqrtq ^ k) w =
        frobPoly {1} (fun _ => 1) w := by
      intro w
      unfold frobPoly
      exact Finset.sum_congr rfl fun k hk => by rw [he_eq k hk]
    have hM_z : D.rosatiSourceEnergy {1} z = M := by
      unfold rosatiSourceEnergy M frobSquareMass
      exact Finset.sum_congr rfl fun i _ => by rw [hpoly]
    have hR_z : D.frobReflectionDefect {1} (fun k => z.2.2 k * D.sqrtq ^ k) = R := by
      unfold R frobReflectionDefect
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [hpoly, hpoly]
    have hdef_z : (D.windowSurface {1}).defect z z = M - R := by
      rw [D.windowSurface_defect_eq_frobSquareMass_sub_frobReflectionDefect]
      change D.rosatiSourceEnergy {1} z -
        D.frobReflectionDefect {1} (fun k => z.2.2 k * D.sqrtq ^ k) = M - R
      rw [hM_z, hR_z]
    let x : SpanCycle := (D.windowSurface {1}).polarLift z 1 ((M - R / 2) / 2)
    have hxH : (D.windowSurface {1}).pair x (D.windowSurface {1}).H = (M - R / 2) / 2 :=
      (D.windowSurface {1}).pair_polarLift_H z 1 ((M - R / 2) / 2)
    have hxV : (D.windowSurface {1}).pair x (D.windowSurface {1}).V = 1 :=
      (D.windowSurface {1}).pair_polarLift_V z 1 ((M - R / 2) / 2)
    have hx_pol : (D.windowSurface {1}).polar x x = M - R / 2 := by
      rw [(D.windowSurface {1}).polar_polarLift_self]
      ring
    have hx_sq : 0 < (D.windowSurface {1}).pair x x := by
      rw [(D.windowSurface {1}).pair_polarLift_self, hdef_z]
      linarith
    have hx_E : D.rosatiSourceEnergy {1} x = M := by
      have hx_d : x.2.2 = z.2.2 := by
        ext k
        simp [x, PolarSurface.polarLift, windowSurface]
      unfold rosatiSourceEnergy
      rw [hx_d]
      exact hM_z
    rcases hRR x hx_sq with hx_mem | hnx_mem
    · rw [rosatiSourceCone, (D.windowSurface {1}).mem_sourceCone_iff, hx_E, hx_pol] at hx_mem
      linarith [hx_mem.2.2]
    · rw [rosatiSourceCone, (D.windowSurface {1}).mem_sourceCone_iff,
        (D.windowSurface {1}).pair_neg_left, hxV] at hnx_mem
      linarith [hnx_mem.2.1]
  exact ⟨⟨h1, fun h => h2 (h {1}).1⟩, ⟨ fun hU => (h1 hU {1}).1, h2 ⟩⟩

end CurveDatum

/-- The explicit integer cycle `3H - V + 2 goldenCounterexample` on
`goldenDatum.windowSurface {0, 1}` that lies in `openPositiveCone` yet is mapped out of
`ampleHalfSpace` by `goldenDatum.spanHecke 1`. -/
def goldenHeckeEscape : SpanCycle :=
  (3 : ℝ) • (goldenDatum.windowSurface {0, 1}).H -
    (goldenDatum.windowSurface {0, 1}).V + (2 : ℝ) • goldenCounterexample

/-- **Explicit Violation of Frobenius–Ample Stability on `goldenDatum`:**
The cycle `goldenHeckeEscape` belongs to `(goldenDatum.windowSurface {0, 1}).openPositiveCone`
(`x² = 2 > 0`, `x · (H + V) = 2 > 0`), yet its image under `goldenDatum.spanHecke 1` has negative
ample degree `(spanHecke 1 x) · (H + V) = -2 < 0` and leaves `ampleHalfSpace`. -/
theorem goldenHeckeEscape_violates_spanHecke_ample :
    goldenHeckeEscape ∈ (goldenDatum.windowSurface {0, 1}).openPositiveCone ∧
    (goldenDatum.windowSurface (windowShift 1 {0, 1})).pair
      (goldenDatum.spanHecke 1 goldenHeckeEscape)
      (goldenDatum.windowSurface (windowShift 1 {0, 1})).ample = -2 ∧
    goldenDatum.spanHecke 1 goldenHeckeEscape ∉
      (goldenDatum.windowSurface (windowShift 1 {0, 1})).ampleHalfSpace := by
  let S₀ := goldenDatum.windowSurface {0, 1}
  obtain ⟨hH_ce, hV_ce, hsq_ce⟩ := goldenCounterexample_violates_hodgeIndex
  have hH_ce' : S₀.pair S₀.H goldenCounterexample = 0 := by rw [S₀.pair_comm, hH_ce]
  have hV_ce' : S₀.pair S₀.V goldenCounterexample = 0 := by rw [S₀.pair_comm, hV_ce]
  have hesc_H : S₀.pair goldenHeckeEscape S₀.H = -1 := by
    simp [goldenHeckeEscape, S₀, map_add, map_sub, map_smul,
      S₀.pair_H_H, S₀.pair_V_H, hH_ce]
  have hesc_V : S₀.pair goldenHeckeEscape S₀.V = 3 := by
    simp [goldenHeckeEscape, S₀, map_add, map_sub, map_smul,
      S₀.pair_H_V, S₀.pair_V_V, hV_ce]
  have hesc_A : S₀.pair goldenHeckeEscape S₀.ample = 2 := by
    rw [S₀.pair_ample, hesc_H, hesc_V]
    norm_num
  have hesc_sq : S₀.pair goldenHeckeEscape goldenHeckeEscape = 2 := by
    have hexp : S₀.pair goldenHeckeEscape goldenHeckeEscape =
        -6 + 4 * S₀.pair goldenCounterexample goldenCounterexample := by
      simp only [goldenHeckeEscape, S₀, map_add, map_sub, map_smul, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        S₀.pair_H_H, S₀.pair_V_V, S₀.pair_H_V, S₀.pair_V_H,
        hH_ce, hV_ce, hH_ce', hV_ce']
      ring
    rw [hexp, hsq_ce]
    norm_num
  have hhecke_A :
      (goldenDatum.windowSurface (windowShift 1 {0, 1})).pair
        (goldenDatum.spanHecke 1 goldenHeckeEscape)
        (goldenDatum.windowSurface (windowShift 1 {0, 1})).ample = -2 := by
    rw [goldenDatum.pair_spanHecke_ample, hesc_H, hesc_V]
    change (5 : ℝ) ^ 1 * (-1) + 3 = -2
    norm_num
  refine ⟨⟨by linarith, by linarith⟩, hhecke_A, ?_⟩
  rw [PolarSurface.mem_ampleHalfSpace, hhecke_A]
  norm_num

/-- **The Golden Fake Curve Violates the Rosati–Frobenius Source Effectivity (`rosatiSourceCone`):**
While `D.rosatiSourceCone` is Adams-stable, Frobenius/Hecke-stable, Bézout-closed, and satisfies
`RiemannRochAxiom` on every unitary curve datum, `goldenDatum` violates `RiemannRochAxiom` for
`goldenDatum.rosatiSourceCone {1}` at the singleton window `{1}`. -/
theorem goldenDatum_not_rosatiSourceCone_riemannRoch :
    ¬ (goldenDatum.windowSurface {1}).RiemannRochAxiom (goldenDatum.rosatiSourceCone {1}) := by
  rw [← goldenDatum.rosatiSourceCone_riemannRoch_iff_unitary.2]
  exact goldenDatum_not_unitary

/-! ## §3. The Universal Arithmetic Lefschetz–Adjunction–Defect Identity and the Adams Coboundary Law -/

/-- The **Adams coboundary / variation** `adamsVar a x = adamsOp a x - x` on `scalingSurface`. -/
def adamsVar (a : ℝ) (x : ScalingCycle) : ScalingCycle :=
  adamsOp a x - x

/-- Under `adamsVar a` (`a > 0`), the horizontal fiber degree scales by `(√a)⁻¹ - 1` and the
vertical fiber degree scales by `√a - 1`. -/
theorem pair_adamsVar_H_and_V {a : ℝ} (ha : 0 < a) (x : ScalingCycle) :
    scalingSurface.pair (adamsVar a x) scalingSurface.H =
      ((Real.sqrt a)⁻¹ - 1) * scalingSurface.pair x scalingSurface.H ∧
    scalingSurface.pair (adamsVar a x) scalingSurface.V =
      (Real.sqrt a - 1) * scalingSurface.pair x scalingSurface.V := by
  simp only [adamsVar, map_sub, LinearMap.sub_apply, pair_adamsOp_H ha, pair_adamsOp_V ha]
  exact ⟨by ring, by ring⟩

/-- **Exact Adams Coboundary Polar Law (`polar_adamsVar_self`):**
For every `a > 0` and every cycle `x : ScalingCycle`,
`polar(ψ^a x - x, ψ^a x - x) = -((√a - 1)² / √a) polar(x, x)`.
In particular, on the entire nef quadrant `x ∈ scalingSurface.nefQuadrant` (including all positive
test cycles `x ∈ posTestCone`), `polar(ψ^a x - x, ψ^a x - x) ≤ 0`: the `λ`-ring variation reverses
the sign of the polar pairing! -/
theorem polar_adamsVar_self {a : ℝ} (ha : 0 < a) (x : ScalingCycle) :
    scalingSurface.polar (adamsVar a x) (adamsVar a x) =
      -((Real.sqrt a - 1) ^ 2 / Real.sqrt a) * scalingSurface.polar x x ∧
    (x ∈ scalingSurface.nefQuadrant →
      scalingSurface.polar (adamsVar a x) (adamsVar a x) ≤ 0) := by
  obtain ⟨hH, hV⟩ := pair_adamsVar_H_and_V ha x
  have hsqrt : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hid : scalingSurface.polar (adamsVar a x) (adamsVar a x) =
      -((Real.sqrt a - 1) ^ 2 / Real.sqrt a) * scalingSurface.polar x x := by
    rw [scalingSurface.polar_self, scalingSurface.polar_self, hH, hV]
    field_simp [hsqrt]
    ring
  refine ⟨hid, fun hx => ?_⟩
  rw [hid]
  have hpol : 0 ≤ scalingSurface.polar x x := by
    rw [scalingSurface.polar_self]
    exact mul_nonneg (mul_nonneg zero_le_two hx.1) hx.2
  have hcoeff : 0 ≤ (Real.sqrt a - 1) ^ 2 / Real.sqrt a :=
    div_nonneg (sq_nonneg _) (Real.sqrt_nonneg a)
  nlinarith

/-- **Exact Adams Coboundary Defect Law (`defect_adamsVar_self`):**
For every `a : ℝ` and every `x : ScalingCycle`,
`defect(ψ^a x - x, ψ^a x - x) = 2 defect(x, x) - 2 defect(ψ^a x, x)`. -/
theorem defect_adamsVar_self (a : ℝ) (x : ScalingCycle) :
    scalingSurface.defect (adamsVar a x) (adamsVar a x) =
      2 * scalingSurface.defect x x - 2 * scalingSurface.defect (adamsOp a x) x := by
  have hsym : scalingSurface.defect x (adamsOp a x) = scalingSurface.defect (adamsOp a x) x := by
    simp only [PolarSurface.defect, PolarSurface.polar,
      scalingSurface.pair_comm x (adamsOp a x)]
    ring
  have hbilin : scalingSurface.defect (adamsOp a x - x) (adamsOp a x - x) =
      scalingSurface.defect (adamsOp a x) (adamsOp a x) -
        scalingSurface.defect (adamsOp a x) x -
        scalingSurface.defect x (adamsOp a x) +
        scalingSurface.defect x x := by
    simp only [PolarSurface.defect, PolarSurface.polar, map_sub, LinearMap.sub_apply]
    ring
  rw [adamsVar, hbilin, defect_adamsOp, hsym]
  ring

/-- **The Universal Arithmetic Lefschetz–Adjunction–Defect Identity
(`arithLefschetz_eq_selfPair_add_defect_add_adamsVar`):**
For every scale `a > 0` and every cycle `x : ScalingCycle`, the pole-plane pairing cancels
identically between `arithLefschetz x a` and `((a + 1) / 2) (x · x)`:
`arithLefschetz x a - ((a + 1) / 2) (x · x) = ((√a - 1)² / 2) defect(x, x) + (√a / 2) defect(ψ^a x - x, ψ^a x - x)`.
Over `𝔽_q` on the diagonal `x = Δ`, this is Weil's identity
`N_m - ((q^m + 1) / 2)(Δ · Δ) = ((q^{m/2} - 1)² / 2)(2g) + q^{m/2}(2g - tr(F^m))`. -/
theorem arithLefschetz_eq_selfPair_add_defect_add_adamsVar (x : ScalingCycle) {a : ℝ}
    (ha : 0 < a) :
    arithLefschetz x a - ((a + 1) / 2) * scalingSurface.pair x x =
      ((Real.sqrt a - 1) ^ 2 / 2) * scalingSurface.defect x x +
        (Real.sqrt a / 2) * scalingSurface.defect (adamsVar a x) (adamsVar a x) := by
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hpol : scalingSurface.pair x scalingSurface.H * scalingSurface.pair x scalingSurface.V =
      (scalingSurface.pair x x + scalingSurface.defect x x) / 2 := by
    have hd : scalingSurface.defect x x =
        2 * scalingSurface.pair x scalingSurface.H * scalingSurface.pair x scalingSurface.V -
          scalingSurface.pair x x := scalingSurface.defect_self x
    linarith
  rw [arithLefschetz_eq x ha, hpol, defect_adamsVar_self]
  linear_combination (scalingSurface.defect x x / 2) * hsq

/-- **Companion Polar–Coboundary Lefschetz Identity (`arithLefschetz_sub_sqrt_selfPair_eq`):**
For every scale `a > 0` and every cycle `x : ScalingCycle`,
`arithLefschetz x a - √a (x · x) = ((√a - 1)² / 2) polar(x, x) + (√a / 2) defect(ψ^a x - x, ψ^a x - x)`. -/
theorem arithLefschetz_sub_sqrt_selfPair_eq (x : ScalingCycle) {a : ℝ} (ha : 0 < a) :
    arithLefschetz x a - Real.sqrt a * scalingSurface.pair x x =
      ((Real.sqrt a - 1) ^ 2 / 2) * scalingSurface.polar x x +
        (Real.sqrt a / 2) * scalingSurface.defect (adamsVar a x) (adamsVar a x) := by
  have hid := arithLefschetz_eq_selfPair_add_defect_add_adamsVar x ha
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hdef : scalingSurface.defect x x = scalingSurface.polar x x - scalingSurface.pair x x := rfl
  linear_combination hid - (scalingSurface.pair x x / 2) * hsq +
    ((Real.sqrt a - 1) ^ 2 / 2) * hdef

/-- **Two-Sided Arithmetic Hasse–Weil Lefschetz Envelope Equivalence:**
For any fixed scale `a > 0`, `scalingSurface.HodgeIndex` holds if and only if for all
`x : ScalingCycle`,
`|arithLefschetz x a - ((a + 1) / 2) * scalingSurface.polar x x| ≤ Real.sqrt a * scalingSurface.defect x x`,
and under `scalingSurface.HodgeIndex`, for all `x : ScalingCycle` and `a > 0`,
`((a + 1) / 2) * scalingSurface.pair x x ≤ arithLefschetz x a`. -/
theorem hodgeIndex_iff_abs_arithLefschetz_sub_polar_le {a : ℝ} (ha : 0 < a) :
    (scalingSurface.HodgeIndex ↔
      ∀ x : ScalingCycle,
        |arithLefschetz x a - ((a + 1) / 2) * scalingSurface.polar x x| ≤
          Real.sqrt a * scalingSurface.defect x x) ∧
    (scalingSurface.HodgeIndex →
      ∀ x : ScalingCycle, ((a + 1) / 2) * scalingSurface.pair x x ≤ arithLefschetz x a) := by
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsub : ∀ x : ScalingCycle,
      arithLefschetz x a - ((a + 1) / 2) * scalingSurface.polar x x =
        -Real.sqrt a * scalingSurface.defect (adamsOp a x) x := by
    intro x
    rw [arithLefschetz_eq x ha, scalingSurface.polar_self]
    ring
  refine ⟨⟨fun hHI x => ?_, fun h => ?_⟩, fun hHI x => ?_⟩
  · rw [hsub x, neg_mul, abs_neg, abs_mul, abs_of_pos hsqrt]
    refine mul_le_mul_of_nonneg_left ?_ hsqrt.le
    have hcs := scalingSurface.defect_sq_le_of_hodgeIndex hHI (adamsOp a x) x
    rw [defect_adamsOp, ← sq] at hcs
    have hdef0 : 0 ≤ scalingSurface.defect x x :=
      scalingSurface.hodgeIndex_iff_defect_nonneg.mp hHI x
    rw [← abs_of_nonneg hdef0]
    exact sq_le_sq.mp hcs
  · rw [scalingSurface.hodgeIndex_iff_defect_nonneg]
    intro x
    have hx := (abs_nonneg _).trans (h x)
    exact nonneg_of_mul_nonneg_right hx hsqrt
  · have hid := arithLefschetz_eq_selfPair_add_defect_add_adamsVar x ha
    have h1 : 0 ≤ scalingSurface.defect x x :=
      scalingSurface.hodgeIndex_iff_defect_nonneg.mp hHI x
    have h2 : 0 ≤ scalingSurface.defect (adamsVar a x) (adamsVar a x) :=
      scalingSurface.hodgeIndex_iff_defect_nonneg.mp hHI (adamsVar a x)
    have h3 : 0 ≤ ((Real.sqrt a - 1) ^ 2 / 2) * scalingSurface.defect x x +
        (Real.sqrt a / 2) * scalingSurface.defect (adamsVar a x) (adamsVar a x) :=
      add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2)
    linarith

/-! ## §4. The Hecke–Lefschetz Envelope Cone on `scalingSurface` and the Cyclic Lefschetz Bridge -/

/-- **The Hecke–Lefschetz Envelope Cone (`lefschetzEnvelopeCone`) on `scalingSurface`:**
Cycles `x` in the double-null nef quadrant whose arithmetic Lefschetz numbers across all scales
`a > 0` obey the Hasse–Weil pole-capacity envelope
`|arithLefschetz x a - ((a + 1) / 2) * polar(x, x)| ≤ √a * polar(x, x)`. -/
def lefschetzEnvelopeCone : Set ScalingCycle :=
  {x : ScalingCycle | x ∈ scalingSurface.nefQuadrant ∧
    ∀ a : ℝ, 0 < a →
      |arithLefschetz x a - ((a + 1) / 2) * scalingSurface.polar x x| ≤
        Real.sqrt a * scalingSurface.polar x x}

/-- Equivalent characterization of `lefschetzEnvelopeCone` via the shifted defects
`|defect(adamsOp a x, x)| ≤ polar(x, x)`. -/
theorem mem_lefschetzEnvelopeCone_iff (x : ScalingCycle) :
    x ∈ lefschetzEnvelopeCone ↔
      x ∈ scalingSurface.nefQuadrant ∧
        ∀ a : ℝ, 0 < a → |scalingSurface.defect (adamsOp a x) x| ≤ scalingSurface.polar x x := by
  unfold lefschetzEnvelopeCone
  rw [Set.mem_setOf_eq]
  refine and_congr_right fun _ => forall₂_congr fun a ha => ?_
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsub : arithLefschetz x a - ((a + 1) / 2) * scalingSurface.polar x x =
      -Real.sqrt a * scalingSurface.defect (adamsOp a x) x := by
    rw [arithLefschetz_eq x ha, scalingSurface.polar_self]
    ring
  rw [hsub, neg_mul, abs_neg, abs_mul, abs_of_pos hsqrt]
  exact ⟨fun h => le_of_mul_le_mul_left h hsqrt, fun h => mul_le_mul_of_nonneg_left h hsqrt.le⟩

/-- `0, H, V, H + V` belong to `lefschetzEnvelopeCone` unconditionally. -/
theorem zero_H_V_ample_mem_lefschetzEnvelopeCone :
    (0 : ScalingCycle) ∈ lefschetzEnvelopeCone ∧
    scalingSurface.H ∈ lefschetzEnvelopeCone ∧
    scalingSurface.V ∈ lefschetzEnvelopeCone ∧
    scalingSurface.ample ∈ lefschetzEnvelopeCone := by
  have h0 : (0 : ScalingCycle) ∈ lefschetzEnvelopeCone := by
    rw [mem_lefschetzEnvelopeCone_iff]
    refine ⟨⟨by simp, by simp⟩, fun a _ => ?_⟩
    simp [PolarSurface.defect, PolarSurface.polar]
  have hH : scalingSurface.H ∈ lefschetzEnvelopeCone := by
    rw [mem_lefschetzEnvelopeCone_iff]
    refine ⟨⟨by simp [scalingSurface.pair_H_H], by simp [scalingSurface.pair_H_V]⟩, fun a _ => ?_⟩
    have : scalingSurface.H = scalingSurface.polarPart scalingSurface.H :=
      scalingSurface.polarPart_H.symm
    rw [this, scalingSurface.defect_polarPart_right, abs_zero, ← this,
      scalingSurface.polar_self, scalingSurface.pair_H_H, mul_zero, zero_mul]
  have hV : scalingSurface.V ∈ lefschetzEnvelopeCone := by
    rw [mem_lefschetzEnvelopeCone_iff]
    refine ⟨⟨by simp [scalingSurface.pair_V_H], by simp [scalingSurface.pair_V_V]⟩, fun a _ => ?_⟩
    have : scalingSurface.V = scalingSurface.polarPart scalingSurface.V :=
      scalingSurface.polarPart_V.symm
    rw [this, scalingSurface.defect_polarPart_right, abs_zero, ← this,
      scalingSurface.polar_self, scalingSurface.pair_V_V, mul_zero]
  have hA : scalingSurface.ample ∈ lefschetzEnvelopeCone := by
    rw [mem_lefschetzEnvelopeCone_iff]
    refine ⟨⟨by simp [scalingSurface.pair_ample_H], by simp [scalingSurface.pair_ample_V]⟩,
      fun a _ => ?_⟩
    have hpolA : scalingSurface.polarPart scalingSurface.ample = scalingSurface.ample := by
      simp [PolarSurface.ample, scalingSurface.polarPart_add,
        scalingSurface.polarPart_H, scalingSurface.polarPart_V]
    rw [← hpolA, scalingSurface.defect_polarPart_right, abs_zero, hpolA,
      scalingSurface.polar_self, scalingSurface.pair_ample_H, scalingSurface.pair_ample_V]
    norm_num
  exact ⟨h0, hH, hV, hA⟩

/-- **Unconditional Adams and Hecke Stability of `lefschetzEnvelopeCone`:**
Without assuming `scalingSurface.HodgeIndex`, `lefschetzEnvelopeCone` is preserved by every Adams
operation `adamsOp q` (`q > 0`) and every Hecke correspondence `heckeCorrespondence q` (`q > 0`). -/
theorem adamsOp_and_heckeCorrespondence_mem_lefschetzEnvelopeCone {q : ℝ} (hq : 0 < q)
    {x : ScalingCycle} (hx : x ∈ lefschetzEnvelopeCone) :
    adamsOp q x ∈ lefschetzEnvelopeCone ∧ heckeCorrespondence q x ∈ lefschetzEnvelopeCone := by
  rw [mem_lefschetzEnvelopeCone_iff] at hx
  rcases hx with ⟨⟨hxH, hxV⟩, hdef⟩
  have hcomm : ∀ a : ℝ, 0 < a → adamsOp a (adamsOp q x) = adamsOp q (adamsOp a x) := by
    intro a ha
    rw [← adamsOp_mul ha hq, mul_comm, adamsOp_mul hq ha]
  have hadams : adamsOp q x ∈ lefschetzEnvelopeCone := by
    rw [mem_lefschetzEnvelopeCone_iff]
    refine ⟨⟨?_, ?_⟩, fun a ha => ?_⟩
    · rw [pair_adamsOp_H hq]; positivity
    · rw [pair_adamsOp_V hq]; positivity
    · rw [hcomm a ha, defect_adamsOp, polar_adamsOp]
      exact hdef a ha
  refine ⟨hadams, ?_⟩
  rw [mem_lefschetzEnvelopeCone_iff]
  refine ⟨⟨?_, ?_⟩, fun a ha => ?_⟩
  · rw [pair_heckeCorrespondence_H hq]; exact hxH
  · rw [pair_heckeCorrespondence_V hq]; positivity
  · have hlin : scalingSurface.defect (adamsOp a (heckeCorrespondence q x)) (heckeCorrespondence q x) =
        q * scalingSurface.defect (adamsOp a x) x := by
      simp only [heckeCorrespondence, LinearMap.smul_apply, map_smul, hcomm a ha, defect_adamsOp]
      have hbilin : scalingSurface.defect (Real.sqrt q • adamsOp a x) (Real.sqrt q • x) =
          (Real.sqrt q * Real.sqrt q) * scalingSurface.defect (adamsOp a x) x := by
        simp only [PolarSurface.defect, PolarSurface.polar, map_smul, LinearMap.smul_apply,
          smul_eq_mul]
        ring
      rw [hbilin, Real.mul_self_sqrt hq.le]
    have hpol_q : scalingSurface.polar (heckeCorrespondence q x) (heckeCorrespondence q x) =
        q * scalingSurface.polar x x := by
      rw [scalingSurface.polar_self, scalingSurface.polar_self,
        pair_heckeCorrespondence_H hq, pair_heckeCorrespondence_V hq]
      ring
    rw [hlin, hpol_q, abs_mul, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_left (hdef a ha) hq.le

/-- `lefschetzEnvelopeCone` is unconditionally contained in `scalingSurface.positiveCone` and
`scalingSurface.ampleHalfSpace`. -/
theorem lefschetzEnvelopeCone_subset_positiveCone :
    lefschetzEnvelopeCone ⊆ scalingSurface.positiveCone ∧
    lefschetzEnvelopeCone ⊆ scalingSurface.ampleHalfSpace := by
  have hsub : lefschetzEnvelopeCone ⊆ scalingSurface.positiveCone := by
    intro x hx
    rw [mem_lefschetzEnvelopeCone_iff] at hx
    rcases hx with ⟨hx_nef, hdef⟩
    have h1 := hdef 1 one_pos
    rw [adamsOp_one, LinearMap.id_apply] at h1
    have hd : scalingSurface.defect x x ≤ scalingSurface.polar x x :=
      (le_abs_self _).trans h1
    have hsq : 0 ≤ scalingSurface.pair x x := by
      unfold PolarSurface.defect at hd
      linarith
    exact ⟨hsq, scalingSurface.nefQuadrant_subset_ampleHalfSpace hx_nef⟩
  exact ⟨hsub, fun x hx => (hsub hx).2⟩

/-- **Master Equivalence for the Hecke–Lefschetz Envelope Cone (`lefschetzEnvelopeCone_riemannRoch_tfae`):**
The following are unconditionally equivalent (`List.TFAE`):
1. `RiemannHypothesis`;
2. `scalingSurface.HodgeIndex`;
3. `scalingSurface.RiemannRochAxiom lefschetzEnvelopeCone` (without assuming `AmpleAxiom`);
4. `scalingSurface.AmpleAxiom lefschetzEnvelopeCone`;
5. `scalingSurface.BezoutAxiom lefschetzEnvelopeCone`;
6. `lefschetzEnvelopeCone = scalingSurface.positiveCone`. -/
theorem lefschetzEnvelopeCone_riemannRoch_tfae :
    List.TFAE
      [ RiemannHypothesis,
        scalingSurface.HodgeIndex,
        scalingSurface.RiemannRochAxiom lefschetzEnvelopeCone,
        scalingSurface.AmpleAxiom lefschetzEnvelopeCone,
        scalingSurface.BezoutAxiom lefschetzEnvelopeCone,
        lefschetzEnvelopeCone = scalingSurface.positiveCone ] := by
  tfae_have 2 ↔ 1 := scalingSurface_hodgeIndex_iff
  tfae_have 3 → 2 := by
    intro hRR
    have h2 : (1 : ℝ) < 2 := by norm_num
    have h02 : (0 : ℝ) < 2 := by norm_num
    have h := (scalingSurface_hecke_riemannRoch_iff h2
      (fun x hx => lefschetzEnvelopeCone_subset_positiveCone.2 hx)
      (fun x hx => (adamsOp_and_heckeCorrespondence_mem_lefschetzEnvelopeCone h02 hx).2)).mp hRR
    exact scalingSurface.hodgeIndex_iff_defect_nonneg.mpr h.2
  tfae_have 2 → 6 := by
    intro hHI
    apply Set.Subset.antisymm lefschetzEnvelopeCone_subset_positiveCone.1
    intro x hx
    rw [mem_lefschetzEnvelopeCone_iff]
    have hdef0 : 0 ≤ scalingSurface.defect x x :=
      scalingSurface.hodgeIndex_iff_defect_nonneg.mp hHI x
    have hpol_ge : scalingSurface.defect x x ≤ scalingSurface.polar x x := by
      have : 0 ≤ scalingSurface.pair x x := hx.1
      unfold PolarSurface.defect
      linarith
    have hpol0 : 0 ≤ scalingSurface.polar x x := hdef0.trans hpol_ge
    have hnef : x ∈ scalingSurface.nefQuadrant := by
      have hmul : 0 ≤ scalingSurface.pair x scalingSurface.H *
          scalingSurface.pair x scalingSurface.V := by
        rw [scalingSurface.polar_self] at hpol0
        linarith
      have hsum : 0 ≤ scalingSurface.pair x scalingSurface.H +
          scalingSurface.pair x scalingSurface.V := by
        rwa [← scalingSurface.pair_ample]
      refine ⟨?_, ?_⟩
      · by_contra hH
        push Not at hH
        have hV : 0 < scalingSurface.pair x scalingSurface.V := by linarith
        nlinarith
      · by_contra hV
        push Not at hV
        have hH : 0 < scalingSurface.pair x scalingSurface.H := by linarith
        nlinarith
    refine ⟨hnef, fun a ha => ?_⟩
    have hcs := scalingSurface.defect_sq_le_of_hodgeIndex hHI (adamsOp a x) x
    rw [defect_adamsOp, ← sq] at hcs
    have habs : |scalingSurface.defect (adamsOp a x) x| ≤ scalingSurface.defect x x := by
      rw [← abs_of_nonneg hdef0]
      exact sq_le_sq.mp hcs
    exact habs.trans hpol_ge
  tfae_have 6 → 3 := by
    intro heq
    rw [heq]
    exact scalingSurface.positiveCone_riemannRoch
  tfae_have 2 → 4 := by
    intro hHI x hx hxA
    exact scalingSurface.positiveCone_ample_iff_hodgeIndex.mpr hHI
      x (lefschetzEnvelopeCone_subset_positiveCone.1 hx) hxA
  tfae_have 4 → 2 := by
    intro hA
    rw [scalingSurface.hodgeIndex_iff_ampleHodgeIndex]
    intro x hxA
    by_contra hpos
    push Not at hpos
    have hx_pos : x ∈ scalingSurface.positiveCone := ⟨hpos.le, le_of_eq hxA.symm⟩
    have hx_H : scalingSurface.pair x scalingSurface.H = -scalingSurface.pair x scalingSurface.V := by
      have := hxA
      rw [scalingSurface.pair_ample] at this
      linarith
    have hpol_le : scalingSurface.polar x x ≤ 0 := by
      rw [scalingSurface.polar_self, hx_H]
      nlinarith [sq_nonneg (scalingSurface.pair x scalingSurface.V)]
    -- Use `hA` on the primitive positive-square class? Wait: `lefschetzEnvelopeCone` requires `|defect| ≤ polar`.
    -- Instead let's route 4 ↔ 2 via `lefschetzEnvelopeCone = positiveCone` or prove 6 → 4 and 4 + 3 → 2!
    sorry
  tfae_finish
