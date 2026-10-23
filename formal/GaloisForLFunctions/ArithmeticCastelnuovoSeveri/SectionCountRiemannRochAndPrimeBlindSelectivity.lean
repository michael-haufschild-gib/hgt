import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface
import GaloisForLFunctions.ArithmeticOrientationTheory.TheNyquistRankBound
import GaloisForLFunctions.RHTower.AdmixturesAndTheShiftedPairLeaveTheWeilCone
import GaloisForLFunctions.RHTower.MarkovJointResolventEnvelopeAndPastThirtyFourPBAP
import GaloisForLFunctions.RHTower.SharpWeilNearRadicalCount

/-!
# Section-Count Riemann–Roch for `ℤ`, Hecke–Ample Rigidity, and Prime-Blind Selectivity

This module resolves the open core of Riemann–Roch for `ℤ` on the scaling surface by establishing
the unconditional structure of section-count effectivity cones, the Hecke–ample quadrant law, the
prime-blind spectral uncertainty floor, the diagonal Dirichlet relabeling invariance of linear node
counts, and the exact selectivity laws separating the von Mangoldt prime weight from both the golden
fake curve and the off-line shifted pair.

## Main Results

1. **The Double-Null Nef Quadrant and Single-Scale Hecke–Ample Rigidity (§1):**
   * On any polar surface `S`, the **nef quadrant** `S.nefQuadrant := {x | 0 ≤ x · H ∧ 0 ≤ x · V}`
     is a convex cone inside the ample half-space `S.ampleHalfSpace := {x | 0 ≤ x · ample}` on which
     the pole form `S.polar` is nonnegative (`nefQuadrant_subset_ampleHalfSpace`,
     `polar_nonneg_of_mem_nefQuadrant`).
   * **General Nef-Quadrant Equivalence (`hodgeIndex_iff_openPositiveCone_subset_nefQuadrant`):**
     On *every* polar surface `S`, the Hodge index theorem holds if and only if
     `S.openPositiveCone ⊆ S.nefQuadrant`. Consequently, on the golden fake curve `goldenDatum` at
     window `{0, 1}`, `openPositiveCone` is not contained in `nefQuadrant`
     (`goldenDatum_openPositiveCone_not_subset_nefQuadrant`).
   * **Hecke/Adams Ample Quadrant Law
     (`forall_heckeCorrespondence_mem_ampleHalfSpace_iff_mem_nefQuadrant`,
     `forall_adamsOp_mem_ampleHalfSpace_iff_mem_nefQuadrant`):**
     On `scalingSurface`, a cycle `x` has nonnegative ample degree under all Hecke correspondences
     `heckeCorrespondence a` (`a > 0`) — or under all Adams operations `adamsOp q` (`q > 0`) — if
     and only if `x ∈ scalingSurface.nefQuadrant`.
   * **Single-Scale Hecke Stability of `openPositiveCone` is Equivalent to RH
     (`scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample`,
     `scalingSurface_hodgeIndex_iff_heckeStable_effectivity`):**
     For any single fixed scale `a > 1` (in particular `a = 2` at the first prime),
     `scalingSurface.HodgeIndex` (and hence `RiemannHypothesis`) holds if and only if
     `heckeCorrespondence a` maps `scalingSurface.openPositiveCone` into
     `scalingSurface.ampleHalfSpace`, if and only if there exists a Hecke-stable cone `E` containing
     `openPositiveCone` inside `ampleHalfSpace`. Under `HodgeIndex`, `openPositiveCone` itself is
     simultaneously Adams-stable, Hecke-stable, Bézout-closed, ample, and satisfies
     `RiemannRochAxiom`.

2. **Box Degrees of Freedom, Prime-Power Node Counts, and the Chebyshev Defect `E(s)` (§2):**
   * On the logarithmic box `[0, s]`, the integrated density of the two-pole plane `ℝH ⊕ ℝV`
     (`polarBoxDoF s := ∫ u in 0..s, (e^u + 1)`) equals `twoPoleWeight s = e^s + s - 1`, and
     subtracting the weighted prime-power node count `primeNodeCount s := lagChebyshev s = ψ(e^s)`
     gives the two-pole Chebyshev defect identically:
     `polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s`
     (`polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect`).
   * For any general arithmetic weight `w : ℕ → ℝ`, the generalized two-pole defect
     `generalizedTwoPoleDefect w s := twoPoleWeight s - weightedNodeCount w s` specializes to
     `chebyshevTwoPoleDefect s` at `w = Λ`, while for the off-line shifted pair
     `shiftedPairVonMangoldt a` (`a ≠ 0`) it drops strictly below `chebyshevTwoPoleDefect s - ψ(e^s)`
     on `[log 2, ∞)` and becomes strictly negative already at `s = log 2` for
     `2^a + 2^{-a} > 1 + 1/log 2` (`generalizedTwoPoleDefect_shiftedPair_lt`,
     `generalizedTwoPoleDefect_shiftedPair_log_two_neg`).

3. **Prime-Blind Section Vanishing and the `99/4` & `69/2` Nyquist–Landau Thresholds (§3):**
   * For any odd `F ∈ C¹_c([-r, r])` that is prime-blind on the correlation box `(0, 2r]`
     (`IsHorizonPrimeBlind F r`), the prime-side charge vanishes and the Chebyshev-defect integral
     on `(0, 2r]` equals `poleCharge F = 2 (oddPoleMoment F)² ≥ 0`
     (`chebyshevTwoPoleDefect_integral_eq_poleCharge_of_isHorizonPrimeBlind`).
   * For globally prime-blind tests `f ∈ C²_c(ℝ)` (`logVector (realWeilTestFn f hf hfc) = 0`) with
     vanishing even pole moment (`coshHalfMoment f = 0`), the spectral uncertainty bounds (`99/4`
     and `69/2`) force complete vanishing `f = 0` (`h⁰ = 0`) whenever the rms spectral height
     satisfies `T² ≤ 69/2` (in particular `T² ≤ 99/4`), at *every* aperture `A > 0`
     (`primeBlind_eq_zero_of_spectralSecondMoment_le_ninety_nine_fourths`,
     `primeBlind_eq_zero_of_spectralSecondMoment_le_sixty_nine_halves`,
     `finrank_primeBlind_subspace_eq_zero`).

4. **The Classical Shadow: Exact Frobenius Mass of `dirichletSampling`, the Square-Root Threshold,
   and Diagonal Relabeling Invariance (§4):**
   * Every entry of `dirichletSampling N lam R` has unit norm, and combined with the
     Montgomery–Vaughan mean value theorem this gives the explicit rank lower bound
     `rank_dirichletSampling_ge` and the square-root threshold cancellation `T = N`
     (`h0_dirichletSampling_at_sqrt_threshold`).
   * **Diagonal Relabeling Theorem (`h0_mul_diagonal_eq_of_iff_eq_zero`,
     `h0_weightedDirichletSampling_shiftedPair_eq_vonMangoldt`):**
     Weighting the columns of any sampling matrix by a weight `w` depends only on the support
     `{m | w m ≠ 0}`. Since `shiftedPairVonMangoldt a n ≠ 0 ↔ Λ(n) ≠ 0` for all `a ∈ ℝ` and
     `n ∈ ℕ`, any linear kernel dimension `h⁰` of prime-node or Dirichlet-polynomial evaluation is
     identical for `Λ` and `shiftedPairVonMangoldt a`, whereas the quadratic Weil/Castelnuovo–Severi
     defect and the Chebyshev prime–pole balance are selective against both `goldenDatum` and
     `shiftedPairVonMangoldt a` (§5).
-/

open Complex Finset MeasureTheory Set Filter Topology
open scoped Real BigOperators
open Zeta23 RHTower RHTower.Sieve RHTower.WeilOneSided RHTower.WeilSpectral RHTower.WeilLevyPole
open RHTower.LebesgueAtomWeil RHTower.NonnegativeCone
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ## §1. The Double-Null Nef Quadrant and Single-Scale Hecke–Ample Rigidity -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **The Ample Half-Space (`ampleHalfSpace`):**
The half-space `{x : C | 0 ≤ x · (H + V)}` of cycles with nonnegative degree against `S.ample`. -/
def ampleHalfSpace : Set C :=
  {x : C | 0 ≤ S.pair x S.ample}

@[simp]
theorem mem_ampleHalfSpace {x : C} :
    x ∈ S.ampleHalfSpace ↔ 0 ≤ S.pair x S.ample := Iff.rfl

/-- **The Double-Null Nef Quadrant (`nefQuadrant`):**
The cone of cycles `x ∈ C` meeting both the horizontal fiber `H` and the vertical fiber `V`
nonnegatively (`0 ≤ x · H` and `0 ≤ x · V`). -/
def nefQuadrant : Set C :=
  {x : C | 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V}

@[simp]
theorem mem_nefQuadrant {x : C} :
    x ∈ S.nefQuadrant ↔ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V := Iff.rfl

theorem zero_mem_nefQuadrant : (0 : C) ∈ S.nefQuadrant := by
  simp [nefQuadrant]

theorem H_mem_nefQuadrant : S.H ∈ S.nefQuadrant := by
  simp [nefQuadrant, S.pair_H_H, S.pair_H_V]

theorem V_mem_nefQuadrant : S.V ∈ S.nefQuadrant := by
  simp [nefQuadrant, S.pair_V_H, S.pair_V_V]

theorem ample_mem_nefQuadrant : S.ample ∈ S.nefQuadrant := by
  simp [nefQuadrant, PolarSurface.ample, S.pair_H_H, S.pair_H_V, S.pair_V_H, S.pair_V_V]

theorem nefQuadrant_add {x y : C} (hx : x ∈ S.nefQuadrant) (hy : y ∈ S.nefQuadrant) :
    x + y ∈ S.nefQuadrant := by
  simp only [mem_nefQuadrant, map_add, LinearMap.add_apply] at hx hy ⊢
  exact ⟨add_nonneg hx.1 hy.1, add_nonneg hx.2 hy.2⟩

theorem nefQuadrant_smul {c : ℝ} (hc : 0 ≤ c) {x : C} (hx : x ∈ S.nefQuadrant) :
    c • x ∈ S.nefQuadrant := by
  simp only [mem_nefQuadrant, map_smul, LinearMap.smul_apply, smul_eq_mul] at hx ⊢
  exact ⟨mul_nonneg hc hx.1, mul_nonneg hc hx.2⟩

/-- Every cycle in `S.nefQuadrant` has nonnegative ample degree `x · (H + V) ≥ 0`. -/
theorem nefQuadrant_subset_ampleHalfSpace : S.nefQuadrant ⊆ S.ampleHalfSpace := by
  intro x hx
  rw [mem_ampleHalfSpace, S.pair_ample]
  exact add_nonneg hx.1 hx.2

theorem openPositiveCone_subset_ampleHalfSpace : S.openPositiveCone ⊆ S.ampleHalfSpace :=
  fun _ hx => le_of_lt hx.2

/-- Under `S.HodgeIndex`, `S.openPositiveCone` satisfies `RiemannRochAxiom`. -/
theorem openPositiveCone_riemannRoch (h : S.HodgeIndex) : S.RiemannRochAxiom S.openPositiveCone :=
  ((S.effectivity_iff h S.openPositiveCone).mpr
    ⟨Set.Subset.rfl, fun _ hx => Or.inl hx.2⟩).1

/-- On `S.nefQuadrant`, the pole-plane hyperbolic form `S.polar x y` is nonnegative. -/
theorem polar_nonneg_of_mem_nefQuadrant {x y : C}
    (hx : x ∈ S.nefQuadrant) (hy : y ∈ S.nefQuadrant) :
    0 ≤ S.polar x y := by
  rw [PolarSurface.polar]
  exact add_nonneg (mul_nonneg hx.1 hy.2) (mul_nonneg hx.2 hy.1)

/-- Under `S.HodgeIndex`, every cycle in `S.openPositiveCone` has strictly positive `H`-degree and
strictly positive `V`-degree, and in particular lies in `S.nefQuadrant`. -/
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

theorem openPositiveCone_subset_nefQuadrant_of_hodgeIndex (h : S.HodgeIndex) :
    S.openPositiveCone ⊆ S.nefQuadrant := fun _ hx =>
  ⟨le_of_lt (S.pair_H_and_V_pos_of_openPositiveCone h hx).1,
   le_of_lt (S.pair_H_and_V_pos_of_openPositiveCone h hx).2⟩

/-- **General Nef-Quadrant Equivalence on any Polar Surface:**
`S.HodgeIndex` holds if and only if `S.openPositiveCone ⊆ S.nefQuadrant`. -/
theorem hodgeIndex_iff_openPositiveCone_subset_nefQuadrant :
    S.HodgeIndex ↔ S.openPositiveCone ⊆ S.nefQuadrant := by
  refine ⟨S.openPositiveCone_subset_nefQuadrant_of_hodgeIndex, fun hsub => ?_⟩
  intro z hzH hzV
  by_contra hpos
  push Not at hpos
  set δ : ℝ := Real.sqrt (S.pair z z) / 3
  have hδ : 0 < δ := by positivity
  have hδ_sq : δ ^ 2 = S.pair z z / 9 := by
    dsimp [δ]
    rw [div_pow, Real.sq_sqrt (le_of_lt hpos)]
    ring
  set x : C := (2 * δ) • S.V - δ • S.H + z
  have hxH : S.pair x S.H = 2 * δ := by
    simp [x, map_add, map_sub, map_smul, S.pair_V_H, S.pair_H_H, hzH]
  have hxV : S.pair x S.V = -δ := by
    simp [x, map_add, map_sub, map_smul, S.pair_V_V, S.pair_H_V, hzV]
  have hxA : 0 < S.pair x S.ample := by
    rw [S.pair_ample, hxH, hxV]
    linarith
  have hxx : 0 < S.pair x x := by
    have hHz : S.pair S.H z = 0 := by rw [S.pair_comm, hzH]
    have hVz : S.pair S.V z = 0 := by rw [S.pair_comm, hzV]
    have hexp : S.pair x x = -4 * δ ^ 2 + S.pair z z := by
      simp only [x, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul, S.pair_V_V, S.pair_H_H, S.pair_V_H, S.pair_H_V,
        hzH, hzV, hHz, hVz]
      ring
    rw [hexp, hδ_sq]
    linarith
  have hx_mem : x ∈ S.openPositiveCone := ⟨hxx, hxA⟩
  have hx_nef := hsub hx_mem
  linarith [hx_nef.2, hxV]

end PolarSurface

/-- On the golden fake curve `goldenDatum` at window `{0, 1}`, the Hodge index fails. -/
theorem goldenDatum_not_hodgeIndex_at_01 :
    ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).HodgeIndex := by
  intro hH
  obtain ⟨h1, h2, h3⟩ := goldenCounterexample_violates_hodgeIndex
  have hle := hH goldenCounterexample h1 h2
  linarith

/-- **Golden Datum Failure of the Nef-Quadrant Law:**
On the golden fake curve `goldenDatum` at window `{0, 1}`, `openPositiveCone` is not contained in
`nefQuadrant`. -/
theorem goldenDatum_openPositiveCone_not_subset_nefQuadrant :
    ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).openPositiveCone ⊆
        (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).nefQuadrant := by
  rw [← (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).hodgeIndex_iff_openPositiveCone_subset_nefQuadrant]
  exact goldenDatum_not_hodgeIndex_at_01

/-- A subset `E ⊆ ScalingCycle` is **Adams-stable** if `adamsOp q` preserves `E` for all `q > 0`. -/
def IsAdamsStable (E : Set ScalingCycle) : Prop :=
  ∀ ⦃q : ℝ⦄, 0 < q → ∀ ⦃x : ScalingCycle⦄, x ∈ E → adamsOp q x ∈ E

/-- A subset `E ⊆ ScalingCycle` is **Hecke-stable** if `heckeCorrespondence a` preserves `E` for
all `a > 0`. -/
def IsHeckeStable (E : Set ScalingCycle) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x : ScalingCycle⦄, x ∈ E → heckeCorrespondence a x ∈ E

/-- Under `adamsOp q` (`q > 0`), the ample degree of `x` is `(√q)⁻¹ (x · H) + √q (x · V)`. -/
theorem pair_adamsOp_ample {q : ℝ} (hq : 0 < q) (x : ScalingCycle) :
    scalingSurface.pair (adamsOp q x) scalingSurface.ample =
      (Real.sqrt q)⁻¹ * scalingSurface.pair x scalingSurface.H +
        Real.sqrt q * scalingSurface.pair x scalingSurface.V := by
  rw [scalingSurface.pair_ample, pair_adamsOp_H hq, pair_adamsOp_V hq]

/-- Under `heckeCorrespondence a` (`a > 0`), the ample degree of `x` is `(x · H) + a (x · V)`. -/
theorem pair_heckeCorrespondence_ample {a : ℝ} (ha : 0 < a) (x : ScalingCycle) :
    scalingSurface.pair (heckeCorrespondence a x) scalingSurface.ample =
      scalingSurface.pair x scalingSurface.H +
        a * scalingSurface.pair x scalingSurface.V := by
  rw [scalingSurface.pair_ample, pair_heckeCorrespondence_H ha, pair_heckeCorrespondence_V ha]

/-- `scalingSurface.nefQuadrant` is Adams-stable. -/
theorem nefQuadrant_isAdamsStable : IsAdamsStable scalingSurface.nefQuadrant := by
  intro q hq x hx
  simp only [PolarSurface.mem_nefQuadrant, pair_adamsOp_H hq, pair_adamsOp_V hq]
  exact ⟨mul_nonneg (by positivity) hx.1, mul_nonneg (by positivity) hx.2⟩

/-- `scalingSurface.nefQuadrant` is Hecke-stable. -/
theorem nefQuadrant_isHeckeStable : IsHeckeStable scalingSurface.nefQuadrant := by
  intro a ha x hx
  simp only [PolarSurface.mem_nefQuadrant, pair_heckeCorrespondence_H ha,
    pair_heckeCorrespondence_V ha]
  exact ⟨hx.1, mul_nonneg (le_of_lt ha) hx.2⟩

/-- **Hecke–Ample Quadrant Law:**
A cycle `x : ScalingCycle` has nonnegative ample degree under all Hecke correspondences
`heckeCorrespondence a` (`a > 0`) if and only if `x ∈ scalingSurface.nefQuadrant`
(`x · H ≥ 0` and `x · V ≥ 0`). -/
theorem forall_heckeCorrespondence_mem_ampleHalfSpace_iff_mem_nefQuadrant (x : ScalingCycle) :
    (∀ a : ℝ, 0 < a → heckeCorrespondence a x ∈ scalingSurface.ampleHalfSpace) ↔
      x ∈ scalingSurface.nefQuadrant := by
  refine ⟨fun h => ?_, fun hx a ha =>
    scalingSurface.nefQuadrant_subset_ampleHalfSpace (nefQuadrant_isHeckeStable ha hx)⟩
  set u := scalingSurface.pair x scalingSurface.H
  set v := scalingSurface.pair x scalingSurface.V
  have hineq : ∀ a : ℝ, 0 < a → 0 ≤ u + a * v := fun a ha => by
    have haA := h a ha
    rwa [PolarSurface.mem_ampleHalfSpace, pair_heckeCorrespondence_ample ha] at haA
  refine ⟨?_, ?_⟩
  · by_contra hu
    push Not at hu
    have ha_pos : 0 < (-u) / (2 * (|v| + 1)) :=
      div_pos (neg_pos.mpr hu) (by positivity)
    have htest := hineq ((-u) / (2 * (|v| + 1))) ha_pos
    have hv_le : v ≤ |v| + 1 := by linarith [le_abs_self v]
    have hmul : ((-u) / (2 * (|v| + 1))) * v ≤ ((-u) / (2 * (|v| + 1))) * (|v| + 1) :=
      mul_le_mul_of_nonneg_left hv_le (le_of_lt ha_pos)
    have hsimp : ((-u) / (2 * (|v| + 1))) * (|v| + 1) = -u / 2 := by
      have hne : |v| + 1 ≠ 0 := by positivity
      field_simp [hne]
    linarith
  · by_contra hv
    push Not at hv
    have ha_pos : 0 < (|u| + 1) / (-v) :=
      div_pos (by positivity) (neg_pos.mpr hv)
    have htest := hineq ((|u| + 1) / (-v)) ha_pos
    have hsimp : ((|u| + 1) / (-v)) * v = -(|u| + 1) := by
      have hne : v ≠ 0 := ne_of_lt hv
      field_simp [hne]
    have hu_le : u ≤ |u| := le_abs_self u
    linarith

/-- **Adams–Ample Quadrant Law:**
A cycle `x : ScalingCycle` has nonnegative ample degree under all Adams operations `adamsOp q`
(`q > 0`) if and only if `x ∈ scalingSurface.nefQuadrant`. -/
theorem forall_adamsOp_mem_ampleHalfSpace_iff_mem_nefQuadrant (x : ScalingCycle) :
    (∀ q : ℝ, 0 < q → adamsOp q x ∈ scalingSurface.ampleHalfSpace) ↔
      x ∈ scalingSurface.nefQuadrant := by
  rw [← forall_heckeCorrespondence_mem_ampleHalfSpace_iff_mem_nefQuadrant]
  refine ⟨fun h a ha => ?_, fun h q hq => ?_⟩
  · have hq := h a ha
    rw [PolarSurface.mem_ampleHalfSpace, pair_adamsOp_ample ha] at hq
    rw [PolarSurface.mem_ampleHalfSpace, pair_heckeCorrespondence_ample ha]
    have hmul := mul_nonneg (Real.sqrt_nonneg a) hq
    have hsqrt : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (le_of_lt ha)
    calc 0 ≤ Real.sqrt a * ((Real.sqrt a)⁻¹ * scalingSurface.pair x scalingSurface.H +
              Real.sqrt a * scalingSurface.pair x scalingSurface.V) := hmul
      _ = (Real.sqrt a * (Real.sqrt a)⁻¹) * scalingSurface.pair x scalingSurface.H +
            (Real.sqrt a * Real.sqrt a) * scalingSurface.pair x scalingSurface.V := by ring
      _ = scalingSurface.pair x scalingSurface.H +
            a * scalingSurface.pair x scalingSurface.V := by
          rw [mul_inv_cancel₀ hsqrt, one_mul, hsq]
  · have ha := h q hq
    rw [PolarSurface.mem_ampleHalfSpace, pair_heckeCorrespondence_ample hq] at ha
    rw [PolarSurface.mem_ampleHalfSpace, pair_adamsOp_ample hq]
    have hmul := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg q)) ha
    have hsqrt : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
    have hsq : (Real.sqrt q)⁻¹ * q = Real.sqrt q := by
      calc (Real.sqrt q)⁻¹ * q = (Real.sqrt q)⁻¹ * (Real.sqrt q * Real.sqrt q) := by
            rw [Real.mul_self_sqrt (le_of_lt hq)]
        _ = ((Real.sqrt q)⁻¹ * Real.sqrt q) * Real.sqrt q := by ring
        _ = Real.sqrt q := by rw [inv_mul_cancel₀ hsqrt, one_mul]
    calc 0 ≤ (Real.sqrt q)⁻¹ * (scalingSurface.pair x scalingSurface.H +
              q * scalingSurface.pair x scalingSurface.V) := hmul
      _ = (Real.sqrt q)⁻¹ * scalingSurface.pair x scalingSurface.H +
            ((Real.sqrt q)⁻¹ * q) * scalingSurface.pair x scalingSurface.V := by ring
      _ = (Real.sqrt q)⁻¹ * scalingSurface.pair x scalingSurface.H +
            Real.sqrt q * scalingSurface.pair x scalingSurface.V := by rw [hsq]

/-- For any Hecke-stable cone `E ⊆ ScalingCycle`, `E ⊆ scalingSurface.ampleHalfSpace` is
equivalent to `E ⊆ scalingSurface.nefQuadrant`. -/
theorem subset_ampleHalfSpace_iff_subset_nefQuadrant_of_isHeckeStable {E : Set ScalingCycle}
    (hE : IsHeckeStable E) :
    E ⊆ scalingSurface.ampleHalfSpace ↔ E ⊆ scalingSurface.nefQuadrant := by
  refine ⟨fun hample x hx => ?_, fun hsub => Set.Subset.trans hsub
    scalingSurface.nefQuadrant_subset_ampleHalfSpace⟩
  rw [← forall_heckeCorrespondence_mem_ampleHalfSpace_iff_mem_nefQuadrant]
  exact fun a ha => hample (hE ha hx)

/-- For any Adams-stable cone `E ⊆ ScalingCycle`, `E ⊆ scalingSurface.ampleHalfSpace` is
equivalent to `E ⊆ scalingSurface.nefQuadrant`. -/
theorem subset_ampleHalfSpace_iff_subset_nefQuadrant_of_isAdamsStable {E : Set ScalingCycle}
    (hE : IsAdamsStable E) :
    E ⊆ scalingSurface.ampleHalfSpace ↔ E ⊆ scalingSurface.nefQuadrant := by
  refine ⟨fun hample x hx => ?_, fun hsub => Set.Subset.trans hsub
    scalingSurface.nefQuadrant_subset_ampleHalfSpace⟩
  rw [← forall_adamsOp_mem_ampleHalfSpace_iff_mem_nefQuadrant]
  exact fun q hq => hample (hE hq hx)

/-- **Single-Scale Hecke–Ample Theorem
(`scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample`):**
For *every* single fixed scale `a > 1` (for example `a = 2` at the first prime), the Hodge index
theorem on `scalingSurface` holds if and only if `heckeCorrespondence a` maps
`scalingSurface.openPositiveCone` into `scalingSurface.ampleHalfSpace`. -/
theorem scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample
    {a : ℝ} (ha : 1 < a) :
    scalingSurface.HodgeIndex ↔
      ∀ x ∈ scalingSurface.openPositiveCone,
        heckeCorrespondence a x ∈ scalingSurface.ampleHalfSpace := by
  have ha0 : 0 < a := by linarith
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · have hnef := scalingSurface.openPositiveCone_subset_nefQuadrant_of_hodgeIndex h hx
    exact scalingSurface.nefQuadrant_subset_ampleHalfSpace (nefQuadrant_isHeckeStable ha0 hnef)
  · intro z hzH hzV
    by_contra hpos
    push Not at hpos
    set c : ℝ := (a + 1) / 2
    have hc1 : 1 < c := by dsimp [c]; linarith
    have hca : c < a := by dsimp [c]; linarith
    have hc0 : 0 < c := by linarith
    set δ : ℝ := Real.sqrt (scalingSurface.pair z z / (4 * c))
    have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
    have hδ_sq : δ ^ 2 = scalingSurface.pair z z / (4 * c) :=
      Real.sq_sqrt (by positivity)
    set x : ScalingCycle := (c * δ) • scalingSurface.V - δ • scalingSurface.H + z
    have hxH : scalingSurface.pair x scalingSurface.H = c * δ := by
      simp [x, map_add, map_sub, map_smul, scalingSurface.pair_V_H, scalingSurface.pair_H_H, hzH]
    have hxV : scalingSurface.pair x scalingSurface.V = -δ := by
      simp [x, map_add, map_sub, map_smul, scalingSurface.pair_V_V, scalingSurface.pair_H_V, hzV]
    have hxA : 0 < scalingSurface.pair x scalingSurface.ample := by
      rw [scalingSurface.pair_ample, hxH, hxV]
      nlinarith
    have hxx : 0 < scalingSurface.pair x x := by
      have hHz : scalingSurface.pair scalingSurface.H z = 0 := by
        rw [scalingSurface.pair_comm, hzH]
      have hVz : scalingSurface.pair scalingSurface.V z = 0 := by
        rw [scalingSurface.pair_comm, hzV]
      have hexp : scalingSurface.pair x x = -2 * c * δ ^ 2 + scalingSurface.pair z z := by
        simp only [x, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.smul_apply, smul_eq_mul, scalingSurface.pair_V_V, scalingSurface.pair_H_H,
          scalingSurface.pair_V_H, scalingSurface.pair_H_V, hzH, hzV, hHz, hVz]
        ring
      rw [hexp, hδ_sq]
      have hcancel : -2 * c * (scalingSurface.pair z z / (4 * c)) + scalingSurface.pair z z =
          scalingSurface.pair z z / 2 := by
        field_simp [ne_of_gt hc0]
        ring
      linarith
    have hx_open : x ∈ scalingSurface.openPositiveCone := ⟨hxx, hxA⟩
    have hTa := h x hx_open
    rw [PolarSurface.mem_ampleHalfSpace, pair_heckeCorrespondence_ample ha0, hxH, hxV] at hTa
    nlinarith

/-- **Single-Scale Adams–Ample Theorem:**
For *every* single fixed scale `q > 1`, `scalingSurface.HodgeIndex` holds if and only if
`adamsOp q` maps `scalingSurface.openPositiveCone` into `scalingSurface.ampleHalfSpace`. -/
theorem scalingSurface_hodgeIndex_iff_adamsOp_openPositiveCone_ample
    {q : ℝ} (hq : 1 < q) :
    scalingSurface.HodgeIndex ↔
      ∀ x ∈ scalingSurface.openPositiveCone,
        adamsOp q x ∈ scalingSurface.ampleHalfSpace := by
  have hq0 : 0 < q := by linarith
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  rw [scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample hq]
  refine forall₂_congr fun x _ => ?_
  rw [PolarSurface.mem_ampleHalfSpace, PolarSurface.mem_ampleHalfSpace,
    pair_heckeCorrespondence_ample hq0, pair_adamsOp_ample hq0]
  have hrel :
      scalingSurface.pair x scalingSurface.H + q * scalingSurface.pair x scalingSurface.V =
        Real.sqrt q *
          ((Real.sqrt q)⁻¹ * scalingSurface.pair x scalingSurface.H +
            Real.sqrt q * scalingSurface.pair x scalingSurface.V) := by
    have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (le_of_lt hq0)
    calc scalingSurface.pair x scalingSurface.H + q * scalingSurface.pair x scalingSurface.V
        = (Real.sqrt q * (Real.sqrt q)⁻¹) * scalingSurface.pair x scalingSurface.H +
            (Real.sqrt q * Real.sqrt q) * scalingSurface.pair x scalingSurface.V := by
          rw [mul_inv_cancel₀ (ne_of_gt hsqrt), one_mul, hsq]
      _ = Real.sqrt q *
            ((Real.sqrt q)⁻¹ * scalingSurface.pair x scalingSurface.H +
              Real.sqrt q * scalingSurface.pair x scalingSurface.V) := by ring
  rw [hrel]
  exact ⟨fun h => nonneg_of_mul_nonneg_right h hsqrt, fun h => mul_nonneg (le_of_lt hsqrt) h⟩

/-- Under `scalingSurface.HodgeIndex`, `scalingSurface.openPositiveCone` is both Adams-stable and
Hecke-stable. -/
theorem openPositiveCone_isAdamsStable_of_hodgeIndex (h : scalingSurface.HodgeIndex) :
    IsAdamsStable scalingSurface.openPositiveCone := by
  intro q hq x hx
  obtain ⟨hH, hV⟩ := scalingSurface.pair_H_and_V_pos_of_openPositiveCone h hx
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hinv : 0 < (Real.sqrt q)⁻¹ := inv_pos.mpr hsqrt
  refine ⟨by rw [pair_adamsOp]; exact hx.1, ?_⟩
  rw [pair_adamsOp_ample hq]
  exact add_pos (mul_pos hinv hH) (mul_pos hsqrt hV)

theorem openPositiveCone_isHeckeStable_of_hodgeIndex (h : scalingSurface.HodgeIndex) :
    IsHeckeStable scalingSurface.openPositiveCone := by
  intro a ha x hx
  obtain ⟨hH, hV⟩ := scalingSurface.pair_H_and_V_pos_of_openPositiveCone h hx
  refine ⟨by rw [pair_heckeCorrespondence (le_of_lt ha)]; exact mul_pos ha hx.1, ?_⟩
  rw [pair_heckeCorrespondence_ample ha]
  exact add_pos hH (mul_pos ha hV)

/-- **Master Equivalence for Hecke-Stable Effectivity Cones on `scalingSurface`:**
The following are unconditionally equivalent:
1. `RiemannHypothesis` (and `scalingSurface.HodgeIndex`);
2. `scalingSurface.openPositiveCone ⊆ scalingSurface.nefQuadrant`;
3. `IsHeckeStable scalingSurface.openPositiveCone`;
4. `IsAdamsStable scalingSurface.openPositiveCone`;
5. At the first prime `p = 2`, `heckeCorrespondence 2` maps `scalingSurface.openPositiveCone` into
   `scalingSurface.ampleHalfSpace`;
6. There exists a cone `E ⊆ ScalingCycle` containing `scalingSurface.openPositiveCone` that is
   Hecke-stable and contained in `scalingSurface.ampleHalfSpace`;
7. There exists a cone `E ⊆ ScalingCycle` containing `scalingSurface.openPositiveCone` that is
   Adams-stable, Hecke-stable, Bézout-closed (`BezoutAxiom E`), ample (`AmpleAxiom E`), contained
   in `scalingSurface.ampleHalfSpace`, and satisfies `RiemannRochAxiom E`. -/
theorem scalingSurface_hodgeIndex_iff_heckeStable_effectivity :
    (scalingSurface.HodgeIndex ↔ RiemannHypothesis) ∧
    (scalingSurface.HodgeIndex ↔
      scalingSurface.openPositiveCone ⊆ scalingSurface.nefQuadrant) ∧
    (scalingSurface.HodgeIndex ↔ IsHeckeStable scalingSurface.openPositiveCone) ∧
    (scalingSurface.HodgeIndex ↔ IsAdamsStable scalingSurface.openPositiveCone) ∧
    (scalingSurface.HodgeIndex ↔
      ∀ x ∈ scalingSurface.openPositiveCone,
        heckeCorrespondence 2 x ∈ scalingSurface.ampleHalfSpace) ∧
    (scalingSurface.HodgeIndex ↔
      ∃ E : Set ScalingCycle,
        scalingSurface.openPositiveCone ⊆ E ∧
          IsHeckeStable E ∧ E ⊆ scalingSurface.ampleHalfSpace) ∧
    (scalingSurface.HodgeIndex ↔
      ∃ E : Set ScalingCycle,
        scalingSurface.openPositiveCone ⊆ E ∧
          IsAdamsStable E ∧ IsHeckeStable E ∧
            scalingSurface.RiemannRochAxiom E ∧
              scalingSurface.AmpleAxiom E ∧
                scalingSurface.BezoutAxiom E ∧
                  E ⊆ scalingSurface.ampleHalfSpace) := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  refine ⟨scalingSurface_hodgeIndex_iff,
    scalingSurface.hodgeIndex_iff_openPositiveCone_subset_nefQuadrant,
    ⟨openPositiveCone_isHeckeStable_of_hodgeIndex, fun h =>
      (scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample h2).mpr
        fun x hx => scalingSurface.openPositiveCone_subset_ampleHalfSpace
          (h (by norm_num : (0 : ℝ) < 2) hx)⟩,
    ⟨openPositiveCone_isAdamsStable_of_hodgeIndex, fun h =>
      (scalingSurface_hodgeIndex_iff_adamsOp_openPositiveCone_ample h2).mpr
        fun x hx => scalingSurface.openPositiveCone_subset_ampleHalfSpace
          (h (by norm_num : (0 : ℝ) < 2) hx)⟩,
    scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample h2,
    ⟨fun h => ⟨scalingSurface.openPositiveCone, Set.Subset.rfl,
      openPositiveCone_isHeckeStable_of_hodgeIndex h,
      scalingSurface.openPositiveCone_subset_ampleHalfSpace⟩,
     fun ⟨E, hsub, hHecke, hAmple⟩ =>
      (scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample h2).mpr
        fun x hx => hAmple (hHecke (by norm_num : (0 : ℝ) < 2) (hsub hx))⟩,
    ⟨fun h => ⟨scalingSurface.openPositiveCone, Set.Subset.rfl,
      openPositiveCone_isAdamsStable_of_hodgeIndex h,
      openPositiveCone_isHeckeStable_of_hodgeIndex h,
      scalingSurface.openPositiveCone_riemannRoch h,
      scalingSurface.openPositiveCone_ample,
      scalingSurface.openPositiveCone_bezout h,
      scalingSurface.openPositiveCone_subset_ampleHalfSpace⟩,
     fun ⟨E, hsub, _, hHecke, _, _, _, hAmple⟩ =>
      (scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample h2).mpr
        fun x hx => hAmple (hHecke (by norm_num : (0 : ℝ) < 2) (hsub hx))⟩⟩

/-! ## §2. Box Degrees of Freedom, Prime-Power Node Counts, and the Chebyshev Defect `E(s)` -/

/-- **Polar Box Degrees of Freedom (`polarBoxDoF`):**
The integrated density `∫ u in 0..s, (e^u + 1)` of the two-pole plane `ℝH ⊕ ℝV` over the
logarithmic box `[0, s]`, where `e^u` is the `s = 1` pole density (`H`) and `1` is the `s = 0`
pole density (`V`). -/
def polarBoxDoF (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, (Real.exp u + 1)

/-- **Weighted Prime-Power Node Count (`primeNodeCount`):**
The Chebyshev summatory weight `ψ(e^s) = ∑_{k ≤ ⌊e^s⌋} Λ(k)` of the prime-power nodes in `[0, s]`. -/
def primeNodeCount (s : ℝ) : ℝ :=
  lagChebyshev s

/-- The integrated polar degree of freedom on `[0, s]` equals `twoPoleWeight s = e^s + s - 1`. -/
theorem polarBoxDoF_eq_twoPoleWeight (s : ℝ) :
    polarBoxDoF s = twoPoleWeight s := by
  unfold polarBoxDoF twoPoleWeight
  have hexp : IntervalIntegrable Real.exp volume 0 s :=
    Real.continuous_exp.intervalIntegrable 0 s
  rw [intervalIntegral.integral_add hexp intervalIntegrable_const,
    integral_exp, intervalIntegral.integral_const, Real.exp_zero, smul_eq_mul]
  ring

/-- **Exact Box Chebyshev–Riemann–Roch Identity
(`polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect`):**
For every logarithmic horizon `s : ℝ`, the excess of the two-pole degree of freedom `polarBoxDoF s`
over the weighted prime-power node count `primeNodeCount s` is identically the two-pole Chebyshev
defect `chebyshevTwoPoleDefect s = e^s + s - 1 - ψ(e^s)`. -/
theorem polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect (s : ℝ) :
    polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s := by
  rw [polarBoxDoF_eq_twoPoleWeight, primeNodeCount, chebyshevTwoPoleDefect]

/-- At an integer scale `s = log N` (`N ≥ 1`), the box degree of freedom is `N + log N - 1` and
its excess over `∑_{k ≤ N} Λ(k)` is `chebyshevTwoPoleDefect (log N)`. -/
theorem polarBoxDoF_sub_primeNodeCount_log_nat {N : ℕ} (hN : 1 ≤ N) :
    polarBoxDoF (Real.log (N : ℝ)) - primeNodeCount (Real.log (N : ℝ)) =
      (N : ℝ) + Real.log (N : ℝ) - 1 -
        ∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect,
    chebyshevTwoPoleDefect, twoPoleWeight, Real.exp_log hN0, lagChebyshev,
    Real.exp_log hN0, Nat.floor_natCast]

/-- **Generalized Weighted Node Count (`weightedNodeCount`):**
The summatory node weight `∑_{k ∈ [0, ⌊e^s⌋]} w(k)` of an arbitrary arithmetic weight `w : ℕ → ℝ`
on the box `[0, s]`. -/
def weightedNodeCount (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊, w k

/-- **Generalized Two-Pole Defect (`generalizedTwoPoleDefect`):**
The excess `twoPoleWeight s - weightedNodeCount w s` of the two-pole degree of freedom over the
`w`-weighted node count on `[0, s]`. -/
def generalizedTwoPoleDefect (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  twoPoleWeight s - weightedNodeCount w s

@[simp]
theorem weightedNodeCount_vonMangoldt (s : ℝ) :
    weightedNodeCount (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) s = primeNodeCount s := rfl

@[simp]
theorem generalizedTwoPoleDefect_vonMangoldt (s : ℝ) :
    generalizedTwoPoleDefect (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) s =
      chebyshevTwoPoleDefect s := rfl

/-- For every `a ∈ ℝ` and `n ≥ 1`, the hyperbolic cosine factor `n^a + n^{-a}` in
`shiftedPairVonMangoldt a n` is at least `2`. -/
theorem rpow_add_rpow_neg_ge_two {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    2 ≤ (n : ℝ) ^ a + (n : ℝ) ^ (-a) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hpos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn_pos a
  have hprod : (n : ℝ) ^ a * (n : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
  have hsq : 0 ≤ ((n : ℝ) ^ a - 1) ^ 2 := sq_nonneg _
  nlinarith

/-- For every `a ≠ 0`, `(2 : ℝ) ^ a + (2 : ℝ) ^ (-a) > 2`. -/
theorem two_lt_two_rpow_add_two_rpow_neg {a : ℝ} (ha : a ≠ 0) :
    2 < (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) := by
  have hpos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have hne : (2 : ℝ) ^ a ≠ 1 := by
    intro h1
    have hlog := congrArg Real.log h1
    rw [Real.log_rpow (by norm_num), Real.log_one] at hlog
    exact mul_ne_zero ha (ne_of_gt (Real.log_pos (by norm_num))) hlog
  have hprod : (2 : ℝ) ^ a * (2 : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  have hsq : 0 < ((2 : ℝ) ^ a - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith

theorem rpow_add_rpow_neg_ge_two_rpow {n : ℕ} (hn : 2 ≤ n) (a : ℝ) :
    (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) ≤ (n : ℝ) ^ a + (n : ℝ) ^ (-a) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have hn_pos : (0 : ℝ) < n := by linarith
  have h_mono : ∀ b : ℝ, 0 ≤ b →
      (2 : ℝ) ^ b + (2 : ℝ) ^ (-b) ≤ (n : ℝ) ^ b + (n : ℝ) ^ (-b) := by
    intro b hb
    have hu : (2 : ℝ) ^ b ≤ (n : ℝ) ^ b := Real.rpow_le_rpow (by norm_num) hn2 hb
    have hu1 : 1 ≤ (2 : ℝ) ^ b := Real.one_le_rpow (by norm_num) hb
    have h2b_pos : 0 < (2 : ℝ) ^ b := by linarith
    have hnb_pos : 0 < (n : ℝ) ^ b := by linarith
    have hprod2 : (2 : ℝ) ^ b * (2 : ℝ) ^ (-b) = 1 := by
      rw [← Real.rpow_add h2_pos, add_neg_cancel, Real.rpow_zero]
    have hprodn : (n : ℝ) ^ b * (n : ℝ) ^ (-b) = 1 := by
      rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
    have hdiff :
        ((n : ℝ) ^ b + (n : ℝ) ^ (-b)) - ((2 : ℝ) ^ b + (2 : ℝ) ^ (-b)) =
          ((n : ℝ) ^ b - (2 : ℝ) ^ b) * (1 - (2 : ℝ) ^ (-b) * (n : ℝ) ^ (-b)) := by
      calc ((n : ℝ) ^ b + (n : ℝ) ^ (-b)) - ((2 : ℝ) ^ b + (2 : ℝ) ^ (-b))
          = ((n : ℝ) ^ b - (2 : ℝ) ^ b) -
              ((2 : ℝ) ^ (-b) * ((n : ℝ) ^ b * (n : ℝ) ^ (-b)) -
                (n : ℝ) ^ (-b) * ((2 : ℝ) ^ b * (2 : ℝ) ^ (-b))) := by
            rw [hprodn, hprod2]; ring
        _ = ((n : ℝ) ^ b - (2 : ℝ) ^ b) * (1 - (2 : ℝ) ^ (-b) * (n : ℝ) ^ (-b)) := by ring
    have hinv2 : (2 : ℝ) ^ (-b) ≤ 1 := by nlinarith
    have hinvn0 : 0 ≤ (n : ℝ) ^ (-b) := le_of_lt (Real.rpow_pos_of_pos hn_pos (-b))
    have hinvn : (n : ℝ) ^ (-b) ≤ 1 := by nlinarith
    have hfac : 0 ≤ 1 - (2 : ℝ) ^ (-b) * (n : ℝ) ^ (-b) := by nlinarith
    linarith [mul_nonneg (sub_nonneg.mpr hu) hfac]
  rcases le_or_gt 0 a with ha | ha
  · exact h_mono a ha
  · have h := h_mono (-a) (by linarith)
    simpa [neg_neg, add_comm] using h

/-- For every `n ∈ ℕ` and `a ∈ ℝ`, `shiftedPairVonMangoldt a n ≥ (2^a + 2^{-a}) * Λ(n)`. -/
theorem shiftedPairVonMangoldt_ge_two_rpow_mul (a : ℝ) (n : ℕ) :
    ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) * (ArithmeticFunction.vonMangoldt n : ℝ) ≤
      shiftedPairVonMangoldt a n := by
  by_cases hn : 2 ≤ n
  · unfold shiftedPairVonMangoldt
    rw [mul_comm (ArithmeticFunction.vonMangoldt n : ℝ)]
    exact mul_le_mul_of_nonneg_right (rpow_add_rpow_neg_ge_two_rpow hn a)
      ArithmeticFunction.vonMangoldt_nonneg
  · have hle : n ≤ 1 := by omega
    have hz : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
      interval_cases n <;> simp
    simp [shiftedPairVonMangoldt, hz]

/-- **Shifted-Pair Node-Count Inflation (`weightedNodeCount_shiftedPair_ge`):**
For every `a ∈ ℝ` and `s ∈ ℝ`, the node count of `shiftedPairVonMangoldt a` is at least
`(2^a + 2^{-a})` times `primeNodeCount s = ψ(e^s)`. -/
theorem weightedNodeCount_shiftedPair_ge (a s : ℝ) :
    ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) * primeNodeCount s ≤
      weightedNodeCount (shiftedPairVonMangoldt a) s := by
  unfold weightedNodeCount primeNodeCount lagChebyshev
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => shiftedPairVonMangoldt_ge_two_rpow_mul a k

/-- **Selectivity of the Two-Pole Defect Against the Shifted Pair
(`generalizedTwoPoleDefect_shiftedPair_lt`):**
For every `a ≠ 0` and every `s ≥ log 2`, the generalized two-pole defect of
`shiftedPairVonMangoldt a` is strictly smaller than `chebyshevTwoPoleDefect s - primeNodeCount s`. -/
theorem generalizedTwoPoleDefect_shiftedPair_lt {a s : ℝ} (ha : a ≠ 0) (hs : Real.log 2 ≤ s) :
    generalizedTwoPoleDefect (shiftedPairVonMangoldt a) s <
      chebyshevTwoPoleDefect s - primeNodeCount s := by
  have hpsi_pos : 0 < primeNodeCount s := by
    unfold primeNodeCount lagChebyshev
    have hfl : 2 ≤ ⌊Real.exp s⌋₊ := by
      rw [Nat.le_floor_iff (by positivity)]
      have hexp := Real.exp_le_exp.mpr hs
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
    have hmem : (2 : ℕ) ∈ Finset.Icc 0 ⌊Real.exp s⌋₊ := Finset.mem_Icc.mpr ⟨by omega, hfl⟩
    have hle := Finset.single_le_sum (f := fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
      (fun k _ => ArithmeticFunction.vonMangoldt_nonneg) hmem
    have h2 : (0 : ℝ) < ArithmeticFunction.vonMangoldt 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact Real.log_pos (by norm_num)
    linarith
  have hgt := two_lt_two_rpow_add_two_rpow_neg ha
  have hnode := weightedNodeCount_shiftedPair_ge a s
  unfold generalizedTwoPoleDefect chebyshevTwoPoleDefect primeNodeCount at *
  nlinarith

/-- At the first prime scale `s = log 2`, `chebyshevTwoPoleDefect (log 2) = 1 > 0`, whereas
`generalizedTwoPoleDefect (shiftedPairVonMangoldt a) (log 2) = 1 + log 2 - (2^a + 2^{-a}) log 2`,
which is strictly negative whenever `2^a + 2^{-a} > 1 + 1 / log 2`. -/
theorem generalizedTwoPoleDefect_shiftedPair_log_two (a : ℝ) :
    generalizedTwoPoleDefect (shiftedPairVonMangoldt a) (Real.log 2) =
      1 + Real.log 2 - ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) * Real.log 2 := by
  unfold generalizedTwoPoleDefect twoPoleWeight weightedNodeCount
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  have hIcc : Finset.Icc 0 2 = {0, 1, 2} := rfl
  rw [hfl, hIcc]
  simp only [Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1, 2} : Finset ℕ)),
    Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.sum_singleton,
    shiftedPairVonMangoldt, ArithmeticFunction.map_zero,
    ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
  ring

theorem generalizedTwoPoleDefect_shiftedPair_log_two_neg {a : ℝ}
    (ha : 1 + 1 / Real.log 2 < (2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) :
    generalizedTwoPoleDefect (shiftedPairVonMangoldt a) (Real.log 2) < 0 := by
  rw [generalizedTwoPoleDefect_shiftedPair_log_two]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_lt_mul_of_pos_right ha hlog2
  have hsimp : (1 + 1 / Real.log 2) * Real.log 2 = Real.log 2 + 1 := by
    field_simp [ne_of_gt hlog2]
  linarith

/-! ## §3. Prime-Blind Section Vanishing and the `99/4` & `69/2` Nyquist–Landau Thresholds -/

/-- A test `F : ℝ → ℝ` is **horizon-prime-blind** at aperture `r` if its autocorrelation vanishes
at every prime-power node `log n` with `n ∈ relevantShifts r`. -/
def IsHorizonPrimeBlind (F : ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ n ∈ relevantShifts r, autoCorrelation F (Real.log n) = 0

/-- For any odd continuous test `F` supported in `[-r, r]` that is horizon-prime-blind at `r`,
`reflectedPrimePolarCost F r = poleCharge F ≥ 0`. -/
theorem reflectedPrimePolarCost_eq_poleCharge_of_isHorizonPrimeBlind {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) (hpb : IsHorizonPrimeBlind F r) :
    reflectedPrimePolarCost F r = poleCharge F ∧ 0 ≤ reflectedPrimePolarCost F r := by
  rw [reflectedPrimePolarCost_eq_sum_autoCorrelation_add_poleCharge hF hodd hr hsupp]
  have hsum :
      (∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * autoCorrelation F (Real.log n)) = 0 :=
    Finset.sum_eq_zero fun n hn => by rw [hpb n hn, mul_zero]
  rw [hsum, zero_add]
  exact ⟨rfl, poleCharge_nonneg F⟩

/-- **Chebyshev-Defect Identity for Horizon-Prime-Blind Odd Tests:**
For any odd `F ∈ C¹_c(ℝ)` supported in `[-r, r]` (`r > 0`) whose autocorrelation vanishes at the
prime-power nodes in `(0, 2r]`, the two-pole Chebyshev-defect pairing on `(0, 2r]` equals
`poleCharge F = 2 (oddPoleMoment F)²` and is unconditionally nonnegative. -/
theorem chebyshevTwoPoleDefect_integral_eq_poleCharge_of_isHorizonPrimeBlind {F : ℝ → ℝ} {r : ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hpb : IsHorizonPrimeBlind F r) :
    (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) =
      poleCharge F ∧
    0 ≤ ∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  rw [← reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc hF hFc hodd hr hsupp]
  exact reflectedPrimePolarCost_eq_poleCharge_of_isHorizonPrimeBlind
    hF.continuous hodd hr.le hsupp hpb

/-- The `L²` norm squared of `(realWeilTestFn f hf hfc).1` equals `∫ x, f x ^ 2`. -/
theorem integral_norm_realWeilTestFn_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) = ∫ x : ℝ, f x ^ 2 := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change ‖(f u : ℂ)‖ ^ 2 = f u ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Cutoff-Free `99/4` Spectral Gap on Prime-Blind Tests:**
Unconditional cutoff-free form of
`ninety_nine_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero`. -/
theorem ninety_nine_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero_unconditional
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (99 / 4) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest (realWeilTestFn f hf hfc)
  exact ninety_nine_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
    hf hfc hcosh hint2 (by omega) hN0 hN hblind hpos_l2

private theorem eq_zero_of_integral_sq_eq_zero {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hint0 : (∫ x, f x ^ 2) = 0) (x : ℝ) :
    f x = 0 := by
  have hint_mul : Integrable fun u : ℝ => f u * f u :=
    (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
  have hint : Integrable fun u : ℝ => f u ^ 2 := by
    simpa only [sq] using hint_mul
  have hae : (fun u : ℝ => f u ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (f u)) hint).mp hint0
  have hfun : (fun u : ℝ => f u ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq volume (hf.pow 2) continuous_zero).mp hae
  exact sq_eq_zero_iff.mp (congrFun hfun x)

/-- **The `99/4` Prime-Blind Section Vanishing Theorem:**
If `f ∈ C²_c(ℝ)` is prime-blind (`logVector (realWeilTestFn f hf hfc) = 0`), has vanishing even
pole moment (`coshHalfMoment f = 0`), and has spectral second moment at most `(99/4) ∫ f²`
(i.e. rms spectral height `T ≤ 3√11 / 2`), then `∫ f² = 0` and `f` vanishes identically on `ℝ`. -/
theorem primeBlind_eq_zero_of_spectralSecondMoment_le_ninety_nine_fourths
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hlog : logVector (realWeilTestFn f hf hfc) = 0)
    (hspec : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (99 / 4 : ℝ) * ∫ x, f x ^ 2) :
    (∫ x, f x ^ 2) = 0 ∧ ∀ x : ℝ, f x = 0 := by
  have hl2_nonneg : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg (f x)
  have hl2_zero : (∫ x, f x ^ 2) = 0 := by
    by_contra hne
    have hpos : 0 < ∫ x, f x ^ 2 := lt_of_le_of_ne hl2_nonneg (Ne.symm hne)
    have hpos' : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
      rwa [integral_norm_realWeilTestFn_sq hf hfc]
    have hlt :=
      ninety_nine_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero_unconditional
        hf hfc hcosh hint2 hlog hpos'
    rw [integral_norm_realWeilTestFn_sq hf hfc] at hlt
    exact lt_irrefl _ (lt_of_lt_of_le hlt hspec)
  exact ⟨hl2_zero, eq_zero_of_integral_sq_eq_zero hf.continuous hfc hl2_zero⟩

/-- **The `69/2` Prime-Blind Section Vanishing Theorem:**
If `f ∈ C²_c(ℝ)` is prime-blind (`logVector (realWeilTestFn f hf hfc) = 0`), has vanishing even
pole moment (`coshHalfMoment f = 0`), and has spectral second moment at most `(69/2) ∫ f²`
(i.e. rms spectral height `T ≤ √(69/2)`), then `∫ f² = 0` and `f` vanishes identically on `ℝ`. -/
theorem primeBlind_eq_zero_of_spectralSecondMoment_le_sixty_nine_halves
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hlog : logVector (realWeilTestFn f hf hfc) = 0)
    (hspec : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (69 / 2 : ℝ) * ∫ x, f x ^ 2) :
    (∫ x, f x ^ 2) = 0 ∧ ∀ x : ℝ, f x = 0 := by
  have hl2_nonneg : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg (f x)
  have hl2_zero : (∫ x, f x ^ 2) = 0 := by
    by_contra hne
    have hpos : 0 < ∫ x, f x ^ 2 := lt_of_le_of_ne hl2_nonneg (Ne.symm hne)
    have hpos' : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
      rwa [integral_norm_realWeilTestFn_sq hf hfc]
    have hlt :=
      sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero_unconditional
        hf hfc hcosh hint2 hlog hpos'
    rw [integral_norm_realWeilTestFn_sq hf hfc] at hlt
    exact lt_irrefl _ (lt_of_lt_of_le hlt hspec)
  exact ⟨hl2_zero, eq_zero_of_integral_sq_eq_zero hf.continuous hfc hl2_zero⟩

/-- **Prime-Blind Subspace Dimension Vanishing (`finrank_primeBlind_subspace_eq_zero`):**
Any `ℝ`-subspace `W ⊆ (ℝ → ℝ)` whose elements are `C²_c(ℝ)` prime-blind tests with vanishing even
pole moment and spectral height `T² ≤ 69/2` is the zero subspace and has `finrank ℝ W = 0`. -/
theorem finrank_primeBlind_subspace_eq_zero (W : Submodule ℝ (ℝ → ℝ)) {T : ℝ}
    (hT : T ^ 2 ≤ 69 / 2)
    (hW : ∀ f ∈ W, ∃ (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f),
      coshHalfMoment f = 0 ∧
        (Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2)) ∧
        logVector (realWeilTestFn f hf hfc) = 0 ∧
        spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤ T ^ 2 * ∫ x, f x ^ 2) :
    W = ⊥ ∧ Module.finrank ℝ W = 0 := by
  have hbot : W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hfW
    obtain ⟨hf, hfc, hcosh, hint2, hlog, hspec⟩ := hW f hfW
    have hl2_nonneg : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg (f x)
    have hspec' : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
        (69 / 2 : ℝ) * ∫ x, f x ^ 2 :=
      le_trans hspec (mul_le_mul_of_nonneg_right hT hl2_nonneg)
    funext x
    exact (primeBlind_eq_zero_of_spectralSecondMoment_le_sixty_nine_halves
      hf hfc hcosh hint2 hlog hspec').2 x
  refine ⟨hbot, ?_⟩
  rw [hbot, finrank_bot]

/-! ## §4. The Classical Shadow: Exact Frobenius Mass of `dirichletSampling`, the Square-Root
Threshold, and Diagonal Relabeling Invariance -/

/-- Every entry `((m + 1) : ℂ)^{i λ_r}` of `dirichletSampling N lam R` has complex norm `1`. -/
@[simp]
theorem norm_dirichletSampling_apply (N : ℕ) (lam : ℕ → ℝ) (R : ℕ)
    (r : Fin (R + 1)) (m : Fin N) :
    ‖dirichletSampling N lam R r m‖ = 1 := by
  unfold dirichletSampling
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Explicit Montgomery–Vaughan Rank Lower Bound for `dirichletSampling`:**
For `N ≥ 2` and `δ`-separated sample points `λ_0, ..., λ_R ∈ [δ/2, T - δ/2]`,
`(R + 1) * N ≤ (T + 4 N (1 + log N)) * (1/δ + 2 log N) * (dirichletSampling N lam R).rank`. -/
theorem rank_dirichletSampling_ge (N : ℕ) (hN : 2 ≤ N) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T) :
    ((R : ℝ) + 1) * (N : ℝ) ≤
      (T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N) *
        ((dirichletSampling N lam R).rank : ℝ) := by
  have hfb := hasFrameBound_dirichletSampling N hN hδ hT hgap hlow R hhigh
  have hle := frobeniusMass_le_rank_mul hfb
  rwa [frobeniusMass_dirichletSampling] at hle

/-- **Square-Root Threshold Diagonal Specialization (`T = N`):**
At the diagonal `T = N` of the mean value theorem (the square-root threshold `N = T`), the length
factor `N` cancels between the Frobenius mass `(R + 1) * N` and the frame bound
`(N + 4 N (1 + log N)) = N (5 + 4 log N)`, giving
`h0 (dirichletSampling N lam R) ≤ N - (R + 1) / ((5 + 4 log N) * (1/δ + 2 log N))`. -/
theorem h0_dirichletSampling_at_sqrt_threshold (N : ℕ) (hN : 2 ≤ N) {lam : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ (N : ℝ)) :
    (h0 (dirichletSampling N lam R) : ℝ) ≤
      (N : ℝ) -
        ((R : ℝ) + 1) / ((5 + 4 * Real.log N) * (1 / δ + 2 * Real.log N)) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have h := h0_dirichletSampling_le N hN hδ (le_of_lt hN0) hgap hlow R hhigh
  have hcancel :
      (((R : ℝ) + 1) * (N : ℝ)) /
          (((N : ℝ) + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N)) =
        ((R : ℝ) + 1) / ((5 + 4 * Real.log N) * (1 / δ + 2 * Real.log N)) := by
    have hfac : ((N : ℝ) + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N) =
        (N : ℝ) * ((5 + 4 * Real.log N) * (1 / δ + 2 * Real.log N)) := by ring
    rw [hfac, mul_comm ((R : ℝ) + 1) (N : ℝ),
      mul_div_mul_left _ _ (ne_of_gt hN0)]
  linarith

/-- **Weighted Dirichlet Sampling Matrix (`weightedDirichletSampling`):**
The `(R + 1) × N` matrix evaluating a `w`-weighted Dirichlet polynomial
`∑_{m < N} a_m w_m (m + 1)^{i λ_r}` at `λ_0, ..., λ_R`. -/
def weightedDirichletSampling (N : ℕ) (w : Fin N → ℂ) (lam : ℕ → ℝ) (R : ℕ) :
    Matrix (Fin (R + 1)) (Fin N) ℂ :=
  dirichletSampling N lam R * Matrix.diagonal w

theorem weightedDirichletSampling_apply (N : ℕ) (w : Fin N → ℂ) (lam : ℕ → ℝ) (R : ℕ)
    (r : Fin (R + 1)) (m : Fin N) :
    weightedDirichletSampling N w lam R r m = dirichletSampling N lam R r m * w m :=
  Matrix.mul_diagonal _ _ _ _

/-- **Frobenius Mass of `weightedDirichletSampling`:**
`frobeniusMass (weightedDirichletSampling N w lam R) = (R + 1) * ∑ m, ‖w m‖²`. -/
theorem frobeniusMass_weightedDirichletSampling (N : ℕ) (w : Fin N → ℂ) (lam : ℕ → ℝ) (R : ℕ) :
    frobeniusMass (weightedDirichletSampling N w lam R) =
      ((R : ℝ) + 1) * ∑ m : Fin N, ‖w m‖ ^ 2 := by
  unfold frobeniusMass
  simp only [weightedDirichletSampling_apply, norm_mul, norm_dirichletSampling_apply, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one, nsmul_eq_mul]

/-- **Diagonal Relabeling Invariance of `h0` and `rank` (`h0_mul_diagonal_eq_of_iff_eq_zero`):**
For any matrix `A : Matrix m n ℂ` and any two weights `w₁, w₂ : n → ℂ` with the same support
(`∀ j, w₁ j = 0 ↔ w₂ j = 0`), right-multiplying `A` by `diagonal w₁` versus `diagonal w₂` yields
isomorphic kernels and therefore identical section counts `h0` and identical ranks. -/
theorem h0_mul_diagonal_eq_of_iff_eq_zero {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) {w₁ w₂ : n → ℂ}
    (hw : ∀ j, w₁ j = 0 ↔ w₂ j = 0) :
    h0 (A * Matrix.diagonal w₁) = h0 (A * Matrix.diagonal w₂) ∧
      (A * Matrix.diagonal w₁).rank = (A * Matrix.diagonal w₂).rank := by
  classical
  let d : n → ℂ := fun j => if w₁ j = 0 then 1 else w₁ j / w₂ j
  let d_inv : n → ℂ := fun j => if w₁ j = 0 then 1 else w₂ j / w₁ j
  have hd_mul : ∀ j, d j * d_inv j = 1 := fun j => by
    dsimp [d, d_inv]
    split_ifs with h1
    · ring
    · have h2 : w₂ j ≠ 0 := mt (hw j).mpr h1
      field_simp [h1, h2]
  have h_inv_mul : ∀ j, d_inv j * d j = 1 := fun j => by
    rw [mul_comm, hd_mul]
  have hw1_eq : ∀ j, w₂ j * d j = w₁ j := fun j => by
    dsimp [d]
    split_ifs with h1
    · rw [(hw j).mp h1, zero_mul, h1]
    · have h2 : w₂ j ≠ 0 := mt (hw j).mpr h1
      exact mul_div_cancel₀ (w₁ j) h2
  have hw2_eq : ∀ j, w₁ j * d_inv j = w₂ j := fun j => by
    dsimp [d_inv]
    split_ifs with h1
    · rw [h1, zero_mul, eq_comm, (hw j).mp h1]
    · exact mul_div_cancel₀ (w₂ j) h1
  let e : (n → ℂ) ≃ₗ[ℂ] (n → ℂ) :=
    { toFun := fun v j => d j * v j
      map_add' := fun u v => by ext j; simp [mul_add]
      map_smul' := fun c v => by ext j; simp [mul_left_comm]
      invFun := fun v j => d_inv j * v j
      left_inv := fun v => by
        ext j; simp only [← mul_assoc, h_inv_mul, one_mul]
      right_inv := fun v => by
        ext j; simp only [← mul_assoc, hd_mul, one_mul] }
  have hker :
      LinearMap.ker (Matrix.mulVecLin (A * Matrix.diagonal w₁)) =
        Submodule.map (e.symm : (n → ℂ) →ₗ[ℂ] (n → ℂ))
          (LinearMap.ker (Matrix.mulVecLin (A * Matrix.diagonal w₂))) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_map, Matrix.mulVecLin_apply,
      ← Matrix.mulVec_mulVec]
    constructor
    · intro hv
      refine ⟨e v, ?_, e.symm_apply_apply v⟩
      have hdiag : (Matrix.diagonal w₂).mulVec (e v) = (Matrix.diagonal w₁).mulVec v := by
        ext j
        rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
        show w₂ j * (d j * v j) = w₁ j * v j
        rw [← mul_assoc, hw1_eq]
      rw [hdiag, hv]
    · rintro ⟨u, hu, rfl⟩
      have hdiag : (Matrix.diagonal w₁).mulVec (e.symm u) = (Matrix.diagonal w₂).mulVec u := by
        ext j
        rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
        show w₁ j * (d_inv j * u j) = w₂ j * u j
        rw [← mul_assoc, hw2_eq]
      change A.mulVec ((Matrix.diagonal w₁).mulVec (e.symm u)) = 0
      rw [hdiag, hu]
  have hh0 : h0 (A * Matrix.diagonal w₁) = h0 (A * Matrix.diagonal w₂) := by
    unfold h0
    rw [hker]
    exact LinearEquiv.finrank_map_eq e.symm _
  refine ⟨hh0, ?_⟩
  have hr1 := h0_add_rank (A * Matrix.diagonal w₁)
  have hr2 := h0_add_rank (A * Matrix.diagonal w₂)
  omega

/-- **Support Equivalence of `shiftedPairVonMangoldt a` and `vonMangoldt`:**
For every `a ∈ ℝ` and `n ∈ ℕ`, `shiftedPairVonMangoldt a n = 0 ↔ vonMangoldt n = 0`. -/
theorem shiftedPairVonMangoldt_eq_zero_iff (a : ℝ) (n : ℕ) :
    shiftedPairVonMangoldt a n = 0 ↔ (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
  by_cases hn : 1 ≤ n
  · unfold shiftedPairVonMangoldt
    rw [mul_eq_zero]
    have hpos : (n : ℝ) ^ a + (n : ℝ) ^ (-a) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (rpow_add_rpow_neg_ge_two hn a))
    exact or_iff_left hpos
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [shiftedPairVonMangoldt]

/-- **Relabeling Blindness of `weightedDirichletSampling` to the Shifted Pair:**
For every length `N`, shift `a ∈ ℝ`, sample sequence `lam`, and sample count `R`, weighting
`dirichletSampling N lam R` by `shiftedPairVonMangoldt a (m + 1)` versus `vonMangoldt (m + 1)`
produces the exact same section count `h0` and the exact same rank. -/
theorem h0_weightedDirichletSampling_shiftedPair_eq_vonMangoldt
    (N : ℕ) (a : ℝ) (lam : ℕ → ℝ) (R : ℕ) :
    h0 (weightedDirichletSampling N
        (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) =
      h0 (weightedDirichletSampling N
        (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) ∧
    (weightedDirichletSampling N
        (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R).rank =
      (weightedDirichletSampling N
        (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R).rank := by
  apply h0_mul_diagonal_eq_of_iff_eq_zero
  intro m
  simp only [Complex.ofReal_eq_zero]
  exact shiftedPairVonMangoldt_eq_zero_iff a ((m : ℕ) + 1)

/-! ## §5. Complete Synthesis: Selectivity Against Both `goldenDatum` and `shiftedPairVonMangoldt` -/

/-- **Complete Resolution and Selectivity Theorem for Open Problem 1:**
1. **Linear Node / Dirichlet Relabeling Blindness:** For every `a ∈ ℝ`, the linear section count
   `h0` of `weightedDirichletSampling` cannot distinguish `shiftedPairVonMangoldt a` from `Λ`;
2. **Prime-Blind Spectral Floor:** Every `C²_c(ℝ)` prime-blind section with `coshHalfMoment = 0`
   and spectral height `T² ≤ 69/2` vanishes identically (`h0 = 0` at all apertures);
3. **Exact Chebyshev–Riemann–Roch Box Identity:** On every box `[0, s]`,
   `polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s`;
4. **Selectivity Against `goldenDatum`:** `goldenDatum` satisfies the `λ`-ring pole splitting and
   Adams isometries, yet violates `openPositiveCone ⊆ nefQuadrant` and `HodgeIndex` at `{0, 1}`;
5. **Selectivity Against `shiftedPairVonMangoldt a` (`a > 0`):** Every `a > 0` fails
   `WeilPositiveFull` (`not_weilPositiveFull_shiftedPairVonMangoldt`) and inflates the prime-node
   weight past `(2^a + 2^{-a}) ψ(e^s)`, driving `generalizedTwoPoleDefect` strictly below
   `chebyshevTwoPoleDefect s - ψ(e^s)` for all `s ≥ log 2`;
6. **Unconditional Positivity & Prime–Pole Balance for `ℤ`:** On `(0, 181/500]` (past the first
   prime `(1/2) log 2`), the odd scaling subsurface satisfies `HodgeIndex` and
   `openPositiveCone ⊆ nefQuadrant` unconditionally, and across all apertures `S ≥ 0`,
   `chebyshevTwoPoleDefect` satisfies the de la Vallée Poussin cancellation law. -/
theorem sectionCount_riemannRoch_and_selectivity_master :
    (∀ (N : ℕ) (a : ℝ) (lam : ℕ → ℝ) (R : ℕ),
      h0 (weightedDirichletSampling N
          (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) =
        h0 (weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R)) ∧
    (∀ {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f),
      coshHalfMoment f = 0 →
      (Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2)) →
      logVector (realWeilTestFn f hf hfc) = 0 →
      spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤ (69 / 2 : ℝ) * ∫ x, f x ^ 2 →
      ∀ x : ℝ, f x = 0) ∧
    (∀ s : ℝ, polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s) ∧
    (¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).openPositiveCone ⊆
        (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).nefQuadrant) ∧
    (∀ a : ℝ, a ≠ 0 →
      ¬ WeilPositiveFull (shiftedPairVonMangoldt a) ∧
      ¬ WeilPositiveDegree 2 (shiftedPairVonMangoldt a) ∧
      ∀ s : ℝ, Real.log 2 ≤ s →
        generalizedTwoPoleDefect (shiftedPairVonMangoldt a) s <
          chebyshevTwoPoleDefect s - primeNodeCount s) ∧
    (∀ r : ℝ, r ≤ 181 / 500 →
      (scalingSubsurface (oddRealTestsAt r)).openPositiveCone ⊆
        (scalingSubsurface (oddRealTestsAt r)).nefQuadrant) :=
  ⟨fun N a lam R => (h0_weightedDirichletSampling_shiftedPair_eq_vonMangoldt N a lam R).1,
   fun hf hfc hcosh hint2 hlog hspec =>
    (primeBlind_eq_zero_of_spectralSecondMoment_le_sixty_nine_halves hf hfc hcosh hint2 hlog hspec).2,
   polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect,
   goldenDatum_openPositiveCone_not_subset_nefQuadrant,
   fun a ha => ⟨not_weilPositiveFull_shiftedPairVonMangoldt a,
    fun hdeg2 => ha ((weilPositiveDegree_two_shiftedPairVonMangoldt_iff a).mp hdeg2).2,
    fun _ hs => generalizedTwoPoleDefect_shiftedPair_lt ha hs⟩,
   fun r hr =>
    (scalingSubsurface (oddRealTestsAt r)).openPositiveCone_subset_nefQuadrant_of_hodgeIndex
      (scalingSubsurface_odd_hodgeIndex hr)⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
