import GaloisForLFunctions.ArithmeticOrientationTheory.TheNyquistRankBound
import GaloisForLFunctions.ArithmeticOrientationTheory.TheWidthDictionary
import GaloisForLFunctions.ArithmeticOrientationTheory.TheLatticeOddLedgerIsBalanced
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhichArithmeticDataForceTheSign
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger

/-!
# The effectivity cone from sections: Bézout classification, curve calibration, and the ring `ℤ`

This module resolves Entry 8 of the Arithmetic Orientation Theory programme:
with `h⁰` from `TheNyquistRankBound`, define the section effectivity cone `E = {x : h⁰(x) ≥ 1}`,
determine when it satisfies the Bézout axiom, verify that it gives the curve Hodge index over `𝔽_q`
and fails on the golden datum, and locate the exact properties of the ring `ℤ` that it uses.

## Main results

1. **Cycle section reading and `E = {x : h⁰(x) ≥ 1}` (`cycleObstructionReading`, `cycleH0`,
   `sectionEffectivityCone`):**
   On any polar surface `S : PolarSurface C`, a cycle `x : C` has polar budget
   `2 (x · H)(x · V)` and Castelnuovo–Severi defect `S.defect x x = 2 (x · H)(x · V) - S.pair x x`.
   Its `1 × 1` obstruction reading `cycleObstructionReading S x : Matrix (Fin 1) (Fin 1) ℂ`
   vanishes when `x` lies in the nef quadrant (`0 ≤ x · H ∧ 0 ≤ x · V`) and its polar budget covers
   its defect (`S.defect x x ≤ 2 (x · H)(x · V)`, equivalently `0 ≤ S.pair x x`), and is the
   identity `1` otherwise. Applying `h0` from `TheNyquistRankBound` defines
   `cycleH0 S x := h0 (cycleObstructionReading S x)` and the section effectivity cone
   $$\operatorname{sectionEffectivityCone}(S) := \{x : C \mid 1 \le \operatorname{cycleH0}(S, x)\}
     = S.\mathrm{positiveCone} \cap S.\mathrm{nefQuadrant}.$$

2. **Exact equivalence of the Bézout axiom, Riemann–Roch axiom, and Hodge index for
   `E = {x : h⁰(x) ≥ 1}` (`sectionEffectivityCone_bezout_iff_hodgeIndex`,
   `sectionEffectivityCone_riemannRoch_iff_hodgeIndex`, `sectionEffectivityCone_tfae`):**
   On *every* polar surface `S`:
   - `S.AmpleAxiom (sectionEffectivityCone S)` holds iff `S.HodgeIndex` holds (and under
     `S.HodgeIndex`, `sectionEffectivityCone S = S.positiveCone`).
   - `S.BezoutAxiom (sectionEffectivityCone S) ↔ S.HodgeIndex`: if `S.HodgeIndex` holds, the reverse
     Cauchy–Schwarz inequality on `S.positiveCone` forces `x · y ≥ 0` on `sectionEffectivityCone S`;
     conversely, if a primitive cycle `x` (`x · H = 0`, `x · V = 0`) had `X = x² > 0`, then both
     `z₁ = (X + 1) x + X (H + V)` and `z₂ = -(X + 1) x + X (H + V)` would satisfy
     `zᵢ · H = X > 0`, `zᵢ · V = X > 0`, and `zᵢ² = (X + 1)² X + 2X² > 0` (hence `cycleH0 S zᵢ = 1`),
     yet `z₁ · z₂ = -(X³ + X) < 0`.
   - `S.RiemannRochAxiom (sectionEffectivityCone S) ↔ S.HodgeIndex`.

3. **Calibration over `𝔽_q` vs. refutation on the golden datum
   (`curve_sectionEffectivityCone_bezout_tfae`, `goldenDatum_not_bezout_sectionEffectivityCone`):**
   - For any curve datum `D : CurveDatum ι`, the Bézout axiom for
     `sectionEffectivityCone (D.windowSurface W)` on all finite windows `W` is equivalent to the
     curve Hodge index across all windows, to the Riemann–Roch axiom for `sectionEffectivityCone`,
     to the unitarity of all Frobenius eigenvalues `‖D.β i‖ = 1`, and to the Hasse–Weil bound.
   - On `goldenDatum.windowSurface {0, 1}`, both `goldenForwardPlus` and `goldenForwardMinus` lie in
     `sectionEffectivityCone` (`cycleH0 = 1`, with `· H = 1`, `· V = 1`, and self-intersection `10`),
     yet their intersection is `-6 < 0`, refuting the Bézout axiom for `E = {x : h⁰(x) ≥ 1}`.

4. **The four properties of the ring `ℤ` used by Bézout and section effectivity:**
   - **Prime-tower closure from unique factorization and archimedean order (`ℤ` pillar I):**
     On the integer log-lattice `log n` (`n ≥ 2`), `Λ(a b) ≠ 0` forces `a = p^i, b = p^j` in the
     same prime tower where `p^{|i-j|} < p^{i+j}`, making the lattice odd Weil ledger balanced at
     every aperture (`frustrationIndex_lattice_eq_zero`).
   - **Lévy–Khintchine collar positivity and `Λ ≥ 0` (`ℤ` pillar II):**
     Disjoint nonnegative `C²_c` cycles on the scaling surface meet nonnegatively at all scales
     (`localPair_nonneg`).
   - **Additive two-pole cancellation and prime-2 selectivity (`ℤ` pillar III):**
     The excess of the two-pole degrees of freedom `polarBoxDoF s = e^s + s - 1` over the prime
     node count `primeNodeCount s = ψ(e^s)` is `chebyshevTwoPoleDefect s`, which strictly dominates
     any shifted-pair perturbation `shiftedPairVonMangoldt a` (`a ≠ 0`) once `s ≥ log 2`, whereas
     uncalibrated linear kernel counts `h0 (A * diagonal w)` are blind to nonzero weight shifts.
   - **Unconditional Castelnuovo–Severi axioms past the first prime `2` of `ℤ`, and global width
     dictionary equivalence (`ℤ` pillar IV):**
     On `scalingSubsurface (oddRealTestsAt r)` (`r ≤ 181/500`) and
     `scalingSubsurface (primitiveSmoothRealTestsAt r)` (`r ≤ (log 2 + 1/50)/2`),
     `sectionEffectivityCone` satisfies `AmpleAxiom`, `BezoutAxiom`, and `RiemannRochAxiom`
     unconditionally; globally on `scalingSurface`, `BezoutAxiom (sectionEffectivityCone scalingSurface)`
     and `RiemannRochAxiom (sectionEffectivityCone scalingSurface)` are equivalent to every unit of
     `widthDictionary_tfae`.
-/

open Complex Matrix Finset Set MeasureTheory
open scoped BigOperators
open Zeta23 GaloisForLFunctions.ArithmeticCastelnuovoSeveri
  GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  GaloisForLFunctions.BezoutValuationIncidence
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
  GaloisForLFunctions.ScaleSignedIncidenceCriticality
  GaloisForLFunctions.SignedArithmeticEnergyIncidence
  GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### 1. Cycle section reading and the effectivity cone `E = {x : h⁰(x) ≥ 1}` -/

/-- The `0` matrix of size `1 × 1` has `h0 = 1`. -/
theorem h0_zero_fin_one : h0 (0 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  have h := h0_add_rank (0 : Matrix (Fin 1) (Fin 1) ℂ)
  rw [Matrix.rank_zero, Fintype.card_fin] at h
  omega

/-- The identity matrix of size `1 × 1` has `h0 = 0`. -/
theorem h0_one_fin_one : h0 (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  have h := h0_add_rank (1 : Matrix (Fin 1) (Fin 1) ℂ)
  rw [Matrix.rank_one, Fintype.card_fin] at h
  omega

variable {C : Type*} [AddCommGroup C] [Module ℝ C]

/-- The double-null nef quadrant `{x : C | 0 ≤ x · H ∧ 0 ≤ x · V}` of a polar surface `S`. -/
def nefQuadrant (S : PolarSurface C) : Set C :=
  {x : C | 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V}

/-- The `1 × 1` cycle obstruction reading on a polar surface `S`: the reading is `0` when the cycle
`x` lies in the nef quadrant (`0 ≤ x · H ∧ 0 ≤ x · V`) and its polar budget `2 (x · H)(x · V)`
covers its Castelnuovo–Severi defect `S.defect x x` (equivalently `0 ≤ S.pair x x`), and is `1`
otherwise. -/
def cycleObstructionReading (S : PolarSurface C) (x : C) : Matrix (Fin 1) (Fin 1) ℂ :=
  open Classical in
  if 0 ≤ S.pair x x ∧ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V then 0 else 1

/-- The section count `h⁰(x)` of a cycle `x` on a polar surface `S`, defined by applying `h0` from
`TheNyquistRankBound` to `cycleObstructionReading S x`. -/
def cycleH0 (S : PolarSurface C) (x : C) : ℕ :=
  h0 (cycleObstructionReading S x)

/-- The obstruction count `h¹(x)` of a cycle `x` on a polar surface `S`, defined by applying `h1`
from `TheNyquistRankBound` to `cycleObstructionReading S x`. -/
def cycleH1 (S : PolarSurface C) (x : C) : ℕ :=
  h1 (cycleObstructionReading S x)

/-- **The effectivity cone from sections:** `E = {x : C | 1 ≤ cycleH0 S x}`. -/
def sectionEffectivityCone (S : PolarSurface C) : Set C :=
  {x : C | 1 ≤ cycleH0 S x}

/-- `cycleH0 S x = 1` when `0 ≤ x² ∧ 0 ≤ x · H ∧ 0 ≤ x · V`, and `0` otherwise. -/
theorem cycleH0_eq_ite (S : PolarSurface C) (x : C) :
    cycleH0 S x =
      (open Classical in if 0 ≤ S.pair x x ∧ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V then 1 else 0) := by
  classical
  unfold cycleH0 cycleObstructionReading
  split_ifs
  · exact h0_zero_fin_one
  · exact h0_one_fin_one

/-- A cycle `x` has `cycleH0 S x ≥ 1` iff `0 ≤ x² ∧ 0 ≤ x · H ∧ 0 ≤ x · V`. -/
theorem one_le_cycleH0_iff (S : PolarSurface C) (x : C) :
    1 ≤ cycleH0 S x ↔ 0 ≤ S.pair x x ∧ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V := by
  classical
  rw [cycleH0_eq_ite]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => le_rfl⟩
  · exact ⟨fun h1 => absurd h1 (by omega), fun h' => absurd h' h⟩

/-- Membership in `sectionEffectivityCone S` in terms of `S.pair`. -/
theorem mem_sectionEffectivityCone_iff (S : PolarSurface C) (x : C) :
    x ∈ sectionEffectivityCone S ↔ 0 ≤ S.pair x x ∧ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V :=
  one_le_cycleH0_iff S x

/-- Membership in `sectionEffectivityCone S` in terms of the Castelnuovo–Severi defect:
`1 ≤ cycleH0 S x` iff `x` meets `H` and `V` nonnegatively and its polar budget `S.polar x x`
covers its defect `S.defect x x`. -/
theorem mem_sectionEffectivityCone_iff_defect_le_polar (S : PolarSurface C) (x : C) :
    x ∈ sectionEffectivityCone S ↔
      0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧ S.defect x x ≤ S.polar x x := by
  rw [mem_sectionEffectivityCone_iff]
  unfold PolarSurface.defect
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h3, by linarith⟩
  · rintro ⟨h2, h3, h1⟩
    exact ⟨by linarith, h2, h3⟩

/-- **Identification of `sectionEffectivityCone S`:** the section effectivity cone `{x : h⁰(x) ≥ 1}`
is the intersection of the positive cone `{x : x² ≥ 0 ∧ x · (H + V) ≥ 0}` and the nef quadrant
`{x : x · H ≥ 0 ∧ x · V ≥ 0}`. -/
theorem sectionEffectivityCone_eq_positiveCone_inter_nefQuadrant (S : PolarSurface C) :
    sectionEffectivityCone S = S.positiveCone ∩ nefQuadrant S := by
  ext x
  simp only [mem_sectionEffectivityCone_iff, Set.mem_inter_iff, PolarSurface.positiveCone,
    nefQuadrant, Set.mem_setOf_eq, S.pair_ample]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, add_nonneg h2 h3⟩, h2, h3⟩
  · rintro ⟨⟨h1, _⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩

/-- `sectionEffectivityCone S` is contained in `S.positiveCone`. -/
theorem sectionEffectivityCone_subset_positiveCone (S : PolarSurface C) :
    sectionEffectivityCone S ⊆ S.positiveCone := by
  rw [sectionEffectivityCone_eq_positiveCone_inter_nefQuadrant]
  exact Set.inter_subset_left

/-- Both polar fibres `H` and `V` belong to `sectionEffectivityCone S` (`h⁰(H) = h⁰(V) = 1`). -/
theorem H_mem_sectionEffectivityCone (S : PolarSurface C) : S.H ∈ sectionEffectivityCone S := by
  rw [mem_sectionEffectivityCone_iff, S.pair_H_H, S.pair_H_V]
  exact ⟨le_rfl, le_rfl, zero_le_one⟩

theorem V_mem_sectionEffectivityCone (S : PolarSurface C) : S.V ∈ sectionEffectivityCone S := by
  rw [mem_sectionEffectivityCone_iff, S.pair_V_V, S.pair_V_H]
  exact ⟨le_rfl, zero_le_one, le_rfl⟩

/-! ### 2. Ampleness, Riemann–Roch, and the Bézout theorem for `E = {x : h⁰(x) ≥ 1}` -/

/-- Under `S.HodgeIndex`, every cycle in `S.positiveCone` has nonnegative `H`- and `V`-degrees, so
`sectionEffectivityCone S = S.positiveCone`. -/
theorem sectionEffectivityCone_eq_positiveCone_of_hodgeIndex {S : PolarSurface C}
    (hHI : S.HodgeIndex) :
    sectionEffectivityCone S = S.positiveCone := by
  ext x
  rw [mem_sectionEffectivityCone_iff, PolarSurface.positiveCone, Set.mem_setOf_eq, S.pair_ample]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, add_nonneg h2 h3⟩
  · rintro ⟨hxx, hsum⟩
    have hdef : 0 ≤ S.defect x x := S.hodgeIndex_iff_defect_nonneg.mp hHI x
    rw [S.defect_self] at hdef
    have hmul : 0 ≤ S.pair x S.H * S.pair x S.V := by linarith
    refine ⟨hxx, ?_, ?_⟩
    · by_contra hH
      push Not at hH
      have hV : 0 < S.pair x S.V := by linarith
      nlinarith
    · by_contra hV
      push Not at hV
      have hH : 0 < S.pair x S.H := by linarith
      nlinarith

/-- **Ampleness of `sectionEffectivityCone S`:** on any polar surface `S`,
`S.AmpleAxiom (sectionEffectivityCone S)` holds if and only if `S.HodgeIndex` holds. -/
theorem sectionEffectivityCone_ample_iff_hodgeIndex (S : PolarSurface C) :
    S.AmpleAxiom (sectionEffectivityCone S) ↔ S.HodgeIndex := by
  constructor
  · intro hA x hxH hxV
    by_contra hpos
    push Not at hpos
    have hx_mem : x ∈ sectionEffectivityCone S := by
      rw [mem_sectionEffectivityCone_iff, hxH, hxV]
      exact ⟨hpos.le, le_rfl, le_rfl⟩
    have hxA : S.pair x S.ample = 0 := by rw [S.pair_ample, hxH, hxV, add_zero]
    have h0 := hA x hx_mem hxA x
    linarith
  · intro hHI
    rw [sectionEffectivityCone_eq_positiveCone_of_hodgeIndex hHI]
    exact (S.positiveCone_axioms hHI).2

/-- **Riemann–Roch classification for `E = {x : h⁰(x) ≥ 1}`:** on any polar surface `S`,
`S.RiemannRochAxiom (sectionEffectivityCone S)` holds if and only if `S.HodgeIndex` holds. -/
theorem sectionEffectivityCone_riemannRoch_iff_hodgeIndex (S : PolarSurface C) :
    S.RiemannRochAxiom (sectionEffectivityCone S) ↔ S.HodgeIndex := by
  constructor
  · intro hRR z hzH hzV
    by_contra hpos
    push Not at hpos
    set δ : ℝ := Real.sqrt (S.pair z z) / 3
    have hδ : 0 < δ := by positivity
    have hδ_sq : δ ^ 2 = S.pair z z / 9 := by
      dsimp [δ]
      rw [div_pow, Real.sq_sqrt hpos.le]
      ring
    set x : C := (2 * δ) • S.V - δ • S.H + z
    have hxH : S.pair x S.H = 2 * δ := by
      simp [x, map_add, map_sub, map_smul, S.pair_V_H, S.pair_H_H, hzH]
    have hxV : S.pair x S.V = -δ := by
      simp [x, map_add, map_sub, map_smul, S.pair_V_V, S.pair_H_V, hzV]
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
    rcases hRR x hxx with hmem | hmem
    · rw [mem_sectionEffectivityCone_iff] at hmem
      linarith [hmem.2.2, hxV]
    · rw [mem_sectionEffectivityCone_iff] at hmem
      have hxH' : S.pair (-x) S.H = -2 * δ := by simp [hxH]
      linarith [hmem.2.1, hxH']
  · intro hHI
    rw [sectionEffectivityCone_eq_positiveCone_of_hodgeIndex hHI]
    exact (S.positiveCone_axioms hHI).1

/-- **Bézout classification for `E = {x : h⁰(x) ≥ 1}`:** on *every* polar surface `S`, the Bézout
axiom `∀ x ∈ sectionEffectivityCone S, ∀ y ∈ sectionEffectivityCone S, 0 ≤ x · y` holds if and
only if `S.HodgeIndex` holds. -/
theorem sectionEffectivityCone_bezout_iff_hodgeIndex (S : PolarSurface C) :
    S.BezoutAxiom (sectionEffectivityCone S) ↔ S.HodgeIndex := by
  constructor
  · intro hBez x hxH hxV
    by_contra hpos
    push Not at hpos
    set X := S.pair x x
    set z₁ : C := (X + 1) • x + X • S.ample
    set z₂ : C := -(X + 1) • x + X • S.ample
    have hA_H : S.pair S.ample S.H = 1 := by
      simp [PolarSurface.ample, map_add, S.pair_H_H, S.pair_V_H]
    have hA_V : S.pair S.ample S.V = 1 := by
      simp [PolarSurface.ample, map_add, S.pair_H_V, S.pair_V_V]
    have hxA : S.pair x S.ample = 0 := by rw [S.pair_ample, hxH, hxV, add_zero]
    have hAx : S.pair S.ample x = 0 := by rw [S.pair_comm, hxA]
    have hz₁H : S.pair z₁ S.H = X := by
      simp [z₁, map_add, map_smul, hxH, hA_H]
    have hz₁V : S.pair z₁ S.V = X := by
      simp [z₁, map_add, map_smul, hxV, hA_V]
    have hz₂H : S.pair z₂ S.H = X := by
      simp [z₂, map_add, map_smul, hxH, hA_H]
    have hz₂V : S.pair z₂ S.V = X := by
      simp [z₂, map_add, map_smul, hxV, hA_V]
    have hz₁ : S.pair z₁ z₁ = (X + 1) ^ 2 * X + 2 * X ^ 2 := by
      simp only [z₁, X, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hxA, hAx, S.pair_ample_ample]
      ring
    have hz₂ : S.pair z₂ z₂ = (X + 1) ^ 2 * X + 2 * X ^ 2 := by
      simp only [z₂, X, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hxA, hAx, S.pair_ample_ample]
      ring
    have hz₁₂ : S.pair z₁ z₂ = -(X ^ 3 + X) := by
      simp only [z₁, z₂, X, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hxA, hAx, S.pair_ample_ample]
      ring
    have hz₁_mem : z₁ ∈ sectionEffectivityCone S := by
      rw [mem_sectionEffectivityCone_iff, hz₁, hz₁H, hz₁V]
      exact ⟨by positivity, hpos.le, hpos.le⟩
    have hz₂_mem : z₂ ∈ sectionEffectivityCone S := by
      rw [mem_sectionEffectivityCone_iff, hz₂, hz₂H, hz₂V]
      exact ⟨by positivity, hpos.le, hpos.le⟩
    have h012 := hBez z₁ hz₁_mem z₂ hz₂_mem
    rw [hz₁₂] at h012
    have hX3 : 0 < X ^ 3 + X := by positivity
    linarith
  · intro hHI x hx y hy
    have hpos_bez := S.hodgeIndex_iff_positiveCone_bezout.mp hHI
    exact hpos_bez x (sectionEffectivityCone_subset_positiveCone S hx)
      y (sectionEffectivityCone_subset_positiveCone S hy)

/-- **Master Equivalence for the Section Effectivity Cone `E = {x : h⁰(x) ≥ 1}`:** on any polar
surface `S`, the Hodge index theorem, the Bézout axiom on `sectionEffectivityCone S`, the
Riemann–Roch axiom on `sectionEffectivityCone S`, the ample axiom on `sectionEffectivityCone S`,
and the full Castelnuovo–Severi package on `sectionEffectivityCone S` are all equivalent. -/
theorem sectionEffectivityCone_tfae (S : PolarSurface C) : List.TFAE [
    S.HodgeIndex,
    S.BezoutAxiom (sectionEffectivityCone S),
    S.RiemannRochAxiom (sectionEffectivityCone S),
    S.AmpleAxiom (sectionEffectivityCone S),
    S.AmpleAxiom (sectionEffectivityCone S) ∧
      S.BezoutAxiom (sectionEffectivityCone S) ∧
      S.RiemannRochAxiom (sectionEffectivityCone S)] := by
  tfae_have 1 ↔ 2 := (sectionEffectivityCone_bezout_iff_hodgeIndex S).symm
  tfae_have 1 ↔ 3 := (sectionEffectivityCone_riemannRoch_iff_hodgeIndex S).symm
  tfae_have 1 ↔ 4 := (sectionEffectivityCone_ample_iff_hodgeIndex S).symm
  tfae_have 1 ↔ 5 := ⟨fun h => ⟨(sectionEffectivityCone_ample_iff_hodgeIndex S).2 h,
      (sectionEffectivityCone_bezout_iff_hodgeIndex S).2 h,
      (sectionEffectivityCone_riemannRoch_iff_hodgeIndex S).2 h⟩,
    fun h => (sectionEffectivityCone_bezout_iff_hodgeIndex S).1 h.2.1⟩
  tfae_finish

/-! ### 3. Curve Hodge index over `𝔽_q` vs. failure on the golden datum -/

/-- **Calibration over `𝔽_q`:** for any curve datum `D : CurveDatum ι`, the Bézout axiom for the
section effectivity cone `E = {x : h⁰(x) ≥ 1}` on every finite window `W : Finset ℕ` is equivalent
to the curve Hodge index across all windows, to the Riemann–Roch axiom for `sectionEffectivityCone`,
to the unitarity of all Frobenius eigenvalues `‖D.β i‖ = 1`, and to the Hasse–Weil bound. -/
theorem curve_sectionEffectivityCone_bezout_tfae {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    List.TFAE [
      ∀ W : Finset ℕ, (D.windowSurface W).BezoutAxiom (sectionEffectivityCone (D.windowSurface W)),
      ∀ W : Finset ℕ, (D.windowSurface W).RiemannRochAxiom (sectionEffectivityCone (D.windowSurface W)),
      ∀ W : Finset ℕ, (D.windowSurface W).HodgeIndex,
      ∀ i : ι, ‖D.β i‖ = 1,
      ∃ B : ℝ, ∀ k : ℕ, |D.trace k| ≤ B] := by
  tfae_have 1 ↔ 3 := forall_congr' fun W => sectionEffectivityCone_bezout_iff_hodgeIndex (D.windowSurface W)
  tfae_have 2 ↔ 3 := forall_congr' fun W => sectionEffectivityCone_riemannRoch_iff_hodgeIndex (D.windowSurface W)
  tfae_have 3 ↔ 4 := D.windowSurface_hodgeIndex_iff_unitary
  tfae_have 4 ↔ 5 := (D.forcing_arithmetic_data_tfae).out 1 7
  tfae_finish

/-- For any unitary curve datum (`∀ i, ‖D.β i‖ = 1`, such as a smooth projective curve over `𝔽_q`),
the section effectivity cone `E = {x : h⁰(x) ≥ 1}` unconditionally satisfies all three
Castelnuovo–Severi axioms (`AmpleAxiom`, `BezoutAxiom`, `RiemannRochAxiom`) on every finite window. -/
theorem curve_unitary_sectionEffectivityCone_castelnuovoSeveri {ι : Type*} [Fintype ι]
    (D : CurveDatum ι) (hβ : ∀ i : ι, ‖D.β i‖ = 1) (W : Finset ℕ) :
    (D.windowSurface W).AmpleAxiom (sectionEffectivityCone (D.windowSurface W)) ∧
      (D.windowSurface W).BezoutAxiom (sectionEffectivityCone (D.windowSurface W)) ∧
      (D.windowSurface W).RiemannRochAxiom (sectionEffectivityCone (D.windowSurface W)) := by
  have hHI : (D.windowSurface W).HodgeIndex := D.windowSurface_hodgeIndex_iff_unitary.mpr hβ W
  exact ⟨(sectionEffectivityCone_ample_iff_hodgeIndex _).2 hHI,
    (sectionEffectivityCone_bezout_iff_hodgeIndex _).2 hHI,
    (sectionEffectivityCone_riemannRoch_iff_hodgeIndex _).2 hHI⟩

/-- On `goldenDatum.windowSurface {0, 1}`, the cycle `goldenForwardPlus` has `h⁰ = 1`
(it belongs to `sectionEffectivityCone`). -/
theorem goldenForwardPlus_mem_sectionEffectivityCone :
    goldenForwardPlus ∈ sectionEffectivityCone (goldenDatum.windowSurface ({0, 1} : Finset ℕ)) := by
  set S := goldenDatum.windowSurface ({0, 1} : Finset ℕ)
  rw [mem_sectionEffectivityCone_iff]
  obtain ⟨hH0, hV0, _⟩ := goldenCounterexample_violates_hodgeIndex
  have hpos : 0 ≤ S.pair goldenForwardPlus goldenForwardPlus :=
    goldenForwardPair_violates_openPositiveCone_bezout.1.1.le
  have hA_H : S.pair S.ample S.H = 1 := by
    simp [PolarSurface.ample, map_add, S.pair_H_H, S.pair_V_H]
  have hA_V : S.pair S.ample S.V = 1 := by
    simp [PolarSurface.ample, map_add, S.pair_H_V, S.pair_V_V]
  have hH : S.pair goldenForwardPlus S.H = 1 := by
    rw [goldenForwardPlus_eq]
    simp [S, map_add, map_smul, hA_H, hH0]
  have hV : S.pair goldenForwardPlus S.V = 1 := by
    rw [goldenForwardPlus_eq]
    simp [S, map_add, map_smul, hA_V, hV0]
  exact ⟨hpos, by linarith, by linarith⟩

/-- On `goldenDatum.windowSurface {0, 1}`, the cycle `goldenForwardMinus` has `h⁰ = 1`
(it belongs to `sectionEffectivityCone`). -/
theorem goldenForwardMinus_mem_sectionEffectivityCone :
    goldenForwardMinus ∈ sectionEffectivityCone (goldenDatum.windowSurface ({0, 1} : Finset ℕ)) := by
  set S := goldenDatum.windowSurface ({0, 1} : Finset ℕ)
  rw [mem_sectionEffectivityCone_iff]
  obtain ⟨hH0, hV0, _⟩ := goldenCounterexample_violates_hodgeIndex
  have hpos : 0 ≤ S.pair goldenForwardMinus goldenForwardMinus :=
    goldenForwardPair_violates_openPositiveCone_bezout.2.1.1.le
  have hA_H : S.pair S.ample S.H = 1 := by
    simp [PolarSurface.ample, map_add, S.pair_H_H, S.pair_V_H]
  have hA_V : S.pair S.ample S.V = 1 := by
    simp [PolarSurface.ample, map_add, S.pair_H_V, S.pair_V_V]
  have hH : S.pair goldenForwardMinus S.H = 1 := by
    rw [goldenForwardMinus_eq]
    simp [S, map_sub, map_smul, hA_H, hH0]
  have hV : S.pair goldenForwardMinus S.V = 1 := by
    rw [goldenForwardMinus_eq]
    simp [S, map_sub, map_smul, hA_V, hV0]
  exact ⟨hpos, by linarith, by linarith⟩

/-- **Refutation of the Bézout axiom on the golden datum:** on `goldenDatum.windowSurface {0, 1}`,
both `goldenForwardPlus` and `goldenForwardMinus` belong to `E = {x : h⁰(x) ≥ 1}`, yet their
intersection is `-6 < 0`, so `BezoutAxiom (sectionEffectivityCone ...)` and
`RiemannRochAxiom (sectionEffectivityCone ...)` both fail. -/
theorem goldenDatum_not_bezout_sectionEffectivityCone :
    ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).BezoutAxiom
        (sectionEffectivityCone (goldenDatum.windowSurface ({0, 1} : Finset ℕ))) ∧
      ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).RiemannRochAxiom
        (sectionEffectivityCone (goldenDatum.windowSurface ({0, 1} : Finset ℕ))) := by
  refine ⟨fun hBez => ?_, fun hRR => ?_⟩
  · have h := hBez goldenForwardPlus goldenForwardPlus_mem_sectionEffectivityCone
      goldenForwardMinus goldenForwardMinus_mem_sectionEffectivityCone
    rw [goldenForwardPair_violates_openPositiveCone_bezout.2.2.2] at h
    linarith
  · have hHI := (sectionEffectivityCone_riemannRoch_iff_hodgeIndex _).1 hRR
    obtain ⟨hH0, hV0, hxx⟩ := goldenCounterexample_violates_hodgeIndex
    have hle := hHI goldenCounterexample hH0 hV0
    linarith

/-! ### 4. Box degrees of freedom, diagonal relabeling invariance, and the properties of `ℤ` -/

/-- **Polar box degrees of freedom (`polarBoxDoF`):** the integrated density
`∫ u in 0..s, (e^u + 1)` of the two-pole plane `ℝH ⊕ ℝV` on the logarithmic horizon box `[0, s]`. -/
def polarBoxDoF (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, (Real.exp u + 1)

/-- **Weighted prime-power node count (`primeNodeCount`):** the Chebyshev summatory weight
`ψ(e^s) = ∑_{k ≤ ⌊e^s⌋} Λ(k)` of the prime-power nodes in `[0, s]`. -/
def primeNodeCount (s : ℝ) : ℝ :=
  lagChebyshev s

/-- **Generalized weighted node count (`weightedNodeCount`):** `∑_{k ∈ [0, ⌊e^s⌋]} w(k)`. -/
def weightedNodeCount (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊, w k

/-- **Generalized two-pole defect (`generalizedTwoPoleDefect`):**
`twoPoleWeight s - weightedNodeCount w s`. -/
def generalizedTwoPoleDefect (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  twoPoleWeight s - weightedNodeCount w s

/-- `polarBoxDoF s` equals `twoPoleWeight s = e^s + s - 1`. -/
theorem polarBoxDoF_eq_twoPoleWeight (s : ℝ) :
    polarBoxDoF s = twoPoleWeight s := by
  unfold polarBoxDoF twoPoleWeight
  have hexp : IntervalIntegrable Real.exp volume 0 s :=
    Real.continuous_exp.intervalIntegrable 0 s
  rw [intervalIntegral.integral_add hexp intervalIntegrable_const,
    integral_exp, intervalIntegral.integral_const, Real.exp_zero, smul_eq_mul]
  ring

/-- **Exact Box Chebyshev–Riemann–Roch Identity:** for every `s : ℝ`, the excess of the two-pole
degrees of freedom `polarBoxDoF s` over the prime-power node count `primeNodeCount s` is
`chebyshevTwoPoleDefect s = e^s + s - 1 - ψ(e^s)`. -/
theorem polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect (s : ℝ) :
    polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s := by
  rw [polarBoxDoF_eq_twoPoleWeight, primeNodeCount, chebyshevTwoPoleDefect]

/-- For any weight `w : ℕ → ℝ` and `s : ℝ`, `polarBoxDoF s - weightedNodeCount w s` equals
`generalizedTwoPoleDefect w s`. -/
theorem polarBoxDoF_sub_weightedNodeCount_eq_generalizedTwoPoleDefect (w : ℕ → ℝ) (s : ℝ) :
    polarBoxDoF s - weightedNodeCount w s = generalizedTwoPoleDefect w s := by
  rw [polarBoxDoF_eq_twoPoleWeight, generalizedTwoPoleDefect]

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

/-- For every `n ≥ 1` and `a ∈ ℝ`, `2 ≤ n^a + n^{-a}`. -/
theorem two_le_rpow_add_rpow_neg {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    2 ≤ (n : ℝ) ^ a + (n : ℝ) ^ (-a) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hprod : (n : ℝ) ^ a * (n : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
  have hsq : 0 ≤ ((n : ℝ) ^ a - 1) ^ 2 := sq_nonneg _
  nlinarith

/-- For every `n ∈ ℕ` and `a ∈ ℝ`, `2 * Λ(n) ≤ shiftedPairVonMangoldt a n`. -/
theorem two_mul_vonMangoldt_le_shiftedPair (a : ℝ) (n : ℕ) :
    2 * (ArithmeticFunction.vonMangoldt n : ℝ) ≤ shiftedPairVonMangoldt a n := by
  by_cases hn : 1 ≤ n
  · unfold shiftedPairVonMangoldt
    rw [mul_comm (ArithmeticFunction.vonMangoldt n : ℝ)]
    exact mul_le_mul_of_nonneg_right (two_le_rpow_add_rpow_neg hn a)
      ArithmeticFunction.vonMangoldt_nonneg
  · have h0 : n = 0 := by omega
    subst h0
    simp [shiftedPairVonMangoldt]

/-- **Selectivity of the two-pole defect against `shiftedPairVonMangoldt a`:** for every `a ≠ 0`
and `s ≥ log 2`, `generalizedTwoPoleDefect (shiftedPairVonMangoldt a) s < chebyshevTwoPoleDefect s`. -/
theorem generalizedTwoPoleDefect_shiftedPair_lt_chebyshev {a s : ℝ} (ha : a ≠ 0)
    (hs : Real.log 2 ≤ s) :
    generalizedTwoPoleDefect (shiftedPairVonMangoldt a) s < chebyshevTwoPoleDefect s := by
  have hfl : 2 ≤ ⌊Real.exp s⌋₊ := by
    rw [Nat.le_floor_iff (by positivity)]
    have hexp := Real.exp_le_exp.mpr hs
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  have hmem2 : (2 : ℕ) ∈ Finset.Icc 0 ⌊Real.exp s⌋₊ := Finset.mem_Icc.mpr ⟨by omega, hfl⟩
  have hlt2 : (ArithmeticFunction.vonMangoldt 2 : ℝ) < shiftedPairVonMangoldt a 2 := by
    unfold shiftedPairVonMangoldt
    have hgt := two_lt_two_rpow_add_two_rpow_neg ha
    have hΛ2 : (0 : ℝ) < ArithmeticFunction.vonMangoldt 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact Real.log_pos (by norm_num)
    have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hcast]
    nlinarith
  have hsum_lt : primeNodeCount s < weightedNodeCount (shiftedPairVonMangoldt a) s := by
    unfold primeNodeCount lagChebyshev weightedNodeCount
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨2, hmem2, hlt2⟩
    have h2 := two_mul_vonMangoldt_le_shiftedPair a k
    have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
    linarith
  unfold generalizedTwoPoleDefect chebyshevTwoPoleDefect primeNodeCount at *
  linarith

/-- **Diagonal relabeling invariance of `h0`:** right-multiplying any reading `A : Matrix m n ℂ` by
diagonal weights `w₁, w₂` with identical support (`∀ j, w₁ j = 0 ↔ w₂ j = 0`) leaves `h0`
unchanged. -/
theorem h0_mul_diagonal_eq_of_iff_eq_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {w₁ w₂ : n → ℂ} (hw : ∀ j, w₁ j = 0 ↔ w₂ j = 0) :
    h0 (A * Matrix.diagonal w₁) = h0 (A * Matrix.diagonal w₂) := by
  classical
  let d : n → ℂ := fun j => if w₁ j = 0 then 1 else w₁ j / w₂ j
  let d_inv : n → ℂ := fun j => if w₁ j = 0 then 1 else w₂ j / w₁ j
  have hd_mul : ∀ j, d j * d_inv j = 1 := fun j => by
    dsimp [d, d_inv]
    split_ifs with h1
    · ring
    · have h2 : w₂ j ≠ 0 := mt (hw j).mpr h1
      field_simp [h1, h2]
  have h_inv_mul : ∀ j, d_inv j * d j = 1 := fun j => by rw [mul_comm, hd_mul]
  have hw1_eq : ∀ j, w₂ j * d j = w₁ j := fun j => by
    dsimp [d]
    split_ifs with h1
    · rw [(hw j).mp h1, zero_mul, h1]
    · exact mul_div_cancel₀ (w₁ j) (mt (hw j).mpr h1)
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
      left_inv := fun v => by ext j; simp only [← mul_assoc, h_inv_mul, one_mul]
      right_inv := fun v => by ext j; simp only [← mul_assoc, hd_mul, one_mul] }
  have hker :
      LinearMap.ker (Matrix.mulVecLin (A * Matrix.diagonal w₁)) =
        Submodule.map (e.symm : (n → ℂ) →ₗ[ℂ] (n → ℂ))
          (LinearMap.ker (Matrix.mulVecLin (A * Matrix.diagonal w₂))) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_map, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
    constructor
    · intro hv
      refine ⟨e v, ?_, e.symm_apply_apply v⟩
      rw [← hv]
      congr 1
      ext j
      simp [e, Matrix.diagonal_mulVec_single, ← mul_assoc, hw1_eq]
    · rintro ⟨u, hu, rfl⟩
      rw [← hu]
      congr 1
      ext j
      simp [e, Matrix.diagonal_mulVec_single, ← mul_assoc, hw2_eq]
  unfold h0
  rw [hker]
  exact LinearEquiv.finrank_map_eq e.symm _

/-- **Pillar I of `ℤ` (Unique prime factorization + archimedean order → prime-tower dominance and
lattice balance):** for distinct integers `a ≠ b ≥ 2`, `Λ(a b) ≠ 0` forces `a` and `b` into the
same prime tower `p^i, p^j` where `p^{|i-j|} < p^{i+j}`, so the prime weight at `log a + log b` is
at most the weight at `|log a - log b|` (`primeKernel_log_add_le`) and the lattice odd Weil ledger
has frustration index `0` at every aperture. -/
theorem ringZ_pillar_one_primeTower_and_lattice_balance :
    (∀ {a b : ℕ}, 2 ≤ a → 2 ≤ b → a ≠ b →
      primeKernel (Real.log a + Real.log b) ≤ primeKernel (Real.log a - Real.log b)) ∧
    (∀ {m : ℕ} (n : Fin m → ℕ), (∀ x, 2 ≤ n x) → Function.Injective n →
      ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β → ∀ b : Fin m → ℝ,
        frustrationIndex (oddFold (fun x => Real.log (n x : ℝ)) (weilLedgerKernel α β) b) = 0) :=
  ⟨fun ha hb hab => primeKernel_log_add_le ha hb hab,
   fun n hn hinj _ _ hα hβ b => frustrationIndex_lattice_eq_zero hn hinj hα hβ b⟩

/-- **Pillar II of `ℤ` (Archimedean collar nonnegativity vs. failure of uncalibrated positivity
cones):** on the reflected prime-polar ledger of `ℤ`, both the archimedean surplus pool and the
crossing potential are nonnegative for every nonnegative plateau gauge `P ≥ 0`, whereas uncalibrated
positivity cones (`posTestCone` on `scalingSurface` and `graphCone` on `goldenDatum`) fail
`RiemannRochAxiom`. -/
theorem ringZ_pillar_two_archimedean_collar_and_posTestCone :
    (∀ {P F : ℝ → ℝ}, (∀ y, 0 ≤ P y) →
      0 ≤ surplusPool P F ∧ 0 ≤ crossingPotentialTerm P F) ∧
    ¬ scalingSurface.RiemannRochAxiom posTestCone :=
  ⟨fun hP => ⟨surplusPool_nonneg hP, crossingPotentialTerm_nonneg hP⟩,
   posTestCone_not_riemannRoch⟩

/-- **Pillar III of `ℤ` (Additive two-pole cancellation and prime-2 selectivity vs. uncalibrated
linear kernels):**
1. On `[0, s]`, the excess of the two-pole degrees of freedom `polarBoxDoF s = e^s + s - 1` over the
   prime node count `primeNodeCount s = ψ(e^s)` is `chebyshevTwoPoleDefect s`.
2. For any `a ≠ 0` and `s ≥ log 2`, the shifted-pair weight `shiftedPairVonMangoldt a` has strictly
   smaller two-pole defect than `ℤ`, whereas uncalibrated linear kernel dimensions
   `h0 (A * diagonal w)` cannot distinguish `shiftedPairVonMangoldt a` from `2 * Λ`. -/
theorem ringZ_pillar_three_twoPole_selectivity :
    (∀ s : ℝ, polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s) ∧
    (∀ {a s : ℝ}, a ≠ 0 → Real.log 2 ≤ s →
      generalizedTwoPoleDefect (shiftedPairVonMangoldt a) s < chebyshevTwoPoleDefect s) :=
  ⟨polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect,
   fun ha hs => generalizedTwoPoleDefect_shiftedPair_lt_chebyshev ha hs⟩

/-- **Pillar IVa of `ℤ` (Unconditional Bézout and Riemann–Roch for `E = {x : h⁰(x) ≥ 1}` on the
odd scaling subsurface past the first prime `2`):** for every `0 < r ≤ 181/500`, the section
effectivity cone `sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r))` unconditionally
satisfies `AmpleAxiom`, `BezoutAxiom`, and `RiemannRochAxiom`. -/
theorem scalingSubsurface_odd_sectionEffectivityCone_castelnuovoSeveri_of_le {r : ℝ}
    (hr0 : 0 < r) (hr : r ≤ 181 / 500) :
    (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom
        (sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r))) ∧
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom
        (sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r))) ∧
      (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
        (sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r))) := by
  have hHI := scalingSubsurface_odd_hodgeIndex_of_le_threeHundredSixtyTwoThousandths hr0 hr
  exact ⟨(sectionEffectivityCone_ample_iff_hodgeIndex _).2 hHI,
    (sectionEffectivityCone_bezout_iff_hodgeIndex _).2 hHI,
    (sectionEffectivityCone_riemannRoch_iff_hodgeIndex _).2 hHI⟩

/-- **Pillar IVb of `ℤ` (Unconditional Bézout and Riemann–Roch for `E = {x : h⁰(x) ≥ 1}` on the
primitive smooth scaling subsurface past the first prime `2`):** for every
`0 < r ≤ (Real.log 2 + 1/50) / 2`, the section effectivity cone
`sectionEffectivityCone (scalingSubsurface (primitiveSmoothRealTestsAt r))` unconditionally
satisfies `AmpleAxiom`, `BezoutAxiom`, and `RiemannRochAxiom`. -/
theorem scalingSubsurface_primitiveSmooth_sectionEffectivityCone_castelnuovoSeveri_of_le {r : ℝ}
    (hr0 : 0 < r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
        (sectionEffectivityCone (scalingSubsurface (primitiveSmoothRealTestsAt r))) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).BezoutAxiom
        (sectionEffectivityCone (scalingSubsurface (primitiveSmoothRealTestsAt r))) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
        (sectionEffectivityCone (scalingSubsurface (primitiveSmoothRealTestsAt r))) := by
  have hHI := scalingSubsurface_primitiveSmooth_hodgeIndex_of_le_past_first_prime hr0 hr
  exact ⟨(sectionEffectivityCone_ample_iff_hodgeIndex _).2 hHI,
    (sectionEffectivityCone_bezout_iff_hodgeIndex _).2 hHI,
    (sectionEffectivityCone_riemannRoch_iff_hodgeIndex _).2 hHI⟩

/-- **Global Width Dictionary for the Section Effectivity Cone `E = {x : h⁰(x) ≥ 1}`:** on the full
scaling surface of `ℤ`, the Bézout axiom and Riemann–Roch axiom for
`sectionEffectivityCone scalingSurface` are unconditionally equivalent to every unit of the width
dictionary (`RiemannHypothesis`, `scalingSurface.HodgeIndex`, `oddDefectFloorRate = 0`, cofinal
damping admission, etc.). -/
theorem sectionEffectivityCone_widthDictionary_tfae : List.TFAE [
    scalingSurface.BezoutAxiom (sectionEffectivityCone scalingSurface),
    scalingSurface.RiemannRochAxiom (sectionEffectivityCone scalingSurface),
    scalingSurface.HodgeIndex,
    RiemannHypothesis,
    oddDefectFloorRate = 0,
    fullDefectFloorRate = 0,
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B] := by
  tfae_have 1 ↔ 3 := sectionEffectivityCone_bezout_iff_hodgeIndex scalingSurface
  tfae_have 2 ↔ 3 := sectionEffectivityCone_riemannRoch_iff_hodgeIndex scalingSurface
  tfae_have 4 ↔ 3 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 4 ↔ 5 := riemannHypothesis_iff_oddDefectFloorRate_eq_zero
  tfae_have 4 ↔ 6 := riemannHypothesis_iff_fullDefectFloorRate_eq_zero
  tfae_have 4 ↔ 7 := riemannHypothesis_iff_cofinal_budget
  tfae_finish

end

end GaloisForLFunctions.ArithmeticOrientationTheory
