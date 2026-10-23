import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HodgeIndexFromEffectivity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity

/-!
# Bézout Effectivity, Canonical Surface Riemann–Roch, and the Beurling Obstruction

In Castelnuovo–Severi and Weil's proof of the Riemann Hypothesis for curves over finite fields, the
Hodge index inequality is forced by the interaction of two geometric inputs on a surface:

1. **Riemann–Roch / Serre duality**: a class of positive self-intersection (or sufficiently large
   Euler characteristic `χ(D) = χ(𝒪) + ½(D² − D·K)`) moves in an effective linear system, either
   directly or after canonical reflection `K − D`;
2. **Bézout positivity**: two effective classes without common fixed components of negative square
   intersect nonnegatively (`D₁ · D₂ ≥ 0`).

This file proves four unconditional results clarifying why positive Euler data alone cannot force
the Hodge index on the Frobenius span surface and isolating the exact arithmetic structure required:

* **Bézout positivity replaces the ample kernel axiom** (`hodgeIndex_of_riemannRoch_of_bezout`,
  `exists_bezout_effectivity_iff_hodgeIndex`): on any polar surface `S`, the Hodge index holds if
  and only if there exists a subset `E` satisfying `RiemannRochAxiom E` (`x² > 0 → x ∈ E ∨ −x ∈ E`)
  and `BezoutAxiom E` (`x, y ∈ E → x · y ≥ 0`), with no reference to the ample class. Conversely,
  under `HodgeIndex`, the open positive cone `{x | x² > 0 ∧ x · A > 0}` has strictly positive
  pairwise intersection (`pair_pos_of_openPositiveCone`), and the closed positive cone satisfies
  `BezoutAxiom` (`positiveCone_bezout`).
* **Canonical surface Riemann–Roch + Serre duality + Bézout** (`hodgeIndex_of_surfaceRiemannRoch`,
  `exists_surfaceRiemannRoch_iff_hodgeIndex`): if a polar surface carries a canonical class `K`, an
  arithmetic genus constant `χ₀`, and an effective cone `E` such that
  `χ₀ + ½(x² − x·K) > 0 → x ∈ E ∨ K − x ∈ E`, `e · A ≥ 0` on `E` (with no kernel condition at
  degree `0`), and `e₁ · e₂ ≥ 0` for `e₁, e₂ ∈ E` with `e₁² > 0, e₂² > 0`, then `S.HodgeIndex`
  holds.
* **The Frobenius span polar surface and the failure of the graph cone** (`CurveDatum.windowSurface`,
  `graphCone_ample`, `graphCone_bezout`, `graphCone_not_riemannRoch`,
  `goldenDatum_graphCone_ample_and_bezout`): for any `CurveDatum D` and finite window `S`, the
  Frobenius span cycle space `ℝ × ℝ × (ℕ → ℝ)` is a `PolarSurface` whose defect is `D.spanDefect S`.
  The positive Frobenius graph cone `{aH + bV + ∑_{k ∈ S} c_k Γ_k | a, b, c_k ≥ 0}` always satisfies
  `AmpleAxiom` and, whenever `D.pointCount j ≥ 0` (in particular for the golden fake curve
  `goldenDatum`), also satisfies `BezoutAxiom`; yet it unconditionally fails `RiemannRochAxiom` once
  `S` is nonempty, and `goldenDatum` admits the explicit integer primitive class
  `−H + 3V + 2Γ₀ − Γ₁` with `x · H = x · V = 0` and `x² = 2 > 0`.
* **The cohomological sign and subshift obstruction** (`toeplitz_range_one`,
  `toeplitz_range_one_le_of_unitary`, `exists_trace_neg_of_unitary`,
  `not_hodgeIndex_of_subshift_bound`): the constant-weight Toeplitz form on `{0, …, n − 1}`
  satisfies the exact identity
  `T_n(1) = n · (2g) + 2 ∑_{m < n} ∑_{j < m} Re Tr(F^{m − j})`,
  while unitarity `|β_i| = 1` with `β_i ≠ 1` bounds `T_n(1) ≤ ∑_i 4 / |β_i − 1|²` uniformly in `n`.
  Hence any positive-genus unitary datum with `1 ∉ Spec(F)` must have `Re Tr(F^k) < 0` (i.e.
  `N_k > q^k + 1`) for some `k ≥ 1`. In particular, no subshift-difference or nonnegative-matrix
  Beurling system satisfying `N_k ≤ q^k + 1` for all `k ≥ 1` can satisfy the Hodge index.
-/

open Complex Finset
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Bézout positivity and the Hodge index on a polar surface -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

theorem hodgeIndex_iff_ampleHodgeIndex : S.HodgeIndex ↔ S.AmpleHodgeIndex :=
  S.hodgeIndex_iff_castelnuovoSeveri.trans S.ampleHodgeIndex_iff_castelnuovoSeveri.symm

theorem hodgeIndex_iff_defect_nonneg : S.HodgeIndex ↔ ∀ x, 0 ≤ S.defect x x :=
  S.hodgeIndex_iff_castelnuovoSeveri.trans S.castelnuovoSeveri_iff_defect_nonneg

/-- **Bézout axiom**: any two effective classes intersect nonnegatively. -/
def BezoutAxiom (E : Set C) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, 0 ≤ S.pair x y

/-- The open forward light cone `{x | x² > 0 ∧ x · A > 0}` of a polar surface. -/
def openPositiveCone : Set C :=
  {x | 0 < S.pair x x ∧ 0 < S.pair x S.ample}

/-- Under the Hodge index, any two classes in the open positive cone have strictly positive
intersection. -/
theorem pair_pos_of_openPositiveCone (hH : S.HodgeIndex) {x y : C}
    (hx : x ∈ S.openPositiveCone) (hy : y ∈ S.openPositiveCone) :
    0 < S.pair x y := by
  have hA : S.AmpleHodgeIndex := S.hodgeIndex_iff_ampleHodgeIndex.mp hH
  rcases hx with ⟨hxx, hxA⟩
  rcases hy with ⟨hyy, hyA⟩
  let u : C := (2 : ℝ) • x - (S.pair x S.ample) • S.ample
  let v : C := (2 : ℝ) • y - (S.pair y S.ample) • S.ample
  have hu : S.pair u S.ample = 0 := by
    simp only [u, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample]
    ring
  have hv : S.pair v S.ample = 0 := by
    simp only [v, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample]
    ring
  have hcs : S.pair u v ^ 2 ≤ S.pair u u * S.pair v v :=
    S.pair_sq_le_of_ampleHodgeIndex hA hu hv
  have hu_le : S.pair u u ≤ 0 := hA u hu
  have hv_le : S.pair v v ≤ 0 := hA v hv
  have huu : S.pair u u = 4 * S.pair x x - 2 * S.pair x S.ample ^ 2 := by
    simp only [u, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample, S.pair_comm S.ample x]
    ring
  have hvv : S.pair v v = 4 * S.pair y y - 2 * S.pair y S.ample ^ 2 := by
    simp only [v, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample, S.pair_comm S.ample y]
    ring
  have huv : S.pair u v = 4 * S.pair x y - 2 * S.pair x S.ample * S.pair y S.ample := by
    simp only [u, v, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample, S.pair_comm S.ample y]
    ring
  have h1 : 0 < 2 * S.pair x S.ample ^ 2 + S.pair u u := by linarith
  have h2 : 0 < 2 * S.pair y S.ample ^ 2 + S.pair v v := by linarith
  have h3 : 0 < 2 * S.pair x S.ample ^ 2 := by positivity
  have hprod : S.pair u u * S.pair v v < (2 * S.pair x S.ample * S.pair y S.ample) ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt h1) (neg_nonneg.mpr hv_le), mul_pos h3 h2]
  have hsq : (4 * S.pair x y - 2 * S.pair x S.ample * S.pair y S.ample) ^ 2 <
      (2 * S.pair x S.ample * S.pair y S.ample) ^ 2 := by
    rw [← huv]
    exact lt_of_le_of_lt hcs hprod
  nlinarith [sq_nonneg (S.pair x y), mul_pos hxA hyA]

/-- Under the Hodge index, the closed positive cone `{x | x² ≥ 0 ∧ x · A ≥ 0}` satisfies the
Bézout axiom. -/
theorem positiveCone_bezout (hH : S.HodgeIndex) : S.BezoutAxiom S.positiveCone := by
  have hA : S.AmpleHodgeIndex := S.hodgeIndex_iff_ampleHodgeIndex.mp hH
  rintro x ⟨hxx, hxA⟩ y ⟨hyy, hyA⟩
  let u : C := (2 : ℝ) • x - (S.pair x S.ample) • S.ample
  let v : C := (2 : ℝ) • y - (S.pair y S.ample) • S.ample
  have hu : S.pair u S.ample = 0 := by
    simp only [u, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample]
    ring
  have hv : S.pair v S.ample = 0 := by
    simp only [v, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample]
    ring
  have hcs : S.pair u v ^ 2 ≤ S.pair u u * S.pair v v :=
    S.pair_sq_le_of_ampleHodgeIndex hA hu hv
  have hu_le : S.pair u u ≤ 0 := hA u hu
  have hv_le : S.pair v v ≤ 0 := hA v hv
  have huu : S.pair u u = 4 * S.pair x x - 2 * S.pair x S.ample ^ 2 := by
    simp only [u, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample, S.pair_comm S.ample x]
    ring
  have hvv : S.pair v v = 4 * S.pair y y - 2 * S.pair y S.ample ^ 2 := by
    simp only [v, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample, S.pair_comm S.ample y]
    ring
  have huv : S.pair u v = 4 * S.pair x y - 2 * S.pair x S.ample * S.pair y S.ample := by
    simp only [u, v, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_ample_ample, S.pair_comm S.ample y]
    ring
  have h1 : 0 ≤ 2 * S.pair x S.ample ^ 2 + S.pair u u := by linarith
  have h2 : 0 ≤ 2 * S.pair y S.ample ^ 2 + S.pair v v := by linarith
  have h3 : 0 ≤ 2 * S.pair x S.ample ^ 2 := by positivity
  have hprod : S.pair u u * S.pair v v ≤ (2 * S.pair x S.ample * S.pair y S.ample) ^ 2 := by
    nlinarith [mul_nonneg h1 (neg_nonneg.mpr hv_le), mul_nonneg h3 h2]
  have hsq : S.pair u v ^ 2 ≤ (2 * S.pair x S.ample * S.pair y S.ample) ^ 2 :=
    le_trans hcs hprod
  have hM : 0 ≤ 2 * S.pair x S.ample * S.pair y S.ample := by positivity
  by_contra hxy
  push Not at hxy
  have huv_lt : S.pair u v < -(2 * S.pair x S.ample * S.pair y S.ample) := by linarith
  nlinarith [mul_pos (neg_pos.mpr (lt_of_lt_of_le huv_lt (by linarith)))
    (sub_pos.mpr huv_lt)]

/-- Under `RiemannRochAxiom E` and `BezoutAxiom E`, any class `z` of positive square that pairs
negatively with an effective class `u ∈ E` must have `−z ∈ E`. -/
theorem neg_mem_of_pos_of_pair_neg {E : Set C} (hRR : S.RiemannRochAxiom E)
    (hB : S.BezoutAxiom E) {u z : C} (hu : u ∈ E) (hz : 0 < S.pair z z)
    (huz : S.pair z u < 0) : -z ∈ E := by
  rcases hRR z hz with hzE | hnzE
  · exfalso
    linarith [hB z hzE u hu]
  · exact hnzE

/-- Two orthogonal classes of strictly positive self-intersection cannot coexist with
`RiemannRochAxiom E` and `BezoutAxiom E`. -/
theorem false_of_orth_pos_of_riemannRoch_of_bezout {E : Set C} (hRR : S.RiemannRochAxiom E)
    (hB : S.BezoutAxiom E) {u w : C} (hu : u ∈ E) (hU : 0 < S.pair u u)
    (hW : 0 < S.pair w w) (huw : S.pair u w = 0) : False := by
  let U : ℝ := S.pair u u
  let W : ℝ := S.pair w w
  let z₁ : C := (U + W) • w - W • u
  let z₂ : C := -(U + W) • w - W • u
  have hwu : S.pair w u = 0 := by rw [S.pair_comm, huw]
  have hz₁ : S.pair z₁ z₁ = (U + W) ^ 2 * W + W ^ 2 * U := by
    simp only [z₁, U, W, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      huw, hwu]
    ring
  have hz₂ : S.pair z₂ z₂ = (U + W) ^ 2 * W + W ^ 2 * U := by
    simp only [z₂, U, W, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      huw, hwu]
    ring
  have hz₁u : S.pair z₁ u = -(W * U) := by
    simp only [z₁, U, W, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hwu]
    ring
  have hz₂u : S.pair z₂ u = -(W * U) := by
    simp only [z₂, U, W, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hwu]
    ring
  have hpos : 0 < (U + W) ^ 2 * W + W ^ 2 * U := by positivity
  have hneg : -(W * U) < 0 := neg_lt_zero.mpr (mul_pos hW hU)
  have hnz₁ : -z₁ ∈ E :=
    S.neg_mem_of_pos_of_pair_neg hRR hB hu (hz₁ ▸ hpos) (hz₁u ▸ hneg)
  have hnz₂ : -z₂ ∈ E :=
    S.neg_mem_of_pos_of_pair_neg hRR hB hu (hz₂ ▸ hpos) (hz₂u ▸ hneg)
  have hbez : 0 ≤ S.pair (-z₁) (-z₂) := hB (-z₁) hnz₁ (-z₂) hnz₂
  have hz₁₂ : S.pair (-z₁) (-z₂) = -(U ^ 2 * W + 2 * U * W ^ 2 + W ^ 3 - W ^ 2 * U) := by
    simp only [z₁, z₂, U, W, map_neg, map_sub, map_smul, LinearMap.neg_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, huw, hwu]
    ring
  have hlt : S.pair (-z₁) (-z₂) < 0 := by
    rw [hz₁₂]
    have : 0 < U ^ 2 * W + 2 * U * W ^ 2 + W ^ 3 - W ^ 2 * U := by
      calc 0 < U ^ 2 * W + U * W ^ 2 + W ^ 3 := by positivity
      _ = U ^ 2 * W + 2 * U * W ^ 2 + W ^ 3 - W ^ 2 * U := by ring
    linarith
  linarith

/-- **Hodge index from Riemann–Roch and Bézout**: if `E` satisfies `RiemannRochAxiom E` and
`BezoutAxiom E`, then `S` satisfies the Hodge index (with no ample-class hypothesis). -/
theorem hodgeIndex_of_riemannRoch_of_bezout {E : Set C} (hRR : S.RiemannRochAxiom E)
    (hB : S.BezoutAxiom E) : S.HodgeIndex := by
  rw [S.hodgeIndex_iff_no_positive_plane]
  rintro x y ⟨hx, hxy⟩
  let w : C := (S.pair x x) • y - (S.pair x y) • x
  have hww : S.pair w w = S.pair x x * (S.pair x x * S.pair y y - S.pair x y ^ 2) := by
    simp only [w, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_comm y x]
    ring
  have hw : 0 < S.pair w w := by
    rw [hww]
    exact mul_pos hx (sub_pos.mpr hxy)
  have hxw : S.pair x w = 0 := by
    simp only [w, map_sub, map_smul, smul_eq_mul, S.pair_comm x y]
    ring
  rcases hRR x hx with hxE | hnxE
  · exact S.false_of_orth_pos_of_riemannRoch_of_bezout hRR hB hxE hx hw hxw
  · have hu : 0 < S.pair (-x) (-x) := by
      simpa [map_neg, LinearMap.neg_apply] using hx
    have huw : S.pair (-x) w = 0 := by
      simp [hxw]
    exact S.false_of_orth_pos_of_riemannRoch_of_bezout hRR hB hnxE hu hw huw

/-- The Hodge index holds if and only if the polar surface admits an effectivity cone satisfying
the Riemann–Roch and Bézout axioms. -/
theorem exists_bezout_effectivity_iff_hodgeIndex :
    (∃ E : Set C, S.RiemannRochAxiom E ∧ S.BezoutAxiom E) ↔ S.HodgeIndex :=
  ⟨fun ⟨_, hRR, hB⟩ => S.hodgeIndex_of_riemannRoch_of_bezout hRR hB,
    fun hH => ⟨S.positiveCone, (S.positiveCone_axioms hH).1, S.positiveCone_bezout hH⟩⟩

/-! ### 2. Canonical surface Riemann–Roch, Serre duality, and Bézout -/

/-- **Canonical surface Riemann–Roch and Serre duality**: for canonical class `K : C` and
arithmetic Euler characteristic constant `χ₀ = χ(𝒪)`, any class `x` with positive Riemann–Roch
Euler characteristic `χ₀ + ½(x² − x·K) > 0` is effective either directly (`x ∈ E`) or after
canonical reflection (`K − x ∈ E`). -/
def SurfaceRiemannRochAxiom (K : C) (χ₀ : ℝ) (E : Set C) : Prop :=
  ∀ x : C, 0 < χ₀ + (S.pair x x - S.pair x K) / 2 → x ∈ E ∨ K - x ∈ E

/-- **Hodge index from canonical surface Riemann–Roch, fiber nefness, and Bézout**: if `E`
satisfies `SurfaceRiemannRochAxiom K χ₀ E`, every effective class pairs nonnegatively with `ample`
(with no kernel condition at degree `0`), and any two effective classes of strictly positive square
intersect nonnegatively, then `S.HodgeIndex` holds. -/
theorem hodgeIndex_of_surfaceRiemannRoch {K : C} {χ₀ : ℝ} {E : Set C}
    (hSRR : S.SurfaceRiemannRochAxiom K χ₀ E)
    (hNef : ∀ e ∈ E, 0 ≤ S.pair e S.ample)
    (hBez : ∀ e₁ ∈ E, ∀ e₂ ∈ E, 0 < S.pair e₁ e₁ → 0 < S.pair e₂ e₂ → 0 ≤ S.pair e₁ e₂) :
    S.HodgeIndex := by
  rw [S.hodgeIndex_iff_ampleHodgeIndex]
  intro x hxA
  by_contra hX_neg
  push Not at hX_neg
  let X : ℝ := S.pair x x
  have hX : 0 < X := hX_neg
  have hAx : S.pair S.ample x = 0 := by rw [S.pair_comm, hxA]
  let z₁ : C := (X + 1) • x + X • S.ample
  let z₂ : C := -(X + 1) • x + X • S.ample
  let Z : ℝ := (X + 1) ^ 2 * X + 2 * X ^ 2
  have hZ : 0 < Z := by positivity
  have hz₁A : S.pair z₁ S.ample = 2 * X := by
    simp only [z₁, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxA, S.pair_ample_ample]
    ring
  have hz₂A : S.pair z₂ S.ample = 2 * X := by
    simp only [z₂, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxA, S.pair_ample_ample]
    ring
  have hz₁z₁ : S.pair z₁ z₁ = Z := by
    simp only [z₁, Z, X, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxA, hAx, S.pair_ample_ample]
    ring
  have hz₂z₂ : S.pair z₂ z₂ = Z := by
    simp only [z₂, Z, X, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxA, hAx, S.pair_ample_ample]
    ring
  have hz₁z₂ : S.pair z₁ z₂ = -(X ^ 3 + X) := by
    simp only [z₁, z₂, X, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxA, hAx, S.pair_ample_ample]
    ring
  let m : ℝ := 1 + |S.pair K S.ample| / X +
    (|S.pair z₁ K| + |S.pair z₂ K| + 2 * |χ₀| + 1) / Z
  have hm_pos : 0 < m := by positivity
  have hm_ge_one : 1 ≤ m := by
    have : 0 ≤ |S.pair K S.ample| / X + (|S.pair z₁ K| + |S.pair z₂ K| + 2 * |χ₀| + 1) / Z := by
      positivity
    linarith
  have hmX : |S.pair K S.ample| < m * X := by
    have hdiv : |S.pair K S.ample| / X < m := by
      have : 0 ≤ (|S.pair z₁ K| + |S.pair z₂ K| + 2 * |χ₀| + 1) / Z := by positivity
      linarith
    exact (div_lt_iff₀ hX).mp hdiv
  have hmZ : |S.pair z₁ K| + |S.pair z₂ K| + 2 * |χ₀| + 1 < m * Z := by
    have hdiv : (|S.pair z₁ K| + |S.pair z₂ K| + 2 * |χ₀| + 1) / Z < m := by
      have : 0 ≤ |S.pair K S.ample| / X := by positivity
      linarith
    exact (div_lt_iff₀ hZ).mp hdiv
  have hKA_lt : S.pair K S.ample < 2 * m * X := by
    linarith [le_abs_self (S.pair K S.ample), mul_pos hm_pos hX]
  have hm₂Z : m * (|S.pair z₁ K| + |S.pair z₂ K| + 2 * |χ₀| + 1) < m ^ 2 * Z := by
    nlinarith [mul_lt_mul_of_pos_left hmZ hm_pos]
  have hrr₁ : 0 < χ₀ + (S.pair (m • z₁) (m • z₁) - S.pair (m • z₁) K) / 2 := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hz₁z₁]
    nlinarith [le_abs_self (S.pair z₁ K), abs_nonneg (S.pair z₂ K),
      neg_le_abs χ₀, abs_nonneg χ₀]
  have hrr₂ : 0 < χ₀ + (S.pair (m • z₂) (m • z₂) - S.pair (m • z₂) K) / 2 := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hz₂z₂]
    nlinarith [abs_nonneg (S.pair z₁ K), le_abs_self (S.pair z₂ K),
      neg_le_abs χ₀, abs_nonneg χ₀]
  have hmz₁E : m • z₁ ∈ E := by
    rcases hSRR (m • z₁) hrr₁ with h1 | h2
    · exact h1
    · exfalso
      have hnef := hNef (K - m • z₁) h2
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hz₁A] at hnef
      linarith
  have hmz₂E : m • z₂ ∈ E := by
    rcases hSRR (m • z₂) hrr₂ with h1 | h2
    · exact h1
    · exfalso
      have hnef := hNef (K - m • z₂) h2
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hz₂A] at hnef
      linarith
  have hsq₁ : 0 < S.pair (m • z₁) (m • z₁) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hz₁z₁]
    positivity
  have hsq₂ : 0 < S.pair (m • z₂) (m • z₂) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hz₂z₂]
    positivity
  have hbez := hBez (m • z₁) hmz₁E (m • z₂) hmz₂E hsq₁ hsq₂
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hz₁z₂] at hbez
  have hneg : m * (m * -(X ^ 3 + X)) < 0 := by
    have : 0 < m ^ 2 * (X ^ 3 + X) := by positivity
    linarith
  linarith

/-- The Hodge index holds if and only if the polar surface admits `(K, χ₀, E)` satisfying
`SurfaceRiemannRochAxiom K χ₀ E`, fiber nefness `e · A ≥ 0`, and Bézout positivity on classes of
positive square. -/
theorem exists_surfaceRiemannRoch_iff_hodgeIndex :
    (∃ (K : C) (χ₀ : ℝ) (E : Set C),
      S.SurfaceRiemannRochAxiom K χ₀ E ∧
      (∀ e ∈ E, 0 ≤ S.pair e S.ample) ∧
      (∀ e₁ ∈ E, ∀ e₂ ∈ E, 0 < S.pair e₁ e₁ → 0 < S.pair e₂ e₂ → 0 ≤ S.pair e₁ e₂)) ↔
    S.HodgeIndex := by
  constructor
  · rintro ⟨K, χ₀, E, hSRR, hNef, hBez⟩
    exact S.hodgeIndex_of_surfaceRiemannRoch hSRR hNef hBez
  · intro hH
    have hA : S.AmpleHodgeIndex := S.hodgeIndex_iff_ampleHodgeIndex.mp hH
    refine ⟨0, 0, S.openPositiveCone, ?_, ?_, ?_⟩
    · intro x hx
      simp only [map_zero, sub_zero, zero_add] at hx
      have hxx : 0 < S.pair x x := by linarith
      have hne : S.pair x S.ample ≠ 0 := fun h0 => by linarith [hA x h0]
      rcases lt_trichotomy (S.pair x S.ample) 0 with hlt | heq | hgt
      · right
        simp only [zero_sub, openPositiveCone, Set.mem_setOf_eq, map_neg, LinearMap.neg_apply,
          neg_neg]
        exact ⟨hxx, by linarith⟩
      · exact False.elim (hne heq)
      · left
        exact ⟨hxx, hgt⟩
    · intro e he
      exact le_of_lt he.2
    · intro e₁ he₁ e₂ he₂ _ _
      exact le_of_lt (S.pair_pos_of_openPositiveCone hH he₁ he₂)

end PolarSurface

/-! ### 3. The Frobenius span polar surface and the failure of the positive graph cone -/

/-- A cycle in the Frobenius span `aH + bV + ∑_{k ∈ S} d(k) Γ_k`. -/
abbrev SpanCycle := ℝ × ℝ × (ℕ → ℝ)

/-- The horizontal degree `d · H = ∑_{k ∈ S} d(k)` of a graph combination on `S`. -/
def windowB (S : Finset ℕ) (d : ℕ → ℝ) : ℝ :=
  ∑ k ∈ S, d k

/-- The positive Euler / Frobenius graph cone `{aH + bV + ∑_{k ∈ S} c_k Γ_k | a, b, c_k ≥ 0}`. -/
def graphCone (S : Finset ℕ) : Set SpanCycle :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ ∀ k ∈ S, 0 ≤ x.2.2 k}

theorem windowB_add (S : Finset ℕ) (d₁ d₂ : ℕ → ℝ) :
    windowB S (d₁ + d₂) = windowB S d₁ + windowB S d₂ :=
  Finset.sum_add_distrib

theorem windowB_smul (S : Finset ℕ) (c : ℝ) (d : ℕ → ℝ) :
    windowB S (c • d) = c * windowB S d := by
  simp only [windowB, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]

theorem windowB_zero (S : Finset ℕ) : windowB S 0 = 0 := by
  simp [windowB]

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The vertical degree `d · V = ∑_{k ∈ S} d(k) q^k` of a graph combination on `S`. -/
def windowA (S : Finset ℕ) (d : ℕ → ℝ) : ℝ :=
  ∑ k ∈ S, d k * D.q ^ k

/-- The graph-graph intersection `∑_{j, k ∈ S} d₁(j) d₂(k) (Γ_j · Γ_k)` on `S`. -/
def windowGraph (S : Finset ℕ) (d₁ d₂ : ℕ → ℝ) : ℝ :=
  ∑ j ∈ S, ∑ k ∈ S, d₁ j * d₂ k * D.graphPair j k

/-- The symmetric bilinear intersection form on `SpanCycle` over the finite window `S`. -/
def windowPairFun (S : Finset ℕ) (x y : SpanCycle) : ℝ :=
  x.1 * y.2.1 + x.2.1 * y.1 +
    x.1 * D.windowA S y.2.2 + y.1 * D.windowA S x.2.2 +
    x.2.1 * windowB S y.2.2 + y.2.1 * windowB S x.2.2 +
    D.windowGraph S x.2.2 y.2.2

theorem windowA_add (S : Finset ℕ) (d₁ d₂ : ℕ → ℝ) :
    D.windowA S (d₁ + d₂) = D.windowA S d₁ + D.windowA S d₂ := by
  simp only [windowA, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem windowA_smul (S : Finset ℕ) (c : ℝ) (d : ℕ → ℝ) :
    D.windowA S (c • d) = c * D.windowA S d := by
  simp only [windowA, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

theorem windowA_zero (S : Finset ℕ) : D.windowA S 0 = 0 := by
  simp [windowA]

theorem windowGraph_add_left (S : Finset ℕ) (d₁ d₂ d₃ : ℕ → ℝ) :
    D.windowGraph S (d₁ + d₂) d₃ = D.windowGraph S d₁ d₃ + D.windowGraph S d₂ d₃ := by
  simp only [windowGraph, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem windowGraph_smul_left (S : Finset ℕ) (c : ℝ) (d₁ d₂ : ℕ → ℝ) :
    D.windowGraph S (c • d₁) d₂ = c * D.windowGraph S d₁ d₂ := by
  simp only [windowGraph, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

theorem windowGraph_symm (S : Finset ℕ) (d₁ d₂ : ℕ → ℝ) :
    D.windowGraph S d₁ d₂ = D.windowGraph S d₂ d₁ := by
  simp only [windowGraph]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [D.graphPair_comm j k]
  ring

theorem windowGraph_zero_left (S : Finset ℕ) (d : ℕ → ℝ) :
    D.windowGraph S 0 d = 0 := by
  simp [windowGraph]

theorem windowGraph_zero_right (S : Finset ℕ) (d : ℕ → ℝ) :
    D.windowGraph S d 0 = 0 := by
  simp [windowGraph]

/-- The intersection pairing on `SpanCycle` over `S` as a bilinear map. -/
def windowPair (S : Finset ℕ) : SpanCycle →ₗ[ℝ] SpanCycle →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (D.windowPairFun S)
    (fun x x' y => by
      simp only [windowPairFun, Prod.fst_add, Prod.snd_add, D.windowA_add, windowB_add,
        D.windowGraph_add_left]
      ring)
    (fun c x y => by
      simp only [windowPairFun, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        D.windowA_smul, windowB_smul, D.windowGraph_smul_left]
      ring)
    (fun x y y' => by
      simp only [windowPairFun, Prod.fst_add, Prod.snd_add, D.windowA_add, windowB_add]
      rw [D.windowGraph_symm S x.2.2, D.windowGraph_add_left,
        D.windowGraph_symm S y.2.2, D.windowGraph_symm S y'.2.2]
      ring)
    (fun c x y => by
      simp only [windowPairFun, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        D.windowA_smul, windowB_smul]
      rw [D.windowGraph_symm S x.2.2, D.windowGraph_smul_left, D.windowGraph_symm]
      ring)

theorem windowPair_apply (S : Finset ℕ) (x y : SpanCycle) :
    D.windowPair S x y = D.windowPairFun S x y := rfl

/-- The Frobenius span over a finite window `S` as a `PolarSurface` with pole classes
`H = (1, 0, 0)` and `V = (0, 1, 0)`. -/
def windowSurface (S : Finset ℕ) : PolarSurface SpanCycle where
  pair := D.windowPair S
  pair_comm x y := by
    simp only [windowPair_apply, windowPairFun, D.windowGraph_symm S x.2.2 y.2.2]
    ring
  H := (1, 0, 0)
  V := (0, 1, 0)
  pair_H_H := by
    simp [windowPair_apply, windowPairFun, D.windowA_zero, windowB_zero, D.windowGraph_zero_left]
  pair_V_V := by
    simp [windowPair_apply, windowPairFun, D.windowA_zero, windowB_zero, D.windowGraph_zero_left]
  pair_H_V := by
    simp [windowPair_apply, windowPairFun, D.windowA_zero, windowB_zero, D.windowGraph_zero_left]

/-- Pairing with `H = (1, 0, 0)` extracts `b + A(d)`. -/
theorem windowSurface_pair_H (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface S).pair x (D.windowSurface S).H = x.2.1 + D.windowA S x.2.2 := by
  simp only [windowSurface, windowPair_apply, windowPairFun,
    D.windowA_zero, windowB_zero, D.windowGraph_zero_right]
  ring

/-- Pairing with `V = (0, 1, 0)` extracts `a + B(d)`. -/
theorem windowSurface_pair_V (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface S).pair x (D.windowSurface S).V = x.1 + windowB S x.2.2 := by
  simp only [windowSurface, windowPair_apply, windowPairFun,
    D.windowA_zero, windowB_zero, D.windowGraph_zero_right]
  ring

/-- The Castelnuovo–Severi defect of `D.windowSurface S` is `D.spanDefect S`. -/
theorem windowSurface_defect_self (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface S).defect x x = D.spanDefect S x.2.2 := by
  rw [(D.windowSurface S).defect_self, D.windowSurface_pair_H, D.windowSurface_pair_V]
  simp only [windowSurface, windowPair_apply, windowPairFun, spanDefect,
    windowA, windowB, windowGraph]
  ring

/-- The Hodge index holds on `D.windowSurface S` for every finite window `S` if and only if all
Frobenius eigenvalues of `D` lie on the unit circle. -/
theorem windowSurface_hodgeIndex_iff_unitary :
    (∀ S : Finset ℕ, (D.windowSurface S).HodgeIndex) ↔ ∀ i : ι, ‖D.β i‖ = 1 := by
  rw [← D.hodgeIndexOnSpan_iff_unitary]
  constructor
  · intro h S d
    have hS := (D.windowSurface S).hodgeIndex_iff_defect_nonneg.mp (h S) (0, 0, d)
    rwa [D.windowSurface_defect_self] at hS
  · intro h S
    rw [(D.windowSurface S).hodgeIndex_iff_defect_nonneg]
    intro x
    rw [D.windowSurface_defect_self]
    exact h S x.2.2

/-- The positive Frobenius graph cone always satisfies `AmpleAxiom`. -/
theorem graphCone_ample (S : Finset ℕ) :
    (D.windowSurface S).AmpleAxiom (graphCone S) := by
  have hq : 0 < D.q := by linarith [D.one_lt_q]
  have hample_eq : ∀ x : SpanCycle,
      (D.windowSurface S).pair x (D.windowSurface S).ample =
        x.1 + x.2.1 + windowB S x.2.2 + D.windowA S x.2.2 := by
    intro x
    rw [(D.windowSurface S).pair_ample, D.windowSurface_pair_H, D.windowSurface_pair_V]
    ring
  intro x ⟨hx1, hx2, hxd⟩ h0 y
  rw [hample_eq] at h0
  have hB : 0 ≤ windowB S x.2.2 := Finset.sum_nonneg hxd
  have hA : 0 ≤ D.windowA S x.2.2 :=
    Finset.sum_nonneg fun k hk => mul_nonneg (hxd k hk) (le_of_lt (pow_pos hq k))
  have hx1_eq : x.1 = 0 := by linarith
  have hx2_eq : x.2.1 = 0 := by linarith
  have hB_eq : windowB S x.2.2 = 0 := by linarith
  have hA_eq : D.windowA S x.2.2 = 0 := by linarith
  have hd_zero : ∀ k ∈ S, x.2.2 k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hxd).mp hB_eq
  have hG_eq : D.windowGraph S x.2.2 y.2.2 = 0 := by
    refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k _ => ?_
    rw [hd_zero j hj, zero_mul, zero_mul]
  simp only [windowSurface, windowPair_apply, windowPairFun, hx1_eq, hx2_eq, hB_eq, hA_eq, hG_eq]
  ring

/-- Whenever all point counts `D.pointCount j` are nonnegative, the positive Frobenius graph cone
satisfies `BezoutAxiom`. -/
theorem graphCone_bezout (S : Finset ℕ) (hN : ∀ j : ℕ, 0 ≤ D.pointCount j) :
    (D.windowSurface S).BezoutAxiom (graphCone S) := by
  have hq : 0 ≤ D.q := by linarith [D.one_lt_q]
  rintro x ⟨hx1, hx2, hxd⟩ y ⟨hy1, hy2, hyd⟩
  simp only [windowSurface, windowPair_apply, windowPairFun]
  have hBx : 0 ≤ windowB S x.2.2 := Finset.sum_nonneg hxd
  have hBy : 0 ≤ windowB S y.2.2 := Finset.sum_nonneg hyd
  have hAx : 0 ≤ D.windowA S x.2.2 :=
    Finset.sum_nonneg fun k hk => mul_nonneg (hxd k hk) (pow_nonneg hq k)
  have hAy : 0 ≤ D.windowA S y.2.2 :=
    Finset.sum_nonneg fun k hk => mul_nonneg (hyd k hk) (pow_nonneg hq k)
  have hG : 0 ≤ D.windowGraph S x.2.2 y.2.2 := by
    refine Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_
    rw [graphPair]
    exact mul_nonneg (mul_nonneg (hxd j hj) (hyd k hk))
      (mul_nonneg (pow_nonneg hq (min j k)) (hN (Nat.dist j k)))
  positivity

/-- The positive Frobenius graph cone unconditionally fails `RiemannRochAxiom` on every nonempty
window `S`. -/
theorem graphCone_not_riemannRoch {S : Finset ℕ} {k : ℕ} (hk : k ∈ S) :
    ¬ (D.windowSurface S).RiemannRochAxiom (graphCone S) := by
  classical
  refine (D.windowSurface S).not_riemannRoch_of_perturbation (x := (0, 0, -Pi.single k 1)) ?_
  intro ε hε
  refine ⟨?_, ?_⟩
  · intro hmem
    have hmem_k := hmem.2.2 k hk
    simp only [PolarSurface.ample, windowSurface, Prod.snd_add, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply,
      smul_eq_mul, zero_add, Pi.single_eq_same, mul_neg, mul_one] at hmem_k
    linarith
  · intro hmem
    have hmem_1 := hmem.1
    simp only [PolarSurface.ample, windowSurface, Prod.fst_neg, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul, mul_zero, add_zero] at hmem_1
    linarith

end CurveDatum

/-! ### 4. The golden fake curve: Bézout + Ample + Euler positivity without Hodge index -/

/-- All point counts `N_n = 5^n + 1 − L_n` of the golden fake curve `goldenDatum` are
nonnegative. -/
theorem goldenDatum_pointCount_nonneg : ∀ n : ℕ, 0 ≤ goldenDatum.pointCount n
  | 0 => by rw [CurveDatum.pointCount_zero]; norm_num
  | n + 1 => by linarith [one_le_goldenDatum_pointCount (Nat.succ_le_succ (Nat.zero_le n))]

/-- On the golden fake curve `goldenDatum`, the positive Frobenius graph cone satisfies both
`AmpleAxiom` and `BezoutAxiom` on every finite window `S`, yet fails `RiemannRochAxiom` on every
nonempty window `S`. -/
theorem goldenDatum_graphCone_ample_and_bezout (S : Finset ℕ) :
    (goldenDatum.windowSurface S).AmpleAxiom (graphCone S) ∧
    (goldenDatum.windowSurface S).BezoutAxiom (graphCone S) :=
  ⟨goldenDatum.graphCone_ample S,
    goldenDatum.graphCone_bezout S goldenDatum_pointCount_nonneg⟩

/-- The explicit integer primitive cycle `−H + 3V + 2Γ₀ − Γ₁` on `goldenDatum`. -/
def goldenCounterexample : SpanCycle :=
  (-1, 3, fun k => if k = 0 then 2 else if k = 1 then -1 else 0)

/-- `goldenCounterexample` is primitive (`x · H = 0` and `x · V = 0`) and has strictly positive
self-intersection `x² = 2 > 0` on the `{0, 1}` window of `goldenDatum`. -/
theorem goldenCounterexample_violates_hodgeIndex :
    (goldenDatum.windowSurface {0, 1}).pair goldenCounterexample
      (goldenDatum.windowSurface {0, 1}).H = 0 ∧
    (goldenDatum.windowSurface {0, 1}).pair goldenCounterexample
      (goldenDatum.windowSurface {0, 1}).V = 0 ∧
    (goldenDatum.windowSurface {0, 1}).pair goldenCounterexample goldenCounterexample = 2 := by
  have hN0 : goldenDatum.pointCount 0 = 0 := by
    rw [goldenDatum_pointCount_eq]; norm_num [goldenLucas]
  have hN1 : goldenDatum.pointCount 1 = 1 := by
    rw [goldenDatum_pointCount_eq]; norm_num [goldenLucas]
  have hH : (goldenDatum.windowSurface {0, 1}).pair goldenCounterexample
      (goldenDatum.windowSurface {0, 1}).H = 0 := by
    rw [goldenDatum.windowSurface_pair_H]
    simp [goldenCounterexample, CurveDatum.windowA, goldenDatum]
  have hV : (goldenDatum.windowSurface {0, 1}).pair goldenCounterexample
      (goldenDatum.windowSurface {0, 1}).V = 0 := by
    rw [goldenDatum.windowSurface_pair_V]
    simp [goldenCounterexample, windowB]
  refine ⟨hH, hV, ?_⟩
  have hdef := goldenDatum.windowSurface_defect_self {0, 1} goldenCounterexample
  rw [(goldenDatum.windowSurface {0, 1}).defect_self, hH, hV] at hdef
  have hspan : goldenDatum.spanDefect {0, 1} goldenCounterexample.2.2 = -2 := by
    simp only [goldenCounterexample, CurveDatum.spanDefect, CurveDatum.graphPair]
    rw [Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one]
    simp only [Finset.sum_pair zero_ne_one, Nat.dist_self, Nat.dist_zero_left, Nat.dist_zero_right]
    norm_num [goldenDatum, hN0, hN1]
  linarith

/-! ### 5. The cohomological sign and subshift obstruction -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **Exact window identity for the constant weight**: on `{0, …, n − 1}`, the Toeplitz form at the
constant vector `1` decomposes into the diagonal term `n · |ι|` and twice the strictly upper
triangular trace sum `∑_{m < n} ∑_{j < m} D.trace (m − j)`. -/
theorem toeplitz_range_one (n : ℕ) :
    D.toeplitz (Finset.range n) (fun _ => 1) =
      (n : ℝ) * (Fintype.card ι : ℝ) +
        2 * ∑ m ∈ Finset.range n, ∑ j ∈ Finset.range m, D.trace (m - j) := by
  induction n with
  | zero =>
    simp [toeplitz]
  | succ n ih =>
    have hstep :
        D.toeplitz (Finset.range (n + 1)) (fun _ => 1) =
          D.toeplitz (Finset.range n) (fun _ => 1) +
            (Fintype.card ι : ℝ) + 2 * ∑ j ∈ Finset.range n, D.trace (n - j) := by
      simp only [toeplitz, one_mul, Finset.sum_range_succ]
      have hleft :
          ∑ x ∈ Finset.range n,
              ((∑ y ∈ Finset.range n, D.trace (Nat.dist x y)) +
                D.trace (Nat.dist x n)) =
            (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
              D.trace (Nat.dist x y)) +
              ∑ x ∈ Finset.range n, D.trace (n - x) := by
        rw [Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxn : x < n := Finset.mem_range.mp hx
        rw [Nat.dist_eq_sub_of_le (le_of_lt hxn)]
      have hright :
          ∑ y ∈ Finset.range n, D.trace (Nat.dist n y) =
            ∑ y ∈ Finset.range n, D.trace (n - y) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        have hyn : y < n := Finset.mem_range.mp hy
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (le_of_lt hyn)]
      rw [hleft, hright, Nat.dist_self, D.trace_zero]
      ring
    rw [hstep, ih, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- If all traces `D.trace k` for `k ≥ 1` are nonnegative, then the constant-weight Toeplitz form
on `{0, …, n − 1}` grows at least linearly as `n · |ι|`. -/
theorem card_mul_le_toeplitz_range_one_of_trace_nonneg
    (htr : ∀ k : ℕ, 1 ≤ k → 0 ≤ D.trace k) (n : ℕ) :
    (n : ℝ) * (Fintype.card ι : ℝ) ≤ D.toeplitz (Finset.range n) (fun _ => 1) := by
  rw [D.toeplitz_range_one n]
  have hsum : 0 ≤ ∑ m ∈ Finset.range n, ∑ j ∈ Finset.range m, D.trace (m - j) := by
    refine Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j hj => ?_
    have hjm : j < m := Finset.mem_range.mp hj
    exact htr (m - j) (by omega)
  linarith

/-- **Uniform Fejér bound under unitarity**: if `|β_i| = 1` and `β_i ≠ 1` for all `i`, then the
constant-weight Toeplitz form on `{0, …, n − 1}` is bounded uniformly in `n` by
`∑_i 4 / ‖β_i − 1‖²`. -/
theorem toeplitz_range_one_le_of_unitary (hU : ∀ i : ι, ‖D.β i‖ = 1)
    (h1 : ∀ i : ι, D.β i ≠ 1) (n : ℕ) :
    D.toeplitz (Finset.range n) (fun _ => 1) ≤ ∑ i : ι, 4 / ‖D.β i - 1‖ ^ 2 := by
  rw [D.toeplitz_eq_sum_normSq hU (Finset.range n) (fun _ => 1)]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Complex.ofReal_one, one_mul]
  rw [geom_sum_eq (h1 i) n, norm_div, div_pow]
  have hden_ne : D.β i - 1 ≠ 0 := sub_ne_zero.mpr (h1 i)
  have hden_pos : 0 < ‖D.β i - 1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hden_ne)
  have hnum : ‖D.β i ^ n - 1‖ ≤ 2 := by
    calc ‖D.β i ^ n - 1‖ ≤ ‖D.β i ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = ‖D.β i‖ ^ n + 1 := by rw [norm_pow, norm_one]
    _ = 2 := by rw [hU i, one_pow]; norm_num
  have hnum_sq : ‖D.β i ^ n - 1‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (D.β i ^ n - 1)]
  exact div_le_div_of_nonneg_right hnum_sq (le_of_lt hden_pos)

/-- **Cohomological sign obstruction**: any nonempty unitary `CurveDatum` with `1 ∉ Spec(F)` must
have a strictly negative trace `D.trace k < 0` at some positive iterate `k ≥ 1`. -/
theorem exists_trace_neg_of_unitary [Nonempty ι] (hU : ∀ i : ι, ‖D.β i‖ = 1)
    (h1 : ∀ i : ι, D.β i ≠ 1) : ∃ k : ℕ, 1 ≤ k ∧ D.trace k < 0 := by
  by_contra h_all
  push Not at h_all
  let M : ℝ := ∑ i : ι, 4 / ‖D.β i - 1‖ ^ 2
  let n : ℕ := Nat.floor M + 1
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) :=
    Nat.one_le_cast.mpr Fintype.card_pos
  have hn_le : (n : ℝ) ≤ (n : ℝ) * (Fintype.card ι : ℝ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg n) hcard
  have hlow : (n : ℝ) * (Fintype.card ι : ℝ) ≤ D.toeplitz (Finset.range n) (fun _ => 1) :=
    D.card_mul_le_toeplitz_range_one_of_trace_nonneg h_all n
  have hhigh : D.toeplitz (Finset.range n) (fun _ => 1) ≤ M :=
    D.toeplitz_range_one_le_of_unitary hU h1 n
  have hlt : M < (n : ℝ) := by
    simpa [n] using Nat.lt_floor_add_one M
  linarith

/-- Under the Hodge index on all finite windows and `1 ∉ Spec(F)`, a nonempty `CurveDatum` must
exceed the subshift baseline `q^k + 1` at some iterate `k ≥ 1`: `D.pointCount k > D.q^k + 1`. -/
theorem exists_pointCount_gt_of_hodgeIndex [Nonempty ι]
    (hH : ∀ S : Finset ℕ, (D.windowSurface S).HodgeIndex)
    (h1 : ∀ i : ι, D.β i ≠ 1) : ∃ k : ℕ, 1 ≤ k ∧ D.q ^ k + 1 < D.pointCount k := by
  have hU : ∀ i : ι, ‖D.β i‖ = 1 := D.windowSurface_hodgeIndex_iff_unitary.mp hH
  obtain ⟨k, hk, htr⟩ := D.exists_trace_neg_of_unitary hU h1
  refine ⟨k, hk, ?_⟩
  simp only [pointCount]
  have hneg : D.sqrtq ^ k * D.trace k < 0 :=
    mul_neg_of_pos_of_neg (pow_pos D.sqrtq_pos k) htr
  linarith

/-- **Subshift / nonnegative-trace no-go for the Hodge index**: no nonempty `CurveDatum` with
`1 ∉ Spec(F)` and `D.pointCount k ≤ D.q^k + 1` for all `k ≥ 1` (such as a single dynamical
subshift difference `1 + q^k − |Fix(σ^k)|` or a nonnegative transfer matrix `B ≥ 0` with
`Tr(B^k) ≥ 0`) can satisfy the Hodge index across all finite windows. -/
theorem not_hodgeIndex_of_subshift_bound [Nonempty ι]
    (h1 : ∀ i : ι, D.β i ≠ 1)
    (hsub : ∀ k : ℕ, 1 ≤ k → D.pointCount k ≤ D.q ^ k + 1) :
    ¬ ∀ S : Finset ℕ, (D.windowSurface S).HodgeIndex := by
  intro hH
  obtain ⟨k, hk, hgt⟩ := D.exists_pointCount_gt_of_hodgeIndex hH h1
  linarith [hsub k hk]

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
