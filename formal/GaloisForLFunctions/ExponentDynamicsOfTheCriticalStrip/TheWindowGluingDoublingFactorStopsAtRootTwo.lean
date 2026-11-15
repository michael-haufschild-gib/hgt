import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheBestDoublingFactorOfTheMarginIsTwoToTheWidth
import GaloisForLFunctions.PNTPlus.Wiener

/-!
# The window-gluing doubling factor stops at `√2`

This module resolves the window-gluing doubling-factor problem unconditionally:

1. **Universal finite-matrix `√2` doubling law (`reweightedDoublingLaw_sqrt_two`,
   `doublingLaw_sqrt_two`)**:
   Every bounded contact-weight model `|ω(k)| ≤ B` (and in particular the true zeta window
   `neutralWindow` at `ω ≡ 1`) satisfies the `√2` doubling law along **every** block-size law
   `ρ : ℕ → ℕ`, directly from the finite block matrices without contour integrals, zero-free
   regions, or polynomial upper caps on `ρ`.

2. **Sharp `√2` barrier for pure window-gluing (`not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight`,
   `sInf_reweightedDoublingLaw_subEulerGluingWeight_eq_sqrt_two`,
   `gluing_indistinguishable_obstruction_package`)**:
   For every finite certified cutoff `Q₀ : ℕ` and every block-size law `ρ` with `ρ(K) ≥ 1`, the
   sub-Euler model `subEulerGluingWeight Q₀` takes values in `{0, 1}`, satisfies `ω(p^r) = ω(p)` on
   all prime powers, agrees entry-for-entry with `neutralWindow` up to `Q₀`, has the exact same
   dyadic-middle Green operator `weilMiddle D` at every `D`, and has identical wide-overlap steps
   up to `Q₀`, yet admits **no** doubling law with any factor `λ < √2` (and in particular none
   with `λ ≤ 2^{3/8}` or `λ < 2^{3/8}`). The infimum of its valid doubling factors is `√2`.

3. **Unconditional single-step top-octave jump and `< 2^{3/8}` equivalence on `neutralWindow`
   (`eventually_two_le_hermNegIndex_neutralWindow_halfCutoff`,
   `topOctave_jump_of_doublingLaw_lt_sqrt_two`,
   `exists_doublingLaw_lt_two_rpow_three_eighths_iff`,
   `riemannZeta_ne_zero_of_doublingLaw`)**:
   On `neutralWindow` itself, gluing `(R, (3K + 1)R]` and `(2R, (6K + 2)R]` across `(2R, (3K + 1)R]`
   produces the un-updated matrix `neutralWindow (3K + 1) R (6KR)`, which unconditionally has at
   least two negative squares up to `(1 / 2000) √K − 40000` for all `R ≥ 6` and all sufficiently
   large `K`. Thus any doubling factor `λ < √2` requires the direct end-to-end top-octave prime
   operator `∑_{k = 3K+2}^{6K+1} floorGraph k` on `(R, 2R] × ((3K + 1)R, (6K + 1)R]` to eliminate
   the second negative eigenvalue across an `Ω(√K)` spectral interval; and along `K¹⁰ ≤ ρ(K) ≤ K^A`,
   a doubling factor `1 < λ < 2^{3/8}` exists if and only if `zetaZeroWidth < 3/8`, yielding a
   zero-free half-plane `Re s > 1/2 + log₂ λ` strictly wider than `Re s > 7/8`.
-/

open Finset Filter Topology Matrix
open scoped Real ArithmeticFunction.vonMangoldt
open Zeta23
open GaloisForLFunctions.HTGeometry (hermNegIndex hermQuad hermQuad_neg IsPosDefOn
  exists_isPosDefOn_finrank_eq_posIndex finrank_le_posIndex)
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_le_three_eighths zetaZeroWidth_le_iff_re_le)
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-! ### 1. Reweighted level laws and doubling laws -/

/-- A **reweighted level law** for contact weights `ω : ℕ → ℝ` along a block-size law `ρ`: on
every window `(ρ(K), (3K + 1)ρ(K)]` (`K ≥ 1`), raising `reweightedNeutral ω (3K + 1)` by `a(K)`
leaves at most one negative square. -/
def IsReweightedLevelLaw (ω : ℕ → ℝ) (ρ : ℕ → ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ K : ℕ, 1 ≤ K →
    hermNegIndex ((windowMatrix (reweightedNeutral ω (3 * K + 1)) (ρ K) (3 * K * ρ K) +
      Matrix.diagonal (fun _ : Fin (3 * K * ρ K) => a K)).map (↑) :
        Matrix (Fin (3 * K * ρ K)) (Fin (3 * K * ρ K)) ℂ) ≤ 1

/-- A **reweighted doubling law with factor `lam`**: a monotone reweighted level law satisfying
`a(2K) ≤ lam * a(K) + c` for all `K ≥ 1`. -/
def ReweightedDoublingLaw (ω : ℕ → ℝ) (ρ : ℕ → ℕ) (lam : ℝ) : Prop :=
  ∃ a : ℕ → ℝ, ∃ c : ℝ,
    Monotone a ∧ (∀ K, 1 ≤ K → a (2 * K) ≤ lam * a K + c) ∧ IsReweightedLevelLaw ω ρ a

/-- Raising the levels preserves a reweighted level law. -/
theorem IsReweightedLevelLaw.mono {ω : ℕ → ℝ} {ρ : ℕ → ℕ} {a b : ℕ → ℝ}
    (h : IsReweightedLevelLaw ω ρ a) (hab : ∀ K, 1 ≤ K → a K ≤ b K) :
    IsReweightedLevelLaw ω ρ b := fun K hK =>
  (hermNegIndex_add_diagonal_mono
    (windowMatrix (reweightedNeutral ω (3 * K + 1)) (ρ K) (3 * K * ρ K)) (hab K hK)).trans (h K hK)

/-- At unit weights `ω ≡ 1`, `IsReweightedLevelLaw` is `IsLevelLaw`. -/
theorem isReweightedLevelLaw_one_iff {ρ : ℕ → ℕ} {a : ℕ → ℝ} :
    IsReweightedLevelLaw (fun _ => 1) ρ a ↔ IsLevelLaw ρ a := by
  have heq : ∀ Q R J, windowMatrix (reweightedNeutral (fun _ => 1) Q) R J = neutralWindow Q R J := by
    intro Q R J; ext i j; simp [neutralWindow, windowMatrix, reweightedNeutral]
  simp only [IsReweightedLevelLaw, IsLevelLaw, heq]

/-- At unit weights `ω ≡ 1`, `ReweightedDoublingLaw` is `DoublingLaw`. -/
theorem reweightedDoublingLaw_one_iff {ρ : ℕ → ℕ} {lam : ℝ} :
    ReweightedDoublingLaw (fun _ => 1) ρ lam ↔ DoublingLaw ρ lam := by
  simp only [ReweightedDoublingLaw, DoublingLaw, isReweightedLevelLaw_one_iff]

/-! ### 2. Universal finite-matrix `√2` doubling law -/

/-- **Universal `√2` doubling law for bounded contact weights**: whenever `|ω(k)| ≤ B` (`B ≥ 0`),
`ReweightedDoublingLaw ω ρ (Real.sqrt 2)` holds along **every** block-size law `ρ : ℕ → ℕ`. -/
theorem reweightedDoublingLaw_sqrt_two {ω : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hω : ∀ k, |ω k| ≤ B) (ρ : ℕ → ℕ) :
    ReweightedDoublingLaw ω ρ (Real.sqrt 2) := by
  have hslope : 0 ≤ reweightedShiftSlope B := by
    unfold reweightedShiftSlope
    nlinarith [floorContactSqrtConst_pos]
  refine ⟨fun K => reweightedShiftSlope B * Real.sqrt K + 5, 5, ?_, ?_, ?_⟩
  · intro K₁ K₂ h12
    have hs : Real.sqrt K₁ ≤ Real.sqrt K₂ := Real.sqrt_le_sqrt (by exact_mod_cast h12)
    nlinarith [mul_le_mul_of_nonneg_left hs hslope]
  · intro K _
    have hs2K : Real.sqrt ((2 * K : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt K := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul zero_le_two]
    rw [hs2K]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg K]
  · intro K hK
    have h0 := hermNegIndex_reweightedNeutral_shift_eq_zero hB hω (ρ K) hK
      (Q := 3 * K + 1) (J := 3 * K * ρ K) (by omega) le_rfl
      (a := reweightedShiftSlope B * Real.sqrt K + 5) le_rfl
    omega

/-- Monotonicity in the doubling factor above `√2`. -/
theorem reweightedDoublingLaw_of_sqrt_two_le {ω : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hω : ∀ k, |ω k| ≤ B) (ρ : ℕ → ℕ) {lam : ℝ} (hlam : Real.sqrt 2 ≤ lam) :
    ReweightedDoublingLaw ω ρ lam := by
  have hslope : 0 ≤ reweightedShiftSlope B := by
    unfold reweightedShiftSlope
    nlinarith [floorContactSqrtConst_pos]
  refine ⟨fun K => reweightedShiftSlope B * Real.sqrt K + 5, 5, ?_, ?_, ?_⟩
  · intro K₁ K₂ h12
    have hs : Real.sqrt K₁ ≤ Real.sqrt K₂ := Real.sqrt_le_sqrt (by exact_mod_cast h12)
    nlinarith [mul_le_mul_of_nonneg_left hs hslope]
  · intro K _
    have hs2K : Real.sqrt ((2 * K : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt K := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul zero_le_two]
    rw [hs2K]
    have hnonneg : 0 ≤ reweightedShiftSlope B * Real.sqrt K + 5 := by positivity
    have hmul : Real.sqrt 2 * (reweightedShiftSlope B * Real.sqrt K + 5) ≤
        lam * (reweightedShiftSlope B * Real.sqrt K + 5) :=
      mul_le_mul_of_nonneg_right hlam hnonneg
    nlinarith [Real.sqrt_nonneg 2]
  · intro K hK
    have h0 := hermNegIndex_reweightedNeutral_shift_eq_zero hB hω (ρ K) hK
      (Q := 3 * K + 1) (J := 3 * K * ρ K) (by omega) le_rfl
      (a := reweightedShiftSlope B * Real.sqrt K + 5) le_rfl
    omega

/-- **Universal finite-matrix `√2` doubling law for `neutralWindow`**: holds unconditionally along
every block-size law `ρ : ℕ → ℕ`, with no zero-free input and no polynomial upper bound on `ρ`. -/
theorem doublingLaw_sqrt_two (ρ : ℕ → ℕ) : DoublingLaw ρ (Real.sqrt 2) :=
  reweightedDoublingLaw_one_iff.mp
    (reweightedDoublingLaw_sqrt_two zero_le_one (fun _ => by norm_num) ρ)

/-- Every factor `lam ≥ √2` is a doubling factor for `neutralWindow` along every `ρ : ℕ → ℕ`. -/
theorem doublingLaw_of_sqrt_two_le (ρ : ℕ → ℕ) {lam : ℝ} (hlam : Real.sqrt 2 ≤ lam) :
    DoublingLaw ρ lam :=
  reweightedDoublingLaw_one_iff.mp
    (reweightedDoublingLaw_of_sqrt_two_le zero_le_one (fun _ => by norm_num) ρ hlam)

/-! ### 3. Sharp `√2` barrier across gluing-indistinguishable sub-Euler models -/

/-- `log₂ (√2) = 1 / 2`. -/
lemma logb_two_sqrt_two : Real.logb 2 (Real.sqrt 2) = 1 / 2 := by
  rw [Real.sqrt_eq_rpow, one_div, Real.logb_rpow (by norm_num) (by norm_num)]

/-- `(2 : ℝ) ^ (3 / 8 : ℝ) < √2`. -/
theorem two_rpow_three_eighths_lt_sqrt_two : (2 : ℝ) ^ (3 / 8 : ℝ) < Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

/-- **Sharp `√2` impossibility for `subEulerGluingWeight Q₀`**: for every finite certified cutoff
`Q₀ : ℕ`, every block-size law `ρ` with `ρ(K) ≥ 1` (`K ≥ 1`), and every `lam < √2` (including all
`lam ≤ 1` and all `1 < lam < √2`), `ReweightedDoublingLaw (subEulerGluingWeight Q₀) ρ lam` is
false. -/
theorem not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight (Q₀ : ℕ) {ρ : ℕ → ℕ}
    (hρ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {lam : ℝ} (hlam : lam < Real.sqrt 2) :
    ¬ ReweightedDoublingLaw (subEulerGluingWeight Q₀) ρ lam := by
  -- First prove the `1 < lam < √2` case, then reduce `lam ≤ 1` to `lam = 5 / 4`.
  have hgt_one : ∀ {μ : ℝ}, 1 < μ → μ < Real.sqrt 2 →
      ¬ ReweightedDoublingLaw (subEulerGluingWeight Q₀) ρ μ := by
    intro μ hμ1 hμ2 ⟨a, c, hmono, hd, hlev⟩
    have hpow := le_rpow_logb_of_doubling hμ1 hmono hd
    set Cₐ : ℝ := max (μ * (|a 1| + 2 * |c| / (μ - 1))) 1
    have hCₐ1 : 1 ≤ Cₐ := le_max_right _ _
    set θ : ℝ := Real.logb 2 μ
    have hθ_pos : 0 < θ := Real.logb_pos (by norm_num) hμ1
    have hθ_lt : θ < 1 / 2 := by
      rw [← logb_two_sqrt_two]
      exact Real.logb_lt_logb (by norm_num) (by linarith) hμ2
    set δ : ℝ := 1 / 2 - θ
    have hδ_pos : 0 < δ := by linarith
    -- Along `K_m = 8 · 256^m`, `(K_m : ℝ) ^ δ → ∞`.
    have htend_K : Tendsto (fun m : ℕ => ((8 * 256 ^ m : ℕ) : ℝ)) atTop atTop := by
      have h1 : Tendsto (fun m : ℕ => (256 : ℝ) ^ m) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      have h2 : Tendsto (fun m : ℕ => (8 : ℝ) * (256 : ℝ) ^ m) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) h1
      exact h2.congr fun m => by push_cast; rfl
    have htend_rpow : Tendsto (fun m : ℕ => ((8 * 256 ^ m : ℕ) : ℝ) ^ δ) atTop atTop :=
      (tendsto_rpow_atTop hδ_pos).comp htend_K
    have hev := (htend_rpow.eventually_gt_atTop
      (60 * (Cₐ + |subEulerCrossConst| + 20001))).and (eventually_ge_atTop (Q₀ + 4))
    obtain ⟨m, hlarge, hm⟩ := hev.exists
    set K : ℕ := 8 * 256 ^ m
    have hK1 : 1 ≤ K := by
      have : 1 ≤ 256 ^ m := Nat.one_le_pow m 256 (by norm_num)
      dsimp [K]; omega
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast hK1
    have hKθ_ge : 1 ≤ (K : ℝ) ^ θ :=
      Real.one_le_rpow (by exact_mod_cast hK1) hθ_pos.le
    have hK_prod : (K : ℝ) ^ δ * (K : ℝ) ^ θ = Real.sqrt K := by
      rw [← Real.rpow_add hK_pos, show δ + θ = 1 / 2 by dsimp [δ]; ring, Real.sqrt_eq_rpow]
    have haK_le : a K ≤ Cₐ * (K : ℝ) ^ θ := by
      have h1 := hpow K hK1
      have h2 : μ * (|a 1| + 2 * |c| / (μ - 1)) ≤ Cₐ := le_max_left _ _
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hK_pos.le θ))
    have ha_shift : a K ≤ (1 / 60 : ℝ) * Real.sqrt K - (subEulerCrossConst + 20000) := by
      have hmul := mul_le_mul_of_nonneg_right hlarge.le (Real.rpow_nonneg hK_pos.le θ)
      rw [hK_prod] at hmul
      have hsub_abs : subEulerCrossConst ≤ |subEulerCrossConst| := le_abs_self _
      have hc0 : 0 ≤ |subEulerCrossConst| + 20001 := by positivity
      have h1 : |subEulerCrossConst| + 20001 ≤ (|subEulerCrossConst| + 20001) * (K : ℝ) ^ θ := by
        nlinarith
      nlinarith
    have htwo := two_le_hermNegIndex_subEulerGluingWeight Q₀ hm (hρ K hK1) ha_shift
    have hone := hlev K hK1
    omega
  by_cases h1 : 1 < lam
  · exact hgt_one h1 hlam
  · intro ⟨a, c, hmono, hd, hlev⟩
    have hlam_le : lam ≤ 1 := not_lt.mp h1
    have h54_lt : (5 / 4 : ℝ) < Real.sqrt 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    refine hgt_one (by norm_num : (1 : ℝ) < 5 / 4) h54_lt
      ⟨fun K => max (a K) 0, |c| + |lam| * |a 1|, hmono.max monotone_const, ?_,
        hlev.mono fun K _ => le_max_left _ _⟩
    intro K hK
    have ha2K := hd K hK
    have ha1_le : a 1 ≤ a K := hmono hK
    have hc_le : c ≤ |c| := le_abs_self c
    have h0_rhs : 0 ≤ (5 / 4 : ℝ) * max (a K) 0 + (|c| + |lam| * |a 1|) := by
      have : 0 ≤ max (a K) 0 := le_max_right _ _
      positivity
    refine max_le ?_ h0_rhs
    by_cases ha0 : 0 ≤ a K
    · have hmax_eq : max (a K) 0 = a K := max_eq_left ha0
      rw [hmax_eq]
      have hmul : lam * a K ≤ (5 / 4 : ℝ) * a K :=
        mul_le_mul_of_nonneg_right (by linarith) ha0
      have hnonneg_tail : 0 ≤ |lam| * |a 1| := by positivity
      linarith
    · push Not at ha0
      have habs_K : |a K| ≤ |a 1| := by
        rw [abs_of_neg ha0, abs_of_neg (ha1_le.trans_lt ha0)]
        linarith
      have hprod : lam * a K ≤ |lam| * |a 1| := by
        calc lam * a K ≤ |lam * a K| := le_abs_self _
          _ = |lam| * |a K| := abs_mul lam (a K)
          _ ≤ |lam| * |a 1| := mul_le_mul_of_nonneg_left habs_K (abs_nonneg lam)
      have : 0 ≤ (5 / 4 : ℝ) * max (a K) 0 := by positivity
      linarith

/-- **No doubling factor `≤ 2^{3/8}` (and hence none `< 2^{3/8}`) exists for
`subEulerGluingWeight Q₀`.** -/
theorem not_reweightedDoublingLaw_of_le_two_rpow_three_eighths_subEulerGluingWeight (Q₀ : ℕ)
    {ρ : ℕ → ℕ} (hρ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {lam : ℝ}
    (hlam : lam ≤ (2 : ℝ) ^ (3 / 8 : ℝ)) :
    ¬ ReweightedDoublingLaw (subEulerGluingWeight Q₀) ρ lam :=
  not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight Q₀ hρ
    (hlam.trans_lt two_rpow_three_eighths_lt_sqrt_two)

/-- **The infimum of valid doubling factors of `subEulerGluingWeight Q₀` is `√2`.** -/
theorem sInf_reweightedDoublingLaw_subEulerGluingWeight_eq_sqrt_two (Q₀ : ℕ) {ρ : ℕ → ℕ}
    (hρ : ∀ K, 1 ≤ K → 1 ≤ ρ K) :
    sInf {lam : ℝ | 1 < lam ∧ ReweightedDoublingLaw (subEulerGluingWeight Q₀) ρ lam} =
      Real.sqrt 2 := by
  let S := {lam : ℝ | 1 < lam ∧ ReweightedDoublingLaw (subEulerGluingWeight Q₀) ρ lam}
  have hs2_gt : (1 : ℝ) < Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one one_lt_two
  have hmem : Real.sqrt 2 ∈ S :=
    ⟨hs2_gt, reweightedDoublingLaw_sqrt_two zero_le_one (abs_subEulerGluingWeight_le_one Q₀) ρ⟩
  have hlow : ∀ lam ∈ S, Real.sqrt 2 ≤ lam := by
    intro lam hS
    by_contra hlt
    exact not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight Q₀ hρ (not_le.mp hlt) hS.2
  exact le_antisymm (csInf_le ⟨1, fun _ h => h.1.le⟩ hmem) (le_csInf ⟨Real.sqrt 2, hmem⟩ hlow)

/-- **Complete window-gluing obstruction theorem**: for every finite certified cutoff `Q₀ : ℕ` and
every `ρ` with `ρ(K) ≥ 1`, `ω := subEulerGluingWeight Q₀` satisfies:
1. Sub-Euler bounds `0 ≤ ω(k) ≤ 1` and exact prime-power constancy `ω(p^r) = ω(p)` (`r ≥ 1`),
2. Entrywise equality with `neutralWindow Q R J` for all `Q ≤ Q₀`,
3. Entrywise equality `windowMatrix (reweightedBlock ω Q) D D = weilMiddle D` on every dyadic
   middle `(D, 2D]`,
4. Entrywise equality with `neutralWindow` on both half-windows `(R, (3K + 1)R]` and
   `(2R, (6K + 2)R]` for all `3K + 1 ≤ Q₀`,
5. Validity of `ReweightedDoublingLaw ω ρ (Real.sqrt 2)`, and
6. Failure of `ReweightedDoublingLaw ω ρ lam` for every `lam < √2` (in particular every
   `lam ≤ 2^{3/8}`). -/
theorem gluing_indistinguishable_obstruction_package (Q₀ : ℕ) {ρ : ℕ → ℕ}
    (hρ : ∀ K, 1 ≤ K → 1 ≤ ρ K) :
    let ω := subEulerGluingWeight Q₀
    (∀ k, 0 ≤ ω k ∧ ω k ≤ 1) ∧
    (∀ p r : ℕ, p.Prime → 1 ≤ r → ω (p ^ r) = ω p) ∧
    (∀ Q R J : ℕ, Q ≤ Q₀ → windowMatrix (reweightedNeutral ω Q) R J = neutralWindow Q R J) ∧
    (∀ Q D : ℕ, windowMatrix (reweightedBlock ω Q) D D = weilMiddle D) ∧
    ReweightedDoublingLaw ω ρ (Real.sqrt 2) ∧
    (∀ lam : ℝ, lam < Real.sqrt 2 → ¬ ReweightedDoublingLaw ω ρ lam) :=
  ⟨fun k => ⟨subEulerGluingWeight_nonneg Q₀ k, subEulerGluingWeight_le_one Q₀ k⟩,
   fun _ _ hp hr => subEulerGluingWeight_prime_pow hp hr,
   fun _ _ _ hQ => windowMatrix_subEulerGluingWeight_eq_neutralWindow hQ,
   windowMatrix_reweightedBlock_dyadic (subEulerGluingWeight Q₀),
   reweightedDoublingLaw_sqrt_two zero_le_one (abs_subEulerGluingWeight_le_one Q₀) ρ,
   fun _ hlam => not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight Q₀ hρ hlam⟩

/-! ### 4. Unconditional top-octave jump on `neutralWindow` and the `< 2^{3/8}` characterization -/

/-- From `WeakPNT`, `Chebyshev.psi N / N → 1` as `N → ∞`. -/
lemma tendsto_psi_div_natCast :
    Tendsto (fun N : ℕ => Chebyshev.psi (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have hcs : ∀ N : ℕ, Chebyshev.psi (N : ℝ) = _root_.cumsum (⇑ArithmeticFunction.vonMangoldt) (N + 1) := by
    intro N
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    simp only [_root_.cumsum, Nat.range_succ_eq_Icc_zero]
  have h1 : Tendsto (fun N : ℕ =>
      _root_.cumsum (⇑ArithmeticFunction.vonMangoldt) (N + 1) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 1) :=
    _root_.WeakPNT.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun N : ℕ => (1 : ℝ) + (N : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    rw [add_zero] at hinv
    refine hinv.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp [hN0]
  have hprod := h1.mul hratio
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hcs N]
  field_simp [hN1]

/-- From `tendsto_psi_div_natCast` and `0 ≤ ψ N - θ N ≤ 3 (log 4 + 4) √N`,
`Chebyshev.theta N / N → 1` as `N → ∞`. -/
lemma tendsto_theta_div_natCast :
    Tendsto (fun N : ℕ => Chebyshev.theta (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have hdiff : Tendsto (fun N : ℕ =>
      (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (g := fun N : ℕ => 3 * (Real.log 4 + 4) * ((N : ℝ) ^ (-(1 / 2 : ℝ)))) ?_
    · filter_upwards [eventually_ge_atTop 1] with N _
      refine div_nonneg ?_ (Nat.cast_nonneg N)
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      calc (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) / (N : ℝ)
          ≤ (3 * (Real.log 4 + 4) * Real.sqrt (N : ℝ)) / (N : ℝ) :=
            div_le_div_of_nonneg_right (psi_sub_theta_le_three_mul_sqrt (N : ℝ)) hNpos.le
        _ = 3 * (Real.log 4 + 4) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) := by
            rw [Real.sqrt_eq_rpow, mul_div_assoc]
            congr 1
            rw [show -(1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub hNpos, Real.rpow_one]
    · have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
      simpa only [mul_zero] using h0.const_mul (3 * (Real.log 4 + 4))
  have hsub := tendsto_psi_div_natCast.sub hdiff
  rw [sub_zero] at hsub
  exact hsub.congr fun N => by ring

/-- Along any linear integer endpoint `N(K)` satisfying `a * K - C ≤ N(K) ≤ a * K + C` (`a > 0`),
`θ(N(K)) / K → a` and `ψ(N(K)) / K → a`. -/
lemma tendsto_theta_psi_linear {N : ℕ → ℕ} {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hlo : ∀ᶠ K in atTop, a * (K : ℝ) - C ≤ (N K : ℝ))
    (hhi : ∀ᶠ K in atTop, (N K : ℝ) ≤ a * (K : ℝ) + C) :
    Tendsto (fun K : ℕ => Chebyshev.theta (N K : ℝ) / (K : ℝ)) atTop (𝓝 a) ∧
    Tendsto (fun K : ℕ => Chebyshev.psi (N K : ℝ) / (K : ℝ)) atTop (𝓝 a) := by
  have hNK_atTop : Tendsto N atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro M
    have hev : ∀ᶠ K : ℕ in atTop, (M : ℝ) ≤ a * (K : ℝ) - C := by
      filter_upwards [(Filter.Tendsto.const_mul_atTop ha
        tendsto_natCast_atTop_atTop).eventually_ge_atTop ((M : ℝ) + C)] with K hK
      linarith
    filter_upwards [hev, hlo] with K h1 h2
    exact_mod_cast h1.trans h2
  have hrat : Tendsto (fun K : ℕ => (N K : ℝ) / (K : ℝ)) atTop (𝓝 a) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun K : ℕ => a - C * (K : ℝ)⁻¹) (h := fun K : ℕ => a + C * (K : ℝ)⁻¹) ?_ ?_ ?_ ?_
    · simpa using tendsto_const_nhds.sub
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C)
    · simpa using tendsto_const_nhds.add
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C)
    · filter_upwards [hlo, eventually_ge_atTop 1] with K h1 hK1
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
      rw [show a - C * (K : ℝ)⁻¹ = (a * (K : ℝ) - C) / (K : ℝ) by field_simp [hKpos.ne']]
      exact div_le_div_of_nonneg_right h1 hKpos.le
    · filter_upwards [hhi, eventually_ge_atTop 1] with K h2 hK1
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
      rw [show a + C * (K : ℝ)⁻¹ = (a * (K : ℝ) + C) / (K : ℝ) by field_simp [hKpos.ne']]
      exact div_le_div_of_nonneg_right h2 hKpos.le
  have hcongr_prod : ∀ g : ℕ → ℝ,
      Tendsto (fun n => g n / (n : ℝ)) atTop (𝓝 1) →
      Tendsto (fun K => g (N K) / (K : ℝ)) atTop (𝓝 a) := by
    intro g hg
    have hp := (hg.comp hNK_atTop).mul hrat
    rw [one_mul] at hp
    refine hp.congr' ?_
    filter_upwards [hNK_atTop.eventually_ge_atTop 1] with K hNK1
    have hne : (N K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp
    field_simp [hne]
  exact ⟨hcongr_prod _ tendsto_theta_div_natCast, hcongr_prod _ tendsto_psi_div_natCast⟩

/-- Interval difference of `Chebyshev.theta` at natural endpoints. -/
lemma theta_natCast_sub_eq_sum_Icc {A B : ℕ} (hAB : A ≤ B) :
    Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ) =
      ∑ p ∈ (Icc (A + 1) B).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast]
  have hsub : (Icc 0 A).filter Nat.Prime ⊆ (Icc 0 B).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hAB)
  rw [← Finset.sum_sdiff hsub]
  have hsdiff : (Icc 0 B).filter Nat.Prime \ (Icc 0 A).filter Nat.Prime =
      (Icc (A + 1) B).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨_, hpB⟩, hp⟩, hnot⟩
      exact ⟨⟨by by_contra h; exact hnot ⟨⟨Nat.zero_le p, by omega⟩, hp⟩, hpB⟩, hp⟩
    · rintro ⟨⟨hpA, hpB⟩, hp⟩
      exact ⟨⟨⟨Nat.zero_le p, hpB⟩, hp⟩, fun h => by omega⟩
  rw [hsdiff]; ring

/-- Interval difference of `Chebyshev.psi` at natural endpoints. -/
lemma psi_natCast_sub_eq_sum_Icc {A B : ℕ} (hAB : A ≤ B) :
    Chebyshev.psi (B : ℝ) - Chebyshev.psi (A : ℝ) =
      ∑ k ∈ Icc (A + 1) B, (Λ k : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast]
  have hsub : Icc 0 A ⊆ Icc 0 B := Finset.Icc_subset_Icc_right hAB
  rw [← Finset.sum_sdiff hsub]
  have hsdiff : Icc 0 B \ Icc 0 A = Icc (A + 1) B := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  rw [hsdiff]; ring

/-- **Unconditional un-updated glued-matrix jump on `neutralWindow (3K + 1)`**: for all
sufficiently large `K`, at every block size `R ≥ 6` and every shift
`a ≤ (1 / 2000) √K − 40000`, the glued matrix `neutralWindow (3K + 1) R (6KR) + a I` has at least
two negative squares. -/
theorem eventually_two_le_hermNegIndex_neutralWindow_halfCutoff :
    ∀ᶠ K : ℕ in atTop, ∀ R : ℕ, 6 ≤ R → ∀ a : ℝ,
      a ≤ (1 / 2000 : ℝ) * Real.sqrt K - 40000 →
      2 ≤ hermNegIndex ((neutralWindow (3 * K + 1) R (6 * K * R) +
        Matrix.diagonal (fun _ : Fin (6 * K * R) => a)).map (↑) :
          Matrix (Fin (6 * K * R)) (Fin (6 * K * R)) ℂ) := by
  have h3K := (tendsto_theta_psi_linear (N := fun K => 3 * K) (a := 3) (C := 0)
    (by norm_num) le_rfl
    (Eventually.of_forall fun K => by push_cast; linarith)
    (Eventually.of_forall fun K => by push_cast; linarith)).1
  have h21K := tendsto_theta_psi_linear (N := fun K => 21 * K / 10) (a := 21 / 10) (C := 2)
    (by norm_num) (by norm_num)
    (Eventually.of_forall fun K => by
      have h1 : ((21 * K : ℕ) : ℝ) ≤ ((10 * (21 * K / 10) + 10 : ℕ) : ℝ) := by
        exact_mod_cast (show 21 * K ≤ 10 * (21 * K / 10) + 10 by omega)
      push_cast at h1; linarith)
    (Eventually.of_forall fun K => by
      have h1 : ((10 * (21 * K / 10) : ℕ) : ℝ) ≤ ((21 * K : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_le (21 * K) 10)
      push_cast at h1; linarith)
  have h23K := (tendsto_theta_psi_linear (N := fun K => 23 * K / 10 + 1) (a := 23 / 10) (C := 2)
    (by norm_num) (by norm_num)
    (Eventually.of_forall fun K => by
      have h1 : ((23 * K : ℕ) : ℝ) ≤ ((10 * (23 * K / 10 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show 23 * K ≤ 10 * (23 * K / 10 + 1) by omega)
      push_cast at h1; linarith)
    (Eventually.of_forall fun K => by
      have h1 : ((10 * (23 * K / 10) : ℕ) : ℝ) ≤ ((23 * K : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_le (23 * K) 10)
      push_cast at h1; linarith)).1
  have h15K := (tendsto_theta_psi_linear (N := fun K => 3 * K / 2) (a := 3 / 2) (C := 2)
    (by norm_num) (by norm_num)
    (Eventually.of_forall fun K => by
      have h1 : ((3 * K : ℕ) : ℝ) ≤ ((2 * (3 * K / 2) + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 3 * K ≤ 2 * (3 * K / 2) + 2 by omega)
      push_cast at h1; linarith)
    (Eventually.of_forall fun K => by
      have h1 : ((2 * (3 * K / 2) : ℕ) : ℝ) ≤ ((3 * K : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_le (3 * K) 2)
      push_cast at h1; linarith)).2
  have hev1 : ∀ᶠ K in atTop,
      (84 / 100 : ℝ) < (Chebyshev.theta ((3 * K : ℕ) : ℝ) -
        Chebyshev.theta ((21 * K / 10 : ℕ) : ℝ)) / (K : ℝ) := by
    have ht : Tendsto (fun K : ℕ =>
        (Chebyshev.theta ((3 * K : ℕ) : ℝ) -
          Chebyshev.theta ((21 * K / 10 : ℕ) : ℝ)) / (K : ℝ)) atTop (𝓝 (9 / 10)) := by
      have hsub := h3K.sub h21K.1
      rw [show (3 : ℝ) - 21 / 10 = 9 / 10 by norm_num] at hsub
      exact hsub.congr fun K => by ring
    exact (tendsto_order.1 ht).1 (84 / 100) (by norm_num)
  have hev2 : ∀ᶠ K in atTop,
      (60 / 100 : ℝ) < (Chebyshev.theta ((3 * K : ℕ) : ℝ) -
        Chebyshev.theta ((23 * K / 10 + 1 : ℕ) : ℝ)) / (K : ℝ) := by
    have ht : Tendsto (fun K : ℕ =>
        (Chebyshev.theta ((3 * K : ℕ) : ℝ) -
          Chebyshev.theta ((23 * K / 10 + 1 : ℕ) : ℝ)) / (K : ℝ)) atTop (𝓝 (7 / 10)) := by
      have hsub := h3K.sub h23K
      rw [show (3 : ℝ) - 23 / 10 = 7 / 10 by norm_num] at hsub
      exact hsub.congr fun K => by ring
    exact (tendsto_order.1 ht).1 (60 / 100) (by norm_num)
  have hev3 : ∀ᶠ K in atTop,
      (Chebyshev.psi ((21 * K / 10 : ℕ) : ℝ) -
        Chebyshev.psi ((3 * K / 2 : ℕ) : ℝ)) / (K : ℝ) < 63 / 100 := by
    have ht : Tendsto (fun K : ℕ =>
        (Chebyshev.psi ((21 * K / 10 : ℕ) : ℝ) -
          Chebyshev.psi ((3 * K / 2 : ℕ) : ℝ)) / (K : ℝ)) atTop (𝓝 (6 / 10)) := by
      have hsub := h21K.2.sub h15K
      rw [show (21 / 10 : ℝ) - 3 / 2 = 6 / 10 by norm_num] at hsub
      exact hsub.congr fun K => by ring
    exact (tendsto_order.1 ht).2 (63 / 100) (by norm_num)
  filter_upwards [eventually_ge_atTop 200, hev1, hev2, hev3] with K hK h1 h2 h3 R hR a ha
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have h3Kpos : (0 : ℝ) < 3 * (K : ℝ) := by positivity
  -- Convert endpoint `θ` and `ψ` bounds into harmonic prime/prime-power sums.
  have hS₁ : (28 / 100 : ℝ) ≤
      ∑ p ∈ (Icc (21 * K / 10 + 1) (3 * K)).filter Nat.Prime, Real.log p / p := by
    rw [theta_natCast_sub_eq_sum_Icc (by omega)] at h1
    have hsum_lo : (84 / 100 : ℝ) * K ≤
        ∑ p ∈ (Icc (21 * K / 10 + 1) (3 * K)).filter Nat.Prime, Real.log p := by
      have := (lt_div_iff₀ hKpos).mp h1
      linarith
    have hpt : ∀ p ∈ (Icc (21 * K / 10 + 1) (3 * K)).filter Nat.Prime,
        Real.log p / (3 * (K : ℝ)) ≤ Real.log p / p := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpI, hpP⟩
      have hp_hi : (p : ℝ) ≤ 3 * (K : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hpI).2
      exact div_le_div_of_nonneg_left
        (Real.log_nonneg (by exact_mod_cast hpP.one_lt.le))
        (by exact_mod_cast hpP.pos) hp_hi
    have hdiv := (div_le_div_of_nonneg_right hsum_lo h3Kpos.le).trans
      ((Finset.sum_div _ _ _).symm.le.trans (Finset.sum_le_sum hpt))
    have hval : ((84 / 100 : ℝ) * K) / (3 * (K : ℝ)) = 28 / 100 := by
      field_simp [hKpos.ne']; norm_num
    linarith
  have hS₂ : (20 / 100 : ℝ) ≤
      ∑ p ∈ (Icc (23 * K / 10 + 2) (3 * K)).filter Nat.Prime, Real.log p / p := by
    rw [theta_natCast_sub_eq_sum_Icc (by omega)] at h2
    have hsum_lo : (60 / 100 : ℝ) * K ≤
        ∑ p ∈ (Icc (23 * K / 10 + 2) (3 * K)).filter Nat.Prime, Real.log p := by
      have := (lt_div_iff₀ hKpos).mp h2
      linarith
    have hpt : ∀ p ∈ (Icc (23 * K / 10 + 2) (3 * K)).filter Nat.Prime,
        Real.log p / (3 * (K : ℝ)) ≤ Real.log p / p := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpI, hpP⟩
      have hp_hi : (p : ℝ) ≤ 3 * (K : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hpI).2
      exact div_le_div_of_nonneg_left
        (Real.log_nonneg (by exact_mod_cast hpP.one_lt.le))
        (by exact_mod_cast hpP.pos) hp_hi
    have hdiv := (div_le_div_of_nonneg_right hsum_lo h3Kpos.le).trans
      ((Finset.sum_div _ _ _).symm.le.trans (Finset.sum_le_sum hpt))
    have hval : ((60 / 100 : ℝ) * K) / (3 * (K : ℝ)) = 20 / 100 := by
      field_simp [hKpos.ne']; norm_num
    linarith
  have hC : ∑ k ∈ Icc (3 * K / 2 + 1) (21 * K / 10), (Λ k : ℝ) / k ≤ 42 / 100 := by
    rw [psi_natCast_sub_eq_sum_Icc (by omega)] at h3
    have hsum_hi : ∑ k ∈ Icc (3 * K / 2 + 1) (21 * K / 10), (Λ k : ℝ) ≤ (63 / 100 : ℝ) * K := by
      have := (div_lt_iff₀ hKpos).mp h3
      linarith
    have h15pos : (0 : ℝ) < (3 / 2 : ℝ) * K := by positivity
    have hpt : ∀ k ∈ Icc (3 * K / 2 + 1) (21 * K / 10),
        (Λ k : ℝ) / k ≤ (Λ k : ℝ) / ((3 / 2 : ℝ) * K) := by
      intro k hk
      have hk_lo_nat : 3 * K ≤ 2 * k := by
        have := (Finset.mem_Icc.mp hk).1; omega
      have hk_lo : (3 / 2 : ℝ) * K ≤ k := by
        have hr : ((3 * K : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hk_lo_nat
        push_cast at hr; linarith
      exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg h15pos hk_lo
    have hdiv := (Finset.sum_le_sum hpt).trans
      ((Finset.sum_div _ _ _).symm.le.trans (div_le_div_of_nonneg_right hsum_hi h15pos.le))
    have hval : ((63 / 100 : ℝ) * K) / ((3 / 2 : ℝ) * K) = 42 / 100 := by
      field_simp [hKpos.ne']; norm_num
    linarith
  exact two_le_hermNegIndex_neutralWindow_halfCutoff_of_primeSums hK hR hS₁ hS₂ hC ha

/-- Any drop `hermNegIndex (B.map (↑)) < hermNegIndex (A.map (↑))` between real matrices exposes a
nonzero real vector `v` with `0 < v ⬝ᵥ ((B - A) *ᵥ v)`. -/
lemma exists_real_vec_of_hermNegIndex_lt {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℝ}
    (hlt : hermNegIndex (B.map (↑) : Matrix ι ι ℂ) <
      hermNegIndex (A.map (↑) : Matrix ι ι ℂ)) :
    ∃ v : ι → ℝ, v ≠ 0 ∧ 0 < v ⬝ᵥ ((B - A) *ᵥ v) := by
  obtain ⟨W, hrank, hW⟩ :=
    exists_isPosDefOn_finrank_eq_posIndex (-(A.map (↑) : Matrix ι ι ℂ))
  have hnot : ¬ IsPosDefOn (-(B.map (↑) : Matrix ι ι ℂ)) W := by
    intro hBW
    have hle : Module.finrank ℂ W ≤ hermNegIndex (B.map (↑) : Matrix ι ι ℂ) :=
      finrank_le_posIndex hBW
    change Module.finrank ℂ W = hermNegIndex (A.map (↑) : Matrix ι ι ℂ) at hrank
    omega
  unfold IsPosDefOn at hnot
  push Not at hnot
  obtain ⟨c, hcW, hc0, hBc⟩ := hnot
  have hAc := hW c hcW hc0
  rw [hermQuad_neg] at hAc hBc
  have hdiff : 0 < hermQuad (B.map (↑)) c - hermQuad (A.map (↑)) c := by linarith
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, HeckeKreinToeplitz.hermQuad_map_ofReal] at hdiff
  set x : ι → ℝ := fun i => (c i).re
  set y : ι → ℝ := fun i => (c i).im
  have hsub_eq : ∀ z : ι → ℝ, z ⬝ᵥ ((B - A) *ᵥ z) = z ⬝ᵥ (B *ᵥ z) - z ⬝ᵥ (A *ᵥ z) := fun z => by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  have hxy : 0 < x ⬝ᵥ ((B - A) *ᵥ x) + y ⬝ᵥ ((B - A) *ᵥ y) := by
    rw [hsub_eq x, hsub_eq y]; linarith
  by_cases hx : 0 < x ⬝ᵥ ((B - A) *ᵥ x)
  · refine ⟨x, ?_, hx⟩
    rintro h0; simp [h0] at hx
  · have hy : 0 < y ⬝ᵥ ((B - A) *ᵥ y) := by linarith
    refine ⟨y, ?_, hy⟩
    rintro h0; simp [h0] at hy

/-- **Single-step top-octave cancellation forced by any `DoublingLaw ρ lam` with `1 < lam < √2`**:
along any block-size law `ρ` with `ρ(K) ≥ 6`, if `DoublingLaw ρ lam` holds with `1 < lam < √2`,
then for all sufficiently large `K`, at `R := ρ (2K)` the un-updated glued matrix
`neutralWindow (3K + 1) R (6KR)` has `hermNegIndex ≥ 2` at shift `(1 / 2000) √K − 40000`, while
`neutralWindow (6K + 1) R (6KR)` has `hermNegIndex ≤ 1` at shift `(1 / 4000) √K − 40000`, forcing a
nonzero real state `v` on which the fresh prime octave `[3K + 2, 6K + 1]` satisfies
`∑_{k = 3K + 2}^{6K + 1} v ⬝ᵥ (windowMatrix (floorGraph k) R (6KR) *ᵥ v) < -(√K / 4000) (v ⬝ᵥ v)`. -/
theorem topOctave_jump_of_doublingLaw_lt_sqrt_two {ρ : ℕ → ℕ} (hρ : ∀ K, 1 ≤ K → 6 ≤ ρ K)
    {lam : ℝ} (hlam1 : 1 < lam) (hlam2 : lam < Real.sqrt 2) (hdoub : DoublingLaw ρ lam) :
    ∀ᶠ K : ℕ in atTop,
      let R := ρ (2 * K)
      2 ≤ hermNegIndex ((neutralWindow (3 * K + 1) R (6 * K * R) +
        Matrix.diagonal (fun _ : Fin (6 * K * R) => (1 / 2000 : ℝ) * Real.sqrt K - 40000)).map (↑) :
          Matrix (Fin (6 * K * R)) (Fin (6 * K * R)) ℂ) ∧
      hermNegIndex ((neutralWindow (6 * K + 1) R (6 * K * R) +
        Matrix.diagonal (fun _ : Fin (6 * K * R) => (1 / 4000 : ℝ) * Real.sqrt K - 40000)).map (↑) :
          Matrix (Fin (6 * K * R)) (Fin (6 * K * R)) ℂ) ≤ 1 ∧
      ∃ v : Fin (6 * K * R) → ℝ, v ≠ 0 ∧
        ∑ k ∈ Icc (3 * K + 2) (6 * K + 1),
          v ⬝ᵥ (windowMatrix (floorGraph k) R (6 * K * R) *ᵥ v) <
            -((1 / 4000 : ℝ) * Real.sqrt K) * (v ⬝ᵥ v) := by
  obtain ⟨a, c, hmono, hd, hlev⟩ := hdoub
  have hpow := le_rpow_logb_of_doubling hlam1 hmono hd
  set Cₐ : ℝ := max (lam * (|a 1| + 2 * |c| / (lam - 1))) 1
  set θ : ℝ := Real.logb 2 lam
  have hθ_pos : 0 < θ := Real.logb_pos (by norm_num) hlam1
  have hθ_lt : θ < 1 / 2 := by
    rw [← logb_two_sqrt_two]
    exact Real.logb_lt_logb (by norm_num) (by linarith) hlam2
  set δ : ℝ := 1 / 2 - θ
  have hδ_pos : 0 < δ := by linarith
  have htend_2K : Tendsto (fun K : ℕ => ((2 * K : ℕ) : ℝ) ^ δ) atTop atTop := by
    have hlin : Tendsto (fun K : ℕ => ((2 * K : ℕ) : ℝ)) atTop atTop :=
      (Filter.Tendsto.const_mul_atTop zero_lt_two tendsto_natCast_atTop_atTop).congr
        fun K => by push_cast; rfl
    exact (tendsto_rpow_atTop hδ_pos).comp hlin
  filter_upwards [eventually_ge_atTop 1,
    htend_2K.eventually_gt_atTop (8000 * (Cₐ + 40001)),
    eventually_two_le_hermNegIndex_neutralWindow_halfCutoff] with K hK1 hlarge htwo_all
  set R : ℕ := ρ (2 * K)
  have h2K1 : 1 ≤ 2 * K := by omega
  have hR6 : 6 ≤ R := hρ (2 * K) h2K1
  have htwo := htwo_all R hR6 ((1 / 2000 : ℝ) * Real.sqrt K - 40000) le_rfl
  -- Bound `a (2 * K) ≤ (1 / 4000) * √K - 40000`.
  have h2K_pos : (0 : ℝ) < ((2 * K : ℕ) : ℝ) := by exact_mod_cast h2K1
  have h2K_θ : 1 ≤ ((2 * K : ℕ) : ℝ) ^ θ :=
    Real.one_le_rpow (by exact_mod_cast h2K1) hθ_pos.le
  have hprod : ((2 * K : ℕ) : ℝ) ^ δ * ((2 * K : ℕ) : ℝ) ^ θ = Real.sqrt 2 * Real.sqrt K := by
    rw [← Real.rpow_add h2K_pos, show δ + θ = 1 / 2 by dsimp [δ]; ring, ← Real.sqrt_eq_rpow,
      Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul zero_le_two]
  have ha2K_pow : a (2 * K) ≤ Cₐ * ((2 * K : ℕ) : ℝ) ^ θ := by
    have h1 := hpow (2 * K) h2K1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h2K_pos.le θ))
  have hs2_le : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq zero_le_two]
    exact Real.sqrt_le_sqrt (by norm_num)
  have ha2K_le : a (2 * K) ≤ (1 / 4000 : ℝ) * Real.sqrt K - 40000 := by
    have hmul := mul_le_mul_of_nonneg_right hlarge.le (Real.rpow_nonneg h2K_pos.le θ)
    rw [hprod] at hmul
    have hC1 : 1 ≤ Cₐ := le_max_right _ _
    have h1 : Cₐ + 40001 ≤ (Cₐ + 40001) * ((2 * K : ℕ) : ℝ) ^ θ := by nlinarith
    have h2 : Real.sqrt 2 * Real.sqrt K ≤ 2 * Real.sqrt K :=
      mul_le_mul_of_nonneg_right hs2_le (Real.sqrt_nonneg K)
    linarith
  have hcast_idx : ∀ (M₁ M₂ : ℕ), M₁ = M₂ →
      hermNegIndex ((neutralWindow (M₁ + 1) R (M₁ * R) +
        Matrix.diagonal (fun _ : Fin (M₁ * R) => a (2 * K))).map (↑) :
          Matrix (Fin (M₁ * R)) (Fin (M₁ * R)) ℂ) =
      hermNegIndex ((neutralWindow (M₂ + 1) R (M₂ * R) +
        Matrix.diagonal (fun _ : Fin (M₂ * R) => a (2 * K))).map (↑) :
          Matrix (Fin (M₂ * R)) (Fin (M₂ * R)) ℂ) := by
    rintro M₁ _ rfl; rfl
  have hlev2K : hermNegIndex ((neutralWindow (6 * K + 1) R (6 * K * R) +
      Matrix.diagonal (fun _ : Fin (6 * K * R) => a (2 * K))).map (↑) :
        Matrix (Fin (6 * K * R)) (Fin (6 * K * R)) ℂ) ≤ 1 := by
    rw [← hcast_idx (3 * (2 * K)) (6 * K) (by omega)]
    exact hlev (2 * K) h2K1
  have hone : hermNegIndex ((neutralWindow (6 * K + 1) R (6 * K * R) +
      Matrix.diagonal (fun _ : Fin (6 * K * R) => (1 / 4000 : ℝ) * Real.sqrt K - 40000)).map (↑) :
        Matrix (Fin (6 * K * R)) (Fin (6 * K * R)) ℂ) ≤ 1 :=
    (hermNegIndex_add_diagonal_mono (neutralWindow (6 * K + 1) R (6 * K * R)) ha2K_le).trans hlev2K
  refine ⟨htwo, hone, ?_⟩
  obtain ⟨v, hv0, hv_pos⟩ := exists_real_vec_of_hermNegIndex_lt (lt_of_le_of_lt hone htwo)
  refine ⟨v, hv0, ?_⟩
  have hdecomp := (neutralWindow_doubling_topOctave_decomposition (K := K) (R := R) (by omega)).1
  -- Expand `v ⬝ᵥ ((B - A) *ᵥ v)` using `hdecomp`.
  have hBA : (neutralWindow (6 * K + 1) R (6 * K * R) +
      Matrix.diagonal (fun _ : Fin (6 * K * R) => (1 / 4000 : ℝ) * Real.sqrt K - 40000)) -
      (neutralWindow (3 * K + 1) R (6 * K * R) +
        Matrix.diagonal (fun _ : Fin (6 * K * R) => (1 / 2000 : ℝ) * Real.sqrt K - 40000)) =
      -(∑ k ∈ Icc (3 * K + 2) (6 * K + 1), windowMatrix (floorGraph k) R (6 * K * R)) -
        Matrix.diagonal (fun _ : Fin (6 * K * R) => (1 / 4000 : ℝ) * Real.sqrt K) := by
    rw [hdecomp]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  rw [hBA, Matrix.sub_mulVec, Matrix.neg_mulVec, dotProduct_sub, dotProduct_neg] at hv_pos
  have hdiag_v : v ⬝ᵥ ((Matrix.diagonal fun _ : Fin (6 * K * R) =>
      (1 / 4000 : ℝ) * Real.sqrt K) *ᵥ v) =
      ((1 / 4000 : ℝ) * Real.sqrt K) * (v ⬝ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum_v : v ⬝ᵥ ((∑ k ∈ Icc (3 * K + 2) (6 * K + 1),
      windowMatrix (floorGraph k) R (6 * K * R)) *ᵥ v) =
      ∑ k ∈ Icc (3 * K + 2) (6 * K + 1),
        v ⬝ᵥ (windowMatrix (floorGraph k) R (6 * K * R) *ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [hdiag_v, hsum_v] at hv_pos
  linarith

/-- **Exact `< 2^{3/8}` characterization**: along any polynomial block-size schedule
`K¹⁰ ≤ ρ(K) ≤ K^A`, a doubling law with factor `1 < lam < 2^{3/8}` exists if and only if
`zetaZeroWidth < 3 / 8`. -/
theorem exists_doublingLaw_lt_two_rpow_three_eighths_iff {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K)
    {A : ℕ} (hρA : ∀ K, ρ K ≤ K ^ A) :
    (∃ lam : ℝ, 1 < lam ∧ lam < (2 : ℝ) ^ (3 / 8 : ℝ) ∧ DoublingLaw ρ lam) ↔
      zetaZeroWidth < 3 / 8 := by
  constructor
  · rintro ⟨lam, h1, hlt, hd⟩
    have hw := zetaZeroWidth_le_logb_of_doublingLaw hρ h1 hd
    have hlog : Real.logb 2 lam < 3 / 8 := by
      have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by linarith) hlt
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h
    exact hw.trans_lt hlog
  · intro hw
    have hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K := fun K hK => (Nat.one_le_pow 10 K hK).trans (hρ K)
    have hw0 := zetaZeroWidth_nonneg
    set β : ℝ := (zetaZeroWidth + 3 / 8) / 2
    refine ⟨(2 : ℝ) ^ β, Real.one_lt_rpow (by norm_num) (by dsimp [β]; linarith),
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by dsimp [β]; linarith),
      doublingLaw_of_zetaZeroWidth_lt hρ₁ hρA (by dsimp [β]; linarith)⟩

/-- **Zero-free half-plane consequence of any doubling law**: along `K¹⁰ ≤ ρ(K)`, a doubling law
with factor `lam > 1` forces `riemannZeta s ≠ 0` on the entire open half-plane
`Re s > 1 / 2 + log₂ lam`. -/
theorem riemannZeta_ne_zero_of_doublingLaw {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K) {lam : ℝ}
    (hlam : 1 < lam) (hd : DoublingLaw ρ lam) {s : ℂ}
    (hs_re : 1 / 2 + Real.logb 2 lam < s.re) :
    riemannZeta s ≠ 0 := by
  intro hs0
  rcases le_or_gt 1 s.re with h1 | hlt1
  · exact riemannZeta_ne_zero_of_one_le_re h1 hs0
  · have hlog_nonneg : 0 ≤ Real.logb 2 lam := Real.logb_nonneg (by norm_num) hlam.le
    have hmem : s ∈ zetaZeroConfig.carrier :=
      show IsNontrivialZero s from ⟨hs0, by linarith, hlt1⟩
    have hw := (zetaZeroWidth_le_iff_re_le hlog_nonneg).mp
      (zetaZeroWidth_le_logb_of_doublingLaw hρ hlam hd) s hmem
    linarith

/-- **Sub-`7/8` zero-free half-plane corollary**: any doubling law with factor
`1 < lam < 2^{3/8}` along `K¹⁰ ≤ ρ(K)` yields a zero-free half-plane `Re s > 1/2 + log₂ lam` with
abscissa strictly below `7/8`. -/
theorem zero_free_below_seven_eighths_of_doublingLaw {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K)
    {lam : ℝ} (hlam1 : 1 < lam) (hlam2 : lam < (2 : ℝ) ^ (3 / 8 : ℝ))
    (hd : DoublingLaw ρ lam) :
    1 / 2 + Real.logb 2 lam < 7 / 8 ∧
      ∀ s : ℂ, 1 / 2 + Real.logb 2 lam < s.re → riemannZeta s ≠ 0 := by
  refine ⟨?_, fun _ hs => riemannZeta_ne_zero_of_doublingLaw hρ hlam1 hd hs⟩
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by linarith) hlam2
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at h
  linarith

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
