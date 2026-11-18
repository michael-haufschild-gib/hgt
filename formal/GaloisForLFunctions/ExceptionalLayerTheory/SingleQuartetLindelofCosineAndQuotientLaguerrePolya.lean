import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion
import GaloisForLFunctions.RHTower.LindelofCosineFiniteDefectDepth
import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine
import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointCriterion
import GaloisForLFunctions.RHTower.OrderOneEvenLaguerrePolya
import GaloisForLFunctions.RHTower.DeBruijnNewmanCosineShift
import GaloisForLFunctions.RHTower.XiRealRootedPolynomialPreimage
import GaloisForLFunctions.HTGeometry.RealTaylorCoefficients

/-!
# Lindelöf Law, Cosine-Producer Transition, and Quotient Laguerre–Pólya Factorization of a Single Quartet

This module establishes three unconditional structural consequences of a single off-line quartet
`HasSingleOffLineQuartet ρ₀` across vertical growth (`LindelofCriticalLine`), the lossless cosine
producer `cosProducer h` (`cos(hD)Ξ`), and the global Hadamard–Jensen structure of `Ξ`:

1. **Full Lindelöf conjecture and contrapositive separation**
   (`zerosApproachLine_of_singleQuartet`, `lindelof_all_forms_of_singleQuartet`,
   `not_hasSingleOffLineQuartet_of_not_lindelof`, `infinite_offLine_of_not_lindelof`,
   `singleQuartet_or_lindelof_without_rh`):
   Every single-quartet world satisfies `LindelofCriticalLine`, `LindelofHalfPlane`, and
   `LindelofOpen` despite violating `RiemannHypothesis`. Any failure of the Lindelöf conjecture
   immediately excludes `HasSingleOffLineQuartet ρ₀` for every `ρ₀ ∈ ℂ` and forces infinitely many
   off-line zeros.

2. **Cosine-producer Laguerre–Pólya phase boundary and confined exceptional points**
   (`laguerrePolya_cosProducer_of_singleQuartet_ge`,
   `exists_lt_not_laguerrePolya_cosProducer_of_singleQuartet`,
   `cosProducer_real_and_simple_of_singleQuartet_gt`,
   `cosProducer_apex_pinning_of_singleQuartet`,
   `exists_confined_exceptionalPoint_of_singleQuartet`):
   Under `HasSingleOffLineQuartet ρ₀` with depth `δ₀ = Re ρ₀ - 1/2`:
   - `cosProducer h ∈ LaguerrePolya` holds for all `h ≥ δ₀` (with all real zeros simple when
     `h > δ₀`), while for every `ε > 0` there exists `0 < b < min ε δ₀` where
     `¬ LaguerrePolya (cosProducer b)`.
   - At `h = δ₀`, `cosProducer δ₀ (±Im ρ₀) = 0`, every zero is real, and every zero with
     `|x| ≠ |Im ρ₀|` is simple.
   - An exceptional point `(h_*, x_*)` (`cosProducer h_* x_* = deriv (cosProducer h_*) x_* = 0`)
     exists inside the defect semicircle `(|x_*| - |Im ρ₀|)² + h_*² ≤ δ₀² ≤ (8999/24000)²`, with
     `0 < h_* ≤ δ₀` and `|x_*| > 3`.

3. **Quotient Laguerre–Pólya factorization and all-degree real-rooted quotient Jensen polynomials**
   (`exists_quotient_laguerrePolya_of_singleQuartet`):
   With `z₀ = Im ρ₀ - i(Re ρ₀ - 1/2)`, `XiC` factors globally on `ℂ` as
   `XiC z = ((z² - z₀²)(z² - (conj z₀)²))^k * Ξ_♭ z` for an integer `k ≥ 1` and an even
   Schwarz-real entire function `Ξ_♭` nonvanishing at `{z₀, -z₀, conj z₀, -conj z₀}` and `0`, such
   that `LaguerrePolya Ξ_♭` holds and every Jensen polynomial `jensenPoly (realTaylorCoeff (deriv^[r] Ξ_♭)) d`
   (`r, d : ℕ`) splits over `ℝ`.
-/

noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology Metric Polynomial Zeta23
open scoped ComplexConjugate
open GaloisForLFunctions.ExclusionOfTheCriticalState
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ## 1. Full Lindelöf conjecture and separation laws under a single off-line quartet -/

/-- Under `HasSingleOffLineQuartet ρ₀`, the zeros of `ξ` approach the critical line. -/
theorem zerosApproachLine_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    RHTower.BacklundConverse.ZerosApproachLine :=
  RHTower.BacklundConverse.zerosApproachLine_of_finiteOffLine hq.finiteOffLine

/-- **Single-quartet Lindelöf theorem.** Under `HasSingleOffLineQuartet ρ₀`, all three standard
forms of the Lindelöf conjecture hold (`LindelofCriticalLine`, `LindelofHalfPlane`, `LindelofOpen`). -/
theorem lindelof_all_forms_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    RHTower.LindelofSparse.LindelofCriticalLine ∧
      RHTower.LindelofSparse.LindelofHalfPlane ∧
      RHTower.BacklundConverse.LindelofOpen := by
  have hCL : RHTower.LindelofSparse.LindelofCriticalLine :=
    RHTower.BacklundConverse.lindelofCriticalLine_of_zerosApproachLine
      (zerosApproachLine_of_singleQuartet hq)
  exact ⟨hCL, RHTower.LindelofSparse.lindelofHalfPlane_of_criticalLine hCL,
    RHTower.BacklundConverse.lindelofCriticalLine_iff_lindelofOpen.mp hCL⟩

/-- **Contrapositive exclusion.** Any failure of the Lindelöf conjecture on the critical line
excludes `HasSingleOffLineQuartet ρ₀` for every `ρ₀ ∈ ℂ`. -/
theorem not_hasSingleOffLineQuartet_of_not_lindelof
    (hnot : ¬ RHTower.LindelofSparse.LindelofCriticalLine) :
    ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ :=
  fun _ hq => hnot (lindelof_all_forms_of_singleQuartet hq).1

/-- Any failure of the Lindelöf conjecture forces infinitely many off-line zero copies of `ξ`. -/
theorem infinite_offLine_of_not_lindelof
    (hnot : ¬ RHTower.LindelofSparse.LindelofCriticalLine) :
    {q : RHTower.XiZeroCopy | (RHTower.xiSpectralPoint q).im ≠ 0}.Infinite :=
  fun hfin => hnot (RHTower.BacklundConverse.lindelofCriticalLine_of_zerosApproachLine
    (RHTower.BacklundConverse.zerosApproachLine_of_finiteOffLine hfin))

/-- **Unconditional single-quartet vs. Lindelöf–RH separation.** Either no single off-line quartet
exists anywhere in `ℂ`, or the Lindelöf conjecture holds on the closed right half-plane `Re s ≥ 1/2`
while `RiemannHypothesis` fails. -/
theorem singleQuartet_or_lindelof_without_rh :
    (∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀) ∨
      (RHTower.LindelofSparse.LindelofCriticalLine ∧
        RHTower.LindelofSparse.LindelofHalfPlane ∧
        ¬ RiemannHypothesis) := by
  by_cases h : ∃ ρ₀ : ℂ, HasSingleOffLineQuartet ρ₀
  · obtain ⟨ρ₀, hq⟩ := h
    obtain ⟨hCL, hHP, -⟩ := lindelof_all_forms_of_singleQuartet hq
    exact Or.inr ⟨hCL, hHP, hq.not_riemannHypothesis⟩
  · exact Or.inl (not_exists.mp h)

/-! ## 2. Spectral zero classification and cosine-producer transition at `δ₀ = Re ρ₀ - 1/2` -/

/-- Centred spectral root `z₀ = Im ρ₀ - i (Re ρ₀ - 1/2)` of `XiC` attached to `ρ₀`. -/
def quartetSpectralRoot (ρ₀ : ℂ) : ℂ :=
  (ρ₀.im : ℂ) - ((ρ₀.re - 1 / 2 : ℝ) : ℂ) * I

private theorem half_add_quartetSpectralRoot_mul_I (ρ₀ : ℂ) :
    (1 / 2 : ℂ) + quartetSpectralRoot ρ₀ * I = ρ₀ := by
  unfold quartetSpectralRoot
  apply Complex.ext <;> simp [sub_eq_add_neg]

private theorem xiZeroCopy_mem_carrier (q : RHTower.XiZeroCopy) :
    (q.1 : ℂ) ∈ zetaZeroConfig.carrier := by
  have h0 := RHTower.xiZeroCopy_re_pos q
  have h1 := RHTower.xiZeroCopy_re_lt_one q
  have hne1 : (q.1 : ℂ) ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
    (RHTower.xi_eq_zero_of_mem_divisor_support q.1)
  exact ⟨hζ, h0, h1⟩

private theorem mem_zeroQuartetSet_coord {ρ₀ ρ : ℂ} (hρ : ρ ∈ zeroQuartetSet ρ₀) :
    |ρ.im| = |ρ₀.im| ∧ (ρ.re = ρ₀.re ∨ ρ.re = 1 - ρ₀.re) := by
  simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨by simp, Or.inl (Complex.conj_re ρ₀)⟩
  · exact ⟨by simp, Or.inr (by simp)⟩
  · exact ⟨by simp, Or.inr (by simp)⟩

/-- Under `HasSingleOffLineQuartet ρ₀`, every `q : XiZeroCopy` satisfies
`|(xiSpectralPoint q).im| ≤ ρ₀.re - 1/2`. -/
theorem abs_xiSpectralPoint_im_le_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (q : RHTower.XiZeroCopy) :
    |(RHTower.xiSpectralPoint q).im| ≤ ρ₀.re - 1 / 2 := by
  have him : (RHTower.xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [RHTower.xiSpectralPoint, Complex.mul_im]
  rw [him]
  by_cases hhalf : (q.1 : ℂ).re = 1 / 2
  · rw [hhalf, sub_self, abs_zero]
    linarith [hq.1]
  · have hmem : (q.1 : ℂ) ∈ zeroQuartetSet ρ₀ := by
      rw [← hq.2.2]
      exact ⟨xiZeroCopy_mem_carrier q, hhalf⟩
    rcases (mem_zeroQuartetSet_coord hmem).2 with hre | hre
    · rw [hre, show (1 : ℝ) / 2 - ρ₀.re = -(ρ₀.re - 1 / 2) by ring, abs_neg,
        abs_of_pos (by linarith [hq.1])]
    · rw [hre, show (1 : ℝ) / 2 - (1 - ρ₀.re) = ρ₀.re - 1 / 2 by ring,
        abs_of_pos (by linarith [hq.1])]

/-- Complete classification of zeros of `XiC` under `HasSingleOffLineQuartet ρ₀`: every zero `w`
is either real (`w.im = 0`) or lies in `{z₀, -z₀, conj z₀, -conj z₀}` with `|w.re| = |ρ₀.im|` and
`|w.im| = ρ₀.re - 1/2`. -/
theorem XiC_eq_zero_classification_of_singleQuartet {ρ₀ w : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hw : RHTower.XiC w = 0) :
    w.im = 0 ∨
      (|w.re| = |ρ₀.im| ∧ |w.im| = ρ₀.re - 1 / 2 ∧
        w ∈ ({quartetSpectralRoot ρ₀, -quartetSpectralRoot ρ₀,
          conj (quartetSpectralRoot ρ₀), -conj (quartetSpectralRoot ρ₀)} : Set ℂ)) := by
  by_cases him : w.im = 0
  · exact Or.inl him
  · right
    have hxi : RHTower.xi (1 / 2 + w * I) = 0 := hw
    obtain ⟨q, hq_eq⟩ := RHTower.exists_xiZeroCopy_of_xi_eq_zero hxi
    have hs_car : (1 / 2 : ℂ) + w * I ∈ zetaZeroConfig.carrier := by
      rw [← hq_eq]; exact xiZeroCopy_mem_carrier q
    have hs_re : ((1 / 2 : ℂ) + w * I).re = 1 / 2 - w.im := by simp; ring
    have hs_im : ((1 / 2 : ℂ) + w * I).im = w.re := by simp
    have hs_ne : ((1 / 2 : ℂ) + w * I).re ≠ 1 / 2 := by
      rw [hs_re]; intro h; exact him (by linarith)
    have hmem : (1 / 2 : ℂ) + w * I ∈ zeroQuartetSet ρ₀ := by
      rw [← hq.2.2]; exact ⟨hs_car, hs_ne⟩
    obtain ⟨hre_abs, hre_or⟩ := mem_zeroQuartetSet_coord hmem
    rw [hs_im] at hre_abs
    rw [hs_re] at hre_or
    have hw_im_abs : |w.im| = ρ₀.re - 1 / 2 := by
      rcases hre_or with h1 | h1
      · have : w.im = -(ρ₀.re - 1 / 2) := by linarith
        rw [this, abs_neg, abs_of_pos (by linarith [hq.1])]
      · have : w.im = ρ₀.re - 1 / 2 := by linarith
        rw [this, abs_of_pos (by linarith [hq.1])]
    refine ⟨hre_abs, hw_im_abs, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases abs_eq_abs.mp hre_abs with hre_pos | hre_neg <;>
      rcases hre_or with him_neg | him_pos
    · left
      apply Complex.ext
      · simp [quartetSpectralRoot, hre_pos]
      · simp [quartetSpectralRoot]; linarith
    · right; right; left
      apply Complex.ext
      · simp [quartetSpectralRoot, hre_pos]
      · simp [quartetSpectralRoot]; linarith
    · right; right; right
      apply Complex.ext
      · simp [quartetSpectralRoot, hre_neg]
      · simp [quartetSpectralRoot]; linarith
    · right; left
      apply Complex.ext
      · simp [quartetSpectralRoot, hre_neg]
      · simp [quartetSpectralRoot]; linarith

/-- Under `HasSingleOffLineQuartet ρ₀`, `deepCopies h = ∅` for every `h ≥ Re ρ₀ - 1/2`. -/
theorem deepCopies_eq_empty_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {h : ℝ} (hh : ρ₀.re - 1 / 2 ≤ h) :
    RHTower.CosineDefectBudget.deepCopies h = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun q hq_deep => ?_
  have hlt : h < (RHTower.xiSpectralPoint q).im := hq_deep
  have hle := (le_abs_self _).trans (abs_xiSpectralPoint_im_le_of_singleQuartet hq q)
  linarith

/-- **Cosine-producer Laguerre–Pólya theorem above the quartet depth.** Under
`HasSingleOffLineQuartet ρ₀`, `cosProducer h` lies in the Laguerre–Pólya class for every
`h ≥ Re ρ₀ - 1/2` (including the apex `h = Re ρ₀ - 1/2`). -/
theorem laguerrePolya_cosProducer_of_singleQuartet_ge {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {h : ℝ} (hh : ρ₀.re - 1 / 2 ≤ h) :
    LaguerrePolya (RHTower.cosProducer h) := by
  let hn : ℕ → ℝ := fun n => h + 1 / ((n : ℝ) + 1)
  have hLP_n : ∀ n : ℕ, LaguerrePolya (RHTower.cosProducer (hn n)) := by
    intro n
    have hstep : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine RHTower.laguerrePolya_cosineShiftXi_of_im_gt fun q => ?_
    have hle := neg_abs_le (RHTower.xiSpectralPoint q).im
    have habs := abs_xiSpectralPoint_im_le_of_singleQuartet hq q
    dsimp [hn]
    linarith
  have hlim : Tendsto hn atTop (𝓝 h) := by
    have h0 : Tendsto (fun n : ℕ => h + 1 / ((n : ℝ) + 1)) atTop (𝓝 (h + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [add_zero] at h0
  have hconv : TendstoLocallyUniformly (fun n => RHTower.cosProducer (hn n))
      (RHTower.cosProducer h) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp
      (RHTower.tendstoLocallyUniformly_cosProducer h)) K hK
    exact Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
      hlim.eventually (Metric.tendstoUniformlyOn_iff.mp hu ε hε)
  exact LaguerrePolya.of_tendstoLocallyUniformly hLP_n hconv

/-- **Failure of Laguerre–Pólya membership at arbitrarily small shifts.** Under
`HasSingleOffLineQuartet ρ₀`, for every `ε > 0` there exists `b ∈ (0, min ε (Re ρ₀ - 1/2))` such
that `¬ LaguerrePolya (cosProducer b)`. -/
theorem exists_lt_not_laguerrePolya_cosProducer_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ b < min ε (ρ₀.re - 1 / 2) ∧ ¬ LaguerrePolya (RHTower.cosProducer b) := by
  set δ₁ : ℝ := min ε (ρ₀.re - 1 / 2)
  have hδ₁ : 0 < δ₁ := lt_min hε (by linarith [hq.1])
  by_contra h_all
  push Not at h_all
  have hev : ∀ᶠ m : ℕ in atTop, 1 / ((m : ℝ) + 1) < δ₁ :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ₁)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let bk : ℕ → ℝ := fun k => 1 / (((k + N : ℕ) : ℝ) + 1)
  have hLP_k : ∀ k : ℕ, LaguerrePolya (RHTower.cosProducer (bk k)) := by
    intro k
    have hpos : 0 < bk k := by dsimp [bk]; positivity
    have hlt : bk k < δ₁ := hN (k + N) (by omega)
    exact h_all (bk k) hpos hlt
  have hconv : TendstoLocallyUniformly (fun k => RHTower.cosProducer (bk k))
      RHTower.XiC atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp
      RHTower.DeBruijn.tendstoLocallyUniformly_cosineShift_XiC) K hK
    exact Metric.tendstoUniformlyOn_iff.mpr fun ε' hε' =>
      (tendsto_add_atTop_nat N).eventually (Metric.tendstoUniformlyOn_iff.mp hu ε' hε')
  have hLP_Xi : LaguerrePolya RHTower.XiC :=
    LaguerrePolya.of_tendstoLocallyUniformly hLP_k hconv
  exact hq.not_riemannHypothesis (RHTower.riemannHypothesis_iff_laguerrePolya_XiC.mpr hLP_Xi)

/-- **Strict super-quartet simplicity.** For every `h > Re ρ₀ - 1/2`, every zero of `cosProducer h`
in `ℂ` is real and simple (`z.im = 0 ∧ deriv (cosProducer h) z ≠ 0`). -/
theorem cosProducer_real_and_simple_of_singleQuartet_gt {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {h : ℝ} (hh : ρ₀.re - 1 / 2 < h) {z : ℂ}
    (hz : RHTower.cosProducer h z = 0) :
    z.im = 0 ∧ deriv (RHTower.cosProducer h) z ≠ 0 := by
  have hh0 : 0 < h := by linarith [hq.1]
  have him0 : z.im = 0 :=
    RHTower.CosineDefectBudget.cosShiftXi_zero_im_eq_zero_of_no_deep
      (deepCopies_eq_empty_of_singleQuartet hq hh.le) hz
  refine ⟨him0, ?_⟩
  have hzeq : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him0)
  rw [hzeq] at hz ⊢
  refine RHTower.deriv_cosineShiftXi_ne_zero_of_local hh0 (fun w hw => ?_) hz
  rcases XiC_eq_zero_classification_of_singleQuartet hq hw with hw0 | ⟨-, hwim, -⟩
  · rw [hw0]
    have : 0 < h ^ 2 := by positivity
    nlinarith [sq_nonneg (z.re - w.re)]
  · have hsq : w.im ^ 2 = (ρ₀.re - 1 / 2) ^ 2 := by rw [← sq_abs, hwim]
    have hlt_sq : (ρ₀.re - 1 / 2) ^ 2 < h ^ 2 :=
      sq_lt_sq.mpr (by rw [abs_of_pos (by linarith [hq.1]), abs_of_pos hh0]; exact hh)
    nlinarith [sq_nonneg (z.re - w.re)]

/-- **Exact pinning at the quartet apex `δ₀ = Re ρ₀ - 1/2`.** At `δ₀ = Re ρ₀ - 1/2`,
`cosProducer δ₀ (±Im ρ₀) = 0`, every zero of `cosProducer δ₀` in `ℂ` is real, and every real zero
at `|x| ≠ |Im ρ₀|` is simple. -/
theorem cosProducer_apex_pinning_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    let δ₀ := ρ₀.re - 1 / 2
    RHTower.cosProducer δ₀ (ρ₀.im : ℂ) = 0 ∧
      RHTower.cosProducer δ₀ ((-ρ₀.im : ℝ) : ℂ) = 0 ∧
      (∀ z : ℂ, RHTower.cosProducer δ₀ z = 0 → z.im = 0) ∧
      (∀ x : ℝ, |x| ≠ |ρ₀.im| → RHTower.cosProducer δ₀ (x : ℂ) = 0 →
        deriv (RHTower.cosProducer δ₀) (x : ℂ) ≠ 0) := by
  intro δ₀
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; linarith [hq.1]
  have hzm : (ρ₀.im : ℂ) - (δ₀ : ℂ) * I = quartetSpectralRoot ρ₀ := rfl
  have hzp : (ρ₀.im : ℂ) + (δ₀ : ℂ) * I = conj (quartetSpectralRoot ρ₀) := by
    unfold quartetSpectralRoot
    apply Complex.ext <;> simp [δ₀]
  have hXi_z0 : RHTower.XiC (quartetSpectralRoot ρ₀) = 0 := by
    change RHTower.xi (1 / 2 + quartetSpectralRoot ρ₀ * I) = 0
    rw [half_add_quartetSpectralRoot_mul_I]
    exact hq.xi_eq_zero
  have hXi_cz0 : RHTower.XiC (conj (quartetSpectralRoot ρ₀)) = 0 := by
    rw [RHTower.XiC_conj, hXi_z0, map_zero]
  have hapex_pos : RHTower.cosProducer δ₀ (ρ₀.im : ℂ) = 0 := by
    unfold RHTower.cosProducer
    rw [hzp, hzm, hXi_cz0, hXi_z0]
    ring
  have hapex_neg : RHTower.cosProducer δ₀ ((-ρ₀.im : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_neg, RHTower.cosProducer_neg, hapex_pos]
  have hreal : ∀ z : ℂ, RHTower.cosProducer δ₀ z = 0 → z.im = 0 := fun z hz =>
    RHTower.CosineDefectBudget.cosShiftXi_zero_im_eq_zero_of_no_deep
      (deepCopies_eq_empty_of_singleQuartet hq le_rfl) hz
  refine ⟨hapex_pos, hapex_neg, hreal, fun x hxne hx0 => ?_⟩
  refine RHTower.deriv_cosineShiftXi_ne_zero_of_local hδ₀ (fun w hw => ?_) hx0
  rcases XiC_eq_zero_classification_of_singleQuartet hq hw with hw0 | ⟨hwre, hwim, -⟩
  · rw [hw0]
    have : 0 < δ₀ ^ 2 := by positivity
    nlinarith [sq_nonneg (x - w.re)]
  · have hne_re : x - w.re ≠ 0 := by
      intro hsub
      apply hxne
      rw [sub_eq_zero.mp hsub, hwre]
    have hpos_sq : 0 < (x - w.re) ^ 2 := sq_pos_of_ne_zero hne_re
    have hsq : w.im ^ 2 = δ₀ ^ 2 := by rw [← sq_abs, hwim]
    linarith

/-- **Confined exceptional-point existence under a single off-line quartet.** There exist
`h, x : ℝ` with `0 < h ≤ Re ρ₀ - 1/2 ≤ 8999/24000`, `cosProducer h x = 0`,
`deriv (cosProducer h) x = 0`, `(|x| - |Im ρ₀|)² + h² ≤ (Re ρ₀ - 1/2)²`, and `3 < |x|`. -/
theorem exists_confined_exceptionalPoint_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    ∃ h x : ℝ, 0 < h ∧ h ≤ ρ₀.re - 1 / 2 ∧ h ≤ 8999 / 24000 ∧
      RHTower.cosProducer h (x : ℂ) = 0 ∧
      deriv (RHTower.cosProducer h) (x : ℂ) = 0 ∧
      (|x| - |ρ₀.im|) ^ 2 + h ^ 2 ≤ (ρ₀.re - 1 / 2) ^ 2 ∧
      3 < |x| := by
  have hnot_ep : ¬ ∀ h : ℝ, 0 < h → h < 1 / 2 → ∀ x : ℝ,
      RHTower.cosProducer h (x : ℂ) = 0 → deriv (RHTower.cosProducer h) (x : ℂ) ≠ 0 :=
    fun hall => hq.not_riemannHypothesis
      (RHTower.riemannHypothesis_iff_cosProducer_no_exceptionalPoint.mpr hall)
  push Not at hnot_ep
  obtain ⟨h, hh0, _, x, hx0, hdx0⟩ := hnot_ep
  have hnot_loc : ¬ ∀ w : ℂ, RHTower.XiC w = 0 → w.im ^ 2 < (x - w.re) ^ 2 + h ^ 2 :=
    fun hloc => RHTower.deriv_cosineShiftXi_ne_zero_of_local hh0 hloc hx0 hdx0
  push Not at hnot_loc
  obtain ⟨w, hw0, hw_ge⟩ := hnot_loc
  have hw_im_ne : w.im ≠ 0 := by
    intro him0
    rw [him0] at hw_ge
    have : 0 < h ^ 2 := by positivity
    nlinarith [sq_nonneg (x - w.re)]
  rcases XiC_eq_zero_classification_of_singleQuartet hq hw0 with him0 | ⟨hwre, hwim, -⟩
  · exact absurd him0 hw_im_ne
  have hw_im_sq : w.im ^ 2 = (ρ₀.re - 1 / 2) ^ 2 := by rw [← sq_abs, hwim]
  have habs_diff : (|x| - |ρ₀.im|) ^ 2 ≤ (x - w.re) ^ 2 := by
    rw [← hwre, ← sq_abs (x - w.re)]
    have h1 := abs_sub_abs_le_abs_sub x w.re
    have h2 := abs_sub_abs_le_abs_sub w.re x
    rw [abs_sub_comm] at h2
    nlinarith
  have hsemi : (|x| - |ρ₀.im|) ^ 2 + h ^ 2 ≤ (ρ₀.re - 1 / 2) ^ 2 := by
    linarith [hw_ge, hw_im_sq, habs_diff]
  have hδ_pos : 0 < ρ₀.re - 1 / 2 := by linarith [hq.1]
  have h_le : h ≤ ρ₀.re - 1 / 2 := by
    have hsq_le : h ^ 2 ≤ (ρ₀.re - 1 / 2) ^ 2 := by
      nlinarith [sq_nonneg (|x| - |ρ₀.im|), hsemi]
    have habs_le := sq_le_sq.mp hsq_le
    rwa [abs_of_pos hh0, abs_of_pos hδ_pos] at habs_le
  have hre_sub : ρ₀.re ≤ 20999 / 24000 :=
    (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip
      hq.2.1.2.1 hq.2.1.1).2
  have hx_dist : |(|x| - |ρ₀.im|)| ≤ ρ₀.re - 1 / 2 := by
    have hsq_le : (|x| - |ρ₀.im|) ^ 2 ≤ (ρ₀.re - 1 / 2) ^ 2 := by
      nlinarith [sq_nonneg h, hsemi]
    have habs_le := sq_le_sq.mp hsq_le
    rwa [abs_of_pos hδ_pos] at habs_le
  have h4 : 4 < |ρ₀.im| := hq.four_lt_abs_im
  have hx3 : 3 < |x| := by
    have h1 := (abs_le.mp hx_dist).1
    linarith
  exact ⟨h, x, hh0, h_le, by linarith, hx0, hdx0, hsemi, hx3⟩

/-! ## 3. Quotient Laguerre–Pólya factorization `Ξ = ((z² - z₀²)(z² - z̄₀²))^k · Ξ_♭` -/

private theorem differentiable_conj_comp_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z : ℂ => conj (f (conj z))) := by
  intro z
  have h := (hf (conj z)).hasDerivAt.conj_conj
  simp only [Function.comp_def, Complex.conj_conj] at h
  exact h.differentiableAt

private theorem analyticOnNhd_conj_comp_conj {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    AnalyticOnNhd ℂ (fun z : ℂ => conj (f (conj z))) Set.univ := by
  have hd : Differentiable ℂ f := fun z => (hf z (Set.mem_univ z)).differentiableAt
  exact (differentiable_conj_comp_conj hd).differentiableOn.analyticOnNhd isOpen_univ

private theorem quartetSpectralRoot_distinct {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    let z₀ := quartetSpectralRoot ρ₀
    z₀ ≠ -z₀ ∧ z₀ ≠ conj z₀ ∧ z₀ ≠ -conj z₀ ∧
      -z₀ ≠ conj z₀ ∧ -z₀ ≠ -conj z₀ ∧ conj z₀ ≠ -conj z₀ := by
  intro z₀
  have hre : z₀.re = ρ₀.im := by simp [z₀, quartetSpectralRoot]
  have him : z₀.im = -(ρ₀.re - 1 / 2) := by simp [z₀, quartetSpectralRoot]
  have hre_ne : z₀.re ≠ 0 := by rw [hre]; exact hq.im_ne_zero
  have him_neg : z₀.im < 0 := by rw [him]; linarith [hq.1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hre_ne; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.im h; simp at this; linarith
  · intro h; apply hre_ne; have := congrArg Complex.re h; simp at this; linarith
  · intro h; apply hre_ne; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.im h; simp at this; linarith
  · intro h; apply hre_ne; have := congrArg Complex.re h; simp at this; linarith

private theorem differentiable_prod_sub_pow (S : Finset ℂ) (m : ℂ → ℕ) :
    Differentiable ℂ (fun z : ℂ => ∏ a ∈ S, (z - a) ^ (m a)) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
    have heq : (fun z : ℂ => ∏ x ∈ insert a S, (z - x) ^ (m x)) =
        fun z : ℂ => (z - a) ^ (m a) * ∏ x ∈ S, (z - x) ^ (m x) := by
      funext z; exact Finset.prod_insert ha
    rw [heq]
    exact ((differentiable_id.sub_const a).pow (m a)).mul ih

private theorem analyticOrderAt_eq_of_finset_factor {T : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hgT : ∀ a ∈ T, g a ≠ 0)
    (hfac : ∀ z : ℂ, RHTower.XiC z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    {b : ℂ} (hb : b ∈ T) :
    analyticOrderAt RHTower.XiC b = (m b : ℕ∞) := by
  classical
  let cofac : ℂ → ℂ := fun z => (∏ a ∈ T.erase b, (z - a) ^ (m a)) * g z
  have hcofac_diff : Differentiable ℂ cofac :=
    (differentiable_prod_sub_pow (T.erase b) m).mul
      (fun z => (hg z (Set.mem_univ z)).differentiableAt)
  have hcofac_an : AnalyticAt ℂ cofac b :=
    (hcofac_diff.differentiableOn.analyticOnNhd isOpen_univ) b (Set.mem_univ b)
  have hcofac_ne : cofac b ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a ha => ?_) (hgT b hb)
    exact pow_ne_zero (m a) (sub_ne_zero.mpr (Finset.ne_of_mem_erase ha).symm)
  refine (RHTower.XiC_analytic b (Set.mem_univ b)).analyticOrderAt_eq_natCast.mpr
    ⟨cofac, hcofac_an, hcofac_ne, Eventually.of_forall fun z => ?_⟩
  rw [hfac z, ← Finset.mul_prod_erase T (fun a => (z - a) ^ (m a)) hb]
  simp only [cofac, smul_eq_mul, mul_assoc]

private theorem analyticOrderAt_XiC_neg_of_finset_factor {T : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hgT : ∀ a ∈ T, g a ≠ 0)
    (hfac : ∀ z : ℂ, RHTower.XiC z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    {b : ℂ} (hb : b ∈ T) :
    analyticOrderAt RHTower.XiC (-b) = (m b : ℕ∞) := by
  classical
  let cofac : ℂ → ℂ := fun z => (∏ a ∈ T.erase b, (z - a) ^ (m a)) * g z
  have hcofac_diff : Differentiable ℂ cofac :=
    (differentiable_prod_sub_pow (T.erase b) m).mul
      (fun z => (hg z (Set.mem_univ z)).differentiableAt)
  have hneg_an : AnalyticAt ℂ (fun z : ℂ => (-1 : ℂ) ^ (m b) * cofac (-z)) (-b) := by
    have hd : Differentiable ℂ (fun z : ℂ => (-1 : ℂ) ^ (m b) * cofac (-z)) :=
      (differentiable_const _).mul (hcofac_diff.comp differentiable_neg)
    exact (hd.differentiableOn.analyticOnNhd isOpen_univ) (-b) (Set.mem_univ (-b))
  have hcofac_ne : cofac b ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a ha => ?_) (hgT b hb)
    exact pow_ne_zero (m a) (sub_ne_zero.mpr (Finset.ne_of_mem_erase ha).symm)
  have hneg_ne : (-1 : ℂ) ^ (m b) * cofac (- -b) ≠ 0 := by
    rw [neg_neg]
    exact mul_ne_zero (pow_ne_zero (m b) (by norm_num)) hcofac_ne
  refine (RHTower.XiC_analytic (-b) (Set.mem_univ (-b))).analyticOrderAt_eq_natCast.mpr
    ⟨fun z => (-1 : ℂ) ^ (m b) * cofac (-z), hneg_an, hneg_ne, Eventually.of_forall fun z => ?_⟩
  rw [← RHTower.XiC_even z, hfac (-z), ← Finset.mul_prod_erase T (fun a => (-z - a) ^ (m a)) hb]
  have hpow : (-z - b) ^ (m b) = (z - -b) ^ (m b) * (-1 : ℂ) ^ (m b) := by
    rw [← mul_pow]; congr 1; ring
  simp only [cofac, smul_eq_mul]
  rw [hpow]
  ring

private theorem analyticOrderAt_XiC_conj_of_finset_factor {T : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hgT : ∀ a ∈ T, g a ≠ 0)
    (hfac : ∀ z : ℂ, RHTower.XiC z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    {b : ℂ} (hb : b ∈ T) :
    analyticOrderAt RHTower.XiC (conj b) = (m b : ℕ∞) := by
  classical
  let cofac : ℂ → ℂ := fun z => (∏ a ∈ T.erase b, (z - a) ^ (m a)) * g z
  have hcofac_diff : Differentiable ℂ cofac :=
    (differentiable_prod_sub_pow (T.erase b) m).mul
      (fun z => (hg z (Set.mem_univ z)).differentiableAt)
  have hconj_an : AnalyticAt ℂ (fun z : ℂ => conj (cofac (conj z))) (conj b) :=
    ((differentiable_conj_comp_conj hcofac_diff).differentiableOn.analyticOnNhd isOpen_univ)
      (conj b) (Set.mem_univ (conj b))
  have hcofac_ne : cofac b ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a ha => ?_) (hgT b hb)
    exact pow_ne_zero (m a) (sub_ne_zero.mpr (Finset.ne_of_mem_erase ha).symm)
  have hconj_ne : conj (cofac (conj (conj b))) ≠ 0 := by
    rw [Complex.conj_conj]
    intro h0
    apply hcofac_ne
    have hc := congrArg conj h0
    simpa using hc
  refine (RHTower.XiC_analytic (conj b) (Set.mem_univ (conj b))).analyticOrderAt_eq_natCast.mpr
    ⟨fun z => conj (cofac (conj z)), hconj_an, hconj_ne, Eventually.of_forall fun z => ?_⟩
  have hreal_Xi : RHTower.XiC z = conj (RHTower.XiC (conj z)) := by
    rw [RHTower.XiC_conj, Complex.conj_conj]
  rw [hreal_Xi, hfac (conj z), ← Finset.mul_prod_erase T (fun a => (conj z - a) ^ (m a)) hb]
  simp only [cofac, smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]
  ring

/-- The degree-`4` quartet polynomial `(z² - z₀²)(z² - (conj z₀)²)`. -/
def quartetBiquadratic (ρ₀ z : ℂ) : ℂ :=
  (z ^ 2 - quartetSpectralRoot ρ₀ ^ 2) * (z ^ 2 - conj (quartetSpectralRoot ρ₀) ^ 2)

theorem quartetBiquadratic_even (ρ₀ z : ℂ) :
    quartetBiquadratic ρ₀ (-z) = quartetBiquadratic ρ₀ z := by
  unfold quartetBiquadratic
  ring

theorem quartetBiquadratic_conj (ρ₀ z : ℂ) :
    quartetBiquadratic ρ₀ (conj z) = conj (quartetBiquadratic ρ₀ z) := by
  unfold quartetBiquadratic
  simp only [map_mul, map_sub, map_pow, Complex.conj_conj]
  ring

theorem quartetBiquadratic_zero_pos {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    (quartetBiquadratic ρ₀ 0).im = 0 ∧ 0 < (quartetBiquadratic ρ₀ 0).re := by
  set z₀ := quartetSpectralRoot ρ₀
  have h0 : quartetBiquadratic ρ₀ 0 = ((Complex.normSq z₀ : ℝ) : ℂ) ^ 2 := by
    unfold quartetBiquadratic
    have hmul : z₀ * conj z₀ = (Complex.normSq z₀ : ℂ) := Complex.mul_conj z₀
    calc ((0 : ℂ) ^ 2 - z₀ ^ 2) * ((0 : ℂ) ^ 2 - conj z₀ ^ 2)
        = (z₀ * conj z₀) ^ 2 := by ring
      _ = ((Complex.normSq z₀ : ℝ) : ℂ) ^ 2 := by rw [hmul]
  rw [h0, ← Complex.ofReal_pow]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  have hz₀_ne : z₀ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [z₀, quartetSpectralRoot] at this
    exact hq.im_ne_zero this
  exact pow_pos (Complex.normSq_pos.mpr hz₀_ne) 2

/-- **Quotient Laguerre–Pólya factorization and real-rooted quotient Jensen theorem.**
Under `HasSingleOffLineQuartet ρ₀`, `XiC` factors globally on `ℂ` as
`XiC z = quartetBiquadratic ρ₀ z ^ k * g z` with `k ≥ 1` and an even Schwarz-real entire cofactor
`g` nonvanishing at `{0, z₀, -z₀, conj z₀, -conj z₀}` such that `LaguerrePolya g` holds and every
Jensen polynomial `jensenPoly (realTaylorCoeff (deriv^[r] g)) d` (`r, d : ℕ`) splits over `ℝ`. -/
theorem exists_quotient_laguerrePolya_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    let z₀ := quartetSpectralRoot ρ₀
    ∃ (k : ℕ) (g : ℂ → ℂ),
      1 ≤ k ∧
      Differentiable ℂ g ∧
      (∀ z : ℂ, g (-z) = g z) ∧
      (∀ z : ℂ, g (conj z) = conj (g z)) ∧
      g 0 ≠ 0 ∧ g z₀ ≠ 0 ∧ g (-z₀) ≠ 0 ∧ g (conj z₀) ≠ 0 ∧ g (-conj z₀) ≠ 0 ∧
      (∀ z : ℂ, RHTower.XiC z = quartetBiquadratic ρ₀ z ^ k * g z) ∧
      (∀ z : ℂ, g z = 0 → z.im = 0) ∧
      LaguerrePolya g ∧
      (∀ r d : ℕ, (jensenPoly (realTaylorCoeff (deriv^[r] g)) d).Splits) := by
  classical
  intro z₀
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := quartetSpectralRoot_distinct hq
  let T : Finset ℂ := {z₀, -z₀, conj z₀, -conj z₀}
  have hmem_z0 : z₀ ∈ T := by simp [T]
  have hmem_nz0 : -z₀ ∈ T := by simp [T]
  have hmem_cz0 : conj z₀ ∈ T := by simp [T]
  have hmem_ncz0 : -conj z₀ ∈ T := by simp [T]
  have hXi_not_ev0 : ∀ a ∈ (Set.univ : Set ℂ), ¬ ∀ᶠ z in 𝓝 a, RHTower.XiC z = 0 := fun a _ h0 =>
    RHTower.analyticOrderAt_XiC_ne_top a (analyticOrderAt_eq_top.mpr h0)
  obtain ⟨m, g, hg_an, hgT, hfac_univ⟩ :=
    exists_prod_factor_of_finset isOpen_univ T (fun _ _ => Set.mem_univ _)
      RHTower.XiC RHTower.XiC_analytic hXi_not_ev0
  have hfac : ∀ z : ℂ, RHTower.XiC z = (∏ a ∈ T, (z - a) ^ (m a)) * g z :=
    fun z => hfac_univ z (Set.mem_univ z)
  set k : ℕ := m z₀
  have hord_z0 : analyticOrderAt RHTower.XiC z₀ = (k : ℕ∞) :=
    analyticOrderAt_eq_of_finset_factor hg_an hgT hfac hmem_z0
  have hm_nz0 : m (-z₀) = k := by
    have h1 := analyticOrderAt_eq_of_finset_factor hg_an hgT hfac hmem_nz0
    have h2 := analyticOrderAt_XiC_neg_of_finset_factor hg_an hgT hfac hmem_z0
    exact Nat.cast_injective (h1.symm.trans h2)
  have hm_cz0 : m (conj z₀) = k := by
    have h1 := analyticOrderAt_eq_of_finset_factor hg_an hgT hfac hmem_cz0
    have h2 := analyticOrderAt_XiC_conj_of_finset_factor hg_an hgT hfac hmem_z0
    exact Nat.cast_injective (h1.symm.trans h2)
  have hm_ncz0 : m (-conj z₀) = k := by
    have h1 := analyticOrderAt_eq_of_finset_factor hg_an hgT hfac hmem_ncz0
    have h2 := analyticOrderAt_XiC_neg_of_finset_factor hg_an hgT hfac hmem_cz0
    rw [hm_cz0] at h2
    exact Nat.cast_injective (h1.symm.trans h2)
  have hXi_z0 : RHTower.XiC z₀ = 0 := by
    change RHTower.xi (1 / 2 + z₀ * I) = 0
    rw [half_add_quartetSpectralRoot_mul_I]
    exact hq.xi_eq_zero
  have hk_pos : 1 ≤ k := by
    by_contra hk0
    have hk_eq0 : k = 0 := by omega
    rw [hk_eq0, Nat.cast_zero,
      (RHTower.XiC_analytic z₀ (Set.mem_univ z₀)).analyticOrderAt_eq_zero] at hord_z0
    exact hord_z0 hXi_z0
  have hprod_eq : ∀ z : ℂ, ∏ a ∈ T, (z - a) ^ (m a) = quartetBiquadratic ρ₀ z ^ k := by
    intro z
    have h1 : z₀ ∉ ({-z₀, conj z₀, -conj z₀} : Finset ℂ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hn1, hn2, hn3⟩
    have h2 : -z₀ ∉ ({conj z₀, -conj z₀} : Finset ℂ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hn4, hn5⟩
    have h3 : conj z₀ ∉ ({-conj z₀} : Finset ℂ) := by
      simp only [Finset.mem_singleton]
      exact hn6
    dsimp [T]
    rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_insert h3,
      Finset.prod_singleton, hm_nz0, hm_cz0, hm_ncz0]
    unfold quartetBiquadratic
    change (z - z₀) ^ k * ((z - -z₀) ^ k * ((z - conj z₀) ^ k * (z - -conj z₀) ^ k)) =
      ((z ^ 2 - z₀ ^ 2) * (z ^ 2 - conj z₀ ^ 2)) ^ k
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    congr 1; ring
  have hfac_bi : ∀ z : ℂ, RHTower.XiC z = quartetBiquadratic ρ₀ z ^ k * g z := by
    intro z; rw [hfac z, hprod_eq z]
  have hg_diff : Differentiable ℂ g := fun z => (hg_an z (Set.mem_univ z)).differentiableAt
  -- Nonvanishing of `quartetBiquadratic ρ₀` on a neighborhood of `0` gives evenness & Schwarz reality.
  obtain ⟨hq0_im, hq0_re⟩ := quartetBiquadratic_zero_pos hq
  have hq0_ne : quartetBiquadratic ρ₀ 0 ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hq0_re; exact lt_irrefl 0 hq0_re
  have hq_cont : Continuous (quartetBiquadratic ρ₀) := by
    unfold quartetBiquadratic; fun_prop
  have hq_ev_ne : ∀ᶠ z in 𝓝 (0 : ℂ), quartetBiquadratic ρ₀ z ^ k ≠ 0 :=
    (hq_cont.continuousAt.eventually_ne hq0_ne).mono fun z hz => pow_ne_zero k hz
  have hg_even : ∀ z : ℂ, g (-z) = g z := by
    have hg_neg_an : AnalyticOnNhd ℂ (fun z : ℂ => g (-z)) Set.univ :=
      (hg_diff.comp differentiable_neg).differentiableOn.analyticOnNhd isOpen_univ
    have hev_eq : (fun z : ℂ => g (-z)) =ᶠ[𝓝 (0 : ℂ)] g := by
      filter_upwards [hq_ev_ne] with z hqz
      have heq : quartetBiquadratic ρ₀ z ^ k * g (-z) = quartetBiquadratic ρ₀ z ^ k * g z := by
        calc quartetBiquadratic ρ₀ z ^ k * g (-z)
            = quartetBiquadratic ρ₀ (-z) ^ k * g (-z) := by rw [quartetBiquadratic_even]
          _ = RHTower.XiC (-z) := (hfac_bi (-z)).symm
          _ = RHTower.XiC z := RHTower.XiC_even z
          _ = quartetBiquadratic ρ₀ z ^ k * g z := hfac_bi z
      exact mul_left_cancel₀ hqz heq
    have hon := hg_neg_an.eqOn_of_preconnected_of_eventuallyEq hg_an isPreconnected_univ
      (Set.mem_univ (0 : ℂ)) hev_eq
    exact fun z => hon (Set.mem_univ z)
  have hg_conj : ∀ z : ℂ, g (conj z) = conj (g z) := by
    have hg_cc_an : AnalyticOnNhd ℂ (fun z : ℂ => conj (g (conj z))) Set.univ :=
      analyticOnNhd_conj_comp_conj hg_an
    have hev_eq : (fun z : ℂ => conj (g (conj z))) =ᶠ[𝓝 (0 : ℂ)] g := by
      filter_upwards [hq_ev_ne] with z hqz
      have heq : quartetBiquadratic ρ₀ z ^ k * conj (g (conj z)) =
          quartetBiquadratic ρ₀ z ^ k * g z := by
        have h1 := congrArg conj (hfac_bi (conj z))
        rw [RHTower.XiC_conj, Complex.conj_conj, map_mul, map_pow,
          quartetBiquadratic_conj, Complex.conj_conj] at h1
        rw [← h1, hfac_bi z]
      exact mul_left_cancel₀ hqz heq
    have hon := hg_cc_an.eqOn_of_preconnected_of_eventuallyEq hg_an isPreconnected_univ
      (Set.mem_univ (0 : ℂ)) hev_eq
    intro z
    have hz := hon (Set.mem_univ (conj z))
    simp only [Complex.conj_conj] at hz
    exact hz.symm
  have hg0_ne : g 0 ≠ 0 := by
    intro h0
    have hX0 := hfac_bi 0
    rw [h0, mul_zero] at hX0
    exact RHTower.XiC_zero_ne hX0
  have hg0_im : (g 0).im = 0 := by
    have hc := hg_conj 0
    rw [map_zero] at hc
    have him := congrArg Complex.im hc
    rw [Complex.conj_im] at him
    linarith
  -- Every zero of `g` is real.
  have hg_real : ∀ z : ℂ, g z = 0 → z.im = 0 := by
    intro z hgz
    have hXz : RHTower.XiC z = 0 := by rw [hfac_bi z, hgz, mul_zero]
    rcases XiC_eq_zero_classification_of_singleQuartet hq hXz with him0 | ⟨-, -, hmemset⟩
    · exact him0
    · exfalso
      have hzT : z ∈ T := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemset
        rcases hmemset with rfl | rfl | rfl | rfl
        · exact hmem_z0
        · exact hmem_nz0
        · exact hmem_cz0
        · exact hmem_ncz0
      exact hgT z hzT hgz
  -- Analytic order finiteness and order-one growth bound for `g`.
  have hg_ord_ne_top : ∀ z : ℂ, analyticOrderAt g z ≠ ⊤ := fun z htop => by
    have hev0 := analyticOrderAt_eq_top.mp htop
    have hon := hg_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) hev0
    exact hg0_ne (hon (Set.mem_univ 0))
  obtain ⟨C, hC_pos, hXi_bound⟩ := RHTower.XiC_order
  let R : ℝ := 2 * ‖z₀‖ + 1
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hg_diff.continuous.continuousOn
  set B : ℝ := max M 1
  have hB1 : 1 ≤ B := le_max_right M 1
  have hB_pos : 0 < B := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogB_nn : 0 ≤ Real.log B := Real.log_nonneg hB1
  set K' : ℝ := C + Real.log B / Real.log 2
  have hK'_nn : 0 ≤ K' := add_nonneg hC_pos.le (div_nonneg hlogB_nn hlog2_pos.le)
  have hg_bound : ∀ z : ℂ, ‖g z‖ ≤ Real.exp (K' * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    intro z
    have h1z : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hlog_ge : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
      Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
    have hprod_ge : Real.log 2 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
      calc Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
        _ ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
          mul_le_mul h1z hlog_ge hlog2_pos.le (by positivity)
    by_cases hzR : ‖z‖ ≤ R
    · have hz_ball : z ∈ closedBall (0 : ℂ) R := by simpa [mem_closedBall] using hzR
      have hgz_B : ‖g z‖ ≤ B := (hM z hz_ball).trans (le_max_left M 1)
      have hexp_ge : Real.log B ≤ K' * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
        have hstep : Real.log B ≤
            (Real.log B / Real.log 2) * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]
          exact mul_le_mul_of_nonneg_left hprod_ge hlogB_nn
        have hC_nn : 0 ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
          mul_nonneg (mul_nonneg hC_pos.le (by positivity)) (hlog2_pos.le.trans hlog_ge)
        dsimp [K']
        linarith
      calc ‖g z‖ ≤ B := hgz_B
        _ = Real.exp (Real.log B) := (Real.exp_log hB_pos).symm
        _ ≤ Real.exp (K' * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := Real.exp_le_exp.mpr hexp_ge
    · rw [not_le] at hzR
      have ha_norm : ∀ a ∈ T, ‖a‖ = ‖z₀‖ := by
        intro a ha
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> simp
      have hfac_ge1 : ∀ a ∈ T, 1 ≤ ‖z - a‖ ^ k := by
        intro a ha
        have htri : ‖z‖ - ‖a‖ ≤ ‖z - a‖ := norm_sub_norm_le z a
        rw [ha_norm a ha] at htri
        have hge1 : 1 ≤ ‖z - a‖ := by dsimp [R] at hzR; linarith [norm_nonneg z₀]
        exact one_le_pow₀ hge1
      have hQ_ge1 : 1 ≤ ‖quartetBiquadratic ρ₀ z ^ k‖ := by
        rw [← hprod_eq z, Complex.norm_prod]
        calc (1 : ℝ) = ∏ _a ∈ T, (1 : ℝ) := by simp
          _ ≤ ∏ a ∈ T, ‖(z - a) ^ (m a)‖ := by
            refine Finset.prod_le_prod (fun _ _ => zero_le_one) fun a ha => ?_
            rw [norm_pow]
            have hm_eq : m a = k := by
              simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
              rcases ha with rfl | rfl | rfl | rfl
              · rfl
              · exact hm_nz0
              · exact hm_cz0
              · exact hm_ncz0
            rw [hm_eq]
            exact hfac_ge1 a ha
      have hg_le_Xi : ‖g z‖ ≤ ‖RHTower.XiC z‖ := by
        rw [hfac_bi z, norm_mul]
        calc ‖g z‖ = 1 * ‖g z‖ := (one_mul _).symm
          _ ≤ ‖quartetBiquadratic ρ₀ z ^ k‖ * ‖g z‖ :=
            mul_le_mul_of_nonneg_right hQ_ge1 (norm_nonneg (g z))
      have hexp_le : C * (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤
          K' * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
        have hextra : 0 ≤ (Real.log B / Real.log 2) * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
          mul_nonneg (mul_nonneg (div_nonneg hlogB_nn hlog2_pos.le) (by positivity))
            (by linarith)
        dsimp [K']
        linarith
      exact hg_le_Xi.trans ((hXi_bound z).trans (Real.exp_le_exp.mpr hexp_le))
  have hLP_g : LaguerrePolya g :=
    RHTower.OrderOneHadamard.laguerrePolya_of_even_of_realZeros hK'_nn hg_an hg0_ne hg0_im
      hg_ord_ne_top hg_even hg_bound hg_real
  have hsplits : ∀ r d : ℕ, (jensenPoly (realTaylorCoeff (deriv^[r] g)) d).Splits := by
    intro r d
    have hLP_r : LaguerrePolya (deriv^[r] g) := RHTower.laguerrePolya_iterate_deriv hLP_g r
    have hconj_r : ∀ z : ℂ, deriv^[r] g (conj z) = conj (deriv^[r] g z) := by
      intro z
      rw [← iteratedDeriv_eq_iterate]
      exact iteratedDeriv_conj_of_schwarzReal hg_conj r z
    exact splits_jensenPoly_realTaylorCoeff hLP_r hconj_r d
  exact ⟨k, g, hk_pos, hg_diff, hg_even, hg_conj, hg0_ne,
    hgT z₀ hmem_z0, hgT (-z₀) hmem_nz0, hgT (conj z₀) hmem_cz0, hgT (-conj z₀) hmem_ncz0,
    hfac_bi, hg_real, hLP_g, hsplits⟩

#print axioms zerosApproachLine_of_singleQuartet
#print axioms lindelof_all_forms_of_singleQuartet
#print axioms not_hasSingleOffLineQuartet_of_not_lindelof
#print axioms infinite_offLine_of_not_lindelof
#print axioms singleQuartet_or_lindelof_without_rh
#print axioms laguerrePolya_cosProducer_of_singleQuartet_ge
#print axioms exists_lt_not_laguerrePolya_cosProducer_of_singleQuartet
#print axioms cosProducer_real_and_simple_of_singleQuartet_gt
#print axioms cosProducer_apex_pinning_of_singleQuartet
#print axioms exists_confined_exceptionalPoint_of_singleQuartet
#print axioms exists_quotient_laguerrePolya_of_singleQuartet

end GaloisForLFunctions.ExceptionalLayerTheory
