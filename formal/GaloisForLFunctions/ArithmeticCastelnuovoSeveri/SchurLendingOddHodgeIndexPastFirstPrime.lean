import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDegreeFiltrationOfTheHodgeDefect
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface
import GaloisForLFunctions.ArithmeticIncidencePositivity.SchurLendingOddWindowThreeHundredSixtyTwoThousandths

/-!
# Arithmetic Hodge Index Past the First Prime via Schur Lending in the Odd Reflection Sector

At apertures `a ≤ 3/10 < (log 2)/2 ≈ 0.34657`, the prime-shift support `[-2a, 2a]` of `f ⋆ f̃` lies
strictly inside `(-log 2, log 2)`, so the prime sum of the explicit formula vanishes identically:
the vanishing of `hodgeDefectAt zetaZeroConfig a` for `a ≤ 3/10` uses only the archimedean gamma
collar. Once `a > (log 2)/2`, the prime `2` enters the support on the strip
`S₂ = [log 2 − a, a]`.

This file constructs the unconditional arithmetic Hodge index zero of `ζ` past the first prime
threshold `(log 2)/2 < 181/500 = 0.362`, together with the primitive geometry and coupled
pole–test effectivity cone of the odd reflection sector on the scaling surface of `ℤ`:

1. **Degree filtration of the reflection-sector Hodge defect** (`sectorHodgeDefectAt`,
   `iSup_sectorHodgeDefectAt`, `zeta_iSup_sectorHodgeDefectAt`,
   `forall_zeta_sectorHodgeDefectAt_eq_zero_iff`): the degree-filtered sector defect
   `sectorHodgeDefectAt Z s a` is monotone in `a`, bounded by `(sectorZeros Z s).encard`, and
   exhausts `(sectorZeros Z s).encard` as `a → ∞` for every tempered `FESymmetric` configuration.
   Because `ζ` has no real nontrivial zeros, the vanishing of its odd-sector Hodge defect across all
   degrees is unconditionally equivalent to the vanishing of the full Hodge defect across all
   degrees (and to the Riemann Hypothesis).
2. **Unconditional odd-sector Hodge index zero of `ζ` past the first prime**
   (`half_log_two_lt_threeHundredSixtyTwoThousandths`,
   `zetaZeroConfig_re_W_ge_of_odd_aperture_le_threeHundredSixtyTwoThousandths`,
   `zeta_odd_sectorHodgeDefectAt_eq_zero`,
   `negIndex_weilGram_odd_eq_zero_of_le_threeHundredSixtyTwoThousandths`,
   `posIndex_intersectionGram_odd_eq_one_of_le_threeHundredSixtyTwoThousandths`):
   via the Schur-lending prime-`2` strip construction on `[-181/500, 181/500]` (where the micro-fold
   of `S₂ × S₂` pays `9/5` of the reflected-odd part of the prime-`2` atom and the even part of the
   prime-`2` atom lends potential `49/125` across two Schur rectangles to the archimedean middle),
   every complex odd `C²` test supported in `[-a, a]` with `a ≤ 181/500` satisfies
   `Re W_ζ(f, f) ≥ (1/1000) ∫ ‖f‖²`. Consequently, for all `a ≤ 181/500` (strictly past `(log 2)/2`),
   `sectorHodgeDefectAt zetaZeroConfig (-1) a = 0`, `hermNegIndex (weilGram Λ f) = 0`, and the
   arithmetic intersection Gram matrix of `H, V, f₁, …, f_n` has `hermPosIndex = 1`.
3. **Primitive embedding of the odd sector and coupled pole–test effectivity on the scaling surface**
   (`poleB_eq_neg_poleA_of_odd`, `scalingPair_odd_ample_eq`,
   `scalingPair_odd_self_of_orthogonal_ample`, `scalingSubsurface`, `coupledArithmeticCone`,
   `scalingSubsurface_odd_primitive_pair_self_le`, `scalingSubsurface_odd_hodgeIndex`,
   `coupledArithmeticCone_odd_effectivity`):
   on the scaling surface of `ℤ`, every odd test `f` has opposite pole residues `B(f) = -A(f)`, so
   every pure odd test cycle `(0, 0, f)` has degree `0` against the ample class `H + V` and embeds
   directly into the primitive subspace `(H + V)⊥`. On `(H + V)⊥`, a cycle `a(H - V) + f` has
   self-intersection `-2(a + A(f))² - weilPair f f`, where the polar term `-2(a + A(f))²` is already
   nonpositive. At every aperture `a ≤ 181/500` past the first prime, the odd scaling subsurface
   satisfies the coercive primitive bound
   `x · x ≤ -2(a₀ + A(f))² - (1/1000) ∫ f² ≤ 0`, the full Castelnuovo–Severi `HodgeIndex`, and the
   coupled pole–test arithmetic cone `coupledArithmeticCone` unconditionally satisfies
   `RiemannRochAxiom`, `AmpleAxiom`, and `BezoutAxiom`.
-/

open Complex MeasureTheory Set Matrix
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  zetaZeroConfig_re_W_ge_of_aperture_le_threeTenths)
open GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
  (fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Degree filtration of the reflection-sector Hodge defect -/

/-- The reflection-sector Hodge defect at degree `a`: the largest number of negative squares of the
Weil form on a finite family of `C²` tests of parity `s` supported in `[−a, a]`. -/
def sectorHodgeDefectAt (Z : ZeroConfig) (s : ℂ) (a : ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (f : Fin n → ℝ → ℂ)
    (_ : ∀ i, ContDiff ℝ 2 (f i) ∧ tsupport (f i) ⊆ Icc (-a) a ∧ testNeg (f i) = s • f i),
    (hermNegIndex (zeroGram Z f) : ℕ∞)

theorem le_sectorHodgeDefectAt (Z : ZeroConfig) {s : ℂ} {a : ℝ} {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i) ∧ tsupport (f i) ⊆ Icc (-a) a ∧ testNeg (f i) = s • f i) :
    (hermNegIndex (zeroGram Z f) : ℕ∞) ≤ sectorHodgeDefectAt Z s a :=
  le_iSup₂_of_le n f (le_iSup_of_le hf le_rfl)

/-- The reflection-sector Hodge defect is nondecreasing in the degree `a`. -/
theorem sectorHodgeDefectAt_mono (Z : ZeroConfig) (s : ℂ) :
    Monotone (sectorHodgeDefectAt Z s) := fun _ _ hab =>
  iSup₂_le fun _ f => iSup_le fun hf => le_sectorHodgeDefectAt Z f fun i =>
    ⟨(hf i).1, (hf i).2.1.trans (Icc_subset_Icc (neg_le_neg hab) hab), (hf i).2.2⟩

/-- The reflection-sector Hodge defect at degree `a` is bounded by the full Hodge defect at
degree `a`. -/
theorem sectorHodgeDefectAt_le_hodgeDefectAt (Z : ZeroConfig) (s : ℂ) (a : ℝ) :
    sectorHodgeDefectAt Z s a ≤ hodgeDefectAt Z a :=
  iSup₂_le fun _ f => iSup_le fun hf => le_hodgeDefectAt Z f fun i => ⟨(hf i).1, (hf i).2.1⟩

/-- The reflection-sector Hodge defect at any degree is at most the number of zeros in the sector. -/
theorem sectorHodgeDefectAt_le (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {s : ℂ} (hs : s = 1 ∨ s = -1) (a : ℝ) :
    sectorHodgeDefectAt Z s a ≤ (sectorZeros Z s).encard :=
  iSup₂_le fun _ f => iSup_le fun hf => negIndex_sector_le Z hZ hFE hs f
    (fun i => (hf i).1)
    (fun i => isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hf i).2.1)
    (fun i => (hf i).2.2)

/-- **The degree filtration of a reflection sector exhausts the zeros of that sector.** -/
theorem iSup_sectorHodgeDefectAt (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {s : ℂ} (hs : s = 1 ∨ s = -1) :
    ⨆ a, sectorHodgeDefectAt Z s a = (sectorZeros Z s).encard := by
  refine le_antisymm (iSup_le (sectorHodgeDefectAt_le Z hZ hFE hs)) ?_
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  obtain ⟨f, hf, hfc, hsym, hle⟩ := (sector_pontryagin_law Z hZ hFE hs n).mpr hn
  obtain ⟨a, ha⟩ := exists_aperture f hfc
  calc (n : ℕ∞) ≤ hermNegIndex (zeroGram Z f) := ENat.coe_le_coe.mpr hle
    _ ≤ sectorHodgeDefectAt Z s a := le_sectorHodgeDefectAt Z f fun i => ⟨hf i, ha i, hsym i⟩
    _ ≤ ⨆ a, sectorHodgeDefectAt Z s a := le_iSup _ a

/-- **For `ζ`, each reflection sector's degree filtration exhausts the upper-half-plane zeros
right of the critical line.** -/
theorem zeta_iSup_sectorHodgeDefectAt {s : ℂ} (hs : s = 1 ∨ s = -1) :
    ⨆ a, sectorHodgeDefectAt zetaZeroConfig s a =
      {ρ | ρ ∈ rightZeros zetaZeroConfig ∧ 0 < ρ.im}.encard := by
  rw [iSup_sectorHodgeDefectAt zetaZeroConfig temperedConfig_zetaZeroConfig
    fesSymmetric_zetaZeroConfig hs, zeta_sectorZeros_eq]

/-- Because `ζ` is functional-equation symmetric and has no real nontrivial zeros, `ζ` has no zeros
right of the critical line if and only if it has no upper-half-plane zeros right of the line. -/
theorem zeta_rightZeros_eq_empty_iff :
    rightZeros zetaZeroConfig = ∅ ↔
      {ρ | ρ ∈ rightZeros zetaZeroConfig ∧ 0 < ρ.im} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h ρ hρ
    exact h ρ hρ.1
  · intro h ρ hρ
    have him0 : ρ.im ≠ 0 := zetaZeroConfig_im_ne_zero' ρ hρ.1
    rcases lt_or_gt_of_ne him0 with hlt | hgt
    · refine h (conj ρ) ⟨⟨fesSymmetric_zetaZeroConfig.conj_mem hρ.1, ?_⟩, ?_⟩
      · simpa using hρ.2
      · simp only [Complex.conj_im]; linarith
    · exact h ρ ⟨hρ, hgt⟩

/-- **Single-sector reduction across all degrees for `ζ`.** For either parity `s = 1` or `s = -1`,
the sector Hodge defect of `ζ` vanishes at every degree `a` if and only if the full Hodge defect
of `ζ` vanishes at every degree `a`. -/
theorem forall_zeta_sectorHodgeDefectAt_eq_zero_iff {s : ℂ} (hs : s = 1 ∨ s = -1) :
    (∀ a, sectorHodgeDefectAt zetaZeroConfig s a = 0) ↔
      ∀ a, hodgeDefectAt zetaZeroConfig a = 0 := by
  have hsup : ∀ g : ℝ → ℕ∞, (∀ a, g a = 0) ↔ ⨆ a, g a = 0 := fun g =>
    ⟨fun h => le_antisymm (iSup_le fun a => (h a).le) zero_le,
     fun h a => le_antisymm ((le_iSup g a).trans h.le) zero_le⟩
  rw [hsup, hsup, zeta_iSup_sectorHodgeDefectAt hs,
    iSup_hodgeDefectAt zetaZeroConfig temperedConfig_zetaZeroConfig,
    Set.encard_eq_zero, Set.encard_eq_zero, zeta_rightZeros_eq_empty_iff]

/-! ### 2. Unconditional odd-sector Hodge index zero of `ζ` past the first prime -/

/-- **The aperture `181/500 = 0.362` strictly exceeds the first prime threshold `(log 2)/2`.** -/
theorem half_log_two_lt_threeHundredSixtyTwoThousandths :
    Real.log 2 / 2 < 181 / 500 := by
  have h := Real.log_two_lt_d9
  linarith

/-- **Transfer of an odd real zero-form window to complex odd tests.** If every real odd `C²_c` test
supported in `[−A, A]` satisfies `Ẑ(F) ≥ c ∫ F²`, then every complex odd `C²` test supported in
`[−A, A]` satisfies `Re W_ζ(f, f) ≥ c ∫ ‖f‖²`. -/
theorem zetaZeroConfig_re_W_ge_of_odd_window {A c : ℝ}
    (hwin : ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
      (∀ x, A < |x| → F x = 0) → c * ∫ x, F x ^ 2 ≤ fullZeroForm F)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-A) A)
    (hodd : testNeg f = (-1 : ℂ) • f) :
    c * ∫ x, ‖f x‖ ^ 2 ≤ (zetaZeroConfig.W f f).re := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f).trans hfs)
  have hzero : ∀ x, A < |x| → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hfs hmem
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hRe : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hIm : ContDiff ℝ 2 (fun u => (f u).im) := Complex.imCLM.contDiff.comp hf
  have hRec : HasCompactSupport (fun u => (f u).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hImc : HasCompactSupport (fun u => (f u).im) :=
    hfc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have hReOdd : ∀ x, (f (-x)).re = -(f x).re := fun x => by
    have hx := congrFun hodd x
    simp only [testNeg, Pi.smul_apply, smul_eq_mul, neg_one_mul] at hx
    exact congrArg Complex.re hx
  have hImOdd : ∀ x, (f (-x)).im = -(f x).im := fun x => by
    have hx := congrFun hodd x
    simp only [testNeg, Pi.smul_apply, smul_eq_mul, neg_one_mul] at hx
    exact congrArg Complex.im hx
  have h1 := hwin _ hRe hRec hReOdd fun x hx => by simp [hzero x hx]
  have h2 := hwin _ hIm hImc hImOdd fun x hx => by simp [hzero x hx]
  have hint (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun x => g x ^ 2) volume := by
    have hs : HasCompactSupport (fun x => g x ^ 2) :=
      HasCompactSupport.of_support_subset_isCompact hgc.isCompact fun x hx =>
        subset_tsupport g (by simpa using hx)
    exact (hg.pow 2).integrable_of_hasCompactSupport hs
  have hsplit : ∫ x, ‖f x‖ ^ 2 = (∫ x, (f x).re ^ 2) + ∫ x, (f x).im ^ 2 := by
    rw [← integral_add (hint _ hRe.continuous hRec) (hint _ hIm.continuous hImc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [zeta_W_re_eq_fullZeroForm_re_add_im hf hfc, hsplit, mul_add]
  exact add_le_add h1 h2

/-- **Coercive complex odd Weil positivity of `ζ` past the first prime (`a ≤ 181/500`).** Every
complex odd `C²` test supported in `[−181/500, 181/500]` satisfies
`Re W_ζ(f, f) ≥ (1/1000) ∫ ‖f‖²`, proved unconditionally by the Schur-lending prime-`2` strip
construction. -/
theorem zetaZeroConfig_re_W_ge_of_odd_aperture_le_threeHundredSixtyTwoThousandths
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(181 / 500)) (181 / 500))
    (hodd : testNeg f = (-1 : ℂ) • f) :
    1 / 1000 * ∫ x, ‖f x‖ ^ 2 ≤ (zetaZeroConfig.W f f).re :=
  zetaZeroConfig_re_W_ge_of_odd_window
    (fun _ hF hFc ho hs =>
      fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hF hFc ho hs)
    hf hfs hodd

theorem zetaZeroConfig_re_W_nonneg_of_odd_aperture_le_threeHundredSixtyTwoThousandths
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(181 / 500)) (181 / 500))
    (hodd : testNeg f = (-1 : ℂ) • f) :
    0 ≤ (zetaZeroConfig.W f f).re :=
  le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    (zetaZeroConfig_re_W_ge_of_odd_aperture_le_threeHundredSixtyTwoThousandths hf hfs hodd)

/-- Parity `testNeg (f i) = s • f i` is preserved under linear combinations. -/
theorem testNeg_sum_smul {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ) {s : ℂ}
    (hsym : ∀ i, testNeg (f i) = s • f i) (c : ι → ℂ) :
    testNeg (∑ i, c i • f i) = s • ∑ i, c i • f i := by
  funext u
  simp only [testNeg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := congrFun (hsym i) u
  simp only [testNeg, Pi.smul_apply, smul_eq_mul] at hi
  rw [hi]
  ring

/-- Support in `[−A, A]` is preserved under finite linear combinations when `a ≤ A`. -/
theorem tsupport_sum_smul_subset_Icc {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ) {a A : ℝ}
    (ha : a ≤ A) (hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a) (c : ι → ℂ) :
    tsupport (∑ i, c i • f i) ⊆ Icc (-A) A := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  apply hu
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : f i u = 0 := image_eq_zero_of_notMem_tsupport fun h => hout
    (Icc_subset_Icc (by linarith) ha (hfs i h))
  simp [this]

/-- **Zero-side Gram matrix has no negative squares on odd tests past the first prime
(`a ≤ 181/500`).** -/
theorem negIndex_zeroGram_zeta_odd_eq_zero_of_le_threeHundredSixtyTwoThousandths
    {ι : Type*} [Fintype ι] {a : ℝ} (ha : a ≤ 181 / 500) (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a)
    (hodd : ∀ i, testNeg (f i) = (-1 : ℂ) • f i) :
    hermNegIndex (zeroGram zetaZeroConfig f) = 0 := by
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hfs i)
  refine negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
  rw [hermQuad_zeroGram_of_tempered zetaZeroConfig temperedConfig_zetaZeroConfig f hf hfc]
  exact zetaZeroConfig_re_W_nonneg_of_odd_aperture_le_threeHundredSixtyTwoThousandths
    (contDiff_sum_smul f hf _) (tsupport_sum_smul_subset_Icc f ha hfs _)
    (testNeg_sum_smul f hodd _)

/-- **Explicit-formula Weil Gram matrix of `Λ` has negative index `0` on odd tests past the first
prime (`a ≤ 181/500`).** -/
theorem negIndex_weilGram_odd_eq_zero_of_le_threeHundredSixtyTwoThousandths
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ℝ} (ha : a ≤ 181 / 500) (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a)
    (hodd : ∀ i, testNeg (f i) = (-1 : ℂ) • f i) :
    hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 0 := by
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hfs i)
  rw [weilGram_eq_zeroGram f hf hfc]
  exact negIndex_zeroGram_zeta_odd_eq_zero_of_le_threeHundredSixtyTwoThousandths ha f hf hfs hodd

/-- **Arithmetic Hodge index signature (`posIndex = 1`) on odd tests past the first prime
(`a ≤ 181/500`).** For every finite family `f₁, …, f_n` of odd `C²` tests supported in `[−a, a]`
with `a ≤ 181/500` (where prime `2` is active for `(log 2)/2 < a`), the arithmetic intersection
Gram matrix of `H, V, f₁, …, f_n` has exactly one positive square. -/
theorem posIndex_intersectionGram_odd_eq_one_of_le_threeHundredSixtyTwoThousandths
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ℝ} (ha : a ≤ 181 / 500) (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a)
    (hodd : ∀ i, testNeg (f i) = (-1 : ℂ) • f i) :
    hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1 := by
  rw [posIndex_intersectionGram,
    negIndex_weilGram_odd_eq_zero_of_le_threeHundredSixtyTwoThousandths ha f hf hfs hodd,
    add_zero]

/-- **Unconditional vanishing of the odd-sector Hodge defect of `ζ` past the first prime
(`a ≤ 181/500`).** -/
theorem zeta_odd_sectorHodgeDefectAt_eq_zero {a : ℝ} (ha : a ≤ 181 / 500) :
    sectorHodgeDefectAt zetaZeroConfig (-1) a = 0 := by
  refine le_antisymm (iSup₂_le fun _ f => iSup_le fun hf => ?_) zero_le
  rw [negIndex_zeroGram_zeta_odd_eq_zero_of_le_threeHundredSixtyTwoThousandths ha f
    (fun i => (hf i).1) (fun i => (hf i).2.1) (fun i => (hf i).2.2), Nat.cast_zero]

/-! ### 3. The odd scaling subsurface, primitive embedding into `(H + V)⊥`, and coupled effectivity -/

/-- For any real `C²` compactly supported test `f`, `weilPair f f` equals `(zetaZeroConfig.W (cx f) (cx f)).re`. -/
theorem weilPair_self_eq_zeta_W_re {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilPair f f = (zetaZeroConfig.W (cx f) (cx f)).re := by
  rw [weilPair, ← RHTower.zeta_W_eq_weilFullFunctional_mixed (cx_contDiff hf)
    (cx_hasCompactSupport hfc) (cx_contDiff hf) (cx_hasCompactSupport hfc)]

/-- For any real test `f`, `∫ x, ‖cx f x‖ ^ 2 = ∫ x, f x ^ 2`. -/
theorem integral_norm_cx_sq (f : ℝ → ℝ) :
    (∫ x, ‖cx f x‖ ^ 2) = ∫ x, f x ^ 2 := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Opposite pole residues of an odd test.** Every odd test `f(-u) = -f(u)` satisfies
`B(f) = -A(f)`, because the reflection `u ↦ -u` exchanges `e^{-u/2}` and `e^{u/2}` with a minus
sign. -/
theorem poleB_eq_neg_poleA_of_odd {f : ℝ → ℝ} (hodd : ∀ u, f (-u) = -f u) :
    poleB f = -poleA f := by
  unfold poleB poleA
  rw [← MeasureTheory.integral_neg_eq_self (fun u => f u * Real.exp (-u / 2)),
    ← MeasureTheory.integral_neg]
  congr 1
  funext u
  rw [hodd u]
  have : -(-u) / 2 = u / 2 := by ring
  rw [this]
  ring

theorem poleB_add_poleA_eq_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ u, f (-u) = -f u) :
    poleB f + poleA f = 0 := by
  rw [poleB_eq_neg_poleA_of_odd hodd, neg_add_cancel]

/-- **Primitive embedding of the odd sector.** On the scaling surface of `ℤ`, an odd test `f`
contributes zero to the degree against the ample class `H + V`:
`⟨aH + bV + f, H + V⟩ = a + b`. In particular, every pure odd test cycle `(0, 0, f)` is
automatically orthogonal to `H + V`. -/
theorem scalingPair_odd_ample_eq (x : ScalingCycle)
    (hodd : ∀ u, (x.2.2 : ℝ → ℝ) (-u) = -(x.2.2 : ℝ → ℝ) u) :
    scalingSurface.pair x scalingSurface.ample = x.1 + x.2.1 := by
  change scalingPairFun x ((1, 0, 0) + (0, 1, 0)) = x.1 + x.2.1
  have hB : poleB (x.2.2 : ℝ → ℝ) = -poleA (x.2.2 : ℝ → ℝ) := poleB_eq_neg_poleA_of_odd hodd
  simp only [Prod.mk_add_mk, add_zero, zero_add, scalingPairFun, Submodule.coe_zero,
    poleB_zero, poleA_zero, localPair_zero_right, hB]
  ring

theorem scalingPair_pure_odd_ample_eq_zero (f : realTests)
    (hodd : ∀ u, (f : ℝ → ℝ) (-u) = -(f : ℝ → ℝ) u) :
    scalingSurface.pair (0, 0, f) scalingSurface.ample = 0 := by
  rw [scalingPair_odd_ample_eq (0, 0, f) hodd, add_zero]

/-- **Self-intersection of a primitive odd cycle on `(H + V)⊥`.** When `x = aH + bV + f` has `f` odd
and is orthogonal to `H + V` (`a + b = 0`), its self-intersection on the scaling surface is
`-2(a + A(f))² - weilPair f f`, so the polar contribution `-2(a + A(f))²` is already nonpositive. -/
theorem scalingPair_odd_self_of_orthogonal_ample (x : ScalingCycle)
    (hodd : ∀ u, (x.2.2 : ℝ → ℝ) (-u) = -(x.2.2 : ℝ → ℝ) u)
    (horth : scalingSurface.pair x scalingSurface.ample = 0) :
    scalingSurface.pair x x =
      -2 * (x.1 + poleA (x.2.2 : ℝ → ℝ)) ^ 2 -
        weilPair (x.2.2 : ℝ → ℝ) (x.2.2 : ℝ → ℝ) := by
  have hab : x.1 + x.2.1 = 0 := by rwa [scalingPair_odd_ample_eq x hodd] at horth
  have hb : x.2.1 = -x.1 := by linarith
  have hB : poleB (x.2.2 : ℝ → ℝ) = -poleA (x.2.2 : ℝ → ℝ) := poleB_eq_neg_poleA_of_odd hodd
  change scalingPairFun x x = _
  simp only [scalingPairFun, localPair, hb, hB]
  ring

/-- The embedding `(a, b, f) ↦ (a, b, ↑f)` of a submodule `V ≤ realTests` into `ScalingCycle`. -/
def scalingSubsurfaceInclusion (V : Submodule ℝ realTests) :
    (ℝ × ℝ × V) →ₗ[ℝ] ScalingCycle where
  toFun x := (x.1, x.2.1, x.2.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The scaling subsurface of a test submodule `V ≤ realTests`** as a `PolarSurface`. -/
def scalingSubsurface (V : Submodule ℝ realTests) : PolarSurface (ℝ × ℝ × V) where
  pair := (scalingSurface.pair.comp (scalingSubsurfaceInclusion V)).compl₂
    (scalingSubsurfaceInclusion V)
  pair_comm x y := scalingSurface.pair_comm (x.1, x.2.1, x.2.2.1) (y.1, y.2.1, y.2.2.1)
  H := (1, 0, 0)
  V := (0, 1, 0)
  pair_H_H := scalingSurface.pair_H_H
  pair_V_V := scalingSurface.pair_V_V
  pair_H_V := scalingSurface.pair_H_V

@[simp]
theorem scalingSubsurface_pair_apply (V : Submodule ℝ realTests) (x y : ℝ × ℝ × V) :
    (scalingSubsurface V).pair x y =
      scalingSurface.pair (x.1, x.2.1, x.2.2.1) (y.1, y.2.1, y.2.2.1) := rfl

@[simp]
theorem scalingSubsurface_ample (V : Submodule ℝ realTests) :
    (scalingSubsurface V).ample = (1, 1, 0) := by
  ext <;> simp [PolarSurface.ample, scalingSubsurface]

/-- The Castelnuovo–Severi defect of `scalingSubsurface V` is `weilPair f f`. -/
theorem scalingSubsurface_defect_self (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    (scalingSubsurface V).defect x x =
      weilPair (x.2.2.1 : ℝ → ℝ) (x.2.2.1 : ℝ → ℝ) := by
  have h := scalingSurface_defect_self (x.1, x.2.1, x.2.2.1)
  rw [PolarSurface.defect_self] at h ⊢
  exact h

/-- The degree `x · (H + V)` on `scalingSubsurface V`. -/
theorem scalingSubsurface_pair_ample (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    (scalingSubsurface V).pair x (scalingSubsurface V).ample =
      x.1 + x.2.1 + poleB (x.2.2.1 : ℝ → ℝ) + poleA (x.2.2.1 : ℝ → ℝ) := by
  change scalingPairFun (x.1, x.2.1, x.2.2.1) ((1, 0, 0) + (0, 1, 0)) = _
  simp only [Prod.mk_add_mk, add_zero, zero_add, scalingPairFun, Submodule.coe_zero,
    poleB_zero, poleA_zero, localPair_zero_right]
  ring

/-- The self-intersection `x · x` on `scalingSubsurface V`. -/
theorem scalingSubsurface_pair_self (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    (scalingSubsurface V).pair x x =
      2 * (x.2.1 + poleB (x.2.2.1 : ℝ → ℝ)) * (x.1 + poleA (x.2.2.1 : ℝ → ℝ)) -
        weilPair (x.2.2.1 : ℝ → ℝ) (x.2.2.1 : ℝ → ℝ) := by
  have hd := scalingSubsurface_defect_self V x
  rw [PolarSurface.defect_self] at hd
  have hH : (scalingSubsurface V).pair x (scalingSubsurface V).H =
      x.2.1 + poleB (x.2.2.1 : ℝ → ℝ) := by
    change scalingPairFun (x.1, x.2.1, x.2.2.1) (1, 0, 0) = _
    simp only [scalingPairFun, Submodule.coe_zero, poleB_zero, poleA_zero, localPair_zero_right]
    ring
  have hV : (scalingSubsurface V).pair x (scalingSubsurface V).V =
      x.1 + poleA (x.2.2.1 : ℝ → ℝ) := by
    change scalingPairFun (x.1, x.2.1, x.2.2.1) (0, 1, 0) = _
    simp only [scalingPairFun, Submodule.coe_zero, poleB_zero, poleA_zero, localPair_zero_right]
    ring
  rw [hH, hV] at hd
  linarith

/-- **The coupled pole–test arithmetic effectivity cone** on `scalingSubsurface V`: pole coordinates
`(a, b)` and pole residues `(A(f), B(f))` are coupled directly to the arithmetic Weil/Schur energy
`weilPair f f`. -/
def coupledArithmeticCone (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  {x | 0 ≤ 2 * (x.2.1 + poleB (x.2.2.1 : ℝ → ℝ)) * (x.1 + poleA (x.2.2.1 : ℝ → ℝ)) -
      weilPair (x.2.2.1 : ℝ → ℝ) (x.2.2.1 : ℝ → ℝ) ∧
    0 ≤ x.1 + x.2.1 + poleB (x.2.2.1 : ℝ → ℝ) + poleA (x.2.2.1 : ℝ → ℝ)}

theorem coupledArithmeticCone_eq_positiveCone (V : Submodule ℝ realTests) :
    coupledArithmeticCone V = (scalingSubsurface V).positiveCone := by
  ext x
  simp only [coupledArithmeticCone, PolarSurface.positiveCone, Set.mem_setOf_eq,
    scalingSubsurface_pair_self, scalingSubsurface_pair_ample]

/-- Pairwise nonnegativity (Bézout property) of the positive cone on any polar surface satisfying
`HodgeIndex`. -/
theorem PolarSurface.pair_nonneg_of_positiveCone {C : Type*} [AddCommGroup C] [Module ℝ C]
    (S : PolarSurface C) (hH : S.HodgeIndex) {x y : C}
    (hx : x ∈ S.positiveCone) (hy : y ∈ S.positiveCone) :
    0 ≤ S.pair x y := by
  have hA : S.AmpleHodgeIndex :=
    S.ampleHodgeIndex_iff_castelnuovoSeveri.mpr (S.hodgeIndex_iff_castelnuovoSeveri.mp hH)
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
  have h1 : 0 ≤ 2 * S.pair x S.ample ^ 2 + S.pair u u := by linarith
  have h2 : 0 ≤ 2 * S.pair y S.ample ^ 2 + S.pair v v := by linarith
  have h3 : 0 ≤ 2 * S.pair x S.ample ^ 2 := by positivity
  have hprod : S.pair u u * S.pair v v ≤ (2 * S.pair x S.ample * S.pair y S.ample) ^ 2 := by
    nlinarith [mul_nonneg h1 (neg_nonneg.mpr hv_le), mul_nonneg h3 h2]
  have hsq : (4 * S.pair x y - 2 * S.pair x S.ample * S.pair y S.ample) ^ 2 ≤
      (2 * S.pair x S.ample * S.pair y S.ample) ^ 2 := by
    rw [← huv]
    exact le_trans hcs hprod
  nlinarith [sq_nonneg (S.pair x y), mul_nonneg hxA hyA]

/-- Whenever `weilPair f f ≥ 0` on `V`, `scalingSubsurface V` satisfies `HodgeIndex` and
`coupledArithmeticCone V` satisfies `RiemannRochAxiom`, `AmpleAxiom`, and pairwise Bézout
positivity. -/
theorem scalingSubsurface_hodgeIndex_of_weilPair_nonneg (V : Submodule ℝ realTests)
    (hV : ∀ f : V, 0 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ)) :
    (scalingSubsurface V).HodgeIndex := by
  rw [(scalingSubsurface V).hodgeIndex_iff_castelnuovoSeveri,
    (scalingSubsurface V).castelnuovoSeveri_iff_defect_nonneg]
  intro x
  rw [scalingSubsurface_defect_self]
  exact hV x.2.2

theorem coupledArithmeticCone_effectivity_of_weilPair_nonneg (V : Submodule ℝ realTests)
    (hV : ∀ f : V, 0 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ)) :
    (scalingSubsurface V).RiemannRochAxiom (coupledArithmeticCone V) ∧
      (scalingSubsurface V).AmpleAxiom (coupledArithmeticCone V) ∧
      (∀ x ∈ coupledArithmeticCone V, ∀ y ∈ coupledArithmeticCone V,
        0 ≤ (scalingSubsurface V).pair x y) := by
  have hH := scalingSubsurface_hodgeIndex_of_weilPair_nonneg V hV
  rw [coupledArithmeticCone_eq_positiveCone]
  exact ⟨((scalingSubsurface V).positiveCone_axioms hH).1,
    ((scalingSubsurface V).positiveCone_axioms hH).2,
    fun x hx y hy => (scalingSubsurface V).pair_nonneg_of_positiveCone hH hx hy⟩

/-- The submodule of odd real `C²` tests supported in `[−a, a]`. -/
def oddRealTestsAt (a : ℝ) : Submodule ℝ realTests where
  carrier := {f | tsupport (f : ℝ → ℝ) ⊆ Icc (-a) a ∧ ∀ u, (f : ℝ → ℝ) (-u) = -(f : ℝ → ℝ) u}
  add_mem' {f g} hf hg := ⟨(tsupport_add (f : ℝ → ℝ) (g : ℝ → ℝ)).trans
    (union_subset hf.1 hg.1), fun u => by simp [hf.2 u, hg.2 u]; ring⟩
  zero_mem' := ⟨by simp [tsupport], fun u => by simp⟩
  smul_mem' c f hf := ⟨(tsupport_smul_subset_right (fun _ : ℝ => c) (f : ℝ → ℝ)).trans hf.1,
    fun u => by simp [hf.2 u]⟩

/-- The submodule of all real `C²` tests supported in `[−a, a]`. -/
def realTestsAt (a : ℝ) : Submodule ℝ realTests where
  carrier := {f | tsupport (f : ℝ → ℝ) ⊆ Icc (-a) a}
  add_mem' {f g} hf hg := (tsupport_add (f : ℝ → ℝ) (g : ℝ → ℝ)).trans (union_subset hf hg)
  zero_mem' := by simp [tsupport]
  smul_mem' c f hf := (tsupport_smul_subset_right (fun _ : ℝ => c) (f : ℝ → ℝ)).trans hf

/-- **Coercive Weil positivity on `oddRealTestsAt a` past the first prime (`a ≤ 181/500`).** -/
theorem weilPair_ge_of_mem_oddRealTestsAt {a : ℝ} (ha : a ≤ 181 / 500)
    (f : oddRealTestsAt a) :
    1 / 1000 * ∫ u, (f.1 : ℝ → ℝ) u ^ 2 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) := by
  rw [weilPair_self_eq_zeta_W_re f.1.2.1 f.1.2.2, ← integral_norm_cx_sq]
  refine zetaZeroConfig_re_W_ge_of_odd_aperture_le_threeHundredSixtyTwoThousandths
    (cx_contDiff f.1.2.1) ?_ ?_
  · refine (closure_mono ?_).trans (f.2.1.trans (Icc_subset_Icc (by linarith) ha))
    intro u hu
    simp only [Function.mem_support, cx, ne_eq, Complex.ofReal_eq_zero] at hu ⊢
    exact hu
  · funext u
    simp only [testNeg, cx, f.2.2 u, Complex.ofReal_neg, Pi.smul_apply, smul_eq_mul, neg_one_mul]

/-- **Coercive negative-definiteness on the primitive odd subspace `(H + V)⊥` past the first prime
(`a ≤ 181/500`).** Every cycle `x = a₀ H + b₀ V + f` in `scalingSubsurface (oddRealTestsAt a)`
orthogonal to `H + V` satisfies
`x · x ≤ -2(a₀ + A(f))² - (1/1000) ∫ f² ≤ 0`. -/
theorem scalingSubsurface_odd_primitive_pair_self_le {a : ℝ} (ha : a ≤ 181 / 500)
    (x : ℝ × ℝ × oddRealTestsAt a)
    (horth : (scalingSubsurface (oddRealTestsAt a)).pair x
      (scalingSubsurface (oddRealTestsAt a)).ample = 0) :
    (scalingSubsurface (oddRealTestsAt a)).pair x x ≤
      -2 * (x.1 + poleA (x.2.2.1 : ℝ → ℝ)) ^ 2 -
        1 / 1000 * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 := by
  have horth' : scalingSurface.pair (x.1, x.2.1, x.2.2.1) scalingSurface.ample = 0 := horth
  have hself := scalingPair_odd_self_of_orthogonal_ample (x.1, x.2.1, x.2.2.1) x.2.2.2.2 horth'
  have hw := weilPair_ge_of_mem_oddRealTestsAt ha x.2.2
  change scalingSurface.pair (x.1, x.2.1, x.2.2.1) (x.1, x.2.1, x.2.2.1) ≤ _
  linarith

/-- **Unconditional Castelnuovo–Severi Hodge index on the odd scaling subsurface past the first
prime (`a ≤ 181/500`).** -/
theorem scalingSubsurface_odd_hodgeIndex {a : ℝ} (ha : a ≤ 181 / 500) :
    (scalingSubsurface (oddRealTestsAt a)).HodgeIndex :=
  scalingSubsurface_hodgeIndex_of_weilPair_nonneg (oddRealTestsAt a) fun f =>
    le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (weilPair_ge_of_mem_oddRealTestsAt ha f)

/-- **Unconditional coupled pole–test effectivity (`RiemannRochAxiom`, `AmpleAxiom`, and Bézout
positivity) on the odd scaling subsurface past the first prime (`a ≤ 181/500`).** -/
theorem coupledArithmeticCone_odd_effectivity {a : ℝ} (ha : a ≤ 181 / 500) :
    (scalingSubsurface (oddRealTestsAt a)).RiemannRochAxiom
      (coupledArithmeticCone (oddRealTestsAt a)) ∧
    (scalingSubsurface (oddRealTestsAt a)).AmpleAxiom
      (coupledArithmeticCone (oddRealTestsAt a)) ∧
    (∀ x ∈ coupledArithmeticCone (oddRealTestsAt a),
      ∀ y ∈ coupledArithmeticCone (oddRealTestsAt a),
        0 ≤ (scalingSubsurface (oddRealTestsAt a)).pair x y) :=
  coupledArithmeticCone_effectivity_of_weilPair_nonneg (oddRealTestsAt a) fun f =>
    le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (weilPair_ge_of_mem_oddRealTestsAt ha f)

/-- **Coercive Weil positivity on all-profile tests `realTestsAt a` for `a ≤ 3/10`.** -/
theorem weilPair_ge_of_mem_realTestsAt {a : ℝ} (ha : a ≤ 3 / 10) (f : realTestsAt a) :
    1 / 5000 * ∫ u, (f.1 : ℝ → ℝ) u ^ 2 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) := by
  rw [weilPair_self_eq_zeta_W_re f.1.2.1 f.1.2.2, ← integral_norm_cx_sq]
  refine zetaZeroConfig_re_W_ge_of_aperture_le_threeTenths (cx_contDiff f.1.2.1) ?_
  refine (closure_mono ?_).trans (f.2.trans (Icc_subset_Icc (by linarith) ha))
  intro u hu
  simp only [Function.mem_support, cx, ne_eq, Complex.ofReal_eq_zero] at hu ⊢
  exact hu

/-- **Unconditional Castelnuovo–Severi Hodge index and coupled pole–test effectivity on
`realTestsAt a` for `a ≤ 3/10`.** -/
theorem scalingSubsurface_all_hodgeIndex {a : ℝ} (ha : a ≤ 3 / 10) :
    (scalingSubsurface (realTestsAt a)).HodgeIndex ∧
    (scalingSubsurface (realTestsAt a)).RiemannRochAxiom
      (coupledArithmeticCone (realTestsAt a)) ∧
    (scalingSubsurface (realTestsAt a)).AmpleAxiom
      (coupledArithmeticCone (realTestsAt a)) ∧
    (∀ x ∈ coupledArithmeticCone (realTestsAt a),
      ∀ y ∈ coupledArithmeticCone (realTestsAt a),
        0 ≤ (scalingSubsurface (realTestsAt a)).pair x y) := by
  have hpos : ∀ f : realTestsAt a, 0 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) := fun f =>
    le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (weilPair_ge_of_mem_realTestsAt ha f)
  exact ⟨scalingSubsurface_hodgeIndex_of_weilPair_nonneg (realTestsAt a) hpos,
    coupledArithmeticCone_effectivity_of_weilPair_nonneg (realTestsAt a) hpos⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
