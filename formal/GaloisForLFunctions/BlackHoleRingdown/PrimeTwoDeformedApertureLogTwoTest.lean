import GaloisForLFunctions.BlackHoleRingdown.CausalIdentitiesCannotForceQuarterRingdown
import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLaw
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations
import GaloisForLFunctions.ZeroConfigurationGeometry.RamanujanIsRealityOfAnEulerColumn
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfANumberRingCountsTheZerosOfItsZetaFunction
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ArithmeticHawkingPagePhaseStructure

/-!
# Three-Scale Aperture Hierarchy of the Prime-Two Deformed Horizon System

For `1/2 < α < 1`, `BlackHoleRingdown.xiDeformed α` multiplies `ξ(s)` by the symmetric entire
prime-`2` factor `primeTwoFactor α s`, creating a vertical ladder of off-line zeros at
`Re s = α` and `Re s = 1 - α` with ordinate spacing `2π / log 2` while preserving the global
eternal-AdS KMS, Schur passivity, and prime-support dictionary above `p = 2` and violating
quarter-rate ringdown decay `O(e^{-τ / 4})`.

Superposing `zetaZeroConfig` with the prime-`2` off-line lattice configuration yields the exact
tempered zero configuration `xiDeformedZeroConfig α` of `xiDeformed α` and reveals a sharp
three-scale separation hierarchy:

1. **Sub-Nyquist mimicry (`a ≤ log 2 / 2`, all `α ∈ (1/2, 1)`):** Below the prime-`2` Nyquist
   half-width `log 2 / 2`, the prime-`2` ladder has the exact Weil form of a doubled on-line
   lattice and is nonnegative on every test, so `xiDeformedZeroConfig α` inherits the full
   `10⁻¹³` Weil floor of `ζ` simultaneously for all `α ∈ (1/2, 1)`.
2. **Masking at the certified two-prime aperture (`a = log 2`):** At half-width `log 2` (the second
   aliasing step `⌈2 a / log 2⌉ = 2`), the standalone prime-`2` off-line factor already has the
   strictly negative sharp ground energy `-2 log 2 (cosh((α - 1/2) log 2) - 1) < 0`. Nevertheless,
   the unconditional `10⁻¹³` spectral gap of `ζ` on `[-log 2, log 2]` absorbs this off-line deficit
   throughout an explicit interval `α ∈ (1/2, α₀)`, keeping `xiDeformedZeroConfig α` strictly
   Weil-positive at aperture `log 2` (`log 2 ≤ onsetAperture (xiDeformedZeroConfig α)`) while
    simultaneously zero-source coupling-endpoint competition favors the weak endpoint across all
   confinement scales `(u, v) ∈ ℝ²`.
3. **Global unbounded-aperture separation (`a → ∞`, all `α ∈ (1/2, 1)`):** Because `(α : ℂ)` lies
   off the critical line in `(xiDeformedZeroConfig α).carrier`, every `α ∈ (1/2, 1)` has finite
   onset aperture `onsetAperture (xiDeformedZeroConfig α) < ⊤` and violates Weil positivity on
   some finite window, whereas `RiemannHypothesis ↔ onsetAperture zetaZeroConfig = ⊤`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.BlackHoleRingdown

open Zeta23 _root_.RHTower
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ScaleSignedIncidenceCriticality
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.WindowVisibilityLaw
open GaloisForLFunctions.WindowTowerOfSpecZ
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-! ### 1. Zero configuration of the prime-`2` deformed completed zeta function -/

/-- Zero configuration of `primeTwoFactor α` (`1/2 < α < 1`), realized as the symmetric vertical
off-line lattice `{1/2 ± (α - 1/2) + 2π i k / log 2}`. -/
def primeTwoZeroConfig (α : ℝ) (h0 : 1 / 2 < α) (h1 : α < 1) : ZeroConfig :=
  offLineLatticeConfig (Real.log_pos one_lt_two)
    (sub_pos.mpr h0 : 0 < α - 1 / 2)
    (by linarith : α - 1 / 2 ≤ 1 / 2)

theorem temperedConfig_primeTwoZeroConfig {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1) :
    TemperedConfig (primeTwoZeroConfig α h0 h1) :=
  temperedConfig_offLineLatticeConfig (Real.log_pos one_lt_two) (sub_pos.mpr h0) (by linarith)

private theorem one_sub_two_cpow_sub_eq_zero_iff (δ : ℝ) (s : ℂ) :
    1 - (2 : ℂ) ^ (((1 / 2 + δ : ℝ) : ℂ) - s) = 0 ↔
      s ∈ Set.range (verticalLatticePoint (Real.log 2) δ) := by
  have h2 : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  have hexp : ∀ z : ℂ, (2 : ℂ) ^ z = Complex.exp (z * ((Real.log 2 : ℝ) : ℂ)) := by
    intro z
    rw [Complex.cpow_def_of_ne_zero two_ne_zero,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  rw [sub_eq_zero, eq_comm, hexp, ← natCast_cpow_neg_eq_iff one_lt_two δ s,
    natCast_cpow_neg (by norm_num : (2 : ℕ) ≠ 0) s]
  simp only [Nat.cast_ofNat, Complex.ofReal_exp]
  constructor
  · intro h
    have hmul := congrArg (· * Complex.exp (-(((1 / 2 + δ) * Real.log 2 : ℝ) : ℂ))) h
    dsimp only at hmul
    rw [one_mul, ← Complex.exp_add] at hmul
    convert hmul using 2
    push_cast
    ring
  · intro h
    have hmul := congrArg (· * Complex.exp (((1 / 2 + δ) * Real.log 2 : ℝ) : ℂ)) h
    dsimp only at hmul
    rw [← Complex.exp_add, ← Complex.exp_add] at hmul
    have hrhs : (-((1 / 2 + δ) * Real.log 2 : ℝ) : ℂ) + (((1 / 2 + δ) * Real.log 2 : ℝ) : ℂ) = 0 := by
      ring
    rw [hrhs, Complex.exp_zero] at hmul
    convert hmul using 2
    push_cast
    ring

/-- The carrier of `primeTwoZeroConfig α` is the exact zero locus of `primeTwoFactor α`. -/
theorem carrier_primeTwoZeroConfig {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1) :
    (primeTwoZeroConfig α h0 h1).carrier = {s : ℂ | primeTwoFactor α s = 0} := by
  ext s
  have hne : (2 : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero two_ne_zero]
    exact Complex.exp_ne_zero _
  have hα1 : (α : ℂ) = ((1 / 2 + (α - 1 / 2) : ℝ) : ℂ) := by push_cast; ring
  have hα2 : ((1 - α : ℝ) : ℂ) = ((1 / 2 + -(α - 1 / 2) : ℝ) : ℂ) := by push_cast; ring
  change s ∈ Set.range (verticalLatticePoint (Real.log 2) (α - 1 / 2)) ∪
      Set.range (verticalLatticePoint (Real.log 2) (-(α - 1 / 2))) ↔
    primeTwoFactor α s = 0
  unfold primeTwoFactor
  rw [hα1, hα2, mul_assoc, mul_eq_zero, or_iff_right hne, mul_eq_zero,
    one_sub_two_cpow_sub_eq_zero_iff, one_sub_two_cpow_sub_eq_zero_iff, Set.mem_union]

/-- Exact zero configuration of `xiDeformed α`, obtained by superposing `zetaZeroConfig` with
`primeTwoZeroConfig α`. -/
def xiDeformedZeroConfig (α : ℝ) (h0 : 1 / 2 < α) (h1 : α < 1) : ZeroConfig :=
  superposeFamily ![zetaZeroConfig, primeTwoZeroConfig α h0 h1]

theorem temperedConfig_xiDeformedZeroConfig {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1) :
    TemperedConfig (xiDeformedZeroConfig α h0 h1) :=
  temperedConfig_superposeFamily _ (Fin.forall_fin_two.mpr
    ⟨temperedConfig_zetaZeroConfig, temperedConfig_primeTwoZeroConfig h0 h1⟩)

theorem mem_zetaZeroConfig_carrier_iff_xi_eq_zero (s : ℂ) :
    s ∈ zetaZeroConfig.carrier ↔ _root_.RHTower.xi s = 0 :=
  ⟨fun hs => (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hs).1,
   _root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_of_xi_eq_zero⟩

/-- The carrier of `xiDeformedZeroConfig α` is the exact zero locus of `xiDeformed α`. -/
theorem carrier_xiDeformedZeroConfig {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1) :
    (xiDeformedZeroConfig α h0 h1).carrier = {s : ℂ | xiDeformed α s = 0} := by
  ext s
  change (∃ i : Fin 2, s ∈ (![zetaZeroConfig, primeTwoZeroConfig α h0 h1] i).carrier) ↔
    primeTwoFactor α s * _root_.RHTower.xi s = 0
  rw [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    mem_zetaZeroConfig_carrier_iff_xi_eq_zero, carrier_primeTwoZeroConfig h0 h1, Set.mem_setOf_eq,
    mul_eq_zero, or_comm]

theorem alpha_mem_xiDeformedZeroConfig_carrier {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1) :
    (α : ℂ) ∈ (xiDeformedZeroConfig α h0 h1).carrier := by
  rw [carrier_xiDeformedZeroConfig h0 h1, Set.mem_setOf_eq, xiDeformed,
    primeTwoFactor_eval_self, zero_mul]

/-- Additivity of the Weil sesquilinear form on `xiDeformedZeroConfig α`. -/
theorem W_xiDeformedZeroConfig {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    (xiDeformedZeroConfig α h0 h1).W f g =
      zetaZeroConfig.W f g + (primeTwoZeroConfig α h0 h1).W f g := by
  rw [xiDeformedZeroConfig,
    W_superposeFamily _ (Fin.forall_fin_two.mpr
      ⟨temperedConfig_zetaZeroConfig, temperedConfig_primeTwoZeroConfig h0 h1⟩) hf hfc hg hgc,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ### 2. Sub-Nyquist mimicry (`a ≤ log 2 / 2`) and global separation (`a → ∞`) -/

private theorem hasCompactSupport_of_tsupport_Icc {a : ℝ} {f : ℝ → ℂ}
    (hfs : tsupport f ⊆ Icc (-a) a) : HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)

/-- **Sub-Nyquist Uniform Floor (`a ≤ log 2 / 2`).** Below the prime-`2` Nyquist half-width
`log 2 / 2`, every deformed system `xiDeformedZeroConfig α` (`1/2 < α < 1`) inherits the full
`10⁻¹³` Weil floor of `ζ`, uniformly in `α`. -/
theorem xiDeformedZeroConfig_re_W_ge_below_nyquist {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1)
    {a : ℝ} (ha : a ≤ Real.log 2 / 2) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    (1 / 10 ^ 13 : ℝ) * (∫ u, ‖f u‖ ^ 2) ≤ ((xiDeformedZeroConfig α h0 h1).W f f).re := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_Icc hfs
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfs_log2 : tsupport f ⊆ Icc (-Real.log 2) (Real.log 2) :=
    hfs.trans (Icc_subset_Icc (by linarith) (by linarith))
  have hζ := zetaZeroConfig_re_W_ge_at_aperture_log_two hf hfs_log2
  have hp2 : 0 ≤ ((primeTwoZeroConfig α h0 h1).W f f).re :=
    (offLineLattice_weil_positive_iff hlog2 (sub_pos.mpr h0) (by linarith) a).mpr ha f hf hfs
  rw [W_xiDeformedZeroConfig h0 h1 hf hfc hf hfc, Complex.add_re]
  linarith

/-- Every deformed system `xiDeformedZeroConfig α` (`1/2 < α < 1`) is window-positive up to the
prime-`2` Nyquist half-width `log 2 / 2`, so `log 2 / 2 ≤ onsetAperture (xiDeformedZeroConfig α)`. -/
theorem half_log_two_le_onsetAperture_xiDeformedZeroConfig {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1) :
    ((Real.log 2 / 2 : ℝ) : EReal) ≤ onsetAperture (xiDeformedZeroConfig α h0 h1) := by
  have hlog2 : 0 < Real.log 2 / 2 := by positivity
  refine le_onsetAperture_of_windowPositiveAt hlog2.le fun f hf hfs => ?_
  have hfloor := xiDeformedZeroConfig_re_W_ge_below_nyquist h0 h1 le_rfl hf hfs
  have hint : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Global Multi-Aperture Separation (`a → ∞`).** For every `α ∈ (1/2, 1)`, the deformed zero
configuration `xiDeformedZeroConfig α` has finite onset aperture `< ⊤` and takes strictly negative
Weil values on some finite window, whereas `RiemannHypothesis ↔ onsetAperture zetaZeroConfig = ⊤`. -/
theorem onsetAperture_xiDeformedZeroConfig_lt_top {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1) :
    onsetAperture (xiDeformedZeroConfig α h0 h1) < ⊤ ∧
      ∃ (a : ℝ) (f : ℝ → ℂ), 0 < a ∧ ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        ((xiDeformedZeroConfig α h0 h1).W f f).re < 0 := by
  have htemp := temperedConfig_xiDeformedZeroConfig h0 h1
  have hne_top : onsetAperture (xiDeformedZeroConfig α h0 h1) ≠ ⊤ := by
    rw [Ne, onsetAperture_eq_top_iff_onLine htemp]
    intro hall
    have hre := hall (α : ℂ) (alpha_mem_xiDeformedZeroConfig_carrier h0 h1)
    rw [Complex.ofReal_re] at hre
    linarith
  have hlt_top : onsetAperture (xiDeformedZeroConfig α h0 h1) < ⊤ := lt_top_iff_ne_top.mpr hne_top
  refine ⟨hlt_top, ?_⟩
  cases hval : onsetAperture (xiDeformedZeroConfig α h0 h1) with
  | bot =>
    exfalso
    have h0le := zero_le_onsetAperture (xiDeformedZeroConfig α h0 h1)
    rw [hval] at h0le
    exact absurd h0le (by decide)
  | top => exact absurd hval hne_top
  | coe b =>
    have hb0 : 0 ≤ b := EReal.coe_le_coe_iff.mp
      (hval ▸ zero_le_onsetAperture (xiDeformedZeroConfig α h0 h1))
    have hapos : 0 < b + 1 := by linarith
    have hlt_a : onsetAperture (xiDeformedZeroConfig α h0 h1) < ((b + 1 : ℝ) : EReal) := by
      rw [hval, EReal.coe_lt_coe_iff]; linarith
    obtain ⟨f, hf, hfs, hneg⟩ :=
      (exists_re_W_neg_iff_onsetAperture_lt htemp hapos.le).mpr hlt_a
    exact ⟨b + 1, f, hapos, hf, hfs, hneg⟩

/-! ### 3. Sharp standalone deficit and masking at the certified aperture `log 2` -/

/-- **Exact Standalone Deficit of `primeTwoZeroConfig α` at Aperture `log 2`.**
At half-width `log 2` (twice its Nyquist half-width), `primeTwoZeroConfig α` satisfies the sharp
lower bound `Re W(f, f) ≥ -2 log 2 (cosh((α - 1/2) log 2) - 1) ∫ ‖f‖²` on every `C²` test
supported in `[-log 2, log 2]`, and even polar-constrained tests come arbitrarily close to this
strictly negative floor. -/
theorem primeTwoZeroConfig_re_W_ge_and_sharp_at_aperture_log_two {α : ℝ}
    (h0 : 1 / 2 < α) (h1 : α < 1) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-Real.log 2) (Real.log 2) →
      -weilFloorThreshold (Real.log 2) (α - 1 / 2) * (∫ u, ‖f u‖ ^ 2) ≤
        ((primeTwoZeroConfig α h0 h1).W f f).re) ∧
    0 < weilFloorThreshold (Real.log 2) (α - 1 / 2) ∧
    (∀ ε : ℝ, 0 < ε → ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧
      tsupport f ⊆ Icc (-Real.log 2) (Real.log 2) ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ((primeTwoZeroConfig α h0 h1).W f f).re <
        (-weilFloorThreshold (Real.log 2) (α - 1 / 2) + ε) * ∫ u, ‖f u‖ ^ 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hδ : 0 < α - 1 / 2 := sub_pos.mpr h0
  have hδ' : α - 1 / 2 ≤ 1 / 2 := by linarith
  have hceil : ⌈2 * Real.log 2 / Real.log 2⌉₊ = 2 :=
    ceil_two_mul_div_eq_two hlog2 (by linarith) le_rfl
  have hfl2 : latticeFloor (Real.log 2) (α - 1 / 2) 2 =
      2 - 2 * Real.cosh ((α - 1 / 2) * Real.log 2) :=
    latticeFloor_two (mul_pos hδ hlog2)
  have hcoef : Real.log 2 * latticeFloor (Real.log 2) (α - 1 / 2) ⌈2 * Real.log 2 / Real.log 2⌉₊ =
      -weilFloorThreshold (Real.log 2) (α - 1 / 2) := by
    rw [hceil, hfl2, weilFloorThreshold]
    ring
  refine ⟨fun f hf hfs => ?_, ?_, fun ε hε => ?_⟩
  · have h := offLineLattice_weil_floor hlog2 hδ hδ' hf hfs
    rwa [hcoef] at h
  · have hcosh : 1 < Real.cosh ((α - 1 / 2) * Real.log 2) :=
      Real.one_lt_cosh.mpr (mul_pos hδ hlog2).ne'
    unfold weilFloorThreshold
    nlinarith
  · have hμ : latticeFloor (Real.log 2) (α - 1 / 2) ⌈2 * Real.log 2 / Real.log 2⌉₊ <
        (-weilFloorThreshold (Real.log 2) (α - 1 / 2) + ε) / Real.log 2 := by
      rw [lt_div_iff₀ hlog2, mul_comm, hcoef]
      linarith
    obtain ⟨f, hf, hfs, hp, hm, hlt⟩ :=
      offLineLattice_hodge_floor_sharp hlog2 hδ hδ' (by linarith : Real.log 2 / 2 < Real.log 2) hμ
    refine ⟨f, hf, hfs, hp, hm, ?_⟩
    have hmul : Real.log 2 * ((-weilFloorThreshold (Real.log 2) (α - 1 / 2) + ε) / Real.log 2) =
        -weilFloorThreshold (Real.log 2) (α - 1 / 2) + ε :=
      mul_div_cancel₀ _ hlog2.ne'
    rwa [hmul] at hlt

/-- **Combined Weil Floor of `xiDeformedZeroConfig α` at Aperture `log 2`.**
Every `C²` test `f` supported in `[-log 2, log 2]` satisfies
`(10⁻¹³ - 2 log 2 (cosh((α - 1/2) log 2) - 1)) ∫ ‖f‖² ≤ Re W_{ξ_α}(f, f)`. -/
theorem xiDeformedZeroConfig_re_W_ge_at_aperture_log_two {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-Real.log 2) (Real.log 2)) :
    (1 / 10 ^ 13 - weilFloorThreshold (Real.log 2) (α - 1 / 2)) * (∫ u, ‖f u‖ ^ 2) ≤
      ((xiDeformedZeroConfig α h0 h1).W f f).re := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_Icc hfs
  have hζ := zetaZeroConfig_re_W_ge_at_aperture_log_two hf hfs
  have hp2 := (primeTwoZeroConfig_re_W_ge_and_sharp_at_aperture_log_two h0 h1).1 f hf hfs
  rw [W_xiDeformedZeroConfig h0 h1 hf hfc hf hfc, Complex.add_re]
  linarith

/-- **Non-Separation of `[FLOORLOG2]` and `[ADS-NOGO]` at Fixed Aperture `log 2`, and Global
Unbounded-Aperture Separation.**
There exists `α₀ ∈ (1/2, 1)` such that for every `α ∈ (1/2, α₀)`:
1. `xiDeformed α` has the off-line zero `(α : ℂ)` and `deformedReflectedField α` fails quarter-rate
   ringdown `O(e^{-τ / 4})` on a smooth compactly supported boundary pulse;
2. on the certified two-prime window `[-log 2, log 2]`, `xiDeformedZeroConfig α` retains the uniform
   positive Weil floor `(1 / (2 · 10¹³)) ∫ ‖f‖² ≤ Re W(f, f)` on all `C²` tests, so
   `WindowPositiveAt (xiDeformedZeroConfig α) (log 2)` holds and
   `log 2 ≤ onsetAperture (xiDeformedZeroConfig α)`;
3. zero-source coupling-endpoint competition strictly selects the weak confinement endpoint across
   all scales `(u, v) ∈ ℝ²`;
4. yet globally across all apertures, `onsetAperture (xiDeformedZeroConfig α) < ⊤` for every
   `α ∈ (1/2, 1)`, whereas `RiemannHypothesis ↔ onsetAperture zetaZeroConfig = ⊤`. -/
theorem exists_adsNoGo_nonseparation_at_aperture_log_two :
    ∃ α₀ ∈ Ioo (1 / 2 : ℝ) 1,
      (∀ α : ℝ, ∀ (h0 : 1 / 2 < α) (h1 : α < 1), α < α₀ →
        xiDeformed α (α : ℂ) = 0 ∧
        (¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
          ‖deformedReflectedField α (excitingPulse (((α : ℂ) - 1) / 2)) τ‖ ≤
            C * Real.exp (-(1 / 4) * τ)) ∧
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-Real.log 2) (Real.log 2) →
          (1 / (2 * 10 ^ 13) : ℝ) * (∫ u, ‖f u‖ ^ 2) ≤
            ((xiDeformedZeroConfig α h0 h1).W f f).re) ∧
        WindowPositiveAt (xiDeformedZeroConfig α h0 h1) (Real.log 2) ∧
        ((Real.log 2 : ℝ) : EReal) ≤ onsetAperture (xiDeformedZeroConfig α h0 h1) ∧
        onsetAperture (xiDeformedZeroConfig α h0 h1) < ⊤) ∧
      (∀ u v : ℝ,
        confiningSourceEnergy 0 (Real.exp u) <
          confiningSourceEnergy 0 (Real.exp u + Real.exp v)) ∧
      (RiemannHypothesis ↔ onsetAperture zetaZeroConfig = ⊤) := by
  set φ : ℝ → ℝ := fun α => weilFloorThreshold (Real.log 2) (α - 1 / 2)
  have hcont : Continuous φ := by
    unfold φ weilFloorThreshold
    fun_prop
  have hφ_half : φ (1 / 2) = 0 := by
    simp [φ, weilFloorThreshold]
  have hε : (0 : ℝ) < 1 / (2 * 10 ^ 13) := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hcont.continuousAt _ hε
  set α₀ : ℝ := 1 / 2 + min (1 / 4) (δ / 2)
  have hmin_pos : 0 < min (1 / 4) (δ / 2) := lt_min (by norm_num) (by positivity)
  have hα₀_mem : α₀ ∈ Ioo (1 / 2 : ℝ) 1 :=
    ⟨by dsimp [α₀]; linarith, by dsimp [α₀]; linarith [min_le_left (1 / 4) (δ / 2)]⟩
  refine ⟨α₀, hα₀_mem, ?_,
    fun u v => confiningSourceEnergy_weak_endpoint_strict_lt u v
      (criticalAliasCoefficient_positive zero_lt_one).le,
    riemannHypothesis_iff_onsetAperture_zeta_eq_top⟩
  intro α h0 h1 hα_lt
  have hdist : dist α (1 / 2) < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr h0)]
    have hle : min (1 / 4) (δ / 2) ≤ δ / 2 := min_le_right _ _
    dsimp [α₀] at hα_lt
    linarith
  have hφ_lt : φ α < 1 / (2 * 10 ^ 13) := by
    have h := hδ hdist
    rw [Real.dist_eq, hφ_half, sub_zero] at h
    exact (le_abs_self (φ α)).trans_lt h
  have hfloor : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-Real.log 2) (Real.log 2) →
      (1 / (2 * 10 ^ 13) : ℝ) * (∫ u, ‖f u‖ ^ 2) ≤
        ((xiDeformedZeroConfig α h0 h1).W f f).re := by
    intro f hf hfs
    have hge := xiDeformedZeroConfig_re_W_ge_at_aperture_log_two h0 h1 hf hfs
    have hint : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hcoef : (1 / (2 * 10 ^ 13) : ℝ) ≤ 1 / 10 ^ 13 - φ α := by linarith
    exact (mul_le_mul_of_nonneg_right hcoef hint).trans hge
  have hwpos : WindowPositiveAt (xiDeformedZeroConfig α h0 h1) (Real.log 2) := by
    intro f hf hfs
    have hge := hfloor f hf hfs
    have hint : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    nlinarith
  refine ⟨by rw [xiDeformed, primeTwoFactor_eval_self, zero_mul],
    not_deformedReflectedField_decay_gt h0 h1 (by linarith),
    hfloor, hwpos,
    le_onsetAperture_of_windowPositiveAt (Real.log_pos one_lt_two).le hwpos,
    (onsetAperture_xiDeformedZeroConfig_lt_top h0 h1).1⟩

#print axioms primeTwoZeroConfig_re_W_ge_and_sharp_at_aperture_log_two
#print axioms onsetAperture_xiDeformedZeroConfig_lt_top
#print axioms exists_adsNoGo_nonseparation_at_aperture_log_two

end GaloisForLFunctions.BlackHoleRingdown
