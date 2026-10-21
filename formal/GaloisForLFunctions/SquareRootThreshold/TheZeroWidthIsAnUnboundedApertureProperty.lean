import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.SquareRootThreshold.WeilPositivityForcesTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.OnLineShadowIndistinguishability
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations

/-!
# The zero width is an unbounded-aperture property

For a zero configuration `Z` let `configWidth Z = sup |Re ρ − ½|` be its width; for `ζ` this is
`zetaZeroWidth`. The Weil form of `Z` on tests supported in `[−a, a]` is the form "at aperture
`a`". Two facts, one positive and one negative, say exactly what the aperture buys.

* **Unbounded aperture is faithful** (`configWidth_eq_zero_iff_weil_nonneg`). A tempered
  configuration has width zero iff its Weil form is nonnegative on every compactly supported `C²`
  test, and the negativity rate of the form along the lag family is the width
  (`configWidth_le_iff_lag_twoBump_ge_neg_exp`).
* **Every bounded aperture is blind to every width** (`exists_configWidth_eq_and_weil_nonneg_on_aperture`).
  For every aperture `a > 0` and every depth `δ ∈ (0, ½]` there is a tempered configuration of
  width exactly `δ`, the off-line lattice `{½ ± δ + πik/a}`, whose Weil form is nonnegative on every
  test of aperture `a`; below that aperture its form is literally the form of an on-line
  configuration (`exists_configWidth_eq_and_onLineShadow_on_aperture`): invisibility is mimicry.

Hence no bounded aperture decides the width (`not_forall_configWidth_eq_zero_of_weil_nonneg_on_aperture`),
while the full aperture range does (`configWidth_unbounded_aperture_property`). A positivity
certificate at a finite aperture, however large, is consistent with every width; the width lives
in the limit `a → ∞` alone. The exchange rate is the Nyquist law: the lattice of ordinate spacing
`2π/L` hides exactly up to the aperture `L/2` (`offLineLattice_weil_positive_iff`).
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### 1. The width of a configuration -/

/-- The width of a zero configuration: the supremum of `|Re ρ − ½|` over its zeros. -/
noncomputable def configWidth (Z : ZeroConfig) : ℝ :=
  sSup ((fun ρ : ℂ => |ρ.re - 1 / 2|) '' Z.carrier)

/-- The zero width of `ζ` is the width of its configuration. -/
theorem zetaZeroWidth_eq_configWidth : zetaZeroWidth = configWidth zetaZeroConfig := rfl

theorem abs_re_sub_half_le_half_of_mem {Z : ZeroConfig} {ρ : ℂ} (hρ : ρ ∈ Z.carrier) :
    |ρ.re - 1 / 2| ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := Z.strip ρ hρ
  rw [abs_le]; constructor <;> linarith

theorem bddAbove_configWidth_image (Z : ZeroConfig) :
    BddAbove ((fun ρ : ℂ => |ρ.re - 1 / 2|) '' Z.carrier) :=
  ⟨1 / 2, by rintro _ ⟨ρ, hρ, rfl⟩; exact abs_re_sub_half_le_half_of_mem hρ⟩

theorem abs_re_sub_half_le_configWidth {Z : ZeroConfig} {ρ : ℂ} (hρ : ρ ∈ Z.carrier) :
    |ρ.re - 1 / 2| ≤ configWidth Z :=
  le_csSup (bddAbove_configWidth_image Z) ⟨ρ, hρ, rfl⟩

theorem configWidth_nonneg (Z : ZeroConfig) : 0 ≤ configWidth Z :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _

theorem configWidth_le_half (Z : ZeroConfig) : configWidth Z ≤ 1 / 2 :=
  Real.sSup_le (by rintro _ ⟨ρ, hρ, rfl⟩; exact abs_re_sub_half_le_half_of_mem hρ) (by norm_num)

/-- `configWidth Z ≤ σ` iff every zero has `Re ρ ≤ ½ + σ` (the reflection supplies the other side). -/
theorem configWidth_le_iff_re_le {Z : ZeroConfig} {σ : ℝ} (hσ : 0 ≤ σ) :
    configWidth Z ≤ σ ↔ ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + σ := by
  constructor
  · intro h ρ hρ
    have := (abs_re_sub_half_le_configWidth hρ).trans h
    linarith [(abs_le.mp this).2]
  · intro h
    refine Real.sSup_le ?_ hσ
    rintro _ ⟨ρ, hρ, rfl⟩
    have h1 := h ρ hρ
    have h2 := h _ (Z.reflect_mem ρ hρ)
    rw [reflect_re] at h2
    rw [abs_le]; constructor <;> linarith

/-- Width zero is the critical line. -/
theorem configWidth_eq_zero_iff_onLine {Z : ZeroConfig} :
    configWidth Z = 0 ↔ ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  constructor
  · intro h ρ hρ
    have := abs_re_sub_half_le_configWidth hρ
    rw [h, abs_nonpos_iff] at this
    linarith
  · intro h
    refine le_antisymm ?_ (configWidth_nonneg Z)
    exact (configWidth_le_iff_re_le le_rfl).mpr fun ρ hρ => by rw [h ρ hρ]; norm_num

/-! ### 2. Unbounded aperture is faithful -/

/-- **Weil criterion for configurations in width form.** A tempered configuration has width zero
iff its Weil form is nonnegative on every compactly supported `C²` test. -/
theorem configWidth_eq_zero_iff_weil_nonneg {Z : ZeroConfig} (hZ : TemperedConfig Z) :
    configWidth Z = 0 ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ (Z.W f f).re :=
  configWidth_eq_zero_iff_onLine.trans (weil_nonneg_iff_onLine Z hZ).symm

/-- **The negativity rate of the lag family is the width.** -/
theorem configWidth_le_iff_lag_twoBump_ge_neg_exp {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    configWidth Z ≤ σ ↔ ∃ C V : ℝ, ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
      (Z.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re :=
  (configWidth_le_iff_re_le hσ).trans (re_le_iff_lag_twoBump_ge_neg_exp Z hZ hlt hw hgood hσ)

/-! ### 3. Every bounded aperture is blind to every width -/

/-- The off-line lattice `{½ ± δ + 2πik/L}` has width exactly `δ`. -/
theorem configWidth_offLineLatticeConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    configWidth (offLineLatticeConfig hL hδ hδ') = δ := by
  have himage : (fun ρ : ℂ => |ρ.re - 1 / 2|) '' (offLineLatticeConfig hL hδ hδ').carrier = {δ} := by
    ext x
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      rcases hρ with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · show |(verticalLatticePoint L δ k).re - 1 / 2| = δ
        simp [verticalLatticePoint, abs_of_pos hδ]
      · show |(verticalLatticePoint L (-δ) k).re - 1 / 2| = δ
        simp [verticalLatticePoint, abs_of_pos hδ]
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      refine ⟨verticalLatticePoint L δ 0, Or.inl ⟨0, rfl⟩, ?_⟩
      show |(verticalLatticePoint L δ 0).re - 1 / 2| = δ
      simp [verticalLatticePoint, abs_of_pos hδ]
  rw [configWidth, himage, csSup_singleton]

/-- **Every bounded aperture is blind to every width.** For every aperture `a > 0` and depth
`δ ∈ (0, ½]` there is a tempered configuration of width `δ` whose Weil form is nonnegative on every
`C²` test supported in `[−a, a]`: the off-line lattice of ordinate spacing `π/a`. -/
theorem exists_configWidth_eq_and_weil_nonneg_on_aperture {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ configWidth Z = δ ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  exact ⟨offLineLatticeConfig hL hδ hδ', temperedConfig_offLineLatticeConfig hL hδ hδ',
    configWidth_offLineLatticeConfig hL hδ hδ',
    (offLineLattice_weil_positive_iff hL hδ hδ' a).mpr (by linarith)⟩

/-- **Invisibility is mimicry.** The same lattice has, below the aperture `a`, the Weil form of a
weighted on-line periodic configuration of weight `2`. -/
theorem exists_configWidth_eq_and_onLineShadow_on_aperture {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ configWidth Z = δ ∧ ∃ (c w : Fin 1 → ℝ), w 0 = 2 ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        Z.W f f = ((onLineShadow (2 * a) c w f : ℝ) : ℂ) := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  exact ⟨offLineLatticeConfig hL hδ hδ', temperedConfig_offLineLatticeConfig hL hδ hδ',
    configWidth_offLineLatticeConfig hL hδ hδ',
    offLineLattice_onLineShadow hL hδ hδ' ha (by linarith)⟩

/-- **No bounded aperture decides the width.** -/
theorem not_forall_configWidth_eq_zero_of_weil_nonneg_on_aperture {a : ℝ} (ha : 0 < a) :
    ¬ ∀ Z : ZeroConfig, TemperedConfig Z →
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re) →
        configWidth Z = 0 := by
  intro h
  obtain ⟨Z, hZ, hw, hpos⟩ :=
    exists_configWidth_eq_and_weil_nonneg_on_aperture ha (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
  linarith [h Z hZ hpos]

/-! ### 4. The principle -/

/-- **The width is an unbounded-aperture property.** Positivity of the Weil form on all compactly
supported tests is width zero, and positivity at any one aperture is consistent with every width. -/
theorem configWidth_unbounded_aperture_property :
    (∀ Z : ZeroConfig, TemperedConfig Z → (configWidth Z = 0 ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ (Z.W f f).re)) ∧
    ∀ a : ℝ, 0 < a → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∃ Z : ZeroConfig, TemperedConfig Z ∧ configWidth Z = δ ∧
        ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re :=
  ⟨fun _ hZ => configWidth_eq_zero_iff_weil_nonneg hZ,
    fun _ ha _ hδ hδ' => exists_configWidth_eq_and_weil_nonneg_on_aperture ha hδ hδ'⟩

/-- RH is the vanishing of the width of the configuration of `ζ`. -/
theorem riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero :
    RiemannHypothesis ↔ configWidth zetaZeroConfig = 0 :=
  riemannHypothesis_iff_zetaZeroWidth_eq_zero

end GaloisForLFunctions.SquareRootThreshold
