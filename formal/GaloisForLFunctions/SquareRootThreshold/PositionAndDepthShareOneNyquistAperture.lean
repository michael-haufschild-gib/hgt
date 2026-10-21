import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsAnUnboundedApertureProperty
import GaloisForLFunctions.SquareRootThreshold.NyquistResolutionOfTheWeilForm

/-!
# Position and depth share one Nyquist aperture

Two limits of the Weil form on tests of a bounded aperture are usually stated separately: a finite
aperture cannot *resolve the positions* of zeros closer than its Nyquist spacing, and a finite
aperture cannot *orient* a zero relative to the critical line, so positivity does not locate
zeros. For the vertical lattices of density `L/π` both are one law with one threshold `L/2`.

Fix `L > 0` and the three configurations
* `D = {½ + 2πik/L}` with multiplicity two (`onLineLatticeConfig`);
* `S = {½ + πik/L}` simple (`simpleHalfLatticeConfig`): the same density, another carrier;
* `P_δ = {½ ± δ + 2πik/L}` simple, `0 < δ ≤ ½` (`offLineLatticeConfig`): the same density,
  width `δ`.

* **Flat value** (`weil_eq_flat_of_le_nyquist`). On every `C²` test supported in `[−a, a]` with
  `a ≤ L/2` the three forms equal `2L∫|f|²`: the form reads the density and nothing else.
* **Position face** (`onLineLattices_agree_iff_le_nyquist`). `D` and `S` agree on every test of
  aperture `a` iff `a ≤ L/2`. Below, the flat value; above, `eq_of_weil_eq_of_separated` with
  separation `π/L` would force `D = S`.
* **Depth face** (`offLineLattice_agrees_iff_le_nyquist`). `P_δ` and `D` agree on every test of
  aperture `a` iff `a ≤ L/2`, for every depth. Above, the two-bump test of
  `exists_re_W_offLineLatticeConfig_neg` makes `P_δ` negative while `D` is nonnegative.
* **One law** (`position_and_depth_share_nyquist_aperture`). The position face holds at an
  aperture iff the depth face holds there for every depth, and below the common threshold the
  position mimic `S` and every depth mimic `P_δ` coincide on the aperture. The aperture-`a`
  fibre through `D` contains a second on-line configuration and a configuration of every width
  `δ ∈ (0, ½]` for `a ≤ L/2` (`nyquist_fibre_through_onLineLattice`), and both mimics are
  detected for `a > L/2` (`mimics_detected_of_nyquist_lt`).

The mean spacing of the ordinates of `ζ` near height `γ₀` is `2π/log γ₀`, so the analogous
threshold grows like `(log γ₀)/4`: no bounded aperture resolves positions or depths at all
heights, which is the aperture property of the zero width
(`configWidth_unbounded_aperture_property`) in the language of resolution.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The flat value below the Nyquist aperture -/

/-- Below the Nyquist aperture `L/2` the double on-line lattice, the simple on-line lattice and
the off-line lattice pair of every depth have the same Weil form `2L∫|f|²`. -/
theorem weil_eq_flat_of_le_nyquist {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {a : ℝ} (haL : a ≤ L / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    (onLineLatticeConfig hL).W f f = 2 * L * ∫ t, f t * conj (f t) ∧
    (simpleHalfLatticeConfig hL).W f f = 2 * L * ∫ t, f t * conj (f t) ∧
    (offLineLatticeConfig hL hδ hδ').W f f = 2 * L * ∫ t, f t * conj (f t) := by
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Icc_subset_Icc (by linarith) haL)
  have hfsL : tsupport f ⊆ Icc (-L) L :=
    hfs'.trans (Icc_subset_Icc (by linarith) (by linarith))
  exact ⟨W_onLineLatticeConfig_of_le_nyquist hL hf hf.continuous hfs' hfs',
    W_simpleHalfLatticeConfig hL hf hf.continuous hfsL hfsL,
    W_offLineLatticeConfig_of_le_nyquist hL hδ hδ' hf hf.continuous hfs' hfs'⟩

/-! ### The two faces -/

/-- **Position face.** The double lattice `{½ + 2πik/L}` and the simple lattice `{½ + πik/L}`
have the same Weil form on every `C²` test supported in `[−a, a]` iff `a ≤ L/2`. -/
theorem onLineLattices_agree_iff_le_nyquist {L : ℝ} (hL : 0 < L) (a : ℝ) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      (onLineLatticeConfig hL).W f f = (simpleHalfLatticeConfig hL).W f f) ↔ a ≤ L / 2 := by
  obtain ⟨hT, hT', hon, hon', hsep, hne, hagree⟩ := lattice_resolution_sharp hL
  constructor
  · intro h
    by_contra hlt
    have hg : 0 < π / L := by positivity
    have ha : π / (2 * (π / L)) < a := by
      have hπ : π ≠ 0 := Real.pi_pos.ne'
      have hL0 : L ≠ 0 := hL.ne'
      have : π / (2 * (π / L)) = L / 2 := by field_simp
      rw [this]
      exact lt_of_not_ge hlt
    exact hne (eq_of_weil_eq_of_separated _ _ hT hT' hon hon' hg hsep ha h).1
  · intro haL f hf hfs
    exact hagree f hf (hfs.trans (Icc_subset_Icc (by linarith) haL))

/-- **Depth face.** The off-line lattice pair `{½ ± δ + 2πik/L}` and the double on-line lattice
have the same Weil form on every `C²` test supported in `[−a, a]` iff `a ≤ L/2`, whatever the
depth `δ ∈ (0, ½]`. -/
theorem offLineLattice_agrees_iff_le_nyquist {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (a : ℝ) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      (offLineLatticeConfig hL hδ hδ').W f f = (onLineLatticeConfig hL).W f f) ↔ a ≤ L / 2 := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨f, hf, hfs, hneg⟩ :=
      exists_re_W_offLineLatticeConfig_neg hL hδ hδ' (lt_of_not_ge hlt)
    have h0 := re_W_onLineLatticeConfig_nonneg hL f
    rw [h f hf hfs] at hneg
    exact absurd h0 (not_le.mpr hneg)
  · intro haL f hf hfs
    have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
      hfs.trans (Icc_subset_Icc (by linarith) haL)
    exact W_offLineLatticeConfig_eq_onLine hL hδ hδ' hf hf.continuous hfs' hfs'

/-! ### Widths of the three configurations -/

theorem configWidth_onLineLatticeConfig {L : ℝ} (hL : 0 < L) :
    configWidth (onLineLatticeConfig hL) = 0 :=
  configWidth_eq_zero_iff_onLine.mpr (lattice_resolution_sharp hL).2.2.1

theorem configWidth_simpleHalfLatticeConfig {L : ℝ} (hL : 0 < L) :
    configWidth (simpleHalfLatticeConfig hL) = 0 :=
  configWidth_eq_zero_iff_onLine.mpr (lattice_resolution_sharp hL).2.2.2.1

/-! ### One law -/

/-- **Position and depth share one Nyquist aperture.** The position face holds at aperture `a`
iff the depth face holds there for every depth, and below the common threshold `L/2` the
position mimic and every depth mimic have the same Weil form on the aperture. -/
theorem position_and_depth_share_nyquist_aperture {L : ℝ} (hL : 0 < L) (a : ℝ) :
    ((∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        (onLineLatticeConfig hL).W f f = (simpleHalfLatticeConfig hL).W f f) ↔
      ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hδ' : δ ≤ 1 / 2, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a →
          (offLineLatticeConfig hL hδ hδ').W f f = (onLineLatticeConfig hL).W f f) ∧
    (a ≤ L / 2 → ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hδ' : δ ≤ 1 / 2, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a →
          (offLineLatticeConfig hL hδ hδ').W f f = (simpleHalfLatticeConfig hL).W f f) := by
  refine ⟨?_, ?_⟩
  · rw [onLineLattices_agree_iff_le_nyquist hL a]
    constructor
    · intro haL δ hδ hδ' f hf hfs
      exact (offLineLattice_agrees_iff_le_nyquist hL hδ hδ' a).mpr haL f hf hfs
    · intro h
      exact (offLineLattice_agrees_iff_le_nyquist hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl a).mp
        (h _ _ _)
  · intro haL δ hδ hδ' f hf hfs
    obtain ⟨-, hS, hP⟩ := weil_eq_flat_of_le_nyquist hL hδ hδ' haL hf hfs
    rw [hS, hP]

/-- **The aperture-`a` fibre through the double lattice**, `a ≤ L/2`: it contains a tempered
on-line configuration with another carrier, and a tempered configuration of every width
`δ ∈ (0, ½]`. -/
theorem nyquist_fibre_through_onLineLattice {L : ℝ} (hL : 0 < L) {a : ℝ} (haL : a ≤ L / 2) :
    (∃ Z : ZeroConfig, TemperedConfig Z ∧ configWidth Z = 0 ∧
      Z.carrier ≠ (onLineLatticeConfig hL).carrier ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a → Z.W f f = (onLineLatticeConfig hL).W f f) ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∃ Z : ZeroConfig, TemperedConfig Z ∧ configWidth Z = δ ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        Z.W f f = (onLineLatticeConfig hL).W f f := by
  refine ⟨⟨simpleHalfLatticeConfig hL, temperedConfig_simpleHalfLatticeConfig hL,
    configWidth_simpleHalfLatticeConfig hL, (lattice_resolution_sharp hL).2.2.2.2.2.1.symm,
    fun f hf hfs => ((onLineLattices_agree_iff_le_nyquist hL a).mpr haL f hf hfs).symm⟩,
    fun δ hδ hδ' => ⟨offLineLatticeConfig hL hδ hδ', temperedConfig_offLineLatticeConfig hL hδ hδ',
      configWidth_offLineLatticeConfig hL hδ hδ',
      fun f hf hfs => (offLineLattice_agrees_iff_le_nyquist hL hδ hδ' a).mpr haL f hf hfs⟩⟩

/-- **Above the Nyquist aperture both mimics are detected.** For `a > L/2` some test of aperture
`a` separates the simple lattice from the double lattice, and for every depth some test of
aperture `a` is negative on the off-line pair and nonnegative on the double lattice. -/
theorem mimics_detected_of_nyquist_lt {L : ℝ} (hL : 0 < L) {a : ℝ} (ha : L / 2 < a) :
    (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (onLineLatticeConfig hL).W f f ≠ (simpleHalfLatticeConfig hL).W f f) ∧
    ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hδ' : δ ≤ 1 / 2, ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧
      tsupport f ⊆ Icc (-a) a ∧ ((offLineLatticeConfig hL hδ hδ').W f f).re < 0 ∧
        0 ≤ ((onLineLatticeConfig hL).W f f).re := by
  refine ⟨?_, fun δ hδ hδ' => ?_⟩
  · by_contra hcon
    have hall : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        (onLineLatticeConfig hL).W f f = (simpleHalfLatticeConfig hL).W f f := by
      intro f hf hfs
      by_contra hne
      exact hcon ⟨f, hf, hfs, hne⟩
    have := (onLineLattices_agree_iff_le_nyquist hL a).mp hall
    linarith
  · obtain ⟨f, hf, hfs, hneg⟩ := exists_re_W_offLineLatticeConfig_neg hL hδ hδ' ha
    exact ⟨f, hf, hfs, hneg, re_W_onLineLatticeConfig_nonneg hL f⟩

end GaloisForLFunctions.SquareRootThreshold
