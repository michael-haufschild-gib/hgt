import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHeightApertureSeamIsEmpty

/-!
# Coercivity at a bounded aperture is still blind

A real method rarely produces bare nonnegativity. It produces a *coercive* certificate: a
constant `η > 0` with `Re W_Z(f, f) ≥ η ‖f‖²` for every test of aperture `a`. The natural hope is
that a positive constant is qualitatively better than nonnegativity — that a spectral gap at a
finite aperture could be bootstrapped towards the critical line.

It cannot. The graded reading `apertureGain a η` has the trivial resolution limit `½` for the width
at **every** level `η`, however large (`resolutionLimit_width_apertureGain`).

The mechanism is that the two parameters of the witness are independent. The doubled on-line
lattice of spacing `2π/L` with one inserted off-line pair of depth `½` has
`Re W(f, f) ≥ 2(L − S_δ(a)) ‖f‖²` below its Nyquist aperture
(`SquareRootThreshold.re_W_isolatedPairConfig_ge`): the background spacing supplies the coercivity
constant and the inserted pair supplies the width, and neither constrains the other. Taking the
background dense enough makes the gap exceed any prescribed `η` while the width stays `½`
(`exists_width_eq_half_apertureGain`).

* `certifies_width_apertureGain_iff` — a coercive certificate at aperture `a` and level `η`
  certifies the bound `β` on the width exactly when `β ≥ ½`, for every `η`.
* `gainLadderIsTrivial` — the levels form a chain of strictly stronger certificates
  (`apertureGain_mono_level`), and every stage of it has limit `½`.
* `not_resolves_onLine_apertureGain` — no coercive finite-aperture certificate decides the
  critical line.

Together with the aperture ladder this says the width is insensitive to *both* refinements of a
finite-aperture certificate: enlarging the aperture (while keeping it bounded) and strengthening
the constant. The only parameter that moves the width is the unbounded aperture itself.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The graded aperture reading -/

/-- The aperture-`a` certificate at level `η`: the Weil form of `Z` dominates `η ‖f‖²` on every
`C²` test supported in `[−a, a]`. At `η = 0` this is bare positivity; at `η > 0` it is a coercive
certificate with gap `η`. -/
def apertureGain (a η : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    η * ∫ t, ‖f t‖ ^ 2 ≤ (Z.1.W f f).re

theorem apertureGain_zero_iff {a : ℝ} {Z : TemperedZeroConfig} :
    apertureGain a 0 Z ↔ aperturePositivity a Z := by
  simp only [apertureGain, aperturePositivity, zero_mul]

/-- A larger gap is a stronger certificate. -/
theorem apertureGain_mono_level {a η η' : ℝ} (h : η' ≤ η) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) : apertureGain a η' Z := fun f hf hfs =>
  le_trans (mul_le_mul_of_nonneg_right h (MeasureTheory.integral_nonneg fun _ => by positivity)) (hZ f hf hfs)

/-- A certificate at a larger aperture contains the certificate at a smaller one. -/
theorem apertureGain_mono_aperture {a b η : ℝ} (hab : a ≤ b) {Z : TemperedZeroConfig}
    (hZ : apertureGain b η Z) : apertureGain a η Z := fun f hf hfs =>
  hZ f hf (hfs.trans (Icc_subset_Icc (by linarith) hab))

/-! ### 2. The gap and the width are independent parameters -/

/-- **Any prescribed gap at a bounded aperture coexists with the maximal width.** The background
lattice spacing fixes the gap and the inserted pair fixes the width. -/
theorem exists_width_eq_half_apertureGain {a : ℝ} (ha : 0 < a) (η : ℝ) :
    ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain a η Z := by
  set L : ℝ := 2 * a + |pairEnergy (1 / 2) a| + |η| + 1 with hLdef
  have hL : 0 < L := by
    have := abs_nonneg (pairEnergy (1 / 2) a)
    have := abs_nonneg η
    simp only [hLdef]; linarith
  have haL : a ≤ L / 2 := by
    have := abs_nonneg (pairEnergy (1 / 2) a)
    have := abs_nonneg η
    simp only [hLdef]; linarith
  have hgap : η ≤ 2 * (L - pairEnergy (1 / 2) a) := by
    have h1 : pairEnergy (1 / 2) a ≤ |pairEnergy (1 / 2) a| := le_abs_self _
    have h2 : η ≤ |η| := le_abs_self _
    have h3 : (0 : ℝ) ≤ |η| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |pairEnergy (1 / 2) a| := abs_nonneg _
    simp only [hLdef]; linarith
  refine ⟨latticeWithPairAt hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl 0,
    le_antisymm (width_le_half _)
      (depth_le_width_latticeWithPairAt hL (by norm_num) le_rfl 0), fun f hf hfs => ?_⟩
  have hbase := re_W_isolatedPairConfig_ge hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl 0
    ha.le haL hf hfs
  have hint : (0 : ℝ) ≤ ∫ t, ‖f t‖ ^ 2 := MeasureTheory.integral_nonneg fun _ => by positivity
  exact le_trans (mul_le_mul_of_nonneg_right hgap hint) hbase

/-! ### 3. Every level has the trivial limit -/

/-- **The resolution limit of the width is `½` at every aperture and every gap.** A coercivity
constant, however large, certifies nothing about the width. -/
theorem resolutionLimit_width_apertureGain {a η : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) : resolutionLimit width (apertureGain a η) Z = 1 / 2 := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_apertureGain ha η
  refine le_antisymm (csSup_le (shadow_image_nonempty width (apertureGain a η) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · have hmem : Z' ∈ shadow (apertureGain a η) Z := propext (iff_of_true hpos' hZ)
    exact hw' ▸ le_csSup (bddAbove_width_image _) ⟨Z', hmem, rfl⟩

/-- A coercive finite-aperture certificate certifies the bound `β` on the width exactly when
`β ≥ ½`, at every level. -/
theorem certifies_width_apertureGain_iff {a η : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) {β : ℝ} :
    Certifies width (apertureGain a η) Z β ↔ 1 / 2 ≤ β := by
  rw [certifies_iff_resolutionLimit_le (bddAbove_width_image _),
    resolutionLimit_width_apertureGain ha hZ]

/-- **No coercive finite-aperture certificate decides the critical line.** -/
theorem not_resolves_onLine_apertureGain {a η : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) (hw : width Z = 0) :
    ¬ Resolves (apertureGain a η) (fun W => width W = 0) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_apertureGain ha η
  intro hres
  have h0 : width Z' = 0 := (hres Z Z' (propext (iff_of_true hpos' hZ))).mpr hw
  rw [hw'] at h0
  norm_num at h0

/-- **The gap ladder.** At a fixed bounded aperture the certificates are ordered by their gap, and
every stage of that chain has resolution limit `½` for the width: strengthening the constant gains
information, and none of it is the width. -/
theorem gainLadderIsTrivial {a : ℝ} (ha : 0 < a) :
    ∀ η : ℝ, ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain a η Z ∧
      resolutionLimit width (apertureGain a η) Z = 1 / 2 := fun η => by
  obtain ⟨Z, hw, hZ⟩ := exists_width_eq_half_apertureGain ha η
  exact ⟨Z, hw, hZ, resolutionLimit_width_apertureGain ha hZ⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
