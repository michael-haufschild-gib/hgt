import GaloisForLFunctions.ZeroConfigurationGeometry.RamanujanIsRealityOfAnEulerColumn
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold

/-!
# Euler columns are seen just above their prime

`RamanujanIsRealityOfAnEulerColumn` shows that the zeros of an Euler factor at `p` off the line
form the off-line lattice `{½ ± δ + 2πik/log p}`, which has the image of the doubled on-line
lattice at every aperture `≤ log p / 2`. Here the threshold is shown to be sharp, without a sign.

* **Separation above the Nyquist aperture** (`offLineLattice_separated_above_nyquist`). For every
  aperture `a > L/2` the two-bump window at lag `L` gives the off-line lattice the image
  `4L‖κ‖²(1 − cosh δL) ≠ 0` and the on-line lattice the image `0`.
* **The mimicry threshold of a lattice** (`offLineLattice_mimic_iff`). The off-line lattice of
  depth `δ > 0` and the doubled on-line lattice are mimics at aperture `a` exactly when
  `a ≤ L/2`.
* **Selectivity against Euler columns** (`eulerColumn_mimic_iff`). An Euler column at `p` is a mimic
  of an on-line lattice at aperture `a` exactly when `a ≤ log p / 2`. The camera family of all
  apertures separates every Euler column, and the separating aperture is exactly `log p / 2⁺`.
  Bounded apertures cannot exclude all twins; unbounded apertures exclude each one.
-/

open MeasureTheory Complex Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 _root_.RHTower SquareRootThreshold SelbergClass.PositiveFiniteEuler

/-- The lag formula of the doubled on-line lattice for every compactly supported window. -/
theorem W_onLineLatticeConfig_lagFormula {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (onLineLatticeConfig hL).W f f =
      ((L : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * L) * ((2 : ℝ) : ℂ) := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hs : tsupport f ⊆ Icc (-((2 * R) / 2)) ((2 * R) / 2) := fun u hu => by
    have := hR hu
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    rw [show 2 * R / 2 = R by ring]
    exact abs_le.mp this
  rw [W_onLineLatticeConfig hL hf hf.continuous hs hs, tsum_mul_right]
  push_cast; ring

/-- **Separation above the Nyquist aperture.** -/
theorem offLineLattice_separated_above_nyquist {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : L / 2 < a) :
    ∃ f, ApertureWindow a f ∧
      (offLineLatticeConfig hL hδ hδ').W f f ≠ (onLineLatticeConfig hL).W f f := by
  set w := min (a - L / 2) (L / 8) with hw
  have hw0 : 0 < w := lt_min (by linarith) (by positivity)
  have hwL : 4 * w < L := by have := min_le_right (a - L / 2) (L / 8); linarith
  have hwa : ((1 : ℕ) : ℝ) * L / 2 + w ≤ a := by
    have := min_le_left (a - L / 2) (L / 8); push_cast; linarith
  refine ⟨twoBump (modScaledBump w 0) ((1 : ℕ) * L) (-1),
    ⟨contDiff_bumpTest (contDiff_modScaledBump_two w 0) _ _,
      (tsupport_twoBump_modScaledBump_subset hw0 (by positivity)).trans
        (Icc_subset_Icc (by linarith) hwa)⟩, ?_⟩
  rw [W_offLineLattice_lag_nat_mul hL hδ hδ' hw0 hwL le_rfl,
    W_lag_nat_mul_of_lagFormula (onLineLatticeConfig hL) (fun _ => ((2 : ℝ) : ℂ))
      (W_onLineLatticeConfig_lagFormula hL) hw0 hwL le_rfl]
  have hκ := integral_norm_sq_modScaledBump_pos hw0
  have hc : 1 < Real.cosh (((1 : ℕ) : ℝ) * δ * L) :=
    Real.one_lt_cosh.mpr (by push_cast; positivity)
  intro h
  have h' : ((4 * L * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * (1 - Real.cosh (((1 : ℕ) : ℝ) * δ * L)) :
      ℝ) : ℂ) = 0 := by rw [h]; push_cast; ring
  have h'' := Complex.ofReal_eq_zero.mp h'
  have hneg : 4 * L * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) *
      (1 - Real.cosh (((1 : ℕ) : ℝ) * δ * L)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

/-- **The mimicry threshold of a lattice is its Nyquist aperture.** -/
theorem offLineLattice_mimic_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (a : ℝ) :
    (∀ f, ApertureWindow a f →
      (offLineLatticeConfig hL hδ hδ').W f f = (onLineLatticeConfig hL).W f f) ↔ a ≤ L / 2 := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨f, hf, hne⟩ := offLineLattice_separated_above_nyquist hL hδ hδ' (not_le.mp hlt)
    exact hne (h f hf)
  · intro ha f hf
    exact W_offLineLatticeConfig_eq_onLine hL hδ hδ' hf.1 hf.1.continuous
      (hf.2.trans (Icc_subset_Icc (by linarith) ha)) (hf.2.trans (Icc_subset_Icc (by linarith) ha))

/-- **Selectivity against Euler columns.** The zeros of the Euler factor at `p` with coefficient
`A_δ` (`0 < δ ≤ ½`) mimic an on-line lattice at aperture `a` exactly when `a ≤ log p / 2`. -/
theorem eulerColumn_mimic_iff {p : ℕ} (hp : 1 < p) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (a : ℝ) :
    let hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
    (offLineLatticeConfig hL hδ hδ').carrier = {s | localFactor p (eulerColumnCoeff p δ) s = 0} ∧
      ((∀ f, ApertureWindow a f →
        (offLineLatticeConfig hL hδ hδ').W f f = (onLineLatticeConfig hL).W f f) ↔
          a ≤ Real.log p / 2) := by
  intro hL
  exact ⟨(eulerColumn_mimics_onLineLattice hp hδ hδ').1, offLineLattice_mimic_iff hL hδ hδ' a⟩

end GaloisForLFunctions.ZeroConfigurationGeometry
