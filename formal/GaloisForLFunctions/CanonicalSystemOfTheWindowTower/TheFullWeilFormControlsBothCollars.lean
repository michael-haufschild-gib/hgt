import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilFormRetainsLogarithmicCollarEnergy
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilFormHasBoundedExteriorCrossings
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.SharpRestrictionPreservesTheCompleteComplexWeilDomain

/-!
# Full Weil coercivity on two closing collars

Each collar pays logarithmic energy. The full Gamma, prime and polar
crossings have bounded physical L² norm. Completing the square against
the old positive ground energy leaves the same leading logarithmic floor
on the two collar masses.
-/

open Complex MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- The full boundary crossing bound, including all prime and polar terms. -/
def weilExteriorCrossingBound (b : SuzukiPositiveAperture) : ℝ :=
  2*Real.pi+‖ccmRestrictedWeilBoundedRemainder b‖

/-- The fixed error after eliminating the old positive space and coupling the two collars. -/
def weilTwoCollarEnergyError (a b : PrecontactAperture) : ℝ :=
  ‖weilLogarithmicCorrection b.1‖ + weilExteriorCrossingBound b.1 +
    2*(weilExteriorCrossingBound b.1)^2/ccmRestrictedWeilGroundEnergy a.1

private theorem three_component_square_bound {lam C D L x y z : ℝ}
    (hLam : 0 < lam) (hC : 0 ≤ C) :
    (L-D-C-2*C^2/lam)*(y^2+z^2) ≤
      lam*x^2+(L-D)*(y^2+z^2)-2*C*x*(y+z)-2*C*y*z := by
  have hn : 0 ≤ ((lam*x-C*(y+z))^2+(lam*C+C^2)*(y-z)^2)/lam :=
    div_nonneg (add_nonneg (sq_nonneg _)
      (mul_nonneg (add_nonneg (mul_nonneg hLam.le hC) (sq_nonneg _)) (sq_nonneg _))) hLam.le
  have he : ((lam*x-C*(y+z))^2+(lam*C+C^2)*(y-z)^2)/lam =
      (lam*x^2+(L-D)*(y^2+z^2)-2*C*x*(y+z)-2*C*y*z) -
        (L-D-C-2*C^2/lam)*(y^2+z^2) := by
    field_simp [hLam.ne']
    ring
  rw [he] at hn
  exact sub_nonneg.mp hn

namespace WeilHilbertBeforeContact

/-- The old positive form absorbs both full collar crossings with a fixed energy error. -/
theorem twoCollar_energy_floor {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (p : WeilHilbertBeforeContact a) (l r : WeilHilbertBeforeContact b)
    (hl : ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (-a.1.1) →
      ccmArchimedeanFormEmbedding b.1 (toForm b l) x = 0)
    (hr : ∀ᵐ x ∂volume, x ∉ Icc a.1.1 (a.1.1+h) →
      ccmArchimedeanFormEmbedding b.1 (toForm b r) x = 0) :
    (Real.log (1/h)-weilTwoCollarEnergyError a b) *
      (‖ccmArchimedeanFormToAperture b.1 (toForm b l)‖^2 +
        ‖ccmArchimedeanFormToAperture b.1 (toForm b r)‖^2) ≤
      ‖r+l+inclusion hab p‖^2 := by
  let x := ‖ccmArchimedeanFormToAperture a.1 (toForm a p)‖
  let y := ‖ccmArchimedeanFormToAperture b.1 (toForm b l)‖
  let z := ‖ccmArchimedeanFormToAperture b.1 (toForm b r)‖
  let C := weilExteriorCrossingBound b.1
  let D := ‖weilLogarithmicCorrection b.1‖
  let L := Real.log (1/h)
  let lam := ccmRestrictedWeilGroundEnergy a.1
  have hLam : 0 < lam := precontact_groundEnergy_pos a
  have hC : 0 ≤ C := by dsimp only [C, weilExteriorCrossingBound]; positivity
  have hpE : lam*x^2 ≤ ‖p‖^2 := groundEnergy_mul_mass_le a p
  have hlE : (L-D)*y^2 ≤ ‖l‖^2 := by
    rw [norm_sq_eq_weil]
    apply ccmWeilForm_ge_log_inverse_width b.1 (lo := -a.1.1-h) hh hh1 (toForm b l)
    simpa only [sub_add_cancel] using hl
  have hrE : (L-D)*z^2 ≤ ‖r‖^2 := by
    rw [norm_sq_eq_weil]
    exact ccmWeilForm_ge_log_inverse_width b.1 (lo := a.1.1) hh hh1 (toForm b r) hr
  have hlout : ∀ᵐ x ∂volume, -a.1.1 < x →
      ccmArchimedeanFormEmbedding b.1 (toForm b l) x = 0 := by
    filter_upwards [hl] with x hx hout
    apply hx
    intro hin
    exact (not_le.mpr hout) hin.2
  have hrout : ∀ᵐ x ∂volume, x < a.1.1 →
      ccmArchimedeanFormEmbedding b.1 (toForm b r) x = 0 := by
    filter_upwards [hr] with x hx hout
    apply hx
    intro hin
    exact (not_le.mpr hout) hin.1
  have hlhalf : ∀ᵐ x ∂volume, 0 < x →
      ccmArchimedeanFormEmbedding b.1 (toForm b l) x = 0 := by
    filter_upwards [hlout] with x hx hp
    exact hx (by linarith only [a.1.property, hp])
  have hrhalf : ∀ᵐ x ∂volume, x < 0 →
      ccmArchimedeanFormEmbedding b.1 (toForm b r) x = 0 := by
    filter_upwards [hrout] with x hx hn
    exact hx (hn.trans a.1.property)
  have hlp : ‖inner ℂ l (inclusion hab p)‖ ≤ C*y*x := by
    rw [inner_eq_weil, toForm_inclusion]
    exact norm_ccmWeilForm_leftExterior_of_supported hab (toForm b l) (toForm a p) hlout
  have hrp : ‖inner ℂ r (inclusion hab p)‖ ≤ C*z*x := by
    rw [inner_eq_weil, toForm_inclusion]
    exact norm_ccmWeilForm_rightExterior_of_supported hab (toForm b r) (toForm a p) hrout
  have hrl : ‖inner ℂ r l‖ ≤ C*z*y := by
    rw [inner_eq_weil]
    exact norm_ccmWeilForm_oppositeHalfLines_of_supported b.1 (toForm b r) (toForm b l) hrhalf hlhalf
  have hlpR := (abs_le.mp ((Complex.abs_re_le_norm (inner ℂ l (inclusion hab p))).trans hlp)).1
  have hrpR := (abs_le.mp ((Complex.abs_re_le_norm (inner ℂ r (inclusion hab p))).trans hrp)).1
  have hrlR := (abs_le.mp ((Complex.abs_re_le_norm (inner ℂ r l)).trans hrl)).1
  have hsum : lam*x^2+(L-D)*(y^2+z^2)-2*C*x*(y+z)-2*C*y*z ≤
      ‖r+l+inclusion hab p‖^2 := by
    rw [norm_add_sq (𝕜 := ℂ) (E := WeilHilbertBeforeContact b),
      norm_add_sq (𝕜 := ℂ) (E := WeilHilbertBeforeContact b),
      inner_add_left (E := WeilHilbertBeforeContact b), (inclusion hab).norm_map]
    simp only [RCLike.re_to_complex, Complex.add_re]
    nlinarith only [hpE, hlE, hrE, hlpR, hrpR, hrlR]
  have hs := (three_component_square_bound (D := D) (L := L) (x := x) (y := y) (z := z) hLam hC).trans hsum
  have hcoef : Real.log (1/h)-weilTwoCollarEnergyError a b = L-D-C-2*C^2/lam := by
    dsimp only [L, D, C, lam, weilTwoCollarEnergyError]
    ring
  rw [hcoef]
  exact hs

/-- Every source in a growing window admits the exact two-collar decomposition and its full energy floor. -/
theorem exists_twoCollar_decomposition_with_floor {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (u : WeilHilbertBeforeContact b)
    (hu : ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (a.1.1+h) →
      ccmArchimedeanFormEmbedding b.1 (toForm b u) x = 0) :
    ∃ p : WeilHilbertBeforeContact a, ∃ l r : WeilHilbertBeforeContact b,
      u = r+l+inclusion hab p ∧
      (∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (-a.1.1) →
        ccmArchimedeanFormEmbedding b.1 (toForm b l) x = 0) ∧
      (∀ᵐ x ∂volume, x ∉ Icc a.1.1 (a.1.1+h) →
        ccmArchimedeanFormEmbedding b.1 (toForm b r) x = 0) ∧
      (Real.log (1/h)-weilTwoCollarEnergyError a b) *
        (‖ccmArchimedeanFormToAperture b.1 (toForm b l)‖^2 +
          ‖ccmArchimedeanFormToAperture b.1 (toForm b r)‖^2) ≤ ‖u‖^2 := by
  obtain ⟨p, l, r, he, -, hl, hr⟩ := exists_ccm_interval_decomposition a.1 b.1 hab (toForm b u)
  let P := (toForm a).symm p
  let L := (toForm b).symm l
  let R := (toForm b).symm r
  have he' : u = R+L+inclusion hab P := by
    apply (toForm b).injective
    rw [map_add, map_add, toForm_inclusion]
    simpa only [P, L, R, LinearEquiv.apply_symm_apply] using he
  have hl' : ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (-a.1.1) →
      ccmArchimedeanFormEmbedding b.1 (toForm b L) x = 0 := by
    change ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (-a.1.1) →
      ccmArchimedeanFormEmbedding b.1 (toForm b ((toForm b).symm l)) x = 0
    rw [LinearEquiv.apply_symm_apply, hl]
    filter_upwards [hu, indicatorCutoff_ae (Ico (-b.1.1) (-a.1.1)) measurableSet_Ico
      (ccmArchimedeanFormEmbedding b.1 (toForm b u))] with x hu hc hx
    rw [hc]
    by_cases hm : x ∈ Ico (-b.1.1) (-a.1.1)
    · rw [indicator_of_mem hm]
      apply hu
      intro hi
      exact hx ⟨hi.1, hm.2.le⟩
    · rw [indicator_of_notMem hm]
  have hr' : ∀ᵐ x ∂volume, x ∉ Icc a.1.1 (a.1.1+h) →
      ccmArchimedeanFormEmbedding b.1 (toForm b R) x = 0 := by
    change ∀ᵐ x ∂volume, x ∉ Icc a.1.1 (a.1.1+h) →
      ccmArchimedeanFormEmbedding b.1 (toForm b ((toForm b).symm r)) x = 0
    rw [LinearEquiv.apply_symm_apply, hr]
    filter_upwards [hu, indicatorCutoff_ae (Ico a.1.1 b.1.1) measurableSet_Ico
      (ccmArchimedeanFormEmbedding b.1 (toForm b u))] with x hu hc hx
    rw [hc]
    by_cases hm : x ∈ Ico a.1.1 b.1.1
    · rw [indicator_of_mem hm]
      apply hu
      intro hi
      exact hx ⟨hm.1, hi.2⟩
    · rw [indicator_of_notMem hm]
  refine ⟨P, L, R, he', hl', hr', ?_⟩
  rw [he']
  exact twoCollar_energy_floor hab hh hh1 P L R hl' hr'

#print axioms exists_twoCollar_decomposition_with_floor
#print axioms twoCollar_energy_floor
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
