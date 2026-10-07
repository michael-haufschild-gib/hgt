import GaloisForLFunctions.HTGeometry.LegendreHalvingCriterion
import GaloisForLFunctions.RHTower.XiGlobalKummerTranslatedSection

/-!
# Exact division fields of the actual Xi Legendre sections

Over every field extension of the infinite marked source, the original section
has a half exactly when Xi becomes square. Its translate by the rational two-torsion
section has a half exactly when both Xi and its labelled positive companion become
squares. All source nonvanishing conditions are discharged by existing theorems.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry WeierstrassCurve.Affine
namespace RHTower.XiGlobalKummer
local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective
variable (E : Type*) [Field E] [Algebra Marked E]
local instance : CharZero E := charZero_of_injective_algebraMap (algebraMap Marked E).injective
local instance : DecidableEq E := Classical.decEq E
local notation "φ" => algebraMap Marked E

def sourceCurveOver (n : ℕ) : WeierstrassCurve.Affine E :=
  LegendreDoubling.curve (φ (1 + sourceParameter n))

theorem sourceCurveOver_eq_baseChange (n : ℕ) :
    sourceCurveOver E n = (sourceCurve n).baseChange E := by
  ext <;> simp [sourceCurveOver, sourceCurve, LegendreDoubling.curve,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem sourceSectionOver_nonsingular (n : ℕ) :
    (sourceCurveOver E n).Nonsingular (φ (sourceParameter n)) (φ (sourceY n)) := by
  have h := ((sourceCurve n).map_nonsingular (φ).injective
    (sourceParameter n) (sourceY n)).mpr (sourceSection_nonsingular n)
  simpa [sourceCurveOver, sourceCurve, LegendreDoubling.curve, WeierstrassCurve.map] using h

def sourceSectionOver (n : ℕ) : (sourceCurveOver E n).Point :=
  Point.some (φ (sourceParameter n)) (φ (sourceY n)) (sourceSectionOver_nonsingular E n)

theorem translatedSectionOver_nonsingular (n : ℕ) :
    (sourceCurveOver E n).Nonsingular (φ (translatedX n)) (φ (translatedY n)) := by
  have h := ((sourceCurve n).map_nonsingular (φ).injective
    (translatedX n) (translatedY n)).mpr (translatedSection_nonsingular n)
  simpa [sourceCurveOver, sourceCurve, LegendreDoubling.curve, WeierstrassCurve.map] using h

def translatedSectionOver (n : ℕ) : (sourceCurveOver E n).Point :=
  Point.some (φ (translatedX n)) (φ (translatedY n)) (translatedSectionOver_nonsingular E n)

private theorem lambdaOver_ne_zero (n : ℕ) : φ (1 + sourceParameter n) ≠ 0 :=
  (map_ne_zero φ).mpr (sourceLambda_ne_zero n)

private theorem lambdaOver_ne_one (n : ℕ) : φ (1 + sourceParameter n) ≠ 1 := by
  intro he
  have h : 1 + sourceParameter n = 1 := (φ).injective (by simpa using he)
  apply sourceParameter_ne_zero n
  linear_combination h

omit [Algebra Marked E] in
private theorem square_mul_square_iff {a b : E} (ha : a ≠ 0) :
    IsSquare (a ^ 2 * b) ↔ IsSquare b := by
  constructor
  · intro hs
    have h := hs.div (IsSquare.sq a)
    rw [mul_div_cancel_left₀ b (pow_ne_zero 2 ha)] at h
    exact h
  · exact fun hb => (IsSquare.sq a).mul hb

theorem sourceParameter_map_isSquare_iff (n : ℕ) :
    IsSquare (φ (sourceParameter n)) ↔ IsSquare (φ xiMarked) := by
  rw [sourceParameter, map_mul, map_pow]
  exact square_mul_square_iff E ((map_ne_zero φ).mpr (betaMarked_ne_zero n))

/-- Over every extension, the original section has a half exactly when the common Xi class dies. -/
theorem sourceSectionOver_has_half_iff (n : ℕ) :
    (∃ R : (sourceCurveOver E n).Point, R + R = sourceSectionOver E n) ↔
      IsSquare (φ xiMarked) := by
  unfold sourceSectionOver sourceCurveOver
  rw [LegendreDoubling.exists_half_iff_square_coordinates
    (lambdaOver_ne_zero E n) (lambdaOver_ne_one E n)
    ((map_ne_zero φ).mpr (sourceY_ne_zero n)) (sourceSectionOver_nonsingular E n)]
  constructor
  · exact fun h => (sourceParameter_map_isSquare_iff E n).mp h.1
  · intro hxi
    have hd := (sourceParameter_map_isSquare_iff E n).mpr hxi
    refine ⟨hd, ?_⟩
    have hs := (IsSquare.sq (φ markedI)).mul ((IsSquare.sq (φ (sourceY n))).div hd)
    have he : (φ markedI) ^ 2 * ((φ (sourceY n)) ^ 2 / φ (sourceParameter n)) =
        φ (sourceParameter n) - 1 := by
      rw [← map_pow, markedI_sq, map_neg, map_one,
        ← map_pow, sourceY_sq, map_mul,
        mul_div_cancel_left₀ (φ (factorMarked n)) ((map_ne_zero φ).mpr (sourceParameter_ne_zero n))]
      have hf := congrArg φ (sourceParameter_add_factor n)
      simp only [map_add, map_one] at hf
      linear_combination -hf
    rw [he] at hs
    exact hs

/-- Over every extension, the translated section needs exactly the common and its labelled class. -/
theorem translatedSectionOver_has_half_iff (n : ℕ) :
    (∃ R : (sourceCurveOver E n).Point, R + R = translatedSectionOver E n) ↔
      IsSquare (φ xiMarked) ∧ IsSquare (φ (1 + sourceParameter n)) := by
  unfold translatedSectionOver sourceCurveOver
  rw [LegendreDoubling.exists_half_iff_square_coordinates
    (lambdaOver_ne_zero E n) (lambdaOver_ne_one E n)
    ((map_ne_zero φ).mpr (translatedY_ne_zero n)) (translatedSectionOver_nonsingular E n)]
  have hd0 : φ (sourceParameter n) ≠ 0 := (map_ne_zero φ).mpr (sourceParameter_ne_zero n)
  have hx : φ (translatedX n) = φ (1 + sourceParameter n) / φ (sourceParameter n) := by
    simp only [translatedX, map_div₀]
  have hx1 : φ (translatedX n) - 1 = (φ (sourceParameter n))⁻¹ := by
    rw [hx, map_add, map_one]
    field_simp
    ring
  rw [hx1]
  constructor
  · rintro ⟨hq, hdInv⟩
    have hd : IsSquare (φ (sourceParameter n)) := isSquare_inv.mp hdInv
    refine ⟨(sourceParameter_map_isSquare_iff E n).mp hd, ?_⟩
    have h := hq.mul hd
    rw [hx, div_mul_cancel₀ _ hd0] at h
    exact h
  · rintro ⟨hxi, hl⟩
    have hd := (sourceParameter_map_isSquare_iff E n).mpr hxi
    refine ⟨?_, hd.inv⟩
    rw [hx]
    exact hl.div hd

end RHTower.XiGlobalKummer
