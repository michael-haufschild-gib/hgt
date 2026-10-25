import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ExactArithmeticSourceEffectivity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceConePrimitiveFaithfulness
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceRiemannRochWithoutSymmetry

/-!
# Arithmetic majorants supply Bézout on the original surface

The explicit Chebyshev lower floor yields a quadratic reserve dominating both signs of
the actual defect. A discriminant argument gives its mixed bound, hence Bézout and
ampleness at every positive aperture. Its strictly positive extra mass prevents RR.
The intersection pairing remains the original scaling pairing.
-/

open MeasureTheory
noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace PolarSurface
variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- Absolute diagonal domination by a quadratic form controls the mixed defect. -/
theorem defect_sq_le_of_quadratic_majorant
    (Q : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y = Q y x)
    (hup : ∀ x, S.defect x x ≤ Q x x)
    (hlo : ∀ x, -S.defect x x ≤ Q x x) (x y : C) :
    S.defect x y ^ 2 ≤ Q x x * Q y y := by
  have hp (t : ℝ) :
      0 ≤ Q y y * (t * t) + (-2 * S.defect x y) * t + Q x x := by
    have h1 := hup (x + t • y)
    have h2 := hlo (x - t • y)
    simp only [defect, polar, map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, S.pair_comm y x,
      hQ y x] at h1 h2 ⊢
    nlinarith only [h1, h2]
  have hd := discrim_le_zero hp
  rw [discrim] at hd
  nlinarith only [hd]

/-- The defect as a real bilinear map. -/
def defectLinearMap : C →ₗ[ℝ] C →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ S.defect S.defect_add_left S.defect_smul_left
    (fun x y z => by
      rw [S.defect_comm, S.defect_add_left, S.defect_comm y x, S.defect_comm z x])
    (fun a x y => by rw [S.defect_comm, S.defect_smul_left, S.defect_comm y x, smul_eq_mul])

end PolarSurface

/-- An arithmetic reserve that pays both signs of the defect at every aperture. -/
def arithmeticMajorantSourceEnergy (r : ℝ) (x : ℝ × ℝ × realTestsAt r) : ℝ :=
  criticalDeficitSourceEnergy r (realTestsAt r) x +
    l2SourceEnergy (2 * (10 + 72 * Real.exp r)) (realTestsAt r) x

/-- The original-surface source cone defined by the arithmetic majorant. -/
def arithmeticMajorantSourceCone (r : ℝ) : Set (ℝ × ℝ × realTestsAt r) :=
  (scalingSubsurface (realTestsAt r)).sourceCone (arithmeticMajorantSourceEnergy r)

private theorem majorant_eq {r : ℝ} (hr : 0 < r) (x : ℝ × ℝ × realTestsAt r) :
    arithmeticMajorantSourceEnergy r x = (scalingSubsurface (realTestsAt r)).defect x x +
      2 * (10 + 72 * Real.exp r) * ∫ u : ℝ, x.2.2.1.1 u ^ 2 := by
  rw [arithmeticMajorantSourceEnergy, criticalDeficitSourceEnergy_eq_defect hr.le le_rfl]
  rfl

/-- The majorant retains a strictly positive mass floor. -/
theorem arithmeticMajorantSourceEnergy_mass_floor {r : ℝ} (hr : 0 < r)
    (x : ℝ × ℝ × realTestsAt r) :
    (10 + 72 * Real.exp r) * (∫ u : ℝ, x.2.2.1.1 u ^ 2) ≤
      arithmeticMajorantSourceEnergy r x := by
  rw [majorant_eq hr]
  have hf := realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp hr x
  linarith only [hf]

theorem arithmeticMajorantSourceEnergy_nonneg {r : ℝ} (hr : 0 < r)
    (x : ℝ × ℝ × realTestsAt r) : 0 ≤ arithmeticMajorantSourceEnergy r x := by
  apply le_trans _ (arithmeticMajorantSourceEnergy_mass_floor hr x)
  exact mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _)

private theorem majorant_neg {r : ℝ} (hr : 0 < r) (x : ℝ × ℝ × realTestsAt r) :
    arithmeticMajorantSourceEnergy r (-x) = arithmeticMajorantSourceEnergy r x := by
  simp only [arithmeticMajorantSourceEnergy,
    criticalDeficitSourceEnergy_eq_defect hr.le le_rfl,
    PolarSurface.defect_neg_self, l2SourceEnergy_neg]

private theorem majorant_fibre (r : ℝ) (x : ℝ × ℝ × realTestsAt r) (a b : ℝ) :
    arithmeticMajorantSourceEnergy r
      (x + a • (scalingSubsurface (realTestsAt r)).H + b • (scalingSubsurface (realTestsAt r)).V) =
      arithmeticMajorantSourceEnergy r x := by
  have hs : (x + a • (scalingSubsurface (realTestsAt r)).H +
      b • (scalingSubsurface (realTestsAt r)).V).2.2 = x.2.2 := by
    change x.2.2 + a • (0 : realTestsAt r) + b • 0 = x.2.2
    simp only [smul_zero, add_zero]
  simp only [arithmeticMajorantSourceEnergy, criticalDeficitSourceEnergy, l2SourceEnergy, hs]

/-- Arithmetic mass compensation controls every mixed source pairing. -/
theorem defect_sq_le_arithmeticMajorantSourceEnergy {r : ℝ} (hr : 0 < r)
    (x y : ℝ × ℝ × realTestsAt r) :
    (scalingSubsurface (realTestsAt r)).defect x y ^ 2 ≤
      arithmeticMajorantSourceEnergy r x * arithmeticMajorantSourceEnergy r y := by
  let S := scalingSubsurface (realTestsAt r)
  let Q := S.defectLinearMap + l2ReserveBilinear (2 * (10 + 72 * Real.exp r)) (realTestsAt r)
  have hQ (u v : ℝ × ℝ × realTestsAt r) : Q u v = Q v u := by
    change S.defect u v + l2ReserveBilinear _ _ u v =
      S.defect v u + l2ReserveBilinear _ _ v u
    rw [S.defect_comm, l2ReserveBilinear_symm]
  have he (u : ℝ × ℝ × realTestsAt r) : Q u u = arithmeticMajorantSourceEnergy r u := by
    change S.defect u u + l2ReserveBilinear _ _ u u = _
    rw [l2ReserveBilinear_self, majorant_eq hr]
    rfl
  rw [← he x, ← he y]
  apply S.defect_sq_le_of_quadratic_majorant Q hQ
  · intro u
    rw [he, majorant_eq hr]
    have hm : 0 ≤ ∫ t : ℝ, u.2.2.1.1 t ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hc : 0 ≤ 2 * (10 + 72 * Real.exp r) := by positivity
    linarith only [mul_nonneg hc hm]
  · intro u
    rw [he, majorant_eq hr]
    have hf := realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp hr u
    linarith only [hf]

/-- The arithmetic majorant gives Bézout on the original pairing, at every positive aperture. -/
theorem arithmeticMajorantSourceCone_bezout {r : ℝ} (hr : 0 < r) :
    (scalingSubsurface (realTestsAt r)).BezoutAxiom (arithmeticMajorantSourceCone r) :=
  ((scalingSubsurface (realTestsAt r)).sourceCone_bezout_iff_defect_sq_le
    (arithmeticMajorantSourceEnergy_nonneg hr) (majorant_neg hr) (majorant_fibre r)).mpr
    (defect_sq_le_arithmeticMajorantSourceEnergy hr)

/-- Zero majorant reserve lies in the entire mixed radical, proving ampleness. -/
theorem arithmeticMajorantSourceCone_ample {r : ℝ} (hr : 0 < r) :
    (scalingSubsurface (realTestsAt r)).AmpleAxiom (arithmeticMajorantSourceCone r) := by
  apply ((scalingSubsurface (realTestsAt r)).sourceCone_ample_iff_defect_radical
    (majorant_fibre r)).mpr
  intro x hx y
  have hz := le_antisymm hx (arithmeticMajorantSourceEnergy_nonneg hr x)
  have hb := defect_sq_le_arithmeticMajorantSourceEnergy hr x y
  rw [hz, zero_mul] at hb
  nlinarith only [hb, sq_nonneg ((scalingSubsurface (realTestsAt r)).defect x y)]

/-- An effective class orthogonal to the ample class vanishes, not merely numerically. -/
theorem arithmeticMajorantSourceCone_ample_zero {r : ℝ} (hr : 0 < r)
    (x : ℝ × ℝ × realTestsAt r) (hx : x ∈ arithmeticMajorantSourceCone r)
    (hA : (scalingSubsurface (realTestsAt r)).pair x
      (scalingSubsurface (realTestsAt r)).ample = 0) : x = 0 := by
  have hc : 0 < 10 + 72 * Real.exp r := by positivity
  have hx' : x ∈ l2SourceCone (10 + 72 * Real.exp r) (realTestsAt r) := by
    rw [l2SourceCone, PolarSurface.mem_sourceCone_iff]
    change x ∈ (scalingSubsurface (realTestsAt r)).sourceCone (arithmeticMajorantSourceEnergy r) at hx
    rw [PolarSurface.mem_sourceCone_iff] at hx
    exact ⟨hx.1, hx.2.1, (arithmeticMajorantSourceEnergy_mass_floor hr x).trans hx.2.2⟩
  exact eq_zero_of_mem_l2SourceCone_of_pair_ample_eq_zero hc (realTestsAt r) hx' hA

/-- The strictly positive extra reserve is the exact obstruction to Riemann–Roch. -/
theorem arithmeticMajorantSourceCone_not_riemannRoch {r : ℝ} (hr : 0 < r) :
    ¬ (scalingSubsurface (realTestsAt r)).RiemannRochAxiom (arithmeticMajorantSourceCone r) := by
  intro hRR
  have hle := ((scalingSubsurface (realTestsAt r)).sourceCone_riemannRoch_iff_le_defect_without_symmetry
    (arithmeticMajorantSourceEnergy_nonneg hr) (majorant_fibre r)).mp hRR
  obtain ⟨f, hm, -, -⟩ := exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq hr 0
    (0 : realTestsAt r →ₗ[ℝ] ℝ)
  have h := hle (0, 0, f)
  rw [majorant_eq hr] at h
  have hc : 0 < 2 * (10 + 72 * Real.exp r) := by positivity
  linarith only [h, mul_pos hc hm]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
