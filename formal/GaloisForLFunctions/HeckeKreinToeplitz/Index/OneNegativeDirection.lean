import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Geometry of one negative direction

The form on `H × ℂ` is the Hilbert inner product minus the scalar product.
Its nonpositive vectors have positive orthogonal hyperplanes, and distinct
normalized nonpositive vectors have nonzero pairing. These are the geometric
constraints behind the common eigenline theorem for commuting isometries.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hermitian form with one negative scalar direction. -/
def pairing (v w : H × ℂ) : ℂ := inner ℂ v.1 w.1 - conj v.2 * w.2

theorem pairing_conj_symm (v w : H × ℂ) : conj (pairing w v) = pairing v w := by
  simp only [pairing, map_sub, map_mul, conj_conj, inner_conj_symm]
  ring

theorem pairing_smul_left (a : ℂ) (v w : H × ℂ) :
    pairing (a • v) w = conj a * pairing v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, inner_smul_left, map_mul]
  ring

theorem pairing_smul_right (a : ℂ) (v w : H × ℂ) :
    pairing v (a • w) = a * pairing v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, inner_smul_right]
  ring

theorem pairing_add_left (u v w : H × ℂ) :
    pairing (u + v) w = pairing u w + pairing v w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, inner_add_left, map_add]
  ring

theorem pairing_add_right (u v w : H × ℂ) :
    pairing u (v + w) = pairing u v + pairing u w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

theorem pairing_self_re (v : H × ℂ) :
    (pairing v v).re = ‖v.1‖ ^ 2 - ‖v.2‖ ^ 2 := by
  rw [pairing, Complex.sub_re, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v.1

theorem pairing_self_nonpos_iff (v : H × ℂ) :
    (pairing v v).re ≤ 0 ↔ ‖v.1‖ ≤ ‖v.2‖ := by
  rw [pairing_self_re, sub_nonpos]
  exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)

/-- A nonzero nonpositive vector must have a nonzero scalar coordinate. -/
theorem snd_ne_zero_of_nonpositive {v : H × ℂ} (hv : v ≠ 0)
    (hq : (pairing v v).re ≤ 0) : v.2 ≠ 0 := by
  intro hzero
  have h := (pairing_self_nonpos_iff v).mp hq
  rw [hzero, norm_zero] at h
  have hf : v.1 = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  exact hv (Prod.ext hf hzero)

theorem eq_zero_of_nonpositive_snd_eq_zero {v : H × ℂ}
    (hq : (pairing v v).re ≤ 0) (hs : v.2 = 0) : v = 0 := by
  by_contra hv
  exact snd_ne_zero_of_nonpositive hv hq hs

/-- Orthogonality to a nonzero nonpositive vector forces a nonnegative square. -/
theorem nonneg_of_orthogonal_nonpositive {v : H × ℂ} (hv : v ≠ 0)
    (hq : (pairing v v).re ≤ 0) {w : H × ℂ} (horth : pairing v w = 0) :
    0 ≤ (pairing w w).re := by
  have ha : 0 < ‖v.2‖ := norm_pos_iff.mpr (snd_ne_zero_of_nonpositive hv hq)
  have hvnorm := (pairing_self_nonpos_iff v).mp hq
  have he : inner ℂ v.1 w.1 = conj v.2 * w.2 := sub_eq_zero.mp horth
  have hcs : ‖v.2‖ * ‖w.2‖ ≤ ‖v.2‖ * ‖w.1‖ := by
    calc
      ‖v.2‖ * ‖w.2‖ = ‖inner ℂ v.1 w.1‖ := by rw [he, norm_mul, norm_conj]
      _ ≤ ‖v.1‖ * ‖w.1‖ := norm_inner_le_norm _ _
      _ ≤ ‖v.2‖ * ‖w.1‖ := mul_le_mul_of_nonneg_right hvnorm (norm_nonneg _)
  have hw : ‖w.2‖ ≤ ‖w.1‖ := (mul_le_mul_iff_right₀ ha).mp hcs
  rw [pairing_self_re]
  exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hw)

theorem pairing_normalized (z w : H) :
    pairing (z, (1 : ℂ)) (w, 1) = inner ℂ z w - 1 := by
  simp only [pairing, map_one, one_mul]

/-- Two normalized nonpositive vectors with zero pairing are equal. -/
theorem eq_of_pairing_normalized_eq_zero {z w : H} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (h : pairing (z, (1 : ℂ)) (w, 1) = 0) : z = w := by
  rw [pairing_normalized, sub_eq_zero] at h
  have he := norm_sub_sq (𝕜 := ℂ) z w
  rw [h] at he
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith only [hz, norm_nonneg z]
  have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith only [hw, norm_nonneg w]
  have hzero : ‖z - w‖ = 0 := by
    norm_num only [RCLike.one_re] at he
    nlinarith only [he, hz2, hw2, norm_nonneg (z - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- An eigenvector with a nonunit-modulus eigenvalue is isotropic. -/
theorem pairing_self_eq_zero_of_nonunit_eigenvalue
    (T : (H × ℂ) →ₗ[ℂ] (H × ℂ))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    {a : ℂ} (ha : ‖a‖ ≠ 1) {v : H × ℂ} (hv : T v = a • v) :
    pairing v v = 0 := by
  have hfactor : conj a * a - 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re (sub_eq_zero.mp h)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, Complex.one_re] at he
    exact ha (by nlinarith only [he, norm_nonneg a])
  have he := hT v v
  rw [hv, pairing_smul_left, pairing_smul_right] at he
  have hz : (conj a * a - 1) * pairing v v = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left hfactor

/-- A nonunit eigenvalue has a one-dimensional eigenspace. -/
theorem eigenvector_eq_scalar_mul_of_nonunit
    (T : (H × ℂ) →ₗ[ℂ] (H × ℂ))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    {a : ℂ} (ha : ‖a‖ ≠ 1) {v w : H × ℂ}
    (hv : T v = a • v) (hw : T w = a • w) (hv0 : v ≠ 0) :
    w = (w.2 / v.2) • v := by
  have hvq := pairing_self_eq_zero_of_nonunit_eigenvalue T hT ha hv
  have hv2 : v.2 ≠ 0 := snd_ne_zero_of_nonpositive hv0 (by rw [hvq]; rfl)
  have hd : T (w - (w.2 / v.2) • v) = a • (w - (w.2 / v.2) • v) := by
    rw [map_sub, map_smul, hw, hv, smul_sub]
    congr 1
    exact smul_comm _ _ _
  have hdq := pairing_self_eq_zero_of_nonunit_eigenvalue T hT ha hd
  have hds : (w - (w.2 / v.2) • v).2 = 0 := by
    change w.2 - (w.2 / v.2) * v.2 = 0
    rw [div_mul_cancel₀ _ hv2, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_nonpositive_snd_eq_zero (by rw [hdq]; rfl) hds)

/-- A unitary eigenvalue on a nonpositive line is the only eigenvalue on such lines. -/
theorem eigenvalue_eq_of_normalized_nonpositive
    (T : (H × ℂ) →ₗ[ℂ] (H × ℂ))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    {z w : H} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    {a b : ℂ} (ha : ‖a‖ = 1)
    (hza : T (z, 1) = a • (z, 1)) (hwb : T (w, 1) = b • (w, 1)) : b = a := by
  by_cases hpair : pairing (z, (1 : ℂ)) (w, 1) = 0
  · have hzw := eq_of_pairing_normalized_eq_zero hz hw hpair
    rw [hzw] at hza
    have he := congrArg Prod.snd (hwb.symm.trans hza)
    simpa only [Prod.smul_snd, smul_eq_mul, mul_one] using he
  · have he := hT (z, 1) (w, 1)
    rw [hza, hwb, pairing_smul_left, pairing_smul_right] at he
    have hab : conj a * b = 1 := by
      apply mul_right_cancel₀ hpair
      simpa only [one_mul, mul_assoc] using he
    have haa : conj a * a = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
      norm_num
    have ha0 : conj a ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at haa
      exact zero_ne_one haa
    exact mul_left_cancel₀ ha0 (hab.trans haa.symm)

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
