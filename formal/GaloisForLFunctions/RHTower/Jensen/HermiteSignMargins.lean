import GaloisForLFunctions.HTGeometry.HermitePerturbationRealRoots
import GaloisForLFunctions.HTGeometry.HermiteSignChanges

/-!
# Explicit finite Hermite sign margins

Reciprocal sums of root gaps give disjoint sign intervals. Reciprocal sums
of their endpoint values give a positive margin with no continuity choice.
-/

open Polynomial Finset
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Reciprocal root gaps define an explicit common interval radius. -/
def finiteRootSignRadius (Z : Finset ℝ) : ℝ := by
  classical
  exact (1 + ∑ z ∈ Z, ∑ w ∈ Z.erase z, 4 / |z - w|)⁻¹

theorem finiteRootSignRadius_pos (Z : Finset ℝ) : 0 < finiteRootSignRadius Z := by
  classical
  have hsum : 0 ≤ ∑ z ∈ Z, ∑ w ∈ Z.erase z, 4 / |z - w| := by
    apply Finset.sum_nonneg
    intro z hz
    apply Finset.sum_nonneg
    intro w hw
    positivity
  unfold finiteRootSignRadius
  positivity

theorem finiteRootSignRadius_separated (Z : Finset ℝ) {z w : ℝ}
    (hz : z ∈ Z) (hw : w ∈ Z) (hzw : z ≠ w) :
    2 * finiteRootSignRadius Z < |z - w| := by
  classical
  have hd : 0 < |z - w| := abs_pos.mpr (sub_ne_zero.mpr hzw)
  have h₁ : 4 / |z - w| ≤ ∑ v ∈ Z.erase z, 4 / |z - v| :=
    Finset.single_le_sum (f := fun v : ℝ => 4 / |z - v|)
      (fun v _ => by positivity) (Finset.mem_erase.mpr ⟨hzw.symm, hw⟩)
  have h₂ : (∑ v ∈ Z.erase z, 4 / |z - v|) ≤
      ∑ u ∈ Z, ∑ v ∈ Z.erase u, 4 / |u - v| :=
    Finset.single_le_sum (f := fun u : ℝ => ∑ v ∈ Z.erase u, 4 / |u - v|)
      (fun u _ => Finset.sum_nonneg (fun v _ => by positivity)) hz
  have hsum : 0 ≤ ∑ u ∈ Z, ∑ v ∈ Z.erase u, 4 / |u - v| :=
    (by positivity : 0 ≤ 4 / |z - w|).trans (h₁.trans h₂)
  have hmul := (div_le_iff₀ hd).mp (h₁.trans h₂)
  unfold finiteRootSignRadius
  rw [← div_eq_mul_inv]
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith only [hmul, hd]

private theorem product_changes_sign_at_root (Z : Finset ℝ) {z ε : ℝ}
    (hz : z ∈ Z) (hε : 0 < ε)
    (hsep : ∀ w ∈ Z, z ≠ w → 2 * ε < |z - w|) :
    (∏ w ∈ Z, (z - ε - w)) * (∏ w ∈ Z, (z + ε - w)) < 0 := by
  classical
  have hprod : 0 < (∏ w ∈ Z.erase z, (z - ε - w)) *
      (∏ w ∈ Z.erase z, (z + ε - w)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro w hw
    have hgap := hsep w (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
    have hsmall : ε < |z - w| := by linarith only [hgap, hε]
    have hsq := (sq_lt_sq₀ hε.le (abs_nonneg (z - w))).mpr hsmall
    rw [sq_abs] at hsq
    nlinarith only [hsq]
  rw [← Finset.mul_prod_erase Z (fun w => z - ε - w) hz,
    ← Finset.mul_prod_erase Z (fun w => z + ε - w) hz]
  calc
    _ = -(ε ^ 2) * ((∏ w ∈ Z.erase z, (z - ε - w)) *
        (∏ w ∈ Z.erase z, (z + ε - w))) := by ring
    _ < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hε)) hprod

/-- The finite, simple real root set of the degree-`d` Hermite polynomial. -/
def hermiteSignRoots (d : ℕ) : Finset ℝ := (hermiteReal d).roots.toFinset

theorem hermiteSignRoots_card (d : ℕ) : (hermiteSignRoots d).card = d :=
  card_roots_toFinset_hermiteReal d

theorem hermiteReal_eq_product_signRoots (d : ℕ) :
    hermiteReal d = ∏ z ∈ hermiteSignRoots d, (X - C z) := by
  classical
  have h := (splits_hermiteReal d).eq_prod_roots
  have hm : (hermiteReal d).Monic := (hermite_monic d).map (Int.castRingHom ℝ)
  rw [hm.leadingCoeff, C_1, one_mul] at h
  calc
    _ = ((hermiteReal d).roots.map (fun z => X - C z)).prod := h
    _ = _ := by
      change ((hermiteReal d).roots.map (fun z => X - C z)).prod =
        ((hermiteReal d).roots.toFinset.val.map (fun z => X - C z)).prod
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots_hermiteReal d)]

theorem hermiteSignRoots_sign_change (d : ℕ) {z : ℝ} (hz : z ∈ hermiteSignRoots d) :
    (hermiteReal d).eval (z - finiteRootSignRadius (hermiteSignRoots d)) *
      (hermiteReal d).eval (z + finiteRootSignRadius (hermiteSignRoots d)) < 0 := by
  rw [hermiteReal_eq_product_signRoots d, Polynomial.eval_prod, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact product_changes_sign_at_root (hermiteSignRoots d) hz
    (finiteRootSignRadius_pos _) (fun w hw hzw => finiteRootSignRadius_separated _ hz hw hzw)

/-- A finite endpoint-radius bound containing every Hermite sign sample. -/
def hermiteSignSampleBound (d : ℕ) : ℝ :=
  1 + ∑ z ∈ hermiteSignRoots d,
    (|z - finiteRootSignRadius (hermiteSignRoots d)| + |z + finiteRootSignRadius (hermiteSignRoots d)|)

theorem one_le_hermiteSignSampleBound (d : ℕ) : 1 ≤ hermiteSignSampleBound d := by
  have h := Finset.sum_nonneg (fun z (_ : z ∈ hermiteSignRoots d) =>
    add_nonneg (abs_nonneg (z - finiteRootSignRadius (hermiteSignRoots d)))
      (abs_nonneg (z + finiteRootSignRadius (hermiteSignRoots d))))
  unfold hermiteSignSampleBound
  linarith only [h]

theorem abs_hermiteSignSamples_le (d : ℕ) {z : ℝ} (hz : z ∈ hermiteSignRoots d) :
    |z - finiteRootSignRadius (hermiteSignRoots d)| ≤ hermiteSignSampleBound d ∧
      |z + finiteRootSignRadius (hermiteSignRoots d)| ≤ hermiteSignSampleBound d := by
  have h := Finset.single_le_sum (fun w (_ : w ∈ hermiteSignRoots d) =>
    add_nonneg (abs_nonneg (w - finiteRootSignRadius (hermiteSignRoots d)))
      (abs_nonneg (w + finiteRootSignRadius (hermiteSignRoots d)))) hz
  unfold hermiteSignSampleBound
  constructor <;> linarith only [h, abs_nonneg (z - finiteRootSignRadius (hermiteSignRoots d)),
    abs_nonneg (z + finiteRootSignRadius (hermiteSignRoots d))]

/-- A positive finite reciprocal-sum margin for all sign-sample values. -/
def hermiteSignMargin (d : ℕ) : ℝ :=
  (1 + ∑ z ∈ hermiteSignRoots d,
    (|(hermiteReal d).eval (z - finiteRootSignRadius (hermiteSignRoots d))|⁻¹ +
      |(hermiteReal d).eval (z + finiteRootSignRadius (hermiteSignRoots d))|⁻¹))⁻¹

theorem hermiteSignMargin_pos (d : ℕ) : 0 < hermiteSignMargin d := by
  have h : 0 ≤ ∑ z ∈ hermiteSignRoots d,
      (|(hermiteReal d).eval (z - finiteRootSignRadius (hermiteSignRoots d))|⁻¹ +
        |(hermiteReal d).eval (z + finiteRootSignRadius (hermiteSignRoots d))|⁻¹) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  unfold hermiteSignMargin
  positivity

theorem hermiteSignMargin_le_values (d : ℕ) {z : ℝ} (hz : z ∈ hermiteSignRoots d) :
    hermiteSignMargin d ≤ |(hermiteReal d).eval (z - finiteRootSignRadius (hermiteSignRoots d))| ∧
      hermiteSignMargin d ≤ |(hermiteReal d).eval (z + finiteRootSignRadius (hermiteSignRoots d))| := by
  have hsign := hermiteSignRoots_sign_change d hz
  have hleft : 0 < |(hermiteReal d).eval (z - finiteRootSignRadius (hermiteSignRoots d))| := by
    apply abs_pos.mpr
    intro he
    rw [he, zero_mul] at hsign
    exact (lt_irrefl 0) hsign
  have hright : 0 < |(hermiteReal d).eval (z + finiteRootSignRadius (hermiteSignRoots d))| := by
    apply abs_pos.mpr
    intro he
    rw [he, mul_zero] at hsign
    exact (lt_irrefl 0) hsign
  have hsum : 0 ≤ ∑ w ∈ hermiteSignRoots d,
      (|(hermiteReal d).eval (w - finiteRootSignRadius (hermiteSignRoots d))|⁻¹ +
        |(hermiteReal d).eval (w + finiteRootSignRadius (hermiteSignRoots d))|⁻¹) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hterm := Finset.single_le_sum (fun w (_ : w ∈ hermiteSignRoots d) =>
    add_nonneg (inv_nonneg.mpr (abs_nonneg
      ((hermiteReal d).eval (w - finiteRootSignRadius (hermiteSignRoots d)))))
      (inv_nonneg.mpr (abs_nonneg
        ((hermiteReal d).eval (w + finiteRootSignRadius (hermiteSignRoots d)))))) hz
  have hL := inv_nonneg.mpr hleft.le
  have hR := inv_nonneg.mpr hright.le
  unfold hermiteSignMargin
  constructor
  · apply (inv_le_iff_one_le_mul₀ (by positivity)).mpr
    have hbound : |(hermiteReal d).eval (z - finiteRootSignRadius (hermiteSignRoots d))|⁻¹ ≤
        1 + ∑ w ∈ hermiteSignRoots d,
          (|(hermiteReal d).eval (w - finiteRootSignRadius (hermiteSignRoots d))|⁻¹ +
            |(hermiteReal d).eval (w + finiteRootSignRadius (hermiteSignRoots d))|⁻¹) := by
      linarith only [hterm, hR]
    have h := mul_le_mul_of_nonneg_left hbound hleft.le
    rwa [mul_inv_cancel₀ hleft.ne'] at h
  · apply (inv_le_iff_one_le_mul₀ (by positivity)).mpr
    have hbound : |(hermiteReal d).eval (z + finiteRootSignRadius (hermiteSignRoots d))|⁻¹ ≤
        1 + ∑ w ∈ hermiteSignRoots d,
          (|(hermiteReal d).eval (w - finiteRootSignRadius (hermiteSignRoots d))|⁻¹ +
            |(hermiteReal d).eval (w + finiteRootSignRadius (hermiteSignRoots d))|⁻¹) := by
      linarith only [hterm, hL]
    have h := mul_le_mul_of_nonneg_left hbound hright.le
    rwa [mul_inv_cancel₀ hright.ne'] at h

end RHTower

#print axioms RHTower.finiteRootSignRadius_separated
#print axioms RHTower.hermiteSignRoots_sign_change
#print axioms RHTower.hermiteSignMargin_le_values
