import GaloisForLFunctions.HTGeometry.LyapunovInverseBounds

/-!
# Norm bounds for the Sylvester equation

A solution of `x z + z y = d` with `μ • 1 ≤ x` and `ν • 1 ≤ y` satisfies `(μ + ν) ‖z‖ ≤ ‖d‖`,
in the operator norm and — when `z` is Hilbert–Schmidt — in the Hilbert–Schmidt norm.  The proof
is the two-sided midpoint identity `(μ' + ν') z = d - (x - μ') z - z (y - ν')`: each commutator
term is bounded by the half-length of a Loewner interval, and midpoint minus half-length is the
lower Loewner bound.

This is the estimate that makes the *difference* of two geometric means Lipschitz: if
`x = a # b` and `y = a # c` then `x a⁻¹ (x - y) + (x - y) a⁻¹ y = b - c`, a Sylvester equation
with positive coefficients.
-/

open scoped Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The two-sided midpoint identity behind the Sylvester norm bounds. -/
lemma sylvester_midpoint_identity {x y z d : A} (μ ν : ℝ) (heq : x * z + z * y = d) :
    (μ + ν) • z = d - (x - μ • (1 : A)) * z - z * (y - ν • (1 : A)) := by
  rw [← heq, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

/-- **Operator-norm bound for the Sylvester equation.** -/
theorem norm_le_of_sylvester {x y z d : A} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hxl : μ • (1 : A) ≤ x) (hyl : ν • (1 : A) ≤ y) (heq : x * z + z * y = d) :
    (μ + ν) * ‖z‖ ≤ ‖d‖ := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · have hz : z = 0 := Subsingleton.elim _ _
    have hd : d = 0 := Subsingleton.elim _ _
    rw [hz, hd, norm_zero, mul_zero]
  have hxM : x ≤ ‖x‖ • (1 : A) := by
    have h := hx.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hyM : y ≤ ‖y‖ • (1 : A) := by
    have h := hy.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hμM : μ ≤ ‖x‖ := by
    have h0 : (0 : A) ≤ μ • (1 : A) := smul_nonneg hμ.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hxl
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hμ, norm_one, mul_one] at h
  have hνM : ν ≤ ‖y‖ := by
    have h0 : (0 : A) ≤ ν • (1 : A) := smul_nonneg hν.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hyl
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hν, norm_one, mul_one] at h
  have hwx : ‖x - ((μ + ‖x‖) / 2) • (1 : A)‖ ≤ (‖x‖ - μ) / 2 :=
    norm_sub_midpoint_le hμM hx hxl hxM
  have hwy : ‖y - ((ν + ‖y‖) / 2) • (1 : A)‖ ≤ (‖y‖ - ν) / 2 :=
    norm_sub_midpoint_le hνM hy hyl hyM
  have hid := sylvester_midpoint_identity (x := x) (y := y) (z := z) (d := d)
    ((μ + ‖x‖) / 2) ((ν + ‖y‖) / 2) heq
  have hpos : (0 : ℝ) < (μ + ‖x‖) / 2 + (ν + ‖y‖) / 2 := by linarith
  have hL : ‖((μ + ‖x‖) / 2 + (ν + ‖y‖) / 2) • z‖
      = ((μ + ‖x‖) / 2 + (ν + ‖y‖) / 2) * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
  have hbound : ((μ + ‖x‖) / 2 + (ν + ‖y‖) / 2) * ‖z‖
      ≤ ‖d‖ + ((‖x‖ - μ) / 2) * ‖z‖ + ‖z‖ * ((‖y‖ - ν) / 2) := by
    rw [← hL, hid]
    have ha := norm_sub_le (d - (x - ((μ + ‖x‖) / 2) • (1 : A)) * z)
      (z * (y - ((ν + ‖y‖) / 2) • (1 : A)))
    have hb := norm_sub_le d ((x - ((μ + ‖x‖) / 2) • (1 : A)) * z)
    have hc : ‖(x - ((μ + ‖x‖) / 2) • (1 : A)) * z‖ ≤ ((‖x‖ - μ) / 2) * ‖z‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hwx (norm_nonneg _))
    have hd2 : ‖z * (y - ((ν + ‖y‖) / 2) • (1 : A))‖ ≤ ‖z‖ * ((‖y‖ - ν) / 2) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hwy (norm_nonneg _))
    linarith
  nlinarith [norm_nonneg z, norm_nonneg d]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The Sylvester solution is close to `d/2` when both coefficients are close to `1`. -/
lemma two_smul_sub_sylvester_identity {x y z d : A} (heq : x * z + z * y = d) :
    (2 : ℝ) • z - d = -((x - 1) * z) - z * (y - 1) := by
  rw [← heq, sub_mul, mul_sub, one_mul, mul_one]
  module

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Comparison of the Sylvester solution with the linear solution at the identity.** -/
theorem norm_two_smul_sub_sylvester {x y z d : A} (heq : x * z + z * y = d) :
    ‖(2 : ℝ) • z - d‖ ≤ (‖x - 1‖ + ‖y - 1‖) * ‖z‖ := by
  rw [two_smul_sub_sylvester_identity heq]
  calc ‖-((x - 1) * z) - z * (y - 1)‖ ≤ ‖-((x - 1) * z)‖ + ‖z * (y - 1)‖ := norm_sub_le _ _
    _ = ‖(x - 1) * z‖ + ‖z * (y - 1)‖ := by rw [norm_neg]
    _ ≤ ‖x - 1‖ * ‖z‖ + ‖z‖ * ‖y - 1‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = (‖x - 1‖ + ‖y - 1‖) * ‖z‖ := by ring

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Perturbation identity for the Sylvester equation.**  The difference of two Sylvester
solutions is itself a Sylvester solution, for the first pair of coefficients. -/
lemma sylvester_sub_sylvester {x₁ y₁ x₂ y₂ z₁ z₂ d₁ d₂ : A}
    (h1 : x₁ * z₁ + z₁ * y₁ = d₁) (h2 : x₂ * z₂ + z₂ * y₂ = d₂) :
    x₁ * (z₁ - z₂) + (z₁ - z₂) * y₁
      = (d₁ - d₂) - (x₁ - x₂) * z₂ - z₂ * (y₁ - y₂) := by
  have hL : x₁ * (z₁ - z₂) + (z₁ - z₂) * y₁
      = (x₁ * z₁ + z₁ * y₁) - x₁ * z₂ - z₂ * y₁ := by noncomm_ring
  have hR : (d₁ - d₂) - (x₁ - x₂) * z₂ - z₂ * (y₁ - y₂)
      = d₁ - d₂ - x₁ * z₂ - z₂ * y₁ + (x₂ * z₂ + z₂ * y₂) := by noncomm_ring
  rw [hL, hR, h1, h2]
  abel

/-- **Perturbation bound for the Sylvester equation** (operator norm). -/
theorem norm_sylvester_sub_le {x₁ y₁ x₂ y₂ z₁ z₂ d₁ d₂ : A}
    (hx₁ : IsSelfAdjoint x₁) (hy₁ : IsSelfAdjoint y₁) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hxl : μ • (1 : A) ≤ x₁) (hyl : ν • (1 : A) ≤ y₁)
    (h1 : x₁ * z₁ + z₁ * y₁ = d₁) (h2 : x₂ * z₂ + z₂ * y₂ = d₂) :
    (μ + ν) * ‖z₁ - z₂‖ ≤ ‖d₁ - d₂‖ + (‖x₁ - x₂‖ + ‖y₁ - y₂‖) * ‖z₂‖ := by
  have hkey := norm_le_of_sylvester hx₁ hy₁ hμ hν hxl hyl (sylvester_sub_sylvester h1 h2)
  refine hkey.trans ?_
  have ha := norm_sub_le ((d₁ - d₂) - (x₁ - x₂) * z₂) (z₂ * (y₁ - y₂))
  have hb := norm_sub_le (d₁ - d₂) ((x₁ - x₂) * z₂)
  have hc : ‖(x₁ - x₂) * z₂‖ ≤ ‖x₁ - x₂‖ * ‖z₂‖ := norm_mul_le _ _
  have hd : ‖z₂ * (y₁ - y₂)‖ ≤ ‖z₂‖ * ‖y₁ - y₂‖ := norm_mul_le _ _
  nlinarith [norm_nonneg z₂]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- **Hilbert–Schmidt bound for the Sylvester equation.** -/
theorem hsNorm_le_of_sylvester {x y z d : E →L[ℂ] E} (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) (hz : IsHilbertSchmidt z) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hxl : μ • (1 : E →L[ℂ] E) ≤ x) (hyl : ν • (1 : E →L[ℂ] E) ≤ y)
    (heq : x * z + z * y = d) :
    (μ + ν) * hsNorm z ≤ hsNorm d := by
  rcases subsingleton_or_nontrivial (E →L[ℂ] E) with hsub | hnt
  · have hz0 : z = 0 := Subsingleton.elim _ _
    have hd0 : d = 0 := Subsingleton.elim _ _
    rw [hz0, hd0, hsNorm_zero, mul_zero]
  have hxM : x ≤ ‖x‖ • (1 : E →L[ℂ] E) := by
    have h := hx.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hyM : y ≤ ‖y‖ • (1 : E →L[ℂ] E) := by
    have h := hy.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hμM : μ ≤ ‖x‖ := by
    have h0 : (0 : E →L[ℂ] E) ≤ μ • (1 : E →L[ℂ] E) := smul_nonneg hμ.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hxl
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hμ, norm_one, mul_one] at h
  have hνM : ν ≤ ‖y‖ := by
    have h0 : (0 : E →L[ℂ] E) ≤ ν • (1 : E →L[ℂ] E) := smul_nonneg hν.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hyl
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hν, norm_one, mul_one] at h
  have hwx : ‖x - ((μ + ‖x‖) / 2) • (1 : E →L[ℂ] E)‖ ≤ (‖x‖ - μ) / 2 :=
    norm_sub_midpoint_le hμM hx hxl hxM
  have hwy : ‖y - ((ν + ‖y‖) / 2) • (1 : E →L[ℂ] E)‖ ≤ (‖y‖ - ν) / 2 :=
    norm_sub_midpoint_le hνM hy hyl hyM
  have hid := sylvester_midpoint_identity (x := x) (y := y) (z := z) (d := d)
    ((μ + ‖x‖) / 2) ((ν + ‖y‖) / 2) heq
  have hpos : (0 : ℝ) < (μ + ‖x‖) / 2 + (ν + ‖y‖) / 2 := by linarith
  have hdHS : IsHilbertSchmidt d := by
    rw [← heq]; exact (hz.comp_left x).add (hz.comp_right y)
  have h1 : IsHilbertSchmidt ((x - ((μ + ‖x‖) / 2) • (1 : E →L[ℂ] E)) * z : E →L[ℂ] E) :=
    hz.comp_left _
  have h2 : IsHilbertSchmidt (z * (y - ((ν + ‖y‖) / 2) • (1 : E →L[ℂ] E)) : E →L[ℂ] E) :=
    hz.comp_right _
  have hbound : ((μ + ‖x‖) / 2 + (ν + ‖y‖) / 2) * hsNorm z
      ≤ hsNorm d + ((‖x‖ - μ) / 2) * hsNorm z + hsNorm z * ((‖y‖ - ν) / 2) := by
    have hL : hsNorm (((μ + ‖x‖) / 2 + (ν + ‖y‖) / 2) • z)
        = ((μ + ‖x‖) / 2 + (ν + ‖y‖) / 2) * hsNorm z := by
      rw [hsNorm_real_smul, abs_of_pos hpos]
    have ha := hsNorm_sub_le (hdHS.sub h1) h2
    have hb := hsNorm_sub_le hdHS h1
    have hc : hsNorm ((x - ((μ + ‖x‖) / 2) • (1 : E →L[ℂ] E)) * z : E →L[ℂ] E)
        ≤ ((‖x‖ - μ) / 2) * hsNorm z :=
      (hsNorm_comp_left_le hz).trans (mul_le_mul_of_nonneg_right hwx (hsNorm_nonneg _))
    have hd2 : hsNorm (z * (y - ((ν + ‖y‖) / 2) • (1 : E →L[ℂ] E)) : E →L[ℂ] E)
        ≤ hsNorm z * ((‖y‖ - ν) / 2) :=
      (hsNorm_comp_right_le hz).trans (mul_le_mul_of_nonneg_left hwy (hsNorm_nonneg _))
    rw [← hL, hid]
    linarith
  nlinarith [hsNorm_nonneg z, hsNorm_nonneg d]

/-- **The Sylvester inverse preserves the Hilbert–Schmidt class.**  If `x z + z y` is
Hilbert–Schmidt with `x, y` bounded below in the Loewner order, then so is `z`. -/
theorem isHilbertSchmidt_of_sylvester {x y z d : E →L[ℂ] E} (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hxl : μ • (1 : E →L[ℂ] E) ≤ x) (hyl : ν • (1 : E →L[ℂ] E) ≤ y)
    (hd : IsHilbertSchmidt d) (heq : x * z + z * y = d) : IsHilbertSchmidt z := by
  rcases subsingleton_or_nontrivial (E →L[ℂ] E) with hsub | hnt
  · exact (Subsingleton.elim z 0) ▸ isHilbertSchmidt_zero
  have hxM : x ≤ ‖x‖ • (1 : E →L[ℂ] E) := by
    have h := hx.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hyM : y ≤ ‖y‖ • (1 : E →L[ℂ] E) := by
    have h := hy.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hμM : μ ≤ ‖x‖ := by
    have h0 : (0 : E →L[ℂ] E) ≤ μ • (1 : E →L[ℂ] E) := smul_nonneg hμ.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hxl
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hμ, norm_one, mul_one] at h
  have hνM : ν ≤ ‖y‖ := by
    have h0 : (0 : E →L[ℂ] E) ≤ ν • (1 : E →L[ℂ] E) := smul_nonneg hν.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hyl
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hν, norm_one, mul_one] at h
  obtain ⟨S, R, wx, wy, hSpos, hRnn, hRS, hSdef, hRdef, hwxdef, hwydef, hwxn, hwyn⟩ :
      ∃ (S R : ℝ) (wx wy : E →L[ℂ] E), 0 < S ∧ 0 ≤ R ∧ R < S ∧
        S = (μ + ‖x‖) / 2 + (ν + ‖y‖) / 2 ∧ R = (‖x‖ - μ) / 2 + (‖y‖ - ν) / 2 ∧
        wx = x - ((μ + ‖x‖) / 2) • (1 : E →L[ℂ] E) ∧
        wy = y - ((ν + ‖y‖) / 2) • (1 : E →L[ℂ] E) ∧ ‖wx‖ ≤ (‖x‖ - μ) / 2
          ∧ ‖wy‖ ≤ (‖y‖ - ν) / 2 :=
    ⟨(μ + ‖x‖) / 2 + (ν + ‖y‖) / 2, (‖x‖ - μ) / 2 + (‖y‖ - ν) / 2, _, _,
      by linarith, by linarith, by linarith, rfl, rfl,
      rfl, rfl, norm_sub_midpoint_le hμM hx hxl hxM, norm_sub_midpoint_le hνM hy hyl hyM⟩
  have hfix : z = S⁻¹ • (d - wx * z - z * wy) := by
    have hid : S • z = d - wx * z - z * wy := by
      rw [hwxdef, hwydef, hSdef]
      exact sylvester_midpoint_identity _ _ heq
    rw [← hid, smul_smul, inv_mul_cancel₀ (ne_of_gt hSpos), one_smul]
  obtain ⟨zn, hz0, hstep⟩ : ∃ zn : ℕ → (E →L[ℂ] E), zn 0 = 0 ∧
      ∀ n, zn (n + 1) = S⁻¹ • (d - wx * zn n - zn n * wy) :=
    ⟨fun n => (fun t => S⁻¹ • (d - wx * t - t * wy))^[n] 0, rfl,
      fun n => Function.iterate_succ_apply' _ n 0⟩
  have hHS : ∀ n, IsHilbertSchmidt (zn n) := by
    intro n
    induction n with
    | zero => rw [hz0]; exact isHilbertSchmidt_zero
    | succ n ih =>
      rw [hstep]
      exact IsHilbertSchmidt.real_smul ((hd.sub (ih.comp_left wx)).sub (ih.comp_right wy)) _
  obtain ⟨K, hKnn, hdK⟩ : ∃ K : ℝ, 0 ≤ K ∧ hsNorm d = (S - R) * K := by
    have hSR : (0 : ℝ) < S - R := by linarith
    exact ⟨hsNorm d / (S - R), div_nonneg (hsNorm_nonneg d) hSR.le, by field_simp⟩
  have hwxnn : (0 : ℝ) ≤ ‖wx‖ := norm_nonneg _
  have hwynn : (0 : ℝ) ≤ ‖wy‖ := norm_nonneg _
  have hbound : ∀ n, hsNorm (zn n) ≤ K := by
    intro n
    induction n with
    | zero => rw [hz0, hsNorm_zero]; exact hKnn
    | succ n ih =>
      have hHSn := hHS n
      have h1 : hsNorm (wx * zn n : E →L[ℂ] E) ≤ ‖wx‖ * hsNorm (zn n) :=
        hsNorm_comp_left_le hHSn
      have h2 : hsNorm (zn n * wy : E →L[ℂ] E) ≤ hsNorm (zn n) * ‖wy‖ :=
        hsNorm_comp_right_le hHSn
      have h3 : hsNorm (d - wx * zn n - zn n * wy : E →L[ℂ] E)
          ≤ hsNorm d + ‖wx‖ * hsNorm (zn n) + hsNorm (zn n) * ‖wy‖ := by
        have ha : hsNorm ((d - wx * zn n) - zn n * wy : E →L[ℂ] E)
            ≤ hsNorm (d - wx * zn n : E →L[ℂ] E) + hsNorm (zn n * wy : E →L[ℂ] E) :=
          hsNorm_sub_le (hd.sub (hHSn.comp_left wx)) (hHSn.comp_right wy)
        have hb : hsNorm (d - wx * zn n : E →L[ℂ] E)
            ≤ hsNorm d + hsNorm (wx * zn n : E →L[ℂ] E) :=
          hsNorm_sub_le hd (hHSn.comp_left wx)
        linarith
      have hnn : 0 ≤ hsNorm (zn n) := hsNorm_nonneg _
      rw [hstep, hsNorm_real_smul, abs_of_pos (inv_pos.mpr hSpos)]
      have hkey : hsNorm (d - wx * zn n - zn n * wy : E →L[ℂ] E) ≤ S * K := by
        have hwK : ‖wx‖ * hsNorm (zn n) + hsNorm (zn n) * ‖wy‖ ≤ R * K := by
          rw [hRdef]
          nlinarith [hwxn, hwyn, ih, hnn, hKnn]
        rw [hdK] at h3
        linarith
      calc S⁻¹ * hsNorm (d - wx * zn n - zn n * wy : E →L[ℂ] E) ≤ S⁻¹ * (S * K) :=
            mul_le_mul_of_nonneg_left hkey (inv_pos.mpr hSpos).le
        _ = K := by field_simp
  have hcontr : ∀ n, ‖zn (n + 1) - z‖ ≤ (R / S) * ‖zn n - z‖ := by
    intro n
    have hdiff : zn (n + 1) - z = S⁻¹ • (-(wx * (zn n - z)) - (zn n - z) * wy) := by
      rw [hstep]
      conv_lhs => rw [hfix]
      rw [← smul_sub]
      congr 1
      simp only [mul_sub, sub_mul]
      abel
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hSpos)]
    have h1 : ‖-(wx * (zn n - z)) - (zn n - z) * wy‖ ≤ R * ‖zn n - z‖ := by
      have ha : ‖-(wx * (zn n - z))‖ ≤ ‖wx‖ * ‖zn n - z‖ := by
        rw [norm_neg]; exact norm_mul_le _ _
      have hb : ‖(zn n - z) * wy‖ ≤ ‖zn n - z‖ * ‖wy‖ := norm_mul_le _ _
      have hc := norm_sub_le (-(wx * (zn n - z))) ((zn n - z) * wy)
      rw [hRdef]
      nlinarith [norm_nonneg (zn n - z), hwxn, hwyn]
    calc S⁻¹ * ‖-(wx * (zn n - z)) - (zn n - z) * wy‖ ≤ S⁻¹ * (R * ‖zn n - z‖) :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hSpos).le
      _ = (R / S) * ‖zn n - z‖ := by field_simp
  have hratio0 : 0 ≤ R / S := div_nonneg hRnn hSpos.le
  have hgeo : ∀ n, ‖zn n - z‖ ≤ (R / S) ^ n * ‖z‖ := by
    intro n
    induction n with
    | zero => rw [hz0]; simp
    | succ n ih =>
      refine (hcontr n).trans ?_
      calc (R / S) * ‖zn n - z‖ ≤ (R / S) * ((R / S) ^ n * ‖z‖) :=
            mul_le_mul_of_nonneg_left ih hratio0
        _ = (R / S) ^ (n + 1) * ‖z‖ := by ring
  have hratio : R / S < 1 := (div_lt_one hSpos).mpr hRS
  have htend0 : Filter.Tendsto (fun n => ‖zn n - z‖) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) hgeo ?_
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio).mul_const ‖z‖
    simpa using h
  have hptw : ∀ e : E, Filter.Tendsto (fun n => zn n e) Filter.atTop (nhds (z e)) := by
    intro e
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n => ‖zn n - z‖ * ‖e‖) (fun n => norm_nonneg _)
      (fun n => ?_) ?_
    · show ‖zn n e - z e‖ ≤ ‖zn n - z‖ * ‖e‖
      exact (zn n - z).le_opNorm e
    · simpa using htend0.mul_const ‖e‖
  refine isHilbertSchmidt_of_tendsto hHS (C := K ^ 2) (fun n => ?_) hptw
  rw [← sq_hsNorm]
  exact pow_le_pow_left₀ (hsNorm_nonneg _) (hbound n) 2

/-- **Perturbation bound for the Sylvester equation** (Hilbert–Schmidt norm). -/
theorem hsNorm_sylvester_sub_le {x₁ y₁ x₂ y₂ z₁ z₂ d₁ d₂ : E →L[ℂ] E}
    (hx₁ : IsSelfAdjoint x₁) (hy₁ : IsSelfAdjoint y₁)
    (hz₁ : IsHilbertSchmidt z₁) (hz₂ : IsHilbertSchmidt z₂)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hxl : μ • (1 : E →L[ℂ] E) ≤ x₁) (hyl : ν • (1 : E →L[ℂ] E) ≤ y₁)
    (h1 : x₁ * z₁ + z₁ * y₁ = d₁) (h2 : x₂ * z₂ + z₂ * y₂ = d₂) :
    (μ + ν) * hsNorm (z₁ - z₂)
      ≤ hsNorm (d₁ - d₂) + (‖x₁ - x₂‖ + ‖y₁ - y₂‖) * hsNorm z₂ := by
  have hkey := hsNorm_le_of_sylvester hx₁ hy₁ (hz₁.sub hz₂) hμ hν hxl hyl
    (sylvester_sub_sylvester h1 h2)
  refine hkey.trans ?_
  have hdd : IsHilbertSchmidt (d₁ - d₂ : E →L[ℂ] E) := by
    rw [← h1, ← h2]
    exact ((hz₁.comp_left _).add (hz₁.comp_right _)).sub
      ((hz₂.comp_left _).add (hz₂.comp_right _))
  have h3 : IsHilbertSchmidt ((x₁ - x₂) * z₂ : E →L[ℂ] E) := hz₂.comp_left _
  have h4 : IsHilbertSchmidt (z₂ * (y₁ - y₂) : E →L[ℂ] E) := hz₂.comp_right _
  have ha := hsNorm_sub_le (hdd.sub h3) h4
  have hb := hsNorm_sub_le hdd h3
  have hc : hsNorm ((x₁ - x₂) * z₂ : E →L[ℂ] E) ≤ ‖x₁ - x₂‖ * hsNorm z₂ :=
    hsNorm_comp_left_le hz₂
  have hd : hsNorm (z₂ * (y₁ - y₂) : E →L[ℂ] E) ≤ hsNorm z₂ * ‖y₁ - y₂‖ :=
    hsNorm_comp_right_le hz₂
  nlinarith [hsNorm_nonneg z₂]

omit [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
/-- **Hilbert–Schmidt comparison of the Sylvester solution with the linear solution.** -/
theorem hsNorm_two_smul_sub_sylvester {x y z d : E →L[ℂ] E} (hz : IsHilbertSchmidt z)
    (heq : x * z + z * y = d) :
    hsNorm ((2 : ℝ) • z - d) ≤ (‖x - 1‖ + ‖y - 1‖) * hsNorm z := by
  rw [two_smul_sub_sylvester_identity heq]
  have h1 : IsHilbertSchmidt (-((x - 1) * z) : E →L[ℂ] E) := (hz.comp_left _).neg
  have h2 : IsHilbertSchmidt (z * (y - 1) : E →L[ℂ] E) := hz.comp_right _
  have hneg : hsNorm (-((x - 1) * z) : E →L[ℂ] E) = hsNorm ((x - 1) * z : E →L[ℂ] E) := by
    show Real.sqrt (hsNormSq _) = Real.sqrt (hsNormSq _)
    rw [hsNormSq_neg_eq_self]
  calc hsNorm (-((x - 1) * z) - z * (y - 1) : E →L[ℂ] E)
      ≤ hsNorm (-((x - 1) * z) : E →L[ℂ] E) + hsNorm (z * (y - 1) : E →L[ℂ] E) :=
        hsNorm_sub_le h1 h2
    _ = hsNorm ((x - 1) * z : E →L[ℂ] E) + hsNorm (z * (y - 1) : E →L[ℂ] E) := by rw [hneg]
    _ ≤ ‖x - 1‖ * hsNorm z + hsNorm z * ‖y - 1‖ :=
        add_le_add (hsNorm_comp_left_le hz) (hsNorm_comp_right_le hz)
    _ = (‖x - 1‖ + ‖y - 1‖) * hsNorm z := by ring

end

end GaloisForLFunctions.HTGeometry
