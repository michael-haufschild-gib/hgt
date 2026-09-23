import GaloisForLFunctions.HTGeometry.GeometricCDDConstraint
import Mathlib

/-!
# Elastic channel saturation and the physical strip of a geometric CDD phase

Two exact facts about an elastic scattering channel.

*Saturation.*  If an output Hilbert space splits as `H_el ⊕ H_perp` and a norm-preserving map `U`
has a norm-preserving elastic compression `P U i`, then `(1 − P) U i = 0`: no orthogonal output
channel receives any amplitude.  This is `mem_of_norm_orthogonalProjectionOnto_eq` and its channel
form `orthogonalProjectionOnto_orthogonal_eq_zero_of_compression_norm_eq`.

*Unit modulus and pole freedom.*  On the real rapidity axis every geometric CDD factor has modulus
one (`norm_geometricCDDStep_ofReal_eq_one`), so the elastic compression really is norm preserving;
and in the physical strip `0 < Im θ < π` no factor has a pole
(`geometricCDDStep_denom_ne_zero_of_physicalStrip`), so the geometric divisor adds no
physical-strip bound-state pole.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-! ## Saturation of a norm-preserving elastic compression -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Elastic norm saturation.**  A vector whose orthogonal projection onto `K` has the same norm
already lies in `K`. -/
theorem mem_of_norm_orthogonalProjectionOnto_eq (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    {y : H} (h : ‖K.orthogonalProjectionOnto y‖ = ‖y‖) : y ∈ K := by
  have hs := Submodule.norm_sq_eq_add_norm_sq_projection y K
  rw [h] at hs
  have hnn : (0 : ℝ) ≤ ‖Kᗮ.orthogonalProjectionOnto y‖ := norm_nonneg _
  have hz : ‖Kᗮ.orthogonalProjectionOnto y‖ = 0 := by nlinarith
  have hzero : Kᗮ.orthogonalProjectionOnto y = 0 := by
    rwa [norm_eq_zero] at hz
  have hmem : y ∈ Kᗮᗮ := Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hzero
  rwa [Submodule.orthogonal_orthogonal] at hmem

/-- **The channel form of saturation.**  If `U` preserves norms and its compression to `K`
preserves the norm of `x`, then the orthogonal channel receives nothing from `x`. -/
theorem orthogonalProjectionOnto_orthogonal_eq_zero_of_compression_norm_eq
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] {U : H → H} (hU : ∀ z, ‖U z‖ = ‖z‖)
    {x : H} (hx : ‖K.orthogonalProjectionOnto (U x)‖ = ‖x‖) :
    Kᗮ.orthogonalProjectionOnto (U x) = 0 := by
  have hmem : U x ∈ K :=
    mem_of_norm_orthogonalProjectionOnto_eq K (by rw [hx, hU x])
  exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    ((Submodule.orthogonal_orthogonal K).symm ▸ hmem)

/-- **No orthogonal output channel.**  A norm-preserving map with a norm-preserving elastic
compression maps the elastic channel into itself. -/
theorem mapsTo_of_compression_norm_eq (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    {U : H → H} (hU : ∀ z, ‖U z‖ = ‖z‖)
    (hA : ∀ x ∈ K, ‖K.orthogonalProjectionOnto (U x)‖ = ‖x‖) :
    ∀ x ∈ K, U x ∈ K := fun x hx =>
  mem_of_norm_orthogonalProjectionOnto_eq K (by rw [hA x hx, hU x])

/-! ## Unit modulus on the real rapidity axis -/

theorem geometricCDDCrossingCoordinate_ofReal (C theta : ℝ) :
    geometricCDDCrossingCoordinate (C : ℂ) (theta : ℂ)
      = -Complex.I * ((Real.sinh theta / C : ℝ) : ℂ) := by
  rw [geometricCDDCrossingCoordinate, ← Complex.ofReal_sinh]
  push_cast
  ring

/-- On the real rapidity axis every geometric CDD factor has modulus one: the crossing coordinate
is purely imaginary, and `|1 − i s| = |1 + i s|` for real `s`. -/
theorem norm_geometricCDDStep_ofReal_eq_one (q C theta : ℝ) (k : ℕ)
    (hden : 1 + (q : ℂ) ^ k * geometricCDDCrossingCoordinate (C : ℂ) (theta : ℂ) ≠ 0) :
    ‖geometricCDDStep (q : ℂ) (geometricCDDCrossingCoordinate (C : ℂ) (theta : ℂ)) k‖ = 1 := by
  set s : ℝ := q ^ k * (Real.sinh theta / C) with hs
  have hcoord : (q : ℂ) ^ k * geometricCDDCrossingCoordinate (C : ℂ) (theta : ℂ)
      = -Complex.I * (s : ℂ) := by
    rw [geometricCDDCrossingCoordinate_ofReal, hs]
    push_cast
    ring
  have hnum : ‖1 - (-Complex.I * (s : ℂ))‖ = Real.sqrt (1 + s ^ (2 : ℕ)) := by
    have hre : (1 - (-Complex.I * (s : ℂ))).re = 1 := by simp
    have him : (1 - (-Complex.I * (s : ℂ))).im = s := by simp
    rw [Complex.norm_def, Complex.normSq_apply, hre, him]
    congr 1
    ring
  have hden' : ‖1 + (-Complex.I * (s : ℂ))‖ = Real.sqrt (1 + s ^ (2 : ℕ)) := by
    have hre : (1 + (-Complex.I * (s : ℂ))).re = 1 := by simp
    have him : (1 + (-Complex.I * (s : ℂ))).im = -s := by simp
    rw [Complex.norm_def, Complex.normSq_apply, hre, him]
    congr 1
    ring
  have hdenne : (1 : ℂ) + (-Complex.I * (s : ℂ)) ≠ 0 := by
    rw [← hcoord]; exact hden
  rw [geometricCDDStep, hcoord, norm_pow, norm_div, hnum, hden']
  have hpos : 0 < Real.sqrt (1 + s ^ (2 : ℕ)) := by
    apply Real.sqrt_pos.mpr
    positivity
  rw [div_self (ne_of_gt hpos), one_pow]

/-! ## The physical strip carries no geometric pole -/

theorem sinh_im_eq (theta : ℂ) :
    (Complex.sinh theta).im = Real.cosh theta.re * Real.sin theta.im := by
  conv_lhs => rw [← Complex.re_add_im theta]
  rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **No pole in the physical strip.**  The equation `sinh θ = −i·R` with `R > 0` forces
`sin (Im θ) < 0`, which is impossible for `0 < Im θ < π`. -/
theorem sinh_ne_neg_I_mul_of_physicalStrip {R : ℝ} (hR : 0 < R) {theta : ℂ}
    (h1 : 0 < theta.im) (h2 : theta.im < Real.pi) :
    Complex.sinh theta ≠ -Complex.I * (R : ℂ) := by
  intro hcon
  have him : (Complex.sinh theta).im = -R := by
    rw [hcon]; simp
  rw [sinh_im_eq] at him
  have hcosh : 0 < Real.cosh theta.re := Real.cosh_pos _
  have hsin : 0 < Real.sin theta.im := Real.sin_pos_of_pos_of_lt_pi h1 h2
  nlinarith

/-- **The geometric divisor adds no physical-strip pole.**  For `0 < q < 1` and `C > 0` no factor
of the geometric CDD product is singular at a rapidity of the physical strip. -/
theorem geometricCDDStep_denom_ne_zero_of_physicalStrip {q C : ℝ} (hq : 0 < q) (hC : 0 < C)
    (k : ℕ) {theta : ℂ} (h1 : 0 < theta.im) (h2 : theta.im < Real.pi) :
    1 + (q : ℂ) ^ k * geometricCDDCrossingCoordinate (C : ℂ) theta ≠ 0 := by
  intro hcon
  have hqk : (0 : ℝ) < q ^ k := pow_pos hq k
  have hqkC : ((q : ℂ)) ^ k ≠ 0 := by
    simpa using (ne_of_gt hqk)
  have hCC : (C : ℂ) ≠ 0 := by simpa using (ne_of_gt hC)
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [geometricCDDCrossingCoordinate] at hcon
  have hmul : (C : ℂ) + (q : ℂ) ^ k * (-Complex.I * Complex.sinh theta) = 0 := by
    field_simp at hcon
    linear_combination hcon
  have hgoal : Complex.sinh theta * (q : ℂ) ^ k = -Complex.I * (C : ℂ) := by
    linear_combination Complex.I * hmul + (Complex.sinh theta * (q : ℂ) ^ k) * hI
  have hcast : ((C / q ^ k : ℝ) : ℂ) = (C : ℂ) / (q : ℂ) ^ k := by push_cast; ring
  have hsinh : Complex.sinh theta = -Complex.I * ((C / q ^ k : ℝ) : ℂ) := by
    rw [hcast, ← mul_div_assoc, eq_div_iff hqkC]
    exact hgoal
  exact sinh_ne_neg_I_mul_of_physicalStrip (by positivity) h1 h2 hsinh

end

end GaloisForLFunctions.HTGeometry
