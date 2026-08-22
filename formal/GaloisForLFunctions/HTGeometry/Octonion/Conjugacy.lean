import GaloisForLFunctions.HTGeometry.Octonion.RestrictedInverse

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

set_option maxHeartbeats 400000

/-- Real part of a concrete Cayley octonion. -/
def realPart (x : RealOctonion) : ℝ := x.1.re

/-- Squared Euclidean length of the imaginary part of a concrete Cayley octonion. -/
def imaginaryNormSq (x : RealOctonion) : ℝ :=
  x.1.imI ^ 2 + x.1.imJ ^ 2 + x.1.imK ^ 2 + Quaternion.normSq x.2

theorem realPart_scalarEmbed (r : ℝ) : realPart (scalarEmbed r) = r := by
  simp [realPart, scalarEmbed]

theorem normSq_eq_realPart_sq_add_imaginaryNormSq (x : RealOctonion) :
    normSq x = realPart x ^ 2 + imaginaryNormSq x := by
  unfold realPart imaginaryNormSq
  rw [normSq_eq_quaternion_normSq, Quaternion.normSq_def']
  ring

theorem imaginaryNormSq_nonneg (x : RealOctonion) : 0 ≤ imaginaryNormSq x := by
  unfold imaginaryNormSq
  exact add_nonneg
    (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
    Quaternion.normSq_nonneg

/-- The equality of real part and norm-square characterizing an octonionic conjugacy sphere. -/
def sameConjugacySphere (s q : RealOctonion) : Prop :=
  realPart s = realPart q ∧ normSq s = normSq q

/-- The conjugacy sphere `[q]` used in the source paper, expressed using squared imaginary norm. -/
def conjugacySphere (q : RealOctonion) : Set RealOctonion :=
  {s | realPart s = realPart q ∧ imaginaryNormSq s = imaginaryNormSq q}

theorem sameConjugacySphere_iff_mem_conjugacySphere (s q : RealOctonion) :
    sameConjugacySphere s q ↔ s ∈ conjugacySphere q := by
  constructor
  · rintro ⟨hre, hnorm⟩
    constructor
    · exact hre
    · have hs := normSq_eq_realPart_sq_add_imaginaryNormSq s
      have hq := normSq_eq_realPart_sq_add_imaginaryNormSq q
      calc
        imaginaryNormSq s = normSq s - realPart s ^ 2 := by linarith
        _ = normSq q - realPart q ^ 2 := by rw [hnorm, hre]
        _ = imaginaryNormSq q := by linarith
  · rintro ⟨hre, him⟩
    constructor
    · exact hre
    · have hs := normSq_eq_realPart_sq_add_imaginaryNormSq s
      have hq := normSq_eq_realPart_sq_add_imaginaryNormSq q
      calc
        normSq s = realPart s ^ 2 + imaginaryNormSq s := hs
        _ = realPart q ^ 2 + imaginaryNormSq q := by rw [hre, him]
        _ = normSq q := hq.symm

theorem quadratic_of_scalarEmbed (s : RealOctonion) (r : ℝ) :
    quadratic s (scalarEmbed r) =
      scalarEmbed (r ^ 2 - 2 * s.1.re * r + normSq s) := by
  unfold quadratic
  rw [← map_mul, ← map_mul, ← map_sub, ← map_add]
  congr 1
  ring

theorem scalarEmbed_injective : Function.Injective scalarEmbed := by
  intro r t h
  have hre := congrArg (fun x : RealOctonion => x.1.re) h
  simpa [scalarEmbed] using hre

theorem normSq_scalarEmbed (r : ℝ) : normSq (scalarEmbed r) = r ^ 2 := by
  rw [normSq_eq_quaternion_normSq]
  simp [scalarEmbed, Quaternion.normSq_coe]

theorem quadratic_decomposition (s q : RealOctonion) :
    quadratic s q =
      (q * q - scalarEmbed (2 * q.1.re) * q + scalarEmbed (normSq q)) +
        scalarEmbed (2 * (q.1.re - s.1.re)) * q +
          scalarEmbed (normSq s - normSq q) := by
  unfold quadratic
  have hcoeff : scalarEmbed (2 * s.1.re) =
      scalarEmbed (2 * q.1.re) - scalarEmbed (2 * (q.1.re - s.1.re)) := by
    rw [← map_sub]
    congr 1
    ring
  have hnorm : scalarEmbed (normSq s) =
      scalarEmbed (normSq q) + scalarEmbed (normSq s - normSq q) := by
    rw [← map_add]
    congr 1
    ring
  rw [hcoeff, hnorm, sub_mul]
  abel

theorem scalar_relation_of_quadratic_eq_zero (s q : RealOctonion) (h : quadratic s q = 0) :
    scalarEmbed (2 * (q.1.re - s.1.re)) * q +
      scalarEmbed (normSq s - normSq q) = 0 := by
  rw [quadratic_decomposition, quadratic_characteristic] at h
  simpa using h

theorem eq_scalarEmbed_of_scalar_linear_relation (a b : ℝ) (q : RealOctonion)
    (hlin : scalarEmbed a * q + scalarEmbed b = 0) (ha : a ≠ 0) :
    q = scalarEmbed (-(a⁻¹) * b) := by
  have hprod : scalarEmbed a * q = -scalarEmbed b := eq_neg_of_add_eq_zero_left hlin
  calc
    q = scalarEmbed 1 * q := by rw [map_one, one_mul]
    _ = (scalarEmbed a⁻¹ * scalarEmbed a) * q := by
      rw [← map_mul, inv_mul_cancel₀ ha, map_one]
    _ = scalarEmbed a⁻¹ * (scalarEmbed a * q) :=
      scalarEmbed_associates a⁻¹ (scalarEmbed a) q
    _ = scalarEmbed a⁻¹ * (-scalarEmbed b) := by rw [hprod]
    _ = scalarEmbed (-(a⁻¹) * b) := by
      rw [mul_neg, ← map_mul, ← map_neg]
      congr 1
      ring

set_option maxHeartbeats 800000 in
theorem quadratic_eq_zero_iff_sameConjugacySphere (s q : RealOctonion) :
    quadratic s q = 0 ↔ sameConjugacySphere s q := by
  constructor
  · intro hzero
    have hlin := scalar_relation_of_quadratic_eq_zero s q hzero
    by_cases hdiff : q.1.re - s.1.re = 0
    · constructor
      · unfold realPart
        linarith
      · have hscalar : scalarEmbed (normSq s - normSq q) = 0 := by
          rw [show 2 * (q.1.re - s.1.re) = 0 by rw [hdiff]; ring] at hlin
          simpa using hlin
        have hnorm : normSq s - normSq q = 0 :=
          scalarEmbed_injective (by simpa using hscalar)
        linarith
    · have hcoeff : 2 * (q.1.re - s.1.re) ≠ 0 :=
        mul_ne_zero (by norm_num) hdiff
      have hqscalar := eq_scalarEmbed_of_scalar_linear_relation
        (2 * (q.1.re - s.1.re)) (normSq s - normSq q) q hlin hcoeff
      have hreal : quadratic s q =
          scalarEmbed ((-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q)) ^ 2 -
            2 * s.1.re * (-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q)) + normSq s) := by
        calc
          quadratic s q = quadratic s
              (scalarEmbed (-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q))) := by
                conv_lhs => rw [hqscalar]
          _ = scalarEmbed ((-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q)) ^ 2 -
              2 * s.1.re * (-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q)) + normSq s) :=
                quadratic_of_scalarEmbed s _
      rw [hreal] at hzero
      have hpoly : (-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q)) ^ 2 -
          2 * s.1.re * (-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q)) + normSq s = 0 :=
        scalarEmbed_injective (by simpa using hzero)
      have hdecomp := normSq_eq_realPart_sq_add_imaginaryNormSq s
      change normSq s = s.1.re ^ 2 + imaginaryNormSq s at hdecomp
      have hsum :
          (-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q) - s.1.re) ^ 2 +
            imaginaryNormSq s = 0 := by
        nlinarith [hpoly, hdecomp]
      have hparts := (add_eq_zero_iff_of_nonneg (sq_nonneg _)
        (imaginaryNormSq_nonneg s)).mp hsum
      have hr : -(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q) = s.1.re :=
        sub_eq_zero.mp (sq_eq_zero_iff.mp hparts.1)
      have hqre : q.1.re = -(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q) := by
        have hrealpart := congrArg realPart hqscalar
        change q.1.re = realPart
          (scalarEmbed (-(2 * (q.1.re - s.1.re))⁻¹ * (normSq s - normSq q))) at hrealpart
        rw [realPart_scalarEmbed] at hrealpart
        exact hrealpart
      have hreq : q.1.re = s.1.re := by rw [hqre, hr]
      exfalso
      apply hdiff
      rw [hreq]
      ring
  · rintro ⟨hre, hnorm⟩
    unfold realPart at hre
    unfold quadratic
    rw [hre, hnorm]
    exact quadratic_characteristic q

/-- The source-paper conjugacy sphere is exactly the zero locus of `Q_s(q)`. -/
theorem mem_conjugacySphere_iff_quadratic_eq_zero (s q : RealOctonion) :
    s ∈ conjugacySphere q ↔ quadratic s q = 0 := by
  rw [← sameConjugacySphere_iff_mem_conjugacySphere,
    ← quadratic_eq_zero_iff_sameConjugacySphere]

theorem quadratic_ne_zero_of_not_mem_conjugacySphere (s q : RealOctonion)
    (h : s ∉ conjugacySphere q) : quadratic s q ≠ 0 := by
  intro hzero
  exact h ((mem_conjugacySphere_iff_quadratic_eq_zero s q).mpr hzero)

/-- Lemma 8.6 equation (8.7): the stated candidate is a two-sided inverse on the
two-generated associative subalgebra whenever `s` lies off the conjugacy sphere of `q`. -/
theorem restricted_resolvent_inverse_of_not_mem_conjugacySphere (s q : RealOctonion)
    (h : s ∉ conjugacySphere q) :
    restrictedResolvent s q ∘
      restrictedResolventInverseMap s q (quadratic_ne_zero_of_not_mem_conjugacySphere s q h) = id ∧
    restrictedResolventInverseMap s q (quadratic_ne_zero_of_not_mem_conjugacySphere s q h) ∘
      restrictedResolvent s q = id := by
  constructor
  · exact restrictedResolvent_comp_restrictedResolventInverse s q
      (quadratic_ne_zero_of_not_mem_conjugacySphere s q h)
  · exact restrictedResolventInverse_comp_restrictedResolvent s q
      (quadratic_ne_zero_of_not_mem_conjugacySphere s q h)

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
