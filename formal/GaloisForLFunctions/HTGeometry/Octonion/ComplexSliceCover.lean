import GaloisForLFunctions.HTGeometry.Octonion.PullbackSpectrum

open scoped Quaternion

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- The imaginary component of a concrete real octonion. -/
def imaginaryPart (x : RealOctonion) : RealOctonion :=
  x - scalarEmbed (realPart x)

theorem real_add_imaginaryPart (x : RealOctonion) :
    scalarEmbed (realPart x) + imaginaryPart x = x := by
  unfold imaginaryPart
  abel

theorem star_imaginaryPart (x : RealOctonion) :
    star (imaginaryPart x) = -imaginaryPart x := by
  unfold imaginaryPart realPart
  rw [star_sub, star_scalarEmbed, star_eq_scalarEmbed_sub]
  have htwo : scalarEmbed (2 * x.1.re) =
      scalarEmbed x.1.re + scalarEmbed x.1.re := by
    rw [← map_add]
    congr 1
    ring
  rw [htwo]
  abel

theorem imaginaryPart_sq (x : RealOctonion) :
    imaginaryPart x * imaginaryPart x = -scalarEmbed (normSq (imaginaryPart x)) := by
  have h := mul_star_self_eq_scalarEmbed (imaginaryPart x)
  rw [star_imaginaryPart, mul_neg] at h
  calc
    imaginaryPart x * imaginaryPart x =
      - (-(imaginaryPart x * imaginaryPart x)) := by abel
    _ = -scalarEmbed (normSq (imaginaryPart x)) := by rw [h]

/-- A fixed imaginary unit, used to place real octonions in a complex slice. -/
def canonicalImaginaryUnit : ImaginaryUnit where
  val := mk (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) 0
  square := by
    apply ext
    · apply Quaternion.ext <;>
        norm_num [mul_fst, Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]
    · norm_num [mul_snd]

/-- The normalized imaginary direction of a non-real octonion. -/
def normalizedImaginaryUnit (x : RealOctonion) : RealOctonion :=
  scalarEmbed ((Real.sqrt (normSq (imaginaryPart x)))⁻¹) * imaginaryPart x

theorem normalizedImaginaryUnit_sq (x : RealOctonion)
    (hx : imaginaryPart x ≠ 0) :
    normalizedImaginaryUnit x * normalizedImaginaryUnit x = -1 := by
  let u := imaginaryPart x
  let t := Real.sqrt (normSq u)
  have hnormne : normSq u ≠ 0 := by
    intro hzero
    exact hx ((normSq_eq_zero u).mp hzero)
  have hnormpos : 0 < normSq u :=
    lt_of_le_of_ne (normSq_nonneg u) (Ne.symm hnormne)
  have ht : t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnormpos)
  have hsq : t ^ (2 : ℕ) = normSq u := Real.sq_sqrt (normSq_nonneg u)
  have hcoeff : t⁻¹ * t⁻¹ * normSq u = 1 := by
    rw [← hsq]
    calc
      t⁻¹ * t⁻¹ * (t ^ (2 : ℕ)) = t⁻¹ * (t⁻¹ * (t * t)) := by
        rw [pow_two, mul_assoc]
      _ = t⁻¹ * ((t⁻¹ * t) * t) := by rw [mul_assoc]
      _ = t⁻¹ * (1 * t) := by rw [inv_mul_cancel₀ ht]
      _ = t⁻¹ * t := by rw [one_mul]
      _ = 1 := inv_mul_cancel₀ ht
  have hmain : (scalarEmbed t⁻¹ * u) * (scalarEmbed t⁻¹ * u) = -1 := by
    calc
      (scalarEmbed t⁻¹ * u) * (scalarEmbed t⁻¹ * u) =
        (t⁻¹ * t⁻¹) • (u * u) := by
          rw [scalarEmbed_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = (t⁻¹ * t⁻¹) • (-scalarEmbed (normSq u)) := by
        rw [show u = imaginaryPart x by rfl, imaginaryPart_sq]
      _ = -scalarEmbed ((t⁻¹ * t⁻¹) * normSq u) := by
        rw [smul_neg]
        congr 1
        calc
          (t⁻¹ * t⁻¹) • scalarEmbed (normSq u) =
              scalarEmbed (t⁻¹ * t⁻¹) * scalarEmbed (normSq u) :=
            (scalarEmbed_mul _ _).symm
          _ = scalarEmbed ((t⁻¹ * t⁻¹) * normSq u) :=
            (map_mul scalarEmbed (t⁻¹ * t⁻¹) (normSq u)).symm
      _ = -1 := by rw [hcoeff, map_one]
  simpa only [normalizedImaginaryUnit, u, t] using hmain

theorem normalizedImaginaryUnit_representation (x : RealOctonion)
    (hx : imaginaryPart x ≠ 0) :
    x = scalarEmbed (realPart x) +
      scalarEmbed (Real.sqrt (normSq (imaginaryPart x))) * normalizedImaginaryUnit x := by
  let u := imaginaryPart x
  let t := Real.sqrt (normSq u)
  have hnormne : normSq u ≠ 0 := by
    intro hzero
    exact hx ((normSq_eq_zero u).mp hzero)
  have hnormpos : 0 < normSq u :=
    lt_of_le_of_ne (normSq_nonneg u) (Ne.symm hnormne)
  have ht : t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnormpos)
  have hprod' : scalarEmbed t * (scalarEmbed t⁻¹ * u) = u := by
    calc
      scalarEmbed t * (scalarEmbed t⁻¹ * u) =
        (scalarEmbed t * scalarEmbed t⁻¹) * u :=
          (scalarEmbed_associates t (scalarEmbed t⁻¹) u).symm
      _ = scalarEmbed (t * t⁻¹) * u := by rw [← map_mul]
      _ = u := by rw [mul_inv_cancel₀ ht, map_one, one_mul]
  have hprod : scalarEmbed t * normalizedImaginaryUnit x = u := by
    simpa only [normalizedImaginaryUnit, u, t] using hprod'
  change x = scalarEmbed (realPart x) + scalarEmbed t * normalizedImaginaryUnit x
  rw [hprod]
  exact (real_add_imaginaryPart x).symm

/-- Every real octonion belongs to a complex slice. -/
theorem exists_complexSliceSubmodule_mem (x : RealOctonion) :
    ∃ J : ImaginaryUnit, x ∈ complexSliceSubmodule J := by
  by_cases hx : imaginaryPart x = 0
  · refine ⟨canonicalImaginaryUnit, x.1.re, 0, ?_⟩
    have hxreal : x = scalarEmbed (realPart x) := by
      calc
        x = scalarEmbed (realPart x) + imaginaryPart x := (real_add_imaginaryPart x).symm
        _ = scalarEmbed (realPart x) + 0 := by rw [hx]
        _ = scalarEmbed (realPart x) := by simp
    change x = scalarEmbed x.1.re + scalarEmbed 0 * canonicalImaginaryUnit.val
    rw [map_zero, zero_mul, add_zero]
    exact hxreal
  · let J : ImaginaryUnit := ⟨normalizedImaginaryUnit x, normalizedImaginaryUnit_sq x hx⟩
    refine ⟨J, realPart x, Real.sqrt (normSq (imaginaryPart x)), ?_⟩
    change x = scalarEmbed (realPart x) +
      scalarEmbed (Real.sqrt (normSq (imaginaryPart x))) * normalizedImaginaryUnit x
    exact normalizedImaginaryUnit_representation x hx

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
