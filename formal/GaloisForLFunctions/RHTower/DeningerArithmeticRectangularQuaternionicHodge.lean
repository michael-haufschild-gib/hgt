import GaloisForLFunctions.RHTower.DeningerArithmeticRectangularHalfDensity
import Mathlib.Data.Complex.Basic

/-!
# Rectangular quaternionic Hodge atom for arithmetic cohomology

This module complexifies the moving rectangular weight-one source and constructs its canonical
odd Hodge operator.  For modulus `r`, coefficient conjugation followed by the rectangular complex
structure is anti-linear, squares to `-1`, and preserves the positive rectangular energy.  Moving
the modulus by `q` scales energy by `q`; any real normalization `a` with `a² q = 1` makes the map
unitary.

Everything is local and divisor-free.  No Xi zero, zero location, Weil positivity, or RH premise
occurs.
-/

namespace RHTower

noncomputable section

/-- Coefficient conjugation on the complexified rectangular tangent plane. -/
def deningerRectangularConjugation (v : ℂ × ℂ) : ℂ × ℂ :=
  ((starRingEnd ℂ) v.1, (starRingEnd ℂ) v.2)

/-- Complex-linear extension of the rectangular complex structure. -/
def deningerRectangularComplexJ (r : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (-((r : ℂ) * v.2), v.1 / (r : ℂ))

/-- Odd arithmetic Hodge operator: rectangular complex structure after conjugation. -/
def deningerRectangularQuaternionicHodge (r : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  deningerRectangularComplexJ r (deningerRectangularConjugation v)

/-- Moving-modulus dilation on the complexified tangent plane. -/
def deningerRectangularComplexScale (q : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  ((q : ℂ) * v.1, v.2)

/-- Real rescaling on both complexified tangent coordinates. -/
def deningerRectangularRealRescale (a : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  ((a : ℂ) * v.1, (a : ℂ) * v.2)

/-- Positive rectangular energy on the complexified tangent plane. -/
def deningerRectangularComplexEnergy (r : ℝ) (v : ℂ × ℂ) : ℝ :=
  Complex.normSq v.1 / r + r * Complex.normSq v.2

/-- A centered moving-modulus map.  The unitary condition is `a² * q = 1`. -/
def deningerRectangularCenteredScale (a q : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  deningerRectangularRealRescale a (deningerRectangularComplexScale q v)

/-- Coordinatewise conjugation is a real structure on the local rectangular atom. -/
@[simp]
theorem deningerRectangularConjugation_sq (v : ℂ × ℂ) :
    deningerRectangularConjugation (deningerRectangularConjugation v) = v := by
  rcases v with ⟨z, w⟩
  ext <;> simp [deningerRectangularConjugation]

/-- Coordinatewise conjugation is anti-linear. -/
theorem deningerRectangularConjugation_smul
    (a : ℂ) (v : ℂ × ℂ) :
    deningerRectangularConjugation (a • v) =
      (starRingEnd ℂ) a • deningerRectangularConjugation v := by
  rcases v with ⟨z, w⟩
  ext <;> simp [deningerRectangularConjugation, map_mul]

/-- Untwisted moving-modulus maps preserve the local real structure. -/
theorem deningerRectangularComplexScale_intertwines_conjugation
    (q : ℝ) (v : ℂ × ℂ) :
    deningerRectangularComplexScale q (deningerRectangularConjugation v) =
      deningerRectangularConjugation (deningerRectangularComplexScale q v) := by
  rcases v with ⟨z, w⟩
  ext <;>
    simp [deningerRectangularComplexScale, deningerRectangularConjugation,
      map_mul, Complex.conj_ofReal]

/-- Every real-centered moving-modulus map still preserves the local real structure. -/
theorem deningerRectangularCenteredScale_intertwines_conjugation
    (a q : ℝ) (v : ℂ × ℂ) :
    deningerRectangularCenteredScale a q (deningerRectangularConjugation v) =
      deningerRectangularConjugation (deningerRectangularCenteredScale a q v) := by
  rcases v with ⟨z, w⟩
  ext <;>
    simp [deningerRectangularCenteredScale, deningerRectangularRealRescale,
      deningerRectangularComplexScale, deningerRectangularConjugation,
      map_mul, Complex.conj_ofReal]

/-- The complexified rectangular endomorphism still squares to `-1`. -/
@[simp]
theorem deningerRectangularComplexJ_sq
    {r : ℝ} (hr : r ≠ 0) (v : ℂ × ℂ) :
    deningerRectangularComplexJ r (deningerRectangularComplexJ r v) = -v := by
  rcases v with ⟨z, w⟩
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  ext <;> simp only [deningerRectangularComplexJ, Prod.neg_mk] <;>
    field_simp [hrc]

/-- The local arithmetic Hodge operator is genuinely quaternionic. -/
@[simp]
theorem deningerRectangularQuaternionicHodge_sq
    {r : ℝ} (hr : r ≠ 0) (v : ℂ × ℂ) :
    deningerRectangularQuaternionicHodge r
        (deningerRectangularQuaternionicHodge r v) = -v := by
  rcases v with ⟨z, w⟩
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  ext
  · simp only [deningerRectangularQuaternionicHodge, deningerRectangularComplexJ,
      deningerRectangularConjugation, Prod.neg_mk, map_neg, map_mul,
      Complex.conj_ofReal, starRingEnd_self_apply]
    rw [map_div₀]
    simp only [Complex.conj_ofReal, starRingEnd_self_apply]
    field_simp [hrc]
  · simp only [deningerRectangularQuaternionicHodge, deningerRectangularComplexJ,
      deningerRectangularConjugation, Prod.neg_mk, map_neg, map_mul,
      Complex.conj_ofReal, starRingEnd_self_apply]
    field_simp [hrc]

/-- Exact anti-linearity of the local arithmetic Hodge operator. -/
theorem deningerRectangularQuaternionicHodge_smul
    (r : ℝ) (a : ℂ) (v : ℂ × ℂ) :
    deningerRectangularQuaternionicHodge r (a • v) =
      (starRingEnd ℂ) a • deningerRectangularQuaternionicHodge r v := by
  rcases v with ⟨z, w⟩
  ext <;>
    simp only [deningerRectangularQuaternionicHodge, deningerRectangularComplexJ,
      deningerRectangularConjugation, Prod.smul_mk, smul_eq_mul, map_mul] <;>
    ring

/-- The rectangular energy is strictly positive away from zero. -/
theorem deningerRectangularComplexEnergy_pos
    {r : ℝ} (hr : 0 < r) {v : ℂ × ℂ} (hv : v ≠ 0) :
    0 < deningerRectangularComplexEnergy r v := by
  rcases v with ⟨z, w⟩
  by_cases hz : z = 0
  · have hw : w ≠ 0 := by
      intro hw
      apply hv
      simp [hz, hw]
    simp [deningerRectangularComplexEnergy, hz]
    exact mul_pos hr (Complex.normSq_pos.mpr hw)
  · have hzpos : 0 < Complex.normSq z / r :=
      div_pos (Complex.normSq_pos.mpr hz) hr
    have hwnonneg : 0 ≤ r * Complex.normSq w :=
      mul_nonneg hr.le (Complex.normSq_nonneg w)
    simp only [deningerRectangularComplexEnergy]
    linarith

/-- The odd Hodge operator preserves the local positive energy. -/
theorem deningerRectangularQuaternionicHodge_energy
    {r : ℝ} (hr : r ≠ 0) (v : ℂ × ℂ) :
    deningerRectangularComplexEnergy r
        (deningerRectangularQuaternionicHodge r v) =
      deningerRectangularComplexEnergy r v := by
  rcases v with ⟨z, w⟩
  simp only [deningerRectangularQuaternionicHodge, deningerRectangularComplexJ,
    deningerRectangularConjugation, deningerRectangularComplexEnergy]
  rw [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_conj, Complex.normSq_div, Complex.normSq_conj,
    Complex.normSq_ofReal]
  field_simp
  ring

/-- Moving the modulus intertwines the local quaternionic Hodge operators. -/
theorem deningerRectangularComplexScale_intertwines_hodge
    {q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0) (v : ℂ × ℂ) :
    deningerRectangularComplexScale q
        (deningerRectangularQuaternionicHodge r v) =
      deningerRectangularQuaternionicHodge (q * r)
        (deningerRectangularComplexScale q v) := by
  rcases v with ⟨z, w⟩
  have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  ext <;>
    simp only [deningerRectangularComplexScale, deningerRectangularQuaternionicHodge,
      deningerRectangularComplexJ, deningerRectangularConjugation, map_mul,
      Complex.conj_ofReal, Complex.ofReal_mul] <;>
    field_simp [hqc, hrc]

/-- Exact weight-one law for the complexified rectangular energy. -/
theorem deningerRectangularComplexEnergy_scale
    {q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0) (v : ℂ × ℂ) :
    deningerRectangularComplexEnergy (q * r)
        (deningerRectangularComplexScale q v) =
      q * deningerRectangularComplexEnergy r v := by
  rcases v with ⟨z, w⟩
  simp only [deningerRectangularComplexEnergy, deningerRectangularComplexScale]
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  field_simp

/-- Real scalar rescaling changes energy by its square. -/
theorem deningerRectangularComplexEnergy_realRescale
    (r a : ℝ) (v : ℂ × ℂ) :
    deningerRectangularComplexEnergy r
        (deningerRectangularRealRescale a v) =
      a ^ (2 : ℕ) * deningerRectangularComplexEnergy r v := by
  rcases v with ⟨z, w⟩
  simp only [deningerRectangularComplexEnergy, deningerRectangularRealRescale]
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- Centering by any `a` satisfying `a² q = 1` makes the prime map unitary. -/
theorem deningerRectangularCenteredScale_energy
    {a q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hnorm : a ^ (2 : ℕ) * q = 1) (v : ℂ × ℂ) :
    deningerRectangularComplexEnergy (q * r)
        (deningerRectangularCenteredScale a q v) =
      deningerRectangularComplexEnergy r v := by
  rw [deningerRectangularCenteredScale,
    deningerRectangularComplexEnergy_realRescale,
    deningerRectangularComplexEnergy_scale hq hr]
  calc
    a ^ (2 : ℕ) * (q * deningerRectangularComplexEnergy r v) =
        (a ^ (2 : ℕ) * q) * deningerRectangularComplexEnergy r v := by ring
    _ = deningerRectangularComplexEnergy r v := by rw [hnorm, one_mul]

/-- Every real-centered prime map remains a Hodge intertwiner. -/
theorem deningerRectangularCenteredScale_intertwines_hodge
    {a q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0) (v : ℂ × ℂ) :
    deningerRectangularCenteredScale a q
        (deningerRectangularQuaternionicHodge r v) =
      deningerRectangularQuaternionicHodge (q * r)
        (deningerRectangularCenteredScale a q v) := by
  rcases v with ⟨z, w⟩
  have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  ext <;>
    simp only [deningerRectangularCenteredScale, deningerRectangularRealRescale,
      deningerRectangularComplexScale, deningerRectangularQuaternionicHodge,
      deningerRectangularComplexJ, deningerRectangularConjugation, map_mul,
      Complex.conj_ofReal, Complex.ofReal_mul] <;>
    field_simp [hqc, hrc]

/-- Centered moving-modulus maps retain the multiplicative semigroup law. -/
@[simp]
theorem deningerRectangularCenteredScale_mul
    (a₁ q₁ a₂ q₂ : ℝ) (v : ℂ × ℂ) :
    deningerRectangularCenteredScale a₁ q₁
        (deningerRectangularCenteredScale a₂ q₂ v) =
      deningerRectangularCenteredScale (a₁ * a₂) (q₁ * q₂) v := by
  rcases v with ⟨z, w⟩
  ext <;>
    simp only [deningerRectangularCenteredScale, deningerRectangularRealRescale,
      deningerRectangularComplexScale, Complex.ofReal_mul] <;>
    ring

/-- The canonical centering `U_q = q^{-1/2} A_q` of a moving-modulus map. -/
def deningerRectangularUnitaryScale (q : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  deningerRectangularCenteredScale (Real.sqrt q)⁻¹ q v

/-- The canonical centering satisfies the unitary normalization. -/
theorem deningerRectangularUnitaryScale_norm {q : ℝ} (hq : 0 < q) :
    ((Real.sqrt q)⁻¹) ^ (2 : ℕ) * q = 1 := by
  have hsq : (Real.sqrt q) ^ (2 : ℕ) = q := Real.sq_sqrt (le_of_lt hq)
  have hne : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  field_simp
  exact hsq.symm

/-- **The centered prime map is unitary.** -/
theorem deningerRectangularUnitaryScale_energy {q r : ℝ} (hq : 0 < q) (hr : r ≠ 0) (v : ℂ × ℂ) :
    deningerRectangularComplexEnergy (q * r) (deningerRectangularUnitaryScale q v) =
      deningerRectangularComplexEnergy r v :=
  deningerRectangularCenteredScale_energy (ne_of_gt hq) hr
    (deningerRectangularUnitaryScale_norm hq) v

/-- **The centered prime map is a Hodge intertwiner.** -/
theorem deningerRectangularUnitaryScale_intertwines_hodge {q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0)
    (v : ℂ × ℂ) :
    deningerRectangularUnitaryScale q (deningerRectangularQuaternionicHodge r v) =
      deningerRectangularQuaternionicHodge (q * r) (deningerRectangularUnitaryScale q v) :=
  deningerRectangularCenteredScale_intertwines_hodge hq hr v

/-- **The centered prime maps compose**: `U_{q₁} U_{q₂} = U_{q₁q₂}`, by the positive square-root
law. -/
theorem deningerRectangularUnitaryScale_mul {q₁ q₂ : ℝ} (h₁ : 0 ≤ q₁) (v : ℂ × ℂ) :
    deningerRectangularUnitaryScale q₁ (deningerRectangularUnitaryScale q₂ v) =
      deningerRectangularUnitaryScale (q₁ * q₂) v := by
  rw [deningerRectangularUnitaryScale, deningerRectangularUnitaryScale,
    deningerRectangularCenteredScale_mul, deningerRectangularUnitaryScale]
  congr 1
  rw [Real.sqrt_mul h₁, mul_inv]

end

end RHTower
