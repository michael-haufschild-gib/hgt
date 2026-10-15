import GaloisForLFunctions.HTGeometry.QuantumLaurentTraceIntegrality

/-!
# Central scalar structure of the quantum Laurent division ring

The ground field embeds centrally in both Laurent degrees zero. This gives
an actual algebra structure, exact multiplication of ordered quantum words,
and linearity of the coefficient trace. These constructions support the
comparison with finite Weyl operators in the concrete rotation algebra.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped Classical
variable {F : Type*} [Field F]

private theorem scale_zpow (c : Fˣ) (n : ℤ) (f : HahnSeries ℤ F) :
    (quantumLaurentScaleAut c ^ n) f = quantumLaurentScaleSeries (c ^ n) f := by
  change (quantumLaurentScaleHom c ^ n) f = _
  rw [← map_zpow]
  rfl

theorem quantumLaurentScaleAut_zpow_single (c : Fˣ) (n b : ℤ) (z : F) :
    (quantumLaurentScaleAut c ^ n) (HahnSeries.single b z) =
      HahnSeries.single b ((↑(c ^ (n * b)) : F) * z) := by
  rw [scale_zpow]
  ext k
  by_cases hk : k = b
  · subst k
    simp [quantumLaurentScaleSeries_coeff, ← zpow_mul]
  · simp [quantumLaurentScaleSeries_coeff, hk]

/-- The ground field is included in both Laurent degrees zero. -/
def quantumLaurentScalar (c : Fˣ) : F →+* QuantumLaurentDivisionRing c :=
  (skewLaurentConstant (quantumLaurentScaleAut c)).comp (HahnSeries.C (Γ := ℤ) (R := F))

private theorem scalar_commutes (c : Fˣ) (z : F) (f : QuantumLaurentDivisionRing c) :
    quantumLaurentScalar c z * f = f * quantumLaurentScalar c z := by
  apply Subtype.ext
  apply HahnSeries.ext
  funext n
  change (HahnSeries.single 0 (skewLaurentCoefficient (quantumLaurentScaleAut c) 0
      (HahnSeries.single 0 z)) * f.val).coeff n =
    (f.val * HahnSeries.single 0 (skewLaurentCoefficient (quantumLaurentScaleAut c) 0
      (HahnSeries.single 0 z))).coeff n
  rw [HahnSeries.coeff_single_zero_mul, HahnSeries.coeff_mul_single_zero,
    ← skewLaurentCoefficient_normalForm (quantumLaurentScaleAut c) f n,
    skewLaurentCoefficient_mul, skewLaurentCoefficient_mul,
    zero_add, add_zero, zpow_zero, RingAut.one_apply,
    quantumLaurentScaleAut_zpow_single]
  simp only [mul_zero, zpow_zero, Units.val_one, one_mul]
  rw [mul_comm]

instance quantumLaurentDivisionRing_algebra (c : Fˣ) :
    Algebra F (QuantumLaurentDivisionRing c) :=
  (quantumLaurentScalar c).toAlgebra' (scalar_commutes c)

@[simp] theorem quantumLaurentScalar_eq_algebraMap (c : Fˣ) (z : F) :
    quantumLaurentScalar c z = algebraMap F (QuantumLaurentDivisionRing c) z := rfl

theorem quantumLaurent_smul_monomial (c : Fˣ) (z : F) (a : ℤ) (f : HahnSeries ℤ F) :
    z • skewLaurentMonomial (quantumLaurentScaleAut c) a f =
      skewLaurentMonomial (quantumLaurentScaleAut c) a (HahnSeries.single 0 z * f) := by
  change skewLaurentMonomial (quantumLaurentScaleAut c) 0 (HahnSeries.single 0 z) * _ = _
  rw [skewLaurentMonomial_mul]
  simp

/-- Exact multiplication in the same ordered normal form as the concrete Weyl words. -/
theorem quantumLaurentWord_mul (c : Fˣ) (a b d e : ℤ) :
    quantumLaurentWord c a b * quantumLaurentWord c d e =
      (↑(c ^ (a * e)) : F) • quantumLaurentWord c (a + d) (b + e) := by
  unfold quantumLaurentWord
  rw [skewLaurentMonomial_mul, quantumLaurentScaleAut_zpow_single,
    quantumLaurent_smul_monomial, HahnSeries.single_mul_single,
    HahnSeries.single_mul_single]
  simp

@[simp] theorem quantumLaurentWord_zero (c : Fˣ) : quantumLaurentWord c 0 0 = 1 := by
  change skewLaurentMonomial _ 0 (HahnSeries.single 0 1) = 1
  simp [skewLaurentMonomial_zero_one]

theorem quantumLaurentTrace_smul (c : Fˣ) (z : F) (f : QuantumLaurentDivisionRing c) :
    quantumLaurentTrace c (z • f) = z • quantumLaurentTrace c f := by
  change (((HahnSeries.single 0 (skewLaurentCoefficient (quantumLaurentScaleAut c) 0
      (HahnSeries.single 0 z))) * f.val).coeff 0 1).coeff 0 = _
  rw [HahnSeries.coeff_single_zero_mul]
  change (HahnSeries.single 0 z * f.val.coeff 0 1).coeff 0 = _
  rw [HahnSeries.coeff_single_zero_mul]
  rfl

/-- The coefficient trace is linear over the ground field. -/
def quantumLaurentTraceLinear (c : Fˣ) : QuantumLaurentDivisionRing c →ₗ[F] F :=
  { quantumLaurentTrace c with map_smul' := quantumLaurentTrace_smul c }

end
end GaloisForLFunctions.HTGeometry
