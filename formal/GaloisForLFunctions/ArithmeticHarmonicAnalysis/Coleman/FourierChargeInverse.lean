import GaloisForLFunctions.HTGeometry.CoppoFourierCircuit

/-!
# Inverting invariant differentiation on the Fourier core

The finite-support analogue of Goto–Ishii, Lemma 4.3(iii), is division
by frequency. For the existing Josephson charge operator, the sole
obstruction is the constant mode. An explicit inverse recovers every
other mode and classifies both the kernel and the solvability condition.
-/

noncomputable section
namespace HTGeometry

/-- Projection onto the constant Fourier mode. -/
def coppoFourierZeroMode : CoppoFourierEnd where
  toFun f := Finsupp.single 0 (f 0)
  map_add' f g := by simp
  map_smul' c f := by simp

/-- Frequency division, with the constant mode sent to zero. -/
def coppoFourierChargeInverse : CoppoFourierEnd :=
  Finsupp.linearCombination ℂ (fun n : ℤ => (n : ℂ)⁻¹ • Finsupp.single n 1)

@[simp] theorem coppoFourierChargeInverse_basis (n : ℤ) :
    coppoFourierChargeInverse (Finsupp.single n 1) =
      (n : ℂ)⁻¹ • Finsupp.single n 1 := by
  simp [coppoFourierChargeInverse]

/-- Differentiation after frequency division deletes exactly the constant mode. -/
theorem coppoFourierCharge_mul_inverse :
    coppoFourierCharge * coppoFourierChargeInverse = 1 - coppoFourierZeroMode := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [Module.End.mul_apply, coppoFourierChargeInverse_basis,
    map_smul, coppoFourierCharge_basis, smul_smul]
  by_cases hn : n = 0
  · subst n
    simp [coppoFourierZeroMode]
  · have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp [LinearMap.sub_apply, coppoFourierZeroMode, hc, hn]

/-- Frequency division is also a left inverse modulo the constant mode. -/
theorem coppoFourierChargeInverse_mul :
    coppoFourierChargeInverse * coppoFourierCharge = 1 - coppoFourierZeroMode := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [Module.End.mul_apply, coppoFourierCharge_basis,
    map_smul, coppoFourierChargeInverse_basis, smul_smul]
  by_cases hn : n = 0
  · subst n
    simp [coppoFourierZeroMode]
  · have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp [LinearMap.sub_apply, coppoFourierZeroMode, hc, hn]

private theorem zeroMode_mul_charge : coppoFourierZeroMode * coppoFourierCharge = 0 := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  by_cases hn : n = 0
  · subst n
    simp [Module.End.mul_apply]
  · simp [Module.End.mul_apply, coppoFourierZeroMode, hn]

/-- The charge equation is solvable exactly when the constant coefficient vanishes. -/
theorem coppoFourierCharge_solvable_iff (f : CoppoFourierCore) :
    (∃ g, coppoFourierCharge g = f) ↔ f 0 = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    have h := congrArg (fun A : CoppoFourierEnd => A g 0) zeroMode_mul_charge
    simpa [Module.End.mul_apply, coppoFourierZeroMode] using h
  · intro hf
    refine ⟨coppoFourierChargeInverse f, ?_⟩
    have h := congrArg (fun A : CoppoFourierEnd => A f) coppoFourierCharge_mul_inverse
    simpa [Module.End.mul_apply, coppoFourierZeroMode, hf] using h

/-- The kernel consists precisely of constant Fourier modes. -/
theorem coppoFourierCharge_eq_zero_iff (f : CoppoFourierCore) :
    coppoFourierCharge f = 0 ↔ f = Finsupp.single 0 (f 0) := by
  constructor
  · intro hf
    have h := congrArg (fun A : CoppoFourierEnd => A f) coppoFourierChargeInverse_mul
    have hz : f - Finsupp.single 0 (f 0) = 0 := by
      simpa [Module.End.mul_apply, coppoFourierZeroMode, hf] using h.symm
    exact sub_eq_zero.mp hz
  · intro hf
    rw [hf]
    simp [coppoFourierCharge]

end HTGeometry

#print axioms HTGeometry.coppoFourierCharge_mul_inverse
#print axioms HTGeometry.coppoFourierCharge_solvable_iff
#print axioms HTGeometry.coppoFourierCharge_eq_zero_iff
