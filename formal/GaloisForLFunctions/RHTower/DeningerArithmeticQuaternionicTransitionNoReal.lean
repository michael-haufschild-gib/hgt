import GaloisForLFunctions.RHTower.DeningerArithmeticRectangularQuaternionicHodge

/-!
# Genuine quaternionic transition atom for Deninger arithmetic cohomology

The untwisted rectangular power maps preserve coordinatewise conjugation, so the local
quaternionic Hodge atom alone still has a real reduction.  This module isolates the smallest
transition algebra that removes it.

Two explicit complex-linear operators on `ℂ × ℂ` generate the standard quaternion-group
representation.  They commute with the rectangular quaternionic Hodge operator at modulus one.
Any anti-linear map commuting with both cannot square to the identity.  Thus this transition
atom is genuinely quaternionic, unconditionally and without spectral-divisor input.
-/

namespace RHTower

noncomputable section

/-- First quaternion transition: diagonal multiplication by `I` and `-I`. -/
def deningerQuaternionTransitionI (v : ℂ × ℂ) : ℂ × ℂ :=
  (Complex.I * v.1, -Complex.I * v.2)

/-- Second quaternion transition: the standard real complex structure. -/
def deningerQuaternionTransitionK (v : ℂ × ℂ) : ℂ × ℂ :=
  (-v.2, v.1)

/-- The first quaternion transition squares to minus the identity. -/
@[simp]
theorem deningerQuaternionTransitionI_sq (v : ℂ × ℂ) :
    deningerQuaternionTransitionI (deningerQuaternionTransitionI v) = -v := by
  rcases v with ⟨z, w⟩
  ext <;> simp [deningerQuaternionTransitionI] <;> ring

/-- The second quaternion transition squares to minus the identity. -/
@[simp]
theorem deningerQuaternionTransitionK_sq (v : ℂ × ℂ) :
    deningerQuaternionTransitionK (deningerQuaternionTransitionK v) = -v := by
  rcases v with ⟨z, w⟩
  ext <;> simp [deningerQuaternionTransitionK]

/-- The two generators anticommute, hence generate quaternion rather than abelian holonomy. -/
theorem deningerQuaternionTransitionI_anticommutes_K (v : ℂ × ℂ) :
    deningerQuaternionTransitionI (deningerQuaternionTransitionK v) =
      -deningerQuaternionTransitionK (deningerQuaternionTransitionI v) := by
  rcases v with ⟨z, w⟩
  ext <;> simp [deningerQuaternionTransitionI, deningerQuaternionTransitionK] <;> ring

/-- Quaternion holonomy preserves the odd rectangular Hodge operator. -/
theorem deningerQuaternionTransitionI_commutes_hodge (v : ℂ × ℂ) :
    deningerQuaternionTransitionI (deningerRectangularQuaternionicHodge 1 v) =
      deningerRectangularQuaternionicHodge 1 (deningerQuaternionTransitionI v) := by
  rcases v with ⟨z, w⟩
  ext <;>
    simp [deningerQuaternionTransitionI, deningerRectangularQuaternionicHodge,
      deningerRectangularComplexJ, deningerRectangularConjugation, map_mul] <;>
    ring

/-- Quaternion holonomy preserves the odd rectangular Hodge operator. -/
theorem deningerQuaternionTransitionK_commutes_hodge (v : ℂ × ℂ) :
    deningerQuaternionTransitionK (deningerRectangularQuaternionicHodge 1 v) =
      deningerRectangularQuaternionicHodge 1 (deningerQuaternionTransitionK v) := by
  rcases v with ⟨z, w⟩
  ext <;>
    simp [deningerQuaternionTransitionK, deningerRectangularQuaternionicHodge,
      deningerRectangularComplexJ, deningerRectangularConjugation]

/-- The quaternion generators preserve the positive rectangular energy at modulus one. -/
theorem deningerQuaternionTransitionI_energy (v : ℂ × ℂ) :
    deningerRectangularComplexEnergy 1 (deningerQuaternionTransitionI v) =
      deningerRectangularComplexEnergy 1 v := by
  rcases v with ⟨z, w⟩
  simp [deningerQuaternionTransitionI, deningerRectangularComplexEnergy,
    Complex.normSq_mul]

/-- The quaternion generators preserve the positive rectangular energy at modulus one. -/
theorem deningerQuaternionTransitionK_energy (v : ℂ × ℂ) :
    deningerRectangularComplexEnergy 1 (deningerQuaternionTransitionK v) =
      deningerRectangularComplexEnergy 1 v := by
  rcases v with ⟨z, w⟩
  simp [deningerQuaternionTransitionK, deningerRectangularComplexEnergy]
  ring

/-- No anti-linear real structure can commute with both quaternion transitions.

Only anti-linearity, equivariance under the two explicit generators, and the putative square-one
law are used.  Additivity or continuity are not needed for the contradiction. -/
theorem deningerQuaternionTransition_no_real_reduction
    (C : (ℂ × ℂ) → (ℂ × ℂ))
    (hanti : ∀ (a : ℂ) (v : ℂ × ℂ),
      C (a • v) = (starRingEnd ℂ) a • C v)
    (hI : ∀ v, C (deningerQuaternionTransitionI v) =
      deningerQuaternionTransitionI (C v))
    (hK : ∀ v, C (deningerQuaternionTransitionK v) =
      deningerQuaternionTransitionK (C v))
    (hsq : ∀ v, C (C v) = v) :
    False := by
  let e₁ : ℂ × ℂ := (1, 0)
  let e₂ : ℂ × ℂ := (0, 1)
  let a : ℂ := (C e₁).1
  let b : ℂ := (C e₁).2
  have hIe := hI e₁
  have hI_smul : deningerQuaternionTransitionI e₁ = Complex.I • e₁ := by
    ext <;> simp [e₁, deningerQuaternionTransitionI]
  rw [hI_smul, hanti] at hIe
  have haeq : -Complex.I * a = Complex.I * a := by
    simpa [a, deningerQuaternionTransitionI] using congrArg Prod.fst hIe
  have hIa : Complex.I * a = 0 := by
    exact neg_eq_self.mp haeq
  have ha : a = 0 := (mul_eq_zero.mp hIa).resolve_left Complex.I_ne_zero
  have hCe₁ : C e₁ = (0, b) := by
    apply Prod.ext
    · exact ha
    · rfl
  have hKe := hK e₁
  have hKe₁ : deningerQuaternionTransitionK e₁ = e₂ := by
    ext <;> simp [e₁, e₂, deningerQuaternionTransitionK]
  rw [hKe₁, hCe₁] at hKe
  have hCe₂ : C e₂ = (-b, 0) := by
    simpa [deningerQuaternionTransitionK] using hKe
  have hbsmul : (0, b) = b • e₂ := by
    ext <;> simp [e₂]
  have hsqe := hsq e₁
  rw [hCe₁, hbsmul, hanti, hCe₂] at hsqe
  have hbad : -((starRingEnd ℂ) b * b) = 1 := by
    simpa [e₁] using congrArg Prod.fst hsqe
  rw [← Complex.normSq_eq_conj_mul_self] at hbad
  have hbadRe := congrArg Complex.re hbad
  simp only [map_neg, Complex.ofReal_re, Complex.one_re] at hbadRe
  nlinarith [Complex.normSq_nonneg b]

end

end RHTower
