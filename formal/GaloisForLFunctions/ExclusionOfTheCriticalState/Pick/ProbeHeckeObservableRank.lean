import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeHeckeSpecialization

/-!
# Exact rank jumps of polynomial Hecke observables

The two reflection sectors give an explicit generalized inverse for every
polynomial in the actual Hecke action. A sector survives exactly when its
polynomial value is nonzero. This identifies the full image and kernel,
and counts every specialization rank jump without genericity assumptions.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open _root_.Polynomial
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

/-- Retain exactly the reflection sectors on which the observable does not vanish. -/
def hullHeckeSupport (q : ℂ) (f : _root_.Polynomial ℂ) : Module.End ℂ (reflectionHull p) :=
  (if f.eval (q ^ 2) = 0 then (0 : ℂ) else 1) • hullPositive p +
    (if f.eval (-1) = 0 then (0 : ℂ) else 1) • hullNegative p

/-- Reciprocal values on the surviving sectors, and zero on the killed sectors. -/
def hullHeckeReciprocal (q : ℂ) (f : _root_.Polynomial ℂ) : Module.End ℂ (reflectionHull p) :=
  (f.eval (q ^ 2))⁻¹ • hullPositive p + (f.eval (-1))⁻¹ • hullNegative p

/-- The polynomial observable and its reciprocal multiply to the same support projection. -/
theorem hullHecke_reciprocal_products (q : ℂ) (f : _root_.Polynomial ℂ) :
    aeval (hullHecke p q) f * hullHeckeReciprocal p q f = hullHeckeSupport p q f ∧
      hullHeckeReciprocal p q f * aeval (hullHecke p q) f = hullHeckeSupport p q f := by
  have hp : hullPositive p * hullPositive p = hullPositive p := hullPositive_idempotent p
  have hn : hullNegative p * hullNegative p = hullNegative p := hullNegative_idempotent p
  simp only [hullHecke_polynomial, hullHeckeReciprocal, hullHeckeSupport,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    hullPositive_mul_hullNegative, hullNegative_mul_hullPositive, hp, hn,
    smul_zero, add_zero, zero_add]
  by_cases ha : f.eval (q ^ 2) = 0 <;> by_cases hb : f.eval (-1) = 0 <;>
    simp only [ha, hb, if_pos, if_neg, inv_zero, zero_mul, mul_zero,
      mul_inv_cancel₀, inv_mul_cancel₀, zero_smul, one_smul, and_self]

/-- The support projection acts identically on the observable from either side. -/
theorem hullHecke_support_absorbs (q : ℂ) (f : _root_.Polynomial ℂ) :
    hullHeckeSupport p q f * aeval (hullHecke p q) f = aeval (hullHecke p q) f ∧
      aeval (hullHecke p q) f * hullHeckeSupport p q f = aeval (hullHecke p q) f := by
  have hp : hullPositive p * hullPositive p = hullPositive p := hullPositive_idempotent p
  have hn : hullNegative p * hullNegative p = hullNegative p := hullNegative_idempotent p
  simp only [hullHecke_polynomial, hullHeckeSupport, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    hullPositive_mul_hullNegative, hullNegative_mul_hullPositive, hp, hn,
    smul_zero, add_zero, zero_add]
  by_cases ha : f.eval (q ^ 2) = 0 <;> by_cases hb : f.eval (-1) = 0 <;>
    simp only [ha, hb, if_pos, if_neg, zero_mul, mul_zero, one_mul, mul_one,
      zero_smul, and_self]

/-- The surviving sectors form a genuine projection, even at exceptional parameters. -/
theorem hullHeckeSupport_idempotent (q : ℂ) (f : _root_.Polynomial ℂ) :
    IsIdempotentElem (hullHeckeSupport p q f) := by
  have hp : hullPositive p * hullPositive p = hullPositive p := hullPositive_idempotent p
  have hn : hullNegative p * hullNegative p = hullNegative p := hullNegative_idempotent p
  change hullHeckeSupport p q f * hullHeckeSupport p q f = hullHeckeSupport p q f
  simp only [hullHeckeSupport, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, hullPositive_mul_hullNegative, hullNegative_mul_hullPositive,
    hp, hn, smul_zero, add_zero, zero_add]
  by_cases ha : f.eval (q ^ 2) = 0 <;> by_cases hb : f.eval (-1) = 0 <;>
    simp only [ha, hb, if_pos, if_neg, zero_mul, one_mul]

/-- The entire observable image is the sum of its surviving reflection sectors. -/
theorem hullHecke_polynomial_range (q : ℂ) (f : _root_.Polynomial ℂ) :
    LinearMap.range (aeval (hullHecke p q) f) = LinearMap.range (hullHeckeSupport p q f) := by
  have hab := (hullHecke_reciprocal_products p q f).1
  have hsa := (hullHecke_support_absorbs p q f).1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨aeval (hullHecke p q) f y, ?_⟩
    exact congrArg (fun U : Module.End ℂ (reflectionHull p) => U y) hsa
  · rintro ⟨y, rfl⟩
    exact ⟨hullHeckeReciprocal p q f y,
      congrArg (fun U : Module.End ℂ (reflectionHull p) => U y) hab⟩

/-- The full kernel is exactly the kernel of the surviving-sector projection. -/
theorem hullHecke_polynomial_kernel (q : ℂ) (f : _root_.Polynomial ℂ) :
    LinearMap.ker (aeval (hullHecke p q) f) = LinearMap.ker (hullHeckeSupport p q f) := by
  have hba := (hullHecke_reciprocal_products p q f).2
  have has := (hullHecke_support_absorbs p q f).2
  ext x
  change aeval (hullHecke p q) f x = 0 ↔ hullHeckeSupport p q f x = 0
  constructor
  · intro hx
    have h := congrArg (fun U : Module.End ℂ (reflectionHull p) => U x) hba
    simpa only [Module.End.mul_apply, hx, map_zero] using h.symm
  · intro hx
    have h := congrArg (fun U : Module.End ℂ (reflectionHull p) => U x) has
    simpa only [Module.End.mul_apply, hx, map_zero] using h.symm

/-- Exact specialization rank: each nonvanishing spectral value contributes its full sector. -/
theorem hullHecke_polynomial_rank (q : ℂ) (f : _root_.Polynomial ℂ) :
    (Module.finrank ℂ (LinearMap.range (aeval (hullHecke p q) f)) : ℂ) =
      (if f.eval (q ^ 2) = 0 then 0 else
        (Module.finrank ℂ (LinearMap.range (hullPositive p)) : ℂ)) +
      (if f.eval (-1) = 0 then 0 else
        (Module.finrank ℂ (LinearMap.range (hullNegative p)) : ℂ)) := by
  rw [hullHecke_polynomial_range,
    ← (LinearMap.IsIdempotentElem.isProj_range _ (hullHeckeSupport_idempotent p q f)).trace]
  rw [hullHeckeSupport, map_add, map_smul, map_smul,
    (LinearMap.IsIdempotentElem.isProj_range _ (hullPositive_idempotent p)).trace,
    (LinearMap.IsIdempotentElem.isProj_range _ (hullNegative_idempotent p)).trace]
  by_cases ha : f.eval (q ^ 2) = 0 <;> by_cases hb : f.eval (-1) = 0 <;>
    simp only [ha, hb, if_pos, if_neg, zero_smul, one_smul]

#print axioms hullHecke_reciprocal_products
#print axioms hullHecke_polynomial_range
#print axioms hullHecke_polynomial_kernel
#print axioms hullHecke_polynomial_rank

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
