import GaloisForLFunctions.RHTower.CriticalDiscAnalyticCompleteness

/-!
# Schwarz-real critical-disc completeness

This file constructs the literal Schwarz involution on the critical closed
disc and verifies that the actual paired Euler tangents are fixed by it.
-/

noncomputable section

namespace RHTower

open Complex Metric Set ComplexConjugate

/-- Complex conjugation preserves the critical closed disc. -/
def criticalDiscConjugation (r : ℝ) : C(CriticalClosedDisc r, CriticalClosedDisc r) where
  toFun z := ⟨conj z, by
    have hz := z.prop
    rw [mem_closedBall, dist_eq] at hz ⊢
    have heq : conj (z : ℂ) - 1 / 2 = conj ((z : ℂ) - 1 / 2) := by simp
    rw [heq, RCLike.norm_conj]
    exact hz⟩
  continuous_toFun := Continuous.subtype_mk
    (Complex.continuous_conj.comp continuous_subtype_val) _

@[simp]
theorem criticalDiscConjugation_involutive
    (r : ℝ) (z : CriticalClosedDisc r) :
    criticalDiscConjugation r (criticalDiscConjugation r z) = z := by
  apply Subtype.ext
  simp [criticalDiscConjugation]

@[simp]
theorem criticalDiscCoordinate_conjugation
    (r : ℝ) (z : CriticalClosedDisc r) :
    criticalDiscCoordinate r (criticalDiscConjugation r z) =
      conj (criticalDiscCoordinate r z) := rfl

/-- Schwarz conjugation of a continuous function on the critical disc. -/
def criticalSchwarzTransform
    (r : ℝ) (g : C(CriticalClosedDisc r, ℂ)) : C(CriticalClosedDisc r, ℂ) where
  toFun z := conj (g (criticalDiscConjugation r z))
  continuous_toFun := Complex.continuous_conj.comp
    (g.continuous.comp (criticalDiscConjugation r).continuous)

@[simp]
theorem criticalSchwarzTransform_apply
    (r : ℝ) (g : C(CriticalClosedDisc r, ℂ)) (z : CriticalClosedDisc r) :
    criticalSchwarzTransform r g z =
      conj (g (criticalDiscConjugation r z)) := rfl

theorem criticalSchwarzTransform_add
    (r : ℝ) (f g : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (f + g) =
      criticalSchwarzTransform r f + criticalSchwarzTransform r g := by
  ext z
  simp [criticalSchwarzTransform]

theorem criticalSchwarzTransform_smul
    (r : ℝ) (c : ℂ) (f : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (c • f) =
      conj c • criticalSchwarzTransform r f := by
  ext z
  simp [criticalSchwarzTransform]

@[simp]
theorem criticalSchwarzTransform_involutive
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (criticalSchwarzTransform r f) = f := by
  ext z
  simp [criticalSchwarzTransform]

theorem norm_criticalSchwarzTransform_le
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    ‖criticalSchwarzTransform r f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro z
  rw [criticalSchwarzTransform_apply, RCLike.norm_conj]
  exact ContinuousMap.norm_coe_le_norm f _

@[simp]
theorem norm_criticalSchwarzTransform
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    ‖criticalSchwarzTransform r f‖ = ‖f‖ := by
  apply le_antisymm (norm_criticalSchwarzTransform_le r f)
  have h := norm_criticalSchwarzTransform_le r (criticalSchwarzTransform r f)
  simpa using h

/-- On the critical disc the compact tangent agrees pointwise with the literal
actual-source formula. -/
theorem criticalDisc_compactPrimeEulerUnitTangent_apply
    {r : ℝ} (hr : r < 1 / 2) (p : Nat.Primes)
    (z : CriticalClosedDisc r) :
    compactPrimeEulerUnitTangent (criticalDiscCoordinate r) (p : ℕ) z =
      primeEulerUnitTangent (p : ℕ) z := by
  have hδ : 0 < 1 / 2 - r := by linarith
  have hlog : 0 < Real.log ((p : Nat.Primes) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hq : ‖compactExponentialTest (criticalDiscCoordinate r)
      (Real.log (p : ℝ))‖ < 1 := by
    apply norm_compactExponentialTest_lt_one_of_re_pos
      (criticalDiscCoordinate r) _
      (Real.log (p : ℝ) * (1 / 2 - r)) (mul_pos hlog hδ)
    intro k
    have hk := criticalDiscCoordinate_re_lower k
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left hk hlog.le
  exact compactPrimeEulerUnitTangent_apply
    (criticalDiscCoordinate r) p.prop.two_le z
      (lt_of_lt_of_le hδ (criticalDiscCoordinate_re_lower z)) hq

/-- The compact paired Euler tangent is the literal FE-paired actual-source
tangent pointwise. -/
theorem criticalDisc_compactPrimeEulerUnitFETangent_apply
    {r : ℝ} (hr : r < 1 / 2) (p : Nat.Primes)
    (z : CriticalClosedDisc r) :
    compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r) (criticalDiscReflection r) (p : ℕ) z =
      primeEulerUnitFETangent (p : ℕ) z := by
  unfold compactPrimeEulerUnitFETangent primeEulerUnitFETangent
  rw [ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    criticalDisc_compactPrimeEulerUnitTangent_apply hr,
    criticalDisc_compactPrimeEulerUnitTangent_apply hr]
  rfl

/-- Every actual paired Euler tangent is Schwarz fixed. -/
theorem criticalSchwarzTransform_primeEulerUnitFETangent
    {r : ℝ} (hr : r < 1 / 2) (p : Nat.Primes) :
    criticalSchwarzTransform r
      (compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r) (criticalDiscReflection r) (p : ℕ)) =
      compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r) (criticalDiscReflection r) (p : ℕ) := by
  ext z
  rw [criticalSchwarzTransform_apply,
    criticalDisc_compactPrimeEulerUnitFETangent_apply hr,
    criticalDisc_compactPrimeEulerUnitFETangent_apply hr]
  rw [primeEulerUnitFETangent_conj p.prop.two_le]

end RHTower
