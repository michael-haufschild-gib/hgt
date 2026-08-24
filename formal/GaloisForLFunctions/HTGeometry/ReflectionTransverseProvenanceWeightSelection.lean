import GaloisForLFunctions.HTGeometry.ReflectionTransverseDivisibilitySelection

/-!
# Reflection-transverse provenance--weight selection

A formation cover may preserve an arbitrary reflection-fixed core while scaling only the
reflection-transverse integral charge. This file defines that action and proves the exact selection
law: if a cover of degree at least two fixes the complete charge, then its transverse part is zero.

The result preserves every fixed-label coefficient. It does not assert that the Euler--Gamma source
admits the required cover descent, or identify a source charge with the Xi divisor. Those are the
arithmetic construction and landing obligations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {ι : Type u}

/-- Formation scaling fixes the reflection-fixed core and multiplies only the transverse charge. -/
def reflectionProvenanceWeightAction
    (r : ι ≃ ι) (scale : ℕ) (q : ι →₀ ℤ) : ι →₀ ℤ :=
  reflectionFixedIntegralPart r q + scale • reflectionTransverseIntegralPart r q

@[simp]
theorem reflectionProvenanceWeightAction_one
    (r : ι ≃ ι) (q : ι →₀ ℤ) :
    reflectionProvenanceWeightAction r 1 q = q := by
  rw [reflectionProvenanceWeightAction, one_nsmul,
    reflectionFixedIntegralPart_add_transverse]

/-- Every formation scale preserves the complete fixed core. -/
theorem reflectionFixedIntegralPart_provenanceWeightAction
    (r : ι ≃ ι) (scale : ℕ) (q : ι →₀ ℤ) :
    reflectionFixedIntegralPart r (reflectionProvenanceWeightAction r scale q) =
      reflectionFixedIntegralPart r q := by
  classical
  ext i
  by_cases hi : r i = i <;>
    simp [reflectionProvenanceWeightAction, reflectionFixedIntegralPart,
      reflectionTransverseIntegralPart, hi]

/-- The transverse projection has formation weight one. -/
theorem reflectionTransverseIntegralPart_provenanceWeightAction
    (r : ι ≃ ι) (scale : ℕ) (q : ι →₀ ℤ) :
    reflectionTransverseIntegralPart r (reflectionProvenanceWeightAction r scale q) =
      scale • reflectionTransverseIntegralPart r q := by
  classical
  ext i
  by_cases hi : r i = i <;>
    simp [reflectionProvenanceWeightAction, reflectionFixedIntegralPart,
      reflectionTransverseIntegralPart, hi]

/-- Formation scales compose multiplicatively. -/
theorem reflectionProvenanceWeightAction_comp
    (r : ι ≃ ι) (m n : ℕ) (q : ι →₀ ℤ) :
    reflectionProvenanceWeightAction r m
        (reflectionProvenanceWeightAction r n q) =
      reflectionProvenanceWeightAction r (m * n) q := by
  rw [reflectionProvenanceWeightAction,
    reflectionFixedIntegralPart_provenanceWeightAction,
    reflectionTransverseIntegralPart_provenanceWeightAction,
    reflectionProvenanceWeightAction]
  rw [← mul_nsmul]
  simp [mul_comm]

/-- A nontrivial formation cover cannot fix a nonzero weight-one transverse integral charge. -/
theorem reflectionTransverseIntegralPart_eq_zero_of_provenanceWeightInvariant
    (r : ι ≃ ι) (q : ι →₀ ℤ) {scale : ℕ} (hscale : 2 ≤ scale)
    (hinv : reflectionProvenanceWeightAction r scale q = q) :
    reflectionTransverseIntegralPart r q = 0 := by
  have htrans := congrArg (reflectionTransverseIntegralPart r) hinv
  rw [reflectionTransverseIntegralPart_provenanceWeightAction] at htrans
  ext i
  have hi := congrArg (fun z : ι →₀ ℤ => z i) htrans
  simp only [nsmul_eq_mul, Finsupp.smul_apply] at hi
  have hscaleOne : (scale : ℤ) ≠ 1 := by
    exact_mod_cast (by omega : scale ≠ 1)
  have hprod : ((scale : ℤ) - 1) * reflectionTransverseIntegralPart r q i = 0 := by
    calc
      ((scale : ℤ) - 1) * reflectionTransverseIntegralPart r q i =
          (scale : ℤ) * reflectionTransverseIntegralPart r q i -
            reflectionTransverseIntegralPart r q i := by ring
      _ = 0 := by rw [hi]; ring
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hscaleOne)

/-- Invariance under one nontrivial formation scale is exactly transverse neutrality. -/
theorem reflectionProvenanceWeightAction_eq_self_iff
    (r : ι ≃ ι) (q : ι →₀ ℤ) {scale : ℕ} (hscale : 2 ≤ scale) :
    reflectionProvenanceWeightAction r scale q = q ↔
      reflectionTransverseIntegralPart r q = 0 := by
  constructor
  · exact reflectionTransverseIntegralPart_eq_zero_of_provenanceWeightInvariant
      r q hscale
  · intro hzero
    rw [reflectionProvenanceWeightAction, hzero, nsmul_zero, add_zero]
    simpa [hzero] using reflectionFixedIntegralPart_add_transverse r q

/-- Provenance invariance under a nontrivial cover confines support to reflection-fixed labels. -/
theorem support_fixed_of_provenanceWeightInvariant
    (r : ι ≃ ι) (q : ι →₀ ℤ) {scale : ℕ} (hscale : 2 ≤ scale)
    (hinv : reflectionProvenanceWeightAction r scale q = q) :
    ∀ i ∈ q.support, r i = i :=
  support_fixed_of_reflectionTransverseIntegralPart_eq_zero r q
    (reflectionTransverseIntegralPart_eq_zero_of_provenanceWeightInvariant
      r q hscale hinv)

/-- A fixed-label core survives every formation scale with its full integer multiplicity. -/
theorem reflectionProvenanceWeightAction_single_of_fixed
    [DecidableEq ι] (r : ι ≃ ι) {i : ι} (m : ℤ) (scale : ℕ)
    (hi : r i = i) :
    reflectionProvenanceWeightAction r scale (Finsupp.single i m) =
      Finsupp.single i m := by
  have hfixed := reflectionFixedIntegralPart_single_of_fixed r m hi
  have htrans :
      reflectionTransverseIntegralPart r (Finsupp.single i m) = 0 := by
    rw [reflectionTransverseIntegralPart, hfixed, sub_self]
  rw [reflectionProvenanceWeightAction, hfixed, htrans, nsmul_zero, add_zero]

/-- Positive formation weight reduces to the weight-one selector at scale `degree ^ weight`. -/
theorem support_fixed_of_positiveFormationWeightInvariant
    (r : ι ≃ ι) (q : ι →₀ ℤ) {degree weight : ℕ}
    (hdegree : 2 ≤ degree) (hweight : 1 ≤ weight)
    (hinv : reflectionProvenanceWeightAction r (degree ^ weight) q = q) :
    ∀ i ∈ q.support, r i = i := by
  apply support_fixed_of_provenanceWeightInvariant r q _ hinv
  exact le_trans hdegree (Nat.le_pow hweight)

end

end GaloisForLFunctions.HTGeometry
