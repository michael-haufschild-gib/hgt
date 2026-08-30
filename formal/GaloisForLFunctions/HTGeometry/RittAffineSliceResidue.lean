import GaloisForLFunctions.HTGeometry.RittAffineSliceDescent
import GaloisForLFunctions.HTGeometry.RittEigenSliceDescent

/-!
# The residue of the affine slice is one of the two inhomogeneity coefficients

The top-degree identity of `exists_eigen_relation_of_affine_cross` carries the coefficient
`((α·X + β)·Q).coeff (deg P)`.  Cancelling the denominator shows that `(α·X + β)·Q` is a difference
of two polynomials of degree `deg P`, so its own degree is at most `deg P`; its coefficient there is
therefore either zero or its leading coefficient, and the latter is `α` or `β`, since `Q` is monic.

So the slice always returns a relation

`φ(u)·a^{deg P} = a^{deg Q}·(c·u + r)`,  `r ∈ {0, α, β}`,  `u ≠ 0`,

in the coefficient field.  That the residue is *one of the two given coefficients* — never a new
element of the bigger field — is what lets the descent be iterated down a jet tower: an inhomogeneity
which is a base combination of the lower jets stays one.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

section Polynomials

variable {K : Type*} [Field K]

/-- The coefficient of the affine inhomogeneity at the numerator's degree is `0`, `α` or `β`. -/
theorem coeff_affineInhom_mem (α β : K) {Q : K[X]} (hQ : Q.Monic) {D : ℕ}
    (hle : ((C α * X + C β) * Q).natDegree ≤ D) :
    ((C α * X + C β) * Q).coeff D = 0 ∨ ((C α * X + C β) * Q).coeff D = α ∨
      ((C α * X + C β) * Q).coeff D = β := by
  classical
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- the coefficient is the leading coefficient of the product
    have hlead : ((C α * X + C β) * Q).coeff D = (C α * X + C β : K[X]).leadingCoeff := by
      rw [← heq, ← leadingCoeff, leadingCoeff_mul, hQ.leadingCoeff, mul_one]
    by_cases hα : α = 0
    · by_cases hβ : β = 0
      · left
        rw [hlead, hα, hβ]
        simp
      · right; right
        rw [hlead, hα]
        simp [leadingCoeff_C]
    · right; left
      rw [hlead, leadingCoeff_linear hα]
  · left
    exact coeff_eq_zero_of_natDegree_lt hlt

/-- **The affine slice with its residue identified.** -/
theorem exists_eigen_relation_residue_of_affine_cross (Φ : K →+* K) {a b c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic)
    (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + (C α * X + C β) * Q)) :
    ∃ r : K, (r = 0 ∨ r = α ∨ r = β) ∧
      Φ P.leadingCoeff * a ^ P.natDegree
        = a ^ Q.natDegree * (c * P.leadingCoeff + r) := by
  classical
  have hmain := exists_eigen_relation_of_affine_cross Φ ha hc hQ hcop hcross
  refine ⟨((C α * X + C β) * Q).coeff P.natDegree, ?_, hmain⟩
  refine coeff_affineInhom_mem α β hQ ?_
  -- the inhomogeneity has degree at most that of the numerator
  set T : K[X] := C a * X + C b with hT
  have hTdeg : T.natDegree = 1 := natDegree_linear ha
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hcopQ : IsCoprime Q (C c * P + (C α * X + C β) * Q) := by
    have hcu : IsUnit (C c : K[X]) := isUnit_C.mpr (Ne.isUnit hc)
    have h1 : IsCoprime Q (C c * P) :=
      (isCoprime_mul_unit_left_right hcu _ _).mpr hcop.symm
    have h2 := h1.add_mul_left_right (C α * X + C β)
    have heq : C c * P + Q * (C α * X + C β) = C c * P + (C α * X + C β) * Q := by ring
    rwa [heq] at h2
  have hdvd : Q ∣ twistComp Φ T Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨twistComp Φ T P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  have hnum : twistComp Φ T P = C d * (C c * P + (C α * X + C β) * Q) := by
    refine mul_right_cancel₀ hQ0 ?_
    rw [hcross, hd]
    ring
  have hsplit : (C α * X + C β) * Q
      = C d⁻¹ * twistComp Φ T P - C c * P := by
    have hdinv : (C d⁻¹ : K[X]) * C d = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hd0, map_one]
    calc (C α * X + C β) * Q
        = C d⁻¹ * (C d * (C c * P + (C α * X + C β) * Q)) - C c * P := by
          rw [← mul_assoc, hdinv, one_mul]; ring
      _ = C d⁻¹ * twistComp Φ T P - C c * P := by rw [hnum]
  rw [hsplit]
  refine le_trans (natDegree_sub_le _ _) ?_
  refine max_le ?_ ?_
  · refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_C, zero_add, natDegree_twistComp Φ hTdeg]
  · refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_C, zero_add]

end Polynomials

section Ambient

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- Evaluation intertwines the shift with any twisted substitution realising it on the generator. -/
theorem aeval_twistComp_of_aeval_eq (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} {T : E[X]} (hT : aeval t T = σ t) (p : E[X]) :
    aeval t (twistComp φ T p) = σ (aeval t p) := by
  rw [twistComp, aeval_comp, hT, aeval_shift_map σ φ hcomp t p]

/-- **The affine slice inside an ambient field.**  An eigen-inhomogeneous relation for a member of a
simple transcendental extension whose generator the shift moves affinely descends to a relation in
the coefficient field, with residue one of the two inhomogeneity coefficients. -/
theorem exists_eigen_relation_residue_of_affine_mem_adjoin (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a b c α β : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t + algebraMap E L b)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : σ W = algebraMap E L c * W + (algebraMap E L α * t + algebraMap E L β)) :
    ∃ (u r : E) (D e : ℕ), u ≠ 0 ∧ (r = 0 ∨ r = α ∨ r = β) ∧
      φ u * a ^ D = a ^ e * (c * u + r) := by
  classical
  obtain ⟨A, B, hB, hcop, hAB⟩ := exists_coprime_monic_repr ht hW
  have hinj : Function.Injective (aeval t : E[X] →ₐ[E] L) :=
    transcendental_iff_injective.mp ht
  have hB0 : B ≠ 0 := hB.ne_zero
  have hBt : aeval t B ≠ 0 := fun h => hB0 (hinj (by simpa using h))
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, map_zero] at hAB
    exact hW0 ((mul_eq_zero.mp hAB).resolve_right hBt)
  have hWeq : W = aeval t A / aeval t B := by
    field_simp
    exact hAB
  set T : E[X] := C a * X + C b with hT
  have hTval : aeval t T = σ t := by rw [hT, hσt]; simp
  have htwB : aeval t (twistComp φ T B) ≠ 0 := fun h =>
    (twistComp_ne_zero φ (natDegree_linear ha) hB0) (hinj (by simpa using h))
  have hcross : twistComp φ T A * B = twistComp φ T B * (C c * A + (C α * X + C β) * B) := by
    refine hinj ?_
    have hσA := aeval_twistComp_of_aeval_eq σ φ hcomp hTval A
    have hσB := aeval_twistComp_of_aeval_eq σ φ hcomp hTval B
    rw [hWeq, map_div₀, ← hσA, ← hσB] at hrel
    rw [map_mul, map_mul, map_add, map_mul, map_mul, map_add, map_mul, aeval_C, aeval_C,
      aeval_C, aeval_X]
    rw [div_eq_iff htwB] at hrel
    field_simp at hrel
    linear_combination hrel
  obtain ⟨r, hr, hmain⟩ :=
    exists_eigen_relation_residue_of_affine_cross φ ha hc hB hcop hcross
  exact ⟨A.leadingCoeff, r, A.natDegree, B.natDegree, leadingCoeff_ne_zero.mpr hA0, hr, hmain⟩

end Ambient

end GaloisForLFunctions.HTGeometry
