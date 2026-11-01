import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeDirections
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnInertia

/-!
# Index loss in the orthogonal complement of a nonpositive vector

A strictly negative subspace orthogonal to a nonzero nonpositive vector
can be enlarged by that vector to an injective nonpositive family.
Projection to the finite negative Hilbert factor is injective on this
family. Its dimension therefore exceeds the strictly negative dimension
by one, even when the adjoined vector is null.
-/

noncomputable section
set_option autoImplicit false
open Complex Module
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [AddCommGroup V] [Module ℂ V]

/-- Adjoin one vector to a linear family. -/
def adjoinVector (F : V →ₗ[ℂ] (H × E)) (w : H × E) : (V × ℂ) →ₗ[ℂ] (H × E) where
  toFun z := F z.1 + z.2 • w
  map_add' z t := by
    change F (z.1 + t.1) + (z.2 + t.2) • w = (F z.1 + z.2 • w) + (F t.1 + t.2 • w)
    rw [map_add, add_smul]
    abel
  map_smul' c z := by
    change F (c • z.1) + (c * z.2) • w = c • (F z.1 + z.2 • w)
    rw [map_smul, smul_add, mul_smul]

variable (F : V →ₗ[ℂ] (H × E)) (w : H × E)
    (ho : ∀ v, pairing w (F v) = 0)

include ho in
theorem pairing_family_vector (v : V) : pairing (F v) w = 0 := by
  rw [← pairing_conj_symm (F v) w, ho v, map_zero]

include ho in
/-- Orthogonality makes the square of the enlarged family diagonal in its two components. -/
theorem pairing_adjoinVector_self (v : V) (t : ℂ) :
    pairing (adjoinVector F w (v, t)) (adjoinVector F w (v, t)) =
      pairing (F v) (F v) + (normSq t : ℂ) * pairing w w := by
  change pairing (F v + t • w) (F v + t • w) = _
  simp only [pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right,
    ho, pairing_family_vector F w ho, mul_zero, zero_add, add_zero]
  rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self]

variable (hF : ∀ v, v ≠ 0 → (pairing (F v) (F v)).re < 0)
    (hw : w ≠ 0) (hwq : (pairing w w).re ≤ 0)

include ho hF hwq in
theorem adjoinVector_nonpositive (z : V × ℂ) :
    (pairing (adjoinVector F w z) (adjoinVector F w z)).re ≤ 0 := by
  have hn : (pairing (F z.1) (F z.1)).re ≤ 0 := by
    by_cases hz : z.1 = 0
    · simp only [hz, map_zero, pairing, inner_zero_left, sub_self, Complex.zero_re, le_refl]
    · exact (hF z.1 hz).le
  rw [pairing_adjoinVector_self F w ho z.1 z.2, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact add_nonpos hn (mul_nonpos_of_nonneg_of_nonpos (normSq_nonneg _) hwq)

include ho hF hw in
/-- Strict negativity separates the old family from the adjoined nonpositive line. -/
theorem adjoinVector_eq_zero (z : V × ℂ) (hz : adjoinVector F w z = 0) : z = 0 := by
  have hv : z.1 = 0 := by
    have hpair : pairing (F z.1) (F z.1) = 0 := by
      have he := congrArg (pairing (F z.1)) hz
      change pairing (F z.1) (F z.1 + z.2 • w) = pairing (F z.1) 0 at he
      simpa only [pairing_add_right, pairing_smul_right, pairing_family_vector F w ho,
        mul_zero, add_zero, pairing, inner_zero_right, sub_self] using he
    by_contra hv
    have hn := hF z.1 hv
    rw [hpair, Complex.zero_re] at hn
    exact (lt_irrefl 0) hn
  have ht : z.2 = 0 := by
    have he : z.2 • w = 0 := by
      simpa only [adjoinVector, LinearMap.coe_mk, AddHom.coe_mk, hv, map_zero, zero_add] using hz
    exact (smul_eq_zero.mp he).resolve_right hw
  exact Prod.ext hv ht

include ho hF hw hwq in
/-- Orthogonality to one nonzero nonpositive vector lowers the possible negative dimension. -/
theorem finrank_add_one_le_of_negative_orthogonal [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] :
    finrank ℂ V + 1 ≤ finrank ℂ E := by
  let L : (V × ℂ) →ₗ[ℂ] E := (LinearMap.snd ℂ H E).comp (adjoinVector F w)
  have hzero (z : V × ℂ) (hz : L z = 0) : z = 0 := by
    have hq := adjoinVector_nonpositive F w ho hF hwq z
    have he := eq_zero_of_nonpositive_snd_eq_zero hq hz
    exact adjoinVector_eq_zero F w ho hF hw z he
  have hi : Function.Injective L := by
    intro z t hzt
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hzt, sub_self]
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_prod, Module.finrank_self] using hd

#print axioms finrank_add_one_le_of_negative_orthogonal

/-- A Gram form represented inside the orthogonal complement loses one negative direction. -/
theorem hermNegIndex_add_one_le_of_orthogonal [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (L : (ι → ℂ) →ₗ[ℂ] (H × E))
    (hL : ∀ c, GaloisForLFunctions.HTGeometry.hermQuad M c = (pairing (L c) (L c)).re)
    {w : H × E} (hw : w ≠ 0) (hwq : (pairing w w).re ≤ 0)
    (ho : ∀ c, pairing w (L c) = 0) :
    GaloisForLFunctions.HTGeometry.hermNegIndex M + 1 ≤ finrank ℂ E := by
  obtain ⟨W, hW, hneg⟩ :=
    GaloisForLFunctions.HTGeometry.exists_isPosDefOn_finrank_eq_posIndex (-M)
  have hn (c : W) (hc : c ≠ 0) :
      (pairing ((L.comp W.subtype) c) ((L.comp W.subtype) c)).re < 0 := by
    have hc' : (c : ι → ℂ) ≠ 0 := fun he => hc (Subtype.ext he)
    have h := hneg c c.property hc'
    rw [GaloisForLFunctions.HTGeometry.hermQuad_neg, hL] at h
    exact neg_pos.mp h
  have hd := finrank_add_one_le_of_negative_orthogonal (L.comp W.subtype) w
    (fun c => ho c) hn hw hwq
  rw [hW] at hd
  exact hd

#print axioms hermNegIndex_add_one_le_of_orthogonal

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
