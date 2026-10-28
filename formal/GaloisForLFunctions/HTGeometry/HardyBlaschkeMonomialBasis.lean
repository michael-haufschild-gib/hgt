import GaloisForLFunctions.HTGeometry.HardyLeakageRankOne
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# A Blaschke factor and its geometric complement form a Hilbert basis

The normalized Szego kernel spans the complement of a single Blaschke range.
Adjoining it to the Blaschke images of the monomials gives a complete
orthonormal basis of coefficient Hardy space.
-/

noncomputable section

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {a : ℂ}

/-- The unit vector along the geometric reproducing kernel. -/
def hardyBlaschkeGround (ha : ‖a‖ < 1) : HardyDisk :=
  ((‖hardyKernel ha‖ : ℂ)⁻¹) • hardyKernel ha

theorem norm_hardyBlaschkeGround (ha : ‖a‖ < 1) :
    ‖hardyBlaschkeGround ha‖ = 1 := by
  have hk : ‖hardyKernel ha‖ ≠ 0 := norm_ne_zero_iff.mpr (hardyKernel_ne_zero ha)
  rw [hardyBlaschkeGround, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hk]

theorem norm_smul_hardyBlaschkeGround (ha : ‖a‖ < 1) :
    (‖hardyKernel ha‖ : ℂ) • hardyBlaschkeGround ha = hardyKernel ha := by
  have hk : (‖hardyKernel ha‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hardyKernel_ne_zero ha))
  rw [hardyBlaschkeGround, smul_smul, mul_inv_cancel₀ hk, one_smul]

theorem inner_hardyBlaschkeGround_blaschkeMul (ha : ‖a‖ < 1) (x : HardyDisk) :
    inner ℂ (hardyBlaschkeGround ha) (blaschkeMul ha x) = 0 := by
  have hx : blaschkeMul ha x ∈ (modelSpace ha)ᗮ := by
    rw [orthogonal_modelSpace]
    exact ⟨x, rfl⟩
  have hker : inner ℂ (hardyKernel ha) (blaschkeMul ha x) = 0 :=
    (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.mem_span_singleton_self _)
  rw [hardyBlaschkeGround, inner_smul_left, hker, mul_zero]

/-- The geometric ground mode followed by the Blaschke-shifted monomials. -/
def hardyBlaschkeMode (ha : ‖a‖ < 1) : Option ℕ → HardyDisk
  | none => hardyBlaschkeGround ha
  | some n => blaschkeMul ha (HilbertSchmidt.lpBasis ℕ n)

/-- The one-dimensional geometric complement is orthogonal to every shifted monomial. -/
theorem orthonormal_hardyBlaschkeMode (ha : ‖a‖ < 1) :
    Orthonormal ℂ (hardyBlaschkeMode ha) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [hardyBlaschkeMode, ↓reduceIte, inner_self_eq_norm_sq_to_K,
        norm_hardyBlaschkeGround]
      norm_num
    | some j =>
      simpa only [hardyBlaschkeMode, reduceCtorEq, ↓reduceIte] using
        inner_hardyBlaschkeGround_blaschkeMul ha (HilbertSchmidt.lpBasis ℕ j)
  | some i =>
    cases j with
    | none =>
      have h : inner ℂ (blaschkeMul ha (HilbertSchmidt.lpBasis ℕ i))
          (hardyBlaschkeGround ha) = 0 := by
        rw [← inner_conj_symm, inner_hardyBlaschkeGround_blaschkeMul, map_zero]
      simpa only [hardyBlaschkeMode, reduceCtorEq, ↓reduceIte] using h
    | some j =>
      simpa only [hardyBlaschkeMode, inner_blaschkeMul, Option.some.injEq] using
        orthonormal_iff_ite.mp (HilbertSchmidt.lpBasis ℕ).orthonormal i j

/-- The geometric complement and the Blaschke range together exhaust Hardy space. -/
theorem orthogonal_span_hardyBlaschkeMode (ha : ‖a‖ < 1) :
    (Submodule.span ℂ (Set.range (hardyBlaschkeMode ha)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hmode : ∀ i, inner ℂ (hardyBlaschkeMode ha i) x = 0 := fun i =>
    (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨i, rfl⟩)
  have hkernel : inner ℂ (hardyKernel ha) x = 0 := by
    rw [← norm_smul_hardyBlaschkeGround ha, inner_smul_left]
    change starRingEnd ℂ (‖hardyKernel ha‖ : ℂ) *
      inner ℂ (hardyBlaschkeMode ha none) x = 0
    rw [hmode none, mul_zero]
  have hxperp : x ∈ (modelSpace ha)ᗮ := by
    change x ∈ (ℂ ∙ hardyKernel ha)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left,
      ← inner_conj_symm, hkernel, map_zero]
  rw [orthogonal_modelSpace] at hxperp
  obtain ⟨y, hy⟩ := hxperp
  change blaschkeMul ha y = x at hy
  have hyzero : y = 0 := by
    apply (HilbertSchmidt.lpBasis ℕ).repr.injective
    ext n
    rw [HilbertBasis.repr_apply_apply, map_zero]
    change inner ℂ (HilbertSchmidt.lpBasis ℕ n) y = 0
    have hn := hmode (some n)
    change inner ℂ (blaschkeMul ha (HilbertSchmidt.lpBasis ℕ n)) x = 0 at hn
    rw [← hy, inner_blaschkeMul] at hn
    exact hn
  rw [← hy, hyzero, map_zero]

/-- The complete Blaschke-monomial Hilbert basis, including the geometric ground mode. -/
def hardyBlaschkeBasis (ha : ‖a‖ < 1) : HilbertBasis (Option ℕ) ℂ HardyDisk :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_hardyBlaschkeMode ha)
    (orthogonal_span_hardyBlaschkeMode ha)

theorem hardyBlaschkeBasis_apply (ha : ‖a‖ < 1) (i : Option ℕ) :
    hardyBlaschkeBasis ha i = hardyBlaschkeMode ha i := by
  rw [hardyBlaschkeBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

end GaloisForLFunctions.HTGeometry
