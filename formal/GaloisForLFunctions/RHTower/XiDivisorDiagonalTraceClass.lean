import GaloisForLFunctions.RHTower.XiDivisorHilbertCarrier
import GaloisForLFunctions.RHTower.DeningerDivisorDefectTrace
import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.TraceNormLimit

/-!
# Diagonal trace-class operators on the Xi divisor carrier

The trace-tower conjecture needs concrete trace-class operators with honest divisor spectrum.
This file constructs them, joining the divisor Hilbert carrier `XiDivisorL2 = ℓ²(XiZeroCopy)`
to the corpus's Schatten framework for the first time:

* `xiDivisorHilbertBasis` — the canonical Hilbert basis of the divisor carrier;
* `xiDivisorDiagonal` — the diagonal operator of any uniformly bounded weight family, with
  `xiDivisorDiagonal_isHilbertSchmidt` for square-summable weights;
* `norm_inv_xiSpectralPoint_le` — the spectral points are uniformly bounded away from zero
  (divisor separation at the origin), so the **inverse-spectral diagonal**
  `diag(μ_q⁻¹)` is a bounded operator, and it is Hilbert–Schmidt by the corpus's
  `Σ 1/‖μ‖² < ∞`;
* `xiDivisorResolventSquare_memSchattenClass_one` — **the resolvent-square diagonal
  `diag(μ_q⁻²)` is trace class** (Schatten-1), as a product of two Hilbert–Schmidt diagonals.

This is the first concrete Schatten-1 operator in the corpus whose spectrum is the actual
(reciprocal-square) Xi divisor — the divisor-side witness that the trace tower's limit
theorem has arithmetic consumers.  Unconditional throughout.
-/

namespace RHTower

noncomputable section

open Complex ContinuousLinearMap

/-- The canonical Hilbert basis of the divisor carrier. -/
def xiDivisorHilbertBasis : HilbertBasis XiZeroCopy ℂ XiDivisorL2 :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp]
theorem xiDivisorHilbertBasis_apply (q : XiZeroCopy) :
    xiDivisorHilbertBasis q = lp.single 2 q (1 : ℂ) := by
  rw [← xiDivisorHilbertBasis.repr_symm_single]
  rfl

/-- The underlying function of the diagonal operator. -/
def xiDivisorDiagonalFun (w : XiZeroCopy → ℂ) (f : XiDivisorL2)
    (q : XiZeroCopy) : ℂ :=
  w q * f q

theorem xiDivisorDiagonalFun_memℓp (w : XiZeroCopy → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ q, ‖w q‖ ≤ C) (f : XiDivisorL2) :
    Memℓp (xiDivisorDiagonalFun w f) 2 := by
  have hg : Memℓp (fun q : XiZeroCopy => (C : ℂ) * f q) 2 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      (lp.memℓp ((C : ℂ) • f))
  apply hg.mono'
  intro q
  simp only [xiDivisorDiagonalFun, norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((ha q).trans_eq (by simp [abs_of_nonneg hC])) (norm_nonneg _)

/-- The diagonal operator of a uniformly bounded weight family, as a linear map. -/
def xiDivisorDiagonalLinearMap (w : XiZeroCopy → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ q, ‖w q‖ ≤ C) :
    XiDivisorL2 →ₗ[ℂ] XiDivisorL2 where
  toFun f := ⟨xiDivisorDiagonalFun w f, xiDivisorDiagonalFun_memℓp w hC ha f⟩
  map_add' f g := by
    ext q
    change w q * (f q + g q) = w q * f q + w q * g q
    rw [mul_add]
  map_smul' z f := by
    ext q
    change w q * (z * f q) = z * (w q * f q)
    ring

/-- The diagonal operator of a uniformly bounded weight family. -/
def xiDivisorDiagonal (w : XiZeroCopy → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ q, ‖w q‖ ≤ C) :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  (xiDivisorDiagonalLinearMap w hC ha).mkContinuous C fun f => by
    calc ‖xiDivisorDiagonalLinearMap w hC ha f‖
        ≤ ‖(C : ℂ) • f‖ := by
          apply lp.norm_mono (by norm_num)
          intro q
          change ‖w q * f q‖ ≤ ‖((C : ℂ) • f) q‖
          rw [norm_mul]
          change _ ≤ ‖(C : ℂ) * f q‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            ((ha q).trans_eq (by simp [abs_of_nonneg hC])) (norm_nonneg _)
      _ = C * ‖f‖ := by
          rw [norm_smul]
          simp [abs_of_nonneg hC]

@[simp]
theorem xiDivisorDiagonal_apply (w : XiZeroCopy → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ q, ‖w q‖ ≤ C) (f : XiDivisorL2) (q : XiZeroCopy) :
    (xiDivisorDiagonal w hC ha f : XiZeroCopy → ℂ) q = w q * f q :=
  rfl

/-- The diagonal operator acts on the canonical basis by its weights. -/
theorem xiDivisorDiagonal_basis (w : XiZeroCopy → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ q, ‖w q‖ ≤ C) (q : XiZeroCopy) :
    xiDivisorDiagonal w hC ha (xiDivisorHilbertBasis q) =
      w q • xiDivisorHilbertBasis q := by
  rw [xiDivisorHilbertBasis_apply]
  ext r
  change w r * (lp.single 2 q (1 : ℂ) : XiDivisorL2) r =
    (w q • (lp.single 2 q (1 : ℂ) : XiDivisorL2)) r
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : r = q
  · subst h
    rfl
  · rw [lp.single_apply_ne 2 q 1 h]
    ring

theorem norm_xiDivisorDiagonal_basis (w : XiZeroCopy → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ q, ‖w q‖ ≤ C) (q : XiZeroCopy) :
    ‖xiDivisorDiagonal w hC ha (xiDivisorHilbertBasis q)‖ = ‖w q‖ := by
  rw [xiDivisorDiagonal_basis, norm_smul,
    xiDivisorHilbertBasis.orthonormal.1 q, mul_one]

/-- Square-summable weights give a Hilbert–Schmidt diagonal. -/
theorem xiDivisorDiagonal_isHilbertSchmidt (w : XiZeroCopy → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ q, ‖w q‖ ≤ C)
    (hsum : Summable fun q => ‖w q‖ ^ 2) :
    IsHilbertSchmidt (xiDivisorDiagonal w hC ha) := by
  apply isHilbertSchmidt_of_summable xiDivisorHilbertBasis
  exact hsum.congr fun q =>
    congrArg (· ^ 2) (norm_xiDivisorDiagonal_basis w hC ha q).symm

/-- **Divisor separation at the origin**: the spectral points are uniformly bounded away from
zero. -/
theorem exists_uniform_norm_xiSpectralPoint_lowerBound :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : XiZeroCopy, δ ≤ ‖xiSpectralPoint q‖ := by
  obtain ⟨δ, hδ0, _, hδ⟩ := exists_xiSpectralPoint_separation 0
  refine ⟨δ, hδ0, fun q => ?_⟩
  have h := hδ q (xiSpectralPoint_ne_zero q)
  rwa [sub_zero] at h

/-- The inverse-spectral weights are square-summable, in norm form. -/
theorem summable_norm_inv_xiSpectralPoint_sq :
    Summable fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹‖ ^ 2 := by
  apply xiSpectralPoint_inv_sq_summable.congr
  intro q
  rw [norm_inv, inv_pow, one_div]

/-- **The resolvent-square diagonal `diag(μ_q⁻²)` is trace class**: the first concrete
Schatten-1 operator with honest (reciprocal-square) Xi divisor spectrum — the divisor-side
witness that the trace tower's limit theorem has arithmetic consumers. -/
theorem xiDivisorResolventSquare_memSchattenClass_one :
    ∃ (δ : ℝ) (hδ0 : 0 < δ)
      (hbound : ∀ q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖ ≤ δ⁻¹),
      MemSchattenClass 1
        ((xiDivisorDiagonal (fun q => (xiSpectralPoint q)⁻¹)
            (le_of_lt (inv_pos.mpr hδ0)) hbound).comp
          (xiDivisorDiagonal (fun q => (xiSpectralPoint q)⁻¹)
            (le_of_lt (inv_pos.mpr hδ0)) hbound)) := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_uniform_norm_xiSpectralPoint_lowerBound
  have hbound : ∀ q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖ ≤ δ⁻¹ := by
    intro q
    rw [norm_inv]
    have hpos : 0 < ‖xiSpectralPoint q‖ :=
      norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    rw [inv_eq_one_div, inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) hδ0 (hδ q)
  refine ⟨δ, hδ0, hbound, ?_⟩
  exact memSchattenClass_one_comp
    (xiDivisorDiagonal_isHilbertSchmidt _ _ _
      summable_norm_inv_xiSpectralPoint_sq)
    (xiDivisorDiagonal_isHilbertSchmidt _ _ _
      summable_norm_inv_xiSpectralPoint_sq)

end

end RHTower
