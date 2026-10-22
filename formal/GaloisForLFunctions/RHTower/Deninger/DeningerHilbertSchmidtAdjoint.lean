import GaloisForLFunctions.RHTower.Deninger.DeningerHilbertSchmidtNuclear

/-!
# Parseval, and the Hilbert–Schmidt condition is basis independent

The coefficients of a vector in a Hilbert basis are square-summable with sum the squared norm.
Applying this in both spaces to the matrix coefficients of a map, and exchanging the two sums,
shows that the sum of the squared norms of the images of a Hilbert basis is the same for the map
and for its adjoint, and therefore does not depend on the chosen bases.

So the Hilbert–Schmidt condition is a property of the map alone.

* `deningerParseval_summable`, `deningerParseval` : Parseval for a Hilbert basis.
* `deningerHilbertSchmidt_tsum_eq_adjoint` : the Hilbert–Schmidt sums of a map and its adjoint
  agree, as extended reals.
* `deningerIsHilbertSchmidtOn_adjoint_iff`, `deningerIsHilbertSchmidtOn_basis_independent` : the
  condition transfers to the adjoint and does not depend on the basis.
-/

namespace RHTower

open ContinuousLinearMap

open scoped ENNReal NNReal

section Parseval

variable {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The coefficients of a vector in a Hilbert basis are square-summable.** -/
theorem deningerParseval_summable (b : HilbertBasis ι ℂ H) (x : H) :
    Summable fun i => ‖(inner ℂ (b i) x : ℂ)‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := (lp.memℓp (b.repr x)).summable hp
  have htwo : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [htwo] at h
  simp only [Real.rpow_natCast] at h
  simpa [HilbertBasis.repr_apply_apply] using h

/-- **Parseval's identity for a Hilbert basis.** -/
theorem deningerParseval (b : HilbertBasis ι ℂ H) (x : H) :
    ∑' i, ‖(inner ℂ (b i) x : ℂ)‖ ^ 2 = ‖x‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (b.repr x)
  have htwo : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [htwo] at h
  simp only [Real.rpow_natCast] at h
  rw [LinearIsometryEquiv.norm_map] at h
  rw [h]
  exact tsum_congr fun i => by rw [HilbertBasis.repr_apply_apply]

end Parseval

section AdjointSum

variable {ι κ : Type} {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

omit [CompleteSpace H₁] in
/-- The squared norm of a vector as an extended real, expanded in a Hilbert basis. -/
theorem deningerParseval_ennreal (b : HilbertBasis ι ℂ H₁) (x : H₁) :
    ∑' i, ((‖(inner ℂ (b i) x : ℂ)‖₊ : ℝ≥0∞)) ^ 2
      = ((‖x‖₊ : ℝ≥0∞)) ^ 2 := by
  have hsum : Summable fun i => ‖(inner ℂ (b i) x : ℂ)‖ ^ 2 := deningerParseval_summable b x
  have hnn : HasSum (fun i => (‖(inner ℂ (b i) x : ℂ)‖₊) ^ 2) ((‖x‖₊) ^ 2) := by
    rw [← NNReal.hasSum_coe]
    have : ((fun i => ((‖(inner ℂ (b i) x : ℂ)‖₊ ^ 2 : ℝ≥0) : ℝ)))
        = fun i => ‖(inner ℂ (b i) x : ℂ)‖ ^ 2 := by
      funext i
      push_cast
      rfl
    rw [this]
    have : (((‖x‖₊ ^ 2 : ℝ≥0) : ℝ)) = ‖x‖ ^ 2 := by
      push_cast
      rfl
    rw [this, ← deningerParseval b x]
    exact hsum.hasSum
  have hcast : ∀ r : ℝ≥0, ((r ^ 2 : ℝ≥0) : ℝ≥0∞) = (r : ℝ≥0∞) ^ 2 := by
    intro r
    push_cast
    ring
  calc ∑' i, ((‖(inner ℂ (b i) x : ℂ)‖₊ : ℝ≥0∞)) ^ 2
      = ∑' i, ((‖(inner ℂ (b i) x : ℂ)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) :=
        tsum_congr fun i => (hcast _).symm
    _ = ((‖x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.tsum_coe_eq hnn
    _ = ((‖x‖₊ : ℝ≥0∞)) ^ 2 := hcast _

/-- **The Hilbert–Schmidt sum of a map equals that of its adjoint.**  Both are the sum of the
squared absolute values of the matrix coefficients, in the two possible orders. -/
theorem deningerHilbertSchmidt_tsum_eq_adjoint (A : H₁ →L[ℂ] H₂)
    (b : HilbertBasis ι ℂ H₁) (c : HilbertBasis κ ℂ H₂) :
    ∑' i, ((‖A (b i)‖₊ : ℝ≥0∞)) ^ 2
      = ∑' j, ((‖ContinuousLinearMap.adjoint A (c j)‖₊ : ℝ≥0∞)) ^ 2 := by
  have hleft : ∀ i, ((‖A (b i)‖₊ : ℝ≥0∞)) ^ 2
      = ∑' j, ((‖(inner ℂ (c j) (A (b i)) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 :=
    fun i => (deningerParseval_ennreal c (A (b i))).symm
  have hright : ∀ j, ((‖ContinuousLinearMap.adjoint A (c j)‖₊ : ℝ≥0∞)) ^ 2
      = ∑' i, ((‖(inner ℂ (b i)
        (ContinuousLinearMap.adjoint A (c j)) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 :=
    fun j => (deningerParseval_ennreal b (ContinuousLinearMap.adjoint A (c j))).symm
  have hcoeff : ∀ i j,
      ((‖(inner ℂ (c j) (A (b i)) : ℂ)‖₊ : ℝ≥0∞))
      = ((‖(inner ℂ (b i) (ContinuousLinearMap.adjoint A (c j)) : ℂ)‖₊ : ℝ≥0∞)) :=
      by
    intro i j
    have hreal : ‖(inner ℂ (c j) (A (b i)) : ℂ)‖
        = ‖(inner ℂ (b i) (ContinuousLinearMap.adjoint A (c j)) : ℂ)‖ := by
      rw [← ContinuousLinearMap.adjoint_inner_left A (b i) (c j)]
      exact norm_inner_symm _ _
    exact congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) (NNReal.coe_injective hreal)
  calc ∑' i, ((‖A (b i)‖₊ : ℝ≥0∞)) ^ 2
      = ∑' i, ∑' j, ((‖(inner ℂ (c j) (A (b i)) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 :=
        tsum_congr hleft
    _ = ∑' j, ∑' i, ((‖(inner ℂ (c j) (A (b i)) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 :=
        ENNReal.tsum_comm
    _ = ∑' j, ∑' i,
          ((‖(inner ℂ (b i)
            (ContinuousLinearMap.adjoint A (c j)) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 :=
        tsum_congr fun j => tsum_congr fun i => by rw [hcoeff i j]
    _ = ∑' j, ((‖ContinuousLinearMap.adjoint A (c j)‖₊ : ℝ≥0∞)) ^ 2 :=
        (tsum_congr hright).symm

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem deningerIsHilbertSchmidtOn_iff_tsum_ne_top (A : H₁ →L[ℂ] H₂)
    (b : HilbertBasis ι ℂ H₁) :
    DeningerIsHilbertSchmidtOn b A ↔ ∑' i, ((‖A (b i)‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤ := by
  rw [DeningerIsHilbertSchmidtOn]
  have hcoe : (fun i => ((‖A (b i)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞))
      = fun i => ((‖A (b i)‖₊ : ℝ≥0∞)) ^ 2 := by
    funext i
    push_cast
    ring
  rw [← hcoe, ENNReal.tsum_coe_ne_top_iff_summable]
  constructor
  · intro h
    rw [← NNReal.summable_coe] at *
    refine h.congr fun i => ?_
    push_cast
    rfl
  · intro h
    rw [← NNReal.summable_coe] at h
    refine h.congr fun i => ?_
    push_cast
    rfl

/-- **The Hilbert–Schmidt condition transfers to the adjoint.** -/
theorem deningerIsHilbertSchmidtOn_adjoint_iff (A : H₁ →L[ℂ] H₂)
    (b : HilbertBasis ι ℂ H₁) (c : HilbertBasis κ ℂ H₂) :
    DeningerIsHilbertSchmidtOn b A ↔
      DeningerIsHilbertSchmidtOn c (ContinuousLinearMap.adjoint A) := by
  rw [deningerIsHilbertSchmidtOn_iff_tsum_ne_top, deningerIsHilbertSchmidtOn_iff_tsum_ne_top,
    deningerHilbertSchmidt_tsum_eq_adjoint A b c]

/-- **The Hilbert–Schmidt condition does not depend on the basis.** -/
theorem deningerIsHilbertSchmidtOn_basis_independent (A : H₁ →L[ℂ] H₂)
    (b b' : HilbertBasis ι ℂ H₁) (c : HilbertBasis κ ℂ H₂) :
    DeningerIsHilbertSchmidtOn b A ↔ DeningerIsHilbertSchmidtOn b' A := by
  rw [deningerIsHilbertSchmidtOn_adjoint_iff A b c,
    deningerIsHilbertSchmidtOn_adjoint_iff A b' c]

end AdjointSum

end RHTower

