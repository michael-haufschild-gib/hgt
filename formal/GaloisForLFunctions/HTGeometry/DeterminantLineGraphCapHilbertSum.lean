import GaloisForLFunctions.HTGeometry.DeterminantLineGraphCapHolonomy

/-!
# The graph cap of an operator between two Hilbert spaces

For a Hilbert–Schmidt `A : E → F` the graph cap `z ↦ graph(zA)` lives in the restricted
Grassmannian of the Hilbert sum `E ⊕ F` polarized by the projection onto `E`; it is the cap of the
block operator `Â = ι_F A π_E`.  Since `Â*Â = ι_E K π_E` with `K = A*A`, the inverse of `1 + Â*Â`
is `ι_E (1 + K)⁻¹ π_E + (1 − ι_E π_E)` and cyclicity of the trace across the two spaces gives
`Tr(K̂(1 + K̂)⁻¹) = Tr(K(1 + K)⁻¹)` (`graphCapArea_graphBlockOp`).  Hence, for every Hilbert–Schmidt
`A : E → F`:

* `integral_graphCapKahler`: `∫_D Γ_A^* ω_det = Tr(K(I + K)⁻¹) = E(A)`;
* `edgeHol_graphCapBoundary`: `Hol(∂Γ_A) = exp(2πi E(A))`;
* `graphCapBoundary_unique_lift`: if `E(A) < 1`, `E(A)` is the unique lift in `[0, 1)`.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## The orthogonal sum `E ⊕ F` -/

section Block

variable (E F) in
/-- The inclusion of `E` into the Hilbert sum `E ⊕ F`. -/
def sumInl : E →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ E F

variable (E F) in
/-- The inclusion of `F` into the Hilbert sum `E ⊕ F`. -/
def sumInr : F →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ E F

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem sumInl_fst (x : E) : (sumInl E F x).fst = x := rfl
omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem sumInl_snd (x : E) : (sumInl E F x).snd = 0 := rfl
omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem sumInr_fst (y : F) : (sumInr E F y).fst = 0 := rfl
omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem sumInr_snd (y : F) : (sumInr E F y).snd = y := rfl

theorem adjoint_sumInl : adjoint (sumInl E F) = WithLp.fstL 2 ℂ E F :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun w x => by
    simp [WithLp.prod_inner_apply]).symm

theorem adjoint_sumInr : adjoint (sumInr E F) = WithLp.sndL 2 ℂ E F :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun w y => by
    simp [WithLp.prod_inner_apply]).symm

omit [CompleteSpace E] [CompleteSpace F] in
theorem fstL_comp_sumInl : WithLp.fstL 2 ℂ E F ∘L sumInl E F = ContinuousLinearMap.id ℂ E := by
  ext x; rfl
omit [CompleteSpace E] [CompleteSpace F] in
theorem fstL_comp_sumInr : WithLp.fstL 2 ℂ E F ∘L sumInr E F = 0 := by ext x; rfl
omit [CompleteSpace E] [CompleteSpace F] in
theorem sndL_comp_sumInr : WithLp.sndL 2 ℂ E F ∘L sumInr E F = ContinuousLinearMap.id ℂ F := by
  ext x; rfl

variable (E F) in
/-- The polarization `P₊` of `E ⊕ F`: the orthogonal projection onto `E`. -/
def sumPol : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) := sumInl E F ∘L WithLp.fstL 2 ℂ E F

theorem isStarProjection_sumPol : IsStarProjection (sumPol E F) := by
  refine ⟨?_, ?_⟩
  · change sumInl E F ∘L WithLp.fstL 2 ℂ E F ∘L (sumInl E F ∘L WithLp.fstL 2 ℂ E F) = _
    rw [← ContinuousLinearMap.comp_assoc (WithLp.fstL 2 ℂ E F), fstL_comp_sumInl,
      ContinuousLinearMap.id_comp]
    rfl
  · rw [IsSelfAdjoint, star_eq_adjoint, sumPol, adjoint_comp, adjoint_sumInl, ← adjoint_sumInl,
      adjoint_adjoint]

/-- The block operator `Â = ι_F A π_E` of `A : E → F` on `E ⊕ F`. -/
def graphBlockOp (A : E →L[ℂ] F) : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  sumInr E F ∘L A ∘L WithLp.fstL 2 ℂ E F

theorem isHilbertSchmidt_graphBlockOp {A : E →L[ℂ] F} (hA : IsHilbertSchmidt A) :
    IsHilbertSchmidt (graphBlockOp A) := by
  unfold graphBlockOp
  exact (hA.comp_right (WithLp.fstL 2 ℂ E F)).comp_left (sumInr E F)

omit [CompleteSpace E] [CompleteSpace F] in
theorem sumPol_mul_graphBlockOp (A : E →L[ℂ] F) : sumPol E F * graphBlockOp A = 0 := by
  change sumInl E F ∘L WithLp.fstL 2 ℂ E F ∘L (sumInr E F ∘L A ∘L WithLp.fstL 2 ℂ E F) = 0
  rw [← ContinuousLinearMap.comp_assoc (WithLp.fstL 2 ℂ E F), fstL_comp_sumInr]
  simp

omit [CompleteSpace E] [CompleteSpace F] in
theorem graphBlockOp_mul_sumPol (A : E →L[ℂ] F) : graphBlockOp A * sumPol E F = graphBlockOp A := by
  change sumInr E F ∘L A ∘L WithLp.fstL 2 ℂ E F ∘L (sumInl E F ∘L WithLp.fstL 2 ℂ E F) = _
  rw [← ContinuousLinearMap.comp_assoc (WithLp.fstL 2 ℂ E F), fstL_comp_sumInl,
    ContinuousLinearMap.id_comp]
  rfl

end Block


/-! ## The graph-cap area of the block operator -/

section Area

variable {A : E →L[ℂ] F}

theorem adjoint_graphBlockOp_mul_graphBlockOp (A : E →L[ℂ] F) :
    adjoint (graphBlockOp A) * graphBlockOp A =
      sumInl E F ∘L (adjoint A ∘L A) ∘L WithLp.fstL 2 ℂ E F := by
  have h1 : adjoint (WithLp.fstL 2 ℂ E F) = sumInl E F := by
    rw [← adjoint_sumInl, adjoint_adjoint]
  change adjoint (sumInr E F ∘L A ∘L WithLp.fstL 2 ℂ E F) ∘L
    (sumInr E F ∘L A ∘L WithLp.fstL 2 ℂ E F) = _
  simp only [adjoint_comp, h1, adjoint_sumInr, ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc (WithLp.sndL 2 ℂ E F) (sumInr E F), sndL_comp_sumInr,
    ContinuousLinearMap.id_comp]

/-- **The graph cap of `A : E → F` is that of its block operator on `E ⊕ F`**:
`Tr(K̂(1 + K̂)⁻¹) = Tr(K(1 + K)⁻¹)` for `K̂ = Â*Â = ι K π`. -/
theorem opTrace_resolventRatio_graphBlockOp (hA : IsHilbertSchmidt A) :
    opTrace (resolventRatio (adjoint (graphBlockOp A) ∘L graphBlockOp A)) =
      opTrace (resolventRatio (adjoint A ∘L A)) := by
  set J := sumInl E F
  set π := WithLp.fstL 2 ℂ E F
  set K := adjoint A ∘L A
  set R := Ring.inverse (1 + K)
  have hu : IsUnit (1 + K) := isUnit_one_add_adjoint_comp_self hA
  have hR1 : R * (1 + K) = 1 := Ring.inverse_mul_cancel _ hu
  have hR2 : (1 + K) * R = 1 := Ring.mul_inverse_cancel _ hu
  have hπJ : π ∘L J = ContinuousLinearMap.id ℂ E := fstL_comp_sumInl
  -- the operators `P = Jπ`, `K̂ = JKπ`, `R̂ = JRπ` on `E ⊕ F`
  set P : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) := J ∘L π
  set Kh : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) := J ∘L K ∘L π
  set Rh : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) := J ∘L R ∘L π
  have sandwich : ∀ X Y : E →L[ℂ] E, (J ∘L X ∘L π) * (J ∘L Y ∘L π) = J ∘L (X * Y) ∘L π := by
    intro X Y
    change (J ∘L X ∘L π) ∘L (J ∘L Y ∘L π) = J ∘L (X ∘L Y) ∘L π
    simp only [ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc π J, hπJ, ContinuousLinearMap.id_comp]
  have hP : P = J ∘L 1 ∘L π := by rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  have hKP : Kh * P = Kh := by rw [hP, sandwich, mul_one]
  have hPK : P * Kh = Kh := by rw [hP, sandwich, one_mul]
  have e1 : R + R * K = 1 := by rw [← hR1]; noncomm_ring
  have e2 : R + K * R = 1 := by rw [← hR2]; noncomm_ring
  have hRK : Rh + Rh * Kh = P := by
    rw [sandwich, hP, ← ContinuousLinearMap.comp_add, ← ContinuousLinearMap.add_comp, e1]
  have hKR : Rh + Kh * Rh = P := by
    rw [sandwich, hP, ← ContinuousLinearMap.comp_add, ← ContinuousLinearMap.add_comp, e2]
  have hKh : adjoint (graphBlockOp A) ∘L graphBlockOp A = Kh :=
    adjoint_graphBlockOp_mul_graphBlockOp A
  -- the inverse of `1 + K̂`
  have hinv : Ring.inverse (1 + Kh) = Rh + (1 - P) := by
    have h1 : (1 + Kh) * (Rh + (1 - P)) = 1 := by
      rw [add_mul, one_mul, mul_add, mul_sub, mul_one, hKP, sub_self, add_zero,
        show Rh + (1 - P) + Kh * Rh = (Rh + Kh * Rh) + 1 - P by abel, hKR]
      abel
    have h2 : (Rh + (1 - P)) * (1 + Kh) = 1 := by
      rw [mul_add, mul_one, add_mul, sub_mul, one_mul, hPK, sub_self, add_zero,
        show Rh + (1 - P) + Rh * Kh = (Rh + Rh * Kh) + 1 - P by abel, hRK]
      abel
    exact Ring.inverse_unit ⟨1 + Kh, Rh + (1 - P), h1, h2⟩
  have hratio : resolventRatio Kh = J ∘L (K * R) ∘L π := by
    rw [resolventRatio, hinv, mul_add, mul_sub, mul_one, hKP, sub_self, add_zero, sandwich]
  rw [hKh, hratio, resolventRatio]
  -- cyclicity of the trace across the spaces
  have hAR : K * R = adjoint A ∘L (A ∘L R) := rfl
  have hL : opTrace (J ∘L (K * R) ∘L π) =
      opTrace ((A ∘L R ∘L π) ∘L (J ∘L adjoint A)) := by
    rw [hAR, show J ∘L (adjoint A ∘L (A ∘L R)) ∘L π = (J ∘L adjoint A) ∘L (A ∘L R ∘L π) by
      simp only [ContinuousLinearMap.comp_assoc]]
    exact opTrace_comp_comm (hA.adjoint.comp_left J) ((hA.comp_right R).comp_right π)
  have hR' : opTrace (K * R) = opTrace ((A ∘L R) ∘L adjoint A) := by
    rw [hAR]; exact opTrace_comp_comm hA.adjoint (hA.comp_right R)
  rw [hL, hR', show (A ∘L R ∘L π) ∘L (J ∘L adjoint A) = (A ∘L R) ∘L adjoint A by
    simp only [ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc π J, hπJ, ContinuousLinearMap.id_comp]]

theorem graphCapArea_graphBlockOp (hA : IsHilbertSchmidt A) :
    graphCapArea (graphBlockOp A) (isHilbertSchmidt_graphBlockOp hA) = graphCapArea A hA := by
  haveI : Fact (IsCompactOperator (adjoint A ∘L A)) := ⟨isCompactOperator_adjoint_comp_self hA⟩
  haveI : Fact (IsCompactOperator (adjoint (graphBlockOp A) ∘L graphBlockOp A)) :=
    ⟨isCompactOperator_adjoint_comp_self (isHilbertSchmidt_graphBlockOp hA)⟩
  have h1 := (graphCapArea_eq (isHilbertSchmidt_graphBlockOp hA)).2.1
  have h2 := (graphCapArea_eq hA).2.1
  rw [opTrace_resolventRatio_graphBlockOp hA, h2] at h1
  exact_mod_cast h1.symm

end Area


/-! ## Holonomy of the graph cap of `A : E → F` -/

section Holonomy

variable {A : E →L[ℂ] F}

variable (A) in
/-- The graph cap `z ↦ graph(zA) ⊆ E ⊕ F` in polar coordinates, as a square of the restricted
Grassmannian of the polarization `E ⊕ F`. -/
def graphCapSquare (hA : IsHilbertSchmidt A) : ℝ × ℝ → SLSpace (WithLp 2 (E × F)) :=
  capMap (sumPol E F) (graphBlockOp A) (isHilbertSchmidt_graphBlockOp hA)

variable (A) in
/-- The positively oriented boundary loop `θ ↦ graph(e^{2πiθ}A)` of the graph cap. -/
def graphCapBoundary (hA : IsHilbertSchmidt A) : ℝ → SLSpace (WithLp 2 (E × F)) :=
  capBoundary (sumPol E F) (graphBlockOp A) (isHilbertSchmidt_graphBlockOp hA)

/-- **(DLLA.2)** `∫_D Γ_A^* ω_det = Tr(K(I + K)⁻¹) = E(A)` for every Hilbert–Schmidt
`A : E → F`. -/
theorem integral_graphCapKahler (hA : IsHilbertSchmidt A) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      squareKahler (sumPol E F) (graphCapSquare A hA) (x, y) = graphCapArea A hA := by
  rw [graphCapSquare, integral_capKahler isStarProjection_sumPol (isHilbertSchmidt_graphBlockOp hA)
    (sumPol_mul_graphBlockOp A) (graphBlockOp_mul_sumPol A), graphCapArea_graphBlockOp hA]

/-- **Theorem DLLA-A.**  The determinant-line holonomy of the positively oriented boundary of the
graph cap `Γ_A` is `exp(2πi E(A))`. -/
theorem edgeHol_graphCapBoundary (hA : IsHilbertSchmidt A) :
    edgeHol (sumPol E F) (sumPol E F) (graphCapBoundary A hA) =
      Complex.exp (2 * Real.pi * Complex.I * graphCapArea A hA) := by
  rw [graphCapBoundary, edgeHol_capBoundary isStarProjection_sumPol
    (isHilbertSchmidt_graphBlockOp hA) (sumPol_mul_graphBlockOp A) (graphBlockOp_mul_sumPol A),
    graphCapArea_graphBlockOp hA]

/-- **Theorem DLLA-A, principal lift.**  If `E(A) < 1`, then `E(A)` is the unique `x ∈ [0, 1)`
with `exp(2πi x) = Hol(∂Γ_A)`. -/
theorem graphCapBoundary_unique_lift (hA : IsHilbertSchmidt A) (hlt : graphCapArea A hA < 1)
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hxe : Complex.exp (2 * Real.pi * Complex.I * x) =
      edgeHol (sumPol E F) (sumPol E F) (graphCapBoundary A hA)) :
    x = graphCapArea A hA := by
  have h := capBoundary_unique_lift isStarProjection_sumPol (isHilbertSchmidt_graphBlockOp hA)
    (sumPol_mul_graphBlockOp A) (graphBlockOp_mul_sumPol A)
    (by rw [graphCapArea_graphBlockOp hA]; exact hlt) hx hxe
  rwa [graphCapArea_graphBlockOp hA] at h

end Holonomy

end

end GaloisForLFunctions.HTGeometry
