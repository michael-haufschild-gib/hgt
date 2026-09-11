import GaloisForLFunctions.HTGeometry.KukolComplexDiagonalOrbits

/-!
# Exact quotient coordinates of the saturated future tube

Kukol's complex unipotent action (arXiv:2609.10214, Sections 3 and 5)
admits an exact single-point saturation criterion in every finite transverse
dimension. The imaginary Lorentz margin is an invariant maximum minus a
sum of squares. The whole saturated domain is parametrized bijectively by
two upper half-planes and a free transverse complex vector.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {κ : Type*} [Fintype κ]

/-- A single transverse square has an exact nonpositive imaginary Lorentz defect. -/
theorem kukolComplex_square_defect (m : ℂˣ) (z : ℂ) :
    (m : ℂ).im*(z^2/(m : ℂ)).im-z.im^2 =
      -(((m : ℂ).im*z.re-(m : ℂ).re*z.im)^2/Complex.normSq (m : ℂ)) := by
  have hm : Complex.normSq (m : ℂ) ≠ 0 := (Complex.normSq_pos.mpr m.ne_zero).ne'
  simp only [Complex.div_im,pow_two,Complex.mul_im,Complex.mul_re]
  field_simp
  rw [Complex.normSq_apply]
  ring

/-- The invariant divided by the nonzero minus coordinate is a global quotient coordinate. -/
def kukolRegularQuotientCoordinate (x : KukolRegularPoint κ) : ℂ :=
  kukolRegularQuadratic x/(x.minus : ℂ)

theorem kukolRegularQuotientCoordinate_eq (x : KukolRegularPoint κ) :
    kukolRegularQuotientCoordinate x = x.plus-∑ k,x.transverse k^2/(x.minus : ℂ) := by
  rw [← Finset.sum_div]
  dsimp [kukolRegularQuotientCoordinate,kukolRegularQuadratic]
  field_simp

/-- This quotient coordinate is invariant under the entire complex unipotent group. -/
theorem kukolRegularQuotientCoordinate_action (u : κ → ℂ) (x : KukolRegularPoint κ) :
    kukolRegularQuotientCoordinate (kukolRegularAction u x)=kukolRegularQuotientCoordinate x := by
  unfold kukolRegularQuotientCoordinate
  rw [kukolRegularQuadratic_action]
  rfl

/-- The Lorentz margin of the imaginary part, in arbitrary transverse dimension. -/
def kukolRegularImaginaryMargin (x : KukolRegularPoint κ) : ℝ :=
  (x.minus : ℂ).im*x.plus.im-∑ k,(x.transverse k).im^2

/-- The imaginary-part margin is its orbit maximum minus an explicit sum of squares. -/
theorem kukolRegularImaginaryMargin_decomposition (x : KukolRegularPoint κ) :
    kukolRegularImaginaryMargin x = (x.minus : ℂ).im*(kukolRegularQuotientCoordinate x).im-
      ∑ k,((x.minus : ℂ).im*(x.transverse k).re-
        (x.minus : ℂ).re*(x.transverse k).im)^2/Complex.normSq (x.minus : ℂ) := by
  have hs := congrArg (fun f : κ → ℝ => ∑ k,f k)
    (funext (fun k => kukolComplex_square_defect x.minus (x.transverse k)))
  simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib,← Finset.mul_sum] at hs
  have hi : (∑ k,x.transverse k^2/(x.minus : ℂ)).im =
      ∑ k,(x.transverse k^2/(x.minus : ℂ)).im :=
    map_sum Complex.imAddGroupHom _ _
  rw [kukolRegularQuotientCoordinate_eq,Complex.sub_im,hi]
  dsimp [kukolRegularImaginaryMargin]
  linear_combination hs

/-- Future-tube membership is the strict Lorentz condition on the imaginary part. -/
def kukolRegularFutureTube : Set (KukolRegularPoint κ) :=
  {x | 0 < (x.minus : ℂ).im ∧ 0 < kukolRegularImaginaryMargin x}

/-- The complex unipotent saturation of the entire regular future tube. -/
def kukolRegularTubeSaturation : Set (KukolRegularPoint κ) :=
  {x | ∃ u : κ → ℂ,kukolRegularAction u x ∈ kukolRegularFutureTube}

/-- The zero-transverse representative has the invariant quotient coordinate as its plus coordinate. -/
def kukolRegularCanonical (x : KukolRegularPoint κ) : KukolRegularPoint κ :=
  ⟨x.minus,kukolRegularQuotientCoordinate x,0⟩

/-- Every complex orbit reaches this representative by the explicitly displayed parameter. -/
theorem kukolRegularAction_canonical (x : KukolRegularPoint κ) :
    kukolRegularAction (fun k => -x.transverse k/(x.minus : ℂ)) x =
      kukolRegularCanonical x := by
  apply (kukolRegularPoint_eq_iff _ _).mpr
  refine ⟨rfl,?_,?_⟩
  · rw [kukolRegularQuadratic_action]
    dsimp [kukolRegularCanonical,kukolRegularQuadratic,kukolRegularQuotientCoordinate]
    simp only [zero_pow two_ne_zero,Finset.sum_const_zero,sub_zero]
    field_simp
  · funext k
    dsimp [kukolRegularAction,kukolRegularCanonical]
    field_simp
    ring

/-- Exact saturation criterion: the two invariant complex coordinates independently lie in the upper half-plane. -/
theorem kukolRegularTubeSaturation_iff (x : KukolRegularPoint κ) :
    x ∈ kukolRegularTubeSaturation ↔
      0 < (x.minus : ℂ).im ∧ 0 < (kukolRegularQuotientCoordinate x).im := by
  constructor
  · rintro ⟨u,hm,hmargin⟩
    have hnonneg : 0 ≤ ∑ k,
        ((kukolRegularAction u x).minus.val.im*((kukolRegularAction u x).transverse k).re-
          (kukolRegularAction u x).minus.val.re*((kukolRegularAction u x).transverse k).im)^2/
            Complex.normSq (kukolRegularAction u x).minus.val :=
      Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
    rw [kukolRegularImaginaryMargin_decomposition,kukolRegularQuotientCoordinate_action] at hmargin
    refine ⟨hm,?_⟩
    have hp : 0 < (x.minus : ℂ).im*(kukolRegularQuotientCoordinate x).im := by
      dsimp [kukolRegularAction] at hmargin hnonneg
      linarith
    exact pos_of_mul_pos_right hp hm.le
  · rintro ⟨hm,hq⟩
    refine ⟨fun k => -x.transverse k/(x.minus : ℂ),?_⟩
    rw [kukolRegularAction_canonical]
    refine ⟨hm,?_⟩
    simpa [kukolRegularCanonical,kukolRegularImaginaryMargin] using mul_pos hm hq

/-- Explicit coordinates on the saturated tube: two upper half-planes and a free complex transverse vector. -/
def kukolTubeParameters (m h : UpperHalfPlane) (z : κ → ℂ) : KukolRegularPoint κ :=
  ⟨Units.mk0 (m : ℂ) m.ne_zero,(h : ℂ)+(∑ k,z k^2)/(m : ℂ),z⟩

theorem kukolTubeParameters_quotient (m h : UpperHalfPlane) (z : κ → ℂ) :
    kukolRegularQuotientCoordinate (kukolTubeParameters m h z)=(h : ℂ) := by
  have hm : (m : ℂ) ≠ 0 := m.ne_zero
  dsimp [kukolRegularQuotientCoordinate,kukolRegularQuadratic,kukolTubeParameters]
  field_simp [hm]
  ring

/-- The parameterization covers exactly the entire saturated domain. -/
theorem kukolTubeParameters_range :
    Set.range (fun p : UpperHalfPlane × UpperHalfPlane × (κ → ℂ) =>
      kukolTubeParameters p.1 p.2.1 p.2.2)=kukolRegularTubeSaturation := by
  ext x
  constructor
  · rintro ⟨⟨m,h,z⟩,rfl⟩
    rw [kukolRegularTubeSaturation_iff,kukolTubeParameters_quotient]
    exact ⟨m.im_pos,h.im_pos⟩
  · intro hx
    obtain ⟨hm,hq⟩ := (kukolRegularTubeSaturation_iff x).mp hx
    refine ⟨(UpperHalfPlane.mk (x.minus : ℂ) hm,
      UpperHalfPlane.mk (kukolRegularQuotientCoordinate x) hq,x.transverse),?_⟩
    apply KukolRegularPoint.ext
    · apply Units.ext
      rfl
    · dsimp [kukolTubeParameters,kukolRegularQuotientCoordinate,kukolRegularQuadratic]
      field_simp
      ring
    · rfl

end GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {κ : Type*} [Fintype κ]

/-- The saturated tube has unique coordinates in two upper half-planes and the transverse vector space. -/
def kukolTubeParameterEquiv :
    (UpperHalfPlane × UpperHalfPlane × (κ → ℂ)) ≃
      {x : KukolRegularPoint κ | x ∈ kukolRegularTubeSaturation} where
  toFun p := ⟨kukolTubeParameters p.1 p.2.1 p.2.2,by
    change kukolTubeParameters p.1 p.2.1 p.2.2 ∈ kukolRegularTubeSaturation
    rw [kukolRegularTubeSaturation_iff,kukolTubeParameters_quotient]
    exact ⟨p.1.im_pos,p.2.1.im_pos⟩⟩
  invFun x := (UpperHalfPlane.mk (x.val.minus : ℂ) ((kukolRegularTubeSaturation_iff x.val).mp x.property).1,
    UpperHalfPlane.mk (kukolRegularQuotientCoordinate x.val)
      ((kukolRegularTubeSaturation_iff x.val).mp x.property).2,x.val.transverse)
  left_inv p := by
    apply Prod.ext
    · apply UpperHalfPlane.ext
      rfl
    · apply Prod.ext
      · apply UpperHalfPlane.ext
        exact kukolTubeParameters_quotient p.1 p.2.1 p.2.2
      · rfl
  right_inv x := by
    apply Subtype.ext
    apply KukolRegularPoint.ext
    · apply Units.ext
      rfl
    · dsimp [kukolTubeParameters,kukolRegularQuotientCoordinate,kukolRegularQuadratic]
      field_simp
      ring
    · rfl

end GaloisForLFunctions.HTGeometry
