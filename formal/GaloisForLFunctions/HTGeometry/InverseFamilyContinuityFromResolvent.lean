import GaloisForLFunctions.HTGeometry.InverseFamilyThirdDerivative

/-!
# Continuity of the expansion amplitudes from the resolvent alone

The amplitudes `D₀,…,∂D₂` of the three-fold expansion are polynomial expressions in the resolvent
`C⁻¹` and the symbol jets `C₁,C₂,C₃`.  Their continuity therefore needs nothing about *why* the
resolvent is continuous — only that it is.  Stating the chain that way lets the same lemmas serve
two different variables: the position, where the resolvent is continuous because the generator is
differentiable, and the frequency, where it is continuous because inversion is.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Set

variable {R : Type*} [NormedRing R]
variable {C C₁ C₂ C₃ : ℝ → R} {S : Set ℝ}

theorem continuousOn_invFamilyDeriv_of_resolvent (hD : ContinuousOn (invFamily C) S)
    (hC₁ : ContinuousOn C₁ S) : ContinuousOn (invFamilyDeriv C C₁) S := by
  have h : ContinuousOn (fun s => -(invFamily C s * C₁ s * invFamily C s)) S :=
    ((hD.mul hC₁).mul hD).neg
  exact h

theorem continuousOn_invFamilyDeriv2_of_resolvent (hD : ContinuousOn (invFamily C) S)
    (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) :
    ContinuousOn (invFamilyDeriv2 C C₁ C₂) S := by
  have h : ContinuousOn (fun s =>
      invFamily C s * C₁ s * invFamily C s * C₁ s * invFamily C s
        + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamily C s
        - invFamily C s * C₂ s * invFamily C s) S :=
    ((((hD.mul hC₁).mul hD).mul hC₁).mul hD).add
      ((((hD.mul hC₁).mul hD).mul hC₁).mul hD) |>.sub ((hD.mul hC₂).mul hD)
  exact h

theorem continuousOn_invFamilyDeriv3_of_resolvent (hD : ContinuousOn (invFamily C) S)
    (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) (hC₃ : ContinuousOn C₃ S) :
    ContinuousOn (invFamilyDeriv3 C C₁ C₂ C₃) S := by
  have hDd := continuousOn_invFamilyDeriv_of_resolvent hD hC₁
  have t1 : ContinuousOn (fun s =>
      invFamilyDeriv C C₁ s * C₁ s * invFamily C s * C₁ s * invFamily C s) S :=
    (((hDd.mul hC₁).mul hD).mul hC₁).mul hD
  have t2 : ContinuousOn (fun s =>
      invFamily C s * C₂ s * invFamily C s * C₁ s * invFamily C s) S :=
    (((hD.mul hC₂).mul hD).mul hC₁).mul hD
  have t3 : ContinuousOn (fun s =>
      invFamily C s * C₁ s * invFamilyDeriv C C₁ s * C₁ s * invFamily C s) S :=
    (((hD.mul hC₁).mul hDd).mul hC₁).mul hD
  have t4 : ContinuousOn (fun s =>
      invFamily C s * C₁ s * invFamily C s * C₂ s * invFamily C s) S :=
    (((hD.mul hC₁).mul hD).mul hC₂).mul hD
  have t5 : ContinuousOn (fun s =>
      invFamily C s * C₁ s * invFamily C s * C₁ s * invFamilyDeriv C C₁ s) S :=
    (((hD.mul hC₁).mul hD).mul hC₁).mul hDd
  have t6 : ContinuousOn (fun s =>
      invFamilyDeriv C C₁ s * C₂ s * invFamily C s) S := (hDd.mul hC₂).mul hD
  have t7 : ContinuousOn (fun s =>
      invFamily C s * C₃ s * invFamily C s) S := (hD.mul hC₃).mul hD
  have t8 : ContinuousOn (fun s =>
      invFamily C s * C₂ s * invFamilyDeriv C C₁ s) S := (hD.mul hC₂).mul hDd
  have h : ContinuousOn (fun s =>
      (invFamilyDeriv C C₁ s * C₁ s * invFamily C s * C₁ s * invFamily C s
          + invFamily C s * C₂ s * invFamily C s * C₁ s * invFamily C s
          + invFamily C s * C₁ s * invFamilyDeriv C C₁ s * C₁ s * invFamily C s
          + invFamily C s * C₁ s * invFamily C s * C₂ s * invFamily C s
          + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamilyDeriv C C₁ s)
        + (invFamilyDeriv C C₁ s * C₁ s * invFamily C s * C₁ s * invFamily C s
          + invFamily C s * C₂ s * invFamily C s * C₁ s * invFamily C s
          + invFamily C s * C₁ s * invFamilyDeriv C C₁ s * C₁ s * invFamily C s
          + invFamily C s * C₁ s * invFamily C s * C₂ s * invFamily C s
          + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamilyDeriv C C₁ s)
        - (invFamilyDeriv C C₁ s * C₂ s * invFamily C s
          + invFamily C s * C₃ s * invFamily C s
          + invFamily C s * C₂ s * invFamilyDeriv C C₁ s)) S :=
    ((((((t1.add t2).add t3).add t4).add t5).add
      (((((t1.add t2).add t3).add t4).add t5))).sub ((t6.add t7).add t8))
  exact h

theorem continuousOn_invFamilyProductDeriv_of_resolvent (hD : ContinuousOn (invFamily C) S)
    (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) :
    ContinuousOn (invFamilyProductDeriv C C₁ C₂) S := by
  have hDd := continuousOn_invFamilyDeriv_of_resolvent hD hC₁
  have hD2 := continuousOn_invFamilyDeriv2_of_resolvent hD hC₁ hC₂
  have h : ContinuousOn (fun s =>
      invFamilyDeriv C C₁ s * invFamilyDeriv C C₁ s
        + invFamily C s * invFamilyDeriv2 C C₁ C₂ s) S := (hDd.mul hDd).add (hD.mul hD2)
  exact h

theorem continuousOn_invFamilyProductDeriv2_of_resolvent (hD : ContinuousOn (invFamily C) S)
    (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) (hC₃ : ContinuousOn C₃ S) :
    ContinuousOn (invFamilyProductDeriv2 C C₁ C₂ C₃) S := by
  have hDd := continuousOn_invFamilyDeriv_of_resolvent hD hC₁
  have hD2 := continuousOn_invFamilyDeriv2_of_resolvent hD hC₁ hC₂
  have hD3 := continuousOn_invFamilyDeriv3_of_resolvent hD hC₁ hC₂ hC₃
  have h : ContinuousOn (fun s =>
      invFamilyDeriv2 C C₁ C₂ s * invFamilyDeriv C C₁ s
        + invFamilyDeriv C C₁ s * invFamilyDeriv2 C C₁ C₂ s
        + invFamilyDeriv C C₁ s * invFamilyDeriv2 C C₁ C₂ s
        + invFamily C s * invFamilyDeriv3 C C₁ C₂ C₃ s) S :=
    (((hD2.mul hDd).add (hDd.mul hD2)).add (hDd.mul hD2)).add (hD.mul hD3)
  exact h

theorem continuousOn_invFamilyProduct2_of_resolvent (hD : ContinuousOn (invFamily C) S)
    (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) :
    ContinuousOn (invFamilyProduct2 C C₁ C₂) S := by
  have hP := continuousOn_invFamilyProductDeriv_of_resolvent hD hC₁ hC₂
  have h : ContinuousOn (fun s => invFamily C s * invFamilyProductDeriv C C₁ C₂ s) S := hD.mul hP
  exact h

/-- **The amplitude surviving three integrations by parts is continuous wherever the resolvent
is.** -/
theorem continuousOn_invFamilyProduct2Deriv_of_resolvent (hD : ContinuousOn (invFamily C) S)
    (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) (hC₃ : ContinuousOn C₃ S) :
    ContinuousOn (invFamilyProduct2Deriv C C₁ C₂ C₃) S := by
  have hDd := continuousOn_invFamilyDeriv_of_resolvent hD hC₁
  have hP := continuousOn_invFamilyProductDeriv_of_resolvent hD hC₁ hC₂
  have hP2 := continuousOn_invFamilyProductDeriv2_of_resolvent hD hC₁ hC₂ hC₃
  have h : ContinuousOn (fun s =>
      invFamilyDeriv C C₁ s * invFamilyProductDeriv C C₁ C₂ s
        + invFamily C s * invFamilyProductDeriv2 C C₁ C₂ C₃ s) S :=
    (hDd.mul hP).add (hD.mul hP2)
  exact h

end GaloisForLFunctions.HTGeometry
