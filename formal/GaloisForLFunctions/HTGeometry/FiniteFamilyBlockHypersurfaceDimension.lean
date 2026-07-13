import GaloisForLFunctions.HTGeometry.IteratedBlockHypersurfaceDimension

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The iterated coordinate ring obtained by imposing a finite family of equations in independent
copies of one variable block. -/
def finiteFamilyBlockHypersurfaceRing
    {row σ : Type} [Fintype row] (P : row → MvPolynomial σ ℂ) : CommAlgCat ℂ :=
  iteratedBlockHypersurfaceRing
    (List.ofFn fun i : Fin (Fintype.card row) => P ((Fintype.equivFin row).symm i))

/-- A finite family of nonconstant equations in independent variable blocks cuts iterated Krull
dimension by at least the cardinality of the family. -/
theorem finiteFamilyBlockHypersurfaceRing_krullDim_add_card_le
    {row σ : Type} [Fintype row] [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (P : row → MvPolynomial σ ℂ) (hP : ∀ b, ¬ IsConstantMvPolynomial (P b)) :
    ringKrullDim (finiteFamilyBlockHypersurfaceRing P) + Fintype.card row ≤
      Fintype.card row * Nat.card σ := by
  unfold finiteFamilyBlockHypersurfaceRing
  have hall : ∀ Q ∈
      (List.ofFn fun i : Fin (Fintype.card row) => P ((Fintype.equivFin row).symm i)),
      ¬ IsConstantMvPolynomial Q := by
    intro Q hQ
    rw [List.mem_ofFn] at hQ
    obtain ⟨i, rfl⟩ := hQ
    exact hP _
  simpa using iteratedBlockHypersurfaceRing_krullDim_add_length_le _ hall

end
end GaloisForLFunctions.HTGeometry
