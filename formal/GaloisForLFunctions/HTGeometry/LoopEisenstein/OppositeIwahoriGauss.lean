import GaloisForLFunctions.HTGeometry.LoopEisenstein.IwahoriGaussCoordinates

/-!
# Opposite Gauss factorization of positive Iwahori matrices

Inverting the lower–diagonal–upper factors of the inverse matrix gives
upper–diagonal–lower factors over the power-series ring. The lower root
parameter retains its zero constant coefficient.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable (F : Type*) [Field F]

/-- Every positive Iwahori matrix admits upper–diagonal–lower factors. -/
theorem exists_iwahori_upper_diagonal_lower (g : iwahoriMatrices F) :
    ∃ u : PowerSeries F, ∃ a : (PowerSeries F)ˣ, ∃ l : PowerSeries F,
      PowerSeries.constantCoeff l = 0 ∧
        FiniteRingSl2.upper u * powerSeriesDiagonal F a * FiniteRingSl2.lower l =
          (g : PowerSeriesSL2 F) := by
  let p := iwahoriCoordinates F g⁻¹
  refine ⟨-p.upper, p.diagonal⁻¹, -p.lower, ?_, ?_⟩
  · rw [map_neg, p.lower_constant, neg_zero]
  · have he := congrArg (fun h : iwahoriMatrices F => ((h : PowerSeriesSL2 F)⁻¹))
      (iwahoriCoordinates_toMatrix F g⁻¹)
    change (gaussMatrix F p.lower p.diagonal p.upper)⁻¹ =
      ((g : PowerSeriesSL2 F)⁻¹)⁻¹ at he
    rw [inv_inv] at he
    rw [← he]
    unfold gaussMatrix
    rw [mul_inv_rev, mul_inv_rev]
    have hu : (FiniteRingSl2.upper p.upper)⁻¹ = FiniteRingSl2.upper (-p.upper) :=
      (map_inv (FiniteRingSl2.upperHom (R := PowerSeries F)) (Multiplicative.ofAdd p.upper)).symm
    have hl : (FiniteRingSl2.lower p.lower)⁻¹ = FiniteRingSl2.lower (-p.lower) :=
      (map_inv (FiniteRingSl2.lowerHom (R := PowerSeries F)) (Multiplicative.ofAdd p.lower)).symm
    have hd : (powerSeriesDiagonal F p.diagonal)⁻¹ = powerSeriesDiagonal F p.diagonal⁻¹ :=
      (map_inv (powerSeriesDiagonalHom F) p.diagonal).symm
    rw [hu, hl, hd, mul_assoc]

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_iwahori_upper_diagonal_lower
