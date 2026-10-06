import GaloisForLFunctions.RHTower.ThetaCuspRatioSquareSlopeFactor

namespace HTGeometry.ThetaRatioSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource

private theorem variable_factor_of_square_power (m : ℕ) (hm : 0 < m)
    (P Q : Poly) (h : square P=(X Coord.U)^m*Q) :
    ∃ R : Poly, P=X Coord.U*R := by
  have hz (v : Coord → ℂ) (hv : v .U=0) : eval v P=0 := by
    have he := congrArg (eval v) h
    rw [square_eval_seam P v hv] at he
    simpa only [map_mul,map_pow,eval_X,hv,zero_pow (Nat.ne_of_gt hm),zero_mul] using he
  have hs : seamReset P=0 := by
    apply MvPolynomial.funext
    intro v
    rw [seamReset_eval,hz (fun i => if i=Coord.U then 0 else v i) (by simp)]
    simp
  obtain ⟨R,hR⟩ := seamReset_division P
  exact ⟨R,by simpa only [hs,add_zero] using hR⟩

/-- Odd vanishing order in the square chart forces the next whole power. -/
theorem square_odd_power_descent (n : ℕ) (P Q : Poly)
    (h : square P=(X Coord.U)^(2*n+1)*Q) :
    ∃ R : Poly, P=(X Coord.U)^(n+1)*R := by
  induction n generalizing P with
  | zero =>
      simpa only [Nat.mul_zero,Nat.zero_add,pow_one] using
        variable_factor_of_square_power 1 (by omega) P Q h
  | succ n ih =>
      obtain ⟨S,hS⟩ := variable_factor_of_square_power (2*(n+1)+1) (by omega) P Q h
      have he : (X Coord.U:Poly)^2*square S=
          (X Coord.U)^2*((X Coord.U)^(2*n+1)*Q) := by
        calc
          _ = square P := by simp only [hS,map_mul,square_X,squareCoord]
          _ = (X Coord.U)^(2*(n+1)+1)*Q := h
          _ = _ := by
            rw [show 2*(n+1)+1=2+(2*n+1) by omega,pow_add]
            ring
      have hc : square S=(X Coord.U)^(2*n+1)*Q :=
        mul_left_cancel₀ (pow_ne_zero 2 (MvPolynomial.X_ne_zero Coord.U)) he
      obtain ⟨R,hR⟩ := ih S hc
      refine ⟨R,?_⟩
      rw [hS,hR,pow_succ]
      ring

end
end HTGeometry.ThetaRatioSquare
