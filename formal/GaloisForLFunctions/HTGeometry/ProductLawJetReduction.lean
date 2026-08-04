import GaloisForLFunctions.HTGeometry.ProductLawTopReduction
import GaloisForLFunctions.HTGeometry.AffineTopBellJacobian
import GaloisForLFunctions.HTGeometry.DerivationTerminalLinearJacobian

/-!
# One Bell reduction for the product law

The jet `δX_k` of a coordinate is logarithmically linear with multiplier

`logSum_k + (v_k'/v_k)(X_k)·δX_k`,

and the terminal factor cancels in the second term: `(v_k'/v_k)(X_k)·δX_k = v_k'(X_k)·∏_(j<k)Q_j(X_j)`.
When `v_k` is linear that is a constant times the head product, so the whole multiplier avoids the
`k`-th coordinate — exactly the property the tower's partial sums have, and the one the terminal-scaled
Bell reduction needs.

So one reduction carries the jet Jacobian of `δX_k` down to the jet Jacobian of its multiplier, with a
nonzero cofactor.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- **The terminal factor cancels in the multiplier.** -/
theorem totalLog_eq_of_ne_zero {k : ℕ} (hv : fact (v k) k ≠ 0) :
    totalLog Q v k = logSum Q v k + fact (v k).derivative k * prodHead Q k := by
  rw [totalLog, logFactor, prodJet_eq]
  congr 1
  field_simp

/-- With a linear terminal factor the multiplier avoids the coordinate. -/
theorem totalLog_linear {α β : ℂ} {k : ℕ} (hα : α ≠ 0)
    (hv : v k = Polynomial.C α * Polynomial.X + Polynomial.C β) :
    totalLog Q v k = logSum Q v k + algebraMap ℂ CascadeField α * prodHead Q k := by
  have hvne : fact (v k) k ≠ 0 := by
    refine fact_ne_zero ?_ k
    intro h0
    rw [h0] at hv
    have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 1) hv
    simp at hcoeff
    exact hα hcoeff.symm
  rw [totalLog_eq_of_ne_zero Q v hvne, hv]
  congr 2
  rw [Polynomial.derivative_add, Polynomial.derivative_C, add_zero, Polynomial.derivative_C_mul,
    Polynomial.derivative_X, mul_one, fact_C]

/-- The logarithmic sum of a level is low one level down: it runs over strictly earlier
coordinates. -/
theorem logSum_mem_lowSub_pred (m : ℕ) : logSum Q v (m + 1) ∈ lowSub Q v m := by
  refine Subalgebra.sum_mem _ fun j hj => ?_
  have hjm : j < m + 1 := Finset.mem_range.mp hj
  exact Subalgebra.mul_mem _ (logFactorQ_mem_lowSub Q v (by omega))
    (prodJet_mem_lowSub Q v (by omega))

theorem prodHead_mem_lowSub_pred (m : ℕ) : prodHead Q (m + 1) ∈ lowSub Q v m := by
  refine Subalgebra.prod_mem _ fun j hj => ?_
  have hjm : j < m + 1 := Finset.mem_range.mp hj
  exact fact_mem_lowSub Q v (by omega) (Q j)

/-- The multiplier of a linear-terminal jet is low. -/
theorem totalLog_mem_lowSub_pred {α β : ℂ} {m : ℕ} (hα : α ≠ 0)
    (hv : v (m + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β) :
    totalLog Q v (m + 1) ∈ lowSub Q v m := by
  rw [totalLog_linear Q v hα hv]
  exact Subalgebra.add_mem _ (logSum_mem_lowSub_pred Q v m)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ α) (prodHead_mem_lowSub_pred Q v m))

/-! ## The reduction -/

/-- The Jacobian of the jets of the `r`-th coordinate jet against the coordinate derivations. -/
noncomputable def prodJetJacobian (r : ℕ) : Matrix (Fin r) (Fin r) CascadeField :=
  Matrix.of fun i j => fpderiv ((j : ℕ) + 1)
    (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (prodJet Q v r))

/-- The Jacobian of the jets of the multiplier one level down. -/
noncomputable def totalLogJacobian (m : ℕ) : Matrix (Fin m) (Fin m) CascadeField :=
  Matrix.of fun i j => fpderiv ((j : ℕ) + 1)
    (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (totalLog Q v (m + 1)))

/-- **The terminal derivative of a coordinate jet.**  Only the terminal factor sees the coordinate,
and it contributes its slope. -/
theorem fpderiv_prodJet_terminal {α β : ℂ} {m : ℕ}
    (hv : v (m + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β) :
    fpderiv (m + 1) (prodJet Q v (m + 1))
      = algebraMap ℂ CascadeField α * prodHead Q (m + 1) := by
  have hhead : fpderiv (m + 1) (prodHead Q (m + 1)) = 0 :=
    fpderiv_eq_zero_of_mem_lowSub Q v (by omega) (prodHead_mem_lowSub_pred Q v m)
  have hder : (v (m + 1)).derivative = Polynomial.C α := by
    rw [hv, Polynomial.derivative_add, Polynomial.derivative_C, add_zero,
      Polynomial.derivative_C_mul, Polynomial.derivative_X, mul_one]
  rw [prodJet_eq, Derivation.leibniz, hhead, derivation_fact, hder, fact_C,
    fpderiv_fx_self]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  ring

/-- **One Bell reduction for the product law.**  The jet Jacobian of a coordinate jet is the
multiplier's jet Jacobian, times the terminal slope, a power of the jet, and the cofactor sign. -/
theorem prodJetJacobian_det_reduce {α β : ℂ} {s : ℕ} {Q : ℕ → Polynomial ℂ}
    (hQ : ∀ j, Q j ≠ 0) (hα : α ≠ 0)
    (hv : v (s + 2) = Polynomial.C α * Polynomial.X + Polynomial.C β) :
    (prodJetJacobian Q v (s + 2)).det
      = (-1 : CascadeField) ^ (s + 1)
        * (algebraMap ℂ CascadeField α * prodHead Q (s + 2))
        * prodJet Q v (s + 2) ^ (s + 1)
        * (totalLogJacobian Q v (s + 1)).det := by
  have hmat : prodJetJacobian Q v (s + 2)
      = derivationIterateOutputJacobian (prodDerivation Q v) s
          (fun l : Fin (s + 2) => fpderiv ((l : ℕ) + 1)) (prodJet Q v (s + 2)) := by
    funext i j
    rfl
  have hδH : prodDerivation Q v (prodJet Q v (s + 2))
      = totalLog Q v (s + 2) * prodJet Q v (s + 2) := prodDerivation_prodJet' v hQ (s + 2)
  have hterm : ∀ i : Fin (s + 1),
      (fun l : Fin (s + 2) => fpderiv ((l : ℕ) + 1)) (Fin.last (s + 1))
        (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)])
          (totalLog Q v (s + 2))) = 0 := by
    intro i
    have hidx : ((Fin.last (s + 1) : Fin (s + 2)) : ℕ) + 1 = s + 2 := by simp
    show fpderiv (((Fin.last (s + 1) : Fin (s + 2)) : ℕ) + 1)
        (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)])
          (totalLog Q v (s + 2))) = 0
    rw [hidx]
    exact fpderiv_iterate_of_low Q v (m := s + 1) (by omega)
      (totalLog_mem_lowSub_pred Q v hα hv) _
  have hred := derivationIterateOutputJacobian_det_terminalScaled (prodDerivation Q v) s
    (fun l : Fin (s + 2) => fpderiv ((l : ℕ) + 1)) (prodJet Q v (s + 2))
    (totalLog Q v (s + 2)) hδH hterm
  have hlow : derivationLowerJetJacobian (prodDerivation Q v) s
      (fun l : Fin (s + 2) => fpderiv ((l : ℕ) + 1)) (totalLog Q v (s + 2))
      = totalLogJacobian Q v (s + 1) := by
    funext i j
    rfl
  have hterminal :
      (fun l : Fin (s + 2) => fpderiv ((l : ℕ) + 1)) (Fin.last (s + 1)) (prodJet Q v (s + 2))
        = algebraMap ℂ CascadeField α * prodHead Q (s + 2) := by
    show fpderiv (((Fin.last (s + 1) : Fin (s + 2)) : ℕ) + 1) (prodJet Q v (s + 2))
      = algebraMap ℂ CascadeField α * prodHead Q (s + 2)
    exact fpderiv_prodJet_terminal Q v hv
  rw [hmat, hred, hlow, hterminal]

/-- **The reduction preserves nonvanishing.** -/
theorem prodJetJacobian_det_ne_zero_of_totalLog {α β : ℂ} {s : ℕ} {Q : ℕ → Polynomial ℂ}
    (hQ : ∀ j, Q j ≠ 0) (hα : α ≠ 0)
    (hv : v (s + 2) = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hvne : ∀ j, v j ≠ 0)
    (hsub : (totalLogJacobian Q v (s + 1)).det ≠ 0) :
    (prodJetJacobian Q v (s + 2)).det ≠ 0 := by
  rw [prodJetJacobian_det_reduce v hQ hα hv]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) hsub
  · exact pow_ne_zero _ (by norm_num : (-1 : CascadeField) ≠ 0)
  · refine mul_ne_zero ?_ (prodHead_ne_zero hQ (s + 2))
    simpa using hα
  · exact pow_ne_zero _ (prodJet_ne_zero hQ hvne (s + 2))

end GaloisForLFunctions.HTGeometry
