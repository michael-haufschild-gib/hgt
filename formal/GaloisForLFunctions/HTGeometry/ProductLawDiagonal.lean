import GaloisForLFunctions.HTGeometry.ProductLawJetReduction
import GaloisForLFunctions.HTGeometry.TerminalWronskian

/-!
# The multiplier depends on its own coordinate

The multiplier of a coordinate jet, evaluated one level up, is

`logSum_(m+1) + α·∏_(j≤m+1)Q_j(X_j) = (low) + (∏_(j≤m)Q_j)·W(X_(m+1))`,

with `W = Q'·v/Q + α·Q` the terminal rational function.  Its coordinate derivative is the head product
times the Wronskian of the cleared numerator against the denominator, so it is nonzero exactly when
that Wronskian is — which is the polynomial statement proved separately.

This is the diagonal entry of the height induction: each level really sees its own coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The multiplier, split into a low part and the terminal rational function. -/
theorem totalLog_split {α β : ℂ} {m : ℕ} (hα : α ≠ 0)
    (hv : v (m + 2) = Polynomial.C α * Polynomial.X + Polynomial.C β) :
    totalLog Q v (m + 2)
      = logSum Q v (m + 1)
        + prodHead Q (m + 1)
          * (logFactor (Q (m + 1)) (m + 1) * fact (v (m + 1)) (m + 1)
              + algebraMap ℂ CascadeField α * fact (Q (m + 1)) (m + 1)) := by
  rw [totalLog_linear Q v hα hv, logSum_succ, prodHead_succ, prodJet_eq]
  ring

/-- The terminal rational function, as a quotient of factors. -/
theorem terminal_bracket_eq {α : ℂ} {m : ℕ} (hQ : Q (m + 1) ≠ 0) :
    logFactor (Q (m + 1)) (m + 1) * fact (v (m + 1)) (m + 1)
        + algebraMap ℂ CascadeField α * fact (Q (m + 1)) (m + 1)
      = fact (terminalNumer (Q (m + 1)) (v (m + 1)) α) (m + 1)
        / fact (Q (m + 1)) (m + 1) := by
  have hne : fact (Q (m + 1)) (m + 1) ≠ 0 := fact_ne_zero hQ (m + 1)
  rw [terminalNumer, fact_add, fact_mul, fact_mul, fact_pow, fact_C, logFactor]
  field_simp

/-- The coordinate derivative of a factor quotient is the Wronskian over the square. -/
theorem fpderiv_terminal_bracket {α : ℂ} {m : ℕ} (hQ : Q (m + 1) ≠ 0) :
    fpderiv (m + 1)
        (fact (terminalNumer (Q (m + 1)) (v (m + 1)) α) (m + 1) / fact (Q (m + 1)) (m + 1))
      = fact (terminalWronskian (Q (m + 1)) (v (m + 1)) α) (m + 1)
        / fact (Q (m + 1)) (m + 1) ^ 2 := by
  have hne : fact (Q (m + 1)) (m + 1) ≠ 0 := fact_ne_zero hQ (m + 1)
  rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, derivation_fact,
    derivation_fact, fpderiv_fx_self, terminalWronskian, fact_sub, fact_mul, fact_mul]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

/-- **The diagonal of the height induction.**  The multiplier at level `m+2` has nonzero derivative in
the coordinate `m+1`, provided that coordinate's factor is nonconstant and the terminal factor above it
is genuinely linear. -/
theorem fpderiv_totalLog_ne_zero {α β : ℂ} {m : ℕ} (hα : α ≠ 0)
    (hv : v (m + 2) = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hQdeg : 1 ≤ (Q (m + 1)).natDegree) (hvdeg : (v (m + 1)).natDegree ≤ 1)
    (hQ : ∀ j, Q j ≠ 0) :
    fpderiv (m + 1) (totalLog Q v (m + 2)) ≠ 0 := by
  have hQne : Q (m + 1) ≠ 0 := hQ (m + 1)
  have hfne : fact (Q (m + 1)) (m + 1) ≠ 0 := fact_ne_zero hQne (m + 1)
  have hlow : fpderiv (m + 1) (logSum Q v (m + 1)) = 0 :=
    fpderiv_eq_zero_of_mem_lowSub Q v (by omega) (logSum_mem_lowSub_pred Q v m)
  have hhead : fpderiv (m + 1) (prodHead Q (m + 1)) = 0 :=
    fpderiv_eq_zero_of_mem_lowSub Q v (by omega) (prodHead_mem_lowSub_pred Q v m)
  rw [totalLog_split Q v hα hv, map_add, hlow, zero_add, Derivation.leibniz, hhead,
    terminal_bracket_eq Q v (α := α) hQne, fpderiv_terminal_bracket Q v hQne]
  simp only [smul_eq_mul, mul_zero, add_zero]
  refine mul_ne_zero (prodHead_ne_zero hQ (m + 1)) ?_
  refine div_ne_zero ?_ (pow_ne_zero 2 hfne)
  exact fact_ne_zero (terminalWronskian_ne_zero hα hQdeg hvdeg) (m + 1)

end GaloisForLFunctions.HTGeometry
