import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticLeading.JetHeads

/-!
# Source polynomials as polynomials in the kinetic coordinate

The algebra equivalence `Poly ≃ₐ (ℂ[U,K])[J]` sends `J` to the polynomial variable and turns
`∂_J` into the polynomial derivative.  Iterated-derivative identities then become statements about
kinetic degree and coefficients: the integer jet `P_n` has kinetic degree at most `n`, leading
coefficient `a_n` and subleading coefficient `b_n`.
-/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

/-- Coefficient ring of the kinetic variable: polynomials in `u = U` (index `0`) and `K` (index `1`). -/
abbrev KCoeff := MvPolynomial (Fin 2) ℂ

/-- `U ↦ some 0`, `K ↦ some 1`, `J ↦ none`. -/
def coordOption : Coord ≃ Option (Fin 2) where
  toFun
    | .U => some 0
    | .K => some 1
    | .J => none
  invFun
    | none => .J
    | some i => if i = 0 then .U else .K
  left_inv i := by cases i <;> rfl
  right_inv o := by
    rcases o with _ | i
    · rfl
    · fin_cases i <;> rfl

/-- Source polynomials as polynomials in the kinetic coordinate `J`. -/
def kineticEquiv : Poly ≃ₐ[ℂ] Polynomial KCoeff :=
  (renameEquiv ℂ coordOption).trans (optionEquivLeft ℂ (Fin 2))

@[simp] theorem kineticEquiv_C (c : ℂ) : kineticEquiv (C c) = Polynomial.C (C c) := by
  simp [kineticEquiv, optionEquivLeft_C]

@[simp] theorem kineticEquiv_X_U : kineticEquiv (X Coord.U) = Polynomial.C (X 0) := by
  simp [kineticEquiv, coordOption, optionEquivLeft_X_some]

@[simp] theorem kineticEquiv_X_K : kineticEquiv (X Coord.K) = Polynomial.C (X 1) := by
  simp [kineticEquiv, coordOption, optionEquivLeft_X_some]

@[simp] theorem kineticEquiv_X_J : kineticEquiv (X Coord.J) = Polynomial.X := by
  simp [kineticEquiv, coordOption, optionEquivLeft_X_none]

/-- `∂_J` is the kinetic derivative. -/
theorem kineticEquiv_pderivJ (P : Poly) :
    kineticEquiv (pderiv Coord.J P) = Polynomial.derivative (kineticEquiv P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul,
      Polynomial.derivative_mul, hp]
    cases i <;> simp [pderiv_X] <;> ring

theorem kineticEquiv_iterate_pderivJ (k : ℕ) (P : Poly) :
    kineticEquiv ((pderiv Coord.J)^[k] P) = Polynomial.derivative^[k] (kineticEquiv P) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', kineticEquiv_pderivJ, ih]

/-! ## Degree and coefficients from iterated derivatives -/

theorem natDegree_le_of_iterate_derivative {p : Polynomial KCoeff} {n : ℕ}
    (h : Polynomial.derivative^[n+1] p = 0) : p.natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hN
  rw [show n + m + 1 = m + (n+1) by omega]
  have hc := Polynomial.coeff_iterate_derivative (k := n+1) p m
  rw [h, Polynomial.coeff_zero] at hc
  have hne : (m + (n+1)).descFactorial (n+1) ≠ 0 :=
    (Nat.descFactorial_pos.mpr (by omega)).ne'
  have : ((m + (n+1)).descFactorial (n+1) : KCoeff) * p.coeff (m + (n+1)) = 0 := by
    rw [← nsmul_eq_mul]; exact hc.symm
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.mpr hne)
  · exact h0

theorem coeff_eq_of_iterate_derivative_coeff_zero {p : Polynomial KCoeff} {n : ℕ} {c : KCoeff}
    (h : (Polynomial.derivative^[n] p).coeff 0 = (n.factorial : KCoeff) * c) : p.coeff n = c := by
  rw [Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul] at h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h

/-! ## Kinetic coefficients of the integer jets -/

/-- `u` and `y = 3K + 1` in the coefficient ring. -/
def kineticU : KCoeff := X 0
def kineticYC : KCoeff := 3 * X 1 + 1

/-- Leading coefficient `a_n` in the coefficient ring. -/
def headA : ℕ → KCoeff
  | 0 => 2*kineticYC-3
  | n+1 => 2*12^(n+1)*kineticYC

/-- Subleading coefficient `b_n` in the coefficient ring. -/
def headB (n : ℕ) : KCoeff :=
  kineticU*12^(n-1)*(-8*(n:KCoeff)*kineticYC^2+(4*(n:KCoeff)^2+6*(n:KCoeff)+12)*kineticYC-
    (if n=1 then 15 else 0))

theorem kineticEquiv_kineticY : kineticEquiv kineticY = Polynomial.C kineticYC := by
  simp [kineticY, kineticYC, map_ofNat]

theorem kineticEquiv_jetHeadA (n : ℕ) : kineticEquiv (jetHeadA n) = Polynomial.C (headA n) := by
  cases n <;> simp [jetHeadA, headA, kineticEquiv_kineticY, map_ofNat]

theorem kineticEquiv_jetHeadB (n : ℕ) : kineticEquiv (jetHeadB n) = Polynomial.C (headB n) := by
  unfold jetHeadB headB
  split_ifs <;> simp [kineticEquiv_kineticY, kineticU, map_ofNat]

/-- **Kinetic degree and leading coefficient of every integer jet.** -/
theorem integerJet_kinetic_head (n : ℕ) :
    (kineticEquiv (integerJet n)).natDegree ≤ n ∧ (kineticEquiv (integerJet n)).coeff n = headA n := by
  obtain ⟨h1, h2⟩ := integerJet_heads n
  constructor
  · apply natDegree_le_of_iterate_derivative
    rw [← kineticEquiv_iterate_pderivJ, h1, map_zero]
  · apply coeff_eq_of_iterate_derivative_coeff_zero
    rw [← kineticEquiv_iterate_pderivJ, h2, map_mul, kineticEquiv_jetHeadA, map_natCast]
    simp

/-- **Subleading coefficient of every integer jet.** -/
theorem integerJet_kinetic_subhead (n : ℕ) :
    (kineticEquiv (integerJet (n+1))).coeff n = headB (n+1) := by
  apply coeff_eq_of_iterate_derivative_coeff_zero
  rw [← kineticEquiv_iterate_pderivJ, integerJet_subheads, map_add, map_mul, map_mul, map_mul,
    kineticEquiv_jetHeadA, kineticEquiv_jetHeadB, kineticEquiv_X_J, map_natCast, map_natCast]
  simp

end
end HTGeometry.ThetaRatioSource
