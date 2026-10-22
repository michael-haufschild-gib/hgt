import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioIntegerReflections
import GaloisForLFunctions.HTGeometry.CoordinateDerivationCommute

/-!
# Kinetic commutator and the top two coefficients of every integer source jet

Differentiating in the kinetic coordinate `J` does not commute with the integer source field: the
commutator is the `J`-independent operator
`C(P) = (12K+4) ∂_K P + (12K+8) U ∂_J P`, which itself commutes with `∂_J`.  Iterating,
`∂_J^{m+1}(step P) = step(∂_J^{m+1} P) + (m+1) C(∂_J^m P)`.

For the integer jets `P_{n+1} = step P_n`, `P_0 = 6K - 1`, this gives `∂_J^{n+1} P_n = 0`
(kinetic degree at most `n`) and, with `y = 3K + 1`,

* `∂_J^n P_n = n!·a_n`, `a_0 = 2y - 3`, `a_n = 2·12^n y` for `n ≥ 1`;
* `∂_J^{n-1} P_n = n! a_n J + (n-1)! b_n` for `n ≥ 1`, where
  `b_n = U·12^{n-1}(-8n y² + (4n²+6n+12) y - 15 δ_{n,1})`.
-/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

/-- The kinetic coordinate `y = 3K + 1`. -/
def kineticY : Poly := 3*X Coord.K+1

/-- The kinetic commutator `C(P) = (12K+4) ∂_K P + (12K+8) U ∂_J P`. -/
def kineticCommutator (P : Poly) : Poly :=
  (12*X Coord.K+4)*pderiv Coord.K P+(12*X Coord.K+8)*X Coord.U*pderiv Coord.J P

private theorem univ_coord : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

theorem integerLie_expand (P : Poly) :
    integerLie P = pderiv Coord.U P*integerField .U+pderiv Coord.K P*integerField .K+
      pderiv Coord.J P*integerField .J := by
  simp [integerLie, univ_coord, add_assoc]

theorem pderivJ_integerLie (P : Poly) :
    pderiv Coord.J (integerLie P)=integerLie (pderiv Coord.J P)+kineticCommutator P := by
  rw [integerLie_expand, integerLie_expand]
  simp only [map_add, Derivation.leibniz, smul_eq_mul]
  rw [GaloisForLFunctions.pderiv_comm Coord.J Coord.U, GaloisForLFunctions.pderiv_comm Coord.J Coord.K]
  simp [integerField, kineticCommutator, pderiv_X]
  ring

theorem pderivJ_integerStep (P : Poly) :
    pderiv Coord.J (integerStep P)=integerStep (pderiv Coord.J P)+kineticCommutator P := by
  unfold integerStep
  rw [map_add, pderivJ_integerLie, Derivation.leibniz]
  simp [pderiv_X]
  ring

theorem pderivJ_kineticCommutator (P : Poly) :
    pderiv Coord.J (kineticCommutator P)=kineticCommutator (pderiv Coord.J P) := by
  unfold kineticCommutator
  simp only [map_add, Derivation.leibniz, smul_eq_mul]
  rw [GaloisForLFunctions.pderiv_comm Coord.J Coord.K]
  simp [pderiv_X]

theorem integerStep_zero : integerStep 0=0 := by simp [integerStep, integerLie]
theorem kineticCommutator_zero : kineticCommutator 0=0 := by simp [kineticCommutator]

theorem kineticCommutator_add (P Q : Poly) :
    kineticCommutator (P+Q)=kineticCommutator P+kineticCommutator Q := by
  simp [kineticCommutator]; ring

theorem kineticCommutator_nsmul (n : ℕ) (P : Poly) :
    kineticCommutator (n • P)=n • kineticCommutator P := by
  simp [kineticCommutator, nsmul_eq_mul]; ring

/-- Iterated kinetic derivative of a source step. -/
theorem iterate_pderivJ_integerStep (m : ℕ) (P : Poly) :
    (pderiv Coord.J)^[m+1] (integerStep P) =
      integerStep ((pderiv Coord.J)^[m+1] P)+(m+1) • kineticCommutator ((pderiv Coord.J)^[m] P) := by
  induction m with
  | zero => simp [pderivJ_integerStep]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_add, pderivJ_integerStep, map_nsmul,
      pderivJ_kineticCommutator, ← Function.iterate_succ_apply' (pderiv Coord.J),
      ← Function.iterate_succ_apply' (pderiv Coord.J)]
    simp only [Nat.succ_eq_add_one, succ_nsmul]
    abel


/-! ## Top two coefficients of the integer jets -/

/-- Leading kinetic coefficient: `a_0 = 2y - 3`, `a_n = 2·12^n y` for `n ≥ 1`. -/
def jetHeadA : ℕ → Poly
  | 0 => 2*kineticY-3
  | n+1 => 2*12^(n+1)*kineticY

/-- Subleading kinetic coefficient
`b_n = U·12^{n-1}(-8n y² + (4n²+6n+12) y - 15 δ_{n,1})`, `n ≥ 1`. -/
def jetHeadB (n : ℕ) : Poly :=
  X Coord.U*12^(n-1)*(-8*(n:Poly)*kineticY^2+(4*(n:Poly)^2+6*(n:Poly)+12)*kineticY-
    (if n=1 then 15 else 0))

theorem pderiv_kineticY (i : Coord) : pderiv i kineticY = if i = Coord.K then 3 else 0 := by
  cases i <;> simp [kineticY, pderiv_X]

theorem pderivJ_jetHeadA (n : ℕ) : pderiv Coord.J (jetHeadA n) = 0 := by
  cases n <;> simp [jetHeadA, pderiv_kineticY]

theorem pderivU_jetHeadA (n : ℕ) : pderiv Coord.U (jetHeadA n) = 0 := by
  cases n <;> simp [jetHeadA, pderiv_kineticY]

theorem pderivJ_jetHeadB (n : ℕ) : pderiv Coord.J (jetHeadB n) = 0 := by
  unfold jetHeadB
  split_ifs <;> simp [pderiv_kineticY, pderiv_X]

/-- `C` applied to a `J`-free polynomial. -/
theorem kineticCommutator_of_pderivJ_eq_zero {P : Poly} (hP : pderiv Coord.J P = 0) :
    kineticCommutator P = (12*X Coord.K+4)*pderiv Coord.K P := by
  simp [kineticCommutator, hP]

/-- The leading recurrence `a_{n+1} = (12K+4) ∂_K a_n`. -/
theorem jetHeadA_succ (n : ℕ) :
    jetHeadA (n+1) = (12*X Coord.K+4)*pderiv Coord.K (jetHeadA n) := by
  cases n <;> simp [jetHeadA, kineticY] <;> ring

theorem iterate_pderivJ_succ_of_eq_zero {k : ℕ} {P : Poly} (h : (pderiv Coord.J)^[k] P = 0) :
    (pderiv Coord.J)^[k+1] P = 0 := by
  rw [Function.iterate_succ_apply', h, map_zero]

/-- **All-order jet heads.**  The kinetic degree of `P_n` is at most `n`, with leading
coefficient `a_n`. -/
theorem integerJet_heads (n : ℕ) :
    (pderiv Coord.J)^[n+1] (integerJet n) = 0 ∧
      (pderiv Coord.J)^[n] (integerJet n) = (n.factorial : Poly)*jetHeadA n := by
  induction n with
  | zero => simp [integerJet, jetHeadA, kineticY, pderiv_X]; ring
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · rw [integerJet, iterate_pderivJ_integerStep, iterate_pderivJ_succ_of_eq_zero h1, h1,
        integerStep_zero, kineticCommutator_zero, smul_zero, add_zero]
    · rw [integerJet, iterate_pderivJ_integerStep, h1, integerStep_zero, zero_add, h2,
        kineticCommutator_of_pderivJ_eq_zero (by simp [pderivJ_jetHeadA]), jetHeadA_succ]
      simp only [Derivation.leibniz, smul_eq_mul, nsmul_eq_mul, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, (pderiv Coord.K).map_natCast, mul_zero, add_zero]
      ring

/-- The subleading recurrence `b_{n+1} = (12K+4) ∂_K b_n + U a_n (4n(y+1) + 5 - 4y)`, `n ≥ 1`. -/
theorem jetHeadB_succ (n : ℕ) :
    jetHeadB (n+2) = (12*X Coord.K+4)*pderiv Coord.K (jetHeadB (n+1))+
      X Coord.U*jetHeadA (n+1)*((1-12*X Coord.K)+((n:Poly)+1)*(12*X Coord.K+8)) := by
  rcases n with _ | n
  · simp [jetHeadB, jetHeadA, kineticY, pderiv_X]
    ring
  · have h1 : n+1+2-1 = n+2 := by omega
    have h2 : n+1+1-1 = n+1 := by omega
    have h3 : n+1+2 ≠ 1 := by omega
    have h4 : n+1+1 ≠ 1 := by omega
    simp only [jetHeadB, jetHeadA, h1, h2, h3, h4, if_false]
    simp [kineticY, pderiv_X, Derivation.leibniz]
    ring

/-- **Subleading jet heads.**  `∂_J^{n} P_{n+1} = (n+1)! a_{n+1} J + n! b_{n+1}`. -/
theorem integerJet_subheads (n : ℕ) :
    (pderiv Coord.J)^[n] (integerJet (n+1)) =
      ((n+1).factorial : Poly)*jetHeadA (n+1)*X Coord.J+(n.factorial : Poly)*jetHeadB (n+1) := by
  induction n with
  | zero =>
    simp [integerJet, integerStep, integerLie_expand, integerField, jetHeadA, jetHeadB, kineticY, pderiv_X]
    ring
  | succ n ih =>
    rw [integerJet, iterate_pderivJ_integerStep, (integerJet_heads (n+1)).2, ih]
    have hA := pderivJ_jetHeadA (n+1)
    have hAU := pderivU_jetHeadA (n+1)
    have hB := pderivJ_jetHeadB (n+1)
    rw [jetHeadB_succ, jetHeadA_succ (n+1)]
    simp only [integerStep, integerLie_expand, kineticCommutator, map_add, Derivation.leibniz,
      smul_eq_mul, nsmul_eq_mul, hA, hAU, hB, (pderiv _).map_natCast, pderiv_X, integerField,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp
    ring

end
end HTGeometry.ThetaRatioSource
