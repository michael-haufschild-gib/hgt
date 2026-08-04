import GaloisForLFunctions.HTGeometry.JetFieldOrderCharacterization
import GaloisForLFunctions.HTGeometry.PolynomialTotalDerivative
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Jet levels are algebraically closed in the free differential rational field

A rational function of the jets of level at most `N` cannot acquire new jets by an algebraic
extension: an element algebraic over a jet level already lies in that level.

The mechanism is implicit differentiation.  The coordinate derivation at a jet above the level kills
every coefficient of the minimal polynomial, so differentiating the minimal equation leaves only the
term `p'(u) · ∂u`, and `p'(u) ≠ 0` in characteristic zero.  Hence every coordinate derivative of `u`
above the level vanishes, which is exactly membership in the level.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

open JetField

noncomputable section

variable {C ι : Type*} [Field C] [CharZero C]

/-- **A derivation vanishing on a subfield kills every algebraic element.** -/
theorem derivation_eq_zero_of_isAlgebraic {L : Type*} [Field L] [CharZero L]
    [Algebra C L] (K : IntermediateField C L) (D : Derivation ℤ L L)
    (hK : ∀ x ∈ K, D x = 0) {u : L} (hu : IsAlgebraic K u) : D u = 0 := by
  classical
  letI : Differential L := ⟨D⟩
  have hint : IsIntegral K u := hu.isIntegral
  set p : Polynomial K := minpoly K u with hp
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hpdeg : 0 < p.natDegree := minpoly.natDegree_pos hint
  set P : Polynomial L := p.map (algebraMap K L) with hP
  have hPeval : Polynomial.eval u P = 0 := by
    rw [hP, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval K u
  have hdp0 : Polynomial.derivative p ≠ 0 := by
    intro hcon
    have hnat := Polynomial.derivative_eq_zero.mp hcon
    omega
  have hBne : Polynomial.eval u (Polynomial.derivative P) ≠ 0 := by
    rw [hP, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
    intro hcon
    have hle := minpoly.degree_le_of_ne_zero K u hdp0 hcon
    have hlt := Polynomial.degree_derivative_lt hp0
    rw [← hp] at hle
    exact absurd hle (not_le.mpr hlt)
  have hcoeff : coeffDeriv P = 0 := by
    refine Polynomial.ext fun i => ?_
    rw [coeffDeriv_coeff, Polynomial.coeff_zero, hP, Polynomial.coeff_map]
    refine hK _ ?_
    simp
  have hchain := deriv_eval P u
  rw [hPeval, hcoeff] at hchain
  simp only [map_zero, Polynomial.eval_zero, zero_add] at hchain
  have hzero : Polynomial.eval u (Polynomial.derivative P) * (D u) = 0 := hchain.symm
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hBne
  · exact h

variable [Fintype ι]

omit [Fintype ι] in
/-- **Jet levels are algebraically closed.**  An element of the free differential rational field that
is algebraic over the field of rational functions of the jets of level at most `N` is itself such a
rational function. -/
theorem mem_jetLevel_of_isAlgebraic {N : ℕ} {u : JetField C ι}
    (hu : IsAlgebraic (IntermediateField.adjoin C
      ((fun p => (jet p : JetField C ι)) '' {p : ι × ℕ | p.2 ≤ N})) u) :
    u ∈ IntermediateField.adjoin C
      ((fun p => (jet p : JetField C ι)) '' {p : ι × ℕ | p.2 ≤ N}) := by
  classical
  refine mem_jetLevel_iff.2 fun j m hm => ?_
  refine derivation_eq_zero_of_isAlgebraic _ ((pd ((j, m) : ι × ℕ)).restrictScalars ℤ) ?_ hu
  intro x hx
  have hq : ((j, m) : ι × ℕ) ∉ {p : ι × ℕ | p.2 ≤ N} := by
    simp only [Set.mem_setOf_eq]
    omega
  simpa using pd_eq_zero_of_mem_adjoin hq hx

/-- The order of an element algebraic over a jet level does not exceed that level. -/
theorem ordJet_le_of_isAlgebraic {N : ℕ} {u : JetField C ι}
    (hu : IsAlgebraic (IntermediateField.adjoin C
      ((fun p => (jet p : JetField C ι)) '' {p : ι × ℕ | p.2 ≤ N})) u) :
    ordJet u ≤ N :=
  (ordJet_le_iff u N).2 (mem_jetLevel_of_isAlgebraic hu)

end

end GaloisForLFunctions.HTGeometry
