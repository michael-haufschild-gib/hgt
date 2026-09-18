import GaloisForLFunctions.RHTower.MaassRationalHeckeFormalProduct

/-!
# Operator-level descent of rational Mackey products

Rational traces that represent one principal Hecke double coset give the same
Maass eigenspace endomorphism.  Consequently the representative-level formal
Mackey product is invariant under changing either input representative after
applying its concrete action.

This is descent modulo the kernel of the formal-coset action.  It does not prove
equality of the formal product sums, their associativity, or commutativity.
-/

namespace GaloisForLFunctions.RHTower

open Complex Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups BigOperators

noncomputable section

/-- Equal principal rational double cosets give equal rational trace
endomorphisms of every fixed Maass eigenspace. -/
theorem rationalPrincipalTraceLinear_eq_of_principal_doubleCoset
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (hgh : DoubleCoset.setoid (principalCongruenceGL N : Set (GL (Fin 2) ℝ))
      (principalCongruenceGL N) (g.map (algebraMap ℚ ℝ))
      (h.map (algebraMap ℚ ℝ))) (lam : ℝ) :
    rationalPrincipalTraceLinear N h hh lam =
      rationalPrincipalTraceLinear N g hg lam := by
  letI : (rationalConjugateGroup N h).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N h
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  ext u z
  change maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) h
        (maassEigenspaceToInvariant u)) z =
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g
        (maassEigenspaceToInvariant u)) z
  exact congrFun (rationalPrincipalTrace_eq_of_principal_doubleCoset N g h hgh
    (maassEigenspaceToInvariant u)) z

/-- Changing the first rational representative within its principal double coset
leaves the action of the formal Mackey product unchanged. -/
theorem rationalMackeyHeckeCosetFormalProduct_action_congr_left
    (N : ℕ) (g g' h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hg' : 0 < (g'.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (hgg' : DoubleCoset.setoid (principalCongruenceGL N : Set (GL (Fin 2) ℝ))
      (principalCongruenceGL N) (g.map (algebraMap ℚ ℝ))
      (g'.map (algebraMap ℚ ℝ))) (lam : ℝ) :
    rationalPrincipalHeckeCosetFinsuppAction N lam
      (rationalMackeyHeckeCosetFormalProduct N g h hg hh) =
    rationalPrincipalHeckeCosetFinsuppAction N lam
      (rationalMackeyHeckeCosetFormalProduct N g' h hg' hh) := by
  rw [rationalMackeyHeckeCosetFormalProduct_action,
    rationalMackeyHeckeCosetFormalProduct_action]
  rw [rationalPrincipalTraceLinear_eq_of_principal_doubleCoset N g g' hg hg' hgg' lam]

/-- Changing the second rational representative within its principal double coset
leaves the action of the formal Mackey product unchanged. -/
theorem rationalMackeyHeckeCosetFormalProduct_action_congr_right
    (N : ℕ) (g h h' : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (hh' : 0 < (h'.map (algebraMap ℚ ℝ)).val.det)
    (hhh' : DoubleCoset.setoid (principalCongruenceGL N : Set (GL (Fin 2) ℝ))
      (principalCongruenceGL N) (h.map (algebraMap ℚ ℝ))
      (h'.map (algebraMap ℚ ℝ))) (lam : ℝ) :
    rationalPrincipalHeckeCosetFinsuppAction N lam
      (rationalMackeyHeckeCosetFormalProduct N g h hg hh) =
    rationalPrincipalHeckeCosetFinsuppAction N lam
      (rationalMackeyHeckeCosetFormalProduct N g h' hg hh') := by
  rw [rationalMackeyHeckeCosetFormalProduct_action,
    rationalMackeyHeckeCosetFormalProduct_action]
  rw [rationalPrincipalTraceLinear_eq_of_principal_doubleCoset N h h' hh hh' hhh' lam]

end

end GaloisForLFunctions.RHTower
