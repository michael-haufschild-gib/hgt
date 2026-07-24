import GaloisForLFunctions.HTGeometry.ScalarDifferentialFieldInstance

/-!
# The generator of `C⟨y⟩` is hypertranscendental

The scalar free differential field `C⟨y⟩ = Frac(DifferentialPolynomial Unit C)` has a canonical
generator `y = X_{(),0}` (the order-zero jet).  Its differential jets are the free polynomial
variables `X_{(),n}`, which are algebraically independent over `C`; mapped injectively into the
fraction field they stay independent, so `y` is hypertranscendental over `C`.

This is the `HypertranscendentalOver C y` hypothesis of the clock-character law for the concrete field.
-/

namespace GaloisForLFunctions

noncomputable section

open scoped Differential

variable {C : Type*} [Field C]

/-- The canonical differential generator `y = X_{(),0}` of `C⟨y⟩`. -/
def scalarDifferentialGenerator (C : Type*) [Field C] : ScalarDifferentialField C :=
  algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) (MvPolynomial.X ((), 0))

/-- The embedding of the polynomial ring into `C⟨y⟩` commutes with the derivation. -/
theorem algebraMap_scalarDifferentialField_deriv (w : DifferentialPolynomial Unit C) :
    algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) (w′)
      = (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) w)′ := by
  rw [scalarDifferentialField_deriv]
  unfold scalarDifferentialFieldDerivation
  rw [fractionRingDerivation_algebraMap]
  rfl

/-- The `n`-th differential jet of the generator is the free variable `X_{(),n}`. -/
theorem differentialJet_scalarDifferentialGenerator (n : ℕ) :
    differentialJet n (scalarDifferentialGenerator C)
      = algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
          (MvPolynomial.X ((), n)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [differentialJet_succ, ih, ← algebraMap_scalarDifferentialField_deriv]
      congr 1
      exact differentialPolynomial_deriv_X () k

/-- **The generator is hypertranscendental.**  `y = X_{(),0}` is hypertranscendental over `C`. -/
theorem scalarDifferentialGenerator_hypertranscendental :
    HypertranscendentalOver C (scalarDifferentialGenerator C) := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hX : AlgebraicIndependent C
      (fun n : ℕ => (MvPolynomial.X ((), n) : DifferentialPolynomial Unit C)) :=
    (MvPolynomial.algebraicIndependent_X (Unit × ℕ) C).comp (fun n : ℕ => ((), n))
      (fun a b hab => by simpa using hab)
  have hinj : Function.Injective
      (algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)) :=
    IsFractionRing.injective _ _
  have hmap : AlgebraicIndependent C
      (fun n : ℕ => algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
        (MvPolynomial.X ((), n))) :=
    hX.map (f := IsScalarTower.toAlgHom C (DifferentialPolynomial Unit C)
      (ScalarDifferentialField C)) hinj.injOn
  have hjet : AlgebraicIndependent C
      (fun n : ℕ => differentialJet n (scalarDifferentialGenerator C)) := by
    have hfun : (fun n : ℕ => differentialJet n (scalarDifferentialGenerator C))
        = (fun n : ℕ => algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
            (MvPolynomial.X ((), n))) :=
      funext differentialJet_scalarDifferentialGenerator
    rw [hfun]; exact hmap
  unfold DifferentialIndependent
  exact hjet.comp (fun p : Unit × ℕ => p.2) (fun a b hab => by
    obtain ⟨u, m⟩ := a; obtain ⟨v, k⟩ := b
    cases u; cases v; simpa using hab)

end

end GaloisForLFunctions
