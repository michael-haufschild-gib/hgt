import GaloisForLFunctions.HTGeometry.KaehlerAnnihilatorTransport
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicKaehler
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# The annihilator of the differentials of a monogenic extension

Over an integrally closed domain, an element generating an algebra presents it as the quotient by
its minimal polynomial (`minpoly.equivAdjoin`), so the monogenic normal form of the cotangent module
transfers:

```text
monogenicEquiv       AdjoinRoot (minpoly A x) ≃ₐ[A] B, when adjoin A {x} = ⊤
monogenicEquiv_mk    it sends the class of g to g(x)
annihilator_kaehler_monogenic
    ** Ann (Ω[B⁄A]) = (p'(x))  for  B = A[x] **
```

The transfer is `KaehlerAnnihilatorTransport.annihilator_kaehler_algEquiv` applied to
`ConstraintRelativity.MonogenicKaehler.annihilator_kaehler`.  Since
`DifferentIdealMonogenic.differentIdeal_eq_span_aeval_derivative` produces the same generator, this
says the annihilator of the differentials *is* the different ideal — the last link between the
Kähler and Dedekind sides of the Jacobian–different bridge.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]

/-- The monogenic presentation of a generated algebra. -/
noncomputable def monogenicEquiv {x : B} (hx : IsIntegral A x)
    (hadj : Algebra.adjoin A ({x} : Set B) = ⊤) :
    AdjoinRoot (minpoly A x) ≃ₐ[A] B :=
  (minpoly.equivAdjoin hx).trans
    ((Subalgebra.equivOfEq _ _ hadj).trans Subalgebra.topEquiv)

theorem monogenicEquiv_mk {x : B} (hx : IsIntegral A x)
    (hadj : Algebra.adjoin A ({x} : Set B) = ⊤) (g : A[X]) :
    monogenicEquiv hx hadj (AdjoinRoot.mk (minpoly A x) g) = Polynomial.aeval x g := by
  have hmk : ∀ q : A[X], (Ideal.Quotient.mkₐ A (Ideal.span {minpoly A x})) q
      = AdjoinRoot.mk (minpoly A x) q := fun _ => rfl
  have hX : monogenicEquiv hx hadj (AdjoinRoot.root (minpoly A x)) = x := by
    simp [monogenicEquiv]
  have hcomp : ((monogenicEquiv hx hadj).toAlgHom.comp
      (Ideal.Quotient.mkₐ A (Ideal.span {minpoly A x}))) = Polynomial.aeval x := by
    refine Polynomial.algHom_ext ?_
    show monogenicEquiv hx hadj ((Ideal.Quotient.mkₐ A (Ideal.span {minpoly A x})) X) = _
    rw [hmk, AdjoinRoot.mk_X]
    simpa using hX
  have hg := congrArg (fun φ => φ g) hcomp
  rw [← hmk g]
  exact hg

/-- **The annihilator of the differentials of a monogenic extension.** -/
theorem annihilator_kaehler_monogenic {x : B} (hx : IsIntegral A x)
    (hadj : Algebra.adjoin A ({x} : Set B) = ⊤) :
    Module.annihilator B (Ω[B⁄A])
      = Ideal.span {Polynomial.aeval x (Polynomial.derivative (minpoly A x))} := by
  classical
  set e := monogenicEquiv hx hadj with he
  have hroot : e (HTGeometry.ConstraintRelativity.rootDifferent (minpoly A x))
      = Polynomial.aeval x (Polynomial.derivative (minpoly A x)) := by
    rw [HTGeometry.ConstraintRelativity.rootDifferent, he, monogenicEquiv_mk]
  have hAR := HTGeometry.ConstraintRelativity.annihilator_kaehler (minpoly A x)
  apply le_antisymm
  · intro b hb
    have hmem : e.symm b ∈ Module.annihilator (AdjoinRoot (minpoly A x))
        (Ω[AdjoinRoot (minpoly A x)⁄A]) := by
      refine (annihilator_kaehler_algEquiv e (e.symm b)).mpr ?_
      rwa [e.apply_symm_apply]
    rw [hAR, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine Ideal.mem_span_singleton.mpr ⟨e c, ?_⟩
    have : b = e (e.symm b) := (e.apply_symm_apply b).symm
    rw [this, hc, map_mul, hroot]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hmem : HTGeometry.ConstraintRelativity.rootDifferent (minpoly A x)
        ∈ Module.annihilator (AdjoinRoot (minpoly A x)) (Ω[AdjoinRoot (minpoly A x)⁄A]) := by
      rw [hAR]
      exact Ideal.mem_span_singleton_self _
    have := (annihilator_kaehler_algEquiv e _).mp hmem
    rwa [hroot] at this

end

end GaloisForLFunctions.HTGeometry
