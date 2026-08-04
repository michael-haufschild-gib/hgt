import GaloisForLFunctions.HTGeometry.JetPrefixClearing

/-!
# Independence of the low jets, and descent of coefficients

A characteristic of order `m` says exactly that the jets below `m` satisfy no polynomial relation
over the coefficient field.  Two consequences: the jet prefix field is a rational function field
over the coefficient field, and an element of a larger field which happens to lie in the jet prefix
field of a smaller one already lies in that smaller field.

The second statement is the step which converts an equality of jet prefix fields into an equality of
coefficient fields.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- **The low jets are algebraically independent over the coefficient field.**  A polynomial
relation among them would be a differential relation of order below the characteristic's. -/
theorem algebraicIndependent_jets_of_minimal {B : IntermediateField F E} {y : E}
    {P : DifferentialPolynomial Unit B}
    (hmin : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal B y : Set _) P) :
    AlgebraicIndependent B
      (fun i : Fin (scalarDifferentialPolynomialOrder P) => differentialJet i y) := by
  classical
  set m := scalarDifferentialPolynomialOrder P with hm
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  set ι : Fin m → Unit × ℕ := fun i => ((), (i : ℕ)) with hι
  have hιinj : Function.Injective ι := by
    intro a b hab
    exact Fin.ext (congrArg Prod.snd hab)
  set Q : DifferentialPolynomial Unit B := MvPolynomial.rename ι p with hQ
  have hQeval : differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y) Q = 0 := by
    rw [hQ, differentialPolynomialEvalOver, MvPolynomial.aeval_rename]
    exact hp
  have hQmem : Q ∈ differentialIntermediateRelationIdeal B y :=
    (mem_differentialIntermediateRelationIdeal_iff B y Q).2 hQeval
  have hQne : Q ≠ 0 := fun h0 => hp0 (MvPolynomial.rename_injective ι hιinj (by simpa using h0))
  have hQvars : ∀ r ∈ Q.vars, r.2 < m := by
    intro r hr
    rw [hQ] at hr
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hr)
    rw [← hj]
    exact j.2
  by_cases hvars : Q.vars.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hvars
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (hQvars r₀ hr₀)
    have hlt : scalarDifferentialPolynomialOrder Q < m := by
      rw [scalarDifferentialPolynomialOrder]
      exact (Finset.sup_lt_iff hmpos).2 fun j hj => hQvars j hj
    exact absurd ((hmin.2.2.2 hQmem hQne ⟨r₀, hr₀⟩).1) (by omega)
  · rw [Finset.not_nonempty_iff_eq_empty] at hvars
    have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
    have hcne : Q.coeff 0 ≠ 0 := by
      intro h0
      apply hQne
      rw [hC, h0, map_zero]
    rw [hC] at hQeval
    simp only [differentialPolynomialEvalOver_C] at hQeval
    exact hcne ((algebraMap B E).injective (by simpa using hQeval))

/-- **Descent of a coefficient.**  An element of the larger field which lies in the jet prefix field
of the smaller one already lies in the smaller field, as soon as the jets are algebraically
independent over the larger field: clearing denominators exhibits the element as a ratio of two
coefficients of one polynomial identity. -/
theorem mem_of_mem_jetAdjoin {R G : IntermediateField F E} (hRG : R ≤ G) {y : E} {m : ℕ}
    (hindep : AlgebraicIndependent G (fun i : Fin m => differentialJet i y))
    {g : E} (hgG : g ∈ G) (hg : g ∈ jetAdjoin R y m) : g ∈ R := by
  classical
  obtain ⟨N, D, hD, hND⟩ := exists_jetAdjoin_fraction R y m hg
  set jets : Fin m → E := fun i => differentialJet i y with hjets
  set incl : R →+* G := (IntermediateField.inclusion hRG : R →ₐ[F] G).toRingHom with hincl
  have hmapeval : ∀ q : MvPolynomial (Fin m) R,
      MvPolynomial.aeval jets (MvPolynomial.map incl q) = MvPolynomial.aeval jets q := by
    intro q
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.aeval_def]
    rfl
  set p : MvPolynomial (Fin m) G :=
    MvPolynomial.C (⟨g, hgG⟩ : G) * MvPolynomial.map incl D - MvPolynomial.map incl N with hp
  have hzero : MvPolynomial.aeval jets p = 0 := by
    rw [hp, map_sub, map_mul, hmapeval, hmapeval, MvPolynomial.aeval_C]
    have hgval : (algebraMap G E) (⟨g, hgG⟩ : G) = g := rfl
    rw [hgval, hND, sub_self]
  have hp0 : p = 0 := hindep (by simpa using hzero)
  have hDne : D ≠ 0 := by
    intro h0
    exact hD (by rw [h0, map_zero])
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.1 hDne
  have hcoeff : (⟨g, hgG⟩ : G) * incl (D.coeff μ) = incl (N.coeff μ) := by
    have hc := congrArg (fun r : MvPolynomial (Fin m) G => MvPolynomial.coeff μ r) hp0
    rw [hp] at hc
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      MvPolynomial.coeff_zero] at hc
    exact sub_eq_zero.1 hc
  have hcoeffE : g * ((D.coeff μ : R) : E) = ((N.coeff μ : R) : E) :=
    congrArg (fun c : G => (c : E)) hcoeff
  have hDμ : ((D.coeff μ : R) : E) ≠ 0 := by
    intro h0
    exact hμ (Subtype.ext h0)
  have hdiv : ((N.coeff μ / D.coeff μ : R) : E) =
      ((N.coeff μ : R) : E) / ((D.coeff μ : R) : E) := by
    push_cast
    rfl
  have hgeq : g = ((N.coeff μ / D.coeff μ : R) : E) := by
    rw [hdiv, eq_div_iff hDμ, hcoeffE]
  rw [hgeq]
  exact (N.coeff μ / D.coeff μ).2

end

end GaloisForLFunctions
