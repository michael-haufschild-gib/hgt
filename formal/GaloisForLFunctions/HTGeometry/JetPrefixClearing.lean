import GaloisForLFunctions.HTGeometry.JetPrefixPolynomial

/-!
# Clearing denominators back into a differential relation

Every element of the jet prefix field is a fraction of polynomial expressions in the low jets.  So a
univariate relation of the top jet over that field, after multiplication by one common denominator,
becomes a scalar differential relation over the coefficient field with the same degree in the top
jet and no higher jets.

Together with the univariate polynomial attached to the characteristic, this pins the degree of the
minimal polynomial of the top jet: it is exactly the leader degree of the characteristic.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

section

variable (B : IntermediateField F E) (y : E) (m : ℕ)

/-- **The jet prefix field consists of fractions in the low jets.** -/
theorem exists_jetAdjoin_fraction {x : E} (hx : x ∈ jetAdjoin B y m) :
    ∃ R S : MvPolynomial (Fin m) B,
      MvPolynomial.aeval (fun i : Fin m => differentialJet i y) S ≠ 0 ∧
        x * MvPolynomial.aeval (fun i : Fin m => differentialJet i y) S =
          MvPolynomial.aeval (fun i : Fin m => differentialJet i y) R := by
  classical
  rw [mem_jetAdjoin_iff, jetAdjoinOver, IntermediateField.mem_adjoin_iff_div] at hx
  obtain ⟨r, hr, s, hs, hx⟩ := hx
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨R, rfl⟩ := hr
  obtain ⟨S, rfl⟩ := hs
  have hx' : x = MvPolynomial.aeval (fun i : Fin m => differentialJet i y) R /
      MvPolynomial.aeval (fun i : Fin m => differentialJet i y) S := hx
  by_cases hS : MvPolynomial.aeval (fun i : Fin m => differentialJet i y) S = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [hx', hS, div_zero]
    simp
  · exact ⟨R, S, hS, by rw [hx']; field_simp⟩

/-- **Clearing denominators.**  A monic univariate relation of the top jet over the jet prefix field
becomes a scalar differential relation over the coefficient field, with no jets above `m` and with
exactly the same degree in the top jet. -/
theorem exists_differentialRelation_of_monic
    {q : Polynomial (jetAdjoin B y m)} (hmonic : q.Monic)
    (hz : Polynomial.aeval (differentialJet m y) q = 0) :
    ∃ Q : DifferentialPolynomial Unit B,
      Q ∈ differentialIntermediateRelationIdeal B y ∧
        (∀ r ∈ Q.vars, r.2 ≤ m) ∧
        MvPolynomial.degreeOf ((), m) Q = q.natDegree := by
  classical
  set jets : Fin m → E := fun i => differentialJet i y with hjets
  set e := q.natDegree with he
  have hfrac : ∀ i : ℕ, ∃ RS : MvPolynomial (Fin m) B × MvPolynomial (Fin m) B,
      MvPolynomial.aeval jets RS.2 ≠ 0 ∧
        ((q.coeff i : E)) * MvPolynomial.aeval jets RS.2 =
          MvPolynomial.aeval jets RS.1 := by
    intro i
    obtain ⟨R, S, h1, h2⟩ := exists_jetAdjoin_fraction B y m (q.coeff i).2
    exact ⟨(R, S), h1, h2⟩
  choose RS hD hEq using hfrac
  set S : MvPolynomial (Fin m) B := ∏ i ∈ Finset.range (e + 1), (RS i).2 with hS
  set c : ℕ → MvPolynomial (Fin m) B :=
    fun i => (RS i).1 * ∏ j ∈ (Finset.range (e + 1)).erase i, (RS j).2 with hc
  have hSne : MvPolynomial.aeval jets S ≠ 0 := by
    rw [hS, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hD i
  have hkey : ∀ i ∈ Finset.range (e + 1),
      MvPolynomial.aeval jets (c i) = (q.coeff i : E) * MvPolynomial.aeval jets S := by
    intro i hi
    rw [hc]
    simp only [map_mul, map_prod]
    rw [← hEq i, mul_assoc,
      Finset.mul_prod_erase (Finset.range (e + 1))
        (fun j => MvPolynomial.aeval jets (RS j).2) hi, hS, map_prod]
  set ι' : Fin m → {j : Unit × ℕ // j ≠ ((), m)} := fun i => ⟨((), (i : ℕ)), by
    simp only [ne_eq, Prod.mk.injEq, not_and]
    exact fun _ => Nat.ne_of_lt i.2⟩ with hι'
  have hι'inj : Function.Injective ι' := by
    intro a b hab
    have h2 : ((ι' a : Unit × ℕ)) = ((ι' b : Unit × ℕ)) := congrArg Subtype.val hab
    exact Fin.ext (congrArg Prod.snd h2)
  set Q : DifferentialPolynomial Unit B :=
    ∑ i ∈ Finset.range (e + 1),
      MvPolynomial.rename (fun j : Fin m => (ι' j : Unit × ℕ)) (c i) *
        MvPolynomial.X ((), m) ^ i with hQ
  have hrename : ∀ p : MvPolynomial (Fin m) B,
      differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y)
          (MvPolynomial.rename (fun j : Fin m => (ι' j : Unit × ℕ)) p) =
        MvPolynomial.aeval jets p := by
    intro p
    rw [differentialPolynomialEvalOver, MvPolynomial.aeval_rename]
    rfl
  have heval : differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y) Q = 0 := by
    rw [hQ, map_sum]
    simp only [map_mul, map_pow, differentialPolynomialEvalOver_X, hrename]
    have hstep : ∀ i ∈ Finset.range (e + 1),
        MvPolynomial.aeval jets (c i) * differentialJet m y ^ i =
          MvPolynomial.aeval jets S * ((q.coeff i : E) * differentialJet m y ^ i) := by
      intro i hi
      rw [hkey i hi]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    have hq : Polynomial.aeval (differentialJet m y) q =
        ∑ i ∈ Finset.range (e + 1), (q.coeff i : E) * differentialJet m y ^ i := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
      rfl
    rw [← hq, hz, mul_zero]
  have hvars : ∀ r ∈ Q.vars, r.2 ≤ m := by
    intro r hr
    rw [hQ] at hr
    obtain ⟨i, -, hri⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hr)
    rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hri) with h1 | h2
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h1)
      rw [← hj]
      exact le_of_lt j.2
    · have hx : r ∈ (MvPolynomial.X ((), m) : DifferentialPolynomial Unit B).vars :=
        MvPolynomial.vars_pow _ _ h2
      rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx
      rw [hx]
  have hequiv : mvPolynomialPolynomialEquivAt ((), m) Q =
      ∑ i ∈ Finset.range (e + 1),
        Polynomial.C (MvPolynomial.rename ι' (c i)) * Polynomial.X ^ i := by
    rw [hQ, map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_mul, map_pow, mvPolynomialPolynomialEquivAt_X_self]
    congr 1
    rw [show (fun j : Fin m => (ι' j : Unit × ℕ)) = Subtype.val ∘ ι' from rfl,
      ← MvPolynomial.rename_rename]
    exact mvPolynomialPolynomialEquivAt_rename_ne _ _
  have hcoeff : ∀ k : ℕ,
      (∑ i ∈ Finset.range (e + 1),
        Polynomial.C (MvPolynomial.rename ι' (c i)) * Polynomial.X ^ i).coeff k =
        if k ∈ Finset.range (e + 1) then MvPolynomial.rename ι' (c k) else 0 := by
    intro k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    exact Finset.sum_ite_eq (Finset.range (e + 1)) k fun i => MvPolynomial.rename ι' (c i)
  have hce : c e ≠ 0 := by
    intro h0
    apply hSne
    have hkeye := hkey e (Finset.self_mem_range_succ e)
    rw [h0, map_zero, he, hmonic.coeff_natDegree] at hkeye
    simpa using hkeye.symm
  have hae : MvPolynomial.rename ι' (c e) ≠ 0 := fun h0 =>
    hce (MvPolynomial.rename_injective ι' hι'inj (by simpa using h0))
  have hnat : (∑ i ∈ Finset.range (e + 1),
      Polynomial.C (MvPolynomial.rename ι' (c i)) * Polynomial.X ^ i).natDegree = e := by
    refine le_antisymm ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hcoeff N, if_neg (by simp; omega)]
    · refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [hcoeff e, if_pos (Finset.self_mem_range_succ e)]
      exact hae
  refine ⟨Q, heval, hvars, ?_⟩
  rw [mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt, ← mvPolynomialPolynomialEquivAt_apply,
    hequiv, hnat]

end

section

variable {B : IntermediateField F E} {y : E} {P : DifferentialPolynomial Unit B}

/-- **Lower bound for Ritt's degree equality.**  The leader degree of the characteristic is at most
the degree of the minimal polynomial of the top jet over the jet prefix field: a smaller minimal
polynomial would clear denominators into a relation of smaller rank. -/
theorem leaderDegree_le_minpoly_natDegree
    (hmin : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal B y : Set _) P) :
    scalarDifferentialPolynomialLeaderDegree P ≤
      (minpoly (jetAdjoin B y (scalarDifferentialPolynomialOrder P))
        (differentialJet (scalarDifferentialPolynomialOrder P) y)).natDegree := by
  classical
  set m := scalarDifferentialPolynomialOrder P with hm
  set z := differentialJet m y with hz
  have hint : IsIntegral (jetAdjoin B y m) z := isIntegral_differentialJet_of_minimal hmin
  set qm := minpoly (jetAdjoin B y m) z with hqm
  have hmonic : qm.Monic := minpoly.monic hint
  have hdeg : 1 ≤ qm.natDegree := minpoly.natDegree_pos hint
  have haeval : Polynomial.aeval z qm = 0 := minpoly.aeval _ _
  obtain ⟨Q, hQmem, hQvars, hQdeg⟩ :=
    exists_differentialRelation_of_monic B y m hmonic haeval
  have hleadmem : ((), m) ∈ Q.vars := by
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, hQdeg]
    omega
  have hQne : Q ≠ 0 := by
    intro h0
    rw [h0] at hleadmem
    simp at hleadmem
  have hQvarsNe : Q.vars.Nonempty := ⟨((), m), hleadmem⟩
  have hQorder : scalarDifferentialPolynomialOrder Q = m := by
    refine le_antisymm ?_ ?_
    · exact Finset.sup_le fun j hj => hQvars j hj
    · exact Finset.le_sup (f := fun j : Unit × ℕ ↦ j.2) hleadmem
  have hQleader : scalarDifferentialPolynomialLeaderDegree Q = qm.natDegree := by
    rw [scalarDifferentialPolynomialLeaderDegree, scalarDifferentialPolynomialLeader, hQorder,
      hQdeg]
  have hcmp := (hmin.2.2.2 (SetLike.mem_coe.mpr hQmem) hQne hQvarsNe).2.1 (by rw [hQorder])
  rw [hQleader] at hcmp
  exact hcmp

/-- **Ritt's degree equality.**  The minimal polynomial of the top jet over the field generated by
the lower jets has degree exactly the leader degree of the characteristic. -/
theorem minpoly_natDegree_eq_leaderDegree
    (hmin : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal B y : Set _) P) :
    (minpoly (jetAdjoin B y (scalarDifferentialPolynomialOrder P))
        (differentialJet (scalarDifferentialPolynomialOrder P) y)).natDegree =
      scalarDifferentialPolynomialLeaderDegree P :=
  le_antisymm (minpoly_natDegree_le_leaderDegree hmin) (leaderDegree_le_minpoly_natDegree hmin)

end

end

end GaloisForLFunctions
