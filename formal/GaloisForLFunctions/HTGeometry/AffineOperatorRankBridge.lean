import GaloisForLFunctions.HTGeometry.AffineOperatorRankLaw

/-!
# Operator rank as linear independence of the shifted rows

The coefficient vector of a row of constant-coefficient operators identifies the row space with a
finitely supported complex vector space.  Under that identification the family of all shifts
`∂^γ · L_i` corresponds to the operator rows scaled by monomials, so complex linear independence of
the shifts is exactly linear independence of the rows over the operator ring, i.e. the operator
rank of the matrix `(L_{i,λ})`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {d m n : ℕ}

/-- The coefficient vector of a row of operators. -/
def rowVector (p : Fin n → MvPolynomial (Fin d) ℂ) : (Fin n × (Fin d →₀ ℕ)) →₀ ℂ :=
  ∑ j : Fin n, ∑ δ ∈ (p j).support, Finsupp.single (j, δ) (coeff δ (p j))

theorem shiftedSingleSum_apply (r : MvPolynomial (Fin d) ℂ) (γ δ : Fin d →₀ ℕ) (j : Fin n) :
    (∑ β ∈ r.support, Finsupp.single ((j, γ + β) : Fin n × (Fin d →₀ ℕ)) (coeff β r)) (j, δ) =
      coeff δ (monomial γ (1 : ℂ) * r) := by
  classical
  rw [Finsupp.finsetSum_apply, coeff_monomial_mul']
  simp only [Finsupp.single_apply, Prod.mk.injEq, true_and]
  by_cases hle : γ ≤ δ
  · rw [if_pos hle, one_mul]
    have hcond : ∀ β : Fin d →₀ ℕ, (γ + β = δ) ↔ (β = δ - γ) := by
      intro β
      constructor
      · intro h
        rw [← h, add_tsub_cancel_left]
      · intro h
        rw [h, add_tsub_cancel_of_le hle]
    have hsum : (∑ β ∈ r.support, if γ + β = δ then coeff β r else 0) =
        ∑ β ∈ r.support, if β = δ - γ then coeff β r else 0 := by
      refine Finset.sum_congr rfl fun β _ => ?_
      by_cases h : γ + β = δ
      · rw [if_pos h, if_pos ((hcond β).mp h)]
      · rw [if_neg h, if_neg fun hc => h ((hcond β).mpr hc)]
    rw [hsum, Finset.sum_ite_eq' r.support (δ - γ) (fun β => coeff β r)]
    by_cases hmem : δ - γ ∈ r.support
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      exact (MvPolynomial.notMem_support_iff.mp hmem).symm
  · rw [if_neg hle]
    refine Finset.sum_eq_zero fun β _ => ?_
    refine if_neg fun hc => hle ?_
    exact hc ▸ le_self_add

theorem shiftedRowSum_apply (q : Fin n → MvPolynomial (Fin d) ℂ) (γ : Fin d →₀ ℕ)
    (j : Fin n) (δ : Fin d →₀ ℕ) :
    (∑ j' : Fin n, ∑ β ∈ (q j').support,
        Finsupp.single ((j', γ + β) : Fin n × (Fin d →₀ ℕ)) (coeff β (q j'))) (j, δ) =
      coeff δ (monomial γ (1 : ℂ) * q j) := by
  classical
  rw [Finsupp.finsetSum_apply,
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_]
  · exact shiftedSingleSum_apply (q j) γ δ j
  · intro j' _ hne
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    refine Finsupp.single_eq_of_ne fun hcon => hne ?_
    simp only [Prod.mk.injEq] at hcon
    exact hcon.1.symm

@[simp] theorem rowVector_apply (p : Fin n → MvPolynomial (Fin d) ℂ) (j : Fin n)
    (δ : Fin d →₀ ℕ) : rowVector p (j, δ) = coeff δ (p j) := by
  have := shiftedRowSum_apply p 0 j δ
  simpa [rowVector, monomial_zero'] using this

theorem rowVector_ext_iff (p q : Fin n → MvPolynomial (Fin d) ℂ) :
    rowVector p = rowVector q ↔ p = q := by
  constructor
  · intro h
    funext j
    ext δ
    have := congrArg (fun t : (Fin n × (Fin d →₀ ℕ)) →₀ ℂ => t (j, δ)) h
    simpa using this
  · intro h; rw [h]

theorem rowVector_add (p q : Fin n → MvPolynomial (Fin d) ℂ) :
    rowVector (p + q) = rowVector p + rowVector q := by
  ext ⟨j, δ⟩
  simp

theorem rowVector_smul (c : ℂ) (p : Fin n → MvPolynomial (Fin d) ℂ) :
    rowVector (c • p) = c • rowVector p := by
  ext ⟨j, δ⟩
  simp [MvPolynomial.coeff_smul]

theorem rowVector_zero : rowVector (0 : Fin n → MvPolynomial (Fin d) ℂ) = 0 := by
  ext ⟨j, δ⟩
  simp

theorem rowVector_sum {ι : Type*} (s : Finset ι) (F : ι → Fin n → MvPolynomial (Fin d) ℂ) :
    rowVector (∑ i ∈ s, F i) = ∑ i ∈ s, rowVector (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [rowVector_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, rowVector_add, ih, Finset.sum_insert ha]

/-- Every coefficient vector comes from a row of operators. -/
theorem rowVector_surjective (κ : (Fin n × (Fin d →₀ ℕ)) →₀ ℂ) :
    ∃ p : Fin n → MvPolynomial (Fin d) ℂ, rowVector p = κ := by
  classical
  refine ⟨fun i => ∑ q ∈ κ.support, if q.1 = i then monomial q.2 (κ q) else 0, ?_⟩
  ext ⟨j, δ⟩
  rw [rowVector_apply, MvPolynomial.coeff_sum]
  by_cases hmem : (j, δ) ∈ κ.support
  · rw [Finset.sum_eq_single (j, δ) ?_ ?_]
    · simp
    · intro q _ hq
      by_cases h1 : q.1 = j
      · rw [if_pos h1, coeff_monomial, if_neg]
        intro h2
        exact hq (Prod.ext h1 h2)
      · rw [if_neg h1, MvPolynomial.coeff_zero]
    · intro h; exact absurd hmem h
  · rw [Finsupp.notMem_support_iff.mp hmem]
    refine Finset.sum_eq_zero fun q hq => ?_
    by_cases h1 : q.1 = j
    · rw [if_pos h1, coeff_monomial, if_neg]
      intro h2
      refine hmem ?_
      have hqe : q = (j, δ) := Prod.ext h1 h2
      rwa [hqe] at hq
    · rw [if_neg h1, MvPolynomial.coeff_zero]

/-- The substitution vector of an operator matrix is the coefficient vector of the shifted row. -/
theorem operatorJetSubstVector_eq (L : Fin m → Fin n → MvPolynomial (Fin d) ℂ)
    (i : Fin m) (γ : Fin d →₀ ℕ) :
    operatorJetSubstVector L (i, γ) = rowVector (fun j => monomial γ (1 : ℂ) * L i j) := by
  ext ⟨j, δ⟩
  rw [rowVector_apply, operatorJetSubstVector]
  exact shiftedRowSum_apply (L i) γ j δ

/-- **Operator rank.**  Complex linear independence of the shifted rows is linear independence of
the rows over the ring of constant-coefficient operators. -/
theorem linearIndependent_operatorJetSubstVector_iff
    (L : Fin m → Fin n → MvPolynomial (Fin d) ℂ) :
    LinearIndependent ℂ (operatorJetSubstVector L) ↔
      LinearIndependent (MvPolynomial (Fin d) ℂ) L := by
  classical
  have hcomb : ∀ g : Fin m → MvPolynomial (Fin d) ℂ,
      Finsupp.linearCombination ℂ (operatorJetSubstVector L) (rowVector g) =
        rowVector (∑ i : Fin m, g i • L i) := by
    intro g
    rw [rowVector, map_sum, rowVector_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    have hstep : ∀ δ ∈ (g i).support,
        Finsupp.linearCombination ℂ (operatorJetSubstVector L)
            (Finsupp.single ((i, δ) : Fin m × (Fin d →₀ ℕ)) (coeff δ (g i))) =
          rowVector (coeff δ (g i) • (fun j => monomial δ (1 : ℂ) * L i j)) := by
      intro δ _
      rw [Finsupp.linearCombination_single, operatorJetSubstVector_eq, rowVector_smul]
    rw [Finset.sum_congr rfl hstep, ← rowVector_sum]
    congr 1
    funext j
    have hsupp : ∑ δ ∈ (g i).support,
        (coeff δ (g i) • (fun j => monomial δ (1 : ℂ) * L i j)) j =
        (∑ δ ∈ (g i).support, monomial δ (coeff δ (g i))) * L i j := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [Pi.smul_apply, smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one]
    simpa [MvPolynomial.support_sum_monomial_coeff] using hsupp
  constructor
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : Finsupp.linearCombination ℂ (operatorJetSubstVector L) (rowVector g) = 0 := by
      rw [hcomb g, hg, rowVector_zero]
    have := linearIndependent_iff.mp h _ h0
    have hg0 : g = 0 := (rowVector_ext_iff g 0).mp (by rw [this, rowVector_zero])
    exact congrFun hg0 i
  · intro h
    rw [linearIndependent_iff]
    intro κ hκ
    obtain ⟨g, rfl⟩ := rowVector_surjective κ
    rw [hcomb g] at hκ
    have hzero : ∑ i : Fin m, g i • L i = 0 :=
      (rowVector_ext_iff _ 0).mp (by rw [hκ, rowVector_zero])
    have := (Fintype.linearIndependent_iff.mp h) g hzero
    rw [show g = 0 from funext this, rowVector_zero]

/-- **Operator-rank law, independent rows.**  Rows independent over the ring of
constant-coefficient operators produce outputs satisfying no nonzero differential relation on a
generic source. -/
theorem exists_jetRelationValue_operatorRowSource_ne_zero_of_linearIndependent
    {d : ℕ} (hd : 0 < d) {Λ : Type*} [Countable Λ]
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    {f : MultivariateEntire d} (hf : f ∈ affineJetPacketGenericSet hd frame hframe)
    {n : ℕ} (lab : Fin n → Λ) (hlab : Function.Injective lab)
    {m : ℕ} (L : Fin m → Fin n → MvPolynomial (Fin d) ℂ)
    (hL : LinearIndependent (MvPolynomial (Fin d) ℂ) L)
    {Q : MvPolynomial (Fin m × (Fin d →₀ ℕ)) (MvPolynomial (Fin d) ℂ)} (hQ : Q ≠ 0) :
    ∃ z : Fin d → ℂ,
      jetRelationValue (fun i => operatorRowSource (fun j => frame (lab j)) f (L i)) Q z ≠ 0 :=
  exists_jetRelationValue_operatorRowSource_ne_zero hd frame hframe hf lab hlab L
    ((linearIndependent_operatorJetSubstVector_iff L).mpr hL) hQ

/-- **Operator-rank law, dependent rows.**  Rows dependent over the ring of constant-coefficient
operators produce outputs satisfying a nonzero linear differential relation. -/
theorem exists_nonzero_jetRelation_of_not_linearIndependent_operator {d m n : ℕ}
    (frame : Fin n → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (f : MultivariateEntire d)
    (L : Fin m → Fin n → MvPolynomial (Fin d) ℂ)
    (hL : ¬ LinearIndependent (MvPolynomial (Fin d) ℂ) L) :
    ∃ Q : MvPolynomial (Fin m × (Fin d →₀ ℕ)) (MvPolynomial (Fin d) ℂ), Q ≠ 0 ∧
      ∀ z : Fin d → ℂ,
        jetRelationValue (fun i => operatorRowSource frame f (L i)) Q z = 0 :=
  exists_nonzero_jetRelation_of_not_linearIndependent frame f L
    fun h => hL ((linearIndependent_operatorJetSubstVector_iff L).mp h)

end

end GaloisForLFunctions.HTGeometry
