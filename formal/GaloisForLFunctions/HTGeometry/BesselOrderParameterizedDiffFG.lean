import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedReduced

/-!
# Differential finite generation of the Bessel parameterized PV quotient

The four entries of the fundamental matrix and the inverse of its determinant differentially
generate the concrete parameterized Picard--Vessiot quotient over `Constants(z)`.  The final theorem
constructs the PPV datum, so no PPV existence or generation premise is retained.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

/-- Four fundamental-matrix entries and the inverse determinant. -/
def BesselOrderParameterizedPVData.diffGenerators {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    Fin 5 → ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
  ![
    Ideal.Quotient.mk data.M (ppvFundamental (RatFunc Constants) 2 0 0),
    Ideal.Quotient.mk data.M (ppvFundamental (RatFunc Constants) 2 0 1),
    Ideal.Quotient.mk data.M (ppvFundamental (RatFunc Constants) 2 1 0),
    Ideal.Quotient.mk data.M (ppvFundamental (RatFunc Constants) 2 1 1),
    data.detInverse
  ]

@[simp]
theorem BesselOrderParameterizedPVData.diffGenerators_zero_zero {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    data.diffGenerators 0 =
      Ideal.Quotient.mk data.M (ppvFundamental (RatFunc Constants) 2 0 0) := rfl

@[simp]
theorem BesselOrderParameterizedPVData.diffGenerators_zero_one {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    data.diffGenerators 1 =
      Ideal.Quotient.mk data.M (ppvFundamental (RatFunc Constants) 2 0 1) := rfl

@[simp]
theorem BesselOrderParameterizedPVData.diffGenerators_one_zero {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    data.diffGenerators 2 =
      Ideal.Quotient.mk data.M (ppvFundamental (RatFunc Constants) 2 1 0) := rfl

@[simp]
theorem BesselOrderParameterizedPVData.diffGenerators_one_one {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    data.diffGenerators 3 =
      Ideal.Quotient.mk data.M (ppvFundamental (RatFunc Constants) 2 1 1) := rfl

@[simp]
theorem BesselOrderParameterizedPVData.diffGenerators_inverse {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : data.diffGenerators 4 = data.detInverse := rfl

/-- Evaluation at the five concrete generators reaches every element of the PPV quotient. -/
theorem BesselOrderParameterizedPVData.diffGenerators_surjective {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    letI : Differential (RatFunc Constants) := coordinateTotalDifferential
    letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
      quotientDifferential data.M data.isSigmaDeltaIdeal.2
    Function.Surjective
      (differentialPolynomialEvalOver (K := RatFunc Constants) data.diffGenerators) := by
  letI : Differential (RatFunc Constants) := coordinateTotalDifferential
  letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
    quotientDifferential data.M data.isSigmaDeltaIdeal.2
  let Ψ := differentialPolynomialEvalOver (K := RatFunc Constants) data.diffGenerators
  have hjet : ∀ i j k,
      Ideal.Quotient.mk data.M
          (algebraMap (DifferentialPolynomial (Fin 2 × Fin 2) (RatFunc Constants))
            (ppvLocalization (RatFunc Constants) 2) (MvPolynomial.X ((i, j), k))) ∈
        Ψ.range := by
    intro i j k
    fin_cases i <;> fin_cases j
    · refine ⟨MvPolynomial.X ((0 : Fin 5), k), ?_⟩
      change Ψ (MvPolynomial.X ((0 : Fin 5), k)) = _
      rw [show Ψ (MvPolynomial.X ((0 : Fin 5), k)) =
        differentialJet k (data.diffGenerators 0) from
          differentialPolynomialEvalOver_X data.diffGenerators 0 k]
      rw [data.diffGenerators_zero_zero]
      unfold differentialJet
      convert data.jets_are_iteratedDeriv (0 : Fin 2) (0 : Fin 2) k using 1
      all_goals simp
    · refine ⟨MvPolynomial.X ((1 : Fin 5), k), ?_⟩
      change Ψ (MvPolynomial.X ((1 : Fin 5), k)) = _
      rw [show Ψ (MvPolynomial.X ((1 : Fin 5), k)) =
        differentialJet k (data.diffGenerators 1) from
          differentialPolynomialEvalOver_X data.diffGenerators 1 k]
      rw [data.diffGenerators_zero_one]
      unfold differentialJet
      convert data.jets_are_iteratedDeriv (0 : Fin 2) (1 : Fin 2) k using 1
      all_goals simp
    · refine ⟨MvPolynomial.X ((2 : Fin 5), k), ?_⟩
      change Ψ (MvPolynomial.X ((2 : Fin 5), k)) = _
      rw [show Ψ (MvPolynomial.X ((2 : Fin 5), k)) =
        differentialJet k (data.diffGenerators 2) from
          differentialPolynomialEvalOver_X data.diffGenerators 2 k]
      rw [data.diffGenerators_one_zero]
      unfold differentialJet
      convert data.jets_are_iteratedDeriv (1 : Fin 2) (0 : Fin 2) k using 1
      all_goals simp
    · refine ⟨MvPolynomial.X ((3 : Fin 5), k), ?_⟩
      change Ψ (MvPolynomial.X ((3 : Fin 5), k)) = _
      rw [show Ψ (MvPolynomial.X ((3 : Fin 5), k)) =
        differentialJet k (data.diffGenerators 3) from
          differentialPolynomialEvalOver_X data.diffGenerators 3 k]
      rw [data.diffGenerators_one_one]
      unfold differentialJet
      convert data.jets_are_iteratedDeriv (1 : Fin 2) (1 : Fin 2) k using 1
      all_goals simp
  have hinv : data.detInverse ∈ Ψ.range := by
    refine ⟨MvPolynomial.X ((4 : Fin 5), 0), ?_⟩
    change Ψ (MvPolynomial.X ((4 : Fin 5), 0)) = _
    rw [show Ψ (MvPolynomial.X ((4 : Fin 5), 0)) =
      differentialJet 0 (data.diffGenerators 4) from
        differentialPolynomialEvalOver_X data.diffGenerators 4 0,
      differentialJet_zero, data.diffGenerators_inverse]
  have hgen : Set.range (fun q : (Fin 2 × Fin 2) × ℕ =>
        Ideal.Quotient.mk data.M
          (algebraMap (DifferentialPolynomial (Fin 2 × Fin 2) (RatFunc Constants))
            (ppvLocalization (RatFunc Constants) 2) (MvPolynomial.X q))) ∪
        {data.detInverse} ⊆ Ψ.range := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨q, rfl⟩ := hx
      exact hjet q.1.1 q.1.2 q.2
    · rw [Set.mem_singleton_iff] at hx
      simpa [hx] using hinv
  have htop : Ψ.range = ⊤ := by
    apply top_unique
    rw [← data.generatedJets]
    exact Algebra.adjoin_le hgen
  intro x
  have hx : x ∈ Ψ.range := by
    rw [htop]
    trivial
  exact hx

/-- Unconditional differential finite generation of a concrete Bessel PPV quotient. -/
theorem besselOrder_parameterizedPicardVessiot_diffFG :
    ∀ s : ℝ, ∃ data : BesselOrderParameterizedPVData s,
      letI : Differential (RatFunc Constants) := coordinateTotalDifferential
      letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
        quotientDifferential data.M data.isSigmaDeltaIdeal.2
      Function.Surjective
        (differentialPolynomialEvalOver (K := RatFunc Constants) data.diffGenerators) := by
  intro s
  obtain ⟨data⟩ := besselOrder_parameterizedPicardVessiot_exists s
  exact ⟨data, data.diffGenerators_surjective⟩

/-- One unconditionally constructed Bessel PPV quotient is simultaneously reduced and
differentially generated by the five concrete generators. -/
theorem besselOrder_parameterizedPicardVessiot_reduced_diffFG :
    ∀ s : ℝ, ∃ data : BesselOrderParameterizedPVData s,
      IsReduced ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) ∧
      (letI : Differential (RatFunc Constants) := coordinateTotalDifferential
       letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
         quotientDifferential data.M data.isSigmaDeltaIdeal.2
       Function.Surjective
         (differentialPolynomialEvalOver (K := RatFunc Constants) data.diffGenerators)) := by
  intro s
  obtain ⟨data⟩ := besselOrder_parameterizedPicardVessiot_exists s
  exact ⟨data, data.isReduced, data.diffGenerators_surjective⟩

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
