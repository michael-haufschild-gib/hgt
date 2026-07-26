import GaloisForLFunctions.RHTower.PrimeArchCombinedResidualSonin

/-!
# Prime-Arch cofinal irreducible negative-Hankel universality

Failure of RH produces negative prime--Gamma source-Hankel witnesses not merely somewhere in each
infinite degree palette, but cofinally inside it.  Every witness may simultaneously be chosen
monic, irreducible, Eisenstein at two, and outside all three unconditional structured-positive
coefficient families.
-/

open Polynomial Set

namespace RHTower

noncomputable section

/-- **Cofinal irreducible negative-Hankel universality law.**  Under non-RH, every infinite
prescribed degree palette contains arbitrarily high monic irreducible `2`-Eisenstein tests in the
combined residual with strictly negative prime--Gamma source trace-Hankel value. -/
theorem exists_cofinal_irreducible_combinedResidualTwoEisenstein_negativeTraceHankel_of_not_rh
    {D : Set ℕ} (hD : D.Infinite) (hRH : ¬ RiemannHypothesis) (N : ℕ) :
    ∃ p : Polynomial ℤ,
      p.Monic ∧
        Irreducible p ∧
          p.IsEisensteinAt primeArchTwoEisensteinIdeal ∧
            p.natDegree ∈ D ∧
              N < p.natDegree ∧
                PrimeArchCombinedCoefficientResidual p ∧
                  (primeArchSourceTraceHankel
                    (p.map (Int.castRingHom ℝ))).re < 0 := by
  let Dtail : Set ℕ := D \ Set.Iic N
  have hDtail : Dtail.Infinite := hD.diff (Set.finite_Iic N)
  obtain ⟨p, hmonic, heisenstein, hdegree, hresidual, hnegative⟩ :=
    exists_combinedResidualTwoEisenstein_negativeTraceHankel_of_not_riemannHypothesis
      hDtail hRH
  have hdegreeD : p.natDegree ∈ D := hdegree.1
  have hdegreeAbove : N < p.natDegree := Nat.lt_of_not_ge hdegree.2
  have hdegreePos : 0 < p.natDegree := lt_of_le_of_lt (Nat.zero_le N) hdegreeAbove
  have hirreducible : Irreducible p :=
    irreducible_of_monic_primeArchTwoEisenstein hmonic heisenstein hdegreePos
  exact
    ⟨p, hmonic, hirreducible, heisenstein, hdegreeD, hdegreeAbove,
      hresidual, hnegative⟩

end

end RHTower
