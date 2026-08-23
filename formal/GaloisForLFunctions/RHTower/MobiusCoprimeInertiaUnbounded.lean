import GaloisForLFunctions.RHTower.MobiusCoprimeInertia
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

open scoped ArithmeticFunction.Moebius

namespace RHTower

noncomputable section

/-- The first `k` primes inject into the negative Möbius coordinates below the `k`th prime. -/
theorem card_negativeMobiusCoordinates_nthPrime_ge (k : ℕ) :
    k ≤ ({d | μ d.1 = -1} :
      Finset (finiteMobiusCoprimeCoordinate (nthPrimeSubtype k : ℕ))).card := by
  let negSet : Finset (finiteMobiusCoprimeCoordinate (nthPrimeSubtype k : ℕ)) :=
    {d | μ d.1 = -1}
  let f : Fin k → {d // d ∈ negSet} := fun i =>
    ⟨⟨(nthPrimeSubtype i.1 : ℕ), Finset.mem_Icc.mpr
      ⟨(nthPrimeSubtype i.1).prop.one_le,
        nthPrimeSubtype_strictMono.monotone (Nat.le_of_lt i.2)⟩⟩,
      by simp [negSet, ArithmeticFunction.moebius_apply_prime,
        (nthPrimeSubtype i.1).prop]⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply nthPrimeSubtype_injective
    apply Subtype.ext
    exact congrArg (fun d => d.1.1) hij
  have hcard := Fintype.card_le_of_injective f hinj
  have hcoe : Fintype.card {d // d ∈ negSet} = negSet.card :=
    Fintype.card_coe negSet
  rw [Fintype.card_fin, hcoe] at hcard
  simpa [negSet] using hcard

/-- The negative inertia of finite coprimality matrices is unbounded. -/
theorem finiteMobiusCoprimeMatrixComplex_negativeInertia_unbounded (k : ℕ) :
    ∃ N : ℕ, k ≤
      GaloisForLFunctions.HTGeometry.hermNegIndex (finiteMobiusCoprimeMatrixComplex N) := by
  refine ⟨(nthPrimeSubtype k : ℕ), ?_⟩
  rw [hermNegIndex_finiteMobiusCoprimeMatrixComplex]
  exact card_negativeMobiusCoordinates_nthPrime_ge k

end

end RHTower
