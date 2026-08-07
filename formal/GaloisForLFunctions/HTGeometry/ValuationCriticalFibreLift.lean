import GaloisForLFunctions.HTGeometry.ValuationCriticalFibreIntegrality

/-!
# Descent of integral critical-fibre points to a valuation subring

Once valuative integrality supplies membership of every low coefficient, this module reconstructs
the point over the valuation subring and reflects its truncated compatibility equation through the
injective subtype map.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- Lift a polynomial of degree below `d` whose coefficients lie in a valuation subring. -/
noncomputable def valuationSubringLowLift
    {L : Type*} [Field L] (O : ValuationSubring L)
    {d : ℕ} (A : L[X]) (hA : ∀ i : Fin d, A.coeff i ∈ O) : O[X] :=
  lowPolynomial fun i => ⟨A.coeff i, hA i⟩

theorem valuationSubringLowLift_map
    {L : Type*} [Field L] (O : ValuationSubring L)
    {d : ℕ} {A : L[X]} (hAdeg : A.degree < (d : ℕ))
    (hA : ∀ i : Fin d, A.coeff i ∈ O) :
    (valuationSubringLowLift O A hA).map O.subtype = A := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < d
  · rw [Polynomial.coeff_map, valuationSubringLowLift, lowPolynomial_coeff, dif_pos hk]
    rfl
  · rw [Polynomial.coeff_map, valuationSubringLowLift, lowPolynomial_coeff, dif_neg hk,
      map_zero]
    exact ((Polynomial.degree_lt_iff_coeff_zero A d).mp hAdeg k
      (Nat.le_of_not_gt hk)).symm

/-- Descend a critical-fibre point whose low coefficients all belong to a valuation subring. -/
noncomputable def valuationSubringCriticalFibreLift
    {L : Type*} [Field L] (O : ValuationSubring L)
    {m n : ℕ} (US VS : O[X])
    (p : criticalFibre L m n (US.map O.subtype) (VS.map O.subtype))
    (hmem : (∀ i : Fin m, p.1.1.coeff i ∈ O) ∧
      ∀ j : Fin n, p.1.2.coeff j ∈ O) :
    criticalFibre O m n US VS := by
  classical
  let Ahat : O[X] := valuationSubringLowLift O p.1.1 hmem.1
  let Bhat : O[X] := valuationSubringLowLift O p.1.2 hmem.2
  have hmapA : Ahat.map O.subtype = p.1.1 :=
    valuationSubringLowLift_map O p.2.1 hmem.1
  have hmapB : Bhat.map O.subtype = p.1.2 :=
    valuationSubringLowLift_map O p.2.2.1 hmem.2
  refine ⟨(Ahat, Bhat), lowPolynomial_degree_lt _, lowPolynomial_degree_lt _, ?_⟩
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  apply O.subtype_injective
  have hpzero := (Polynomial.X_pow_dvd_iff.mp p.2.2.2) k hk
  have hmapDefect :
      (criticalLowProduct US VS Ahat Bhat - 1).map O.subtype =
        criticalLowProduct (US.map O.subtype) (VS.map O.subtype) p.1.1 p.1.2 - 1 := by
    simp only [criticalLowProduct, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_one, hmapA, hmapB]
  have hcoeff := congrArg (fun q : L[X] => q.coeff k) hmapDefect
  rw [Polynomial.coeff_map] at hcoeff
  rw [hcoeff, hpzero, map_zero]

end


end GaloisForLFunctions.HTGeometry
