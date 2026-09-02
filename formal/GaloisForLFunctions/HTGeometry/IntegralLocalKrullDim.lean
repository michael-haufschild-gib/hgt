import GaloisForLFunctions.HTGeometry.IntegralExtensionKrullDim
import GaloisForLFunctions.HTGeometry.IntegralLocalMaximalRadical
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Local dimension in an integral extension with going down

If `A` is local, `D` is integral over `A`, going down holds, and `q` is maximal in `D`, then the
local ring `D_q` has the same Krull dimension as `A`.  Contraction gives one inequality by
incomparability.  Going down lifts every prime chain in `A` below the chosen `q`, giving the other.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing Order

universe u v

/-- **A maximal localization of an integral going-down algebra has the dimension of the local
base.** -/
theorem ringKrullDim_localizationAtMaximal_eq_of_isIntegral_of_hasGoingDown
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.IsIntegral A D] [Algebra.HasGoingDown A D] [IsLocalRing A]
    (q : Ideal D) [q.IsMaximal] :
    ringKrullDim (Localization.AtPrime q) = ringKrullDim A := by
  let B := Localization.AtPrime q
  have hqcomap : Ideal.comap (algebraMap A D) q = maximalIdeal A := by
    apply IsLocalRing.eq_maximalIdeal
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro p P hpP
    have hD : p.asIdeal.comap (algebraMap D B) <
        P.asIdeal.comap (algebraMap D B) := by
      have hsub :
          (⟨p.asIdeal, p.isPrime⟩ : {J : Ideal B // J.IsPrime}) <
            ⟨P.asIdeal, P.isPrime⟩ := hpP
      exact (IsLocalization.AtPrime.orderIsoOfPrime B q).strictMono hsub
    have hA := Ideal.IsIntegral.comap_lt_comap (R := A) (A := D) hD
    change Ideal.comap (algebraMap A B) p.asIdeal <
      Ideal.comap (algebraMap A B) P.asIdeal
    simpa only [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A D B] using hA
  · refine iSup_le fun l => ?_
    have hlastle : l.last.asIdeal ≤ maximalIdeal A :=
      IsLocalRing.le_maximalIdeal l.last.isPrime.ne_top
    letI : q.LiesOver (maximalIdeal A) := ⟨hqcomap.symm⟩
    obtain ⟨P, hPq, hPprime, hPlo⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (Q := q)
        (p := l.last.asIdeal) (q := maximalIdeal A) hlastle
    letI : P.IsPrime := hPprime
    letI : P.LiesOver l.last.asIdeal := hPlo
    obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
    have hLle : ∀ i, (L i).asIdeal ≤ q := by
      intro i
      have hi : L i ≤ L.last := L.strictMono.monotone (Fin.le_last i)
      have hiP : (L i).asIdeal ≤ P := by
        change (L i).asIdeal ≤ L.last.asIdeal at hi
        rw [hlast] at hi
        exact hi
      exact hiP.trans hPq
    let e := IsLocalization.AtPrime.primeSpectrumOrderIso B q
    let LB : LTSeries (PrimeSpectrum B) :=
      { length := L.length
        toFun := fun i => e.symm ⟨L i, hLle i⟩
        step := fun i => e.symm.strictMono
          (show (⟨L i.castSucc, hLle i.castSucc⟩ : Set.Iic
              (⟨q, by infer_instance⟩ : PrimeSpectrum D)) <
            ⟨L i.succ, hLle i.succ⟩ from L.strictMono Fin.castSucc_lt_succ) }
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim LB

end GaloisForLFunctions.HTGeometry
