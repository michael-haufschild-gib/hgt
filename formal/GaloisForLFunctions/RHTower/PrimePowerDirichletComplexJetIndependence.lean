import GaloisForLFunctions.RHTower.PrimeShiftJetIndependence

/-!
# Heterogeneous complex-shift jets of prime-power Dirichlet sources

The existing prime-feature theorem proves differential independence of every finite family of
distinct complex shifts.  This file records the card's literal heterogeneous finite-jet form:
each shift may carry its own derivative cutoff.  It also specializes the result to the filtered
von Mangoldt source exposed by the completed-Xi `+2` increment.
-/

namespace RHTower

open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.PrimeShiftJet

/-- A differentially independent finite family remains algebraically independent after selecting
an arbitrary finite derivative block at each coordinate. -/
theorem differentialIndependent_algebraicIndependent_heterogeneousJets
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {q : ℕ} {x : Fin q → K}
    (hx : DifferentialIndependent F x) (ν : Fin q → ℕ) :
    AlgebraicIndependent F
      (fun jk : (j : Fin q) × Fin (ν j + 1) =>
        differentialJet (jk.2 : ℕ) (x jk.1)) := by
  let e : ((j : Fin q) × Fin (ν j + 1)) → Fin q × ℕ :=
    fun jk => (jk.1, (jk.2 : ℕ))
  have he : Function.Injective e := by
    rintro ⟨j, k⟩ ⟨l, n⟩ h
    change (j, (k : ℕ)) = (l, (n : ℕ)) at h
    have hj : j = l := congrArg Prod.fst h
    subst l
    have hkn : (k : ℕ) = (n : ℕ) := congrArg Prod.snd h
    have hk : k = n := Fin.ext hkn
    subst n
    rfl
  unfold DifferentialIndependent at hx
  have h := AlgebraicIndependent.comp hx e he
  convert h using 1
  rfl

/-- Coefficient-side form of the card theorem over the constant field: arbitrary finite complex
shifts and arbitrary per-shift derivative cutoffs of a prime-power source are algebraically
independent. -/
theorem primePowerDirichlet_complexShiftJets_algebraicIndependent
    {q : ℕ} [Nonempty (Fin q)] (F : ArithmeticFunction ℂ)
    (hsupport : SupportedOnPositivePrimePowers F)
    (hzeros : {p : Nat.Primes | F ((p : ℕ)) = 0}.Finite)
    (h : Fin q → ℂ) (hdistinct : Function.Injective h)
    (ν : Fin q → ℕ) :
    AlgebraicIndependent ℂ
      (fun jk : (j : Fin q) × Fin (ν j + 1) =>
        differentialJet (jk.2 : ℕ)
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (dirichletShift (h jk.1) F))) := by
  exact differentialIndependent_algebraicIndependent_heterogeneousJets
    (dirichletShiftFamily_differentialIndependent
      F hsupport hzeros h hdistinct) ν

local instance primePowerJetUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance primePowerJetUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance primePowerJetUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- Analytic upper-end form: the actual meromorphic carriers of the heterogeneous complex-shift
jet packet are algebraically independent over the genuine rational coordinate field. -/
theorem primePowerDirichlet_upperEnd_complexShiftJets_algebraicIndependent
    {q : ℕ} [Nonempty (Fin q)] (S : finiteAbscissaArithmeticSubalgebra)
    (hsupport : SupportedOnPositivePrimePowers S.1)
    (hzeros : {p : Nat.Primes | S.1 ((p : ℕ)) = 0}.Finite)
    (h : Fin q → ℂ) (hdistinct : Function.Injective h)
    (ν : Fin q → ℕ) :
    AlgebraicIndependent upperEndRationalCoordinateField
      (fun jk : (j : Fin q) × Fin (ν j + 1) =>
        differentialJet (jk.2 : ℕ)
          (upperEndTranslationMeroEquiv (Complex.I * h jk.1)
            (finiteAbscissaLSeriesToUpperEndMero S))) := by
  exact differentialIndependent_algebraicIndependent_heterogeneousJets
    (dirichletShiftFamily_upperEnd_differentialIndependent
      S hsupport hzeros h hdistinct) ν

/-- Completed-Xi source specialization: every heterogeneous finite jet packet of distinct complex
translates of the filtered von Mangoldt carrier is algebraically independent over the genuine
rational coordinate field. -/
theorem filteredVonMangoldt_complexShiftJets_algebraicIndependent
    {q : ℕ} [Nonempty (Fin q)]
    (h : Fin q → ℂ) (hdistinct : Function.Injective h)
    (ν : Fin q → ℕ) :
    AlgebraicIndependent upperEndRationalCoordinateField
      (fun jk : (j : Fin q) × Fin (ν j + 1) =>
        differentialJet (jk.2 : ℕ)
          (upperEndTranslationMeroEquiv (Complex.I * h jk.1)
            filteredVonMangoldtUpperEndCarrier)) := by
  exact differentialIndependent_algebraicIndependent_heterogeneousJets
    (filteredVonMangoldt_translates_differentialIndependent h hdistinct) ν

end

end RHTower
