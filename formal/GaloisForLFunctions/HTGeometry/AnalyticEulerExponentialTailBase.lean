import GaloisForLFunctions.HTGeometry.AnalyticDirichletCompleteRelationPresentation

/-!
# The analytic Euler-exponential tail base

The intrinsic analytic base for coefficient tails is obtained by adjoining every single-prime
Dirichlet exponential to the embedded coordinate field.  Every finitely supported prime source,
and every derivative of its carrier, lies in this base.  This is the descent bridge required to
make bounded prime coefficient streams depend only on their classes modulo finite support.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential

noncomputable section

attribute [local instance]
  analyticObservableUpperEndAnalyticDomain
  analyticObservableUpperEndMeroComplexAlgebra
  analyticObservableUpperEndMeroDifferential

/-- The Kronecker coefficient stream supported at one prime. -/
def primeKroneckerCoefficient (q p : Nat.Primes) : ℂ :=
  if p = q then 1 else 0

theorem primeKroneckerCoefficient_norm_le_one (q p : Nat.Primes) :
    ‖primeKroneckerCoefficient q p‖ ≤ 1 := by
  unfold primeKroneckerCoefficient
  split <;> norm_num

/-- The actual single-prime Dirichlet exponential at a common shift. -/
def analyticSinglePrimeShiftCarrier (a : ℂ) (q : Nat.Primes) : upperEndMeroField :=
  analyticPrimeObservableShiftCarrier
    (primeKroneckerCoefficient q) 1 (primeKroneckerCoefficient_norm_le_one q) a

/-- The analytic Euler-exponential base: the coordinate field together with all single-prime
exponentials and all of their derivatives. -/
def analyticEulerExponentialBase (a : ℂ) :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  GaloisForLFunctions.differentialAdjoin upperEndRationalCoordinateField
    (Set.range (analyticSinglePrimeShiftCarrier a))

/-- The absolute coefficient mass of a finitely supported prime source. -/
def finitePrimeSourceBound (u : Nat.Primes →₀ ℂ) : ℝ :=
  u.sum fun _ z ↦ ‖z‖

theorem finitePrimeSource_norm_le_bound (u : Nat.Primes →₀ ℂ) (p : Nat.Primes) :
    ‖u p‖ ≤ finitePrimeSourceBound u := by
  classical
  unfold finitePrimeSourceBound Finsupp.sum
  by_cases hp : p ∈ u.support
  · exact Finset.single_le_sum (fun q _ ↦ norm_nonneg (u q)) hp
  · have hup : u p = 0 := by
      by_contra hne
      exact hp (Finsupp.mem_support_iff.mpr hne)
    rw [hup, norm_zero]
    exact Finset.sum_nonneg fun q _ ↦ norm_nonneg (u q)

/-- The analytic Dirichlet carrier of a finitely supported prime source. -/
def analyticFinitePrimeShiftCarrier (a : ℂ) (u : Nat.Primes →₀ ℂ) :
    upperEndMeroField :=
  analyticPrimeObservableShiftCarrier (fun p ↦ u p)
    (finitePrimeSourceBound u) (finitePrimeSource_norm_le_bound u) a

theorem finsupp_sum_primeKroneckerCoefficient
    (u : Nat.Primes →₀ ℂ) (p : Nat.Primes) :
    u.sum (fun q z ↦ z * primeKroneckerCoefficient q p) = u p := by
  classical
  unfold primeKroneckerCoefficient
  by_cases hp : p ∈ u.support
  · simpa [hp] using
      (Finsupp.sum_eq_single p (f := u)
        (g := fun q z ↦ z * if p = q then 1 else 0))
  · have hup : u p = 0 := by
      by_contra hne
      exact hp (Finsupp.mem_support_iff.mpr hne)
    rw [hup]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro q hq
    have hqp : q ≠ p := by
      intro h
      subst q
      exact hp hq
    simp [hqp, hqp.symm]

/-- A finite-prime carrier is exactly the corresponding finite linear combination of the
single-prime generators. -/
theorem analyticFinitePrimeShiftCarrier_eq_sum
    (a : ℂ) (u : Nat.Primes →₀ ℂ) :
    analyticFinitePrimeShiftCarrier a u =
      u.sum fun q z ↦ algebraMap ℂ upperEndMeroField z *
        analyticSinglePrimeShiftCarrier a q := by
  apply analyticPrimeObservableShiftCarrier_finsuppLinearCombination
    (primeKroneckerCoefficient) (fun _ ↦ 1)
    primeKroneckerCoefficient_norm_le_one u (fun p ↦ u p)
    (finitePrimeSourceBound u) (finitePrimeSource_norm_le_bound u)
  · intro p
    exact (finsupp_sum_primeKroneckerCoefficient u p).symm

/-- Every finitely supported prime carrier lies in the Euler-exponential base. -/
theorem analyticFinitePrimeShiftCarrier_mem_eulerBase
    (a : ℂ) (u : Nat.Primes →₀ ℂ) :
    analyticFinitePrimeShiftCarrier a u ∈ analyticEulerExponentialBase a := by
  rw [analyticFinitePrimeShiftCarrier_eq_sum]
  unfold Finsupp.sum
  apply IntermediateField.sum_mem
  intro q hq
  apply IntermediateField.mul_mem
  · rw [IsScalarTower.algebraMap_apply ℂ upperEndRationalCoordinateField upperEndMeroField]
    exact IntermediateField.algebraMap_mem _
      (algebraMap ℂ upperEndRationalCoordinateField (u q))
  · exact GaloisForLFunctions.subset_differentialAdjoin
      upperEndRationalCoordinateField _ (Set.mem_range_self q)

/-- Every derivative of a finite-prime carrier remains in the Euler-exponential base. -/
theorem differentialJet_analyticFinitePrimeShiftCarrier_mem_eulerBase
    (a : ℂ) (u : Nat.Primes →₀ ℂ) (n : ℕ) :
    GaloisForLFunctions.differentialJet n (analyticFinitePrimeShiftCarrier a u) ∈
      analyticEulerExponentialBase a := by
  have hjets :=
    differentialJet_analyticPrimeObservableShiftCarrier_finsuppLinearCombination
      (primeKroneckerCoefficient) (fun _ ↦ 1)
      primeKroneckerCoefficient_norm_le_one u (fun p ↦ u p)
      (finitePrimeSourceBound u) (finitePrimeSource_norm_le_bound u)
      (fun p ↦ (finsupp_sum_primeKroneckerCoefficient u p).symm) a n
  change GaloisForLFunctions.differentialJet n
      (analyticPrimeObservableShiftCarrier (fun p ↦ u p)
        (finitePrimeSourceBound u) (finitePrimeSource_norm_le_bound u) a) ∈ _
  rw [hjets]
  unfold Finsupp.sum
  apply IntermediateField.sum_mem
  intro q hq
  apply IntermediateField.mul_mem
  · rw [IsScalarTower.algebraMap_apply ℂ upperEndRationalCoordinateField upperEndMeroField]
    exact IntermediateField.algebraMap_mem _
      (algebraMap ℂ upperEndRationalCoordinateField (u q))
  · exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
      upperEndRationalCoordinateField (Set.mem_range_self q) n

/-- The analytic jet represented by a bounded source is independent of the numerical bound used
to certify convergence. -/
theorem differentialJet_analyticPrimeObservableShiftCarrier_congr_bound
    (c : Nat.Primes → ℂ) (M N : ℝ)
    (hc : ∀ p, ‖c p‖ ≤ M) (hd : ∀ p, ‖c p‖ ≤ N)
    (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (analyticPrimeObservableShiftCarrier c M hc a) =
      GaloisForLFunctions.differentialJet k
        (analyticPrimeObservableShiftCarrier c N hd a) := by
  have hlin := differentialJet_analyticPrimeObservableShiftCarrier_linearCombination
    (J := Fin 1) (fun _ ↦ c) (fun _ ↦ M) (fun _ ↦ hc)
    (fun _ ↦ (1 : ℂ)) c N hd (by intro p; simp) a k
  simpa using hlin.symm

/-- Two bounded prime sources that differ at only finitely many primes have the same analytic
tail at every differential order: their jet difference lies in the Euler-exponential base. -/
theorem differentialJet_analyticPrimeObservableShiftCarrier_sub_mem_eulerBase_of_finiteSupport
    (c d : Nat.Primes → ℂ) (M N : ℝ)
    (hc : ∀ p, ‖c p‖ ≤ M) (hd : ∀ p, ‖d p‖ ≤ N)
    (hsupport : {p | c p - d p ≠ 0}.Finite) (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
          (analyticPrimeObservableShiftCarrier c M hc a) -
        GaloisForLFunctions.differentialJet k
          (analyticPrimeObservableShiftCarrier d N hd a) ∈
      analyticEulerExponentialBase a := by
  classical
  let u : Nat.Primes →₀ ℂ :=
    Finsupp.onFinset hsupport.toFinset (fun p ↦ c p - d p) (by
      intro p hp
      exact hsupport.mem_toFinset.mpr hp)
  have hu (p : Nat.Primes) : u p = c p - d p := by
    exact Finsupp.onFinset_apply
  have hcarrier :
      analyticFinitePrimeShiftCarrier a u =
        analyticPrimeObservableShiftCarrier c M hc a -
          analyticPrimeObservableShiftCarrier d N hd a := by
    have hlin := analyticPrimeObservableShiftCarrier_linearCombination
      (J := Fin 2)
      (fun i ↦ if i = 0 then c else d)
      (fun i ↦ if i = 0 then M else N)
      (by
        intro i p
        fin_cases i
        · simpa using hc p
        · simpa using hd p)
      (fun i ↦ if i = 0 then (1 : ℂ) else -1)
      (fun p ↦ u p) (finitePrimeSourceBound u)
      (finitePrimeSource_norm_le_bound u)
      (by
        intro p
        change u p = _
        rw [hu]
        simp [Fin.sum_univ_two, sub_eq_add_neg]) a
    simpa [analyticFinitePrimeShiftCarrier, Fin.sum_univ_two, sub_eq_add_neg] using hlin
  rw [← GaloisForLFunctions.differentialJet_sub, ← hcarrier]
  exact differentialJet_analyticFinitePrimeShiftCarrier_mem_eulerBase a u k

end

end GaloisForLFunctions.HTGeometry
