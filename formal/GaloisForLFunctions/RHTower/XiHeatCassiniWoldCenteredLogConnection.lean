import GaloisForLFunctions.RHTower.XiHeatCassiniWoldLogDiscrepancy

/-!
# Centered logarithmic connection of the pure Wold Route-T producer

The pure Wold half-density current admits an exact ordered Abel decomposition.  Its cumulative
coefficient splits into logarithmic Lebesgue mass and a uniformly bounded Wold discrepancy.  Thus
the remaining Route-T obstruction is an ordered phase-gradient connection with bounded arithmetic
primitive, plus an explicit logarithmic-mesh main current.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- First `N+1` primes are exactly all primes up to the `N`th prime. -/
theorem image_range_succ_nthPrimeSubtype_eq_primes_Icc (N : ℕ) :
    (Finset.range (N + 1)).image (fun n => (nthPrimeSubtype n : ℕ)) =
      (Finset.Icc 0 (nthPrimeSubtype N : ℕ)).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨Nat.zero_le _, nthPrimeSubtype_strictMono.monotone (by omega)⟩,
      (nthPrimeSubtype n).2⟩
  · rintro ⟨⟨hp0, hpN⟩, hp⟩
    let q : Nat.Primes := ⟨p, hp⟩
    let n : ℕ := nthPrimeEquiv.symm q
    have hnval : (nthPrimeSubtype n : ℕ) = p := by
      change ((nthPrimeEquiv n : Nat.Primes) : ℕ) = p
      rw [show nthPrimeEquiv n = q by simp [n]]
    have hnN : n ≤ N := by
      by_contra hnot
      have hNn : N < n := Nat.lt_of_not_ge hnot
      have hprimeLt := nthPrimeSubtype_strictMono hNn
      change (nthPrimeSubtype N : ℕ) < (nthPrimeSubtype n : ℕ) at hprimeLt
      rw [hnval] at hprimeLt
      exact (not_lt_of_ge hpN) hprimeLt
    exact ⟨n, by omega, hnval⟩

/-- Ordered Wold cumulative mass through the `N`th prime. -/
def xiHeatCassiniOrderedWoldPartialMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), woldCoeff 1 (nthPrimeSubtype n)

/-- Ordered Wold mass agrees with the natural-cutoff Wold mass. -/
theorem xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum (N : ℕ) :
    xiHeatCassiniOrderedWoldPartialMass N =
      xiHeatCassiniWoldNatWeightSum (nthPrimeSubtype N : ℕ) := by
  classical
  have hinj : Function.Injective (fun n : ℕ => (nthPrimeSubtype n : ℕ)) :=
    nthPrimeSubtype_strictMono.injective
  rw [xiHeatCassiniOrderedWoldPartialMass,
    xiHeatCassiniWoldNatWeightSum]
  calc
    (∑ n ∈ Finset.range (N + 1), woldCoeff 1 (nthPrimeSubtype n)) =
        ∑ p ∈ (Finset.range (N + 1)).image
            (fun n => (nthPrimeSubtype n : ℕ)),
          xiHeatCassiniWoldNatWeight p := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        simp [xiHeatCassiniWoldNatWeight, (nthPrimeSubtype n).2]
      · exact hinj.injOn
    _ = ∑ p ∈ (Finset.Icc 0 (nthPrimeSubtype N : ℕ)).filter Nat.Prime,
          xiHeatCassiniWoldNatWeight p := by
      rw [image_range_succ_nthPrimeSubtype_eq_primes_Icc]
    _ = ∑ p ∈ Finset.Icc 0 (nthPrimeSubtype N : ℕ),
          xiHeatCassiniWoldNatWeight p := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hpIcc hpNotPrimeFilter
      have hnp : ¬ p.Prime := by
        intro hpPrime
        exact hpNotPrimeFilter (Finset.mem_filter.mpr ⟨hpIcc, hpPrime⟩)
      simp [xiHeatCassiniWoldNatWeight, hnp]

/-- Centered cumulative Wold discrepancy at the `N`th ordered prime. -/
def xiHeatCassiniOrderedWoldLogDiscrepancy (N : ℕ) : ℝ :=
  xiHeatCassiniOrderedWoldPartialMass N - xiMassNthPrimeLogHeight N

/-- Ordered Wold discrepancy is uniformly bounded. -/
theorem abs_xiHeatCassiniOrderedWoldLogDiscrepancy_le (N : ℕ) :
    |xiHeatCassiniOrderedWoldLogDiscrepancy N| ≤
      mertensPrimeWindowBound + xiHeatCassiniWoldNatTraceCorrectionMass := by
  rw [xiHeatCassiniOrderedWoldLogDiscrepancy,
    xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum,
    xiMassNthPrimeLogHeight]
  exact abs_xiHeatCassiniWoldNatWeightSum_nthPrime_sub_log_le N

/-- Restored mass half-density profile on the ordered prime mesh. -/
def xiHeatCassiniOrderedPrimeHalfDensityProfile
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  ((Real.sqrt (nthPrimeSubtype N : ℝ) : ℝ) : ℂ) *
    xiHeatCassiniPrimeMassFourierProfile a τ (nthPrimeSubtype N)

/-- Pure Wold atom equals coefficient times ordered restored profile. -/
theorem xiHeatCassiniPureWoldHalfDensityAtom_nthPrime_eq
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniPureWoldHalfDensityAtom a τ (nthPrimeSubtype N) =
      (woldCoeff 1 (nthPrimeSubtype N) : ℂ) *
        xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N := by
  unfold xiHeatCassiniPureWoldHalfDensityAtom
    xiHeatCassiniOrderedPrimeHalfDensityProfile
  push_cast
  ring

/-- Wold cumulative terminal flux. -/
def xiHeatCassiniOrderedWoldTerminalFlux
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N *
    xiHeatCassiniOrderedWoldPartialMass N

/-- Wold cumulative edge-gradient atom. -/
def xiHeatCassiniOrderedWoldConnectionAtom
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldPartialMass N : ℂ) *
    (xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N -
      xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1))

/-- Exact Abel decomposition of every finite pure Wold source prefix. -/
theorem sum_range_pureWoldHalfDensityAtom_eq_terminal_add_connection
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        xiHeatCassiniPureWoldHalfDensityAtom a τ (nthPrimeSubtype n) =
      xiHeatCassiniOrderedWoldTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedWoldConnectionAtom a τ n := by
  have hAbel := complex_sum_range_by_parts_flux
    (xiHeatCassiniOrderedPrimeHalfDensityProfile a τ)
    (fun n => (woldCoeff 1 (nthPrimeSubtype n) : ℂ)) (N + 1)
  rw [show N + 1 - 1 = N by omega] at hAbel
  calc
    (∑ n ∈ Finset.range (N + 1),
        xiHeatCassiniPureWoldHalfDensityAtom a τ (nthPrimeSubtype n)) =
      ∑ n ∈ Finset.range (N + 1),
        (woldCoeff 1 (nthPrimeSubtype n) : ℂ) *
          xiHeatCassiniOrderedPrimeHalfDensityProfile a τ n := by
            apply Finset.sum_congr rfl
            intro n hn
            exact xiHeatCassiniPureWoldHalfDensityAtom_nthPrime_eq a τ n
    _ = _ := by
      simpa [xiHeatCassiniOrderedWoldTerminalFlux,
        xiHeatCassiniOrderedWoldConnectionAtom,
        xiHeatCassiniOrderedWoldPartialMass,
        Complex.ofReal_sum] using hAbel

/-- Logarithmic-mesh terminal flux. -/
def xiHeatCassiniOrderedLogMeshTerminalFlux
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N *
    xiMassNthPrimeLogHeight N

/-- Logarithmic-mesh connection atom. -/
def xiHeatCassiniOrderedLogMeshConnectionAtom
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  (xiMassNthPrimeLogHeight N : ℂ) *
    (xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N -
      xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1))

/-- Bounded-discrepancy terminal flux. -/
def xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N *
    xiHeatCassiniOrderedWoldLogDiscrepancy N

/-- Bounded-discrepancy connection atom. -/
def xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldLogDiscrepancy N : ℂ) *
    (xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N -
      xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1))

/-- Wold terminal flux splits into logarithmic main and bounded discrepancy. -/
theorem xiHeatCassiniOrderedWoldTerminalFlux_eq_logMesh_add_discrepancy
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniOrderedWoldTerminalFlux a τ N =
      xiHeatCassiniOrderedLogMeshTerminalFlux a τ N +
        xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux a τ N := by
  unfold xiHeatCassiniOrderedWoldTerminalFlux
    xiHeatCassiniOrderedLogMeshTerminalFlux
    xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux
    xiHeatCassiniOrderedWoldLogDiscrepancy
  push_cast
  ring

/-- Every Wold connection atom splits into logarithmic main and bounded discrepancy. -/
theorem xiHeatCassiniOrderedWoldConnectionAtom_eq_logMesh_add_discrepancy
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniOrderedWoldConnectionAtom a τ N =
      xiHeatCassiniOrderedLogMeshConnectionAtom a τ N +
        xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom a τ N := by
  unfold xiHeatCassiniOrderedWoldConnectionAtom
    xiHeatCassiniOrderedLogMeshConnectionAtom
    xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom
    xiHeatCassiniOrderedWoldLogDiscrepancy
  push_cast
  ring

/-- **Centered logarithmic connection law.**  Each pure Wold prefix is exactly logarithmic-mesh
main current plus a connection whose arithmetic primitive is uniformly bounded. -/
theorem sum_range_pureWoldHalfDensityAtom_eq_logMesh_add_boundedDiscrepancy
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        xiHeatCassiniPureWoldHalfDensityAtom a τ (nthPrimeSubtype n) =
      (xiHeatCassiniOrderedLogMeshTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedLogMeshConnectionAtom a τ n) +
      (xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom a τ n) := by
  rw [sum_range_pureWoldHalfDensityAtom_eq_terminal_add_connection,
    xiHeatCassiniOrderedWoldTerminalFlux_eq_logMesh_add_discrepancy]
  conv_lhs =>
    enter [2, 2, n]
    rw [xiHeatCassiniOrderedWoldConnectionAtom_eq_logMesh_add_discrepancy]
  rw [Finset.sum_add_distrib]
  ring

end

end RHTower
