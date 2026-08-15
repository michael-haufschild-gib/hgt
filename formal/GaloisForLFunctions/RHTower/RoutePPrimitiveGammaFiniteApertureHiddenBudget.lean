import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaAntidiagonalTraceBlindness

/-!
# Route P finite-aperture hidden colligation budget

P-G192 proves that the antidiagonal Wold channel must be retained as energy,
not annihilated by codiagonal observation.  The infinitesimal flux is not the
appropriate finite budget: P-G188 already supplies a finite-aperture defect
mass whose total tends to zero at the wall and whose normalized derivative is
the P-G190 flux.

This module builds the corresponding resolved antidiagonal defect current,
computes its complete ordered-pair energy, and proves that for every
sufficiently small positive aperture its entire hidden trace lies strictly
inside the fixed P-G184 source budget.

No Xi divisor, zero-location statement, target positivity assumption, or
Riemann-hypothesis premise occurs.
-/

open Complex Matrix Set Filter Topology
open scoped BigOperators ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem routePPrimitiveBaseCauchyCubicWeight_pos
    (pe : Nat.Primes × ℕ) :
    0 < routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveBaseCauchyCubicWeight,
    xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by
    exact_mod_cast pe.1.property.pos
  have hlog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  positivity

theorem routePPrimitiveBaseCauchyCubicTraceBudget_pos :
    0 < routePPrimitiveBaseCauchyCubicTraceBudget := by
  exact summable_routePPrimitiveBaseCauchyCubicWeight.tsum_pos
    routePPrimitiveBaseCauchyCubicWeight_nonneg
    (⟨2, Nat.prime_two⟩, 0)
    (routePPrimitiveBaseCauchyCubicWeight_pos _)

theorem routePPrimitiveBurnolApertureDefectMass_pos
    {c : ℝ} (hc : 0 < c) (pe : Nat.Primes × ℕ) :
    0 < routePPrimitiveBurnolApertureDefectMass c pe := by
  rw [routePPrimitiveBurnolApertureDefectMass]
  apply mul_pos
  · rw [sub_pos, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hc)
      (xiGammaEulerPrimitiveLogFrequency_pos pe)
  · exact routePPrimitiveBaseCauchyCubicWeight_pos pe

theorem routePPrimitiveBurnolApertureTotalDefectMass_pos
    {c : ℝ} (hc : 0 < c) :
    0 < routePPrimitiveBurnolApertureTotalDefectMass c := by
  rw [routePPrimitiveBurnolApertureTotalDefectMass]
  exact (summable_routePPrimitiveBurnolApertureDefectMass hc.le).tsum_pos
    (routePPrimitiveBurnolApertureDefectMass_nonneg hc.le)
    (⟨2, Nat.prime_two⟩, 0)
    (routePPrimitiveBurnolApertureDefectMass_pos hc _)

/-- Finite aperture defect mass vanishes at the balanced wall.  Its first
right derivative remains the nonzero P-G190 flux, but its unscaled energy is
small. -/
theorem tendsto_routePPrimitiveBurnolApertureTotalDefectMass_zero :
    Tendsto routePPrimitiveBurnolApertureTotalDefectMass
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hc : Tendsto (fun c : ℝ => c)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hprod := hc.mul
    tendsto_routePPrimitiveBurnolApertureTotalDefectMass_div_zero
  have hzero : Tendsto
      (fun c : ℝ => c * (routePPrimitiveBurnolApertureTotalDefectMass c / c))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hprod
  refine hzero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hcpos
  change 0 < c at hcpos
  field_simp [hcpos.ne']

/-- Canonical finite-aperture square-root amplitude on an ordered primitive
cell pair. -/
def routePPrimitiveGammaFiniteApertureHiddenAmplitude
    (c : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  Real.sqrt
    (routePPrimitiveBurnolApertureDefectMass c i *
      routePPrimitiveBurnolApertureDefectMass c j)

theorem routePPrimitiveGammaFiniteApertureHiddenAmplitude_pos
    {c : ℝ} (hc : 0 < c) (i j : Nat.Primes × ℕ) :
    0 < routePPrimitiveGammaFiniteApertureHiddenAmplitude c i j := by
  rw [routePPrimitiveGammaFiniteApertureHiddenAmplitude, Real.sqrt_pos]
  exact mul_pos
    (routePPrimitiveBurnolApertureDefectMass_pos hc i)
    (routePPrimitiveBurnolApertureDefectMass_pos hc j)

/-- Resolved finite-aperture defect current in the forced P-G191 hidden
channel. -/
def routePPrimitiveGammaFiniteApertureHiddenCurrent
    (c : ℝ) (i j : Nat.Primes × ℕ) : ℝ × ℝ :=
  resolvedDefectAntidiagonal (R := ℝ)
    (routePPrimitiveGammaFiniteApertureHiddenAmplitude c i j)

@[simp] theorem routePPrimitiveGammaCoorientedResolvedReporter_finiteApertureHiddenCurrent
    (a c : ℝ) (i j : Nat.Primes × ℕ) :
    routePPrimitiveGammaCoorientedResolvedReporter a i j
      (routePPrimitiveGammaFiniteApertureHiddenCurrent c i j) = 0 := by
  rw [routePPrimitiveGammaCoorientedResolvedReporter_eq_codiagonal]
  simp [routePPrimitiveGammaFiniteApertureHiddenCurrent]

/-- Complete energy of one finite-aperture hidden pair. -/
def routePPrimitiveGammaFiniteApertureHiddenPairEnergy
    (c : ℝ) (ij : (Nat.Primes × ℕ) × (Nat.Primes × ℕ)) : ℝ :=
  routePPrimitiveGammaResolvedEnergy
    (routePPrimitiveGammaFiniteApertureHiddenCurrent c ij.1 ij.2)

theorem routePPrimitiveGammaFiniteApertureHiddenPairEnergy_eq
    {c : ℝ} (hc : 0 ≤ c)
    (ij : (Nat.Primes × ℕ) × (Nat.Primes × ℕ)) :
    routePPrimitiveGammaFiniteApertureHiddenPairEnergy c ij =
      2 * routePPrimitiveBurnolApertureDefectMass c ij.1 *
        routePPrimitiveBurnolApertureDefectMass c ij.2 := by
  rw [routePPrimitiveGammaFiniteApertureHiddenPairEnergy,
    routePPrimitiveGammaResolvedEnergy,
    routePPrimitiveGammaFiniteApertureHiddenCurrent,
    resolvedDefectAntidiagonal_apply]
  simp only [neg_sq]
  rw [routePPrimitiveGammaFiniteApertureHiddenAmplitude,
    Real.sq_sqrt]
  · ring
  · exact mul_nonneg
      (routePPrimitiveBurnolApertureDefectMass_nonneg hc ij.1)
      (routePPrimitiveBurnolApertureDefectMass_nonneg hc ij.2)

theorem summable_routePPrimitiveGammaFiniteApertureHiddenPairEnergy
    {c : ℝ} (hc : 0 ≤ c) :
    Summable (routePPrimitiveGammaFiniteApertureHiddenPairEnergy c) := by
  have hmass := summable_routePPrimitiveBurnolApertureDefectMass hc
  have hprod : Summable (fun ij :
      (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      2 * routePPrimitiveBurnolApertureDefectMass c ij.1 *
        routePPrimitiveBurnolApertureDefectMass c ij.2) := by
    rw [summable_prod_of_nonneg (fun ij =>
      mul_nonneg
        (mul_nonneg (by norm_num)
          (routePPrimitiveBurnolApertureDefectMass_nonneg hc ij.1))
        (routePPrimitiveBurnolApertureDefectMass_nonneg hc ij.2))]
    constructor
    · intro i
      exact hmass.mul_left
        (2 * routePPrimitiveBurnolApertureDefectMass c i)
    · apply
        (hmass.mul_left
          (2 * routePPrimitiveBurnolApertureTotalDefectMass c)).congr
      intro i
      rw [routePPrimitiveBurnolApertureTotalDefectMass]
      calc
        (2 * ∑' j, routePPrimitiveBurnolApertureDefectMass c j) *
              routePPrimitiveBurnolApertureDefectMass c i =
            (2 * routePPrimitiveBurnolApertureDefectMass c i) *
              ∑' j, routePPrimitiveBurnolApertureDefectMass c j := by ring
        _ = ∑' j, (2 * routePPrimitiveBurnolApertureDefectMass c i) *
              routePPrimitiveBurnolApertureDefectMass c j := by
            rw [tsum_mul_left]
        _ = ∑' j,
              2 * routePPrimitiveBurnolApertureDefectMass c (i, j).1 *
                routePPrimitiveBurnolApertureDefectMass c (i, j).2 := by
            apply tsum_congr
            intro j
            ring
  exact hprod.congr fun ij =>
    (routePPrimitiveGammaFiniteApertureHiddenPairEnergy_eq hc ij).symm

/-- The entire ordered-pair hidden energy is the square of total finite
aperture defect mass, with the forced rank-two factor. -/
theorem tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy
    {c : ℝ} (hc : 0 ≤ c) :
    ∑' ij, routePPrimitiveGammaFiniteApertureHiddenPairEnergy c ij =
      2 * routePPrimitiveBurnolApertureTotalDefectMass c ^ 2 := by
  have hmass := summable_routePPrimitiveBurnolApertureDefectMass hc
  have hnorm : Summable (fun pe =>
      ‖routePPrimitiveBurnolApertureDefectMass c pe‖) := by
    exact hmass.congr fun pe => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (routePPrimitiveBurnolApertureDefectMass_nonneg hc pe)]
  have hmul := tsum_mul_tsum_of_summable_norm hnorm hnorm
  rw [routePPrimitiveBurnolApertureTotalDefectMass]
  calc
    (∑' ij, routePPrimitiveGammaFiniteApertureHiddenPairEnergy c ij) =
        ∑' ij : (Nat.Primes × ℕ) × (Nat.Primes × ℕ),
          2 * routePPrimitiveBurnolApertureDefectMass c ij.1 *
          routePPrimitiveBurnolApertureDefectMass c ij.2 := by
      apply tsum_congr
      intro ij
      rw [routePPrimitiveGammaFiniteApertureHiddenPairEnergy_eq hc]
    _ = ∑' ij : (Nat.Primes × ℕ) × (Nat.Primes × ℕ),
          2 * (routePPrimitiveBurnolApertureDefectMass c ij.1 *
            routePPrimitiveBurnolApertureDefectMass c ij.2) := by
      apply tsum_congr
      intro ij
      ring
    _ = 2 * ∑' ij : (Nat.Primes × ℕ) × (Nat.Primes × ℕ),
          routePPrimitiveBurnolApertureDefectMass c ij.1 *
            routePPrimitiveBurnolApertureDefectMass c ij.2 := by
      rw [tsum_mul_left]
    _ = 2 * ((∑' i, routePPrimitiveBurnolApertureDefectMass c i) *
        ∑' j, routePPrimitiveBurnolApertureDefectMass c j) := by
      rw [hmul]
    _ = 2 * (∑' pe, routePPrimitiveBurnolApertureDefectMass c pe) ^ 2 := by ring

/-- Total retained hidden energy vanishes at the aperture wall. -/
theorem tendsto_tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy_zero :
    Tendsto
      (fun c : ℝ =>
        ∑' ij, routePPrimitiveGammaFiniteApertureHiddenPairEnergy c ij)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hmass := tendsto_routePPrimitiveBurnolApertureTotalDefectMass_zero
  have henergy : Tendsto
      (fun c : ℝ => 2 * routePPrimitiveBurnolApertureTotalDefectMass c ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (hmass.pow 2).const_mul 2
  refine henergy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  change 0 < c at hc
  rw [tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy hc.le]

/-- For every sufficiently small positive aperture, the complete retained
hidden trace lies strictly inside the fixed P-G184 source budget. -/
theorem eventually_tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy_lt_budget :
    ∀ᶠ c : ℝ in nhdsWithin 0 (Ioi 0),
      (∑' ij, routePPrimitiveGammaFiniteApertureHiddenPairEnergy c ij) <
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  exact tendsto_tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy_zero.eventually
    (Iio_mem_nhds routePPrimitiveBaseCauchyCubicTraceBudget_pos)

theorem exists_positive_tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy_lt_budget :
    ∃ c : ℝ, 0 < c ∧
      (∑' ij, routePPrimitiveGammaFiniteApertureHiddenPairEnergy c ij) <
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  obtain ⟨c, hlt, hc⟩ :=
    (eventually_tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy_lt_budget.and
      self_mem_nhdsWithin).exists
  exact ⟨c, hc, hlt⟩

end

end RHTower
