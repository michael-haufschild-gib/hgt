import GaloisForLFunctions.HTGeometry.PauliCommutatorReturnTubeLaw
import GaloisForLFunctions.HTGeometry.PauliContinuousLaboratoryReturnLaw

/-!
# Continuous circuit-family returns after low-incidence excision

For every finite unitary circuit family, remove exactly those endpoint targets
whose two-local observer incidence lies below the universal interpolation
threshold `2 / gaussianIntervalActivationMass`.  The probability that one
ordinary static Gaussian two-local Hamiltonian enters a narrow return tube
around any surviving target anywhere in a continuous `n^k` laboratory window
is bounded by the same-draw energy-cap tail plus a polynomial grid factor times
the target-image incidence partition function.

This identifies the remaining circuit-set problem without a word-count union:
only the incidence-weighted occupied target image survives.  Low-incidence
projective-return mass is excised before the circuit union.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Energy-normalized distance from the static orbit to an arbitrary unitary
circuit target. -/
def twoLocalCircuitScaledReturnDistance
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) (t : ℝ)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  2 * ‖realActivePauliHamiltonian x‖ *
    hsNorm (unitaryEvolution (realActivePauliHamiltonian x) t -
      (U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))

/-- Time variation of arbitrary-target scaled return distance. -/
theorem twoLocalCircuitScaledReturnDistance_time_le
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (t u : ℝ) :
    twoLocalCircuitScaledReturnDistance x u U ≤
      twoLocalCircuitScaledReturnDistance x t U +
        2 * Real.sqrt ((2 : ℝ) ^ n) *
          ‖realActivePauliHamiltonian x‖ ^ 2 * |t - u| := by
  have hself := isSelfAdjoint_realActivePauliHamiltonian x
  have hdim : (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) =
      (2 : ℝ) ^ n := by
    simp
  have htri := hsNorm_sub_le
    (unitaryEvolution (realActivePauliHamiltonian x) u)
    (unitaryEvolution (realActivePauliHamiltonian x) t)
    (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
  have hspeed := hsNorm_unitaryEvolution_time_sub_le hself u t
  rw [hdim] at hspeed
  unfold twoLocalCircuitScaledReturnDistance
  calc
    2 * ‖realActivePauliHamiltonian x‖ *
        hsNorm (unitaryEvolution (realActivePauliHamiltonian x) u -
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)) ≤
      2 * ‖realActivePauliHamiltonian x‖ *
        (hsNorm (unitaryEvolution (realActivePauliHamiltonian x) u -
            unitaryEvolution (realActivePauliHamiltonian x) t) +
          hsNorm (unitaryEvolution (realActivePauliHamiltonian x) t -
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ))) := by
      gcongr
    _ ≤ 2 * ‖realActivePauliHamiltonian x‖ *
        (Real.sqrt ((2 : ℝ) ^ n) * ‖realActivePauliHamiltonian x‖ * |u - t| +
          hsNorm (unitaryEvolution (realActivePauliHamiltonian x) t -
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ))) := by
      gcongr
    _ = 2 * ‖realActivePauliHamiltonian x‖ *
          hsNorm (unitaryEvolution (realActivePauliHamiltonian x) t -
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) +
        2 * Real.sqrt ((2 : ℝ) ^ n) *
          ‖realActivePauliHamiltonian x‖ ^ 2 * |t - u| := by
      rw [abs_sub_comm]
      ring

/-- On the quenched Gaussian energy box, one mesh step changes arbitrary
circuit-target distance by at most square-root Hilbert dimension. -/
theorem twoLocalCircuitScaledReturnDistance_increment_le_sqrtDimension
    {n : ℕ} (hn : 1 ≤ n) {x : TwoLocalPauliCoefficientSpace n}
    (hx : x ∈ twoLocalPauliCoefficientBox n) {t u : ℝ}
    (htu : |t - u| ≤ 1 / (648 * (n : ℝ) ^ 6))
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalCircuitScaledReturnDistance x u U ≤
      twoLocalCircuitScaledReturnDistance x t U +
        Real.sqrt ((2 : ℝ) ^ n) := by
  have hcap :=
    norm_realActivePauliHamiltonian_le_eighteen_mul_cube_of_mem_box hn hx
  have hbase := twoLocalCircuitScaledReturnDistance_time_le x U t u
  refine hbase.trans ?_
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnormsq : ‖realActivePauliHamiltonian x‖ ^ 2 ≤
      (18 * (n : ℝ) ^ 3) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcap 2
  have hdelta :
      2 * Real.sqrt ((2 : ℝ) ^ n) *
          ‖realActivePauliHamiltonian x‖ ^ 2 * |t - u| ≤
        Real.sqrt ((2 : ℝ) ^ n) := by
    calc
      2 * Real.sqrt ((2 : ℝ) ^ n) *
          ‖realActivePauliHamiltonian x‖ ^ 2 * |t - u| ≤
        2 * Real.sqrt ((2 : ℝ) ^ n) *
          (18 * (n : ℝ) ^ 3) ^ 2 *
            (1 / (648 * (n : ℝ) ^ 6)) := by
        gcongr
      _ = Real.sqrt ((2 : ℝ) ^ n) := by
        field_simp
        ring
  simpa [add_comm] using
    (add_le_add_left hdelta
      (twoLocalCircuitScaledReturnDistance x t U))

/-- High-incidence target labels after low-incidence/projective-return
excision.  The occupied-image quotient below removes duplicate endpoints. -/
noncomputable def twoLocalPauliHighIncidenceCircuitTargets
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) : Finset C := by
  classical
  exact Finset.univ.filter fun c =>
    2 / gaussianIntervalActivationMass ≤
      twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)

/-- Narrow return event for the incidence-excised occupied circuit image. -/
def twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    Set (TwoLocalPauliCoefficientSpace n) :=
  ⋃ c : ↥(twoLocalPauliHighIncidenceCircuitTargets U),
    {x | twoLocalCircuitScaledReturnDistance x t (U c.1) ^ 2 ≤
      (gaussianIntervalActivationMass / 8) *
        (4 * (2 : ℝ) ^ n *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1))}

/-- Narrow return to a surviving circuit target transfers to its wide
fixed-time incidence tube at the nearby grid point. -/
theorem twoLocalPauli_highIncidenceCircuit_uniformNarrowEvent_subset_wide
    {n : ℕ} (hn : 1 ≤ n) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ)
    {t u : ℝ} (htu : |t - u| ≤ 1 / (648 * (n : ℝ) ^ 6)) :
    twoLocalPauliCoefficientBox n ∩
        twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent U t ⊆
      ⋃ c : ↥(twoLocalPauliHighIncidenceCircuitTargets U),
        {x | twoLocalCircuitScaledReturnDistance x u (U c.1) ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            (4 * (2 : ℝ) ^ n *
              twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1))} := by
  classical
  rintro x ⟨hxbox, hx⟩
  rw [twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent,
    Set.mem_iUnion] at hx
  obtain ⟨c, hc⟩ := hx
  change twoLocalCircuitScaledReturnDistance x t (U c.1) ^ 2 ≤
    (gaussianIntervalActivationMass / 8) *
      (4 * (2 : ℝ) ^ n *
        twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1)) at hc
  rw [Set.mem_iUnion]
  refine ⟨c, ?_⟩
  change twoLocalCircuitScaledReturnDistance x u (U c.1) ^ 2 ≤
    (gaussianIntervalActivationMass / 2) *
      (4 * (2 : ℝ) ^ n *
        twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1))
  let I := twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1)
  let B := (gaussianIntervalActivationMass / 2) * (2 : ℝ) ^ n * I
  have hI : 2 / gaussianIntervalActivationMass ≤ I := by
    exact (Finset.mem_filter.mp c.2).2
  have hI0 : 0 ≤ I :=
    twoLocalPauliUnitaryAnticommutingIncidenceMass_nonneg (U c.1)
  have hB0 : 0 ≤ B := by
    unfold B
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg gaussianIntervalActivationMass_pos.le (by norm_num))
        (by positivity)) hI0
  have hsmallSq : twoLocalCircuitScaledReturnDistance x t (U c.1) ^ 2 ≤ B := by
    unfold B I
    convert hc using 1
    ring
  have hdist0 : 0 ≤ twoLocalCircuitScaledReturnDistance x t (U c.1) := by
    unfold twoLocalCircuitScaledReturnDistance
    exact mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _)) (hsNorm_nonneg _)
  have hsmall : twoLocalCircuitScaledReturnDistance x t (U c.1) ≤
      Real.sqrt B := by
    calc
      twoLocalCircuitScaledReturnDistance x t (U c.1) =
          Real.sqrt (twoLocalCircuitScaledReturnDistance x t (U c.1) ^ 2) :=
        (Real.sqrt_sq hdist0).symm
      _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hsmallSq
  have hdimB : (2 : ℝ) ^ n ≤ B := by
    unfold B I
    have hg := gaussianIntervalActivationMass_pos
    have hmul : 2 ≤ gaussianIntervalActivationMass *
        twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1) := by
      rw [div_le_iff₀ hg] at hI
      simpa [mul_comm] using hI
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
  have hsqrtDim : Real.sqrt ((2 : ℝ) ^ n) ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt hdimB
  have htime :=
    twoLocalCircuitScaledReturnDistance_increment_le_sqrtDimension
      hn hxbox htu (U c.1)
  have hwideDist : twoLocalCircuitScaledReturnDistance x u (U c.1) ≤
      2 * Real.sqrt B := by
    linarith
  have hwideSq : twoLocalCircuitScaledReturnDistance x u (U c.1) ^ 2 ≤
      4 * B := by
    have hnonneg : 0 ≤ twoLocalCircuitScaledReturnDistance x u (U c.1) := by
      unfold twoLocalCircuitScaledReturnDistance
      exact mul_nonneg
        (mul_nonneg (by norm_num) (norm_nonneg _)) (hsNorm_nonneg _)
    have hsqrtNonneg := Real.sqrt_nonneg B
    have hsqrtSq := Real.sq_sqrt hB0
    nlinarith
  unfold B I at hwideSq
  convert hwideSq using 1
  ring

/-- Complete continuous polynomial-window return event for the incidence-
excised circuit image. -/
def twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent
    (k n : ℕ) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (A : ℝ) :
    Set (TwoLocalPauliCoefficientSpace n) :=
  {x | ∃ t ∈ Set.Icc A (A + (n : ℝ) ^ k),
    x ∈ twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent U t}

/-- Every continuous-window high-incidence circuit return is either an energy
cap failure or one fixed-time grid return. -/
theorem twoLocalPauli_highIncidenceCircuitPolynomialWindowReturnEvent_subset
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (A : ℝ) :
    twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent k n U A ⊆
      (twoLocalPauliCoefficientBox n)ᶜ ∪
        ⋃ j : Fin (649 * n ^ (k + 7)),
          ⋃ c : ↥(twoLocalPauliHighIncidenceCircuitTargets U),
            {x | twoLocalCircuitScaledReturnDistance x
                (twoLocalPauliContinuumGridTime k n A j) (U c.1) ^ 2 ≤
              (gaussianIntervalActivationMass / 2) *
                (4 * (2 : ℝ) ^ n *
                  twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1))} := by
  intro x hx
  rcases hx with ⟨t, ht, hreturn⟩
  by_cases hxbox : x ∈ twoLocalPauliCoefficientBox n
  · right
    obtain ⟨j, hj⟩ :=
      exists_twoLocalPauliContinuumGridTime_near k hn A ht
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    exact twoLocalPauli_highIncidenceCircuit_uniformNarrowEvent_subset_wide
      hn U hj ⟨hxbox, hreturn⟩
  · exact Or.inl hxbox

/-- **Incidence-normalized continuous coarea bound.**  Complete continuous
polynomial-window circuit-return mass is controlled by one Gaussian energy
tail plus the occupied high-incidence endpoint image partition function. -/
theorem stdGaussian_twoLocalPauli_measure_highIncidenceCircuitPolynomialWindowReturnEvent_le
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (A : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent
          k n U A) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          ∑ c : ↥(twoLocalPauliHighIncidenceCircuitTargets U),
            Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
              twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1)) := by
  have hsub :=
    twoLocalPauli_highIncidenceCircuitPolynomialWindowReturnEvent_subset
      k hn U A
  let Uhi : ↥(twoLocalPauliHighIncidenceCircuitTargets U) →
      Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ :=
    fun c => U c.1
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent
          k n U A) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        ((twoLocalPauliCoefficientBox n)ᶜ ∪
          ⋃ j : Fin (649 * n ^ (k + 7)),
            ⋃ c : ↥(twoLocalPauliHighIncidenceCircuitTargets U),
              {x | twoLocalCircuitScaledReturnDistance x
                  (twoLocalPauliContinuumGridTime k n A j) (U c.1) ^ 2 ≤
                (gaussianIntervalActivationMass / 2) *
                  (4 * (2 : ℝ) ^ n *
                    twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1))}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (⋃ j : Fin (649 * n ^ (k + 7)),
            ⋃ c : ↥(twoLocalPauliHighIncidenceCircuitTargets U),
              {x | twoLocalCircuitScaledReturnDistance x
                  (twoLocalPauliContinuumGridTime k n A j) (U c.1) ^ 2 ≤
                (gaussianIntervalActivationMass / 2) *
                  (4 * (2 : ℝ) ^ n *
                    twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1))}) :=
      measureReal_union_le _ _
    _ ≤ (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (Fintype.card (Fin (649 * n ^ (k + 7))) : ℝ) *
          (∑ c : ↥(twoLocalPauliHighIncidenceCircuitTargets U),
            Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
              twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1))) := by
      gcongr
      apply measureReal_iUnion_le_card_mul
      intro j
      simpa [Uhi, twoLocalCircuitScaledReturnDistance] using
        stdGaussian_twoLocalPauli_measure_iUnion_incidenceReturnTube_le
          Uhi (twoLocalPauliContinuumGridTime k n A j)
    _ = (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          ∑ c : ↥(twoLocalPauliHighIncidenceCircuitTargets U),
            Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
              twoLocalPauliUnitaryAnticommutingIncidenceMass (U c.1)) := by
      simp [Nat.cast_mul, Nat.cast_pow]

/-- Actual occupied circuit endpoint image.  Arbitrarily many circuit words
with the same unitary endpoint occur only once. -/
noncomputable def twoLocalPauliOccupiedCircuitImage
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    Finset (Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) := by
  classical
  exact Finset.univ.image U

/-- Inclusion of the occupied endpoint image into the unitary group. -/
def twoLocalPauliOccupiedCircuitTarget
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    ↥(twoLocalPauliOccupiedCircuitImage U) →
      Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ :=
  fun V => V.1

/-- **Endpoint multiplicity cancellation.**  Return to the high-incidence
circuit family depends only on its occupied unitary image, not on circuit-word
multiplicity. -/
theorem twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent_eq_occupiedImage
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (t : ℝ) :
    twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent U t =
      twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent
        (twoLocalPauliOccupiedCircuitTarget U) t := by
  classical
  ext x
  simp only [twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent,
    Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc⟩
    let V : ↥(twoLocalPauliOccupiedCircuitImage U) :=
      ⟨U c.1, Finset.mem_image.mpr ⟨c.1, Finset.mem_univ _, rfl⟩⟩
    have hVhi : V ∈ twoLocalPauliHighIncidenceCircuitTargets
        (twoLocalPauliOccupiedCircuitTarget U) := by
      rw [twoLocalPauliHighIncidenceCircuitTargets, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (Finset.mem_filter.mp c.2).2
    let d : ↥(twoLocalPauliHighIncidenceCircuitTargets
        (twoLocalPauliOccupiedCircuitTarget U)) := ⟨V, hVhi⟩
    refine ⟨d, ?_⟩
    simpa [d, V, twoLocalPauliOccupiedCircuitTarget] using hc
  · rintro ⟨d, hd⟩
    obtain ⟨c, -, hcU⟩ := Finset.mem_image.mp d.1.2
    have hchi : c ∈ twoLocalPauliHighIncidenceCircuitTargets U := by
      rw [twoLocalPauliHighIncidenceCircuitTargets, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hdhi := (Finset.mem_filter.mp d.2).2
      simpa [twoLocalPauliOccupiedCircuitTarget, hcU] using hdhi
    let e : ↥(twoLocalPauliHighIncidenceCircuitTargets U) := ⟨c, hchi⟩
    refine ⟨e, ?_⟩
    simpa [e, twoLocalPauliOccupiedCircuitTarget, hcU] using hd

/-- Polynomial-window returns are invariant under exact endpoint-image
compression. -/
theorem twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent_eq_occupiedImage
    (k n : ℕ) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (A : ℝ) :
    twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent k n U A =
      twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent k n
        (twoLocalPauliOccupiedCircuitTarget U) A := by
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    rw [twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent_eq_occupiedImage
      U t] at hx
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    rw [← twoLocalPauliHighIncidenceCircuitUniformNarrowReturnEvent_eq_occupiedImage
      U t] at hx
    exact ⟨t, ht, hx⟩

/-- **Occupied-image incidence-normalized continuous coarea bound.**  The
circuit union pays only once for every distinct high-incidence unitary
endpoint, irrespective of circuit-description multiplicity. -/
theorem stdGaussian_twoLocalPauli_measure_highIncidenceCircuitPolynomialWindowReturnEvent_le_occupiedImage
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (A : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent
          k n U A) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          ∑ V : ↥(twoLocalPauliHighIncidenceCircuitTargets
              (twoLocalPauliOccupiedCircuitTarget U)),
            Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
              twoLocalPauliUnitaryAnticommutingIncidenceMass
                (twoLocalPauliOccupiedCircuitTarget U V.1)) := by
  rw [twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent_eq_occupiedImage
    k n U A]
  exact
    stdGaussian_twoLocalPauli_measure_highIncidenceCircuitPolynomialWindowReturnEvent_le
      k hn (twoLocalPauliOccupiedCircuitTarget U) A

end

end GaloisForLFunctions.HTGeometry
