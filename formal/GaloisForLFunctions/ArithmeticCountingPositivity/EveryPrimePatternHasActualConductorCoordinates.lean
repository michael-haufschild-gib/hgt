import GaloisForLFunctions.ArithmeticCountingPositivity.InfinitePrimeCountsHaveAZeroOrUnitConductorMass
import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheConductorCoordinates

/-!
# Every prime pattern has actual conductor coordinates

The full prime sign equals its finite prime cutoff on each integer
horizon, giving the actual normalized constraint vector and exact mixed
inner products. The arbitrary-pattern harmonic means identify their
limits. Sign-independent quasimode errors and simple energy windows then
transfer every counted coefficient to an actual prime-matrix eigenline.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.BezoutValuationIncidence

open private finiteFlipHorizonVector_norm finiteFlipWindowCoordinateSq_eq from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheConductorCoordinates

/-- The actual normalized harmonic sign vector on an integer horizon. -/
def primeSetHorizonVector (P : Set ℕ) (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  finiteFlipHorizonVector (primeSetCutoff P N) N

/-- Every positive horizon vector retains exactly unit norm. -/
theorem primeSetHorizonVector_norm_sq (P : Set ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ‖primeSetHorizonVector P N‖ ^ 2 = 1 :=
  finiteFlipHorizonVector_norm_sq (primeSetCutoff P N) hN

/-- The mixed arithmetic count is the literal inner product with the
normalized conductor mode on the actual integer horizon. -/
theorem primeSetHorizonVector_inner (P : Set ℕ) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ⟪primeSetHorizonVector P N, harmonicRamanujanHorizonVector m N⟫ =
      primeSetRamanujanSum P m N / gaugeHarmonicSum (fun _ => 1) N /
        Real.sqrt (m.totient : ℝ) := by
  have he : finiteFlipRamanujanSum (primeSetCutoff P N) m N = primeSetRamanujanSum P m N := by
    apply sum_congr rfl
    intro n hn
    rw [← primeSetFlip_eq_finiteFlip_of_le P (mem_Icc.mp hn).2]
  rw [primeSetHorizonVector, finiteFlipHorizonVector_inner hm, he]

/-- Every fixed conductor inner product tends to its counted coefficient,
without any finite-support or positive-density hypothesis. -/
theorem tendsto_primeSetHorizonVector_inner (P : Set ℕ) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ⟪primeSetHorizonVector P N, harmonicRamanujanHorizonVector m N⟫)
      atTop (𝓝 (primeSetConductorCoefficient P m)) := by
  simpa only [primeSetHorizonVector_inner P hm, primeSetConductorCoefficient] using
    (primeSetRamanujanSum_tendsto P m).div_const (Real.sqrt (m.totient : ℝ))

private theorem tendsto_primeSet_inner_projection (P : Set ℕ) {m : ℕ} (hm : 0 < m)
    {δ L : ℝ} (hδ : 0 < δ)
    (hinner : Tendsto (fun N : ℕ =>
      ⟪primeSetHorizonVector P N, harmonicRamanujanHorizonVector m N⟫) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ =>
      ⟪primeSetHorizonVector P N, harmonicRamanujanWindowProjection m N δ⟫)
      atTop (𝓝 L) := by
  have hnorm : Tendsto (fun N : ℕ =>
      ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
      (tendsto_harmonicRamanujanWindowProjection_error_sq hm hδ).sqrt
  have herr : Tendsto (fun N : ℕ =>
      ⟪primeSetHorizonVector P N,
        harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ⟫)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hnorm
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖primeSetHorizonVector P N‖ *
          ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖ :=
        abs_real_inner_le_norm _ _
      _ = _ := by
        rw [primeSetHorizonVector, finiteFlipHorizonVector_norm (primeSetCutoff P N) hN, one_mul]
  have he (N : ℕ) :
      ⟪primeSetHorizonVector P N, harmonicRamanujanWindowProjection m N δ⟫ =
      ⟪primeSetHorizonVector P N, harmonicRamanujanHorizonVector m N⟫ -
        ⟪primeSetHorizonVector P N,
          harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ⟫ := by
    rw [inner_sub_right]
    ring
  simpa only [he, sub_zero] using hinner.sub herr

/-- Squared constraint coordinate in the projected conductor direction. -/
def primeSetWindowCoordinateSq (P : Set ℕ) (m N : ℕ) (δ : ℝ) : ℝ :=
  finiteFlipWindowCoordinateSq (primeSetCutoff P N) m N δ

/-- Actual energy-window projection preserves the counted squared
coefficient for every prime pattern. -/
theorem tendsto_primeSetWindowCoordinateSq (P : Set ℕ) {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => primeSetWindowCoordinateSq P m N δ) atTop
      (𝓝 (primeSetConductorCoefficient P m ^ 2)) := by
  have h := tendsto_primeSet_inner_projection P hm hδ (tendsto_primeSetHorizonVector_inner P hm)
  simpa only [primeSetWindowCoordinateSq, finiteFlipWindowCoordinateSq, primeSetHorizonVector,
    div_one, Pi.div_def] using
    (h.pow 2).div (tendsto_harmonicRamanujanWindowProjection_norm_sq hm hδ)
      (by norm_num : (1 : ℝ) ≠ 0)

private theorem primeSetWindowCoordinateSq_eq (P : Set ℕ) {m N : ℕ} {δ : ℝ}
    (i : PrimeHorizonIndex N)
    (hwindow : fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ = {i})
    (hpos : 0 < ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2) :
    primeSetWindowCoordinateSq P m N δ =
      ⟪primeSetHorizonVector P N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 :=
  finiteFlipWindowCoordinateSq_eq (F := primeSetCutoff P N) i hwindow hpos

/-- Every isolated actual conductor eigenline has the counted squared
constraint coordinate, including zero-density prime patterns. -/
theorem exists_primeSet_eigenline_coordinates (P : Set ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ N : ℕ in atTop,
        (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ).card = 1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
          |fullPrimeEnergyEigenvalue N i - ramanujanAdjunctionEnergy m| < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
          |⟪primeSetHorizonVector P N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 -
            primeSetConductorCoefficient P m ^ 2| < ε) := by
  obtain ⟨δ, hδ, hcard, hnear, _⟩ := exists_simple_fullPrime_eigenline hm
  refine ⟨δ, hδ, hcard, hnear, ?_⟩
  intro ε hε
  have hlim := tendsto_primeSetWindowCoordinateSq P hm hδ
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N₀, hN₀⟩ := hlim ε hε
  have hpos : ∀ᶠ N : ℕ in atTop,
      0 < ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2 :=
    (tendsto_harmonicRamanujanWindowProjection_norm_sq hm hδ).eventually
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hcard, hpos, eventually_ge_atTop N₀] with N hc hn hN i hi
  obtain ⟨j, hj⟩ := card_eq_one.mp hc
  have hij : i = j := mem_singleton.mp (hj ▸ hi)
  subst j
  have h := hN₀ N hN
  rw [Real.dist_eq, primeSetWindowCoordinateSq_eq P i hj hn] at h
  exact h

/-- Actual eigenline sequences realize each positive conductor's energy
and squared arithmetic mass for arbitrary prime support. -/
theorem exists_primeSet_conductor_eigenline (P : Set ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ idx : ∀ N : ℕ, PrimeHorizonIndex (N + 1),
      Tendsto (fun N => fullPrimeEnergyEigenvalue (N + 1) (idx N))
        atTop (𝓝 (ramanujanAdjunctionEnergy m)) ∧
      Tendsto (fun N =>
        ⟪primeSetHorizonVector P (N + 1),
          (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis (idx N)⟫ ^ 2)
        atTop (𝓝 (primeSetConductorCoefficient P m ^ 2)) := by
  classical
  obtain ⟨δ, hδ, hcard, hnear, hcoord⟩ := exists_primeSet_eigenline_coordinates P hm
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop n).mono fun N hN => by omega
  have hchoice : ∀ N : ℕ, ∃ i : PrimeHorizonIndex (N + 1),
      (fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy m) δ).Nonempty →
        i ∈ fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy m) δ := by
    intro N
    by_cases h : (fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy m) δ).Nonempty
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩, fun hn => False.elim (h hn)⟩
  choose idx hidx using hchoice
  have hmem : ∀ᶠ N : ℕ in atTop,
      idx N ∈ fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy m) δ := by
    filter_upwards [hshift.eventually hcard] with N hc
    apply hidx N
    exact card_pos.mp (by rw [hc]; omega)
  refine ⟨idx, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    apply eventually_atTop.mp
    filter_upwards [hshift.eventually (hnear ε hε), hmem] with N hn hi
    simpa only [Real.dist_eq] using hn (idx N) hi
  · rw [Metric.tendsto_atTop]
    intro ε hε
    apply eventually_atTop.mp
    filter_upwards [hshift.eventually (hcoord ε hε), hmem] with N hn hi
    simpa only [Real.dist_eq] using hn (idx N) hi

end GaloisForLFunctions.ArithmeticCountingPositivity
