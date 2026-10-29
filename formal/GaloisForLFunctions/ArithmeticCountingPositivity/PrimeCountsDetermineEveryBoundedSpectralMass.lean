import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternHasActualConductorCoordinates
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum

/-!
# Prime counts determine every bounded spectral mass

The exact bounded-energy eigenvalue count turns the selected conductor
eigenlines into the whole actual spectral sublevel. Their arithmetic
coordinates therefore determine its full squared constraint mass. Zero
Euler density is exactly escape from every bounded energy window.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- Actual squared constraint mass below an energy threshold. -/
def primeSetBoundedSpectralMass (P : Set ℕ) (N : ℕ) (T : ℝ) : ℝ :=
  ∑ i ∈ fullPrimeEnergySublevel N T,
    ⟪primeSetHorizonVector P N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2

/-- Proper arithmetic energy sublevels leave regular thresholds above
every prescribed bound. No ordering of energies by conductor is needed. -/
theorem exists_regular_adjunction_threshold_gt (B : ℝ) :
    ∃ T : ℝ, B < T ∧ ∀ m : ℕ, 0 < m → ramanujanAdjunctionEnergy m ≠ T := by
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_gap_above_adjunctionEnergySublevel (B + 1)
  let q := min (δ / 2) (1 / 2 : ℝ)
  have hq : 0 < q := lt_min (half_pos hδ) (by norm_num)
  have hq1 : q ≤ 1 / 2 := min_le_right _ _
  have hqδ : q ≤ δ / 2 := min_le_left _ _
  refine ⟨B + 1 - q, by linarith only [hq1], ?_⟩
  intro m hm he
  have hmem : m ∈ adjunctionEnergySublevel (B + 1) :=
    (mem_adjunctionEnergySublevel (B + 1) m).mpr
      ⟨hm, by rw [he]; linarith only [hq]⟩
  have h := hgap m hmem
  rw [he] at h
  linarith only [h, hqδ, hδ]

private theorem bounded_spectral_mass_nonneg (P : Set ℕ) (N : ℕ) (T : ℝ) :
    0 ≤ primeSetBoundedSpectralMass P N T := sum_nonneg fun _ _ => sq_nonneg _

private theorem bounded_spectral_mass_mono (P : Set ℕ) (N : ℕ) {T U : ℝ} (hTU : T ≤ U) :
    primeSetBoundedSpectralMass P N T ≤ primeSetBoundedSpectralMass P N U := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [fullPrimeEnergySublevel, mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.trans_le hTU
  · intro i _ _
    exact sq_nonneg _

/-- At every regular threshold, the whole actual spectral sublevel has
the counted limiting conductor mass, with no omitted eigenlines. -/
theorem tendsto_primeSetBoundedSpectralMass (P : Set ℕ) (T : ℝ)
    (hT : ∀ m : ℕ, 0 < m → ramanujanAdjunctionEnergy m ≠ T) :
    Tendsto (fun N : ℕ => primeSetBoundedSpectralMass P (N + 1) T) atTop
      (𝓝 (∑ m ∈ adjunctionEnergySublevel T, primeSetConductorCoefficient P m ^ 2)) := by
  classical
  let S := adjunctionEnergySublevel T
  have hS (m : S) : 0 < (m : ℕ) := (mem_adjunctionEnergySublevel T m).mp m.property |>.1
  choose idx hE ha using fun m : S => exists_primeSet_conductor_eigenline P (hS m)
  let w : (N : ℕ) → PrimeHorizonIndex (N + 1) → ℝ := fun N i =>
    ⟪primeSetHorizonVector P (N + 1), (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis i⟫ ^ 2
  have hmem : ∀ᶠ N : ℕ in atTop, ∀ m : S,
      idx m N ∈ fullPrimeEnergySublevel (N + 1) T := by
    have hall : ∀ᶠ N : ℕ in atTop, ∀ m ∈ (univ : Finset S),
        idx m N ∈ fullPrimeEnergySublevel (N + 1) T := by
      apply (eventually_all_finset _).mpr
      intro m _
      have hmT : ramanujanAdjunctionEnergy m < T :=
        (mem_adjunctionEnergySublevel T m).mp m.property |>.2
      filter_upwards [(hE m).eventually_lt_const hmT] with N hN
      exact mem_filter.mpr ⟨mem_univ _, hN⟩
    exact hall.mono fun _ h m => h m (mem_univ m)
  have hsep (m l : S) (hml : m ≠ l) : ∀ᶠ N : ℕ in atTop, idx m N ≠ idx l N := by
    have hd : ramanujanAdjunctionEnergy m - ramanujanAdjunctionEnergy l ≠ 0 := by
      intro hz
      apply hml
      apply Subtype.ext
      exact ramanujanAdjunctionEnergy_injectiveOn (hS m) (hS l) (by linarith only [hz])
    have hpos := (((hE m).sub (hE l)).pow 2).eventually
      (lt_mem_nhds (sq_pos_of_ne_zero hd))
    filter_upwards [hpos] with N hN heq
    rw [heq, sub_self, pow_two, zero_mul] at hN
    exact lt_irrefl 0 hN
  have hinj : ∀ᶠ N : ℕ in atTop, Function.Injective (fun m : S => idx m N) := by
    have hall : ∀ᶠ N : ℕ in atTop, ∀ m ∈ (univ : Finset S), ∀ l ∈ (univ : Finset S),
        m ≠ l → idx m N ≠ idx l N := by
      apply (eventually_all_finset _).mpr
      intro m _
      apply (eventually_all_finset _).mpr
      intro l _
      by_cases hml : m = l
      · exact Eventually.of_forall fun _ h => False.elim (h hml)
      · exact (hsep m l hml).mono fun _ h _ => h
    filter_upwards [hall] with N hN m l heq
    by_contra hne
    exact hN m (mem_univ m) l (mem_univ l) hne heq
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop n).mono fun N hN => by omega
  -- Exact cardinality upgrades the selected packet to the entire actual sublevel.
  have hevent : ∀ᶠ N : ℕ in atTop,
      primeSetBoundedSpectralMass P (N + 1) T = ∑ m : S, w N (idx m N) := by
    filter_upwards [hmem, hinj,
      hshift.eventually (eventually_fullPrime_spectral_count_eq T hT)] with N hm hi hc
    have hsub : (univ.image (fun m : S => idx m N)) ⊆ fullPrimeEnergySublevel (N + 1) T := by
      intro i hi
      obtain ⟨m, _, rfl⟩ := mem_image.mp hi
      exact hm m
    have hcard : (univ.image (fun m : S => idx m N)).card =
        (fullPrimeEnergySublevel (N + 1) T).card := by
      rw [card_image_of_injective _ hi, card_univ]
      simpa only [Fintype.card_coe, S] using hc.symm
    have himage : univ.image (fun m : S => idx m N) = fullPrimeEnergySublevel (N + 1) T :=
      eq_of_subset_of_card_le hsub hcard.ge
    change (∑ i ∈ fullPrimeEnergySublevel (N + 1) T, w N i) = _
    rw [← himage, sum_image (fun m _ l _ heq => hi heq)]
  have hlim : Tendsto (fun N : ℕ => ∑ m : S, w N (idx m N)) atTop
      (𝓝 (∑ m : S, primeSetConductorCoefficient P m ^ 2)) :=
    tendsto_finsetSum univ (fun m _ => ha m)
  have hsum : (∑ m : S, primeSetConductorCoefficient P m ^ 2) =
      ∑ m ∈ adjunctionEnergySublevel T, primeSetConductorCoefficient P m ^ 2 :=
    sum_coe_sort (adjunctionEnergySublevel T) (fun m => primeSetConductorCoefficient P m ^ 2)
  rw [hsum] at hlim
  exact hlim.congr' (hevent.mono fun _ h => h.symm)

private theorem bounded_spectral_mass_tendsto_zero (P : Set ℕ)
    (hc : primeSetHarmonicDensity P = 0) (T : ℝ) :
    Tendsto (fun N : ℕ => primeSetBoundedSpectralMass P (N + 1) T) atTop (𝓝 0) := by
  obtain ⟨U, hTU, hU⟩ := exists_regular_adjunction_threshold_gt T
  have hlim : Tendsto (fun N : ℕ => primeSetBoundedSpectralMass P (N + 1) U) atTop (𝓝 0) := by
    simpa only [primeSetConductorCoefficient, hc, zero_mul, zero_div, pow_two,
      sum_const_zero] using tendsto_primeSetBoundedSpectralMass P U hU
  exact squeeze_zero (fun N => bounded_spectral_mass_nonneg P (N + 1) T)
    (fun N => bounded_spectral_mass_mono P (N + 1) hTU.le) hlim

private theorem primeSetConductorCoefficient_one (P : Set ℕ) :
    primeSetConductorCoefficient P 1 = primeSetHarmonicDensity P := by
  have hb : primeSetMobius P 1 = 1 :=
    (primeSetMobius_eq_finiteCutoff P (m := 1) (Q := 1) le_rfl).trans
      (finiteFlipMobius_isMultiplicative (primeSetCutoff P 1)).map_one
  rw [primeSetConductorCoefficient, hb, Nat.totient_one, Nat.cast_one,
    Real.sqrt_one, mul_one, div_one]

/-- Zero Euler density is exactly escape of the actual squared constraint
mass from every bounded energy window. -/
theorem primeSet_bounded_spectral_mass_vanishes_iff (P : Set ℕ) :
    primeSetHarmonicDensity P = 0 ↔
      ∀ T : ℝ, Tendsto (fun N : ℕ => primeSetBoundedSpectralMass P (N + 1) T) atTop (𝓝 0) := by
  constructor
  · exact fun hc T => bounded_spectral_mass_tendsto_zero P hc T
  · intro hzero
    obtain ⟨T, hTγ, hT⟩ := exists_regular_adjunction_threshold_gt Real.eulerMascheroniConstant
    have he : (∑ m ∈ adjunctionEnergySublevel T, primeSetConductorCoefficient P m ^ 2) = 0 :=
      tendsto_nhds_unique (tendsto_primeSetBoundedSpectralMass P T hT) (hzero T)
    have hmem : 1 ∈ adjunctionEnergySublevel T :=
      (mem_adjunctionEnergySublevel T 1).mpr
        ⟨zero_lt_one, by simpa only [ramanujanAdjunctionEnergy_one] using hTγ⟩
    have hsq := single_le_sum (f := fun m => primeSetConductorCoefficient P m ^ 2)
      (fun m _ => sq_nonneg _) hmem
    rw [he, primeSetConductorCoefficient_one] at hsq
    exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))

end GaloisForLFunctions.ArithmeticCountingPositivity
