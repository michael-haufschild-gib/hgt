import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternHasItsFullArithmeticResolvent
import GaloisForLFunctions.ArithmeticCountingPositivity.TheFinitePrimeSecularSignsDetermineTheGap

/-!
# Positive density transfers the exact cutoff gap

At positive Euler density the counted reciprocal series classifies every
actual prime-hyperplane gap. Nonnegative conductor packets then identify
this gap condition with the conditions for all finite prime cutoffs.
Their greatest gaps decrease to the actual infinite-pattern greatest gap.
Every pattern has an attained greatest gap, independently of its density.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

open private finiteFlip_form_bound_iff finiteFlip_form_iff_resolvent gap_downward from
  GaloisForLFunctions.ArithmeticCountingPositivity.TheFinitePrimeSecularSignsDetermineTheGap
open private primeSetFlip_mul_self primeSetCutoff_prime from
  GaloisForLFunctions.ArithmeticCountingPositivity.DivisibilityCountsControlInfinitePrimeFlips
open private primeSetCutoff_mono from
  GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternHasItsEulerProductHarmonicMean
open private primeSetConductorCoefficient_one from
  GaloisForLFunctions.ArithmeticCountingPositivity.PrimeCountsDetermineEveryBoundedSpectralMass
open private conductor_energy_gap conductor_weight_nonneg from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent
open private primeSetSpectralWeight_nonneg finite_weight_le_primeSet_weight
  primeSetSpectralWeight_eq_finiteCutoff from
  GaloisForLFunctions.ArithmeticCountingPositivity.InfinitePrimeCountsHaveAZeroOrUnitConductorMass

local notation "γ" => Real.eulerMascheroniConstant

/-- The normalized arithmetic secular series for an arbitrary prime pattern. -/
def primeSetSecular (P : Set ℕ) (s : ℝ) : ℝ :=
  -(1 / s) + ∑' k : ℕ, primeSetSpectralWeight P (k + 2) /
    (ramanujanAdjunctionEnergy (k + 2) - γ - s)

/-- Positive Euler density makes the unnormalized reciprocal tail summable. -/
theorem summable_primeSetSecularTail (P : Set ℕ) (hc : 0 < primeSetHarmonicDensity P)
    {s : ℝ} (_hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    Summable (fun k : ℕ => primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) := by
  apply Summable.of_nonneg_of_le
    (fun k => div_nonneg (primeSetSpectralWeight_nonneg P _) ((sub_pos.mpr
      (hs2.trans_le (conductor_energy_gap k))).le))
    (fun k => div_le_div_of_nonneg_left (primeSetSpectralWeight_nonneg P _)
      (sub_pos.mpr hs2) (sub_le_sub_right (conductor_energy_gap k) s))
  exact ((summable_nat_add_iff 2).mpr
    ((summable_primeSetSpectralWeight_iff P).mpr hc)).div_const (2 * Real.log 2 - s)

/-- The normalized conductor resolvent is the squared Euler density times
the arithmetic secular series. -/
theorem primeSetConductorResolvent_eq (P : Set ℕ) (hc : 0 < primeSetHarmonicDensity P) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    primeSetConductorResolvent P s = primeSetHarmonicDensity P ^ 2 * primeSetSecular P s := by
  have htail : (∑' k : ℕ, primeSetConductorCoefficient P (k + 2) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) =
      primeSetHarmonicDensity P ^ 2 * ∑' k : ℕ, primeSetSpectralWeight P (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
    have h := (summable_primeSetSecularTail P hc hs hs2).hasSum.mul_left
      (primeSetHarmonicDensity P ^ 2)
    simpa only [primeSetConductorCoefficient_sq, mul_div_assoc] using h.tsum_eq
  rw [primeSetConductorResolvent,
    (summable_primeSetConductorResolvent P hs hs2).tsum_eq_zero_add]
  change primeSetConductorCoefficient P 1 ^ 2 /
    (ramanujanAdjunctionEnergy 1 - γ - s) +
    (∑' k : ℕ, primeSetConductorCoefficient P (k + 2) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) = _
  rw [primeSetConductorCoefficient_one, ramanujanAdjunctionEnergy_one, sub_self,
    zero_sub, div_neg, htail, primeSetSecular]
  ring

/-- The ground reciprocal makes the secular function strictly increasing
throughout the physical first gap. -/
theorem primeSetSecular_strictMonoOn (P : Set ℕ) (hc : 0 < primeSetHarmonicDensity P) :
    StrictMonoOn (primeSetSecular P) (Set.Ioo 0 (2 * Real.log 2)) := by
  intro s hs t ht hst
  have htail : (∑' k : ℕ, primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) ≤
      ∑' k : ℕ, primeSetSpectralWeight P (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - t) :=
    Summable.tsum_mono (summable_primeSetSecularTail P hc hs.1 hs.2)
      (summable_primeSetSecularTail P hc ht.1 ht.2)
      (fun k => div_le_div_of_nonneg_left (primeSetSpectralWeight_nonneg P _)
        (sub_pos.mpr (ht.2.trans_le (conductor_energy_gap k)))
        (sub_le_sub_left hst.le _))
  have hdiv : (1 : ℝ) / t < 1 / s :=
    (div_lt_div_iff₀ ht.1 hs.1).mpr (by simpa only [one_mul] using hst)
  dsimp only [primeSetSecular]
  linarith only [hdiv, htail]

private theorem primeSet_form_bound_iff (P : Set ℕ) {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪primeSetHorizonVector P N, u⟫ = 0 →
      (γ + s) * ‖u‖ ^ 2 ≤ Real.log N * ‖u‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) ↔
      (∀ x : ℕ → ℝ, (∑ n ∈ Icc 1 N, x n / Real.sqrt n) = 0 →
        atomicWeilForm N (fun n => primeSetFlip P n * x n) ≤
          (Real.log N - γ - s) * ∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hform (x : ℕ → ℝ) : atomicWeilForm N (fun n => primeSetFlip P n * x n) =
      atomicWeilForm N (fun n => finiteFlip (primeSetCutoff P N) n * x n) :=
    atomicWeilForm_congr fun n hn => by
      rw [primeSetFlip_eq_finiteFlip_of_le P (mem_Icc.mp hn).2]
  simpa only [primeSetHorizonVector, ← hform] using
    (finiteFlip_form_bound_iff (F := primeSetCutoff P N) hN s)

private theorem primeSet_form_iff_resolvent (P : Set ℕ) {N : ℕ} {s : ℝ}
    (i₀ : PrimeHorizonIndex N)
    (hneg : fullPrimeEnergyEigenvalue N i₀ - γ < s)
    (hpos : ∀ i, i ≠ i₀ → s < fullPrimeEnergyEigenvalue N i - γ)
    (hv : ⟪primeSetHorizonVector P N,
      (fullPrimeMatrix_isHermitian N).eigenvectorBasis i₀⟫ ≠ 0) :
    (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪primeSetHorizonVector P N, u⟫ = 0 →
      (γ + s) * ‖u‖ ^ 2 ≤ Real.log N * ‖u‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) ↔
      primeSetFiniteResolvent P N s ≤ 0 :=
  finiteFlip_form_iff_resolvent (F := primeSetCutoff P N) i₀ hneg hpos hv

private theorem eventually_primeSet_form_iff_resolvent (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    ∀ᶠ N : ℕ in atTop,
      (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex (N + 1)),
        ⟪primeSetHorizonVector P (N + 1), u⟫ = 0 →
          (γ + s) * ‖u‖ ^ 2 ≤ Real.log ((N + 1 : ℕ) : ℝ) * ‖u‖ ^ 2 -
            ⟪Matrix.toEuclideanLin (fullPrimeMatrix (N + 1)) u, u⟫) ↔
        primeSetFiniteResolvent P (N + 1) s ≤ 0 := by
  obtain ⟨idx, hAbs, ha⟩ := exists_primeSet_conductor_eigenline P (by norm_num : 0 < 1)
  have hE := hAbs.sub_const γ
  let t := (s + 2 * Real.log 2) / 2
  have hst : s < t := by dsimp only [t]; linarith only [hs2]
  have ht : 0 < t := hs.trans hst
  have ht2 : t < 2 * Real.log 2 := by dsimp only [t]; linarith only [hs2]
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop n).mono fun N hN => by omega
  have hground := hE.eventually_lt_const (by
    simpa only [ramanujanAdjunctionEnergy_one, sub_self] using hs)
  have hcoord := ha.eventually_const_lt (by
    simpa only [primeSetConductorCoefficient_one] using sq_pos_of_pos hc)
  filter_upwards [hground, hcoord,
    hshift.eventually (eventually_fullPrime_ground_count_one ht ht2)] with N hg haN hcount
  apply primeSet_form_iff_resolvent P (idx N) hg
  · intro i hi
    have hmem : idx N ∈ fullPrimeEnergySublevel (N + 1) (γ + t) :=
      mem_filter.mpr ⟨mem_univ _, by linarith only [hg, hst]⟩
    have hnot : i ∉ fullPrimeEnergySublevel (N + 1) (γ + t) := fun him =>
      hi ((card_le_one_iff.mp hcount.le) him hmem)
    have he : γ + t ≤ fullPrimeEnergyEigenvalue (N + 1) i := by
      apply le_of_not_gt
      intro hlt
      exact hnot (mem_filter.mpr ⟨mem_univ _, hlt⟩)
    linarith only [he, hst]
  · intro hz
    rw [hz] at haN
    norm_num at haN

private theorem tendsto_primeSetFiniteResolvent_secular (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    Tendsto (fun N : ℕ => primeSetFiniteResolvent P (N + 1) s) atTop
      (𝓝 (primeSetHarmonicDensity P ^ 2 * primeSetSecular P s)) := by
  rw [← primeSetConductorResolvent_eq P hc hs hs2]
  exact tendsto_primeSetFiniteResolvent P hs hs2

/-- Every positive-density prime-pattern gap is characterized by the arithmetic secular sign
throughout the interval below it, together with the universal dyadic ceiling. -/
theorem primeSetFlip_hasHyperplaneGap_iff_secular (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) (g : ℝ) :
    HasHyperplaneGap (primeSetFlip P) g ↔
      g ≤ 2 * Real.log 2 ∧ ∀ s : ℝ, 0 < s → s < g → primeSetSecular P s ≤ 0 := by
  constructor
  · intro hg
    have hcap := le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one
      (primeSetFlip_mul_self P) hg
    refine ⟨hcap, fun s hs hsg => ?_⟩
    have hs2 := hsg.trans_le hcap
    by_contra hnot
    have hpositive := (tendsto_primeSetFiniteResolvent_secular P hc hs hs2).eventually_const_lt
      (mul_pos (sq_pos_of_pos (hc)) (lt_of_not_ge hnot))
    let ε := (g - s) / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith only [hsg]
    obtain ⟨N₀, hN₀⟩ := hg ε hε
    have hnonpos : ∀ᶠ N : ℕ in atTop, primeSetFiniteResolvent P (N + 1) s ≤ 0 := by
      filter_upwards [eventually_primeSet_form_iff_resolvent P hc hs hs2,
        eventually_ge_atTop N₀] with N hiff hN
      apply hiff.mp
      apply (primeSet_form_bound_iff P (by omega : 1 ≤ N + 1) s).mpr
      intro x hx
      apply (hN₀ (N + 1) (by omega) x hx).trans
      apply mul_le_mul_of_nonneg_right
      · dsimp only [ε]
        linarith only [hsg]
      · exact sum_nonneg fun n _ => sq_nonneg (x n)
    obtain ⟨N, hpN, hnN⟩ := (hpositive.and hnonpos).exists
    exact not_lt_of_ge hnN hpN
  · rintro ⟨hcap, hsign⟩
    by_cases hg : 0 < g
    · intro ε hε
      obtain ⟨s, hslo, hsg⟩ := exists_between (max_lt hg (sub_lt_self g hε))
      have hs : 0 < s := (le_max_left 0 (g - ε)).trans_lt hslo
      have hs2 : s < 2 * Real.log 2 := hsg.trans_le hcap
      obtain ⟨t, hst, htg⟩ := exists_between hsg
      have ht : 0 < t := hs.trans hst
      have ht2 : t < 2 * Real.log 2 := htg.trans_le hcap
      have hneg : primeSetSecular P s < 0 :=
        (primeSetSecular_strictMonoOn P hc ⟨hs, hs2⟩ ⟨ht, ht2⟩ hst).trans_le
          (hsign t ht htg)
      have hnegative := (tendsto_primeSetFiniteResolvent_secular P hc hs hs2).eventually_lt_const
        (mul_neg_of_pos_of_neg (sq_pos_of_pos (hc)) hneg)
      have hbound : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
          (∑ n ∈ Icc 1 (N + 1), x n / Real.sqrt n) = 0 →
            atomicWeilForm (N + 1) (fun n => primeSetFlip P n * x n) ≤
              (Real.log ((N + 1 : ℕ) : ℝ) - γ - s) * ∑ n ∈ Icc 1 (N + 1), x n ^ 2 := by
        filter_upwards [eventually_primeSet_form_iff_resolvent P hc hs hs2,
          hnegative] with N hiff hnegN
        exact (primeSet_form_bound_iff P (by omega : 1 ≤ N + 1) s).mp (hiff.mpr hnegN.le)
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hbound
      refine ⟨N₀ + 1, ?_⟩
      intro N hN x hx
      cases N with
      | zero => omega
      | succ N =>
          apply (hN₀ N (by omega) x hx).trans
          apply mul_le_mul_of_nonneg_right
          · have hh := (le_max_right 0 (g - ε)).trans_lt hslo
            linarith only [hh]
          · exact sum_nonneg fun n _ => sq_nonneg (x n)
    · exact gap_downward (hasHyperplaneGap_zero_of_mul_self_eq_one
        (primeSetFlip_mul_self P)) (le_of_not_gt hg)

/-- The supremum of all uniform gaps for an arbitrary prime pattern. -/
def primeSetGreatestGap (P : Set ℕ) : ℝ :=
  sSup {g : ℝ | HasHyperplaneGap (primeSetFlip P) g}

private theorem primeSet_gaps_nonempty (P : Set ℕ) :
    Set.Nonempty {g : ℝ | HasHyperplaneGap (primeSetFlip P) g} :=
  ⟨0, hasHyperplaneGap_zero_of_mul_self_eq_one (primeSetFlip_mul_self P)⟩

private theorem primeSet_gaps_bddAbove (P : Set ℕ) :
    BddAbove {g : ℝ | HasHyperplaneGap (primeSetFlip P) g} :=
  ⟨2 * Real.log 2, fun _ hg =>
    le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one (primeSetFlip_mul_self P) hg⟩

/-- Every prime pattern has an attained greatest gap. The epsilon in the
uniform gap definition closes the gap set at its supremum. -/
theorem isGreatest_primeSetFlip_hyperplaneGap (P : Set ℕ) :
    IsGreatest {g : ℝ | HasHyperplaneGap (primeSetFlip P) g} (primeSetGreatestGap P) := by
  refine ⟨?_, fun g hg => le_csSup (primeSet_gaps_bddAbove P) hg⟩
  intro ε hε
  have hex : ∃ g : ℝ, HasHyperplaneGap (primeSetFlip P) g ∧
      primeSetGreatestGap P - ε / 2 < g := by
    by_contra hnone
    have hupper : ∀ g ∈ {g : ℝ | HasHyperplaneGap (primeSetFlip P) g},
        g ≤ primeSetGreatestGap P - ε / 2 := by
      intro g hg
      by_contra hn
      exact hnone ⟨g, hg, lt_of_not_ge hn⟩
    have hb : primeSetGreatestGap P ≤ primeSetGreatestGap P - ε / 2 :=
      csSup_le (primeSet_gaps_nonempty P) hupper
    linarith only [hb, hε]
  obtain ⟨g, hg, hnear⟩ := hex
  obtain ⟨N₀, hN₀⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨N₀, fun N hN x hx => (hN₀ N hN x hx).trans ?_⟩
  apply mul_le_mul_of_nonneg_right
  · linarith only [hnear]
  · exact sum_nonneg fun n _ => sq_nonneg (x n)

/-- The entire gap set is the lower interval ending at its attained supremum. -/
theorem primeSetFlip_hasHyperplaneGap_iff_le_greatestGap (P : Set ℕ) (g : ℝ) :
    HasHyperplaneGap (primeSetFlip P) g ↔ g ≤ primeSetGreatestGap P :=
  ⟨fun hg => (isGreatest_primeSetFlip_hyperplaneGap P).2 hg,
    fun hg => gap_downward (isGreatest_primeSetFlip_hyperplaneGap P).1 hg⟩

/-- The counted density lower bound and universal dyadic ceiling apply to
an attained greatest gap for every prime pattern. -/
theorem primeSetGreatestGap_bounds (P : Set ℕ) :
    2 * Real.log 2 * primeSetHarmonicDensity P ^ 2 ≤ primeSetGreatestGap P ∧
      primeSetGreatestGap P ≤ 2 * Real.log 2 :=
  ⟨(isGreatest_primeSetFlip_hyperplaneGap P).2 (primeSetFlip_hasHyperplaneGap P),
    le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one (primeSetFlip_mul_self P)
      (isGreatest_primeSetFlip_hyperplaneGap P).1⟩

private theorem finiteCutoffSecular_le_primeSetSecular (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) (Q : ℕ) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    finiteFlipSecular (primeSetCutoff P Q) s ≤ primeSetSecular P s := by
  unfold finiteFlipSecular primeSetSecular
  apply add_le_add le_rfl
  exact Summable.tsum_mono
    (summable_finiteFlipSecularTail _ (primeSetCutoff_prime P Q) hs hs2)
    (summable_primeSetSecularTail P hc hs hs2)
    (fun k => div_le_div_of_nonneg_right (finite_weight_le_primeSet_weight P Q _)
      (sub_pos.mpr (hs2.trans_le (conductor_energy_gap k))).le)

/-- At positive Euler density, an actual infinite-pattern gap is equivalent
to the same gap at every finite prime cutoff. -/
theorem primeSetFlip_hasHyperplaneGap_iff_cutoffs (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) (g : ℝ) :
    HasHyperplaneGap (primeSetFlip P) g ↔
      ∀ Q : ℕ, HasHyperplaneGap (finiteFlip (primeSetCutoff P Q)) g := by
  constructor
  · intro hg Q
    have hchar := (primeSetFlip_hasHyperplaneGap_iff_secular P hc g).mp hg
    apply (finiteFlip_hasHyperplaneGap_iff_secular _ (primeSetCutoff_prime P Q) g).mpr
    refine ⟨hchar.1, fun s hs hsg => ?_⟩
    exact (finiteCutoffSecular_le_primeSetSecular P hc Q hs (hsg.trans_le hchar.1)).trans
      (hchar.2 s hs hsg)
  · intro hcut
    have hcap := ((finiteFlip_hasHyperplaneGap_iff_secular _
      (primeSetCutoff_prime P 0) g).mp (hcut 0)).1
    apply (primeSetFlip_hasHyperplaneGap_iff_secular P hc g).mpr
    refine ⟨hcap, fun s hs hsg => ?_⟩
    have hs2 := hsg.trans_le hcap
    have hpartial (K : ℕ) :
        (∑ k ∈ range K, primeSetSpectralWeight P (k + 2) /
          (ramanujanAdjunctionEnergy (k + 2) - γ - s)) ≤ 1 / s := by
      have hsum := summable_finiteFlipSecularTail _ (primeSetCutoff_prime P (K + 2)) hs hs2
      have hsign := ((finiteFlip_hasHyperplaneGap_iff_secular _
        (primeSetCutoff_prime P (K + 2)) g).mp (hcut (K + 2))).2 s hs hsg
      calc
        _ = ∑ k ∈ range K, finiteFlipSpectralWeight (primeSetCutoff P (K + 2)) (k + 2) /
            (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
          apply sum_congr rfl
          intro k hk
          rw [primeSetSpectralWeight_eq_finiteCutoff P (by
            have hk' := mem_range.mp hk
            omega : k + 2 ≤ K + 2)]
        _ ≤ ∑' k : ℕ, finiteFlipSpectralWeight (primeSetCutoff P (K + 2)) (k + 2) /
            (ramanujanAdjunctionEnergy (k + 2) - γ - s) :=
          hsum.sum_le_tsum (range K) (fun k _ => div_nonneg (conductor_weight_nonneg _ _)
            (sub_pos.mpr (hs2.trans_le (conductor_energy_gap k))).le)
        _ ≤ _ := by
          dsimp only [finiteFlipSecular] at hsign
          linarith only [hsign]
    have hbound := le_of_tendsto (summable_primeSetSecularTail P hc hs hs2).hasSum.tendsto_sum_nat
      (Eventually.of_forall hpartial)
    dsimp only [primeSetSecular]
    linarith only [hbound]

/-- At positive Euler density, the exact greatest gaps of the finite prime
cutoffs decrease to the actual infinite-pattern greatest gap. -/
theorem tendsto_primeSetCutoff_greatestGap (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) :
    Tendsto (fun Q : ℕ => finiteFlipGreatestGap (primeSetCutoff P Q)) atTop
      (𝓝 (primeSetGreatestGap P)) := by
  have hanti : Antitone (fun Q : ℕ => finiteFlipGreatestGap (primeSetCutoff P Q)) :=
    fun Q N hQN => finiteFlipGreatestGap_antitone (primeSetCutoff_mono P hQN)
      (primeSetCutoff_prime P N)
  have hle (Q : ℕ) : primeSetGreatestGap P ≤ finiteFlipGreatestGap (primeSetCutoff P Q) :=
    (isGreatest_finiteFlip_hyperplaneGap _ (primeSetCutoff_prime P Q)).2
      ((primeSetFlip_hasHyperplaneGap_iff_cutoffs P hc _).mp
        (isGreatest_primeSetFlip_hyperplaneGap P).1 Q)
  have hb : BddBelow (Set.range (fun Q : ℕ => finiteFlipGreatestGap (primeSetCutoff P Q))) := by
    refine ⟨primeSetGreatestGap P, ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact hle Q
  have hgap : HasHyperplaneGap (primeSetFlip P)
      (⨅ Q : ℕ, finiteFlipGreatestGap (primeSetCutoff P Q)) := by
    apply (primeSetFlip_hasHyperplaneGap_iff_cutoffs P hc _).mpr
    intro Q
    apply (finiteFlip_hasHyperplaneGap_iff_le_greatestGap _ (primeSetCutoff_prime P Q) _).mpr
    exact ciInf_le hb Q
  have heq : (⨅ Q : ℕ, finiteFlipGreatestGap (primeSetCutoff P Q)) = primeSetGreatestGap P :=
    le_antisymm ((isGreatest_primeSetFlip_hyperplaneGap P).2 hgap) (le_ciInf hle)
  simpa only [heq] using tendsto_atTop_ciInf hanti hb

#print axioms summable_primeSetSecularTail
#print axioms primeSetConductorResolvent_eq
#print axioms primeSetSecular_strictMonoOn
#print axioms primeSetFlip_hasHyperplaneGap_iff_secular
#print axioms isGreatest_primeSetFlip_hyperplaneGap
#print axioms primeSetFlip_hasHyperplaneGap_iff_le_greatestGap
#print axioms primeSetGreatestGap_bounds
#print axioms primeSetFlip_hasHyperplaneGap_iff_cutoffs
#print axioms tendsto_primeSetCutoff_greatestGap

end GaloisForLFunctions.ArithmeticCountingPositivity
