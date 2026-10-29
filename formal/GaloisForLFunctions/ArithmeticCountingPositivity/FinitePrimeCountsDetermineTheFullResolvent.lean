import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheConductorCoordinates
import GaloisForLFunctions.ArithmeticCountingPositivity.TheParityTowerDeterminesTheFiniteResolvent
import Batteries.Tactic.OpenPrivate

/-!
# The full resolvent of a finite-prime constraint

The counted conductor weights exhaust unit mass. Every fixed packet has
actual eigenline limits, and the unique ground count bounds all omitted
reciprocal denominators. The entire finite resolvent therefore converges
to the explicit arithmetic secular series, which is strictly increasing
below the first global excitation.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open private tendsto_reciprocal_mass_of_packets from
  GaloisForLFunctions.ArithmeticCountingPositivity.TheParityTowerDeterminesTheFiniteResolvent

local notation "γ" => Real.eulerMascheroniConstant

/-- The normalized arithmetic secular function of a finite prime set. -/
def finiteFlipSecular (F : Finset ℕ) (s : ℝ) : ℝ :=
  -(1 / s) + ∑' k : ℕ, finiteFlipSpectralWeight F (k + 2) /
    (ramanujanAdjunctionEnergy (k + 2) - γ - s)

/-- The full scalar reciprocal reading of the finite-prime constraint. -/
def finiteFlipFiniteResolvent (F : Finset ℕ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑ i : PrimeHorizonIndex N,
    ⟪finiteFlipHorizonVector F N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 /
      (fullPrimeEnergyEigenvalue N i - γ - s)

private theorem conductor_energy_gap (k : ℕ) :
    2 * Real.log 2 ≤ ramanujanAdjunctionEnergy (k + 2) - γ := by
  have h := (ramanujanAdjunctionEnergy_sub_one_ge (by omega : 2 ≤ k + 2)).1
  rwa [ramanujanAdjunctionEnergy_one] at h

private theorem conductor_coefficient_one (F : Finset ℕ) :
    finiteFlipConductorCoefficient F 1 = finiteFlipHarmonicDensity F := by
  simp only [finiteFlipConductorCoefficient, (finiteFlipMobius_isMultiplicative F).map_one,
    Nat.totient_one, Nat.cast_one, Real.sqrt_one, mul_one, div_one]

private theorem hasSum_conductor_coefficients_succ (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) :
    HasSum (fun k : ℕ => finiteFlipConductorCoefficient F (k + 1) ^ 2) 1 := by
  have h := hasSum_finiteFlipConductorCoefficient_sq F hF
  have hz : finiteFlipConductorCoefficient F 0 = 0 := by simp [finiteFlipConductorCoefficient]
  have hs := (summable_nat_add_iff 1).mpr h.summable
  have he := h.tsum_eq
  rw [h.summable.tsum_eq_zero_add, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at he
  simpa only [he] using hs.hasSum

private theorem summable_conductor_weights (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    Summable (finiteFlipSpectralWeight F) := by
  have hc : finiteFlipHarmonicDensity F ^ 2 ≠ 0 :=
    pow_ne_zero 2 (finiteFlipHarmonicDensity_pos hF).ne'
  have h := (hasSum_finiteFlipConductorCoefficient_sq F hF).summable.mul_left
    (finiteFlipHarmonicDensity F ^ 2)⁻¹
  have he : (fun m : ℕ => (finiteFlipHarmonicDensity F ^ 2)⁻¹ *
      finiteFlipConductorCoefficient F m ^ 2) = finiteFlipSpectralWeight F := by
    funext m
    rw [finiteFlipConductorCoefficient_sq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rwa [he] at h

private theorem conductor_weight_nonneg (F : Finset ℕ) (m : ℕ) :
    0 ≤ finiteFlipSpectralWeight F m := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Every positive-conductor reciprocal tail is summable below the first excitation. -/
theorem summable_finiteFlipSecularTail (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {s : ℝ} (_hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    Summable (fun k : ℕ => finiteFlipSpectralWeight F (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) := by
  have hpositive : 0 < 2 * Real.log 2 - s := sub_pos.mpr hs2
  apply Summable.of_nonneg_of_le
    (fun k => div_nonneg (conductor_weight_nonneg F _) ((sub_pos.mpr
      (hs2.trans_le (conductor_energy_gap k))).le))
    (fun k => div_le_div_of_nonneg_left (conductor_weight_nonneg F _) hpositive
      (sub_le_sub_right (conductor_energy_gap k) s))
  exact ((summable_nat_add_iff 2).mpr (summable_conductor_weights F hF)).div_const
    (2 * Real.log 2 - s)

/-- The unit-mass coefficient series is the normalized secular series times the squared mean. -/
theorem hasSum_finiteFlipSecularSeries (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    HasSum (fun k : ℕ => finiteFlipConductorCoefficient F (k + 1) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 1) - γ - s))
      (finiteFlipHarmonicDensity F ^ 2 * finiteFlipSecular F s) := by
  have htail : Summable (fun k : ℕ => finiteFlipConductorCoefficient F (k + 2) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) := by
    have h := (summable_finiteFlipSecularTail F hF hs hs2).mul_left
      (finiteFlipHarmonicDensity F ^ 2)
    have he : (fun k : ℕ => finiteFlipHarmonicDensity F ^ 2 *
        (finiteFlipSpectralWeight F (k + 2) /
          (ramanujanAdjunctionEnergy (k + 2) - γ - s))) =
        (fun k : ℕ => finiteFlipConductorCoefficient F (k + 2) ^ 2 /
          (ramanujanAdjunctionEnergy (k + 2) - γ - s)) := by
      funext k
      rw [finiteFlipConductorCoefficient_sq]
      ring
    rwa [he] at h
  have hfull : Summable (fun k : ℕ => finiteFlipConductorCoefficient F (k + 1) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 1) - γ - s)) :=
    (summable_nat_add_iff 1).mp (by simpa only [Nat.add_assoc] using htail)
  have htailEq : (∑' k : ℕ, finiteFlipConductorCoefficient F (k + 2) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) =
      finiteFlipHarmonicDensity F ^ 2 * ∑' k : ℕ, finiteFlipSpectralWeight F (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
    simp only [finiteFlipConductorCoefficient_sq, mul_div_assoc, tsum_mul_left]
  have hv : (∑' k : ℕ, finiteFlipConductorCoefficient F (k + 1) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 1) - γ - s)) =
        finiteFlipHarmonicDensity F ^ 2 * finiteFlipSecular F s := by
    rw [hfull.tsum_eq_zero_add]
    change finiteFlipConductorCoefficient F 1 ^ 2 /
      (ramanujanAdjunctionEnergy 1 - γ - s) +
      (∑' k : ℕ, finiteFlipConductorCoefficient F (k + 2) ^ 2 /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s)) = _
    rw [conductor_coefficient_one, ramanujanAdjunctionEnergy_one, sub_self,
      zero_sub, div_neg, htailEq, finiteFlipSecular]
    ring
  simpa only [hv] using hfull.hasSum

/-- All actual finite eigenlines are included in the arithmetic resolvent limit. -/
theorem tendsto_finiteFlipFiniteResolvent (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    Tendsto (fun N : ℕ => finiteFlipFiniteResolvent F (N + 1) s) atTop
      (𝓝 (finiteFlipHarmonicDensity F ^ 2 * finiteFlipSecular F s)) := by
  classical
  choose idx he ha using fun k : ℕ =>
    exists_finiteFlip_conductor_eigenline F hF (Nat.succ_pos k)
  have hE (k : ℕ) := (he k).sub_const γ
  let E : (N : ℕ) → PrimeHorizonIndex (N + 1) → ℝ :=
    fun N i => fullPrimeEnergyEigenvalue (N + 1) i - γ
  let a : (N : ℕ) → PrimeHorizonIndex (N + 1) → ℝ := fun N i =>
    ⟪finiteFlipHorizonVector F (N + 1),
      (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis i⟫
  let η := (2 * Real.log 2 - s) / 2
  have hη : 0 < η := by dsimp only [η]; linarith only [hs2]
  have ht : 0 < s + η := add_pos hs hη
  have ht2 : s + η < 2 * Real.log 2 := by dsimp only [η]; linarith only [hs2]
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop n).mono fun N hN => by omega
  have hgap : ∀ᶠ N : ℕ in atTop, ∀ i, i ≠ idx 0 N → η ≤ E N i - s := by
    have hground := (hE 0).eventually_lt_const (by
      simpa only [Nat.zero_add, ramanujanAdjunctionEnergy_one, sub_self] using ht)
    filter_upwards [hshift.eventually
      (eventually_fullPrime_ground_count_one ht ht2), hground] with N hc hg i hi
    have hmem : idx 0 N ∈ fullPrimeEnergySublevel (N + 1) (γ + (s + η)) :=
      mem_filter.mpr ⟨mem_univ _, by linarith only [hg]⟩
    have hnot : i ∉ fullPrimeEnergySublevel (N + 1) (γ + (s + η)) := by
      intro him
      exact hi ((card_le_one_iff.mp hc.le) him hmem)
    have hge : γ + (s + η) ≤ fullPrimeEnergyEigenvalue (N + 1) i := by
      apply le_of_not_gt
      intro hlt
      exact hnot (mem_filter.mpr ⟨mem_univ _, hlt⟩)
    dsimp only [E]
    linarith only [hge]
  have hsep (k l : ℕ) (hkl : k ≠ l) : ∀ᶠ N : ℕ in atTop, idx k N ≠ idx l N := by
    have hd : (ramanujanAdjunctionEnergy (k + 1) - γ) -
        (ramanujanAdjunctionEnergy (l + 1) - γ) ≠ 0 := by
      intro hz
      have heq : ramanujanAdjunctionEnergy (k + 1) = ramanujanAdjunctionEnergy (l + 1) :=
        by linarith only [hz]
      have hnat := ramanujanAdjunctionEnergy_injectiveOn (Nat.succ_pos k) (Nat.succ_pos l) heq
      exact hkl (Nat.succ.inj hnat)
    have hpos := (((hE k).sub (hE l)).pow 2).eventually
      (lt_mem_nhds (sq_pos_of_ne_zero hd))
    filter_upwards [hpos] with N hN hsame
    rw [hsame, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hN
    exact lt_irrefl 0 hN
  have hinj (K : ℕ) : ∀ᶠ N : ℕ in atTop,
      Set.InjOn (fun k => idx k N) (↑(range (K + 1)) : Set ℕ) := by
    have hall : ∀ᶠ N : ℕ in atTop, ∀ k ∈ range (K + 1), ∀ l ∈ range (K + 1),
        k ≠ l → idx k N ≠ idx l N := by
      apply (eventually_all_finset _).mpr
      intro k hk
      apply (eventually_all_finset _).mpr
      intro l hl
      by_cases hkl : k = l
      · exact Eventually.of_forall fun _ h => False.elim (h hkl)
      · exact (hsep k l hkl).mono fun _ h _ => h
    filter_upwards [hall] with N hN k hk l hl hkl
    by_contra hne
    exact hN k hk l hl hne hkl
  have hmass : ∀ᶠ N : ℕ in atTop, (∑ i, a N i ^ 2) = 1 := by
    apply Eventually.of_forall
    intro N
    rw [show (∑ i, a N i ^ 2) = ‖finiteFlipHorizonVector F (N + 1)‖ ^ 2 from
      (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis.sum_sq_inner_left _]
    exact finiteFlipHorizonVector_norm_sq F (by omega)
  have hden (k : ℕ) : ramanujanAdjunctionEnergy (k + 1) - γ - s ≠ 0 := by
    cases k with
    | zero => simpa only [Nat.zero_add, ramanujanAdjunctionEnergy_one, sub_self, zero_sub]
        using neg_ne_zero.mpr hs.ne'
    | succ k => exact (sub_pos.mpr (hs2.trans_le (conductor_energy_gap k))).ne'
  exact tendsto_reciprocal_mass_of_packets E a idx
    (fun k => ramanujanAdjunctionEnergy (k + 1) - γ)
    (fun k => finiteFlipConductorCoefficient F (k + 1) ^ 2) hη hE ha hden hinj hmass hgap
    (hasSum_conductor_coefficients_succ F hF) (hasSum_finiteFlipSecularSeries F hF hs hs2)

/-- The normalized secular function is strictly increasing throughout the physical first gap. -/
theorem finiteFlipSecular_strictMonoOn (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    StrictMonoOn (finiteFlipSecular F) (Set.Ioo 0 (2 * Real.log 2)) := by
  intro s hs t ht hst
  have htail : (∑' k : ℕ, finiteFlipSpectralWeight F (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) ≤
      ∑' k : ℕ, finiteFlipSpectralWeight F (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - t) := by
    exact Summable.tsum_mono
      (summable_finiteFlipSecularTail F hF hs.1 hs.2)
      (summable_finiteFlipSecularTail F hF ht.1 ht.2)
      (fun k => div_le_div_of_nonneg_left (conductor_weight_nonneg F _)
        (sub_pos.mpr (ht.2.trans_le (conductor_energy_gap k)))
        (sub_le_sub_left hst.le _))
  have hdiv : (1 : ℝ) / t < 1 / s :=
    (div_lt_div_iff₀ ht.1 hs.1).mpr (by simpa only [one_mul] using hst)
  dsimp only [finiteFlipSecular]
  linarith only [hdiv, htail]

end GaloisForLFunctions.ArithmeticCountingPositivity
