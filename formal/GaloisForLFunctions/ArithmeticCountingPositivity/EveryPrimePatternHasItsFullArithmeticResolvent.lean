import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeCountsDetermineEveryBoundedSpectralMass
import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent

/-!
# Every prime pattern has its full arithmetic resolvent

Positive Euler density gives unit counted conductor mass, which exhausts
the actual resolvent through finite packets. At zero density the unit
horizon mass escapes every bounded energy window. A common separation
from the physical denominator and a reciprocal high-energy bound then
force the full actual reading to vanish.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open private tendsto_reciprocal_mass_of_packets from
  GaloisForLFunctions.ArithmeticCountingPositivity.TheParityTowerDeterminesTheFiniteResolvent
open private conductor_energy_gap from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent

local notation "γ" => Real.eulerMascheroniConstant

/-- The full scalar reciprocal reading of an arbitrary prime constraint. -/
def primeSetFiniteResolvent (P : Set ℕ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑ i : PrimeHorizonIndex N,
    ⟪primeSetHorizonVector P N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 /
      (fullPrimeEnergyEigenvalue N i - γ - s)

/-- The reciprocal series of the counted normalized conductor coefficients. -/
def primeSetConductorResolvent (P : Set ℕ) (s : ℝ) : ℝ :=
  ∑' k : ℕ, primeSetConductorCoefficient P (k + 1) ^ 2 /
    (ramanujanAdjunctionEnergy (k + 1) - γ - s)

private theorem hasSum_primeSet_coefficients_succ (P : Set ℕ) :
    HasSum (fun k : ℕ => primeSetConductorCoefficient P (k + 1) ^ 2)
      (if primeSetHarmonicDensity P = 0 then 0 else 1) := by
  have h := hasSum_primeSetConductorCoefficient_sq P
  have hz : primeSetConductorCoefficient P 0 = 0 := by simp [primeSetConductorCoefficient]
  have hs := (summable_nat_add_iff 1).mpr h.summable
  have he := h.tsum_eq
  rw [h.summable.tsum_eq_zero_add, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at he
  simpa only [he] using hs.hasSum

/-- The normalized conductor reciprocal series is absolutely summable
throughout the physical first gap, for every prime pattern. -/
theorem summable_primeSetConductorResolvent (P : Set ℕ) {s : ℝ}
    (_hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    Summable (fun k : ℕ => primeSetConductorCoefficient P (k + 1) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 1) - γ - s)) := by
  have hpositive : 0 < 2 * Real.log 2 - s := sub_pos.mpr hs2
  have htail : Summable (fun k : ℕ => primeSetConductorCoefficient P (k + 2) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) := by
    apply Summable.of_nonneg_of_le
      (fun k => div_nonneg (sq_nonneg _) ((sub_pos.mpr
        (hs2.trans_le (conductor_energy_gap k))).le))
      (fun k => div_le_div_of_nonneg_left (sq_nonneg _) hpositive
        (sub_le_sub_right (conductor_energy_gap k) s))
    exact ((summable_nat_add_iff 2).mpr
      (hasSum_primeSetConductorCoefficient_sq P).summable).div_const (2 * Real.log 2 - s)
  exact (summable_nat_add_iff 1).mp (by simpa only [Nat.add_assoc] using htail)

private theorem reciprocal_reading_vanishes_of_mass_escape
    {ι : ℕ → Type*} [∀ N, Fintype (ι N)]
    (E a : (N : ℕ) → ι N → ℝ) {s η : ℝ} (hη : 0 < η)
    (hmass : ∀ᶠ N : ℕ in atTop, (∑ i, a N i ^ 2) = 1)
    (hden : ∀ᶠ N : ℕ in atTop, ∀ i, η ≤ |E N i - s|)
    (hescape : ∀ T : ℝ, Tendsto
      (fun N => ∑ i ∈ univ.filter (fun i => E N i < T), a N i ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ i, a N i ^ 2 / (E N i - s)) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  let T := s + 2 / ε
  have hTs : 0 < T - s := by
    dsimp only [T]
    simpa only [add_sub_cancel_left] using div_pos (by norm_num : (0 : ℝ) < 2) hε
  have htail : 1 / (T - s) = ε / 2 := by
    dsimp only [T]
    rw [add_sub_cancel_left]
    field_simp
  have hsmall := ((hescape T).div_const η).eventually_lt_const
    (by simpa only [zero_div] using half_pos hε)
  apply eventually_atTop.mp
  filter_upwards [hmass, hden, hsmall] with N hm hd hl
  have hterm (i : ι N) : a N i ^ 2 / |E N i - s| ≤
      (if E N i < T then a N i ^ 2 / η else 0) + a N i ^ 2 / (T - s) := by
    by_cases hi : E N i < T
    · rw [if_pos hi]
      exact (div_le_div_of_nonneg_left (sq_nonneg _) hη (hd i)).trans
        (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hTs.le))
    · rw [if_neg hi, zero_add]
      have hle : T - s ≤ E N i - s := sub_le_sub_right (le_of_not_gt hi) s
      rw [abs_of_pos (hTs.trans_le hle)]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hTs hle
  have hlow : (∑ i : ι N, if E N i < T then a N i ^ 2 / η else 0) =
      (∑ i ∈ univ.filter (fun i => E N i < T), a N i ^ 2) / η := by
    rw [sum_div, sum_filter]
  have hbound : |∑ i, a N i ^ 2 / (E N i - s)| ≤
      (∑ i ∈ univ.filter (fun i => E N i < T), a N i ^ 2) / η + 1 / (T - s) := by
    calc
      _ ≤ ∑ i, |a N i ^ 2 / (E N i - s)| := abs_sum_le_sum_abs _ _
      _ = ∑ i, a N i ^ 2 / |E N i - s| := by
        apply sum_congr rfl
        intro i _
        rw [abs_div, abs_of_nonneg (sq_nonneg _)]
      _ ≤ ∑ i, ((if E N i < T then a N i ^ 2 / η else 0) + a N i ^ 2 / (T - s)) :=
        sum_le_sum fun i _ => hterm i
      _ = _ := by rw [sum_add_distrib, hlow, ← sum_div, hm]
  have habs : |∑ i, a N i ^ 2 / (E N i - s)| < ε := by
    rw [htail] at hbound
    linarith only [hbound, hl]
  simpa only [Real.dist_eq, sub_zero] using habs

/-- The complete actual resolvent converges to the counted conductor
series for every prime pattern, including zero Euler density. -/
theorem tendsto_primeSetFiniteResolvent (P : Set ℕ) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    Tendsto (fun N : ℕ => primeSetFiniteResolvent P (N + 1) s) atTop
      (𝓝 (primeSetConductorResolvent P s)) := by
  classical
  choose idx he ha using fun k : ℕ =>
    exists_primeSet_conductor_eigenline P (Nat.succ_pos k)
  have hE (k : ℕ) := (he k).sub_const γ
  let E : (N : ℕ) → PrimeHorizonIndex (N + 1) → ℝ :=
    fun N i => fullPrimeEnergyEigenvalue (N + 1) i - γ
  let a : (N : ℕ) → PrimeHorizonIndex (N + 1) → ℝ := fun N i =>
    ⟪primeSetHorizonVector P (N + 1),
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
  have hmass : ∀ᶠ N : ℕ in atTop, (∑ i, a N i ^ 2) = 1 := by
    apply Eventually.of_forall
    intro N
    rw [show (∑ i, a N i ^ 2) = ‖primeSetHorizonVector P (N + 1)‖ ^ 2 from
      (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis.sum_sq_inner_left _]
    exact primeSetHorizonVector_norm_sq P (by omega)
  by_cases hc : primeSetHarmonicDensity P = 0
  · -- Escape makes the low-energy mass small; the high-energy reciprocal is uniformly small.
    have hz : primeSetConductorResolvent P s = 0 := by
      simp only [primeSetConductorResolvent, primeSetConductorCoefficient, hc,
        zero_mul, zero_div, pow_two, tsum_zero]
    rw [hz]
    have hground := (hE 0).eventually_lt_const (by
      simpa only [Nat.zero_add, ramanujanAdjunctionEnergy_one, sub_self] using half_pos hs)
    have hden : ∀ᶠ N : ℕ in atTop, ∀ i, min (s / 2) η ≤ |E N i - s| := by
      filter_upwards [hground, hgap] with N hg hN i
      by_cases hi : i = idx 0 N
      · subst i
        have hg' : E N (idx 0 N) < s / 2 := hg
        have hneg : E N (idx 0 N) - s < 0 := by linarith only [hg', hs]
        rw [abs_of_neg hneg]
        exact (min_le_left _ _).trans (by linarith only [hg'])
      · have hb := hN i hi
        rw [abs_of_pos (hη.trans_le hb)]
        exact (min_le_right _ _).trans hb
    have hescape (T : ℝ) : Tendsto
        (fun N => ∑ i ∈ univ.filter (fun i => E N i < T), a N i ^ 2) atTop (𝓝 0) := by
      have heq (N : ℕ) : univ.filter (fun i => E N i < T) =
          fullPrimeEnergySublevel (N + 1) (γ + T) := by
        ext i
        simp only [mem_filter, mem_univ, true_and, fullPrimeEnergySublevel, E]
        constructor <;> intro h <;> linarith only [h]
      have h := (primeSet_bounded_spectral_mass_vanishes_iff P).mp hc (γ + T)
      simpa only [primeSetBoundedSpectralMass, ← heq] using h
    exact reciprocal_reading_vanishes_of_mass_escape E a
      (lt_min (half_pos hs) hη) hmass hden hescape
  · have hsep (k l : ℕ) (hkl : k ≠ l) : ∀ᶠ N : ℕ in atTop, idx k N ≠ idx l N := by
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
        intro k _
        apply (eventually_all_finset _).mpr
        intro l _
        by_cases hkl : k = l
        · exact Eventually.of_forall fun _ h => False.elim (h hkl)
        · exact (hsep k l hkl).mono fun _ h _ => h
      filter_upwards [hall] with N hN k hk l hl hkl
      by_contra hne
      exact hN k hk l hl hne hkl
    have hden (k : ℕ) : ramanujanAdjunctionEnergy (k + 1) - γ - s ≠ 0 := by
      cases k with
      | zero => simpa only [Nat.zero_add, ramanujanAdjunctionEnergy_one, sub_self, zero_sub]
          using neg_ne_zero.mpr hs.ne'
      | succ k => exact (sub_pos.mpr (hs2.trans_le (conductor_energy_gap k))).ne'
    have hw : HasSum (fun k : ℕ => primeSetConductorCoefficient P (k + 1) ^ 2) 1 := by
      simpa only [if_neg hc] using hasSum_primeSet_coefficients_succ P
    exact tendsto_reciprocal_mass_of_packets E a idx
      (fun k => ramanujanAdjunctionEnergy (k + 1) - γ)
      (fun k => primeSetConductorCoefficient P (k + 1) ^ 2) hη hE ha hden hinj hmass hgap
      hw (summable_primeSetConductorResolvent P hs hs2).hasSum

end GaloisForLFunctions.ArithmeticCountingPositivity
