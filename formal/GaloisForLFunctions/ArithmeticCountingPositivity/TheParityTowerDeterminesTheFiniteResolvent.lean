import GaloisForLFunctions.ArithmeticCountingPositivity.TheParityTowerHasAUniqueSecularRoot
import GaloisForLFunctions.ArithmeticCountingPositivity.FiniteReciprocalMassControlsTheHyperplane
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheConductorTwoIsTheFirstExcitation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiplicativeWeightsPretendingToOneArePaidOnlyByAVanishingLocalFactor

/-!
# The parity tower determines the full finite resolvent

The Möbius transform identifies every prime-power parity coordinate.
Isolated actual eigenlines realize these coefficients and energies.
Bounded spectral counting isolates the ground, while unit tower mass
bounds every omitted reciprocal contribution. Thus finite prime-matrix
resolvents converge to the complete arithmetic parity series.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.BezoutValuationIncidence

local notation "γ" => Real.eulerMascheroniConstant

private theorem horizon_succ_tendsto : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  exact (eventually_ge_atTop n).mono fun N hN => by omega

/-- The arithmetic parity coefficients are exactly the prime-power Möbius transforms. -/
theorem primeParityTowerCoefficient_eq_moebius {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeParityTowerCoefficient p k =
      (primeParityMean p * ∑ d ∈ (p ^ k).divisors,
        moebiusReal (p ^ k / d) * finiteFlip {p} d) /
          Real.sqrt ((p ^ k).totient : ℝ) := by
  cases k with
  | zero => simp [primeParityTowerCoefficient, moebiusReal, finiteFlip]
  | succ k =>
      let f : ArithmeticFunction ℝ :=
        ⟨fun n => if n = 0 then 0 else finiteFlip {p} n, by simp⟩
      have hf (j : ℕ) : f (p ^ j) = (-1 : ℝ) ^ j := by
        simp only [f, ArithmeticFunction.coe_mk, if_neg (pow_ne_zero _ hp.ne_zero),
          finiteFlip, prod_singleton, hp.factorization_pow, Finsupp.single_eq_same]
      have hm : (f * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (p ^ (k + 1)) =
          ∑ d ∈ (p ^ (k + 1)).divisors,
            moebiusReal (p ^ (k + 1) / d) * finiteFlip {p} d := by
        rw [ArithmeticFunction.mul_apply,
          Nat.sum_divisorsAntidiagonal (fun a b => f a *
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
        refine sum_congr rfl fun d hd => ?_
        have hd0 : d ≠ 0 := by
          intro hz
          subst d
          exact (pow_ne_zero _ hp.ne_zero) (zero_dvd_iff.mp (Nat.mem_divisors.mp hd).1)
        simp only [f, ArithmeticFunction.coe_mk, if_neg hd0,
          ArithmeticFunction.intCoe_apply, moebiusReal]
        ring
      have hsum : (∑ d ∈ (p ^ (k + 1)).divisors,
          moebiusReal (p ^ (k + 1) / d) * finiteFlip {p} d) =
            2 * (-1 : ℝ) ^ (k + 1) := by
        rw [← hm,
          TransHorizonIncidenceMechanics.mul_moebius_apply_prime_pow f hp k, hf, hf, pow_succ]
        ring
      rw [primeParityTowerCoefficient, hsum]
      ring

/-- Each prime-power conductor is realized by actual eigenline sequences with
its exact parity mass and energy limits. Horizons start at one to avoid an empty space. -/
theorem exists_primeParity_tower_eigenline {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∃ idx : ∀ N : ℕ, PrimeHorizonIndex (N + 1),
      Tendsto (fun N => fullPrimeEnergyEigenvalue (N + 1) (idx N) - γ)
        atTop (𝓝 (primeParityTowerEnergy p k)) ∧
      Tendsto (fun N =>
        ⟪primeParityHorizonVector p (N + 1),
          (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis (idx N)⟫ ^ 2)
        atTop (𝓝 (primeParityTowerCoefficient p k ^ 2)) := by
  classical
  obtain ⟨δ, hδ, hcard, hnear, hcoord⟩ :=
    exists_primeParity_eigenline_coordinates hp (pow_pos hp.pos k)
  have hshift := horizon_succ_tendsto
  have hchoice : ∀ N : ℕ, ∃ i : PrimeHorizonIndex (N + 1),
      (fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy (p ^ k)) δ).Nonempty →
        i ∈ fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy (p ^ k)) δ := by
    intro N
    by_cases h : (fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy (p ^ k)) δ).Nonempty
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩, fun hn => False.elim (h hn)⟩
  choose idx hidx using hchoice
  have hmem : ∀ᶠ N : ℕ in atTop,
      idx N ∈ fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy (p ^ k)) δ := by
    filter_upwards [hshift.eventually hcard] with N hc
    apply hidx N
    exact card_pos.mp (by rw [hc]; omega)
  have he : Tendsto (fun N => fullPrimeEnergyEigenvalue (N + 1) (idx N))
      atTop (𝓝 (ramanujanAdjunctionEnergy (p ^ k))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    apply eventually_atTop.mp
    filter_upwards [hshift.eventually (hnear ε hε), hmem] with N hn hi
    simpa only [Real.dist_eq] using hn (idx N) hi
  refine ⟨idx, ?_, ?_⟩
  · simpa only [← primeParityTowerEnergy_eq hp k] using he.sub_const γ
  · rw [primeParityTowerCoefficient_eq_moebius hp k, Metric.tendsto_atTop]
    intro ε hε
    apply eventually_atTop.mp
    filter_upwards [hshift.eventually (hcoord ε hε), hmem] with N hn hi
    simpa only [Real.dist_eq, primeParityMean] using hn (idx N) hi

/-- Every energy strictly between the ground and the dyadic excitation
contains exactly one actual prime eigenline eventually. -/
theorem eventually_fullPrime_ground_count_one {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    ∀ᶠ N : ℕ in atTop, (fullPrimeEnergySublevel N (γ + s)).card = 1 := by
  have hclass (m : ℕ) (hm : 0 < m) :
      ramanujanAdjunctionEnergy m < γ + s ↔ m = 1 := by
    constructor
    · intro hlt
      by_contra hne
      have hm2 : 2 ≤ m := by omega
      have hbound := (ramanujanAdjunctionEnergy_sub_one_ge hm2).1
      rw [ramanujanAdjunctionEnergy_one] at hbound
      linarith only [hbound, hlt, hs2]
    · intro he
      subst m
      rw [ramanujanAdjunctionEnergy_one]
      linarith only [hs]
  have hregular : ∀ m : ℕ, 0 < m → ramanujanAdjunctionEnergy m ≠ γ + s := by
    intro m hm he
    by_cases h1 : m = 1
    · subst m
      rw [ramanujanAdjunctionEnergy_one] at he
      linarith only [he, hs]
    · have hbound := (ramanujanAdjunctionEnergy_sub_one_ge (by omega : 2 ≤ m)).1
      rw [ramanujanAdjunctionEnergy_one] at hbound
      linarith only [hbound, he, hs2]
  have hset : adjunctionEnergySublevel (γ + s) = {1} := by
    ext m
    rw [mem_adjunctionEnergySublevel, mem_singleton]
    constructor
    · intro hm
      exact (hclass m hm.1).mp hm.2
    · intro he
      subst m
      exact ⟨by norm_num, (hclass 1 (by norm_num)).mpr rfl⟩
  simpa only [hset, card_singleton] using
    eventually_fullPrime_spectral_count_eq (γ + s) hregular

private theorem tendsto_reciprocal_mass_of_packets
    {ι : ℕ → Type*} [∀ N, Fintype (ι N)] [∀ N, DecidableEq (ι N)]
    (E a : (N : ℕ) → ι N → ℝ) (idx : ℕ → (N : ℕ) → ι N) (d w : ℕ → ℝ)
    {s η F : ℝ} (hη : 0 < η)
    (hE : ∀ k, Tendsto (fun N => E N (idx k N)) atTop (𝓝 (d k)))
    (ha : ∀ k, Tendsto (fun N => a N (idx k N) ^ 2) atTop (𝓝 (w k)))
    (hden : ∀ k, d k - s ≠ 0)
    (hinj : ∀ K, ∀ᶠ N : ℕ in atTop,
      Set.InjOn (fun k => idx k N) (↑(range (K + 1)) : Set ℕ))
    (hmass : ∀ᶠ N : ℕ in atTop, (∑ i, a N i ^ 2) = 1)
    (hgap : ∀ᶠ N : ℕ in atTop, ∀ i, i ≠ idx 0 N → η ≤ E N i - s)
    (hw : HasSum w 1) (hF : HasSum (fun k => w k / (d k - s)) F) :
    Tendsto (fun N => ∑ i, a N i ^ 2 / (E N i - s)) atTop (𝓝 F) := by
  let lower : ℕ → ℕ → ℝ := fun K N =>
    ∑ k ∈ range (K + 1), a N (idx k N) ^ 2 / (E N (idx k N) - s)
  let mass : ℕ → ℕ → ℝ := fun K N => ∑ k ∈ range (K + 1), a N (idx k N) ^ 2
  let lowerLimit : ℕ → ℝ := fun K => ∑ k ∈ range (K + 1), w k / (d k - s)
  let massLimit : ℕ → ℝ := fun K => ∑ k ∈ range (K + 1), w k
  have hl (K : ℕ) : Tendsto (lower K) atTop (𝓝 (lowerLimit K)) :=
    tendsto_finsetSum _ fun k _ => (ha k).div ((hE k).sub_const s) (hden k)
  have hm (K : ℕ) : Tendsto (mass K) atTop (𝓝 (massLimit K)) :=
    tendsto_finsetSum _ fun k _ => ha k
  have hu (K : ℕ) : Tendsto (fun N => lower K N + (1 - mass K N) / η)
      atTop (𝓝 (lowerLimit K + (1 - massLimit K) / η)) :=
    (hl K).add ((tendsto_const_nhds.sub (hm K)).div_const η)
  have hll : Tendsto lowerLimit atTop (𝓝 F) := hF.tendsto_sum_nat.comp horizon_succ_tendsto
  have hml : Tendsto massLimit atTop (𝓝 1) := hw.tendsto_sum_nat.comp horizon_succ_tendsto
  have hul : Tendsto (fun K => lowerLimit K + (1 - massLimit K) / η) atTop (𝓝 F) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_self, zero_div, add_zero] using
      hll.add ((hone.sub hml).div_const η)
  apply tendsto_of_eventual_packet_bounds hl hu hll hul
  intro K
  filter_upwards [hinj K, hmass, hgap] with N hiN hmN hgN
  let S : Finset (ι N) := (range (K + 1)).image (fun k => idx k N)
  have hsum (f : ι N → ℝ) : (∑ i ∈ S, f i) = ∑ k ∈ range (K + 1), f (idx k N) := by
    apply sum_image
    exact fun k hk l hl hkl => hiN hk hl hkl
  have hzero : idx 0 N ∈ S := mem_image.mpr ⟨0, mem_range.mpr (by omega), rfl⟩
  have htail (i : ι N) (hi : i ∈ univ \ S) : η ≤ E N i - s := by
    apply hgN i
    intro he
    exact (mem_sdiff.mp hi).2 (he.symm ▸ hzero)
  have hlo : (∑ i ∈ S, a N i ^ 2 / (E N i - s)) ≤ ∑ i, a N i ^ 2 / (E N i - s) := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ S)
    intro i hi hnot
    exact div_nonneg (sq_nonneg _) (hη.le.trans (htail i (mem_sdiff.mpr ⟨hi, hnot⟩)))
  have hhi := reciprocal_mass_le_packet_add_tail univ S (subset_univ S)
    (fun i => E N i - s) (a N) hη htail
  rw [hsum] at hlo
  rw [hsum, hmN, hsum] at hhi
  exact ⟨hlo, hhi⟩

/-- The scalar resolvent reading of the unit parity constraint on the literal prime matrix. -/
def primeParityFiniteResolvent (p N : ℕ) (s : ℝ) : ℝ :=
  ∑ i : PrimeHorizonIndex N,
    ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 /
      (fullPrimeEnergyEigenvalue N i - γ - s)

/-- Prime-power parity energies strictly increase from the ground. -/
theorem primeParityTowerEnergy_strictMono {p : ℕ} (hp : p.Prime) :
    StrictMono (primeParityTowerEnergy p) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hpR
  have hcorr : 0 < Real.log p / ((p : ℝ) - 1) := div_pos hlog (sub_pos.mpr hpR)
  intro i j hij
  cases i with
  | zero =>
      cases j with
      | zero => omega
      | succ j =>
          change 0 < ((j + 1 : ℕ) : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1)
          exact add_pos (mul_pos (by exact_mod_cast Nat.succ_pos j) hlog) hcorr
  | succ i =>
      cases j with
      | zero => omega
      | succ j =>
          change ((i + 1 : ℕ) : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1) <
            ((j + 1 : ℕ) : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1)
          have hijR : ((i + 1 : ℕ) : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hij
          linarith only [mul_lt_mul_of_pos_right hijR hlog]

/-- Every positive parity-tower energy lies above the first global excitation. -/
theorem primeParityTowerEnergy_ge_excitation {p : ℕ} (hp : p.Prime) (k : ℕ) :
    2 * Real.log 2 ≤ primeParityTowerEnergy p (k + 1) := by
  have hpow : 0 < p ^ k := pow_pos hp.pos k
  have hpk : 2 ≤ p ^ (k + 1) := by
    rw [pow_succ]
    nlinarith only [hpow, hp.two_le]
  have h := (ramanujanAdjunctionEnergy_sub_one_ge hpk).1
  rwa [ramanujanAdjunctionEnergy_one, ← primeParityTowerEnergy_eq hp (k + 1)] at h

/-- Between zero and the first global excitation, finite prime-matrix resolvents
converge to the full counted parity series. The omitted mass is bounded uniformly. -/
theorem tendsto_primeParityFiniteResolvent {p : ℕ} (hp : p.Prime) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    Tendsto (fun N => primeParityFiniteResolvent p (N + 1) s) atTop
      (𝓝 (RHTower.infiniteSecular (primeParityTowerEnergy p) (primeParityTowerCoefficient p) s)) := by
  classical
  choose idx hE ha using exists_primeParity_tower_eigenline hp
  let E : (N : ℕ) → PrimeHorizonIndex (N + 1) → ℝ :=
    fun N i => fullPrimeEnergyEigenvalue (N + 1) i - γ
  let a : (N : ℕ) → PrimeHorizonIndex (N + 1) → ℝ := fun N i =>
    ⟪primeParityHorizonVector p (N + 1),
      (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis i⟫
  let η := (2 * Real.log 2 - s) / 2
  have hη : 0 < η := by dsimp only [η]; linarith only [hs2]
  have ht : 0 < s + η := add_pos hs hη
  have ht2 : s + η < 2 * Real.log 2 := by dsimp only [η]; linarith only [hs2]
  have hgap : ∀ᶠ N : ℕ in atTop, ∀ i, i ≠ idx 0 N → η ≤ E N i - s := by
    have hground := (hE 0).eventually_lt_const (by simpa only [primeParityTowerEnergy] using ht)
    filter_upwards [horizon_succ_tendsto.eventually
      (eventually_fullPrime_ground_count_one ht ht2), hground] with N hc hg i hi
    have hmem : idx 0 N ∈ fullPrimeEnergySublevel (N + 1) (γ + (s + η)) := by
      apply mem_filter.mpr
      exact ⟨mem_univ _, by linarith only [hg]⟩
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
    have hd : primeParityTowerEnergy p k - primeParityTowerEnergy p l ≠ 0 :=
      sub_ne_zero.mpr ((primeParityTowerEnergy_strictMono hp).injective.ne hkl)
    have hpos := (((hE k).sub (hE l)).pow 2).eventually
      (lt_mem_nhds (sq_pos_of_ne_zero hd))
    filter_upwards [hpos] with N hN he
    rw [he, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hN
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
    rw [show (∑ i, a N i ^ 2) = ‖primeParityHorizonVector p (N + 1)‖ ^ 2 from
      (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis.sum_sq_inner_left _]
    exact primeParityHorizonVector_norm_sq p (by omega)
  have hden (k : ℕ) : primeParityTowerEnergy p k - s ≠ 0 := by
    cases k with
    | zero => simpa only [primeParityTowerEnergy, zero_sub] using neg_ne_zero.mpr hs.ne'
    | succ k => exact (sub_pos.mpr (hs2.trans_le (primeParityTowerEnergy_ge_excitation hp k))).ne'
  have hw := hasSum_primeParityTowerCoefficient_sq hp
  have htail : Summable (fun k => primeParityTowerCoefficient p (k + 1) ^ 2 /
      (primeParityTowerEnergy p (k + 1) - s)) := by
    have hpositive : 0 < 2 * Real.log 2 - s := sub_pos.mpr hs2
    apply Summable.of_nonneg_of_le
      (fun k => div_nonneg (sq_nonneg _) ((sub_pos.mpr
        (hs2.trans_le (primeParityTowerEnergy_ge_excitation hp k))).le))
      (fun k => div_le_div_of_nonneg_left (sq_nonneg _) hpositive
        (sub_le_sub_right (primeParityTowerEnergy_ge_excitation hp k) s))
    exact ((summable_nat_add_iff 1).mpr hw.summable).div_const (2 * Real.log 2 - s)
  have hfull : Summable (fun k => primeParityTowerCoefficient p k ^ 2 /
      (primeParityTowerEnergy p k - s)) := (summable_nat_add_iff 1).mp htail
  have hsum : HasSum (fun k => primeParityTowerCoefficient p k ^ 2 /
      (primeParityTowerEnergy p k - s))
      (RHTower.infiniteSecular (primeParityTowerEnergy p) (primeParityTowerCoefficient p) s) := by
    rw [RHTower.infiniteSecular_eq_tsum hfull]
    exact hfull.hasSum
  exact tendsto_reciprocal_mass_of_packets E a idx (primeParityTowerEnergy p)
    (fun k => primeParityTowerCoefficient p k ^ 2) hη hE ha hden hinj hmass hgap hw hsum

end GaloisForLFunctions.ArithmeticCountingPositivity
