import GaloisForLFunctions.RHTower.Sieve.KloostermanSourceFourier
import GaloisForLFunctions.RHTower.Sieve.LargeSieveExpSum

/-!
# Farey large sieve for Kloosterman source transforms

Inverse units modulo the stored clocks `q + 1` give reduced Farey frequencies.  Reindexing their
source transforms as one finite trigonometric polynomial therefore gives a collective large-sieve
bound over every positive stored clock below a common cutoff.
-/

open scoped BigOperators
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Source coefficients supported on a finite subset of `[0, N)`. -/
def kloostermanSupportedCoefficientVec
    (N : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) : Fin N → ℂ :=
  fun n => if (n : ℕ) ∈ B then b n else 0

private theorem circleFreq_pow' (x : ℝ) (n : ℕ) :
    (circleFreq x) ^ n = circleFreq ((n : ℝ) * x) := by
  rw [circleFreq, circleFreq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Sparse coefficient vectors evaluate to the corresponding weighted exponential sum. -/
theorem expSum_kloostermanSupportedCoefficientVec
    {N : ℕ} (B : Finset ℕ) (hB : B ⊆ Finset.range N)
    (b : ℕ → ℂ) (θ : ℝ) :
    expSum N (kloostermanSupportedCoefficientVec N B b) θ =
      ∑ n ∈ B, b n * circleFreq ((n : ℝ) * θ) := by
  classical
  have hfilter : (Finset.range N).filter (fun n => n ∈ B) = B := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hB h, h⟩⟩
  have hstep :
      ∑ n : Fin N,
          kloostermanSupportedCoefficientVec N B b n * (circleFreq θ) ^ (n : ℕ) =
        ∑ n ∈ Finset.range N,
          (if n ∈ B then b n else 0) * (circleFreq θ) ^ n :=
    Fin.sum_univ_eq_sum_range
      (fun n => (if n ∈ B then b n else 0) * (circleFreq θ) ^ n) N
  have hite : ∀ n : ℕ,
      (if n ∈ B then b n else 0) * (circleFreq θ) ^ n =
        if n ∈ B then b n * (circleFreq θ) ^ n else 0 := by
    intro n
    by_cases h : n ∈ B <;> simp [h]
  rw [expSum, hstep, Finset.sum_congr rfl (fun n _ => hite n),
    ← Finset.sum_filter, hfilter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [circleFreq_pow']

/-- Energy of a sparse coefficient vector is its source coefficient energy. -/
theorem sum_norm_sq_kloostermanSupportedCoefficientVec
    {N : ℕ} (B : Finset ℕ) (hB : B ⊆ Finset.range N)
    (b : ℕ → ℂ) :
    ∑ n : Fin N, ‖kloostermanSupportedCoefficientVec N B b n‖ ^ 2 =
      ∑ n ∈ B, ‖b n‖ ^ 2 := by
  classical
  have hfilter : (Finset.range N).filter (fun n => n ∈ B) = B := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hB h, h⟩⟩
  have hstep :
      ∑ n : Fin N, ‖kloostermanSupportedCoefficientVec N B b n‖ ^ 2 =
        ∑ n ∈ Finset.range N,
          if n ∈ B then ‖b n‖ ^ 2 else 0 := by
    have h1 :
        ∑ n : Fin N, ‖kloostermanSupportedCoefficientVec N B b n‖ ^ 2 =
          ∑ n ∈ Finset.range N,
            ‖(if n ∈ B then b n else 0)‖ ^ 2 :=
      Fin.sum_univ_eq_sum_range
        (fun n => ‖(if n ∈ B then b n else 0)‖ ^ 2) N
    rw [h1]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n ∈ B <;> simp [h]
  rw [hstep, ← Finset.sum_filter, hfilter]

/-- Standard additive character at a natural multiple of a unit, in circle-frequency form. -/
theorem stdAddChar_nat_mul_unit_eq_circleFreq_pow
    (q n : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) =
      circleFreq (((u : ZMod q).val : ℝ) / (q : ℝ)) ^ n := by
  have hz : (n : ZMod q) * (u : ZMod q) =
      (n * (u : ZMod q).val : ℕ) := by
    calc
      (n : ZMod q) * (u : ZMod q) =
          (n : ZMod q) * ((u : ZMod q).val : ZMod q) := by
        rw [ZMod.natCast_zmod_val]
      _ = (n * (u : ZMod q).val : ℕ) := by norm_cast
  rw [hz]
  have hchar :
      ZMod.stdAddChar ((n * (u : ZMod q).val : ℕ) : ZMod q) =
        Complex.exp
          (2 * Real.pi * Complex.I * (n * (u : ZMod q).val : ℕ) / q) := by
    simpa using
      (ZMod.stdAddChar_coe (N := q) (n * (u : ZMod q).val : ℕ))
  rw [hchar, circleFreq_pow', circleFreq]
  congr 1
  push_cast
  ring

/-- A Kloosterman source transform is the sparse trigonometric polynomial at its inverse-unit
Farey frequency. -/
theorem kloostermanSourceFourier_eq_expSum
    {N q : ℕ} [NeZero q]
    (B : Finset ℕ) (hB : B ⊆ Finset.range N) (b : ℕ → ℂ)
    (x : (ZMod q)ˣ) :
    kloostermanSourceFourier q B b x =
      expSum N (kloostermanSupportedCoefficientVec N B b)
        ((((x⁻¹ : (ZMod q)ˣ) : ZMod q).val : ℝ) / (q : ℝ)) := by
  rw [expSum_kloostermanSupportedCoefficientVec B hB]
  unfold kloostermanSourceFourier
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [stdAddChar_nat_mul_unit_eq_circleFreq_pow, circleFreq_pow']

/-- Reduced Farey pair attached to an inverse unit modulo one stored clock. -/
def kloostermanUnitFareyPair (q : ℕ) (x : (ZMod (q + 1))ˣ) : ℕ × ℕ :=
  ((((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1)).val), q + 1)

/-- Farey fibre contributed by one stored clock. -/
def kloostermanUnitFareyFibre (q : ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.image (kloostermanUnitFareyPair q)

/-- Union of inverse-unit Farey fibres across stored clocks. -/
def kloostermanUnitFareySet (Q : Finset ℕ) : Finset (ℕ × ℕ) :=
  Q.biUnion kloostermanUnitFareyFibre

theorem kloostermanUnitFareyPair_injective (q : ℕ) :
    Function.Injective (kloostermanUnitFareyPair q) := by
  intro x y hxy
  apply inv_injective
  apply Units.ext
  apply ZMod.val_injective (q + 1)
  exact congrArg Prod.fst hxy

private theorem kloostermanUnitFareyFibre_pairwiseDisjoint (Q : Finset ℕ) :
    (Q : Set ℕ).PairwiseDisjoint kloostermanUnitFareyFibre := by
  intro q _ r _ hqr
  change Disjoint (kloostermanUnitFareyFibre q) (kloostermanUnitFareyFibre r)
  rw [Finset.disjoint_left]
  intro p hpq hpr
  rw [kloostermanUnitFareyFibre, Finset.mem_image] at hpq hpr
  obtain ⟨x, _, rfl⟩ := hpq
  obtain ⟨y, _, hpair⟩ := hpr
  apply hqr
  have hsnd := congrArg Prod.snd hpair
  simp only [kloostermanUnitFareyPair] at hsnd
  omega

/-- Reindex the union of unit Farey fibres as the original nested unit sum. -/
theorem sum_kloostermanUnitFareySet
    (Q : Finset ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ kloostermanUnitFareySet Q, F p =
      ∑ q ∈ Q, ∑ x : (ZMod (q + 1))ˣ, F (kloostermanUnitFareyPair q x) := by
  rw [kloostermanUnitFareySet,
    Finset.sum_biUnion (kloostermanUnitFareyFibre_pairwiseDisjoint Q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [kloostermanUnitFareyFibre,
    Finset.sum_image (kloostermanUnitFareyPair_injective q).injOn]

/-- Weighted energy of all unit source frequencies across the stored clocks. -/
def kloostermanWeightedUnitFrequencyEnergy
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, Complex.normSq (w q) *
    ∑ x : (ZMod (q + 1))ˣ,
      Complex.normSq (kloostermanSourceFourier (q + 1) B b x)

/-- Collective source energy at all inverse-unit frequencies obeys the Farey large sieve. -/
theorem sum_normSq_kloostermanSourceFourier_le_largeSieve
    {N M : ℕ} (hM : 2 ≤ M)
    (Q : Finset ℕ) (hpos : ∀ q ∈ Q, 0 < q)
    (hcut : ∀ q ∈ Q, q + 1 ≤ M)
    (B : Finset ℕ) (hB : B ⊆ Finset.range N) (b : ℕ → ℂ) :
    ∑ q ∈ Q, ∑ x : (ZMod (q + 1))ˣ,
        Complex.normSq (kloostermanSourceFourier (q + 1) B b x) ≤
      ((N : ℝ) + (M : ℝ) ^ 2 * (1 + Real.log ((M : ℝ) ^ 2 / 2 + 1))) *
        ∑ n ∈ B, Complex.normSq (b n) := by
  classical
  have hmem : ∀ p ∈ kloostermanUnitFareySet Q,
      0 < p.2 ∧ p.2 ≤ M ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2 := by
    intro p hp
    rw [kloostermanUnitFareySet, Finset.mem_biUnion] at hp
    obtain ⟨q, hq, hp⟩ := hp
    rw [kloostermanUnitFareyFibre, Finset.mem_image] at hp
    obtain ⟨x, _, rfl⟩ := hp
    have hqpos := hpos q hq
    letI : Nontrivial (ZMod (q + 1)) := ZMod.nontrivial_iff.mpr (by omega)
    have hvalpos :
        0 < (((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1)).val) := by
      exact Nat.pos_of_ne_zero
        ((ZMod.val_ne_zero _).mpr (Units.ne_zero (x⁻¹)))
    have hvallt :
        (((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1)).val) < q + 1 :=
      ZMod.val_lt _
    exact ⟨Nat.succ_pos q, hcut q hq, hvalpos, hvallt.le,
      ZMod.val_coe_unit_coprime (x⁻¹)⟩
  have hlarge := largeSieve_expSum_farey N hM (kloostermanUnitFareySet Q) hmem
    (kloostermanSupportedCoefficientVec N B b)
  rw [sum_kloostermanUnitFareySet] at hlarge
  simp only [kloostermanUnitFareyPair] at hlarge
  simp_rw [← kloostermanSourceFourier_eq_expSum B hB] at hlarge
  rw [sum_norm_sq_kloostermanSupportedCoefficientVec B hB b] at hlarge
  simpa only [Complex.normSq_eq_norm_sq] using hlarge

/-- Uniformly bounded clock weights transport the Farey large sieve to weighted source energy. -/
theorem kloostermanWeightedUnitFrequencyEnergy_le_largeSieve
    {N M : ℕ} (hM : 2 ≤ M)
    (Q : Finset ℕ) (hpos : ∀ q ∈ Q, 0 < q)
    (hcut : ∀ q ∈ Q, q + 1 ≤ M)
    (w : ℕ → ℂ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ q ∈ Q, Complex.normSq (w q) ≤ W)
    (B : Finset ℕ) (hB : B ⊆ Finset.range N) (b : ℕ → ℂ) :
    kloostermanWeightedUnitFrequencyEnergy Q w B b ≤
      W * (((N : ℝ) + (M : ℝ) ^ 2 *
        (1 + Real.log ((M : ℝ) ^ 2 / 2 + 1))) *
          ∑ n ∈ B, Complex.normSq (b n)) := by
  unfold kloostermanWeightedUnitFrequencyEnergy
  calc
    (∑ q ∈ Q, Complex.normSq (w q) *
        ∑ x : (ZMod (q + 1))ˣ,
          Complex.normSq (kloostermanSourceFourier (q + 1) B b x)) ≤
        ∑ q ∈ Q, W * ∑ x : (ZMod (q + 1))ˣ,
          Complex.normSq (kloostermanSourceFourier (q + 1) B b x) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hw q hq)
        (Finset.sum_nonneg fun x hx => Complex.normSq_nonneg _)
    _ = W * ∑ q ∈ Q, ∑ x : (ZMod (q + 1))ˣ,
          Complex.normSq (kloostermanSourceFourier (q + 1) B b x) := by
      rw [Finset.mul_sum]
    _ ≤ W * (((N : ℝ) + (M : ℝ) ^ 2 *
          (1 + Real.log ((M : ℝ) ^ 2 / 2 + 1))) *
            ∑ n ∈ B, Complex.normSq (b n)) :=
      mul_le_mul_of_nonneg_left
        (sum_normSq_kloostermanSourceFourier_le_largeSieve
          hM Q hpos hcut B hB b) hW

end

end RHTower.Sieve
