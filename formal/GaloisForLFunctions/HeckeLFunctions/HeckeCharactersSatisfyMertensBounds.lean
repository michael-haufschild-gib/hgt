import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsDoNotVanishOnTheLineReOne
import GaloisForLFunctions.HeckeLFunctions.HeckeHarmonicSumsSatisfyTheIdealHyperbolaIdentity
import GaloisForLFunctions.ArtinMertens.PrimePowerWeightsHavePowerBounds
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterRemovesTheModulusEulerFactors
import GaloisForLFunctions.ArtinMertens.TheMertensTheoremForPrimeIdealsHasABoundedError
import GaloisForLFunctions.HTGeometry.LogWeightedGeometricSum
import GaloisForLFunctions.ArtinMertens.TheDegreeOnePrimesCarryTheMertensSum

/-!
# Mertens bounds for Hecke characters

The harmonic ideal hyperbola identity, power-saving harmonic tails, and
nonvanishing at one bound the prime-power Mertens sum of every nontrivial
ray class character. The trivial character removes finitely many geometric
prime-power tails from the established number-field Mertens formula.
The bounded composite-norm remainder also gives both conclusions for sums
over prime ideals themselves.
-/

noncomputable section
open Finset NumberField Ideal Module IsDedekindDomain
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions
open ArtinMertens
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

theorem heckeHarmonicTailExponent_lt_one : heckeHarmonicTailExponent (K := K) < 1 := by
  have hn : (1 : ℝ) ≤ finrank ℚ K := by exact_mod_cast finrank_pos
  have hi : (finrank ℚ K : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  unfold heckeHarmonicTailExponent
  linarith

/-- The harmonic approximation remains summable over the prime-power hyperbola. -/
theorem exists_norm_heckeMertens_hyperbola_error_le {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N →
      ‖heckeLogarithmicHarmonicSum 𝔪 ψ N -
        heckeLCont 𝔪 ψ 1 * heckePrimePowerMertensSum 𝔪 ψ N‖ ≤ B := by
  let δ := heckeHarmonicTailExponent (K := K)
  have hδ : 0 < δ := heckeHarmonicTailExponent_pos (K := K)
  have hδ1 : δ < 1 := heckeHarmonicTailExponent_lt_one (K := K)
  obtain ⟨C, hC, htail⟩ := exists_norm_heckeLCont_one_sub_harmonic_le 𝔪 hψ
  obtain ⟨D, hD, hprime⟩ := exists_sum_primePowersLe_log_rpow_le (K := K)
    (σ := 1 - δ) (by linarith) (by linarith)
  refine ⟨C * D, fun N hN => ?_⟩
  have hx : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : heckeLogarithmicHarmonicSum 𝔪 ψ N -
      heckeLCont 𝔪 ψ 1 * heckePrimePowerMertensSum 𝔪 ψ N =
      ∑ pk ∈ primePowersLe K N, heckePrimePowerMertensWeight 𝔪 ψ pk *
        (heckeHarmonicSum 𝔪 ψ (N / absNorm pk.1 ^ pk.2) - heckeLCont 𝔪 ψ 1) := by
    rw [heckeLogarithmicHarmonicSum_eq_hyperbola, heckePrimePowerMertensSum,
      mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have hterm (pk : Ideal (𝓞 K) × ℕ) (hpk : pk ∈ primePowersLe K N) :
      ‖heckePrimePowerMertensWeight 𝔪 ψ pk *
        (heckeHarmonicSum 𝔪 ψ (N / absNorm pk.1 ^ pk.2) - heckeLCont 𝔪 ψ 1)‖ ≤
      (C * (N : ℝ) ^ (-δ)) * (Real.log (absNorm pk.1) *
        ((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-(1 - δ))) := by
    let q := absNorm pk.1 ^ pk.2
    have hq : 1 ≤ q := (mem_Icc.mp (mem_Icc_absNorm_pow hpk)).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hfloor := RHTower.Mertens.cast_div_lt N q hq
    have hr : (((N / q : ℕ) : ℝ) + 1) ^ (-δ) ≤ ((N : ℝ) / q) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hx hq0) hfloor.le (by linarith)
    have ht : ‖heckeHarmonicSum 𝔪 ψ (N / q) - heckeLCont 𝔪 ψ 1‖ ≤
        C * ((N : ℝ) / q) ^ (-δ) := by
      rw [norm_sub_rev]
      exact (htail _).trans (mul_le_mul_of_nonneg_left hr hC)
    rw [norm_mul]
    calc
      _ ≤ (Real.log (absNorm pk.1) / q) * (C * ((N : ℝ) / q) ^ (-δ)) :=
        mul_le_mul (norm_heckePrimePowerMertensWeight_le 𝔪 ψ pk) ht (norm_nonneg _)
          (div_nonneg (log_absNorm_nonneg _) hq0.le)
      _ = _ := by
        change (Real.log (absNorm pk.1) / q) * (C * ((N : ℝ) / q) ^ (-δ)) =
          (C * (N : ℝ) ^ (-δ)) * (Real.log (absNorm pk.1) * (q : ℝ) ^ (-(1 - δ)))
        rw [Real.div_rpow hx.le hq0.le, Real.rpow_neg hq0.le, div_inv_eq_mul,
          show -(1 - δ) = δ - 1 by ring, Real.rpow_sub_one hq0.ne']
        ring
  rw [heq]
  calc
    _ ≤ ∑ pk ∈ primePowersLe K N,
        ‖heckePrimePowerMertensWeight 𝔪 ψ pk *
          (heckeHarmonicSum 𝔪 ψ (N / absNorm pk.1 ^ pk.2) - heckeLCont 𝔪 ψ 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ pk ∈ primePowersLe K N, (C * (N : ℝ) ^ (-δ)) *
        (Real.log (absNorm pk.1) * ((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-(1 - δ))) :=
      sum_le_sum hterm
    _ = (C * (N : ℝ) ^ (-δ)) * ∑ pk ∈ primePowersLe K N,
        Real.log (absNorm pk.1) * ((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-(1 - δ)) := by
      rw [mul_sum]
    _ ≤ (C * (N : ℝ) ^ (-δ)) * (D * (N : ℝ) ^ δ) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.rpow_nonneg hx.le _))
      simpa only [sub_sub_cancel] using hprime N hN
    _ = C * D := by
      calc
        _ = (C * D) * ((N : ℝ) ^ (-δ) * (N : ℝ) ^ δ) := by ring
        _ = C * D := by rw [← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, mul_one]

/-- Every nontrivial ray class character has a bounded prime-power Mertens sum. -/
theorem exists_norm_heckePrimePowerMertensSum_le {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    ∃ B : ℝ, ∀ N : ℕ, ‖heckePrimePowerMertensSum 𝔪 ψ N‖ ≤ B := by
  obtain ⟨T, hT⟩ := exists_norm_heckeLogarithmicHarmonicSum_le 𝔪 hψ
  obtain ⟨E, hE⟩ := exists_norm_heckeMertens_hyperbola_error_le 𝔪 hψ
  have hL : 0 < ‖heckeLCont 𝔪 ψ 1‖ := norm_pos_iff.mpr (heckeLCont_one_ne_zero 𝔪 hψ)
  refine ⟨max 0 ((T + E) / ‖heckeLCont 𝔪 ψ 1‖), fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [heckePrimePowerMertensSum, primePowersLe]
  · apply le_trans _ (le_max_right _ _)
    rw [le_div_iff₀ hL, mul_comm, ← norm_mul]
    have heq : heckeLCont 𝔪 ψ 1 * heckePrimePowerMertensSum 𝔪 ψ N =
        heckeLogarithmicHarmonicSum 𝔪 ψ N -
          (heckeLogarithmicHarmonicSum 𝔪 ψ N -
            heckeLCont 𝔪 ψ 1 * heckePrimePowerMertensSum 𝔪 ψ N) := by ring
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (hT N) (hE N hN))



/-- Prime-power mass deleted by the finite modulus. -/
def heckeDeletedPrimePowerMass (N : ℕ) : ℝ :=
  ∑ pk ∈ primePowersLe K N,
    if pk.1 ∣ 𝔪.fin then Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ) else 0

theorem heckeDeletedPrimePowerMass_nonneg (N : ℕ) : 0 ≤ heckeDeletedPrimePowerMass 𝔪 N := by
  apply sum_nonneg
  intro pk _
  split_ifs
  · exact div_nonneg (log_absNorm_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

/-- The trivial character removes exactly the prime powers supported on the modulus. -/
theorem heckePrimePowerMertensSum_one_eq (N : ℕ) :
    heckePrimePowerMertensSum 𝔪 1 N =
      ((primeMertens K N - heckeDeletedPrimePowerMass 𝔪 N : ℝ) : ℂ) := by
  rw [heckePrimePowerMertensSum, primeMertens, heckeDeletedPrimePowerMass,
    ← sum_sub_distrib, Complex.ofReal_sum]
  refine sum_congr rfl fun pk hpk => ?_
  obtain ⟨hP, hP0, hk, _⟩ := mem_primePowersLe.mp hpk
  have hv : heckeValue 𝔪 1 pk.1 = if pk.1 ∣ 𝔪.fin then 0 else 1 :=
    heckeValue_one_prime 𝔪 ⟨pk.1, hP, hP0⟩
  unfold heckePrimePowerMertensWeight
  rw [hv]
  by_cases hd : pk.1 ∣ 𝔪.fin
  · simp [hd, Nat.ne_of_gt hk]
  · simp [hd]

private theorem sum_prime_power_harmonic_le_two {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (N : ℕ) :
    ∑ k ∈ Icc 1 N, Real.log (absNorm P) / (absNorm P ^ k : ℕ) ≤
      2 * Real.log (absNorm P) := by
  have h2 : (2 : ℝ) ≤ absNorm P := by exact_mod_cast two_le_absNorm_of_isPrime hP hP0
  have hlog : 0 ≤ Real.log (absNorm P) := log_absNorm_nonneg _
  have hratio : (absNorm P : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hgeom : ∑ k ∈ Icc 1 N, (1 / 2 : ℝ) ^ k ≤ 2 := by
    calc
      _ ≤ ∑ k ∈ range (N + 1), (1 / 2 : ℝ) ^ k :=
        sum_le_sum_of_subset_of_nonneg
          (fun k hk => mem_range.mpr (by have := mem_Icc.mp hk; omega))
          (fun k _ _ => pow_nonneg (by norm_num) _)
      _ ≤ 2 := by
        convert HTGeometry.geom_sum_range_le (x := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num) (N + 1) using 1
        norm_num
  calc
    _ ≤ ∑ k ∈ Icc 1 N, Real.log (absNorm P) * (1 / 2 : ℝ) ^ k := by
      refine sum_le_sum fun k _ => ?_
      rw [Nat.cast_pow, div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg _)) hratio _) hlog
    _ = Real.log (absNorm P) * ∑ k ∈ Icc 1 N, (1 / 2 : ℝ) ^ k := by rw [mul_sum]
    _ ≤ Real.log (absNorm P) * 2 := mul_le_mul_of_nonneg_left hgeom hlog
    _ = _ := mul_comm _ _

/-- Finitely many modulus primes contribute uniformly bounded geometric tails. -/
theorem exists_heckeDeletedPrimePowerMass_le :
    ∃ B : ℝ, ∀ N : ℕ, heckeDeletedPrimePowerMass 𝔪 N ≤ B := by
  let S := (idealsLe K (absNorm 𝔪.fin)).filter (fun P => P.IsPrime)
  refine ⟨2 * ∑ P ∈ S, Real.log (absNorm P), fun N => ?_⟩
  have hsub : (primePowersLe K N).filter (fun pk => pk.1 ∣ 𝔪.fin) ⊆ S ×ˢ Icc 1 N := by
    intro pk hpk
    obtain ⟨hpkin, hd⟩ := mem_filter.mp hpk
    obtain ⟨hp, hp0, _, _⟩ := mem_primePowersLe.mp hpkin
    have hk : pk.2 ∈ Icc 1 N := (mem_product.mp (mem_filter.mp hpkin).1).2
    have hnorm : absNorm pk.1 ≤ absNorm 𝔪.fin :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h => 𝔪.fin_ne_bot (absNorm_eq_zero_iff.mp h)))
        (absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd))
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_idealsLe.mpr ⟨hp0, hnorm⟩, hp⟩, hk⟩
  rw [heckeDeletedPrimePowerMass, ← sum_filter]
  calc
    _ ≤ ∑ pk ∈ S ×ˢ Icc 1 N, Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ) :=
      sum_le_sum_of_subset_of_nonneg hsub
        (fun pk _ _ => div_nonneg (log_absNorm_nonneg _) (Nat.cast_nonneg _))
    _ = ∑ P ∈ S, ∑ k ∈ Icc 1 N, Real.log (absNorm P) / (absNorm P ^ k : ℕ) := by
      rw [sum_product]
    _ ≤ ∑ P ∈ S, 2 * Real.log (absNorm P) := by
      refine sum_le_sum fun P hP => ?_
      obtain ⟨hPI, hp⟩ := mem_filter.mp hP
      exact sum_prime_power_harmonic_le_two hp (mem_idealsLe.mp hPI).1 N
    _ = _ := by rw [mul_sum]

/-- The trivial Hecke character has prime-power Mertens sum `log N + O(1)`. -/
theorem exists_norm_heckePrimePowerMertensSum_one_sub_log_le :
    ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      ‖heckePrimePowerMertensSum 𝔪 1 N - (Real.log N : ℂ)‖ ≤ B := by
  obtain ⟨C, hC⟩ := exists_abs_primeMertens_sub_log_le (K := K)
  obtain ⟨D, hD⟩ := exists_heckeDeletedPrimePowerMass_le 𝔪
  refine ⟨C + D, fun N hN => ?_⟩
  rw [heckePrimePowerMertensSum_one_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have heq : primeMertens K N - heckeDeletedPrimePowerMass 𝔪 N - Real.log N =
      (primeMertens K N - Real.log N) - heckeDeletedPrimePowerMass 𝔪 N := by ring
  rw [heq]
  refine (abs_sub _ _).trans (add_le_add (hC N hN) ?_)
  rw [abs_of_nonneg (heckeDeletedPrimePowerMass_nonneg 𝔪 N)]
  exact hD N

/-- The Mertens sum over prime ideals themselves. -/
def heckePrimeMertensSum (ψ : HeckeCharacter 𝔪) (N : ℕ) : ℂ :=
  ∑ P ∈ (idealsLe K N).filter (fun P => P.IsPrime),
    heckeValue 𝔪 ψ P * ((Real.log (absNorm P) / absNorm P : ℝ) : ℂ)

theorem heckePrimeMertensSum_eq_filter (ψ : HeckeCharacter 𝔪) (N : ℕ) :
    heckePrimeMertensSum 𝔪 ψ N =
      ∑ pk ∈ (primePowersLe K N).filter (fun pk => pk.2 = 1),
        heckePrimePowerMertensWeight 𝔪 ψ pk := by
  unfold heckePrimeMertensSum
  refine sum_bij (fun P _ => (P, 1)) (fun P hP => ?_)
    (fun P _ Q _ h => congrArg Prod.fst h) (fun pk hpk => ?_) (fun P _ => ?_)
  · obtain ⟨hI, hp⟩ := mem_filter.mp hP
    obtain ⟨h0, hN⟩ := mem_idealsLe.mp hI
    exact mem_filter.mpr ⟨mem_primePowersLe.mpr ⟨hp, h0, le_rfl, by simpa using hN⟩, rfl⟩
  · obtain ⟨hpk, hk⟩ := mem_filter.mp hpk
    obtain ⟨hp, h0, _, hN⟩ := mem_primePowersLe.mp hpk
    refine ⟨pk.1, mem_filter.mpr ⟨mem_idealsLe.mpr ⟨h0, ?_⟩, hp⟩, ?_⟩
    · simpa only [hk, pow_one] using hN
    · exact Prod.ext rfl hk.symm
  · simp only [heckePrimePowerMertensWeight, pow_one]

/-- The composite-norm part is exactly the already bounded degree-one remainder. -/
theorem sum_compositeNorm_primePowerMass_eq (N : ℕ) :
    ∑ pk ∈ (primePowersLe K N).filter (fun pk => ¬ (absNorm pk.1 ^ pk.2).Prime),
      Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ) =
        primeMertens K N - degreeOneMertens K N := by
  have hmaps : ∀ pk ∈ primePowersLe K N, absNorm pk.1 ^ pk.2 ∈ Icc 1 N :=
    fun _ hpk => mem_Icc_absNorm_pow hpk
  have heq : (∑ pk ∈ (primePowersLe K N).filter (fun pk => ¬ (absNorm pk.1 ^ pk.2).Prime),
      Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ)) =
      ∑ q ∈ (Icc 1 N).filter (fun q => ¬ q.Prime), fiberMertens K N q := by
    rw [sum_filter, ← sum_fiberwise_of_maps_to hmaps, sum_filter]
    refine sum_congr rfl fun q _ => ?_
    by_cases hq : q.Prime
    · rw [if_neg (not_not_intro hq)]
      refine sum_eq_zero fun pk hpk => ?_
      rw [(mem_filter.mp hpk).2, if_neg (not_not_intro hq)]
    · rw [if_pos hq, fiberMertens]
      refine sum_congr rfl fun pk hpk => ?_
      rw [(mem_filter.mp hpk).2, if_pos hq]
  rw [heq]
  have hsplit : primeMertens K N = degreeOneMertens K N +
      ∑ q ∈ (Icc 1 N).filter (fun q => ¬ q.Prime), fiberMertens K N q := by
    rw [primeMertens_eq_sum_fiberMertens,
      ← sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime, degreeOneMertens]
    congr 1
    refine sum_congr rfl fun q hq => ?_
    exact fiberMertens_prime (mem_filter.mp hq).2 (mem_Icc.mp (mem_filter.mp hq).1).2
  rw [hsplit, add_sub_cancel_left]

/-- Higher prime powers have uniformly bounded total mass, even after twisting. -/
theorem norm_heckePrimePowerMertensSum_sub_prime_le (ψ : HeckeCharacter 𝔪) (N : ℕ) :
    ‖heckePrimePowerMertensSum 𝔪 ψ N - heckePrimeMertensSum 𝔪 ψ N‖ ≤
      (finrank ℤ (𝓞 K) : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail) := by
  rw [heckePrimeMertensSum_eq_filter, heckePrimePowerMertensSum,
    ← sum_filter_add_sum_filter_not (primePowersLe K N) (fun pk => pk.2 = 1),
    add_sub_cancel_left]
  have hsub : (primePowersLe K N).filter (fun pk => pk.2 ≠ 1) ⊆
      (primePowersLe K N).filter (fun pk => ¬ (absNorm pk.1 ^ pk.2).Prime) := by
    intro pk hpk
    obtain ⟨hpk, hk⟩ := mem_filter.mp hpk
    refine mem_filter.mpr ⟨hpk, fun hp => hk ?_⟩
    exact (hp.pow_eq_iff.mp rfl).2
  calc
    _ ≤ ∑ pk ∈ (primePowersLe K N).filter (fun pk => pk.2 ≠ 1),
        ‖heckePrimePowerMertensWeight 𝔪 ψ pk‖ := norm_sum_le _ _
    _ ≤ ∑ pk ∈ (primePowersLe K N).filter (fun pk => pk.2 ≠ 1),
        Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ) :=
      sum_le_sum fun pk _ => norm_heckePrimePowerMertensWeight_le 𝔪 ψ pk
    _ ≤ ∑ pk ∈ (primePowersLe K N).filter (fun pk => ¬ (absNorm pk.1 ^ pk.2).Prime),
        Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ) :=
      sum_le_sum_of_subset_of_nonneg hsub
        (fun pk _ _ => div_nonneg (log_absNorm_nonneg _) (Nat.cast_nonneg _))
    _ = primeMertens K N - degreeOneMertens K N := sum_compositeNorm_primePowerMass_eq N
    _ ≤ _ := (primeMertens_sub_degreeOneMertens_le N).2

/-- Prime-ideal Mertens sums are bounded for every nontrivial ray class character. -/
theorem exists_norm_heckePrimeMertensSum_le {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    ∃ B : ℝ, ∀ N : ℕ, ‖heckePrimeMertensSum 𝔪 ψ N‖ ≤ B := by
  obtain ⟨C, hC⟩ := exists_norm_heckePrimePowerMertensSum_le 𝔪 hψ
  refine ⟨C + (finrank ℤ (𝓞 K) : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail), fun N => ?_⟩
  have heq : heckePrimeMertensSum 𝔪 ψ N = heckePrimePowerMertensSum 𝔪 ψ N -
      (heckePrimePowerMertensSum 𝔪 ψ N - heckePrimeMertensSum 𝔪 ψ N) := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans
    (add_le_add (hC N) (norm_heckePrimePowerMertensSum_sub_prime_le 𝔪 ψ N))

/-- The prime-ideal sum for the trivial character is `log N + O(1)`. -/
theorem exists_norm_heckePrimeMertensSum_one_sub_log_le :
    ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N → ‖heckePrimeMertensSum 𝔪 1 N - (Real.log N : ℂ)‖ ≤ B := by
  obtain ⟨C, hC⟩ := exists_norm_heckePrimePowerMertensSum_one_sub_log_le 𝔪
  refine ⟨C + (finrank ℤ (𝓞 K) : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail), fun N hN => ?_⟩
  have heq : heckePrimeMertensSum 𝔪 1 N - (Real.log N : ℂ) =
      (heckePrimePowerMertensSum 𝔪 1 N - (Real.log N : ℂ)) -
        (heckePrimePowerMertensSum 𝔪 1 N - heckePrimeMertensSum 𝔪 1 N) := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans
    (add_le_add (hC N hN) (norm_heckePrimePowerMertensSum_sub_prime_le 𝔪 1 N))

end GaloisForLFunctions.HeckeLFunctions

