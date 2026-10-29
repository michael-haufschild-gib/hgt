import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesHaveEulerProducts
import GaloisForLFunctions.HeckeLFunctions.HeckeHarmonicSumsHavePowerSavingTails

/-!
# The weighted ideal hyperbola identity

Multiplication by a nonzero ideal reindexes weighted bounded ideal sums.
Together with the ideal von Mangoldt identity and exact grouping by norm,
this expresses logarithmic Hecke harmonic sums through their prime-power
Mertens weights and smaller harmonic sums.
-/

noncomputable section
open Finset NumberField Ideal
open scoped Classical

namespace GaloisForLFunctions.ArtinMertens
variable {K : Type*} [Field K] [NumberField K]

/-- Multiplication by a nonzero ideal reindexes every weighted sum of its bounded multiples. -/
theorem sum_filter_dvd_idealsLe_eq {Q : Ideal (𝓞 K)} (hQ : Q ≠ ⊥)
    (f : Ideal (𝓞 K) → ℂ) (x : ℕ) :
    ∑ I ∈ (idealsLe K x).filter (fun I => Q ∣ I), f I =
      ∑ J ∈ idealsLe K (x / absNorm Q), f (Q * J) := by
  have hNQ : 0 < absNorm Q := Nat.pos_of_ne_zero fun h => hQ (absNorm_eq_zero_iff.mp h)
  symm
  refine sum_bij (fun J _ => Q * J) (fun J hJ => ?_) (fun J₁ _ J₂ _ h => ?_)
    (fun I hI => ?_) (fun _ _ => rfl)
  · rw [mem_idealsLe] at hJ
    rw [mem_filter, mem_idealsLe, map_mul]
    refine ⟨⟨mul_ne_zero hQ hJ.1, ?_⟩, dvd_mul_right Q J⟩
    exact (Nat.le_div_iff_mul_le hNQ).mp hJ.2 |>.trans_eq' (mul_comm _ _)
  · exact mul_left_cancel₀ hQ h
  · rw [mem_filter, mem_idealsLe] at hI
    obtain ⟨⟨hI0, hIx⟩, J, rfl⟩ := hI
    refine ⟨J, ?_, rfl⟩
    rw [mem_idealsLe]
    refine ⟨fun h => hI0 (by rw [h, Ideal.mul_bot]), ?_⟩
    rw [map_mul] at hIx
    exact (Nat.le_div_iff_mul_le hNQ).mpr (by linarith [mul_comm (absNorm Q) (absNorm J)])

/-- The ideal von Mangoldt identity with an arbitrary weight, before imposing multiplicativity. -/
theorem sum_weight_mul_log_absNorm_idealsLe_eq (f : Ideal (𝓞 K) → ℂ) (x : ℕ) :
    ∑ I ∈ idealsLe K x, f I * (Real.log (absNorm I) : ℂ) =
      ∑ pk ∈ primePowersLe K x, (Real.log (absNorm pk.1) : ℂ) *
        ∑ J ∈ idealsLe K (x / absNorm pk.1 ^ pk.2), f (pk.1 ^ pk.2 * J) := by
  have hrow (I : Ideal (𝓞 K)) (hI : I ∈ idealsLe K x) :
      f I * (Real.log (absNorm I) : ℂ) =
        ∑ pk ∈ primePowersLe K x,
          if pk.1 ^ pk.2 ∣ I then (Real.log (absNorm pk.1) : ℂ) * f I else 0 := by
    rw [mem_idealsLe] at hI
    rw [← sum_primePowersLe_dvd_eq hI.1 hI.2, Complex.ofReal_sum, mul_sum]
    refine sum_congr rfl fun pk _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [sum_congr rfl hrow, sum_comm]
  refine sum_congr rfl fun pk hpk => ?_
  have hQ : pk.1 ^ pk.2 ≠ ⊥ := pow_ne_zero _ (mem_primePowersLe.mp hpk).2.1
  rw [← sum_filter, ← mul_sum, sum_filter_dvd_idealsLe_eq hQ, map_pow]

end GaloisForLFunctions.ArtinMertens

namespace GaloisForLFunctions.HeckeLFunctions
open ArtinMertens
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Grouping finite weighted ideal sums by norm is an exact partition. -/
theorem sum_idealsLe_eq_sum_norm_fibers (f : Ideal (𝓞 K) → ℂ) (N : ℕ) :
    ∑ I ∈ idealsLe K N, f I = ∑ n ∈ Icc 1 N, ∑ I ∈ idealsOfNorm K n, f I := by
  have hset : (Icc 1 N).biUnion (idealsOfNorm K) = idealsLe K N := by
    ext I
    simp only [mem_biUnion, mem_Icc, mem_idealsOfNorm, mem_idealsLe]
    constructor
    · rintro ⟨n, ⟨hn, hnN⟩, hIn⟩
      refine ⟨fun h => ?_, hIn.trans_le hnN⟩
      rw [h, absNorm_bot] at hIn
      omega
    · rintro ⟨hI, hIN⟩
      exact ⟨absNorm I, ⟨Nat.one_le_iff_ne_zero.mpr (fun h => hI (absNorm_eq_zero_iff.mp h)),
        hIN⟩, rfl⟩
  have hdisj : ((Icc 1 N : Finset ℕ) : Set ℕ).PairwiseDisjoint (idealsOfNorm K) := by
    intro n _ k _ hnk
    refine disjoint_left.mpr fun I hIn hIk => hnk ?_
    exact (mem_idealsOfNorm.mp hIn).symm.trans (mem_idealsOfNorm.mp hIk)
  rw [← sum_biUnion hdisj, hset]

/-- Any norm weight can be attached before or after collecting Hecke coefficients. -/
theorem sum_heckeCoeff_mul_eq_sum_idealsLe (ψ : HeckeCharacter 𝔪) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, heckeCoeff 𝔪 ψ n * w n =
      ∑ I ∈ idealsLe K N, heckeValue 𝔪 ψ I * w (absNorm I) := by
  rw [sum_idealsLe_eq_sum_norm_fibers]
  simp only [heckeCoeff, sum_mul]
  refine sum_congr rfl fun n _ => sum_congr rfl fun I hI => ?_
  rw [mem_idealsOfNorm.mp hI]

/-- Hecke harmonic ideal weights are multiplicative, including noncoprime zeros. -/
theorem heckeHarmonicWeight_mul (ψ : HeckeCharacter 𝔪) (I J : Ideal (𝓞 K)) :
    heckeValue 𝔪 ψ (I * J) / (absNorm (I * J) : ℂ) =
      (heckeValue 𝔪 ψ I / (absNorm I : ℂ)) *
        (heckeValue 𝔪 ψ J / (absNorm J : ℂ)) := by
  rw [heckeValue_mul, map_mul, Nat.cast_mul]
  exact mul_div_mul_comm _ _ _ _

theorem heckeValue_pow (ψ : HeckeCharacter 𝔪) (I : Ideal (𝓞 K)) (k : ℕ) :
    heckeValue 𝔪 ψ (I ^ k) = heckeValue 𝔪 ψ I ^ k := by
  induction k with
  | zero => simp only [pow_zero, heckeValue_one]
  | succ k ih => rw [pow_succ, heckeValue_mul, ih, pow_succ]

theorem heckeHarmonicSum_eq_sum_idealsLe (ψ : HeckeCharacter 𝔪) (N : ℕ) :
    heckeHarmonicSum 𝔪 ψ N =
      ∑ I ∈ idealsLe K N, heckeValue 𝔪 ψ I / (absNorm I : ℂ) := by
  simp only [heckeHarmonicSum, div_eq_mul_inv]
  exact sum_heckeCoeff_mul_eq_sum_idealsLe 𝔪 ψ (fun n => (n : ℂ)⁻¹) N

theorem heckeLogarithmicHarmonicSum_eq_sum_idealsLe (ψ : HeckeCharacter 𝔪) (N : ℕ) :
    heckeLogarithmicHarmonicSum 𝔪 ψ N =
      ∑ I ∈ idealsLe K N, heckeValue 𝔪 ψ I / (absNorm I : ℂ) * (Real.log (absNorm I) : ℂ) := by
  simpa only [heckeLogarithmicHarmonicSum, div_eq_mul_inv, mul_assoc] using
    sum_heckeCoeff_mul_eq_sum_idealsLe 𝔪 ψ (fun n => (n : ℂ)⁻¹ * (Real.log n : ℂ)) N

/-- The actual character-weighted logarithmic mass of a prime power, divided by its norm. -/
def heckePrimePowerMertensWeight (ψ : HeckeCharacter 𝔪) (pk : Ideal (𝓞 K) × ℕ) : ℂ :=
  heckeValue 𝔪 ψ pk.1 ^ pk.2 *
    ((Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ) : ℝ) : ℂ)

/-- The finite prime-power Mertens sum for a ray class character. -/
def heckePrimePowerMertensSum (ψ : HeckeCharacter 𝔪) (N : ℕ) : ℂ :=
  ∑ pk ∈ primePowersLe K N, heckePrimePowerMertensWeight 𝔪 ψ pk

/-- Multiplicativity and the ideal von Mangoldt identity give the exact harmonic hyperbola formula. -/
theorem heckeLogarithmicHarmonicSum_eq_hyperbola (ψ : HeckeCharacter 𝔪) (N : ℕ) :
    heckeLogarithmicHarmonicSum 𝔪 ψ N =
      ∑ pk ∈ primePowersLe K N, heckePrimePowerMertensWeight 𝔪 ψ pk *
        heckeHarmonicSum 𝔪 ψ (N / absNorm pk.1 ^ pk.2) := by
  rw [heckeLogarithmicHarmonicSum_eq_sum_idealsLe, sum_weight_mul_log_absNorm_idealsLe_eq]
  refine sum_congr rfl fun pk _ => ?_
  simp_rw [heckeHarmonicWeight_mul]
  rw [← mul_sum, ← heckeHarmonicSum_eq_sum_idealsLe, heckeValue_pow, map_pow]
  unfold heckePrimePowerMertensWeight
  push_cast
  ring

theorem norm_heckePrimePowerMertensWeight_le (ψ : HeckeCharacter 𝔪) (pk : Ideal (𝓞 K) × ℕ) :
    ‖heckePrimePowerMertensWeight 𝔪 ψ pk‖ ≤
      Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ) := by
  rw [heckePrimePowerMertensWeight, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (log_absNorm_nonneg _) (Nat.cast_nonneg _))]
  exact mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ _))

end GaloisForLFunctions.HeckeLFunctions

