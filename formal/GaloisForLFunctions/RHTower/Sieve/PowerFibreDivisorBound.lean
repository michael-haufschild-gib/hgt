import GaloisForLFunctions.RHTower.Sieve.PrimePowerSupport
import GaloisForLFunctions.RHTower.Sieve.DivisorBound

/-!
# Power fibres of an unrestricted support

`Sieve/PrimePowerSupport` bounds the `ℓ`-fold power fibre by `ℓ^ℓ` when the coefficients are
supported on primes.  Jutila's large-values estimate needs the same for *divisor-bounded*
coefficients on the full support, where the fibre is the set of ordered `ℓ`-factorisations of the
anchored product and is therefore bounded by `d(m)^ℓ`; the divisor bound of `Sieve/DivisorBound`
turns that into `(C_ε (N^ℓ)^ε)^ℓ`, an arbitrarily small power of the length.

This is the last atom of Matomäki–Teräväinen's Lemma 4.1 that the corpus did not already own.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **An unrestricted power fibre is an ordered factorisation set.**  Each coordinate divides the
anchored product, so the fibre injects into the `ℓ`-fold product of the divisor set. -/
theorem powFibreOn_univ_card_le_divisors (N ℓ : ℕ) (j : Fin (N ^ ℓ)) :
    (powFibreOn N ℓ Finset.univ j).card ≤ (((j : ℕ) + 1).divisors.card) ^ ℓ := by
  classical
  have hprodEq : ∀ p ∈ powFibreOn N ℓ Finset.univ j,
      (∏ i : Fin ℓ, ((p i : ℕ) + 1)) = (j : ℕ) + 1 := by
    intro p hp
    rw [powFibreOn, Finset.mem_filter] at hp
    have hmem := hp.1
    rw [Finset.mem_filter] at hmem
    rw [← powIdx_val_add_one p, hmem.2]
  have hmaps : ∀ p ∈ powFibreOn N ℓ Finset.univ j,
      (fun i : Fin ℓ => (p i : ℕ) + 1) ∈ Fintype.piFinset
        (fun _ : Fin ℓ => ((j : ℕ) + 1).divisors) := by
    intro p hp
    rw [Fintype.mem_piFinset]
    intro i
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    rw [← hprodEq p hp]
    exact Finset.dvd_prod_of_mem (fun i : Fin ℓ => ((p i : ℕ) + 1)) (Finset.mem_univ i)
  have hinj : ∀ p ∈ powFibreOn N ℓ Finset.univ j, ∀ q ∈ powFibreOn N ℓ Finset.univ j,
      (fun i : Fin ℓ => (p i : ℕ) + 1) = (fun i : Fin ℓ => (q i : ℕ) + 1) → p = q := by
    intro p _ q _ hpq
    funext i
    have := congrFun hpq i
    exact Fin.ext (by omega)
  have hcard := Finset.card_le_card_of_injOn
    (f := fun p : Fin ℓ → Fin N => fun i : Fin ℓ => (p i : ℕ) + 1) hmaps
    (fun p hp q hq h => hinj p hp q hq h)
  refine le_trans hcard (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const]

/-- **The divisor-bounded power fibre estimate.** -/
theorem powFibreOn_univ_card_le_rpow {ε : ℝ} (hε : 0 < ε) (N ℓ : ℕ) (j : Fin (N ^ ℓ)) :
    ((powFibreOn N ℓ Finset.univ j).card : ℝ)
      ≤ (divisorBoundConst ε * (((N ^ ℓ : ℕ) : ℝ)) ^ ε) ^ ℓ := by
  have hstep : ((powFibreOn N ℓ Finset.univ j).card : ℝ)
      ≤ (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ)) ^ ℓ := by
    have := powFibreOn_univ_card_le_divisors N ℓ j
    exact_mod_cast this
  refine le_trans hstep ?_
  have hd := card_divisors_le_rpow (ε := ε) hε (n := (j : ℕ) + 1) (by omega)
  have hle : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (((N ^ ℓ : ℕ)) : ℝ) := by
    have : (j : ℕ) + 1 ≤ N ^ ℓ := j.isLt
    exact_mod_cast this
  have hmono : ((((j : ℕ) + 1 : ℕ)) : ℝ) ^ ε ≤ (((N ^ ℓ : ℕ)) : ℝ) ^ ε :=
    Real.rpow_le_rpow (by positivity) hle hε.le
  have hC := divisorBoundConst_pos hε
  have hchain : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ))
      ≤ divisorBoundConst ε * (((N ^ ℓ : ℕ)) : ℝ) ^ ε := by
    refine le_trans hd ?_
    exact mul_le_mul_of_nonneg_left hmono hC.le
  refine pow_le_pow_left₀ (by positivity) hchain ℓ

/-- **The `ℓ²` mass of the `ℓ`-fold convolution for divisor-bounded coefficients.** -/
theorem sum_normSq_convPow_le_divisorBounded {ε : ℝ} (hε : 0 < ε) (N ℓ : ℕ) (a : Fin N → ℂ) :
    ∑ j : Fin (N ^ ℓ), ‖convPow N ℓ a j‖ ^ 2
      ≤ (divisorBoundConst ε * (((N ^ ℓ : ℕ) : ℝ)) ^ ε) ^ ℓ
          * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ := by
  have hC := divisorBoundConst_pos hε
  refine sum_normSq_convPow_le_of_support_primePowerSupport N ℓ a Finset.univ (fun n _ => Finset.mem_univ n)
    (fun j => powFibreOn_univ_card_le_rpow hε N ℓ j) ?_
  positivity

/-- **Jutila's adapted-moment level-set bound, for divisor-bounded coefficients.**  This is the
measure-form statement Matomäki–Teräväinen's Lemma 4.1 asserts: the level set of a Dirichlet
polynomial of length `N` at height `V` has measure controlled by the `ℓ`-th moment, and the only
arithmetic input is the divisor bound. -/
theorem volume_largeValues_pow_symm_le_divisorBounded {ε : ℝ} (hε : 0 < ε) (N ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (a : Fin N → ℂ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ (2 * ℓ) * MeasureTheory.volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖}
      ≤ 2 * ((T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)))
          * ((divisorBoundConst ε * (((N ^ ℓ : ℕ) : ℝ)) ^ ε) ^ ℓ
              * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ)) := by
  have hVl : (0 : ℝ) ≤ V ^ ℓ := by positivity
  have hbase := volume_largeValues_symm_le (N ^ ℓ) (convPow N ℓ a) hT hVl
  rw [largeValues_pow_setOf_primePowerSupport N ℓ hℓ a (Set.Icc (-T) T) hV] at hbase
  have hpow : (V ^ ℓ) ^ 2 = V ^ (2 * ℓ) := by
    rw [← pow_mul, mul_comm]
  rw [hpow] at hbase
  refine le_trans hbase ?_
  have hlogNl : (0 : ℝ) ≤ Real.log ((N ^ ℓ : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ ℓ) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ ℓ := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)) := by nlinarith
  have hstep := mul_le_mul_of_nonneg_left
    (sum_normSq_convPow_le_divisorBounded hε N ℓ a) hfactor
  linarith

/-- **The level set itself, solved for the measure.**  The Jutila shape: an arbitrarily small power
of the length times the `ℓ`-th power of the coefficient energy, divided by `V^{2ℓ}`. -/
theorem volume_largeValues_le_divisorBounded {ε : ℝ} (hε : 0 < ε) (N ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (a : Fin N → ℂ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V) :
    MeasureTheory.volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖}
      ≤ 2 * ((T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)))
          * ((divisorBoundConst ε * (((N ^ ℓ : ℕ) : ℝ)) ^ ε) ^ ℓ
              * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ)) / V ^ (2 * ℓ) := by
  have hV0 : (0 : ℝ) < V ^ (2 * ℓ) := by positivity
  have hmain := volume_largeValues_pow_symm_le_divisorBounded hε N ℓ hℓ a hT hV.le
  rw [le_div_iff₀ hV0]
  linarith [hmain]

end

end RHTower.Sieve
