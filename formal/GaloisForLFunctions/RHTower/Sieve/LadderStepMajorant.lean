import GaloisForLFunctions.RHTower.Sieve.BlockMassCompare
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedAnnulusBound

/-!
# The optimal Cauchy--Schwarz weight, made explicit

The weight of the harmonic split is the reciprocal of `V_j √T_j`, where `T_j` is the mean value
factor of the `j`-th cofactor block.  Below the Gallagher cut the mean value factor is dominated by
the square of the cofactor block's length, so the weight is explicit, and the resulting single sum
is the ladder's counting sum against the cofactor lengths — the harmonic mass of the designated
primes.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The explicit majorant for the square root of a ladder step's mean value factor. -/
def stepMVTMajorant (B₀ : ℕ) (Q η : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)

theorem stepMVTMajorant_pos {B₀ : ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    0 < stepMVTMajorant B₀ Q η j := by
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hs : (0 : ℝ) < Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hB : (0 : ℝ) ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) := div_nonneg (Nat.cast_nonneg _) hbase.le
  have : (0 : ℝ) < (B₀ : ℝ) / (Q * (1 + η) ^ j) + 1 := by linarith
  exact mul_pos hs this

/-- **Below the Gallagher cut the mean value factor is dominated by the cofactor length squared.** -/
theorem ladderStepMVT_le_sq {B₀ : ℕ} {Q η G : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ)
    (hG : G ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j)) :
    ladderStepMVT B₀ Q η G j ≤ (stepMVTMajorant B₀ Q η j) ^ 2 := by
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  set N : ℝ := (B₀ : ℝ) / (Q * (1 + η) ^ j) with hN
  have hN0 : (0 : ℝ) ≤ N := div_nonneg (Nat.cast_nonneg _) hbase.le
  have hfl : ((⌊N⌋₊ : ℕ) : ℝ) ≤ N := Nat.floor_le hN0
  have hCpos : (0 : ℝ) ≤ 5 * Real.pi / 2 + 5 * Real.exp 1 / 2 := by positivity
  have hsq : (stepMVTMajorant B₀ Q η j) ^ 2
      = (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) * (N + 1) ^ 2 := by
    rw [stepMVTMajorant, ← hN, mul_pow, Real.sq_sqrt hCpos]
  rw [ladderStepMVT, ← hN, hsq]
  have hstep : 5 * Real.pi / 2 * G + 5 * Real.exp 1 / 2 * ((⌊N⌋₊ : ℕ) : ℝ)
      ≤ (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) * N := by
    have h1 : 5 * Real.pi / 2 * G ≤ 5 * Real.pi / 2 * N :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    have h2 : 5 * Real.exp 1 / 2 * ((⌊N⌋₊ : ℕ) : ℝ) ≤ 5 * Real.exp 1 / 2 * N :=
      mul_le_mul_of_nonneg_left hfl (by positivity)
    nlinarith [h1, h2]
  have hN1 : (0 : ℝ) ≤ N + 1 := by linarith
  nlinarith [hstep, hN1, hN0, hCpos]

/-- The ladder blocks partition the designated primes, so their sizes add up. -/
theorem sum_card_geomBlock_eq {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ}
    (hL : 1 ≤ L) (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) :
    (∑ j ∈ Finset.range L, ((geomBlock P Q (1 + η) j).card : ℝ)) = (P.card : ℝ) := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hcard : P.card
      = ((Finset.range L).biUnion (geomBlock P Q (1 + η))).card := by
    rw [geomBlock_biUnion_eq P Q (1 + η) hL hP]
  rw [hcard, Finset.card_biUnion (fun i hi j hj hij =>
    geomBlock_pairwiseDisjoint P hQ hr1 L (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) hij)]
  push_cast
  rfl

/-- **The single sum of the optimal weight is the harmonic mass.** -/
theorem sum_stepMajorant_le {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ}
    (hL : 1 ≤ L) (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) {B₀ : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (V : ℕ → ℝ)
    (hVj : ∀ j ∈ Finset.range L, V j ≤ ε * ((geomBlock P Q (1 + η) j).card : ℝ)) :
    (∑ j ∈ Finset.range L, V j * stepMVTMajorant B₀ Q η j)
      ≤ Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) * ε
        * ((1 + η) * (B₀ : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + (P.card : ℝ)) := by
  classical
  set C : ℝ := Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) with hC
  have hC0 : (0 : ℝ) ≤ C := Real.sqrt_nonneg _
  have hstep : ∀ j ∈ Finset.range L, V j * stepMVTMajorant B₀ Q η j
      ≤ C * ε * (((geomBlock P Q (1 + η) j).card : ℝ) * ((B₀ : ℝ) / (Q * (1 + η) ^ j))
          + ((geomBlock P Q (1 + η) j).card : ℝ)) := by
    intro j hj
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    have hmaj0 : (0 : ℝ) ≤ stepMVTMajorant B₀ Q η j := (stepMVTMajorant_pos hQ hη j).le
    have h1 := mul_le_mul_of_nonneg_right (hVj j hj) hmaj0
    refine h1.trans (le_of_eq ?_)
    rw [stepMVTMajorant, ← hC]
    ring
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 hε)
  have h1 := sum_card_geomBlock_div_le (P := P) hQ hη hL hP (B := (B₀ : ℝ)) (Nat.cast_nonneg _)
  have h2 := sum_card_geomBlock_eq (P := P) hQ hη hL hP
  linarith [h1, h2]

/-- The explicit majorant for the disc contribution of one ladder step. -/
def discMajorant (P : Finset ℕ) (B₀ : ℕ) (Q η s w₀ : ℝ) (j : ℕ) : ℝ :=
  (((geomBlock P Q (1 + η) j).card : ℝ) + 1) * (s * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) + 1)
    * (Real.sqrt (2 * w₀) + 1)

theorem discMajorant_pos {P : Finset ℕ} {B₀ : ℕ} {Q η s w₀ : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (hs : 0 ≤ s) (j : ℕ) : 0 < discMajorant P B₀ Q η s w₀ j := by
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have h1 : (0 : ℝ) < ((geomBlock P Q (1 + η) j).card : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((geomBlock P Q (1 + η) j).card : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 : (0 : ℝ) < s * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) + 1 := by
    have : (0 : ℝ) ≤ s * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) :=
      mul_nonneg hs (div_nonneg (Nat.cast_nonneg _) hbase.le)
    linarith
  have h3 : (0 : ℝ) < Real.sqrt (2 * w₀) + 1 := by
    have := Real.sqrt_nonneg (2 * w₀)
    linarith
  exact mul_pos (mul_pos h1 h2) h3

/-- **The disc majorant dominates the disc contribution of a step.** -/
theorem discMajorant_sq_ge {P : Finset ℕ} {B₀ : ℕ} {Q η s w₀ : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (hs : 0 ≤ s) (hw₀ : 0 ≤ w₀) {U Vlow : ℕ → ℝ} (j : ℕ) (hU0 : 0 ≤ U j) (hVlow0 : 0 ≤ Vlow j)
    (hVlowj : Vlow j ≤ ((geomBlock P Q (1 + η) j).card : ℝ))
    (hUj : U j ≤ s * ((B₀ : ℝ) / (Q * (1 + η) ^ j))) :
    Vlow j ^ 2 * U j ^ 2 * (2 * w₀) ≤ (discMajorant P B₀ Q η s w₀ j) ^ 2 := by
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  set a : ℝ := ((geomBlock P Q (1 + η) j).card : ℝ) + 1 with ha
  set b : ℝ := s * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) + 1 with hb
  set r : ℝ := Real.sqrt (2 * w₀) + 1 with hr
  have hVa : Vlow j ≤ a := by rw [ha]; linarith [hVlowj]
  have hUb : U j ≤ b := by rw [hb]; linarith [hUj]
  have hsq : Real.sqrt (2 * w₀) ^ 2 = 2 * w₀ := Real.sq_sqrt (by linarith)
  have hwr : 2 * w₀ ≤ r ^ 2 := by
    rw [hr]
    nlinarith [Real.sqrt_nonneg (2 * w₀), hsq]
  have ha0 : (0 : ℝ) ≤ a := le_trans hVlow0 hVa
  have hb0 : (0 : ℝ) ≤ b := le_trans hU0 hUb
  have h1 : Vlow j ^ 2 ≤ a ^ 2 := by nlinarith [hVa, hVlow0]
  have h2 : U j ^ 2 ≤ b ^ 2 := by nlinarith [hUb, hU0]
  rw [discMajorant, ← ha, ← hb, ← hr, mul_pow, mul_pow]
  have hUsq0 : (0 : ℝ) ≤ U j ^ 2 := sq_nonneg _
  have hasq0 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg _
  have hbsq0 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg _
  have hstep1 : Vlow j ^ 2 * U j ^ 2 ≤ a ^ 2 * b ^ 2 := mul_le_mul h1 h2 hUsq0 hasq0
  exact mul_le_mul hstep1 hwr (by linarith) (by positivity)

/-- **The disc majorant sums to the harmonic mass times the cofactor saving.** -/
theorem sum_discMajorant_le {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ}
    (hL : 1 ≤ L) (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) {B₀ : ℕ} {s w₀ : ℝ}
    (hs : 0 ≤ s) :
    (∑ j ∈ Finset.range L, discMajorant P B₀ Q η s w₀ j)
      ≤ (Real.sqrt (2 * w₀) + 1)
        * (s * ((1 + η) * (B₀ : ℝ) * (∑ p ∈ P, 1 / (p : ℝ))) + (P.card : ℝ)
          + s * (∑ j ∈ Finset.range L, (B₀ : ℝ) / (Q * (1 + η) ^ j)) + (L : ℝ)) := by
  classical
  have hr0 : (0 : ℝ) ≤ Real.sqrt (2 * w₀) + 1 := by
    have := Real.sqrt_nonneg (2 * w₀)
    linarith
  have hexp : ∀ j ∈ Finset.range L, discMajorant P B₀ Q η s w₀ j
      = (Real.sqrt (2 * w₀) + 1)
        * (s * (((geomBlock P Q (1 + η) j).card : ℝ) * ((B₀ : ℝ) / (Q * (1 + η) ^ j)))
          + ((geomBlock P Q (1 + η) j).card : ℝ)
          + s * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) + 1) := by
    intro j _
    rw [discMajorant]
    ring
  rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hr0
  have h1 := sum_card_geomBlock_div_le (P := P) hQ hη hL hP (B := (B₀ : ℝ)) (Nat.cast_nonneg _)
  have h2 := sum_card_geomBlock_eq (P := P) hQ hη hL hP
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_range]
  have h3 := mul_le_mul_of_nonneg_left h1 hs
  linarith [h2, h3]

end

end RHTower.Sieve
