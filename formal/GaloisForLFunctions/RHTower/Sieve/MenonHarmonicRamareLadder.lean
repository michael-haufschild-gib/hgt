import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSplitOn
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCofactorError

/-!
# Menon's harmonic Ramaré geometric ladder

The final Ramaré prime range is partitioned into multiplicative blocks.  Each block is replaced by
the product of its harmonic prime polynomial and one common harmonic cofactor polynomial.  The
replacement error retains the square of the reciprocal prime mass and the reciprocal square of the
cofactor endpoint.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The common cofactor interval for one harmonic geometric prime block. -/
def harmonicGeomCofactorBlock (A₀ B₀ : ℕ) (Q eta : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Icc
    ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊
    ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊

/-- The exact common-support replacement budget for one harmonic geometric block. -/
def harmonicCofactorSupportError (A₀ B₀ : ℕ) (Q eta W : ℝ) (j : ℕ) : ℝ :=
  2 * (5 * Real.pi / 2 * W +
      5 * Real.exp 1 / 2 * (⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊ : ℝ)) *
    ((((A₀ : ℝ) + (B₀ : ℝ)) * eta / (Q * (1 + eta) ^ j) + 4 +
        ((B₀ : ℝ) / (Q * (1 + eta) ^ j) ^ 2 + 1)) *
      (1 / (⌈(A₀ : ℝ) /
        ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2)

/-- The harmonic Ramaré bilinear form over a geometric ladder.  Splitting into `L` prime blocks
costs exactly `L`. -/
theorem integral_normSq_harmonicRamareBilinear_le_geomLadder
    {P s : Finset ℕ} {W Q r : ℝ}
    (hQ : 0 < Q) (hr : 1 ≤ r) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * r ^ L) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P s w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          ∫ w in Set.Icc (-W) W,
            ‖harmonicRamareBlock P s (geomBlock P Q r j) w‖ ^ 2 := by
  classical
  have h := integral_normSq_harmonicRamareBilinear_le_blocks
    (P := P) (s := s) (W := W) (Finset.range L) (geomBlock P Q r)
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q r hL hP)
  rwa [Finset.card_range] at h

/-- One harmonic geometric block is a genuine prime/cofactor product plus the exact moving-support
error.  The error is weighted by `harmonicPrimeMass²`, not block cardinality. -/
theorem integral_normSq_harmonicRamareBlock_geom_le
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) /
      ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicRamareBlock P (Finset.Icc A₀ B₀)
        (geomBlock P Q (1 + eta) j) w‖ ^ 2)
      ≤ 2 * (∫ w in Set.Icc (-W) W,
          ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
            logPoly (harmonicRamareCofactorCoeff P)
              (harmonicGeomCofactorBlock A₀ B₀ Q eta j) w‖ ^ 2)
        + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ 2 *
            harmonicCofactorSupportError A₀ B₀ Q eta W j := by
  classical
  let B : Finset ℕ := geomBlock P Q (1 + eta) j
  let Qj : ℝ := Q * (1 + eta) ^ j
  let C : Finset ℕ := harmonicGeomCofactorBlock A₀ B₀ Q eta j
  let E : ℝ := harmonicCofactorSupportError A₀ B₀ Q eta W j
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  have hQj : 0 < Qj := by
    dsimp only [Qj]
    have : 0 < 1 + eta := by linarith
    positivity
  have hdisc : ∀ p ∈ B,
      (∫ w in Set.Icc (-W) W,
        ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
          logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ 2) ≤ E := by
    intro p hp
    have hpB := Finset.mem_filter.1 hp
    have hp0 := (hBprime p hp).pos
    have hphi : (p : ℝ) ≤ Qj * (1 + eta) := by
      calc
        (p : ℝ) ≤ Q * (1 + eta) ^ (j + 1) := hpB.2.2
        _ = Qj * (1 + eta) := by rw [pow_succ]; dsimp only [Qj]; ring
    have hbase := integral_Icc_normSq_harmonicRamareCofactor_sub_common_le
      (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Qj) (eta := eta) (W := W) (p := p)
      hA₀ hQj heta hW hp0 hpB.2.1 hphi hleft
    simpa [Qj, C, E, harmonicGeomCofactorBlock, harmonicCofactorSupportError] using hbase
  have hsum :
      (∑ p ∈ B, (1 / (p : ℝ)) *
        (∫ w in Set.Icc (-W) W,
          ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
            logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ 2))
        ≤ harmonicPrimeMass B * E := by
    calc
      (∑ p ∈ B, (1 / (p : ℝ)) *
          (∫ w in Set.Icc (-W) W,
            ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
              logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ 2))
          ≤ ∑ p ∈ B, (1 / (p : ℝ)) * E := by
            refine Finset.sum_le_sum fun p hp => ?_
            exact mul_le_mul_of_nonneg_left (hdisc p hp) (by positivity)
      _ = harmonicPrimeMass B * E := by
        rw [harmonicPrimeMass, Finset.sum_mul]
  have hbase := setIntegral_normSq_harmonicRamareBlock_le_product
    (P := P) (s := Finset.Icc A₀ B₀) (B := B) (W := W)
      hBprime C measurableSet_Icc (fun _ hw => hw)
  have hmass0 : 0 ≤ harmonicPrimeMass B := by
    rw [harmonicPrimeMass]
    positivity
  have hsecond :
      2 * harmonicPrimeMass B *
          (∑ p ∈ B, (1 / (p : ℝ)) *
            (∫ w in Set.Icc (-W) W,
              ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
                logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ 2))
        ≤ 2 * harmonicPrimeMass B ^ 2 * E := by
    calc
      2 * harmonicPrimeMass B *
          (∑ p ∈ B, (1 / (p : ℝ)) *
            (∫ w in Set.Icc (-W) W,
              ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
                logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ 2))
          ≤ 2 * harmonicPrimeMass B * (harmonicPrimeMass B * E) :=
            mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hmass0)
      _ = 2 * harmonicPrimeMass B ^ 2 * E := by ring
  dsimp only [B, C, E] at hbase hsecond ⊢
  exact hbase.trans (add_le_add le_rfl hsecond)

end

end RHTower.Sieve
