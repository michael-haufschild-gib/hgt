import GaloisForLFunctions.RHTower.Sieve.RamareCofactorBlock
import GaloisForLFunctions.RHTower.Sieve.PrimePhaseShift

/-!
# Splitting the Ramaré bilinear form over a ladder of prime ranges

The Ramaré coefficients depend on the whole designated set `P`, but not on the individual prime, so
the outer sum splits additively over any partition of `P`.  Cauchy–Schwarz over the blocks then
bounds the mean square of the bilinear form by the number of blocks times the sum of the blocks'
mean squares.

This is the shape the ladder `P^{(0)},…,P^{(L)}` is used in: each block is narrow enough for its
cofactor polynomials to be comparable, and the price of assembling them is the block count.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- One block of the Ramaré bilinear form. -/
def ramareBlock (P : Finset ℕ) (M : ℕ) (B : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ p ∈ B, moebiusPhase w p * ramareCofactorPoly P M p w

theorem continuous_ramareBlock (P : Finset ℕ) (M : ℕ) (B : Finset ℕ) :
    Continuous fun w : ℝ => ramareBlock P M B w := by
  refine continuous_finsetSum B fun p _ => ?_
  exact (continuous_moebiusPhase p).mul (continuous_ramareCofactorPoly P M p)

/-- **The bilinear form splits over a partition of the designated primes.** -/
theorem ramareBilinear_eq_sum_blocks {P : Finset ℕ} (M : ℕ) (w : ℝ) {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (B : ι → Finset ℕ) (hdisj : (I : Set ι).PairwiseDisjoint B)
    (hcover : I.biUnion B = P) :
    ramareBilinear P M w = ∑ i ∈ I, ramareBlock P M (B i) w := by
  classical
  simp only [ramareBlock]
  rw [ramareBilinear_eq_sum, ← hcover, Finset.sum_biUnion hdisj]

/-- **The mean square of the bilinear form, over a partition.**  Cauchy--Schwarz over the blocks
costs exactly the block count. -/
theorem integral_normSq_ramareBilinear_le_blocks {P : Finset ℕ} (M : ℕ) {W : ℝ}
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (I.card : ℝ) * ∑ i ∈ I, ∫ w in Set.Icc (-W) W, ‖ramareBlock P M (B i) w‖ ^ 2 := by
  classical
  have hpt : ∀ w : ℝ, ‖ramareBilinear P M w‖ ^ 2
      ≤ (I.card : ℝ) * ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ ^ 2 := by
    intro w
    rw [ramareBilinear_eq_sum_blocks M w I B hdisj hcover]
    have h1 : ‖∑ i ∈ I, ramareBlock P M (B i) w‖ ≤ ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ :=
      norm_sum_le _ _
    have h2 : (∑ i ∈ I, ‖ramareBlock P M (B i) w‖) ^ 2
        ≤ (I.card : ℝ) * ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖∑ i ∈ I, ramareBlock P M (B i) w‖ ^ 2
        ≤ (∑ i ∈ I, ‖ramareBlock P M (B i) w‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith
  have hcont : Continuous fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2 :=
    ((continuous_ramareBilinear P M).norm).pow 2
  have hcontB : ∀ i : ι, Continuous fun w : ℝ => ‖ramareBlock P M (B i) w‖ ^ 2 := fun i =>
    ((continuous_ramareBlock P M (B i)).norm).pow 2
  have hcontS : Continuous fun w : ℝ =>
      (I.card : ℝ) * ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ ^ 2 :=
    (continuous_finsetSum I fun i _ => hcontB i).const_mul _
  have hint1 : IntegrableOn (fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcont.integrableOn_Icc
  have hint2 : IntegrableOn (fun w : ℝ =>
      (I.card : ℝ) * ∑ i ∈ I, ‖ramareBlock P M (B i) w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontS.integrableOn_Icc
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  refine integral_finsetSum I fun i _ => ?_
  exact (hcontB i).integrableOn_Icc

/-! ## The geometric ladder -/

/-- The `j`-th block of a geometric ladder of ratio `r` starting at `Q`. -/
noncomputable def geomBlock (P : Finset ℕ) (Q r : ℝ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p => Q * r ^ j < (p : ℝ) ∧ (p : ℝ) ≤ Q * r ^ (j + 1))

theorem geomBlock_subset (P : Finset ℕ) (Q r : ℝ) (j : ℕ) : geomBlock P Q r j ⊆ P :=
  Finset.filter_subset _ _

/-- **The ladder blocks are pairwise disjoint.** -/
theorem geomBlock_pairwiseDisjoint (P : Finset ℕ) {Q r : ℝ} (hQ : 0 < Q) (hr : 1 ≤ r)
    (L : ℕ) : ((Finset.range L : Finset ℕ) : Set ℕ).PairwiseDisjoint (geomBlock P Q r) := by
  classical
  intro i _ j _ hij
  refine Finset.disjoint_left.2 fun p hpi hpj => ?_
  rw [geomBlock, Finset.mem_filter] at hpi hpj
  obtain ⟨-, hilo, hihi⟩ := hpi
  obtain ⟨-, hjlo, hjhi⟩ := hpj
  have hrpow : ∀ m n : ℕ, m ≤ n → Q * r ^ m ≤ Q * r ^ n := by
    intro m n hmn
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hmn) hQ.le
  rcases Nat.lt_or_ge i j with hlt | hge
  · have : Q * r ^ (i + 1) ≤ Q * r ^ j := hrpow _ _ (by omega)
    linarith
  · have hji : j < i := by omega
    have : Q * r ^ (j + 1) ≤ Q * r ^ i := hrpow _ _ (by omega)
    linarith

/-- **The ladder covers a geometric prime range.** -/
theorem geomBlock_biUnion_eq (P : Finset ℕ) (Q r : ℝ) {L : ℕ}
    (hL : 1 ≤ L) (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * r ^ L) :
    (Finset.range L).biUnion (geomBlock P Q r) = P := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨j, -, hpj⟩ := hp
    exact geomBlock_subset P Q r j hpj
  · intro p hp
    obtain ⟨hplo, hphi⟩ := hP p hp
    haveI : DecidablePred fun k : ℕ => (p : ℝ) ≤ Q * r ^ (k + 1) := Classical.decPred _
    have hex : ∃ k : ℕ, (p : ℝ) ≤ Q * r ^ (k + 1) := by
      refine ⟨L - 1, ?_⟩
      have : L - 1 + 1 = L := by omega
      rw [this]
      exact hphi
    set j : ℕ := Nat.find hex with hjdef
    have hjspec : (p : ℝ) ≤ Q * r ^ (j + 1) := Nat.find_spec hex
    have hjL : j < L := by
      have hle : j ≤ L - 1 := Nat.find_le (by
        have : L - 1 + 1 = L := by omega
        rw [this]
        exact hphi)
      omega
    have hjlo : Q * r ^ j < (p : ℝ) := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · rw [hj0, pow_zero, mul_one]
        exact hplo
      · obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hmin : ¬ ((p : ℝ) ≤ Q * r ^ (k + 1)) := Nat.find_min hex (by omega)
        rw [hk]
        exact lt_of_not_ge hmin
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hjL,
      Finset.mem_filter.2 ⟨hp, hjlo, hjspec⟩⟩

/-- **The mean square over a geometric ladder.**  Splitting a geometric prime range into `L` blocks
of ratio `r` costs the factor `L`, and each block is narrow enough for its cofactor polynomials to
be comparable. -/
theorem integral_normSq_ramareBilinear_le_geomLadder {P : Finset ℕ} (M : ℕ) {W Q r : ℝ}
    (hQ : 0 < Q) (hr : 1 ≤ r) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * r ^ L) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          ∫ w in Set.Icc (-W) W, ‖ramareBlock P M (geomBlock P Q r j) w‖ ^ 2 := by
  classical
  have h := integral_normSq_ramareBilinear_le_blocks M (Finset.range L) (geomBlock P Q r)
    (geomBlock_pairwiseDisjoint P hQ hr L) (geomBlock_biUnion_eq P Q r hL hP) (W := W)
  rwa [Finset.card_range] at h

/-! ## One block, as a product -/

/-- The prime polynomial of a block. -/
def primeBlockPoly (B : Finset ℕ) (w : ℝ) : ℂ := ∑ p ∈ B, moebiusPhase w p

theorem continuous_primeBlockPoly (B : Finset ℕ) : Continuous fun w : ℝ => primeBlockPoly B w :=
  continuous_finsetSum B fun p _ => continuous_moebiusPhase p

/-- **One block is a product up to the cofactor discrepancy.**  Replacing every cofactor
polynomial by a single polynomial over a common index set turns the block into
`(prime polynomial)·(cofactor polynomial)`, at a mean-square cost of the block size times the sum
of the individual discrepancies. -/
theorem integral_normSq_ramareBlock_le_product {P : Finset ℕ} (M : ℕ) {B : Finset ℕ}
    (hBprime : ∀ q ∈ B, q.Prime) (C : Finset ℕ) (W : ℝ) :
    (∫ w in Set.Icc (-W) W, ‖ramareBlock P M B w‖ ^ 2)
      ≤ 2 * (∫ w in Set.Icc (-W) W,
            ‖primeBlockPoly B w * logPoly (ramareCofactorCoeff P) C w‖ ^ 2)
        + 2 * (B.card : ℝ) * ∑ p ∈ B, ∫ w in Set.Icc (-W) W,
            ‖ramareCofactorPoly P M p w - logPoly (ramareCofactorCoeff P) C w‖ ^ 2 := by
  classical
  set G : ℝ → ℂ := fun w => logPoly (ramareCofactorCoeff P) C w with hG
  have hdecomp : ∀ w : ℝ, ramareBlock P M B w
      = primeBlockPoly B w * G w
        + ∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w) := by
    intro w
    rw [ramareBlock, primeBlockPoly, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hpt : ∀ w : ℝ, ‖ramareBlock P M B w‖ ^ 2
      ≤ 2 * ‖primeBlockPoly B w * G w‖ ^ 2
        + 2 * (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2 := by
    intro w
    rw [hdecomp w]
    have hY : ‖∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w)‖
        ≤ ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
      rw [norm_mul, norm_moebiusPhase_prime (hBprime p hp), one_mul]
    have hY2 : ‖∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w)‖ ^ 2
        ≤ (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2 := by
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hY 2) ?_
      exact sq_sum_le_card_mul_sum_sq
    have htri := norm_add_le (primeBlockPoly B w * G w)
      (∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, hY2, sq_nonneg (‖primeBlockPoly B w * G w‖
      - ‖∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w)‖), norm_nonneg
      (∑ p ∈ B, moebiusPhase w p * (ramareCofactorPoly P M p w - G w))]
  -- integrate
  have hcontZ : Continuous fun w : ℝ => ‖ramareBlock P M B w‖ ^ 2 :=
    ((continuous_ramareBlock P M B).norm).pow 2
  have hcontX : Continuous fun w : ℝ => ‖primeBlockPoly B w * G w‖ ^ 2 :=
    (((continuous_primeBlockPoly B).mul (continuous_logPoly _ _)).norm).pow 2
  have hcontD : ∀ p : ℕ, Continuous fun w : ℝ =>
      ‖ramareCofactorPoly P M p w - G w‖ ^ 2 := fun p =>
    ((((continuous_ramareCofactorPoly P M p).sub (continuous_logPoly _ _))).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      2 * ‖primeBlockPoly B w * G w‖ ^ 2
        + 2 * (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2 :=
    (hcontX.const_mul 2).add ((continuous_finsetSum B fun p _ => hcontD p).const_mul _)
  have hint1 : IntegrableOn (fun w : ℝ => ‖ramareBlock P M B w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontZ.integrableOn_Icc
  have hint2 : IntegrableOn (fun w : ℝ =>
      2 * ‖primeBlockPoly B w * G w‖ ^ 2
        + 2 * (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontR.integrableOn_Icc
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  have hiX : IntegrableOn (fun w : ℝ => 2 * ‖primeBlockPoly B w * G w‖ ^ 2)
      (Set.Icc (-W) W) volume := (hcontX.const_mul 2).integrableOn_Icc
  have hiD : IntegrableOn (fun w : ℝ =>
      2 * (B.card : ℝ) * ∑ p ∈ B, ‖ramareCofactorPoly P M p w - G w‖ ^ 2)
      (Set.Icc (-W) W) volume :=
    ((continuous_finsetSum B fun p _ => hcontD p).const_mul _).integrableOn_Icc
  rw [integral_add hiX hiD, integral_const_mul, integral_const_mul]
  congr 1
  congr 1
  exact integral_finsetSum B fun p _ => (hcontD p).integrableOn_Icc

/-! ## One ladder block, fully assembled -/

/-- The common cofactor block of the `j`-th ladder step. -/
noncomputable def geomCofactorBlock (M : ℕ) (Q η : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Icc ⌈((1 : ℕ) : ℝ) / ((Q * (1 + η) ^ j) * (1 + η))⌉₊
    ⌊((M : ℕ) : ℝ) / (Q * (1 + η) ^ j)⌋₊

/-- **One ladder block, as a product plus an explicit error.**  The prime range of the `j`-th step
has relative width `η` about `Q(1+η)^j`, so every cofactor polynomial of the step is within the
common one by `O(η + 1/Q_j)` in mean square. -/
theorem integral_normSq_ramareBlock_geom_le {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) (j : ℕ)
    (hPprime : ∀ q ∈ P, q.Prime) :
    (∫ w in Set.Icc (-W) W, ‖ramareBlock P M (geomBlock P Q (1 + η) j) w‖ ^ 2)
      ≤ 2 * (∫ w in Set.Icc (-W) W,
            ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
              * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
        + 2 * ((geomBlock P Q (1 + η) j).card : ℝ) ^ 2
            * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
                * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 4
                  + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 + 1))) := by
  classical
  set B : Finset ℕ := geomBlock P Q (1 + η) j with hB
  set Qj : ℝ := Q * (1 + η) ^ j with hQj
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj1 : (1 : ℝ) ≤ Qj := by
    rw [hQj]
    have : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ hr1
    nlinarith [hQ, this]
  have hBprime : ∀ q ∈ B, q.Prime := by
    intro q hq
    exact hPprime q (geomBlock_subset P Q (1 + η) j hq)
  have hrange : ∀ p ∈ B, 0 < p ∧ Qj < (p : ℝ) ∧ (p : ℝ) ≤ Qj * (1 + η) := by
    intro p hp
    have hq := hBprime p hp
    rw [hB, geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, hhi⟩ := hp
    refine ⟨hq.pos, hlo, ?_⟩
    have hpow : Q * (1 + η) ^ (j + 1) = Qj * (1 + η) := by
      rw [hQj, pow_succ]
      ring
    rwa [hpow] at hhi
  have hprod := integral_normSq_ramareBlock_le_product (P := P) M hBprime
    (geomCofactorBlock M Q η j) W
  have hterm : ∀ p ∈ B, (∫ w in Set.Icc (-W) W,
      ‖ramareCofactorPoly P M p w
        - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
      ≤ 2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Qj + 4 + (((M : ℕ) : ℝ) / Qj ^ 2 + 1)) := by
    intro p hp
    obtain ⟨hp0, hplo, hphi⟩ := hrange p hp
    exact integral_normSq_cofactor_sub_common_le (P := P) M hQj1 hη hW hp0 hplo hphi
  have hsum : (∑ p ∈ B, ∫ w in Set.Icc (-W) W,
      ‖ramareCofactorPoly P M p w
        - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
      ≤ (B.card : ℝ)
          * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
              * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Qj + 4
                + (((M : ℕ) : ℝ) / Qj ^ 2 + 1))) := by
    have h := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  have hcard0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * (B.card : ℝ))
  refine hprod.trans ?_
  have hval : 2 * (B.card : ℝ)
      * ((B.card : ℝ)
          * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
              * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Qj + 4 + (((M : ℕ) : ℝ) / Qj ^ 2 + 1))))
      = 2 * (B.card : ℝ) ^ 2
          * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
              * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Qj + 4
                + (((M : ℕ) : ℝ) / Qj ^ 2 + 1))) := by ring
  rw [hval] at hmul
  linarith [hmul]

/-- **The whole bilinear mean square, over the ladder.**  Every term is explicit: the product of a
narrow prime polynomial with a single cofactor polynomial, and an error proportional to the block
size squared times `η + 1/Q_j`. -/
theorem integral_normSq_ramareBilinear_le_ladder_assembled {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          (2 * (∫ w in Set.Icc (-W) W,
                ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
                  * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
            + 2 * ((geomBlock P Q (1 + η) j).card : ℝ) ^ 2
                * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
                    * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 4
                      + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 + 1)))) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hladder := integral_normSq_ramareBilinear_le_geomLadder (P := P) M hQ0 hr1 hL hP (W := W)
  refine hladder.trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg L)
  exact integral_normSq_ramareBlock_geom_le M hQ hη hW j hPprime

/-! ## Separating the ladder cost from the error -/

/-- The total discrepancy of the ladder: every cofactor polynomial against the common one of its
step. -/
noncomputable def ramareLadderError (P : Finset ℕ) (M : ℕ) (Q η : ℝ) (L : ℕ) (w : ℝ) : ℂ :=
  ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P Q (1 + η) j,
    moebiusPhase w p
      * (ramareCofactorPoly P M p w
        - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w)

theorem continuous_ramareLadderError (P : Finset ℕ) (M : ℕ) (Q η : ℝ) (L : ℕ) :
    Continuous fun w : ℝ => ramareLadderError P M Q η L w := by
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun p _ => ?_
  exact (continuous_moebiusPhase p).mul
    ((continuous_ramareCofactorPoly P M p).sub (continuous_logPoly _ _))

/-- **The bilinear form is the ladder of products plus one global error.** -/
theorem ramareBilinear_eq_ladder_add_error {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 0 < Q)
    (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) (w : ℝ) :
    ramareBilinear P M w
      = (∑ j ∈ Finset.range L,
          primeBlockPoly (geomBlock P Q (1 + η) j) w
            * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w)
        + ramareLadderError P M Q η L w := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hsplit := ramareBilinear_eq_sum_blocks (P := P) M w (Finset.range L)
    (geomBlock P Q (1 + η)) (geomBlock_pairwiseDisjoint P hQ hr1 L)
    (geomBlock_biUnion_eq P Q (1 + η) hL hP)
  rw [hsplit, ramareLadderError, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ramareBlock, primeBlockPoly, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **The mean square, with the ladder cost separated from the error.**  Only the product terms pay
the block count; the discrepancy is paid once. -/
theorem integral_normSq_ramareBilinear_le_ladder_error {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
            (∫ w in Set.Icc (-W) W,
              ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
                * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
        + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ 2 := by
  classical
  set F : ℕ → ℝ → ℂ := fun j w =>
    primeBlockPoly (geomBlock P Q (1 + η) j) w
      * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w with hF
  have hcontF : ∀ j : ℕ, Continuous fun w : ℝ => ‖F j w‖ ^ 2 := by
    intro j
    exact ((((continuous_primeBlockPoly _).mul (continuous_logPoly _ _))).norm).pow 2
  have hcontE : Continuous fun w : ℝ => ‖ramareLadderError P M Q η L w‖ ^ 2 :=
    ((continuous_ramareLadderError P M Q η L).norm).pow 2
  have hpt : ∀ w : ℝ, ‖ramareBilinear P M w‖ ^ 2
      ≤ 2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2)
        + 2 * ‖ramareLadderError P M Q η L w‖ ^ 2 := by
    intro w
    rw [ramareBilinear_eq_ladder_add_error M hQ hη hL hP w]
    have hsum : ‖∑ j ∈ Finset.range L, F j w‖ ^ 2
        ≤ (L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2 := by
      have h1 : ‖∑ j ∈ Finset.range L, F j w‖ ≤ ∑ j ∈ Finset.range L, ‖F j w‖ :=
        norm_sum_le _ _
      have h2 : (∑ j ∈ Finset.range L, ‖F j w‖) ^ 2
          ≤ ((Finset.range L).card : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      rw [Finset.card_range] at h2
      exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
    have htri := norm_add_le (∑ j ∈ Finset.range L, F j w) (ramareLadderError P M Q η L w)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, hsum, sq_nonneg (‖∑ j ∈ Finset.range L, F j w‖
      - ‖ramareLadderError P M Q η L w‖), norm_nonneg (ramareLadderError P M Q η L w),
      norm_nonneg (∑ j ∈ Finset.range L, F j w)]
  have hcontZ : Continuous fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2 :=
    ((continuous_ramareBilinear P M).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2)
        + 2 * ‖ramareLadderError P M Q η L w‖ ^ 2 :=
    (((continuous_finsetSum _ fun j _ => hcontF j).const_mul _).const_mul 2).add
      (hcontE.const_mul 2)
  have hintZ : IntegrableOn (fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontZ.integrableOn_Icc
  have hintR : IntegrableOn (fun w : ℝ =>
      2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2)
        + 2 * ‖ramareLadderError P M Q η L w‖ ^ 2) (Set.Icc (-W) W) volume :=
    hcontR.integrableOn_Icc
  have hmono := setIntegral_mono_on hintZ hintR measurableSet_Icc (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  have hi1 : IntegrableOn (fun w : ℝ => 2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2))
      (Set.Icc (-W) W) volume :=
    (((continuous_finsetSum _ fun j _ => hcontF j).const_mul _).const_mul 2).integrableOn_Icc
  have hi2 : IntegrableOn (fun w : ℝ => 2 * ‖ramareLadderError P M Q η L w‖ ^ 2)
      (Set.Icc (-W) W) volume := (hcontE.const_mul 2).integrableOn_Icc
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, integral_const_mul]
  have hsplit : (∫ w in Set.Icc (-W) W, ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2)
      = ∑ j ∈ Finset.range L, ∫ w in Set.Icc (-W) W, ‖F j w‖ ^ 2 :=
    integral_finsetSum _ fun j _ => (hcontF j).integrableOn_Icc
  rw [hsplit]
  ring

/-! ## The ladder error as a prime-shifted family -/

/-- **The ladder error, with the cofactor discrepancy exhibited as a gap set.**  Since every
filtered cofactor set lies inside the common block of its step, the discrepancy is minus the
polynomial over the gap. -/
theorem ramareLadderError_eq_neg_sum {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η)
    (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) (w : ℝ) :
    ramareLadderError P M Q η L w
      = -∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P Q (1 + η) j,
          moebiusPhase w p
            * logPoly (ramareCofactorCoeff P)
                (geomCofactorBlock M Q η j
                  \ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}) w := by
  classical
  rw [ramareLadderError, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  set Qj : ℝ := Q * (1 + η) ^ j with hQj
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj1 : (1 : ℝ) ≤ Qj := by
    rw [hQj]
    have : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ hr1
    nlinarith [hQ, this]
  have hq := hPprime p (geomBlock_subset P Q (1 + η) j hp)
  have hrange : Qj < (p : ℝ) ∧ (p : ℝ) ≤ Qj * (1 + η) := by
    rw [geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, hhi⟩ := hp
    refine ⟨hlo, ?_⟩
    have hpow : Q * (1 + η) ^ (j + 1) = Qj * (1 + η) := by
      rw [hQj, pow_succ]
      ring
    rwa [hpow] at hhi
  have hsub := cofactorFilter_subset_common (Q := Qj) (η := η) M hQj1 hη hq.pos
    hrange.1 hrange.2
  have hUC : {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}
      \ geomCofactorBlock M Q η j = ∅ := by
    rw [geomCofactorBlock, ← hQj]
    exact Finset.sdiff_eq_empty_iff_subset.2 hsub
  have hdiff : ramareCofactorPoly P M p w
      - logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w
      = -logPoly (ramareCofactorCoeff P)
          (geomCofactorBlock M Q η j
            \ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}) w := by
    rw [ramareCofactorPoly, logPoly_sub_eq_sdiff, hUC, logPoly]
    simp
  rw [hdiff]
  ring

/-! ## The ladder error, flattened -/

/-- The gap set of one `(step, prime)` pair. -/
noncomputable def ladderGapSet (M : ℕ) (Q η : ℝ) (x : (_ : ℕ) × ℕ) : Finset ℕ :=
  geomCofactorBlock M Q η x.1 \ {m ∈ ramareCofactorSet (Finset.Icc 1 M) x.2 | ¬ x.2 ∣ m}

/-- The flattened index set of the ladder: all `(step, prime)` pairs. -/
noncomputable def ladderIndex (P : Finset ℕ) (Q η : ℝ) (L : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Finset.range L).sigma (fun j => geomBlock P Q (1 + η) j)

/-- **The ladder error, as one prime-shifted family.** -/
theorem ramareLadderError_eq_flat {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η)
    (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) (w : ℝ) :
    ramareLadderError P M Q η L w
      = -∑ x ∈ ladderIndex P Q η L,
          moebiusPhase w x.2 * logPoly (ramareCofactorCoeff P) (ladderGapSet M Q η x) w := by
  classical
  rw [ramareLadderError_eq_neg_sum M hQ hη L hPprime w, ladderIndex]
  congr 1
  rw [Finset.sum_sigma']
  simp only [ladderGapSet]

/-- **The mean square of the ladder error.**  One power of the overlap count and of the total gap
size; no Cauchy--Schwarz over the primes. -/
theorem integral_normSq_ramareLadderError_le {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L N : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hDN : ∀ x ∈ ladderIndex P Q η L,
      (ladderGapSet M Q η x).image (fun m => x.2 * m) ⊆ Finset.Icc 1 N)
    (hK : ∀ n ∈ Finset.Icc 1 N, (((ladderIndex P Q η L).filter
      (fun x => n ∈ (ladderGapSet M Q η x).image (fun m => x.2 * m))).card : ℝ) ≤ K) :
    (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ))
          * (K * ∑ x ∈ ladderIndex P Q η L, ((ladderGapSet M Q η x).card : ℝ)) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hpos : ∀ x ∈ ladderIndex P Q η L, 0 < x.2 := by
    intro x hx
    rw [ladderIndex, Finset.mem_sigma] at hx
    exact (hPprime x.2 (geomBlock_subset P Q (1 + η) x.1 hx.2)).pos
  have hDpos : ∀ x ∈ ladderIndex P Q η L, ∀ m ∈ ladderGapSet M Q η x, 0 < m := by
    intro x _ m hm
    rw [ladderGapSet, Finset.mem_sdiff, geomCofactorBlock, Finset.mem_Icc] at hm
    have h1 : 1 ≤ ⌈((1 : ℕ) : ℝ) / ((Q * (1 + η) ^ x.1) * (1 + η))⌉₊ := by
      refine Nat.one_le_ceil_iff.2 ?_
      have hpow : (0 : ℝ) < (1 + η) ^ x.1 := by positivity
      positivity
    omega
  have hcongr : (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ 2)
      = ∫ w in Set.Icc (-W) W,
        ‖∑ x ∈ ladderIndex P Q η L,
          moebiusPhase w x.2 * logPoly (ramareCofactorCoeff P) (ladderGapSet M Q η x) w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [ramareLadderError_eq_flat M hQ hη L hPprime w, norm_neg]
  rw [hcongr]
  exact integral_Icc_normSq_primeShift_family_le (ladderIndex P Q η L) (fun x => x.2)
    (ladderGapSet M Q η) (ramareCofactorCoeff P) hpos hDpos
    (norm_ramareCofactorCoeff_le_one P) hK0 hDN hK hW

/-! ## The two side conditions of the ladder error -/

/-- **Every shifted index stays below `M(1+η)`.**  A cofactor of the `j`-th step is at most
`M/Q_j` and its prime at most `Q_j(1+η)`. -/
theorem ladderGap_image_subset {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η)
    (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) :
    ∀ x ∈ ladderIndex P Q η L,
      (ladderGapSet M Q η x).image (fun m => x.2 * m)
        ⊆ Finset.Icc 1 ⌊(M : ℝ) * (1 + η)⌋₊ := by
  classical
  intro x hx n hn
  rw [Finset.mem_image] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  rw [ladderIndex, Finset.mem_sigma] at hx
  have hp := hPprime x.2 (geomBlock_subset P Q (1 + η) x.1 hx.2)
  set Qj : ℝ := Q * (1 + η) ^ x.1 with hQj
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj1 : (1 : ℝ) ≤ Qj := by
    rw [hQj]
    have : (1 : ℝ) ≤ (1 + η) ^ x.1 := one_le_pow₀ hr1
    nlinarith [hQ, this]
  have hQj0 : (0 : ℝ) < Qj := lt_of_lt_of_le zero_lt_one hQj1
  have hphi : (x.2 : ℝ) ≤ Qj * (1 + η) := by
    rw [geomBlock, Finset.mem_filter] at hx
    have hhi := hx.2.2.2
    have hpow : Q * (1 + η) ^ (x.1 + 1) = Qj * (1 + η) := by
      rw [hQj, pow_succ]
      ring
    rwa [hpow] at hhi
  have hmC : m ∈ geomCofactorBlock M Q η x.1 := (Finset.mem_sdiff.1 hm).1
  rw [geomCofactorBlock, ← hQj, Finset.mem_Icc] at hmC
  have hm1 : 1 ≤ m := by
    have h1 : 1 ≤ ⌈((1 : ℕ) : ℝ) / (Qj * (1 + η))⌉₊ := by
      refine Nat.one_le_ceil_iff.2 ?_
      positivity
    omega
  have hmhi : (m : ℝ) ≤ (M : ℝ) / Qj := by
    have hfl : ((⌊((M : ℕ) : ℝ) / Qj⌋₊ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) / Qj :=
      Nat.floor_le (by positivity)
    have : ((m : ℕ) : ℝ) ≤ ((⌊((M : ℕ) : ℝ) / Qj⌋₊ : ℕ) : ℝ) := by exact_mod_cast hmC.2
    linarith
  refine Finset.mem_Icc.2 ⟨?_, ?_⟩
  · have : 1 ≤ x.2 := hp.pos
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  · refine Nat.le_floor ?_
    have hprod : ((x.2 * m : ℕ) : ℝ) = (x.2 : ℝ) * (m : ℝ) := by push_cast; ring
    rw [hprod]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hstep : (x.2 : ℝ) * (m : ℝ) ≤ (Qj * (1 + η)) * ((M : ℝ) / Qj) :=
      mul_le_mul hphi hmhi hm0 (by positivity)
    have hval : (Qj * (1 + η)) * ((M : ℝ) / Qj) = (M : ℝ) * (1 + η) := by
      field_simp
    rwa [hval] at hstep

/-- **The overlap count is at most the number of designated primes dividing the index.**  Distinct
ladder steps are disjoint, so a prime determines its step. -/
theorem ladderIndex_filter_card_le {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (L : ℕ) (n : ℕ) :
    (((ladderIndex P Q η L).filter
        (fun x => n ∈ (ladderGapSet M Q η x).image (fun m => x.2 * m))).card : ℝ)
      ≤ ((P.filter (fun p => p ∣ n)).card : ℝ) := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hmaps : ∀ x ∈ (ladderIndex P Q η L).filter
      (fun x => n ∈ (ladderGapSet M Q η x).image (fun m => x.2 * m)),
      x.2 ∈ P.filter (fun p => p ∣ n) := by
    intro x hx
    rw [Finset.mem_filter, ladderIndex, Finset.mem_sigma] at hx
    obtain ⟨⟨-, hxblock⟩, hximg⟩ := hx
    rw [Finset.mem_image] at hximg
    obtain ⟨m, -, hnm⟩ := hximg
    exact Finset.mem_filter.2 ⟨geomBlock_subset P Q (1 + η) x.1 hxblock, ⟨m, hnm.symm⟩⟩
  have hinj : Set.InjOn (fun x : (_ : ℕ) × ℕ => x.2)
      (((ladderIndex P Q η L).filter
        (fun x => n ∈ (ladderGapSet M Q η x).image (fun m => x.2 * m)) : Finset _) : Set _) := by
    intro x hx y hy hEq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, ladderIndex, Finset.mem_sigma] at hx hy
    have hxb := hx.1.2
    have hyb := hy.1.2
    have hEq' : x.2 = y.2 := hEq
    have hsame : x.1 = y.1 := by
      by_contra hne
      have hdisj := geomBlock_pairwiseDisjoint P hQ hr1 L (Finset.mem_coe.2 hx.1.1)
        (Finset.mem_coe.2 hy.1.1) hne
      exact (Finset.disjoint_left.1 hdisj) hxb (hEq' ▸ hyb)
    exact Sigma.ext hsame (by rw [hEq'])
  have hcard := Finset.card_le_card_of_injOn (fun x : (_ : ℕ) × ℕ => x.2) hmaps hinj
  exact_mod_cast hcard

/-- **The ladder error, with both side conditions discharged.**  Only a bound on the number of
designated primes dividing an index is left. -/
theorem integral_normSq_ramareLadderError_le_divisorCount {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hK : ∀ n ∈ Finset.Icc 1 ⌊(M : ℝ) * (1 + η)⌋₊,
      ((P.filter (fun p => p ∣ n)).card : ℝ) ≤ K) :
    (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * (K * ∑ x ∈ ladderIndex P Q η L, ((ladderGapSet M Q η x).card : ℝ)) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  refine integral_normSq_ramareLadderError_le M hQ hη hW hK0 hPprime
    (ladderGap_image_subset M hQ hη L hPprime) ?_
  intro n hn
  exact le_trans (ladderIndex_filter_card_le M hQ0 hη L n) (hK n hn)

end

end RHTower.Sieve
