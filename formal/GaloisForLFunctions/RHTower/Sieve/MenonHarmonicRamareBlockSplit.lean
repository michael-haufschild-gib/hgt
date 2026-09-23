import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamare
import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplit
import GaloisForLFunctions.RHTower.Sieve.HarmonicCauchySchwarz

/-!
# Harmonic Ramaré block splitting

Menon's final-range Ramaré polynomial carries the coefficient `μ(n)/n`.  Splitting its outer
prime sum into blocks therefore gives prime phases of norm `1/p`.  The weighted discrepancy bound
below preserves that harmonic mass exactly: replacing the prime-dependent cofactor polynomial by
one common polynomial costs `∑ 1/p`, not the square of the number of primes.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The prime-dependent damped harmonic cofactor polynomial in Ramaré's identity. -/
def harmonicRamareCofactorPoly (P s : Finset ℕ) (p : ℕ) (w : ℝ) : ℂ :=
  logPoly (harmonicRamareCofactorCoeff P)
    {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w

theorem continuous_harmonicRamareCofactorPoly (P s : Finset ℕ) (p : ℕ) :
    Continuous fun w : ℝ => harmonicRamareCofactorPoly P s p w :=
  continuous_logPoly _ _

/-- One prime block of the harmonic Ramaré bilinear form. -/
def harmonicRamareBlock (P s B : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ p ∈ B, harmonicMoebiusPhase w p * harmonicRamareCofactorPoly P s p w

theorem continuous_harmonicRamareBlock (P s B : Finset ℕ) :
    Continuous fun w : ℝ => harmonicRamareBlock P s B w := by
  refine continuous_finsetSum B fun p _ => ?_
  exact ((continuous_moebiusPhase p).div_const _).mul
    (continuous_harmonicRamareCofactorPoly P s p)

/-- The harmonic Ramaré bilinear form splits exactly over a partition of its prime set. -/
theorem harmonicRamareBilinear_eq_sum_blocks {P s : Finset ℕ} (w : ℝ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P) :
    harmonicRamareBilinear P s w = ∑ i ∈ I, harmonicRamareBlock P s (B i) w := by
  classical
  rw [harmonicRamareBilinear, ← hcover, Finset.sum_biUnion hdisj]
  rfl

/-- Cauchy--Schwarz over a partition of the designated primes costs the number of blocks. -/
theorem integral_normSq_harmonicRamareBilinear_le_blocks {P s : Finset ℕ} {W : ℝ}
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ))
      ≤ (I.card : ℝ) * ∑ i ∈ I,
          ∫ w in Set.Icc (-W) W, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) := by
  classical
  have hpt : ∀ w : ℝ, ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ)
      ≤ (I.card : ℝ) * ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) := by
    intro w
    rw [harmonicRamareBilinear_eq_sum_blocks w I B hdisj hcover]
    have h1 : ‖∑ i ∈ I, harmonicRamareBlock P s (B i) w‖
        ≤ ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ := norm_sum_le _ _
    have h2 : (∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖) ^ (2 : ℕ)
        ≤ (I.card : ℝ) * ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hcont : Continuous fun w : ℝ => ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ) := by
    refine (continuous_finsetSum P fun p _ => ?_).norm.pow 2
    exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _)
  have hcontB : ∀ i : ι, Continuous fun w : ℝ =>
      ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) := fun i =>
    ((continuous_harmonicRamareBlock P s (B i)).norm).pow 2
  have hcontS : Continuous fun w : ℝ =>
      (I.card : ℝ) * ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ) :=
    (continuous_finsetSum I fun i _ => hcontB i).const_mul _
  have hint1 : IntegrableOn (fun w : ℝ => ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume := hcont.integrableOn_Icc
  have hint2 : IntegrableOn (fun w : ℝ =>
      (I.card : ℝ) * ∑ i ∈ I, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume := hcontS.integrableOn_Icc
  have hmono := setIntegral_mono_on hint1 hint2
    measurableSet_Icc (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum I fun i _ => (hcontB i).integrableOn_Icc

/-- The harmonic prime polynomial attached to one block. -/
def harmonicPrimeBlockPoly (B : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ p ∈ B, harmonicMoebiusPhase w p

theorem continuous_harmonicPrimeBlockPoly (B : Finset ℕ) :
    Continuous fun w : ℝ => harmonicPrimeBlockPoly B w :=
  continuous_finsetSum B fun p _ => (continuous_moebiusPhase p).div_const _

/-- Harmonic mass of a finite prime block. -/
def harmonicPrimeMass (B : Finset ℕ) : ℝ := ∑ p ∈ B, 1 / (p : ℝ)

theorem norm_harmonicMoebiusPhase_prime {p : ℕ} (hp : p.Prime) (w : ℝ) :
    ‖harmonicMoebiusPhase w p‖ = 1 / (p : ℝ) := by
  rw [harmonicMoebiusPhase, norm_div, norm_moebiusPhase_prime hp, Complex.norm_natCast]

/-- Pointwise harmonic discrepancy after replacing all prime-dependent cofactors by one common
polynomial.  Weight `p` in Cauchy--Schwarz cancels one of the two factors `1/p`. -/
theorem normSq_harmonicRamareBlock_sub_product_le {P s B C : Finset ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (w : ℝ) :
    ‖harmonicRamareBlock P s B w
        - harmonicPrimeBlockPoly B w * logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)
      ≤ harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
          ‖harmonicRamareCofactorPoly P s p w
            - logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ) := by
  classical
  set G : ℝ → ℂ := fun u => logPoly (harmonicRamareCofactorCoeff P) C u
  have hdecomp : harmonicRamareBlock P s B w - harmonicPrimeBlockPoly B w * G w
      = ∑ p ∈ B, harmonicMoebiusPhase w p *
          (harmonicRamareCofactorPoly P s p w - G w) := by
    rw [harmonicRamareBlock, harmonicPrimeBlockPoly, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hdecomp]
  have hp0 : ∀ p ∈ B, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    exact_mod_cast (hBprime p hp).pos
  have hweighted := normSq_sum_le_weighted B (fun p => (p : ℝ)) hp0
    (fun p => harmonicMoebiusPhase w p *
      (harmonicRamareCofactorPoly P s p w - G w))
  refine hweighted.trans (le_of_eq ?_)
  rw [harmonicPrimeMass]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [norm_mul, norm_harmonicMoebiusPhase_prime (hBprime p hp), mul_pow]
  field_simp [Nat.cast_ne_zero.2 (hBprime p hp).ne_zero]; ring

/-- Mean-square block-to-product replacement with exact harmonic prime-mass loss. -/
theorem integral_normSq_harmonicRamareBlock_le_product {P s B : Finset ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (C : Finset ℕ) (W : ℝ) :
    (∫ w in Set.Icc (-W) W, ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ))
      ≤ 2 * (∫ w in Set.Icc (-W) W,
            ‖harmonicPrimeBlockPoly B w
              * logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ))
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            (∫ w in Set.Icc (-W) W,
              ‖harmonicRamareCofactorPoly P s p w
                - logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)) := by
  classical
  set G : ℝ → ℂ := fun w => logPoly (harmonicRamareCofactorCoeff P) C w
  have hdecomp : ∀ w : ℝ, harmonicRamareBlock P s B w
      = harmonicPrimeBlockPoly B w * G w
        + (harmonicRamareBlock P s B w - harmonicPrimeBlockPoly B w * G w) := by
    intro w
    ring
  have hpt : ∀ w : ℝ, ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ)
      ≤ 2 * ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ)
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ) := by
    intro w
    rw [hdecomp w]
    have hdisc := normSq_harmonicRamareBlock_sub_product_le
      (P := P) (s := s) (C := C) hBprime w
    have htri := norm_add_le (harmonicPrimeBlockPoly B w * G w)
      (harmonicRamareBlock P s B w - harmonicPrimeBlockPoly B w * G w)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, hdisc,
      sq_nonneg (‖harmonicPrimeBlockPoly B w * G w‖ -
        ‖harmonicRamareBlock P s B w - harmonicPrimeBlockPoly B w * G w‖)]
  have hcontZ : Continuous fun w : ℝ => ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ) :=
    ((continuous_harmonicRamareBlock P s B).norm).pow 2
  have hcontX : Continuous fun w : ℝ => ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ) :=
    (((continuous_harmonicPrimeBlockPoly B).mul (continuous_logPoly _ _)).norm).pow 2
  have hcontD : ∀ p : ℕ, Continuous fun w : ℝ =>
      ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ) := fun p =>
    (((continuous_harmonicRamareCofactorPoly P s p).sub
      (continuous_logPoly _ _)).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      2 * ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ)
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ) :=
    (hcontX.const_mul 2).add
      ((continuous_finsetSum B fun p _ => (hcontD p).const_mul _).const_mul _)
  have hint1 : IntegrableOn (fun w : ℝ => ‖harmonicRamareBlock P s B w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume := hcontZ.integrableOn_Icc
  have hint2 : IntegrableOn (fun w : ℝ =>
      2 * ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ)
        + 2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
            ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume := hcontR.integrableOn_Icc
  have hmono := setIntegral_mono_on hint1 hint2
    measurableSet_Icc (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  have hiX : IntegrableOn (fun w : ℝ => 2 * ‖harmonicPrimeBlockPoly B w * G w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume := (hcontX.const_mul 2).integrableOn_Icc
  have hiD : IntegrableOn (fun w : ℝ =>
      2 * harmonicPrimeMass B * ∑ p ∈ B, (1 / (p : ℝ)) *
        ‖harmonicRamareCofactorPoly P s p w - G w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume :=
    ((continuous_finsetSum B fun p _ => (hcontD p).const_mul _).const_mul _).integrableOn_Icc
  rw [integral_add hiX hiD, integral_const_mul]
  congr 1
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum B fun p _ =>
    ((hcontD p).const_mul (1 / (p : ℝ))).integrableOn_Icc]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul]

end

end RHTower.Sieve
