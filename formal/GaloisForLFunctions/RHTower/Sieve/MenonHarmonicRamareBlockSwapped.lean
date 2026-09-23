import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderOnHM

/-!
# The swapped Halasz--Montgomery receiver for one harmonic Ramare block

`MenonHarmonicRamareLadderOnHM` pays the prime factor of a geometric block pointwise and the
harmonic cofactor by reciprocal Halasz--Montgomery.  That ordering is efficient only while the
cofactor polynomial is long.  Once the prime scale is comparable with the source scale the
cofactor is short, its trivial harmonic supremum is `O(1)`, and the entire saving has to come
from the *mean square of the prime polynomial* instead.  This file builds that receiver.

Nothing here is assumed.  The cofactor supremum is the literal harmonic mass of its own support,
proved from the reciprocal coefficient bound, and the prime mean square is the corpus's own
reciprocal Halasz--Montgomery estimate applied to `harmonicMoebiusC` on the block's two natural
endpoints.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The harmonic Moebius coefficient is bounded by the reciprocal index. -/
theorem norm_harmonicMoebiusC_le_inv (n : ℕ) :
    ‖harmonicMoebiusC n‖ ≤ 1 / (n : ℝ) := by
  rw [harmonicMoebiusC, norm_div, Complex.norm_natCast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  have hnorm : ‖((μ n : ℤ) : ℂ)‖ = |((μ n : ℤ) : ℝ)| := by
    rw [show (((μ n : ℤ)) : ℂ) = ((((μ n : ℤ) : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact abs_moebius_real_le_one n

/-- The harmonic prime block polynomial is the Gallagher polynomial of `harmonicMoebiusC`. -/
theorem harmonicPrimeBlockPoly_eq_logPoly (B : Finset ℕ) (w : ℝ) :
    harmonicPrimeBlockPoly B w = logPoly harmonicMoebiusC B w := by
  rw [harmonicPrimeBlockPoly, logPoly_harmonicMoebius_eq_sum_phase]

/-- **Reciprocal Halasz--Montgomery mean square for a harmonic prime block.**  The block's own
lower endpoint supplies the reciprocal coefficient gain. -/
theorem setIntegral_normSq_harmonicPrimeBlockPoly_le_HM_recip
    (B : Finset ℕ) {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N)
    (hB : B ⊆ Finset.Icc L N) {E : Set ℝ} (hE : MeasurableSet E)
    {W : ℝ} (hW : 1 ≤ W) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖harmonicPrimeBlockPoly B w‖ ^ (2 : ℕ))
      ≤ (2 * Real.pi)⁻¹
        * (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E)
            * ((1 / (L : ℝ)) ^ (2 : ℕ) * (B.card : ℝ))) := by
  have hBI : B ⊆ Finset.Icc 1 N := by
    intro n hn
    have hn' := Finset.mem_Icc.1 (hB hn)
    exact Finset.mem_Icc.2 ⟨le_trans hL hn'.1, hn'.2⟩
  have hrw : (∫ w in E, ‖harmonicPrimeBlockPoly B w‖ ^ (2 : ℕ))
      = ∫ w in E, ‖logPoly harmonicMoebiusC B w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun hE fun w _ => ?_
    rw [harmonicPrimeBlockPoly_eq_logPoly]
  rw [hrw]
  refine setIntegral_normSq_logPoly_le_HM_window_recip_on
    harmonicMoebiusC hN hBI hE hW hEs (by positivity) ?_
  intro n hn
  have hn' := Finset.mem_Icc.1 (hB hn)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hL
  have hLn : (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1
  exact (norm_harmonicMoebiusC_le_inv n).trans (one_div_le_one_div_of_le hLR hLn)

/-- The harmonic cofactor polynomial never exceeds the harmonic mass of its own support. -/
theorem norm_logPoly_harmonicRamareCofactorCoeff_le (P D : Finset ℕ) (w : ℝ) :
    ‖logPoly (harmonicRamareCofactorCoeff P) D w‖ ≤ harmonicPrimeMass D := by
  refine (norm_logPoly_le (harmonicRamareCofactorCoeff P) D w).trans ?_
  rw [harmonicPrimeMass]
  exact Finset.sum_le_sum fun m _ => norm_harmonicRamareCofactorCoeff_le_inv P m

/-- Product integral from a cofactor supremum and a harmonic-prime mean square: the exact
reversal of `setIntegral_normSq_harmonicBlockProduct_le_supMeanSquare`. -/
theorem setIntegral_normSq_harmonicBlockProduct_le_meanSquareSup
    (a : ℕ → ℂ) (B D : Finset ℕ) {W U I : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hbound : ∀ w ∈ E, ‖logPoly a D w‖ ≤ U)
    (hI : (∫ w in E, ‖harmonicPrimeBlockPoly B w‖ ^ (2 : ℕ)) ≤ I) :
    (∫ w in E, ‖harmonicPrimeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      ≤ U ^ (2 : ℕ) * I := by
  have hrw : (∫ w in E, ‖harmonicPrimeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      = ∫ w in E, ‖logPoly a D w‖ ^ (2 : ℕ) * ‖harmonicPrimeBlockPoly B w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [norm_mul, mul_pow, mul_comm]
  rw [hrw]
  refine le_trans (setIntegral_normSq_mul_le_of_bound
    (continuous_logPoly a D) (continuous_harmonicPrimeBlockPoly B)
    hEm hEs hbound) ?_
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-- A geometric block sits between the two natural endpoints of its own step. -/
theorem geomBlock_subset_Icc (P : Finset ℕ) {Q eta : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta) (j : ℕ) :
    geomBlock P Q (1 + eta) j ⊆
      Finset.Icc (⌊Q * (1 + eta) ^ j⌋₊ + 1) ⌊Q * (1 + eta) ^ (j + 1)⌋₊ := by
  intro p hp
  rw [geomBlock, Finset.mem_filter] at hp
  obtain ⟨-, hlow, hhigh⟩ := hp
  have hbase : (0 : ℝ) ≤ Q * (1 + eta) ^ j := by positivity
  have hfloor : ⌊Q * (1 + eta) ^ j⌋₊ < p := (Nat.floor_lt hbase).2 hlow
  exact Finset.mem_Icc.2 ⟨hfloor, Nat.le_floor hhigh⟩

/-- **One harmonic geometric block with the two factors exchanged.**  The cofactor is paid by its
own harmonic supremum and the prime block by reciprocal Halasz--Montgomery at the block's natural
endpoints.  This is the efficient ordering once the prime scale is comparable with the source
scale, where the cofactor is short and the pointwise prime bound is wasteful. -/
theorem setIntegral_normSq_harmonicRamareBlock_geom_le_HM_swapped
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (htop : 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E,
      ‖harmonicRamareBlock P (Finset.Icc A₀ B₀)
        (geomBlock P Q (1 + eta) j) w‖ ^ (2 : ℕ))
      ≤ 2 * harmonicPrimeMass (harmonicGeomCofactorBlock A₀ B₀ Q eta j) ^ (2 : ℕ) *
          ((2 * Real.pi)⁻¹ *
            (hmMassRecip ⌊Q * (1 + eta) ^ (j + 1)⌋₊
              (2 * Real.pi * W) (2 * Real.pi * volume.real E) *
                ((1 / ((⌊Q * (1 + eta) ^ j⌋₊ + 1 : ℕ) : ℝ)) ^ (2 : ℕ) *
                  ((geomBlock P Q (1 + eta) j).card : ℝ))))
        + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ (2 : ℕ) *
            harmonicCofactorSupportError A₀ B₀ Q eta W j := by
  have hHM := setIntegral_normSq_harmonicPrimeBlockPoly_le_HM_recip
    (geomBlock P Q (1 + eta) j)
    (L := ⌊Q * (1 + eta) ^ j⌋₊ + 1) (N := ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    (Nat.le_add_left 1 _) htop (geomBlock_subset_Icc P hQ heta j) hEm hW hEs
  have hprod := setIntegral_normSq_harmonicBlockProduct_le_meanSquareSup
    (harmonicRamareCofactorCoeff P) (geomBlock P Q (1 + eta) j)
    (harmonicGeomCofactorBlock A₀ B₀ Q eta j) hEm hEs
    (fun w _ => norm_logPoly_harmonicRamareCofactorCoeff_le P _ w) hHM
  have hblock := setIntegral_normSq_harmonicRamareBlock_geom_le
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    hA₀ hQ heta hW j hPprime hleft hEm hEs
  refine hblock.trans ?_
  have htwo := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2 by norm_num)
  linarith

end

end RHTower.Sieve
