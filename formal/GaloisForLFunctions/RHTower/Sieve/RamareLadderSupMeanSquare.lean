import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplitOn
import GaloisForLFunctions.RHTower.Sieve.SetIntegralBlockSplit
import GaloisForLFunctions.RHTower.Sieve.LadderBlockMeanSquare
import GaloisForLFunctions.RHTower.Sieve.BlockProductAnnulus

/-!
# The Ramaré ladder over a frequency set, with the cofactor's mean square supplied

`Sieve/RamareBlockSplitOn.setIntegral_normSq_ramareBilinear_le_ladder_assembled` leaves each block's
product integral `∫_E ‖P_j·C_j‖²` open.  On a set where the **prime** block obeys a pointwise bound
— a zero-free-region estimate, valid on an annulus — the product integral is that bound squared
times the cofactor's mean square over the same set, and the latter is exactly what an integral
Halász–Montgomery estimate delivers.  Passing the mean square in as a parameter keeps the two
inputs independent: the pointwise bound comes from arithmetic, the mean square from the measure of
the set.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **One block over a frequency set, from a prime sup and a cofactor mean square.** -/
theorem setIntegral_normSq_blockProduct_le_supMeanSquare (a : ℕ → ℂ) (B D : Finset ℕ)
    {W V I : ℝ} {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hbound : ∀ w ∈ E, ‖primeBlockPoly B w‖ ≤ V)
    (hI : (∫ w in E, ‖logPoly a D w‖ ^ (2 : ℕ)) ≤ I) :
    (∫ w in E, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ)) ≤ V ^ (2 : ℕ) * I := by
  have hrw : (∫ w in E, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      = ∫ w in E, ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [norm_mul, mul_pow]
  rw [hrw]
  refine le_trans (setIntegral_normSq_mul_le_of_bound (continuous_primeBlockPoly B)
    (continuous_logPoly a D) hEm hEs hbound) ?_
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-- **The block ladder over a frequency set, with the discrepancy paid once.**  Unlike the
per-block form, the ladder's discrepancy is a single polynomial family: it is *not* multiplied by
the square of a block's prime count, which is what makes a prime range reaching up to `h`
affordable. -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_error {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
            (∫ w in E, ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
                * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
        + 2 * ∫ w in E, ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ) := by
  classical
  set F : ℕ → ℝ → ℂ := fun j w =>
    primeBlockPoly (geomBlock P Q (1 + η) j) w
      * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w with hF
  have hcontF : ∀ j : ℕ, Continuous fun w : ℝ => ‖F j w‖ ^ (2 : ℕ) := fun j =>
    ((((continuous_primeBlockPoly _).mul (continuous_logPoly _ _))).norm).pow 2
  have hcontE : Continuous fun w : ℝ => ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ) :=
    ((continuous_ramareLadderError P M Q η L).norm).pow 2
  have hpt : ∀ w : ℝ, ‖ramareBilinear P M w‖ ^ (2 : ℕ)
      ≤ 2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ))
        + 2 * ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ) := by
    intro w
    rw [ramareBilinear_eq_ladder_add_error M hQ hη hL hP w]
    have hsum : ‖∑ j ∈ Finset.range L, F j w‖ ^ (2 : ℕ)
        ≤ (L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ) := by
      have h1 : ‖∑ j ∈ Finset.range L, F j w‖ ≤ ∑ j ∈ Finset.range L, ‖F j w‖ :=
        norm_sum_le _ _
      have h2 : (∑ j ∈ Finset.range L, ‖F j w‖) ^ (2 : ℕ)
          ≤ ((Finset.range L).card : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ) :=
        sq_sum_le_card_mul_sum_sq
      rw [Finset.card_range] at h2
      exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
    have htri := norm_add_le (∑ j ∈ Finset.range L, F j w) (ramareLadderError P M Q η L w)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, hsum, sq_nonneg (‖∑ j ∈ Finset.range L, F j w‖
      - ‖ramareLadderError P M Q η L w‖), norm_nonneg (ramareLadderError P M Q η L w),
      norm_nonneg (∑ j ∈ Finset.range L, F j w)]
  have hcontZ : Continuous fun w : ℝ => ‖ramareBilinear P M w‖ ^ (2 : ℕ) :=
    ((continuous_ramareBilinear P M).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ))
        + 2 * ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ) :=
    (((continuous_finsetSum _ fun j _ => hcontF j).const_mul _).const_mul 2).add
      (hcontE.const_mul 2)
  have hintZ : IntegrableOn (fun w : ℝ => ‖ramareBilinear P M w‖ ^ (2 : ℕ)) E volume :=
    (hcontZ.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintR : IntegrableOn (fun w : ℝ =>
      2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ))
        + 2 * ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ)) E volume :=
    (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintFj : ∀ j ∈ Finset.range L,
      IntegrableOn (fun w : ℝ => ‖F j w‖ ^ (2 : ℕ)) E volume := fun j _ =>
    ((hcontF j).integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintSum : IntegrableOn (fun w : ℝ => ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ)) E volume :=
    ((continuous_finsetSum _ fun j _ => hcontF j).integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintErr : IntegrableOn (fun w : ℝ => ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ)) E volume :=
    (hcontE.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hintZ hintR hEm (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add ((hintSum.const_mul _).const_mul 2) (hintErr.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul,
    MeasureTheory.integral_finsetSum _ hintFj]
  ring

/-- **The Ramaré ladder over a frequency set, paid by a prime sup and a cofactor mean square.**
This is the orientation the exceptional half needs when the prime range is high enough for a
zero-free-region bound: the pointwise saving lives on the prime blocks and the smallness of the set
is spent on the long polynomial.  The discrepancy is paid once, not per block. -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_supMeanSquare {P : Finset ℕ} (M : ℕ)
    {Q η W : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (V I : ℕ → ℝ)
    (hbound : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hI : ∀ j ∈ Finset.range L,
      (∫ w in E, ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ)) ≤ I j) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L, V j ^ (2 : ℕ) * I j
        + 2 * ∫ w in E, ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ) := by
  refine le_trans (setIntegral_normSq_ramareBilinear_le_ladder_error (P := P) M hQ hη hL hP
    hEm hEs) ?_
  have hstep : ∑ j ∈ Finset.range L,
      (∫ w in E, ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
          * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range L, V j ^ (2 : ℕ) * I j :=
    Finset.sum_le_sum fun j hj =>
      setIntegral_normSq_blockProduct_le_supMeanSquare (ramareCofactorCoeff P)
        (geomBlock P Q (1 + η) j) (geomCofactorBlock M Q η j) hEm hEs (hbound j hj) (hI j hj)
  have hL0 : (0 : ℝ) ≤ 2 * (L : ℝ) := by positivity
  linarith [mul_le_mul_of_nonneg_left hstep hL0]

/-- **The Ramaré ladder over a frequency set, paid by a prime sup and the mean value theorem.**
This is the non-exceptional orientation: on the set where every prime block is small by definition,
the cofactor needs no arithmetic at all. -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_sup {P : Finset ℕ} (M : ℕ)
    {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (V : ℕ → ℝ) (hV0 : ∀ j, 0 ≤ V j)
    (hbound : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
          V j ^ (2 : ℕ) * ((5 * Real.pi / 2 * W
                + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
              * ((geomCofactorBlock M Q η j).card : ℝ))
        + 2 * ∫ w in E, ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  refine le_trans (setIntegral_normSq_ramareBilinear_le_ladder_error (P := P) M hQ0 hη hL hP
    hEm hEs) ?_
  have hstep : ∑ j ∈ Finset.range L,
      (∫ w in E, ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
          * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range L,
          V j ^ (2 : ℕ) * ((5 * Real.pi / 2 * W
                + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
              * ((geomCofactorBlock M Q η j).card : ℝ)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hbounds := geomCofactorBlockAt_bounds (A₀ := 1) (B₀ := M) (by norm_num) hQ0 hη j
    exact integral_normSq_blockProduct_set_le (ramareCofactorCoeff P)
      (norm_ramareCofactorCoeff_le_one P) (geomBlock P Q (1 + η) j) (geomCofactorBlock M Q η j)
      hbounds.1 hbounds.2 hW (hV0 j) hEm hEs (hbound j hj)
  have hL0 : (0 : ℝ) ≤ 2 * (L : ℝ) := by positivity
  linarith [mul_le_mul_of_nonneg_left hstep hL0]

end

end RHTower.Sieve
