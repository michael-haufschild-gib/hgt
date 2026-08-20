import GaloisForLFunctions.RHTower.Sieve.Section4QSide

/-!
# The ladder with the roles of the two factors exchanged

`Sieve/Section4QSide.setIntegral_normSq_omegaWeighted_le_blocks` bounds each ladder step by the
supremum of the *prime* polynomial times the mean square of the cofactor.  On the exceptional set
of the frequency partition that is the wrong way round: there the prime polynomial is by definition
*large*, and what is small is the cofactor — by the zero-free region, super-polylogarithmically
(`Sieve/RouteTDampedTwistRate`).  The mean square that remains is then the prime polynomial's,
which the prime-supported Halász–Montgomery bound of `Sieve/HalaszMontgomerySupport` controls in
terms of the measure of the exceptional set.

Both estimates start from the same symmetric ladder
`Sieve/Section4QSide.setIntegral_normSq_omegaWeighted_le_ladder`; only the choice of which factor
to take out in the supremum differs.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The long ladder with the supremum on the cofactor.**  The dual of
`setIntegral_normSq_omegaWeighted_le_blocks`. -/
theorem setIntegral_normSq_omegaWeighted_le_blocks_cofactorSup {Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range L, 0 < v k) (Ck Jk : ℕ → ℝ)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hCk : ∀ k ∈ Finset.range L, ∀ w ∈ E,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ≤ Ck k)
    (hJk : ∀ k ∈ Finset.range L,
      (∫ w in E, ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ^ 2) ≤ Jk k) :
    (∫ w in E, ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ 2)
      ≤ 2 * ((∑ k ∈ Finset.range L, 1 / v k)
            * ∑ k ∈ Finset.range L, v k * (Ck k ^ 2 * Jk k))
        + 2 * ∫ w in E, ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ 2 := by
  classical
  have hstep2 := setIntegral_normSq_omegaWeighted_le_ladder (Q := Q) (A₁ := A₁) (B₁ := B₁)
    hR hη hL hQprime hQrange v hv hEm hEs
  have hblock : ∀ k ∈ Finset.range L,
      v k * (∫ w in E, ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ^ 2
              * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ 2)
        ≤ v k * (Ck k ^ 2 * Jk k) := by
    intro k hk
    refine mul_le_mul_of_nonneg_left ?_ (hv k hk).le
    have hcomm : (∫ w in E, ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ^ 2
            * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ 2)
        = ∫ w in E, ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ 2
            * ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ^ 2 :=
      MeasureTheory.setIntegral_congr_fun hEm fun w _ => by ring
    rw [hcomm]
    have hb := setIntegral_normSq_mul_le_of_bound
      (F := fun w => logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w)
      (G := fun w => primeBlockPoly (geomBlock Q R (1 + η) k) w)
      (continuous_logPoly _ _) (continuous_primeBlockPoly _) hEm hEs (hCk k hk)
    exact hb.trans (mul_le_mul_of_nonneg_left (hJk k hk) (sq_nonneg _))
  have hsum := Finset.sum_le_sum hblock
  have hmass : (0 : ℝ) ≤ ∑ k ∈ Finset.range L, 1 / v k :=
    Finset.sum_nonneg fun k hk => div_nonneg zero_le_one (hv k hk).le
  refine hstep2.trans ?_
  have := mul_le_mul_of_nonneg_left hsum hmass
  linarith [this]

end

end RHTower.Sieve
