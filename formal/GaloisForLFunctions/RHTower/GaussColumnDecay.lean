import GaloisForLFunctions.RHTower.GaussIterateNormBound
import GaloisForLFunctions.RHTower.GaussConjugationSymmetry
import GaloisForLFunctions.RHTower.GaussRelativePower

/-!
# The columns of `G^m` decay faster than every power below one

`G^m e_n = (p |d_n|²)^m · e_n · (R_n^m 1)` exactly, and multiplication by the exponential monomial
is a contraction.  Since `|d_n|^{2m} ≲ 1/|n|` and `‖R_n^m 1‖ ≲ (1+|n|)^ρ` for every `ρ > 0`, the
columns satisfy `‖G^m e_n‖ ≲ |n|^{-1+ρ}`.

Conjugation symmetry reduces negative frequencies to positive ones.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-! ## Conjugation is isometric -/

theorem norm_star_lp (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖star u‖ = ‖u‖ := by
  have h := inner_star_star u u
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ((‖star u‖ : ℝ) : ℂ) ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    refine h.trans ?_
    simp
  have h2 : ‖star u‖ ^ 2 = ‖u‖ ^ 2 := by exact_mod_cast h'
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

theorem norm_gaussQuasiInnerG_pow_fourierLp_natAbs (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (r : ℕ) (n : ℤ) :
    ‖(gaussQuasiInnerG hm k p ^ r) (fourierLp 2 n)‖
      = ‖(gaussQuasiInnerG hm k p ^ r) (fourierLp 2 ((n.natAbs : ℤ)))‖ := by
  rcases le_or_gt 0 n with h | h
  · rw [Int.natAbs_of_nonneg h]
  · have hneg : ((n.natAbs : ℤ)) = -n := by omega
    rw [hneg]
    have h1 : (fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
        = star (fourierLp 2 (-n)) := by
      rw [star_fourierLp]
      norm_num
    rw [h1, ← star_gaussQuasiInnerG_pow, norm_star_lp]

/-! ## The exact column identity -/

theorem norm_gaussQuasiInnerG_pow_fourierLp_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {n : ℤ} (hn : n ≠ 0) (r : ℕ) :
    ‖(gaussQuasiInnerG hm k p ^ r) (fourierLp 2 n)‖
      ≤ ((p : ℝ) * ‖gaussSampleValue k p n‖ ^ 2) ^ r
        * ‖(gaussPrincipalStepBlock hm k p hp n ^ r)
            (fourierLp 2 (0 : ℤ))‖ := by
  rw [← fourierMulBlock_fourierLp_zero n, gaussQuasiInnerG_pow_fourierMulBlock hm k p hp hn,
    norm_smul, norm_pow, norm_gaussStepScalar_conj_eq]
  refine mul_le_mul_of_nonneg_left (norm_fourierMulBlock_apply_le n _) ?_
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  positivity

/-! ## The sampled magnitude bound at every nonzero integer -/

theorem exists_norm_gaussSampleValue_pow_mul_natAbs_le (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
      ‖gaussSampleValue k p n‖ ^ (2 * m) * (n.natAbs : ℝ) ≤ C := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm k p
  refine ⟨K * (‖gaussSampleValue k p 1‖ ^ (2 * m) * (((1 : ℤ)).natAbs : ℝ)), by positivity,
    fun n hn => hKb n 1 hn one_ne_zero⟩

/-! ## The column decay -/

set_option maxHeartbeats 1000000 in
/-- **Column decay of the critical power.**  For every `ρ > 0` the columns of `G^m` in the Fourier
basis satisfy `‖G^m e_n‖ ≤ C |n|^{-1+ρ}`. -/
theorem exists_norm_gaussQuasiInnerG_pow_fourierLp_le (hm : 1 ≤ m) (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
      ‖(gaussQuasiInnerG hm k p ^ m) (fourierLp 2 n)‖
        ≤ C * ((n.natAbs : ℝ)) ^ (-1 + ρ) := by
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  set ρ' : ℝ := min ρ 1 with hρ'def
  have hρ'0 : 0 < ρ' := lt_min hρ one_pos
  have hρ'1 : ρ' ≤ 1 := min_le_right _ _
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_gaussSampleValue_pow_mul_natAbs_le hm k p
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_gaussPrincipalStep_pow_le hm hm2 k p hp hρ'0
  set G : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := gaussQuasiInnerG hm k p with hGdef
  refine ⟨max (‖G ^ m‖) (2 * (p : ℝ) ^ m * C₁ * C₂), le_max_of_le_left (norm_nonneg _),
    fun n hn => ?_⟩
  have hbasis : ‖(fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖ = 1 := by
    have hb : (fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
        = (fourierBasis (T := (1 : ℝ))) n := by rw [coe_fourierBasis]
    rw [hb]
    exact (fourierBasis (T := (1 : ℝ))).orthonormal.1 n
  have hnat1 : 1 ≤ n.natAbs := by omega
  have hnatR : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hnat1
  have hnatpos : (0 : ℝ) < (n.natAbs : ℝ) := by linarith
  by_cases hsmall : n.natAbs < 2
  · -- `|n| = 1`
    have hn1 : n.natAbs = 1 := by omega
    have hpow : ((n.natAbs : ℝ)) ^ (-1 + ρ) = 1 := by
      rw [hn1]
      norm_num
    rw [hpow, mul_one]
    refine le_trans ?_ (le_max_left _ _)
    have h := (G ^ m).le_opNorm (fourierLp 2 n)
    rw [hbasis, mul_one] at h
    exact h
  · push_neg at hsmall
    -- reduce to the nonnegative frequency
    rw [norm_gaussQuasiInnerG_pow_fourierLp_natAbs hm k p m n]
    have hnz : ((n.natAbs : ℤ)) ≠ 0 := by omega
    have hstep := norm_gaussQuasiInnerG_pow_fourierLp_le hm k p hp hnz m
    have hR := hC₂ n.natAbs hsmall
    have hd := hC₁ ((n.natAbs : ℤ)) hnz
    have hdabs : (((n.natAbs : ℤ)).natAbs : ℝ) = (n.natAbs : ℝ) := by
      norm_num
    rw [hdabs] at hd
    -- `(p |d|²)^m = p^m (|d|^{2m})`
    have hscal : ((p : ℝ) * ‖gaussSampleValue k p ((n.natAbs : ℤ))‖ ^ 2) ^ m
        = (p : ℝ) ^ m * ‖gaussSampleValue k p ((n.natAbs : ℤ))‖ ^ (2 * m) := by
      rw [mul_pow, ← pow_mul]
    have hd2 : ‖gaussSampleValue k p ((n.natAbs : ℤ))‖ ^ (2 * m) ≤ C₁ / (n.natAbs : ℝ) := by
      rw [le_div_iff₀ hnatpos]
      exact hd
    have hone : (1 : ℝ) + (n.natAbs : ℝ) ≤ 2 * (n.natAbs : ℝ) := by linarith
    have hbnd : (1 + (n.natAbs : ℝ)) ^ ρ' ≤ 2 * ((n.natAbs : ℝ)) ^ ρ' := by
      have h1 : (1 + (n.natAbs : ℝ)) ^ ρ' ≤ (2 * (n.natAbs : ℝ)) ^ ρ' :=
        Real.rpow_le_rpow (by positivity) hone hρ'0.le
      have h2 : (2 * (n.natAbs : ℝ)) ^ ρ' = (2 : ℝ) ^ ρ' * ((n.natAbs : ℝ)) ^ ρ' :=
        Real.mul_rpow (by norm_num) hnatpos.le
      have h3 : (2 : ℝ) ^ ρ' ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hρ'1
        rwa [Real.rpow_one] at h
      have h4 : (0 : ℝ) ≤ ((n.natAbs : ℝ)) ^ ρ' := Real.rpow_nonneg hnatpos.le _
      nlinarith [h1, h2.le, h2.ge, h3, h4]
    have hchain : ‖(gaussQuasiInnerG hm k p ^ m) (fourierLp 2 ((n.natAbs : ℤ)))‖
        ≤ (p : ℝ) ^ m * (C₁ / (n.natAbs : ℝ)) * (C₂ * (2 * ((n.natAbs : ℝ)) ^ ρ')) := by
      refine le_trans hstep ?_
      rw [hscal]
      have hA : (p : ℝ) ^ m * ‖gaussSampleValue k p ((n.natAbs : ℤ))‖ ^ (2 * m)
          ≤ (p : ℝ) ^ m * (C₁ / (n.natAbs : ℝ)) :=
        mul_le_mul_of_nonneg_left hd2 (by positivity)
      have hB : ‖(gaussPrincipalStepBlock hm k p hp ((n.natAbs : ℤ)) ^ m)
          (fourierLp 2 (0 : ℤ))‖ ≤ C₂ * (2 * ((n.natAbs : ℝ)) ^ ρ') := by
        refine le_trans hR ?_
        exact mul_le_mul_of_nonneg_left hbnd hC₂0
      have hAn : (0 : ℝ) ≤ (p : ℝ) ^ m * ‖gaussSampleValue k p ((n.natAbs : ℤ))‖ ^ (2 * m) := by
        positivity
      have hBn : (0 : ℝ) ≤ ‖(gaussPrincipalStepBlock hm k p hp ((n.natAbs : ℤ)) ^ m)
          (fourierLp 2 (0 : ℤ))‖ := norm_nonneg _
      nlinarith [hA, hB, hAn, hBn]
    refine le_trans hchain ?_
    -- rewrite the right-hand side as the constant times `|n|^{-1+ρ}`
    have hpowid : (C₁ / (n.natAbs : ℝ)) * ((n.natAbs : ℝ)) ^ ρ'
        = C₁ * ((n.natAbs : ℝ)) ^ (-1 + ρ') := by
      have hinv : ((n.natAbs : ℝ)) ^ (-1 + ρ')
          = ((n.natAbs : ℝ)) ^ (-1 : ℝ) * ((n.natAbs : ℝ)) ^ ρ' :=
        Real.rpow_add hnatpos _ _
      rw [hinv, Real.rpow_neg_one]
      field_simp
    have hmono : ((n.natAbs : ℝ)) ^ (-1 + ρ') ≤ ((n.natAbs : ℝ)) ^ (-1 + ρ) :=
      Real.rpow_le_rpow_of_exponent_le hnatR (by linarith)
    have hfinal : (p : ℝ) ^ m * (C₁ / (n.natAbs : ℝ)) * (C₂ * (2 * ((n.natAbs : ℝ)) ^ ρ'))
        = (2 * (p : ℝ) ^ m * C₁ * C₂) * ((n.natAbs : ℝ)) ^ (-1 + ρ') := by
      have h := hpowid
      field_simp at h ⊢
      nlinarith [h]
    rw [hfinal]
    have hc0 : (0 : ℝ) ≤ 2 * (p : ℝ) ^ m * C₁ * C₂ := by positivity
    calc (2 * (p : ℝ) ^ m * C₁ * C₂) * ((n.natAbs : ℝ)) ^ (-1 + ρ')
        ≤ (2 * (p : ℝ) ^ m * C₁ * C₂) * ((n.natAbs : ℝ)) ^ (-1 + ρ) :=
          mul_le_mul_of_nonneg_left hmono hc0
      _ ≤ max (‖G ^ m‖) (2 * (p : ℝ) ^ m * C₁ * C₂) * ((n.natAbs : ℝ)) ^ (-1 + ρ) := by
          refine mul_le_mul_of_nonneg_right (le_max_right _ _) ?_
          positivity

end

end RHTower
