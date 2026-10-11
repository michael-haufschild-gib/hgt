import GaloisForLFunctions.RHTower.XiSliceHeatTransferNoSlack
import GaloisForLFunctions.RHTower.XiSliceLowestCoeffPositive
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# Negative heat fails at every real zero of `Ξ`

**Theorem** (`not_forall_xiSliceHeatTransfer_nonneg_of_real_zero`).  Let `λ < 0` and let `γ` be a real
zero of `Ξ`.  Then some heated slice coefficient `T_n(λ, 0, γ)` is not `≥ 0`.

Proof.  Let `k ≥ 1` be the order of the zero, so `c_n(γ) = 0` for `n < 2k` and `c_{2k}(γ) > 0`
(`xiSliceCoeff_lowest_of_factor`).  The heat shift from `λ` to `0` writes every slice coefficient as
a positive combination of heated coefficients,
`c_n(γ) = Σ_j (−λ/2)^j/j! · (n+2j)!/n! · T_{n+2j}(λ, 0, γ)` (`hasSum_xiSliceHeatTransfer_shift`).
If all `T_m(λ, 0, γ) ≥ 0`, the identity at `n = 2k − 2` (where `c_n(γ) = 0`) forces
`T_{2k−2+2j}(λ, 0, γ) = 0` for every `j`.  The identity at `n = 2k` then gives `c_{2k}(γ) = 0`, a
contradiction.

So for negative heat the WD failure set contains every real zero of `Ξ`.  With Hardy's real zeros this
gives `λ_WD ≥ 0` (`wdHeatThreshold_nonneg_of_real_zeros`) from the shift identity alone.  The
corpus argument (`nonneg_of_forall_xiSliceHeatTransfer_nonneg`) goes through the transform of the
kernel instead.
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-- At heat `0` the transfer is the slice coefficient. -/
theorem xiSliceHeatTransfer_zero_eq (t : ℝ) (n : ℕ) :
    xiSliceHeatTransfer 0 0 t n = xiSliceCoeff t n := by
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment le_rfl 0 t n
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have hsingle : HasSum (fun k : ℕ => ((((0 : ℝ) / 2) ^ k / k.factorial *
      ((n + 2 * k).factorial / n.factorial) : ℝ) : ℂ) * xiSliceCoeff t (n + 2 * k))
      (xiSliceCoeff t n) := by
    have e : (fun k : ℕ => ((((0 : ℝ) / 2) ^ k / k.factorial *
        ((n + 2 * k).factorial / n.factorial) : ℝ) : ℂ) * xiSliceCoeff t (n + 2 * k)) =
        fun k => if k = 0 then xiSliceCoeff t n else 0 := by
      funext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
        simp [hn]
      · rw [if_neg hk.ne', zero_div, zero_pow hk.ne', zero_div, zero_mul, Complex.ofReal_zero,
          zero_mul]
    rw [e]
    exact hasSum_ite_eq 0 _
  exact hT.unique hsingle

/-- **Negative heat fails at every real zero of `Ξ`.** -/
theorem not_forall_xiSliceHeatTransfer_nonneg_of_real_zero {lam : ℝ} (hlam : lam < 0) {γ : ℝ}
    (hγ : XiC (γ : ℂ) = 0) : ¬ ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 γ n := by
  intro hall
  obtain ⟨k, hlow, hpos⟩ := exists_lowest_xiSliceCoeff_pos γ
  -- the zero has positive order
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst hk0
    have hc0 : xiSliceCoeff γ 0 = 0 := by
      unfold xiSliceCoeff
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
      rw [xiSliceProduct_eq_XiC, mul_zero, sub_zero, add_zero, hγ, zero_mul]
    rw [show 2 * 0 = 0 by rfl, hc0] at hpos
    exact lt_irrefl _ hpos
  -- the heat shift from `λ` to `0`
  have hshift : ∀ n : ℕ, HasSum (fun j : ℕ => ((((0 - lam) / 2) ^ j / j.factorial *
      ((n + 2 * j).factorial / n.factorial) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 γ (n + 2 * j))
      (xiSliceCoeff γ n) := fun n => by
    have h := hasSum_xiSliceHeatTransfer_shift hlam.le 0 γ n
    rwa [xiSliceHeatTransfer_zero_eq] at h
  have hcoef_pos : ∀ n j : ℕ, 0 < ((0 - lam) / 2) ^ j / j.factorial *
      ((n + 2 * j).factorial / n.factorial : ℝ) := fun n j => by
    have : 0 < (0 - lam) / 2 := by linarith
    positivity
  have hterm_nonneg : ∀ n j : ℕ, 0 ≤ ((((0 - lam) / 2) ^ j / j.factorial *
      ((n + 2 * j).factorial / n.factorial) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 γ (n + 2 * j) :=
    fun n j => mul_nonneg (Complex.zero_le_real.mpr (hcoef_pos n j).le) (hall _)
  -- at `n = 2k − 2` every heated term vanishes
  have hzero : ∀ j : ℕ, xiSliceHeatTransfer lam 0 γ (2 * (k - 1) + 2 * j) = 0 := by
    have h := hshift (2 * (k - 1))
    rw [hlow (2 * (k - 1)) (by omega)] at h
    have hfun := (hasSum_zero_iff_of_nonneg (hterm_nonneg (2 * (k - 1)))).mp h
    intro j
    have hj := congrFun hfun j
    simp only [Pi.zero_apply] at hj
    have hne : ((((0 - lam) / 2) ^ j / j.factorial *
        ((2 * (k - 1) + 2 * j).factorial / (2 * (k - 1)).factorial) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hcoef_pos _ j).ne'
    exact (mul_eq_zero.mp hj).resolve_left hne
  -- then `c_{2k}(γ) = 0`
  have h2k := hshift (2 * k)
  have hfun : (fun j : ℕ => ((((0 - lam) / 2) ^ j / j.factorial *
      ((2 * k + 2 * j).factorial / (2 * k).factorial) : ℝ) : ℂ) *
        xiSliceHeatTransfer lam 0 γ (2 * k + 2 * j)) = fun _ => 0 := by
    funext j
    have := hzero (j + 1)
    rw [show 2 * (k - 1) + 2 * (j + 1) = 2 * k + 2 * j by omega] at this
    rw [this, mul_zero]
  rw [hfun] at h2k
  have := h2k.unique hasSum_zero
  rw [this] at hpos
  exact lt_irrefl _ hpos

/-- **`λ_WD ≥ 0` from the real zeros of `Ξ`.**  Every negative heat fails at a real zero. -/
theorem wdHeatThreshold_nonneg_of_real_zeros : 0 ≤ wdHeatThreshold := by
  obtain ⟨a, -, -, -, -, ha, -⟩ := exists_two_distinct_positive_real_XiC_zeros
  refine le_csInf ⟨_, eighth_mem_wdHeatAdmissible⟩ fun lam hlam => ?_
  by_contra hneg
  push Not at hneg
  exact not_forall_xiSliceHeatTransfer_nonneg_of_real_zero hneg ha fun n => hlam a n

end

end RHTower.DeBruijn
