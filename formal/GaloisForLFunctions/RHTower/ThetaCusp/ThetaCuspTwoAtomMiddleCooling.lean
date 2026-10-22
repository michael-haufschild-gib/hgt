import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleAbsoluteCooling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomReflectedBounds

/-! # Uniform derivatives of the retained two-atom partition -/
open Filter Topology
namespace RHTower
noncomputable section

/-- Exact retained partition as the complete likelihood with its deep tail removed. -/
theorem thetaCuspTwoAtomLikelihoodPartition_eq_one_add_sub {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomLikelihoodPartition x =
      1+thetaCuspLikelihoodSourceRemainder x-thetaCuspDeepLikelihoodRemainder x := by
  have he := thetaCuspFullSource_sub_two_eq_first_mul_deep hx
  rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition
    (thetaCuspLikelihoodCoordinate_pos hx.le)] at he
  unfold thetaCuspTwoAtomLikelihoodPartition thetaCuspLikelihoodSourceRemainder
  apply (div_eq_iff (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne').mpr
  nlinarith only [he]

/-- Derivatives of the exact two-atom partition retain the constant only at order zero. -/
theorem iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_eq (n : ℕ) {x : ℝ}
    (hx : 0 < x) : iteratedDeriv n thetaCuspTwoAtomLikelihoodPartition x =
      (0 : ℝ)^n+iteratedDeriv n thetaCuspLikelihoodSourceRemainder x-
        iteratedDeriv n thetaCuspDeepLikelihoodRemainder x := by
  have he : thetaCuspTwoAtomLikelihoodPartition =ᶠ[𝓝 x]
      (fun y => 1+thetaCuspLikelihoodSourceRemainder y-thetaCuspDeepLikelihoodRemainder y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact thetaCuspTwoAtomLikelihoodPartition_eq_one_add_sub hy
  have hr : ContDiffAt ℝ n thetaCuspLikelihoodSourceRemainder x :=
    (contDiffAt_thetaCuspLikelihoodSourceRemainder hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hd : ContDiffAt ℝ n thetaCuspDeepLikelihoodRemainder x :=
    (contDiffAt_thetaCuspDeepLikelihoodRemainder hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  rw [he.iteratedDeriv_eq, iteratedDeriv_fun_sub (contDiffAt_const.add hr) hd,
    iteratedDeriv_fun_add contDiffAt_const hr, iteratedDeriv_const]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, zero_pow hn]

/-- All retained derivatives through order ten admit the same complete middle majorant. -/
theorem abs_iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_le_middle
    {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspTwoAtomLikelihoodPartition x| ≤
      (0 : ℝ)^n+(6*thetaCuspSingleAtomReflectionScale 1 x)^n/100+
        2*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x := by
  rw [iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_eq n
    (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  have hr := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_middle hn hq
  have hd := abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le hn hq
  have ha : |(0 : ℝ)^n+iteratedDeriv n thetaCuspLikelihoodSourceRemainder x-
      iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      |(0 : ℝ)^n|+|iteratedDeriv n thetaCuspLikelihoodSourceRemainder x|+
        |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| :=
    (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_of_nonneg (pow_nonneg (le_refl (0 : ℝ)) n)] at ha
  linarith

end
end RHTower
