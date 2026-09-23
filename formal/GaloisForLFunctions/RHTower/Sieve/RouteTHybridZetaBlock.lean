import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSigma
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaBlock

/-!
# The hybrid Route-T zeta block

Route T is strongest when the height is very large relative to the block.  The classical
derivative-test schedule is strongest in the complementary regime.  This file puts both estimates
on the same actual zeta block, with no change of phase or endpoint convention.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The Route-T half-open block is exactly the standard `Ico` block after shifting both endpoints. -/
theorem routeTZetaBlockSum_eq_Ico (X X' : ℕ) (σ t : ℝ) :
    routeTZetaBlockSum X X' σ t =
      ∑ n ∈ Finset.Ico (X + 1) (X' + 1),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ)) := by
  have hinterval : Finset.Ioc X X' = Finset.Ico (X + 1) (X' + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [routeTZetaBlockSum, hinterval]
  apply Finset.sum_congr rfl
  intro n _hn
  congr 1
  ring

/-- The derivative-test schedule, transported to the exact Route-T zeta block. -/
theorem norm_routeTZetaBlockSum_le_derivativeSchedule
    {X X' k₀ : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (ht : 0 < t) (hXX' : X < X') (hX' : X' ≤ 2 * X)
    (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ X + 1)
    (hlow : 8 * Real.pi * ((X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * ((X + 1 : ℕ) : ℝ) ^ (k₀ - 1)
      * ((X + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖routeTZetaBlockSum X X' σ t‖ ≤
      2560 * ((X + 1 : ℕ) : ℝ) ^ (1 - σ)
        * ((X + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
  rw [routeTZetaBlockSum_eq_Ico]
  exact dirichlet_block_sigma_saving_of_small_factorial hσ ht
    (by omega) (by omega) (by omega) hk₀ hfac hlow hhigh

/-- Fixed-order low-shell receiver.  Order `562` covers every block satisfying the elementary
height window; its saving exponent is absolute and independent of `t`. -/
theorem norm_routeTZetaBlockSum_le_lowShell
    {X X' : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (ht : 0 < t) (hXX' : X < X') (hX' : X' ≤ 2 * X)
    (hfac : Nat.factorial 561 ≤ X + 1)
    (hlow : 8 * Real.pi * ((X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ (562 : ℕ) * ((X + 1 : ℕ) : ℝ) ^ (561 : ℕ)
      * ((X + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖routeTZetaBlockSum X X' σ t‖ ≤
      2560 * ((X + 1 : ℕ) : ℝ) ^ (1 - σ)
        * ((X + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ (562 : ℕ)))) := by
  exact norm_routeTZetaBlockSum_le_derivativeSchedule hσ ht hXX' hX'
    (by norm_num) hfac hlow (by simpa using hhigh)

/-- An order two above a height power automatically satisfies the derivative-test upper window. -/
theorem routeT_lowShell_high_of_le_pow
    {N q : ℕ} {t : ℝ} (hN : 1 ≤ N) (htop : t ≤ (N : ℝ) ^ q) :
    t ≤ 2 * Real.pi * 2 ^ (q + 2) * (N : ℝ) ^ (q + 1)
      * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hpow : (N : ℝ) ^ q ≤
      (N : ℝ) ^ (q + 1) * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
    rw [← Real.rpow_natCast (N : ℝ) q, ← Real.rpow_natCast (N : ℝ) (q + 1),
      ← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    push_cast
    norm_num
  have hprod0 : 0 ≤ (N : ℝ) ^ (q + 1) * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
    positivity
  have hconst : (1 : ℝ) ≤ 2 * Real.pi * 2 ^ (q + 2) := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (q + 2) := one_le_pow₀ (by norm_num)
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact one_le_mul_of_one_le_of_one_le hpi hp
  calc
    t ≤ (N : ℝ) ^ q := htop
    _ ≤ (N : ℝ) ^ (q + 1) * (N : ℝ) ^ (-(1 / 3) : ℝ) := hpow
    _ ≤ (2 * Real.pi * 2 ^ (q + 2)) *
        ((N : ℝ) ^ (q + 1) * (N : ℝ) ^ (-(1 / 3) : ℝ)) := by
      exact le_mul_of_one_le_left hprod0 hconst
    _ = 2 * Real.pi * 2 ^ (q + 2) * (N : ℝ) ^ (q + 1)
        * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
      exact (mul_assoc _ _ _).symm

/-- Fixed-order receiver stated only with the natural complementary condition `t ≤ (X+1)^(560 : ℕ)`. -/
theorem norm_routeTZetaBlockSum_le_lowShell_of_le_pow
    {X X' : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (ht : 0 < t) (hXX' : X < X') (hX' : X' ≤ 2 * X)
    (hfac : Nat.factorial 561 ≤ X + 1)
    (hlow : 8 * Real.pi * ((X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (htop : t ≤ (((X + 1 : ℕ) : ℝ) ^ (560 : ℕ))) :
    ‖routeTZetaBlockSum X X' σ t‖ ≤
      2560 * ((X + 1 : ℕ) : ℝ) ^ (1 - σ)
        * ((X + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ (562 : ℕ)))) := by
  apply norm_routeTZetaBlockSum_le_lowShell hσ ht hXX' hX' hfac hlow
  exact routeT_lowShell_high_of_le_pow (q := 560) (by omega) htop

/-- **Automatic hybrid receiver.**  Every threshold-eligible block is controlled without a height
gap.  Above the `141`-shell boundary Route T gives reciprocal-quartic decay.  Below that boundary,
the same root-cell inequality puts the height below `(X+1)^(564 : ℕ)`, where derivative order `566`
gives an absolute power saving. -/
theorem norm_routeTZetaBlockSum_le_automaticHybrid
    {X X' : ℕ} {σ t : ℝ}
    (hX : 1 ≤ X) (hσ : 0 ≤ σ) (ht : 1 < t)
    (hXsize : 2 ^ (routeTLogCentreExponent *
        (routeTLogReceiverDegreeNineConstant *
          (routeTLogRealShellIndex X t + 1) ^ 9 + 1)) ≤ X)
    (hXX' : X < X') (hX' : X' ≤ 2 * X)
    (hfac : Nat.factorial 565 ≤ X + 1)
    (hlow : 8 * Real.pi * ((X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t) :
    ‖routeTZetaBlockSum X X' σ t‖ ≤
      if (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
          (4 * 141) : ℕ) : ℝ) < t then
        (6912 * Real.exp ((1 - σ) * Real.log (X + 1) -
          (1 / (5000000000000000 *
            (routeTLogRealShellIndex X t : ℝ) ^ 4)) *
              (Real.log X - 200 * Real.log 2)))
      else (2560 * ((X + 1 : ℕ) : ℝ) ^ (1 - σ) *
          ((X + 1 : ℕ) : ℝ) ^
            (-(1 / (3 * (2 : ℝ) ^ (566 : ℕ))))) := by
  have hB2 : 2 ≤ routeTLogRootBase X :=
    routeTLogRootBase_ge_two_of_degreeNine_size hXsize
  obtain ⟨_hbottom, htop⟩ := routeTLogRealShellIndex_bounds hB2 ht
  by_cases hlarge :
      (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
        (4 * 141) : ℕ) : ℝ) < t
  · rw [if_pos hlarge]
    exact norm_routeTZetaBlockSum_le_explicitExponential hX hXsize hlarge htop
      hXX' hX' hσ
  · have htroot : t ≤
        (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
          (4 * 141) : ℕ) : ℝ) := le_of_not_gt hlarge
    obtain ⟨hrootX, _hXroot⟩ := routeTLogRootBase_cell hB2
    have hrootSucc : routeTLogRootBase X ^ routeTLogCentreExponent ≤ X + 1 :=
      hrootX.trans (Nat.le_succ X)
    have hpowNat :
        (routeTLogRootBase X ^ routeTLogCentreExponent) ^ (4 * 141) ≤
          (X + 1) ^ (4 * 141) := Nat.pow_le_pow_left hrootSucc _
    have hpowReal :
        (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
          (4 * 141) : ℕ) : ℝ) ≤ (((X + 1 : ℕ) : ℝ) ^ (564 : ℕ)) := by
      exact_mod_cast hpowNat
    have htX : t ≤ (((X + 1 : ℕ) : ℝ) ^ (564 : ℕ)) := htroot.trans hpowReal
    have hhigh : t ≤ 2 * Real.pi * 2 ^ (566 : ℕ) *
        ((X + 1 : ℕ) : ℝ) ^ (565 : ℕ) *
          ((X + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
      simpa using routeT_lowShell_high_of_le_pow (q := 564) (N := X + 1)
        (by omega) htX
    have hderivative := norm_routeTZetaBlockSum_le_derivativeSchedule
      hσ (lt_trans zero_lt_one ht) hXX' hX' (k₀ := 566) (by norm_num)
      (by simpa using hfac) hlow hhigh
    rw [if_neg hlarge]
    exact hderivative

end

end RHTower.Sieve
