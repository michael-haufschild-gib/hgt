import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaCutoffCommutatorKernel
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaWallHardyBoundary
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The literal Gamma cutoff commutator and the physical wall block norm

The Gamma jump operator is the second-difference average against the kernel `1/(e^s-1)`.  Its
commutator with a cutoff `χ` never sees the singularity at the origin, because the diagonal terms
cancel and the surviving cutoff differences are Lipschitz:

`[R,χ]F(L) = ∫₀^∞ (χ(L)-χ(L+s))F(L+s) + (χ(L)-χ(L-s))F(L-s) ds/(e^s-1)`.

Three consequences are proved here for a cutoff which vanishes on `(-∞,0]`, is one on `[1,∞)` and is
`Λ`-Lipschitz, and for a bounded `X`-valued `F`:

* the uniform bound `‖[R,χ]F‖_∞ ≤ 8Λ‖F‖_∞`;
* the two-sided exponential wall `‖[R,χ]F(L)‖ ≤ 24Λ‖F‖_∞ e^{-|L|}` for `|L| ≥ 2`, which holds
  because outside a distance-one collar of the cutoff step every cutoff difference vanishes
  identically, so only the tail `s ≥ |L|-1` of the kernel contributes;
* finiteness of the physical block norm

  `N_σ(G) = Σ_m e^{max(0,-m)} ‖e^{σL}G‖_{L²([m,m+1])}`

  for every source obeying that wall, throughout the whole open first-pole strip `0 < σ < 1`.

All bounds are stated through the extended norm, so no integrability or measurability hypothesis on
`F` is needed: when the defining integral fails to converge the Bochner integral is zero and the
bound is trivially true.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower (gammaJumpKernel)

section Kernel

theorem gammaJumpKernel_pos {s : ℝ} (hs : 0 < s) : 0 < gammaJumpKernel s := by
  have habs : |s| = s := abs_of_pos hs
  have hexp : 1 < Real.exp s := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr hs
  rw [_root_.RHTower.gammaJumpKernel, habs]
  positivity

theorem gammaJumpKernel_le_inv {s : ℝ} (hs : 0 < s) : gammaJumpKernel s ≤ 1 / s := by
  have habs : |s| = s := abs_of_pos hs
  have hge : s ≤ Real.exp s - 1 := by
    have := Real.add_one_le_exp s
    linarith
  rw [_root_.RHTower.gammaJumpKernel, habs]
  exact one_div_le_one_div_of_le hs hge

theorem gammaJumpKernel_le_two_exp {s : ℝ} (hs : 1 ≤ s) :
    gammaJumpKernel s ≤ 2 * Real.exp (-s) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have habs : |s| = s := abs_of_pos hs0
  have hexp2 : (2 : ℝ) < Real.exp s := by
    calc (2 : ℝ) < Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
      _ ≤ Real.exp s := Real.exp_le_exp.mpr hs
  have hden : 0 < Real.exp s - 1 := by linarith
  have hhalf : Real.exp s / 2 ≤ Real.exp s - 1 := by linarith
  have hinv : Real.exp (-s) = 1 / Real.exp s := by
    rw [Real.exp_neg, one_div]
  rw [_root_.RHTower.gammaJumpKernel, habs, hinv]
  rw [div_le_iff₀ hden]
  have hpos : 0 < Real.exp s := Real.exp_pos s
  rw [mul_comm (2 : ℝ), mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [hhalf, hpos]

end Kernel

section Cutoff

variable {χ : ℝ → ℝ} {Λ : ℝ}

/-- A cutoff rising from `0` to `1` across a unit interval has Lipschitz constant at least one. -/
theorem one_le_of_cutoff_lipschitz (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1) : 1 ≤ Λ := by
  have h := hlip 1 0
  rw [hone 1 le_rfl, hzero 0 le_rfl] at h
  simpa using h

/-- Such a cutoff is bounded by its own Lipschitz constant. -/
theorem abs_cutoff_le_lipschitz (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1) (x : ℝ) :
    |χ x| ≤ Λ := by
  have hΛ : 1 ≤ Λ := one_le_of_cutoff_lipschitz hlip hzero hone
  rcases le_or_gt x 0 with hx | hx
  · rw [hzero x hx]
    simpa using by linarith
  · rcases le_or_gt 1 x with hx1 | hx1
    · rw [hone x hx1]
      simpa using hΛ
    · have h := hlip x 0
      rw [hzero 0 le_rfl, sub_zero, sub_zero, abs_of_pos hx] at h
      calc |χ x| ≤ Λ * x := h
        _ ≤ Λ * 1 := by
            refine mul_le_mul_of_nonneg_left hx1.le (by linarith)
        _ = Λ := mul_one Λ

/-- **The commutator envelope.**  The Gamma kernel times a cutoff difference across a gap `s` is
dominated by `4Λe^{-s}`: near the origin the Lipschitz factor cancels the kernel singularity, and
past the origin the kernel itself decays exponentially. -/
theorem gammaJumpKernel_mul_cutoffDiff_le (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    {s : ℝ} (hs : 0 < s) {u v : ℝ} (huv : |u - v| = s) :
    gammaJumpKernel s * |χ u - χ v| ≤ 4 * Λ * Real.exp (-s) := by
  have hΛ : 1 ≤ Λ := one_le_of_cutoff_lipschitz hlip hzero hone
  have hker0 : 0 < gammaJumpKernel s := gammaJumpKernel_pos hs
  have hexp0 : 0 < Real.exp (-s) := Real.exp_pos _
  rcases le_or_gt s 1 with hle | hgt
  · have hdiff : |χ u - χ v| ≤ Λ * s := by
      rw [← huv]
      exact hlip u v
    have hstep : gammaJumpKernel s * |χ u - χ v| ≤ Λ := by
      calc gammaJumpKernel s * |χ u - χ v| ≤ (1 / s) * (Λ * s) := by
            refine mul_le_mul (gammaJumpKernel_le_inv hs) hdiff (abs_nonneg _) (by positivity)
        _ = Λ := by field_simp
    have hquarter : (1 : ℝ) / 4 ≤ Real.exp (-s) := by
      have hb : Real.exp (-s) = 1 / Real.exp s := by rw [Real.exp_neg, one_div]
      have hlt : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.mpr hle
      have h4 : Real.exp 1 < 4 := by
        have := Real.exp_one_lt_d9
        linarith
      rw [hb]
      have hpos : 0 < Real.exp s := Real.exp_pos s
      rw [div_le_div_iff₀ (by norm_num) hpos]
      linarith
    nlinarith [hstep, hquarter, hΛ]
  · have hdiff : |χ u - χ v| ≤ 2 * Λ := by
      have h1 := abs_cutoff_le_lipschitz hlip hzero hone u
      have h2 := abs_cutoff_le_lipschitz hlip hzero hone v
      have h3 : |χ u - χ v| ≤ |χ u| + |χ v| := abs_sub (χ u) (χ v)
      linarith
    calc gammaJumpKernel s * |χ u - χ v| ≤ (2 * Real.exp (-s)) * (2 * Λ) := by
          refine mul_le_mul (gammaJumpKernel_le_two_exp hgt.le) hdiff (abs_nonneg _) (by positivity)
      _ = 4 * Λ * Real.exp (-s) := by ring

end Cutoff

section Commutator

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Gamma jump commutator `[R,χ]F`, written out as the cutoff-difference integral. -/
def gammaWallCommutator (χ : ℝ → ℝ) (F : ℝ → X) (L : ℝ) : X :=
  ∫ s in Ioi (0 : ℝ), gammaJumpKernel s •
    ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))

/-- **The commutator identity.**  Subtracting the two second-difference integrands cancels the
diagonal term and leaves only cutoff differences, so no derivative of `F` occurs inside the
commutator. -/
theorem gammaWallCommutator_integrand (χ : ℝ → ℝ) (F : ℝ → X) (L s : ℝ) :
    gammaJumpKernel s • ((2 : ℝ) • (χ L • F L) - χ (L + s) • F (L + s) - χ (L - s) • F (L - s))
        - χ L • (gammaJumpKernel s • ((2 : ℝ) • F L - F (L + s) - F (L - s)))
      = gammaJumpKernel s • ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s)) := by
  module

variable {χ : ℝ → ℝ} {Λ : ℝ} {F : ℝ → X} {M : ℝ}

/-- Pointwise envelope for the commutator integrand. -/
theorem enorm_gammaWallCommutator_integrand_le
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (hM : ∀ L, ‖F L‖ ≤ M) {L s : ℝ} (hs : 0 < s) :
    ‖gammaJumpKernel s •
        ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖ₑ
      ≤ ENNReal.ofReal (8 * Λ * M * Real.exp (-s)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hplus : |L - (L + s)| = s := by
    rw [show L - (L + s) = -s by ring, abs_neg, abs_of_pos hs]
  have hminus : |L - (L - s)| = s := by
    rw [show L - (L - s) = s by ring, abs_of_pos hs]
  have hk : 0 < gammaJumpKernel s := gammaJumpKernel_pos hs
  have hb1 := gammaJumpKernel_mul_cutoffDiff_le hlip hzero hone hs hplus
  have hb2 := gammaJumpKernel_mul_cutoffDiff_le hlip hzero hone hs hminus
  have hnorm : ‖gammaJumpKernel s •
      ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖
        ≤ 8 * Λ * M * Real.exp (-s) := by
    calc ‖gammaJumpKernel s •
          ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖
        = |gammaJumpKernel s| *
            ‖(χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ gammaJumpKernel s *
            (|χ L - χ (L + s)| * ‖F (L + s)‖ + |χ L - χ (L - s)| * ‖F (L - s)‖) := by
          rw [abs_of_pos hk]
          refine mul_le_mul_of_nonneg_left ?_ hk.le
          calc ‖(χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s)‖
              ≤ ‖(χ L - χ (L + s)) • F (L + s)‖ + ‖(χ L - χ (L - s)) • F (L - s)‖ :=
                norm_add_le _ _
            _ = |χ L - χ (L + s)| * ‖F (L + s)‖ + |χ L - χ (L - s)| * ‖F (L - s)‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = gammaJumpKernel s * |χ L - χ (L + s)| * ‖F (L + s)‖
            + gammaJumpKernel s * |χ L - χ (L - s)| * ‖F (L - s)‖ := by ring
      _ ≤ 4 * Λ * Real.exp (-s) * M + 4 * Λ * Real.exp (-s) * M := by
          have h4 : (0 : ℝ) ≤ 4 * Λ * Real.exp (-s) :=
            le_trans (mul_nonneg hk.le (abs_nonneg _)) hb1
          exact add_le_add (mul_le_mul hb1 (hM (L + s)) (norm_nonneg _) h4)
            (mul_le_mul hb2 (hM (L - s)) (norm_nonneg _) h4)
      _ = 8 * Λ * M * Real.exp (-s) := by ring
  calc ‖gammaJumpKernel s •
        ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖ₑ
      = ENNReal.ofReal ‖gammaJumpKernel s •
          ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (8 * Λ * M * Real.exp (-s)) := ENNReal.ofReal_le_ofReal hnorm

private theorem lintegral_ofReal_const_mul_exp_neg {C a : ℝ} (hC : 0 ≤ C) :
    ∫⁻ s in Ioi a, ENNReal.ofReal (C * Real.exp (-s))
      = ENNReal.ofReal (C * Real.exp (-a)) := by
  have hint : IntegrableOn (fun s : ℝ => C * Real.exp (-s)) (Ioi a) volume :=
    (integrableOn_exp_neg_Ioi a).const_mul C
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] fun s : ℝ => C * Real.exp (-s) :=
    Filter.Eventually.of_forall fun s => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul, integral_exp_neg_Ioi]

/-- **`(29)`: the Gamma cutoff commutator is uniformly bounded on bounded sources.** -/
theorem norm_gammaWallCommutator_le
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (hM : ∀ L, ‖F L‖ ≤ M) (L : ℝ) :
    ‖gammaWallCommutator χ F L‖ ≤ 8 * Λ * M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hΛ : 1 ≤ Λ := one_le_of_cutoff_lipschitz hlip hzero hone
  have hC : (0 : ℝ) ≤ 8 * Λ * M := by positivity
  have hkey : ‖gammaWallCommutator χ F L‖ₑ ≤ ENNReal.ofReal (8 * Λ * M) := by
    calc ‖gammaWallCommutator χ F L‖ₑ
        ≤ ∫⁻ s in Ioi (0 : ℝ), ‖gammaJumpKernel s •
            ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (8 * Λ * M * Real.exp (-s)) := by
          refine setLIntegral_mono' measurableSet_Ioi ?_
          intro s hs
          exact enorm_gammaWallCommutator_integrand_le hlip hzero hone hM hs
      _ = ENNReal.ofReal (8 * Λ * M * Real.exp (-(0 : ℝ))) :=
          lintegral_ofReal_const_mul_exp_neg hC
      _ = ENNReal.ofReal (8 * Λ * M) := by norm_num
  rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hC] at hkey

/-- **`(28)`: the two-sided exponential Gamma wall.**  Outside the unit collar of the cutoff step
every cutoff difference at range below `|L|-1` vanishes identically, so only the exponentially small
tail of the jump kernel survives. -/
theorem norm_gammaWallCommutator_le_exp
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (hM : ∀ L, ‖F L‖ ≤ M) {L : ℝ} (hL : 2 ≤ |L|) :
    ‖gammaWallCommutator χ F L‖ ≤ 24 * Λ * M * Real.exp (-|L|) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hΛ : 1 ≤ Λ := one_le_of_cutoff_lipschitz hlip hzero hone
  have hC : (0 : ℝ) ≤ 8 * Λ * M := by positivity
  have hCfin : (0 : ℝ) ≤ 24 * Λ * M * Real.exp (-|L|) := by positivity
  -- the cutoff differences vanish on the whole window `0 < s ≤ |L| - 1`
  have hvanish : ∀ s : ℝ, 0 < s → s ≤ |L| - 1 →
      gammaJumpKernel s • ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))
        = 0 := by
    intro s hs hsle
    rcases le_or_gt 0 L with hLpos | hLneg
    · have hLabs : |L| = L := abs_of_nonneg hLpos
      rw [hLabs] at hL hsle
      rw [hone L (by linarith), hone (L + s) (by linarith), hone (L - s) (by linarith)]
      simp
    · have hLabs : |L| = -L := abs_of_neg hLneg
      rw [hLabs] at hL hsle
      rw [hzero L (by linarith), hzero (L + s) (by linarith), hzero (L - s) (by linarith)]
      simp
  have hkey : ‖gammaWallCommutator χ F L‖ₑ
      ≤ ENNReal.ofReal (24 * Λ * M * Real.exp (-|L|)) := by
    have hstep : ∫⁻ s in Ioi (0 : ℝ), ‖gammaJumpKernel s •
        ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖ₑ
          ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioi (|L| - 1)).indicator
              (fun s => ENNReal.ofReal (8 * Λ * M * Real.exp (-s))) s := by
      refine setLIntegral_mono' measurableSet_Ioi ?_
      intro s hs
      by_cases hcase : s ∈ Ioi (|L| - 1)
      · rw [Set.indicator_of_mem hcase]
        exact enorm_gammaWallCommutator_integrand_le hlip hzero hone hM hs
      · rw [Set.indicator_of_notMem hcase, hvanish s hs (not_lt.mp hcase)]
        simp
    have hwindow : ∫⁻ s in Ioi (0 : ℝ), (Ioi (|L| - 1)).indicator
        (fun s => ENNReal.ofReal (8 * Λ * M * Real.exp (-s))) s
          = ENNReal.ofReal (8 * Λ * M * Real.exp (-(|L| - 1))) := by
      rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        Set.Ioi_inter_Ioi, max_eq_left (by linarith : (0 : ℝ) ≤ |L| - 1),
        lintegral_ofReal_const_mul_exp_neg hC]
    have hcompare : (8 : ℝ) * Λ * M * Real.exp (-(|L| - 1))
        ≤ 24 * Λ * M * Real.exp (-|L|) := by
      have hexp : Real.exp (-(|L| - 1)) = Real.exp 1 * Real.exp (-|L|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      have hpos : 0 < Real.exp (-|L|) := Real.exp_pos _
      rw [hexp]
      nlinarith [hpos, hM0, hΛ]
    calc ‖gammaWallCommutator χ F L‖ₑ
        ≤ ∫⁻ s in Ioi (0 : ℝ), ‖gammaJumpKernel s •
            ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ENNReal.ofReal (8 * Λ * M * Real.exp (-(|L| - 1))) := hstep.trans (le_of_eq hwindow)
      _ ≤ ENNReal.ofReal (24 * Λ * M * Real.exp (-|L|)) := ENNReal.ofReal_le_ofReal hcompare
  rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hCfin] at hkey

end Commutator

section BlockNorm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **`(7)`: the physical Gamma-wall block norm.**  Unit physical blocks are weighted by the exact
canonical transport cost `e^{max(0,-m)}` of the expanding branch. -/
def gammaWallBlockNorm (σ : ℝ) (G : ℝ → X) : ℝ≥0∞ :=
  ∑' m : ℤ, ENNReal.ofReal (Real.exp (max 0 (-(m : ℝ)))) *
    eLpNorm (fun L => Real.exp (σ * L) • G L) 2 (volume.restrict (Icc (m : ℝ) ((m : ℝ) + 1)))

private theorem eLpNorm_block_le {σ : ℝ} {G : ℝ → X} {a C : ℝ}
    (hb : ∀ L ∈ Icc a (a + 1), ‖Real.exp (σ * L) • G L‖ ≤ C) :
    eLpNorm (fun L => Real.exp (σ * L) • G L) 2 (volume.restrict (Icc a (a + 1)))
      ≤ ENNReal.ofReal C := by
  have hae : ∀ᵐ L ∂(volume.restrict (Icc a (a + 1))),
      ‖Real.exp (σ * L) • G L‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL
    exact hb L hL
  refine le_trans (eLpNorm_le_of_ae_bound hae) (le_of_eq ?_)
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

/-- **`(8) ⟹ (30)`: an exponential Gamma wall is in the physical block class.**  Both physical rays
are geometric: the positive one decays at rate `1-σ` and the negative one at rate `σ` after paying
the canonical transport cost, so the block norm is finite throughout the open first-pole strip. -/
theorem gammaWallBlockNorm_lt_top_of_exp_wall {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {G : ℝ → X} {C : ℝ} (hC : 0 ≤ C) (hwall : ∀ L : ℝ, ‖G L‖ ≤ C * Real.exp (-|L|)) :
    gammaWallBlockNorm σ G < ⊤ := by
  set B : ℤ → ℝ≥0∞ := fun m => ENNReal.ofReal (Real.exp (max 0 (-(m : ℝ)))) *
    eLpNorm (fun L => Real.exp (σ * L) • G L) 2 (volume.restrict (Icc (m : ℝ) ((m : ℝ) + 1)))
    with hBdef
  have hsplit : ∑' m : ℤ, B m = (∑' n : ℕ, B (n : ℤ)) + ∑' n : ℕ, B (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable
  -- positive physical ray
  have hpos : ∀ n : ℕ, B (n : ℤ) ≤ ENNReal.ofReal (C * suzukiGammaWallPositiveBlock σ n) := by
    intro n
    have hmR : ((n : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
    have hbound : ∀ L ∈ Icc (((n : ℤ) : ℝ)) (((n : ℤ) : ℝ) + 1),
        ‖Real.exp (σ * L) • G L‖ ≤ C * suzukiGammaWallPositiveBlock σ n := by
      intro L hL
      have hL0 : (0 : ℝ) ≤ L := le_trans (by rw [hmR]; exact Nat.cast_nonneg n) hL.1
      have habs : |L| = L := abs_of_nonneg hL0
      have hLm : (n : ℝ) ≤ L := by rw [← hmR]; exact hL.1
      calc ‖Real.exp (σ * L) • G L‖ = Real.exp (σ * L) * ‖G L‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (σ * L) * (C * Real.exp (-|L|)) :=
            mul_le_mul_of_nonneg_left (hwall L) (Real.exp_pos _).le
        _ = C * Real.exp (-(1 - σ) * L) := by
            rw [habs, show -(1 - σ) * L = σ * L + -L by ring, Real.exp_add]
            ring
        _ ≤ C * Real.exp (-(1 - σ) * (n : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
            nlinarith [hLm, hσ1]
        _ = C * suzukiGammaWallPositiveBlock σ n := by
            rw [suzukiGammaWallPositiveBlock_eq]
    have hweight : Real.exp (max 0 (-(((n : ℤ) : ℝ)))) = 1 := by
      rw [max_eq_left (show -(((n : ℤ) : ℝ)) ≤ 0 by
        rw [hmR]; exact neg_nonpos.mpr (Nat.cast_nonneg n)), Real.exp_zero]
    rw [hBdef]
    dsimp only
    rw [hweight, ENNReal.ofReal_one, one_mul]
    exact eLpNorm_block_le hbound
  -- negative physical ray
  have hneg : ∀ n : ℕ, B (-((n : ℤ) + 1))
      ≤ ENNReal.ofReal (C * Real.exp 1 * suzukiGammaWallNegativeBlock σ n) := by
    intro n
    have hmR : ((-((n : ℤ) + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
    have hbound : ∀ L ∈ Icc (((-((n : ℤ) + 1) : ℤ) : ℝ)) (((-((n : ℤ) + 1) : ℤ) : ℝ) + 1),
        ‖Real.exp (σ * L) • G L‖ ≤ C * Real.exp (-(1 + σ) * (n : ℝ)) := by
      intro L hL
      have hLup : L ≤ -(n : ℝ) := by
        have := hL.2
        rw [hmR] at this
        linarith
      have hL0 : L ≤ 0 := le_trans hLup (neg_nonpos.mpr (Nat.cast_nonneg n))
      have habs : |L| = -L := abs_of_nonpos hL0
      calc ‖Real.exp (σ * L) • G L‖ = Real.exp (σ * L) * ‖G L‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (σ * L) * (C * Real.exp (-|L|)) :=
            mul_le_mul_of_nonneg_left (hwall L) (Real.exp_pos _).le
        _ = C * Real.exp ((1 + σ) * L) := by
            rw [habs, neg_neg, show (1 + σ) * L = σ * L + L by ring, Real.exp_add]
            ring
        _ ≤ C * Real.exp (-(1 + σ) * (n : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
            nlinarith [hLup, hσ0]
    have hweight : Real.exp (max 0 (-(((-((n : ℤ) + 1) : ℤ) : ℝ)))) = Real.exp ((n : ℝ) + 1) := by
      rw [hmR, neg_neg, max_eq_right (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    have harith : Real.exp ((n : ℝ) + 1) * (C * Real.exp (-(1 + σ) * (n : ℝ)))
        = C * Real.exp 1 * suzukiGammaWallNegativeBlock σ n := by
      have h1 : Real.exp ((n : ℝ) + 1) * Real.exp (-(1 + σ) * (n : ℝ))
          = Real.exp 1 * Real.exp (-σ * (n : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [suzukiGammaWallNegativeBlock_eq]
      calc Real.exp ((n : ℝ) + 1) * (C * Real.exp (-(1 + σ) * (n : ℝ)))
          = C * (Real.exp ((n : ℝ) + 1) * Real.exp (-(1 + σ) * (n : ℝ))) := by ring
        _ = C * (Real.exp 1 * Real.exp (-σ * (n : ℝ))) := by rw [h1]
        _ = C * Real.exp 1 * Real.exp (-σ * (n : ℝ)) := by ring
    rw [hBdef]
    dsimp only
    rw [hweight, ← harith, ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul' le_rfl (eLpNorm_block_le hbound)
  have hpossum : (∑' n : ℕ, B (n : ℤ)) < ⊤ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hpos) ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => by
        have := (suzukiGammaWallPositiveBlock_eq σ n) ▸ Real.exp_pos (-(1 - σ) * (n : ℝ))
        positivity)
      ((summable_suzukiGammaWallPositiveBlock hσ1).mul_left C)]
    exact ENNReal.ofReal_lt_top
  have hnegsum : (∑' n : ℕ, B (-((n : ℤ) + 1))) < ⊤ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hneg) ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => by
        have := (suzukiGammaWallNegativeBlock_eq σ n) ▸ Real.exp_pos (-σ * (n : ℝ))
        positivity)
      ((summable_suzukiGammaWallNegativeBlock hσ0).mul_left (C * Real.exp 1))]
    exact ENNReal.ofReal_lt_top
  rw [gammaWallBlockNorm, ← hBdef, hsplit]
  exact ENNReal.add_lt_top.mpr ⟨hpossum, hnegsum⟩

end BlockNorm

section WallTransfer

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **`(30)`: the literal Gamma cutoff commutator lives in the physical block class.**  The uniform
bound covers the collar `|L| ≤ 2` and the exponential wall covers both outward rays, so a single
exponential majorant `8Λ‖F‖_∞e²e^{-|L|}` dominates the commutator everywhere. -/
theorem gammaWallBlockNorm_gammaWallCommutator_lt_top {χ : ℝ → ℝ} {Λ : ℝ} {F : ℝ → X} {M : ℝ}
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (hM : ∀ L, ‖F L‖ ≤ M) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    gammaWallBlockNorm σ (gammaWallCommutator χ F) < ⊤ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hΛ : 1 ≤ Λ := one_le_of_cutoff_lipschitz hlip hzero hone
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  refine gammaWallBlockNorm_lt_top_of_exp_wall hσ0 hσ1 (C := 8 * Λ * M * Real.exp 2)
    (by positivity) ?_
  intro L
  have hexp : 0 < Real.exp (-|L|) := Real.exp_pos _
  have hnn : (0 : ℝ) ≤ Λ * M * Real.exp (-|L|) :=
    mul_nonneg (mul_nonneg hΛ0 hM0) hexp.le
  rcases le_or_gt 2 |L| with hL | hL
  · refine le_trans (norm_gammaWallCommutator_le_exp hlip hzero hone hM hL) ?_
    calc 24 * Λ * M * Real.exp (-|L|) = 24 * (Λ * M * Real.exp (-|L|)) := by ring
      _ ≤ (8 * Real.exp 2) * (Λ * M * Real.exp (-|L|)) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
      _ = 8 * Λ * M * Real.exp 2 * Real.exp (-|L|) := by ring
  · refine le_trans (norm_gammaWallCommutator_le hlip hzero hone hM L) ?_
    have hge : (1 : ℝ) ≤ Real.exp 2 * Real.exp (-|L|) := by
      rw [← Real.exp_add]
      calc (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (2 + -|L|) := Real.exp_le_exp.mpr (by linarith)
    have hnn2 : (0 : ℝ) ≤ 8 * Λ * M := by positivity
    calc 8 * Λ * M = (8 * Λ * M) * 1 := by ring
      _ ≤ (8 * Λ * M) * (Real.exp 2 * Real.exp (-|L|)) :=
          mul_le_mul_of_nonneg_left hge hnn2
      _ = 8 * Λ * M * Real.exp 2 * Real.exp (-|L|) := by ring

end WallTransfer

end GaloisForLFunctions.RHTower
