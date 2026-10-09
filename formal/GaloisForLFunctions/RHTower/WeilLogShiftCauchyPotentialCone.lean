import GaloisForLFunctions.RHTower.WeilLogShiftDeficitTranslation

/-!
# Uniform log-shift limits under Cauchy control

Cauchy control of the absolute normalized deviation replaces absolute summability
in uniform potential truncation and whole-panel convergence. Asymptotic log-shift
positivity and summable excess supply this control without an extra premise.
On the summable-excess domain, asymptotic positivity is exactly Cauchy control
together with the countable signed-potential inequalities.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open RHTower.WeilExcess

namespace RHTower

/-- Summable excess and asymptotic panel positivity control the absolute deviation
against every Cauchy profile, even without absolute summability. -/
theorem exists_cauchyBounded_absDeviation_of_logShiftAsymptoticPositive {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) :
    ∃ D : ℝ, 0 ≤ D ∧ CauchyBounded (fun n => |weilDeviation lam n|) D := by
  obtain ⟨D, hD0, hD⟩ := exists_deficit_cauchyBounded_of_logShiftAsymptoticPositive hpos hexc
  have hE := cauchyBounded_of_summable (deviationExcess_nonneg lam) hexc
  refine ⟨2 * (∑' n, deviationExcess lam n) + D,
    add_nonneg (mul_nonneg (by norm_num) (tsum_nonneg fun n => deviationExcess_nonneg lam n))
      hD0, ?_⟩
  intro η hη0 hη1 s
  obtain ⟨hsE, hleE⟩ := hE η hη0 hη1 s
  obtain ⟨hsD, hleD⟩ := hD η hη0 hη1 s
  let P (n : ℕ) := cauchyProfile η s (Real.log n) + cauchyProfile η s (-Real.log n)
  have hP (n : ℕ) : 0 ≤ P n :=
    add_nonneg (cauchyProfile_nonneg hη0.le s _) (cauchyProfile_nonneg hη0.le s _)
  have ha (n : ℕ) : |weilDeviation lam n| ≤ deviationExcess lam n + deviationDeficit lam n := by
    rw [weilDeviation_eq_sub lam n]
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (deviationExcess_nonneg _ _),
      abs_of_nonneg (deviationDeficit_nonneg _ _)])
  have hdom (n : ℕ) : |weilDeviation lam n| * P n ≤
      deviationExcess lam n * P n + deviationDeficit lam n * P n := by
    simpa only [add_mul] using mul_le_mul_of_nonneg_right (ha n) (hP n)
  have hs := Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hP n))
    hdom (hsE.add hsD)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, (deviationExcess lam n * P n + deviationDeficit lam n * P n) :=
      hs.tsum_le_tsum hdom (hsE.add hsD)
    _ = (∑' n, deviationExcess lam n * P n) + ∑' n, deviationDeficit lam n * P n :=
      hsE.tsum_add hsD
    _ ≤ _ := add_le_add hleE hleD

private theorem norm_potential_cauchy_majorant {lam : ℕ → ℝ} {K : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hK : ∀ z, |K z| ≤ C * Real.exp (-(2 * |z|))) (y : ℝ) (n : ℕ) :
    ‖weilDeviation lam n * (K (y + Real.log n) + K (y - Real.log n))‖ ≤
      C * (|weilDeviation lam n| *
        (cauchyProfile 1 y (Real.log n) + cauchyProfile 1 y (-Real.log n))) := by
  have hp := (hK (y + Real.log n)).trans (mul_le_mul_of_nonneg_left
    (exp_neg_two_abs_le_cauchyProfile (y + Real.log n)) hC)
  have hm := (hK (y - Real.log n)).trans (mul_le_mul_of_nonneg_left
    (exp_neg_two_abs_le_cauchyProfile (y - Real.log n)) hC)
  have ep : cauchyProfile 1 0 (y + Real.log n) = cauchyProfile 1 y (-Real.log n) := by
    simp only [cauchyProfile]; ring_nf
  have em : cauchyProfile 1 0 (y - Real.log n) = cauchyProfile 1 y (Real.log n) := by
    simp only [cauchyProfile]; ring_nf
  rw [ep] at hp
  rw [em] at hm
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |weilDeviation lam n| * (|K (y + Real.log n)| + |K (y - Real.log n)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ ≤ |weilDeviation lam n| *
        (C * cauchyProfile 1 y (-Real.log n) + C * cauchyProfile 1 y (Real.log n)) :=
      mul_le_mul_of_nonneg_left (add_le_add hp hm) (abs_nonneg _)
    _ = _ := by ring

private theorem summable_potential_of_cauchyBounded {lam : ℕ → ℝ} {D : ℝ}
    (hD : CauchyBounded (fun n => |weilDeviation lam n|) D) {K : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hK : ∀ z, |K z| ≤ C * Real.exp (-(2 * |z|))) (y : ℝ) :
    Summable fun n : ℕ => weilDeviation lam n * (K (y + Real.log n) + K (y - Real.log n)) :=
  ((hD 1 one_pos le_rfl y).1.mul_left C).of_norm_bounded
    (norm_potential_cauchy_majorant hC hK y)

private theorem summable_truncated_potential_of_cauchyBounded {lam : ℕ → ℝ} {D : ℝ}
    (hD : CauchyBounded (fun n => |weilDeviation lam n|) D) (L y : ℝ) :
    Summable fun n : ℕ => weilDeviation lam n *
      (truncatedRiemannAutocorr L (y + Real.log n) +
        truncatedRiemannAutocorr L (y - Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannAutocorr_le
  apply summable_potential_of_cauchyBounded hD hC0 (fun z => ?_) y
  rw [abs_of_nonneg (truncatedRiemannAutocorr_nonneg _ _)]
  exact (truncatedRiemannAutocorr_le_riemannAutocorr _ _).trans (hC z)

/-- Cauchy control of absolute deviation gives an exponential truncation error
uniform over every real shift; absolute summability is unnecessary. -/
theorem exists_uniform_truncatedPotential_error_of_cauchyBounded {lam : ℕ → ℝ} {D : ℝ}
    (hD : CauchyBounded (fun n => |weilDeviation lam n|) D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L y : ℝ,
      |truncatedDeviationPotential lam L y - deviationPotential lam y| ≤
        C * Real.exp (-(2 * (L - 1))) := by
  obtain ⟨A, _, hA0, _, hA, _⟩ := exists_riemannKernelAutocorr_decay
  have hD0 : 0 ≤ D := (tsum_nonneg fun n =>
    mul_nonneg (abs_nonneg (weilDeviation lam n))
      (add_nonneg (cauchyProfile_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 0 (Real.log n))
        (cauchyProfile_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 0 (-Real.log n)))).trans
    (hD 1 one_pos le_rfl 0).2
  refine ⟨A * D, mul_nonneg hA0 hD0, fun L y => ?_⟩
  let E := Real.exp (-(2 * (L - 1)))
  have hAE : 0 ≤ A * E := mul_nonneg hA0 (Real.exp_pos _).le
  let f (n : ℕ) := weilDeviation lam n *
    (truncatedRiemannAutocorr L (y + Real.log n) + truncatedRiemannAutocorr L (y - Real.log n))
  let g (n : ℕ) := weilDeviation lam n *
    (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))
  let P (n : ℕ) := |weilDeviation lam n| *
    (cauchyProfile 1 y (Real.log n) + cauchyProfile 1 y (-Real.log n))
  have hf : Summable f := summable_truncated_potential_of_cauchyBounded hD L y
  have hg : Summable g := by
    obtain ⟨B, hB0, hB⟩ := exists_riemannAutocorr_le
    apply summable_potential_of_cauchyBounded hD hB0 (fun z => ?_) y
    rw [abs_of_nonneg (riemannAutocorr_nonneg _)]
    exact hB z
  obtain ⟨hsP, hleP⟩ := hD 1 one_pos le_rfl y
  have hpoint (n : ℕ) : ‖f n - g n‖ ≤ (A * E) * P n := by
    have heq : f n - g n = weilDeviation lam n *
        ((truncatedRiemannAutocorr L (y + Real.log n) - riemannAutocorr (y + Real.log n)) +
          (truncatedRiemannAutocorr L (y - Real.log n) - riemannAutocorr (y - Real.log n))) := by
      dsimp only [f, g]
      ring
    rw [heq]
    exact norm_potential_cauchy_majorant hAE (hA L) y n
  change |(∑' n, f n) - ∑' n, g n| ≤ _
  rw [← hf.tsum_sub hg, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' n, ‖f n - g n‖ := norm_tsum_le_tsum_norm (hf.sub hg).norm
    _ ≤ ∑' n, (A * E) * P n :=
      (hf.sub hg).norm.tsum_le_tsum hpoint (hsP.mul_left _)
    _ = (A * E) * ∑' n, P n := tsum_mul_left
    _ ≤ (A * E) * D := mul_le_mul_of_nonneg_left hleP hAE
    _ = _ := by dsimp only [E]; ring

/-- Whole-panel potential approximation holds under Cauchy control of absolute
deviation; its cutoff is independent of the probe index. -/
theorem exists_uniform_logShift_potential_error_of_cauchyBounded {lam : ℕ → ℝ} {D : ℝ}
    (hD : CauchyBounded (fun n => |weilDeviation lam n|) D) {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k → ∀ m,
      |(weilLogShiftWindowPanel k lam m).re -
        2 * (deviationPotential lam (Real.log m.1) - deviationPotential lam 0)| < ε := by
  obtain ⟨C, _, hC⟩ := exists_uniform_truncatedPotential_error_of_cauchyBounded hD
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    ((tendsto_mul_exp_neg_atTop C).eventually_lt_const (by positivity : (0 : ℝ) < ε / 8))
  obtain ⟨N, hN⟩ := exists_uniform_logShift_zeroSide_bound (ε := ε / 4) (by positivity)
  refine ⟨max N ⌈L⌉₊, fun k hk m => ?_⟩
  have hNk : N ≤ k := (le_max_left _ _).trans hk
  have hLk : L ≤ (k : ℝ) := (Nat.le_ceil L).trans
    (by exact_mod_cast (show ⌈L⌉₊ ≤ k from (le_max_right _ _).trans hk))
  have hw := (Complex.abs_re_le_norm _).trans (hN k hNk m)
  have hc := hC k (Real.log m.1)
  have h0 := hC k 0
  have hsmall := hL k hLk
  rw [logShift_panel_potential_identity k (summable_truncated_potential_of_cauchyBounded hD k)]
  let w := (zetaZeroConfig.W (logShiftRiemannDifference k (Real.log m.1))
    (logShiftRiemannDifference k (Real.log m.1))).re
  let dc := truncatedDeviationPotential lam k (Real.log m.1) - deviationPotential lam (Real.log m.1)
  let d0 := truncatedDeviationPotential lam k 0 - deviationPotential lam 0
  change |w + 2 * (truncatedDeviationPotential lam k (Real.log m.1) -
    truncatedDeviationPotential lam k 0) -
    2 * (deviationPotential lam (Real.log m.1) - deviationPotential lam 0)| < ε
  rw [show w + 2 * (truncatedDeviationPotential lam k (Real.log m.1) -
    truncatedDeviationPotential lam k 0) -
    2 * (deviationPotential lam (Real.log m.1) - deviationPotential lam 0) =
    w + 2 * (dc - d0) by dsimp only [dc, d0]; ring]
  have htri : |w + 2 * (dc - d0)| ≤ |w| + 2 * (|dc| + |d0|) := by
    calc _ ≤ |w| + |2 * (dc - d0)| := abs_add_le _ _
      _ = |w| + 2 * |dc - d0| := by rw [abs_mul]; norm_num
      _ ≤ _ := by linarith only [abs_sub dc d0]
  dsimp only [w, dc, d0] at htri ⊢
  linarith only [hε, htri, hw, hc, h0, hsmall]

/-- One-sided summability suffices for uniform whole-panel approximation once
asymptotic positivity supplies the required Cauchy control. -/
theorem exists_uniform_logShift_potential_error_of_summable_excess {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k → ∀ m,
      |(weilLogShiftWindowPanel k lam m).re -
        2 * (deviationPotential lam (Real.log m.1) - deviationPotential lam 0)| < ε := by
  obtain ⟨_, _, hD⟩ := exists_cauchyBounded_absDeviation_of_logShiftAsymptoticPositive hpos hexc
  exact exists_uniform_logShift_potential_error_of_cauchyBounded hD hε

/-- On the summable-excess domain, asymptotic positivity is exactly absolute
deviation Cauchy control together with the countable signed-potential inequalities. -/
theorem weilLogShiftAsymptoticPositive_iff_cauchyBounded_potential {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) :
    WeilLogShiftAsymptoticPositive lam ↔
      (∃ D : ℝ, 0 ≤ D ∧ CauchyBounded (fun n => |weilDeviation lam n|) D) ∧
      ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
  constructor
  · intro hpos
    exact ⟨exists_cauchyBounded_absDeviation_of_logShiftAsymptoticPositive hpos hexc,
      logShiftAsymptotic_potential_le_of_summable_excess hpos hexc⟩
  · rintro ⟨⟨D, _, hD⟩, hpotential⟩ ε hε
    obtain ⟨N, hN⟩ := exists_uniform_logShift_potential_error_of_cauchyBounded hD hε
    refine ⟨N, fun k hk m => ?_⟩
    have hgap := hpotential m.1 (Finset.mem_Icc.mp m.2).1
    have herr := (abs_lt.mp (hN k hk m)).1
    linarith

end RHTower
