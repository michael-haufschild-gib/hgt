import GaloisForLFunctions.RHTower.WeilLogShiftDiagonalMoment

/-!
# The asymptotic log-shift cone is a signed-potential cone

Absolute summability of the normalized deviation gives uniform convergence of
the entire expanding log-shift panel to `2 * (ψ(log m) - ψ(0))`, where `ψ` is
the existing Riemann-kernel deviation potential. Consequently asymptotic panel
nonnegativity is exactly a countable family of fixed potential inequalities.
No full Weil positivity or RH premise is used.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open RHTower.WeilExcess

noncomputable section

namespace RHTower

private theorem summable_potential_kernel {lam : ℕ → ℝ}
    (hs : Summable fun n => |weilDeviation lam n|) {K : ℝ → ℝ} {C : ℝ}
    (hK : ∀ y, |K y| ≤ C) (y : ℝ) :
    Summable fun n : ℕ => weilDeviation lam n * (K (y + Real.log n) + K (y - Real.log n)) := by
  refine (hs.mul_right (2 * C)).of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc _ ≤ |K (y + Real.log n)| + |K (y - Real.log n)| := abs_add_le _ _
    _ ≤ 2 * C := by linarith only [hK (y + Real.log n), hK (y - Real.log n)]

private theorem abs_truncatedAutocorr_le (L y : ℝ) :
    |truncatedRiemannAutocorr L y| ≤ riemannAutocorr 0 := by
  rw [abs_of_nonneg (truncatedRiemannAutocorr_nonneg _ _)]
  exact (truncatedRiemannAutocorr_le_riemannAutocorr _ _).trans (riemannAutocorr_le_zero _)

private theorem abs_autocorr_le (y : ℝ) : |riemannAutocorr y| ≤ riemannAutocorr 0 := by
  rw [abs_of_nonneg (riemannAutocorr_nonneg _)]
  exact riemannAutocorr_le_zero _

/-- Truncation of a summable signed potential converges uniformly in every real shift,
with an exponential error bound independent of the shift. -/
theorem exists_uniform_truncatedDeviationPotential_error {lam : ℕ → ℝ}
    (hs : Summable fun n => |weilDeviation lam n|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L y : ℝ,
      |truncatedDeviationPotential lam L y - deviationPotential lam y| ≤
        C * Real.exp (-(2 * (L - 1))) := by
  obtain ⟨D, _, hD0, _, hD, _⟩ := exists_riemannKernelAutocorr_decay
  have hdefect (L y : ℝ) :
      |truncatedRiemannAutocorr L y - riemannAutocorr y| ≤ D * Real.exp (-(2 * (L - 1))) := by
    have h := hD L y
    change |truncatedRiemannAutocorr L y - riemannAutocorr y| ≤
      D * Real.exp (-(2 * (L - 1))) * Real.exp (-(2 * |y|)) at h
    have hexp : Real.exp (-(2 * |y|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith only [abs_nonneg y])
    exact h.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hD0 (Real.exp_pos _).le))
  refine ⟨2 * D * (∑' n : ℕ, |weilDeviation lam n|),
    mul_nonneg (mul_nonneg (by norm_num) hD0) (tsum_nonneg fun n => abs_nonneg _), ?_⟩
  intro L y
  let E := Real.exp (-(2 * (L - 1)))
  let f (n : ℕ) := weilDeviation lam n *
    (truncatedRiemannAutocorr L (y + Real.log n) + truncatedRiemannAutocorr L (y - Real.log n))
  let g (n : ℕ) := weilDeviation lam n *
    (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))
  have hf : Summable f := summable_potential_kernel hs (abs_truncatedAutocorr_le L) y
  have hg : Summable g := summable_potential_kernel hs abs_autocorr_le y
  have hpoint (n : ℕ) : ‖f n - g n‖ ≤ |weilDeviation lam n| * (2 * D * E) := by
    have heq : f n - g n = weilDeviation lam n *
        ((truncatedRiemannAutocorr L (y + Real.log n) - riemannAutocorr (y + Real.log n)) +
         (truncatedRiemannAutocorr L (y - Real.log n) - riemannAutocorr (y - Real.log n))) := by
      dsimp only [f, g]
      ring
    rw [heq, Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc _ ≤ |truncatedRiemannAutocorr L (y + Real.log n) - riemannAutocorr (y + Real.log n)| +
          |truncatedRiemannAutocorr L (y - Real.log n) - riemannAutocorr (y - Real.log n)| :=
        abs_add_le _ _
      _ ≤ 2 * D * E := by linarith only [hdefect L (y + Real.log n), hdefect L (y - Real.log n)]
  change |(∑' n, f n) - ∑' n, g n| ≤ _
  rw [← hf.tsum_sub hg, ← Real.norm_eq_abs]
  calc _ ≤ ∑' n, ‖f n - g n‖ := norm_tsum_le_tsum_norm (hf.sub hg).norm
    _ ≤ ∑' n, |weilDeviation lam n| * (2 * D * E) :=
      (hf.sub hg).norm.tsum_le_tsum hpoint (hs.mul_right _)
    _ = _ := by rw [tsum_mul_right]; dsimp only [E]; ring

/-- Exact panel identity needs only convergence of the truncated potential series. -/
theorem logShift_panel_potential_identity {lam : ℕ → ℝ} (k : ℕ)
    (hp : ∀ y : ℝ, Summable fun n : ℕ => weilDeviation lam n *
      (truncatedRiemannAutocorr k (y + Real.log n) +
        truncatedRiemannAutocorr k (y - Real.log n)))
    (m : Finset.Icc 2 ⌊Real.exp (2 * (k : ℝ))⌋₊) :
    (weilLogShiftWindowPanel k lam m).re =
      (zetaZeroConfig.W (logShiftRiemannDifference k (Real.log m.1))
        (logShiftRiemannDifference k (Real.log m.1))).re +
      2 * (truncatedDeviationPotential lam k (Real.log m.1) - truncatedDeviationPotential lam k 0) := by
  let f := logShiftRiemannDifference k (Real.log m.1)
  let c := Real.log m.1
  have hfc : HasCompactSupport f := hasCompactSupport_logShiftRiemannDifference _ _
  have hgc := EF.weilTest_hasCompactSupport hfc hfc
  have hterms := summable_primeAtoms (weilDeviation lam) hgc
  have hsum : (∑' n : ℕ, ((weilDeviation lam n : ℝ) : ℂ) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re =
      2 * truncatedDeviationPotential lam k 0 - 2 * truncatedDeviationPotential lam k c := by
    rw [Complex.re_tsum hterms]
    have heq (n : ℕ) : (((weilDeviation lam n : ℝ) : ℂ) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re =
        2 * (weilDeviation lam n * (truncatedRiemannAutocorr k (0 + Real.log n) +
          truncatedRiemannAutocorr k (0 - Real.log n))) -
        2 * (weilDeviation lam n * (truncatedRiemannAutocorr k (c + Real.log n) +
          truncatedRiemannAutocorr k (c - Real.log n))) := by
      rw [show EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n) =
        ((4 * truncatedRiemannAutocorr k (Real.log n) -
          2 * truncatedRiemannAutocorr k (Real.log n + c) -
          2 * truncatedRiemannAutocorr k (Real.log n - c) : ℝ) : ℂ) from
        logShiftRiemannPair_eq _ _ _, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [zero_add, zero_sub, truncatedRiemannAutocorr_neg,
        show c - Real.log n = -(Real.log n - c) by ring, truncatedRiemannAutocorr_neg,
        add_comm c (Real.log n)]
      ring
    rw [tsum_congr heq, (hp 0 |>.mul_left 2).tsum_sub (hp c |>.mul_left 2),
      tsum_mul_left, tsum_mul_left]
    rfl
  change (weilFullFunctional lam (EF.weilTest f f)).re = _
  rw [weilFullFunctional_eq_sub lam hgc, ← weilFullFunctional_vonMangoldt,
    ← zeta_W_eq_weilFullFunctional (contDiff_logShiftRiemannDifference _ _) hfc, Complex.sub_re]
  change (zetaZeroConfig.W f f).re -
    (∑' n : ℕ, ((weilDeviation lam n : ℝ) : ℂ) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re = _
  rw [hsum]
  ring

/-- The zeta zero side tends uniformly to zero over the entire expanding panel. -/
theorem exists_uniform_logShift_zeroSide_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k → ∀ m : Finset.Icc 2 ⌊Real.exp (2 * (k : ℝ))⌋₊,
      ‖zetaZeroConfig.W (logShiftRiemannDifference k (Real.log m.1))
        (logShiftRiemannDifference k (Real.log m.1))‖ ≤ ε := by
  obtain ⟨L, hL⟩ := exists_exp_mul_nearRadicalEnergy_le (ε := ε / 4) (by positivity)
  obtain ⟨Λ, _, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨⌈L⌉₊, fun k hk m => ?_⟩
  have hLk : L ≤ (k : ℝ) := (Nat.le_ceil L).trans (by exact_mod_cast hk)
  have hlog0 := Real.log_natCast_nonneg m.1
  have hm2 := (Finset.mem_Icc.mp m.2).1
  have hmN := (Finset.mem_Icc.mp m.2).2
  have hmpos : (0 : ℝ) < m.1 := by exact_mod_cast (show 0 < m.1 by omega)
  have hmE : (m.1 : ℝ) ≤ Real.exp (2 * (k : ℝ)) :=
    (by exact_mod_cast hmN : (m.1 : ℝ) ≤ (⌊Real.exp (2 * (k : ℝ))⌋₊ : ℝ)).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hlog : Real.log m.1 ≤ 2 * (k : ℝ) := (Real.log_le_iff_le_exp hmpos).mpr hmE
  have hfac : (1 + Real.exp (Real.log m.1 / 2)) ^ 2 ≤ 4 * Real.exp (2 * (k : ℝ)) := by
    have he1 : 1 ≤ Real.exp (k : ℝ) := Real.one_le_exp (Nat.cast_nonneg _)
    have he2 : Real.exp (Real.log m.1 / 2) ≤ Real.exp (k : ℝ) :=
      Real.exp_le_exp.mpr (by linarith only [hlog])
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1 + Real.exp (Real.log m.1 / 2))
      (by positivity : (0 : ℝ) ≤ 2 * Real.exp (k : ℝ))).mpr (by linarith only [he1, he2])
    have heq : Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) ^ 2 := by
      rw [show 2 * (k : ℝ) = (k : ℝ) + k by ring, Real.exp_add, pow_two]
    nlinarith only [hsq, heq]
  have hE0 : 0 ≤ (5 / 4 : ℝ) * zetaInvSqSum * truncatedRiemannTailEnergy k ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) zetaInvSqSum_nonneg) (sq_nonneg _)
  calc _ ≤ (1 + Real.exp (Real.log m.1 / 2)) ^ 2 *
        ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy k ^ 2) :=
      norm_W_logShiftRiemannDifference_le k hlog0 hΛ
    _ ≤ (4 * Real.exp (2 * (k : ℝ))) *
        ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy k ^ 2) :=
      mul_le_mul_of_nonneg_right hfac hE0
    _ ≤ ε := by linarith only [hL k hLk]

/-- Uniform approximation of every entry of the expanding finite panel by its fixed
signed-potential gap. The cutoff is independent of the probe index. -/
theorem exists_uniform_logShift_potential_error {lam : ℕ → ℝ}
    (hs : Summable fun n => |weilDeviation lam n|) {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k → ∀ m,
      |(weilLogShiftWindowPanel k lam m).re -
        2 * (deviationPotential lam (Real.log m.1) - deviationPotential lam 0)| < ε := by
  obtain ⟨C, _, hC⟩ := exists_uniform_truncatedDeviationPotential_error hs
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
  rw [logShift_panel_potential_identity k
    (summable_potential_kernel hs (abs_truncatedAutocorr_le k))]
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

/-- Every sufficiently late panel lies above any prescribed negative tolerance. -/
def WeilLogShiftAsymptoticPositive (lam : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
    ∀ m, -ε ≤ (weilLogShiftWindowPanel k lam m).re

private theorem exists_window_containing_probe (m : ℕ) (hm : 2 ≤ m) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k → m ∈ Finset.Icc 2 ⌊Real.exp (2 * (k : ℝ))⌋₊ := by
  refine ⟨⌈Real.log m / 2⌉₊, fun k hk => ?_⟩
  have hlog : Real.log m / 2 ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact Finset.mem_Icc.mpr ⟨hm, Nat.le_floor
    ((Real.log_le_iff_le_exp hmpos).mp (by linarith only [hlog]))⟩

/-- In the summable signed-deviation sector, asymptotic nonnegativity of all finite
panels is exactly the fixed potential inequality at each integer logarithm. -/
theorem weilLogShiftAsymptoticPositive_iff {lam : ℕ → ℝ}
    (hs : Summable fun n => |weilDeviation lam n|) :
    WeilLogShiftAsymptoticPositive lam ↔
      ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
  constructor
  · intro hpos m hm
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨Np, hp⟩ := hpos ε hε
    obtain ⟨Ne, he⟩ := exists_uniform_logShift_potential_error hs hε
    obtain ⟨Nm, hmN⟩ := exists_window_containing_probe m hm
    let k := max (max Np Ne) Nm
    have hpk : Np ≤ k := (le_max_left Np Ne).trans (le_max_left _ _)
    have hek : Ne ≤ k := (le_max_right Np Ne).trans (le_max_left _ _)
    have hmk : Nm ≤ k := le_max_right _ _
    let j : Finset.Icc 2 ⌊Real.exp (2 * (k : ℝ))⌋₊ := ⟨m, hmN k hmk⟩
    have hfloor := hp k hpk j
    have herror := (abs_lt.mp (he k hek j)).2
    change (weilLogShiftWindowPanel k lam j).re -
      2 * (deviationPotential lam (Real.log m) - deviationPotential lam 0) < ε at herror
    linarith only [hfloor, herror]
  · intro hpotential ε hε
    obtain ⟨N, hN⟩ := exists_uniform_logShift_potential_error hs hε
    refine ⟨N, fun k hk m => ?_⟩
    have herror := (abs_lt.mp (hN k hk m)).1
    have hgap := hpotential m.1 (Finset.mem_Icc.mp m.2).1
    linarith only [herror, hgap]

/-- A uniform positive potential gap gives a positive margin in every sufficiently
late panel, with one cutoff for all probe indices. -/
theorem exists_uniform_logShift_positive_of_potential_gap {lam : ℕ → ℝ}
    (hs : Summable fun n => |weilDeviation lam n|) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ m : ℕ, 2 ≤ m → δ ≤ deviationPotential lam (Real.log m) - deviationPotential lam 0) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k → ∀ m, δ < (weilLogShiftWindowPanel k lam m).re := by
  obtain ⟨N, hN⟩ := exists_uniform_logShift_potential_error hs hδ
  refine ⟨N, fun k hk m => ?_⟩
  have herror := (abs_lt.mp (hN k hk m)).1
  have h := hgap m.1 (Finset.mem_Icc.mp m.2).1
  linarith only [herror, h]

/-- A single negative potential gap produces the same strictly negative probe in
every sufficiently large window. -/
theorem exists_persistent_logShift_negative_of_potential_gap {lam : ℕ → ℝ}
    (hs : Summable fun n => |weilDeviation lam n|) {m : ℕ} (hm : 2 ≤ m)
    (hgap : deviationPotential lam (Real.log m) < deviationPotential lam 0) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
      m ∈ Finset.Icc 2 ⌊Real.exp (2 * (k : ℝ))⌋₊ ∧
      (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (Real.log m))
        (logShiftRiemannDifference k (Real.log m)))).re <
        deviationPotential lam (Real.log m) - deviationPotential lam 0 := by
  have hδ : 0 < deviationPotential lam 0 - deviationPotential lam (Real.log m) := sub_pos.mpr hgap
  obtain ⟨Ne, he⟩ := exists_uniform_logShift_potential_error hs hδ
  obtain ⟨Nm, hmN⟩ := exists_window_containing_probe m hm
  refine ⟨max Ne Nm, fun k hk => ?_⟩
  have hmem := hmN k ((le_max_right _ _).trans hk)
  refine ⟨hmem, ?_⟩
  have herror := (abs_lt.mp (he k ((le_max_left _ _).trans hk) ⟨m, hmem⟩)).2
  change (weilFullFunctional lam (EF.weilTest
    (logShiftRiemannDifference k (Real.log m))
    (logShiftRiemannDifference k (Real.log m)))).re -
      2 * (deviationPotential lam (Real.log m) - deviationPotential lam 0) <
      deviationPotential lam 0 - deviationPotential lam (Real.log m) at herror
  linarith only [herror]

end RHTower

end
