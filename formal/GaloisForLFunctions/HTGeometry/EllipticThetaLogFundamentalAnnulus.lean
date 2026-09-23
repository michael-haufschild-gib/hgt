import GaloisForLFunctions.HTGeometry.EllipticThetaLogPrincipalPart

/-!
# Analyticity on the fundamental multiplicative annulus

For `0 < |q| < 1`, the constructed theta logarithmic kernel is analytic throughout the open
annulus `|q| < |x| < 1`. The proof chooses a smaller closed annulus around the point and supplies
explicit summable majorants for both rational-atom tails. This is the regular fundamental domain
from which nome quasiperiodicity transports meromorphicity to the punctured multiplicative plane.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- **Analyticity of a shifted theta logarithmic series on its annulus.**  For any forward shift
`m`, the series `∑ₖ (A(qᵏ⁺ᵐ/y) − A(qᵏ y))` of elliptic gamma logarithmic atoms is analytic at every
`x` with `‖q‖ᵐ < ‖x‖ < 1`.  The point is enclosed in a closed annulus `r ≤ ‖y‖ ≤ R` strictly inside
the region; on it both atom arguments stay bounded away from `1`, so the geometric majorant
`a^(k+m)/r/(1−cf) + aᵏR/(1−cb)` dominates the summands and term-by-term differentiation applies. -/
theorem analyticAt_ellipticThetaLogShift_of_norm_pow_between {q x : ℂ} {m : ℕ}
    (hq0 : q ≠ 0) (hqmx : ‖q‖ ^ m < ‖x‖) (hx1 : ‖x‖ < 1) :
    AnalyticAt ℂ (fun y : ℂ => ∑' k : ℕ,
      (ellipticGammaLogAtom (q ^ (k + m) / y) -
        ellipticGammaLogAtom (q ^ k * y))) x := by

  let a : ℝ := ‖q‖
  let b : ℝ := ‖x‖
  let r : ℝ := (a ^ m + b) / 2
  let R : ℝ := (b + 1) / 2
  let cf : ℝ := a ^ m / r
  let cb : ℝ := R
  let s : Set ℂ := {y | r ≤ ‖y‖ ∧ ‖y‖ ≤ R}
  let U : Set ℂ := {y | r < ‖y‖ ∧ ‖y‖ < R}
  let uf : ℕ → ℝ := fun k => (a ^ (k + m) / r) / (1 - cf)
  let ub : ℕ → ℝ := fun k => (a ^ k * R) / (1 - cb)
  let u : ℕ → ℝ := fun k => uf k + ub k
  have ha0 : 0 < a := by simpa [a] using norm_pos_iff.mpr hq0
  have hamb : a ^ m < b := by simpa [a, b] using hqmx
  have ha1 : a < 1 := by
    by_contra hcon
    push Not at hcon
    have hle : (1 : ℝ) ≤ a ^ m := by
      calc (1 : ℝ) = 1 ^ m := (one_pow m).symm
        _ ≤ a ^ m := pow_le_pow_left₀ zero_le_one hcon m
    have hb1' : b < 1 := by simpa [b] using hx1
    linarith
  have hb1 : b < 1 := by simpa [b] using hx1
  have hr0 : 0 < r := by dsimp [r]; positivity
  have har : a ^ m < r := by dsimp [r]; linarith
  have hrb : r < b := by dsimp [r]; linarith
  have hbR : b < R := by dsimp [R]; linarith
  have hR0 : 0 ≤ R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hcf1 : cf < 1 := by dsimp [cf]; exact (div_lt_one hr0).mpr har
  have hcb1 : cb < 1 := by simpa [cb] using hR1
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hxU : x ∈ U := by exact ⟨hrb, hbR⟩
  have hgeom : Summable (fun k : ℕ => a ^ k) :=
    summable_geometric_of_lt_one ha0.le ha1
  have huf : Summable uf := by
    have hs := hgeom.mul_left (a ^ m / r / (1 - cf))
    apply hs.congr
    intro k
    dsimp [uf]
    rw [pow_add]
    ring
  have hub : Summable ub := by
    have hs := hgeom.mul_right (R / (1 - cb))
    apply hs.congr
    intro k
    dsimp [ub]
    ring
  have hu : Summable u := huf.add hub
  have hargF (k : ℕ) (y : ℂ) (hy : y ∈ s) :
      ‖q ^ (k + m) / y‖ ≤ cf := by
    change r ≤ ‖y‖ ∧ ‖y‖ ≤ R at hy
    have hbase : ‖q ^ (k + m) / y‖ ≤ a ^ (k + m) / r := by
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg q) _) hr0 hy.1
    apply hbase.trans
    rw [div_le_iff₀ hr0]
    have hpow : a ^ (k + m) ≤ a ^ m := by
      exact pow_le_pow_of_le_one ha0.le ha1.le (by omega)
    calc
      a ^ (k + m) ≤ a ^ m := hpow
      _ = cf * r := by dsimp [cf]; field_simp
  have hargB (k : ℕ) (y : ℂ) (hy : y ∈ s) : ‖q ^ k * y‖ ≤ cb := by
    change r ≤ ‖y‖ ∧ ‖y‖ ≤ R at hy
    rw [norm_mul, norm_pow]
    calc
      a ^ k * ‖y‖ ≤ a ^ k * R :=
        mul_le_mul_of_nonneg_left hy.2 (pow_nonneg ha0.le _)
      _ ≤ 1 * R := by
        exact mul_le_mul_of_nonneg_right (pow_le_one₀ ha0.le ha1.le) hR0
      _ = cb := by simp [cb]
  have hnorm (k : ℕ) (y : ℂ) (hy : y ∈ s) :
      ‖ellipticGammaLogAtom (q ^ (k + m) / y) -
        ellipticGammaLogAtom (q ^ k * y)‖ ≤ u k := by
    have hyr : r ≤ ‖y‖ := by simpa [s] using hy.1
    have hyR : ‖y‖ ≤ R := by simpa [s] using hy.2
    have hyS : y ∈ s := hy
    calc
      ‖ellipticGammaLogAtom (q ^ (k + m) / y) -
          ellipticGammaLogAtom (q ^ k * y)‖ ≤
        ‖ellipticGammaLogAtom (q ^ (k + m) / y)‖ +
          ‖ellipticGammaLogAtom (q ^ k * y)‖ := norm_sub_le _ _
      _ ≤ uf k + ub k := by
        gcongr
        · apply (norm_ellipticGammaLogAtom_le_of_norm_le hcf1 (hargF k y hyS)).trans
          dsimp [uf, a]
          rw [norm_div, norm_pow]
          gcongr
        · apply (norm_ellipticGammaLogAtom_le_of_norm_le hcb1 (hargB k y hyS)).trans
          dsimp [ub, a]
          rw [norm_mul, norm_pow]
          gcongr
      _ = u k := rfl
  have hdiff (k : ℕ) : DifferentiableOn ℂ (fun y : ℂ =>
        ellipticGammaLogAtom (q ^ (k + m) / y) -
          ellipticGammaLogAtom (q ^ k * y)) U := by
    intro y hy
    have hyS : y ∈ s := ⟨hy.1.le, hy.2.le⟩
    have hy0 : y ≠ 0 := norm_pos_iff.mp (hr0.trans hy.1)
    have hf1 : q ^ (k + m) / y ≠ 1 := by
      intro heq
      have := (hargF k y hyS).trans_lt hcf1
      rw [heq, norm_one] at this
      exact lt_irrefl 1 this
    have hb1' : q ^ k * y ≠ 1 := by
      intro heq
      have := (hargB k y hyS).trans_lt hcb1
      rw [heq, norm_one] at this
      exact lt_irrefl 1 this
    change DifferentiableWithinAt ℂ
      (fun y : ℂ => (q ^ (k + m) / y) / (1 - q ^ (k + m) / y) -
        (q ^ k * y) / (1 - q ^ k * y)) U y
    have hFarg : DifferentiableAt ℂ (fun w : ℂ => q ^ (k + m) / w) y :=
      (differentiableAt_const _).div differentiableAt_id hy0
    have hBarg : DifferentiableAt ℂ (fun w : ℂ => q ^ k * w) y :=
      (differentiableAt_const _).mul differentiableAt_id
    exact ((hFarg.div ((differentiableAt_const _).sub hFarg) (sub_ne_zero.mpr hf1.symm)).sub
      (hBarg.div ((differentiableAt_const _).sub hBarg)
        (sub_ne_zero.mpr hb1'.symm))).differentiableWithinAt
  have hsum := Complex.differentiableOn_tsum_of_summable_norm hu hdiff hU
    (fun k y hy => hnorm k y ⟨hy.1.le, hy.2.le⟩)
  exact (hsum.analyticOnNhd hU) x hxU

theorem analyticAt_ellipticThetaLogKernel_of_norm_between {q x : ℂ}
    (hq0 : q ≠ 0) (hqx : ‖q‖ < ‖x‖) (hx1 : ‖x‖ < 1) :
    AnalyticAt ℂ (ellipticThetaLogKernel q) x := by
  have h := analyticAt_ellipticThetaLogShift_of_norm_pow_between (m := 1) hq0
    (by simpa using hqx) hx1
  simpa [ellipticThetaLogKernel, ellipticThetaLogSummand] using! h

theorem analyticAt_ellipticThetaLogRemainder_of_norm_sq_between {q x : ℂ}
    (hq0 : q ≠ 0) (hq2x : ‖q‖ ^ (2 : ℕ) < ‖x‖) (hx1 : ‖x‖ < 1) :
    AnalyticAt ℂ (ellipticThetaLogRemainder q) x := by
  have han := analyticAt_ellipticThetaLogShift_of_norm_pow_between (m := 2) hq0
    (by simpa using hq2x) hx1
  have ha1 : ‖q‖ < 1 := by
    by_contra hcon
    push Not at hcon
    have hle : (1 : ℝ) ≤ ‖q‖ ^ (2 : ℕ) := by
      calc (1 : ℝ) = 1 ^ (2 : ℕ) := (one_pow 2).symm
        _ ≤ ‖q‖ ^ (2 : ℕ) := pow_le_pow_left₀ zero_le_one hcon 2
    linarith
  have heq : (fun y : ℂ => ∑' k : ℕ,
      (ellipticGammaLogAtom (q ^ (k + 2) / y) -
        ellipticGammaLogAtom (q ^ k * y))) = ellipticThetaLogRemainder q := by
    funext y
    have hfBase := summable_ellipticThetaForwardLogAtom (q := q) (x := y) ha1
    have hf : Summable (fun k : ℕ => ellipticGammaLogAtom (q ^ (k + 2) / y)) := by
      simpa [Function.comp_def, Nat.add_assoc] using
        hfBase.comp_injective (i := fun k : ℕ => k + 2) (fun _ _ h => Nat.add_right_cancel h)
    have hb := summable_ellipticThetaBackwardLogAtom (q := q) (x := y) ha1
    rw [hf.tsum_sub hb]
    rfl
  rw [← heq]
  exact han

theorem analyticAt_ellipticThetaLogKernel_of_norm_sq_between_of_ne {q x : ℂ}
    (hq0 : q ≠ 0) (hq2x : ‖q‖ ^ (2 : ℕ) < ‖x‖) (hx1 : ‖x‖ < 1) (hxq : x ≠ q) :
    AnalyticAt ℂ (ellipticThetaLogKernel q) x := by
  have hx0 : x ≠ 0 := by
    exact norm_pos_iff.mp ((sq_pos_of_pos (norm_pos_iff.mpr hq0)).trans hq2x)
  have hq1 : ‖q‖ < 1 := by
    have hqnonneg := norm_nonneg q
    nlinarith [sq_nonneg (‖q‖ - 1)]
  have harg : AnalyticAt ℂ (fun y : ℂ => q / y) x :=
    analyticAt_const.div analyticAt_id hx0
  have harg1 : q / x ≠ 1 := by
    intro h
    have hqx : q = x := (div_eq_one_iff_eq hx0).mp h
    exact hxq hqx.symm
  have hsing : AnalyticAt ℂ (fun y : ℂ => ellipticGammaLogAtom (q / y)) x := by
    change AnalyticAt ℂ (fun y : ℂ => (q / y) / (1 - q / y)) x
    exact harg.div (analyticAt_const.sub harg) (sub_ne_zero.mpr harg1.symm)
  have heq : ellipticThetaLogKernel q =
      fun y => ellipticGammaLogAtom (q / y) + ellipticThetaLogRemainder q y := by
    funext y
    exact ellipticThetaLogKernel_eq_atom_add_remainder hq1
  rw [heq]
  exact hsing.add (analyticAt_ellipticThetaLogRemainder_of_norm_sq_between hq0 hq2x hx1)

/-- On the wider fundamental annulus `|q|^(2 : ℕ) < |x| < 1`, the constructed theta logarithmic kernel
is meromorphic, with the only possible pole at `x = q`. -/
theorem meromorphicAt_ellipticThetaLogKernel_of_norm_sq_between
    {q x : ℂ} (hq0 : q ≠ 0) (hq2x : ‖q‖ ^ (2 : ℕ) < ‖x‖) (hx1 : ‖x‖ < 1) :
    MeromorphicAt (ellipticThetaLogKernel q) x := by
  by_cases hxq : x = q
  · subst x
    have hq1 : ‖q‖ < 1 := hx1
    have harg : AnalyticAt ℂ (fun y : ℂ => q / y) q :=
      analyticAt_const.div analyticAt_id hq0
    have hsing : MeromorphicAt (fun y : ℂ => ellipticGammaLogAtom (q / y)) q := by
      change MeromorphicAt (fun y : ℂ => (q / y) / (1 - q / y)) q
      exact harg.meromorphicAt.div (analyticAt_const.sub harg).meromorphicAt
    have heq : ellipticThetaLogKernel q =
        fun y => ellipticGammaLogAtom (q / y) + ellipticThetaLogRemainder q y := by
      funext y
      exact ellipticThetaLogKernel_eq_atom_add_remainder hq1
    rw [heq]
    exact hsing.add (analyticAt_ellipticThetaLogRemainder_nome hq0 hq1).meromorphicAt
  · exact (analyticAt_ellipticThetaLogKernel_of_norm_sq_between_of_ne
      hq0 hq2x hx1 hxq).meromorphicAt

end

end GaloisForLFunctions
