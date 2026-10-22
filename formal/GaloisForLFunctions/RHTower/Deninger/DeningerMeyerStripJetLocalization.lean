import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerNonlinearMellin
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiJetPacketSurjectivity

/-! # Localizing full finite jets without losing original Meyer admission

Finite source jet surjectivity supplies the local germ. Exponential
polynomials preserve that germ while making its carrier arbitrarily small
on any vertical strip lying strictly inside the node's real part.
-/

open Complex Filter Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- Any finite analytic germ has an original all-weight Mellin representative. -/
theorem exists_deningerMeyerMellin_finiteGerm {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (m : ℕ) :
    ∃ F : ℂ → ℂ, DeningerEntireMellinRegular F ∧
      (m : ℕ∞) ≤ analyticOrderAt (fun z => F z - f z) w := by
  obtain ⟨g, hg⟩ := piMap_surjective_of_linearIndependent
    (fun k : Fin m => deningerMeyerStrongLogMellinJetLM k w)
    (deningerMeyerStrongLogMellinJetLM_linearIndependent w m)
    (fun k : Fin m => iteratedDeriv k f w)
  have hreg := deningerMeyerStrongLogMellin_entireRegular g
  have hA : AnalyticAt ℂ (deningerMeyerStrongLogMellin g) w :=
    hreg.differentiable.differentiableOn.analyticAt univ_mem
  refine ⟨_, hreg, (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA.sub hf)).mpr ?_⟩
  intro k hk
  change iteratedDeriv k (deningerMeyerStrongLogMellin g - f) w = 0
  rw [iteratedDeriv_sub hA.contDiffAt hf.contDiffAt, sub_eq_zero]
  have he := congrFun hg ⟨k, hk⟩
  simpa only [LinearMap.pi_apply, deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] using he

def deningerMeyerJetLocalizer (w : ℂ) (a : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  1 - (1 - Complex.exp ((a : ℂ) * (z-w)))^m

theorem deningerMeyerJetLocalizer_differentiable (w : ℂ) (a : ℝ) (m : ℕ) :
    Differentiable ℂ (deningerMeyerJetLocalizer w a m) := by
  unfold deningerMeyerJetLocalizer
  fun_prop

theorem deningerMeyerJetLocalizer_germ (w : ℂ) (a : ℝ) (m : ℕ) :
    (m : ℕ∞) ≤ analyticOrderAt (fun z => deningerMeyerJetLocalizer w a m z - 1) w := by
  let f : ℂ → ℂ := fun z => 1 - Complex.exp ((a : ℂ) * (z-w))
  have hf : AnalyticAt ℂ f w := by dsimp [f]; fun_prop
  have ho : (1 : ℕ∞) ≤ analyticOrderAt f w := by
    apply Order.one_le_iff_ne_zero.mpr
    intro hz
    exact (hf.analyticOrderAt_eq_zero.mp hz) (by simp [f])
  have he : (fun z => deningerMeyerJetLocalizer w a m z - 1) = -(f^m) := by
    funext z
    simp [deningerMeyerJetLocalizer, f]
  rw [he, analyticOrderAt_neg, analyticOrderAt_pow hf]
  simpa using nsmul_le_nsmul_right ho m

theorem deningerMeyerJetLocalizer_strip_bound (w : ℂ) (a : ℝ) (m : ℕ)
    (l r : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, l ≤ z.re → z.re ≤ r → ‖deningerMeyerJetLocalizer w a m z‖ ≤ C := by
  let A := Real.exp (|a| * (|l| + |r| + |w.re|))
  have hpoly : Continuous (fun t : ℂ => 1-(1-t)^m) := by fun_prop
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) A).exists_bound_of_continuousOn
    hpoly.continuousOn
  refine ⟨max 0 C, le_max_left _ _, fun z hz₁ hz₂ => ?_⟩
  apply (hC (Complex.exp ((a : ℂ)*(z-w))) ?_).trans (le_max_right _ _)
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hz : |z.re| ≤ |l| + |r| := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self l, neg_le_abs l, le_abs_self r,
      neg_le_abs r, abs_nonneg l, abs_nonneg r]
  have ht : |z.re-w.re| ≤ |l|+|r|+|w.re| :=
    (abs_sub _ _).trans (by linarith)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, zero_mul, sub_zero] using
    (le_abs_self (a*(z.re-w.re))).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ht (abs_nonneg a))

private theorem norm_one_sub_one_sub_pow_le {t : ℂ} (ht : ‖t‖ ≤ 1) (m : ℕ) :
    ‖1-(1-t)^m‖ ≤ (m : ℝ)*2^m*‖t‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
      have htwo : ‖1-t‖ ≤ 2 := by
        calc ‖1-t‖ ≤ ‖(1 : ℂ)‖+‖t‖ := norm_sub_le _ _
          _ ≤ 2 := by simp only [norm_one]; linarith
      have hp : ‖(1-t)^m*t‖ ≤ 2^m*‖t‖ := by
        rw [norm_mul, norm_pow]
        gcongr
      have he : 1-(1-t)^(m+1) = (1-(1-t)^m)+(1-t)^m*t := by
        rw [pow_succ]
        ring
      rw [he]
      calc ‖(1-(1-t)^m)+(1-t)^m*t‖
          ≤ ‖1-(1-t)^m‖+‖(1-t)^m*t‖ := norm_add_le _ _
        _ ≤ (m : ℝ)*2^m*‖t‖ + 2^m*‖t‖ := add_le_add ih hp
        _ ≤ _ := by
          rw [Nat.cast_add, Nat.cast_one, pow_succ]
          have hb : 0 ≤ (2 : ℝ)^m*‖t‖ := by positivity
          nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by positivity) hb]

/-- A full jet can be fixed while its multiplier becomes arbitrarily small
on a strict inner vertical strip. -/
theorem exists_deningerMeyerJetLocalizer (w : ℂ) (m : ℕ) {r ε : ℝ}
    (hw : r < |w.re|) (hε : 0 < ε) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖L z‖ ≤ C) ∧
      (m : ℕ∞) ≤ analyticOrderAt (fun z => L z - 1) w ∧
      ∀ z : ℂ, |z.re| ≤ r → ‖L z‖ ≤ ε := by
  let σ : ℝ := if 0 ≤ w.re then 1 else -1
  let q : ℝ := Real.exp (r-|w.re|)
  have hq₀ : 0 ≤ q := (Real.exp_pos _).le
  have hq₁ : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have ht : Tendsto (fun n : ℕ => ((m : ℝ)*2^m)*q^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).const_mul ((m : ℝ)*2^m)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨deningerMeyerJetLocalizer w ((n : ℝ)*σ) m,
    deningerMeyerJetLocalizer_differentiable _ _ _,
    deningerMeyerJetLocalizer_strip_bound _ _ _, deningerMeyerJetLocalizer_germ _ _ _, ?_⟩
  intro z hz
  have hs : σ*(z.re-w.re) ≤ r-|w.re| := by
    dsimp [σ]
    split_ifs with h
    · rw [abs_of_nonneg h]
      linarith [le_abs_self z.re]
    · rw [abs_of_neg (lt_of_not_ge h)]
      linarith [neg_le_abs z.re]
  have he : ‖Complex.exp ((((n : ℝ)*σ : ℝ) : ℂ)*(z-w))‖ ≤ q^n := by
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, zero_mul, sub_zero, mul_assoc] using
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)
  have he₁ : ‖Complex.exp ((((n : ℝ)*σ : ℝ) : ℂ)*(z-w))‖ ≤ 1 :=
    he.trans (pow_le_one₀ hq₀ hq₁.le)
  exact (norm_one_sub_one_sub_pow_le he₁ m).trans
    ((mul_le_mul_of_nonneg_left he (by positivity)).trans hn.le)

end
end RHTower
