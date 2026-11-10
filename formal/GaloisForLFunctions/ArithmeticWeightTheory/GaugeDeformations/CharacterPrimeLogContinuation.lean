import GaloisForLFunctions.RHTower.DirichletLEulerLogarithmRightOfTheOneLine
import GaloisForLFunctions.RHTower.Sieve.LogNormSegment
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeLogarithmRenormalization

/-!
# Bounded continuation of nonprincipal character prime logarithms

The higher-prime-power remainder is holomorphic for `Re s>1/2`, including
ramified primes. A local logarithm of the nonvanishing Dirichlet L-function
extends the actual prime logarithm through one. Gluing to the convergent
prime series gives a bounded horizontal tube, stable under nonnegative
real translations. Absolutely summable Taylor coefficients can therefore
be shifted and summed on that tube.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
variable {Q : ℕ}

/-- The prime part of a Dirichlet Euler logarithm. -/
def characterPrimeLog (χ : DirichletCharacter ℂ Q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-s)

/-- Higher prime powers, including the zero terms at ramified primes. -/
def characterHigherPrimeLog (χ : DirichletCharacter ℂ Q) (s : ℂ) : ℂ :=
  hullRem s (fun n : ℕ => χ n)

private theorem norm_characterEulerVar_le (χ : DirichletCharacter ℂ Q)
    (p : Nat.Primes) (s : ℂ) :
    ‖eulerVar s (fun n : ℕ => χ n) p‖ ≤ (p : ℝ) ^ (-s.re) := by
  simpa only [eulerVar, powCoeff, mul_comm] using norm_char_prime_cpow_le χ (w := s) p

/-- Ramification does not change the quadratic Euler-remainder majorant. -/
theorem norm_characterLocalRem_le (χ : DirichletCharacter ℂ Q)
    (p : Nat.Primes) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖localRem s (fun n : ℕ => χ n) p‖ ≤ 2 * (p : ℝ) ^ (-(2 * s.re)) := by
  let z := eulerVar s (fun n : ℕ => χ n) p
  have hcomp : ‖z‖ ≤ ‖eulerVar s (twist 0) p‖ := by
    rw [norm_eulerVar (norm_twist_prime 0) p.2]
    exact norm_characterEulerVar_le χ p s
  have hsmall : ‖z‖ ≤ 3 / 4 := hcomp.trans (norm_eulerVar_le (norm_twist_prime 0) p.2 hs)
  have hsq : ‖z‖ ^ 2 ≤ (p : ℝ) ^ (-(2 * s.re)) := by
    have hh := pow_le_pow_left₀ (norm_nonneg z) hcomp 2
    rwa [norm_eulerVar_sq (norm_twist_prime 0) p.2] at hh
  have hlog := Complex.norm_log_one_add_sub_self_le (z := -z) (by
    rw [norm_neg]
    linarith only [hsmall])
  rw [norm_neg] at hlog
  have hinv : (1 - ‖z‖)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith only [hsmall]) (by norm_num)]
    linarith only [hsmall]
  have heq : localRem s (fun n : ℕ => χ n) p = -(Complex.log (1 + -z) - -z) := by
    dsimp only [localRem, z]
    rw [← sub_eq_add_neg]
    ring
  rw [heq, norm_neg]
  apply hlog.trans
  have hm := mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖z‖)
  nlinarith only [hm, hsq]

theorem summable_characterLocalRem (χ : DirichletCharacter ℂ Q) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes => localRem s (fun n : ℕ => χ n) p) :=
  Summable.of_norm_bounded
    ((Nat.Primes.summable_rpow.mpr (by linarith only [hs] : -(2 * s.re) < -1)).mul_left 2)
    (fun p => norm_characterLocalRem_le χ p hs)

private theorem differentiableAt_characterLocalRem (χ : DirichletCharacter ℂ Q)
    (p : Nat.Primes) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun w => localRem w (fun n : ℕ => χ n) p) s := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hd : DifferentiableAt ℂ (fun w => eulerVar w (fun n : ℕ => χ n) p) s := by
    dsimp only [eulerVar, powCoeff]
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hp0)).mul_const _
  have hnorm : ‖eulerVar s (fun n : ℕ => χ n) p‖ < 1 := by
    have hh : ‖eulerVar s (fun n : ℕ => χ n) p‖ ≤ ‖eulerVar s (twist 0) p‖ := by
      rw [norm_eulerVar (norm_twist_prime 0) p.2]
      exact norm_characterEulerVar_le χ p s
    exact (hh.trans (norm_eulerVar_le (norm_twist_prime 0) p.2 hs)).trans_lt (by norm_num)
  have hslit : 1 - eulerVar s (fun n : ℕ => χ n) p ∈ Complex.slitPlane := by
    rw [sub_eq_add_neg]
    apply Complex.mem_slitPlane_of_norm_lt_one
    simpa only [norm_neg] using hnorm
  exact (((differentiableAt_const _).sub hd).clog hslit).neg.sub hd

/-- The character Euler remainder is holomorphic throughout `Re s>1/2`. -/
theorem analyticOnNhd_characterHigherPrimeLog (χ : DirichletCharacter ℂ Q) :
    AnalyticOnNhd ℂ (characterHigherPrimeLog χ) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  change 1 / 2 < s.re at hs
  let b := (s.re + 1 / 2) / 2
  have hb : 1 / 2 < b := by dsimp only [b]; linarith only [hs]
  have hbs : b < s.re := by dsimp only [b]; linarith only [hs]
  have hU : IsOpen {w : ℂ | b < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsum : Summable (fun p : Nat.Primes => 2 * (p : ℝ) ^ (-(2 * b))) :=
    (Nat.Primes.summable_rpow.mpr (by linarith only [hb])).mul_left 2
  have hd : DifferentiableOn ℂ (characterHigherPrimeLog χ) {w : ℂ | b < w.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun p w hw => (differentiableAt_characterLocalRem χ p (hb.trans hw)).differentiableWithinAt) hU
    intro p w hw
    change b < w.re at hw
    apply (norm_characterLocalRem_le χ p (hb.trans hw)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (by linarith only [hw])
  exact hd.analyticAt (hU.mem_nhds hbs)

theorem summable_characterPrimeTerm (χ : DirichletCharacter ℂ Q) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => χ p * ((p : ℕ) : ℂ) ^ (-s)) :=
  Summable.of_norm_bounded (Nat.Primes.summable_rpow.mpr (by linarith only [hs]))
    (fun p => norm_char_prime_cpow_le χ p)

/-- Exact separation of the prime and higher-prime-power parts. -/
theorem eulerLog_eq_characterPrimeLog_add (χ : DirichletCharacter ℂ Q)
    {s : ℂ} (hs : 1 < s.re) :
    eulerLog χ s = characterPrimeLog χ s + characterHigherPrimeLog χ s := by
  rw [eulerLog, characterPrimeLog, characterHigherPrimeLog, hullRem,
    ← (summable_characterPrimeTerm χ hs).tsum_add
      (summable_characterLocalRem χ (by linarith only [hs]))]
  apply tsum_congr
  intro p
  simp only [localRem, eulerVar, powCoeff]
  rw [mul_comm (((p : ℕ) : ℂ) ^ (-s)) (χ p)]
  ring

private theorem analyticOnNhd_characterEulerLog (χ : DirichletCharacter ℂ Q) :
    AnalyticOnNhd ℂ (eulerLog χ) {s : ℂ | 1 < s.re} := by
  have hd : DifferentiableOn ℂ (eulerLog χ) {s : ℂ | 1 < s.re} :=
    fun s hs => (differentiableAt_eulerLog χ hs).differentiableWithinAt
  exact fun s hs => hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

theorem analyticOnNhd_characterPrimeLog (χ : DirichletCharacter ℂ Q) :
    AnalyticOnNhd ℂ (characterPrimeLog χ) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have ha := (analyticOnNhd_characterEulerLog χ s hs).sub
    (analyticOnNhd_characterHigherPrimeLog χ s (by change 1 / 2 < s.re; linarith only [hs]))
  apply ha.congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  change eulerLog χ w - characterHigherPrimeLog χ w = characterPrimeLog χ w
  rw [eulerLog_eq_characterPrimeLog_add χ hw]
  simp only [add_sub_cancel_right]

variable [NeZero Q]

/-- A local logarithm is aligned with the actual Euler logarithm by its derivative. -/
theorem exists_characterEulerLog_germ {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G (ball 1 r) ∧
      ∀ s : ℂ, s ∈ ball 1 r → 1 < s.re → eulerLog χ s = G s := by
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have hL1 : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have hnear : ∀ᶠ s : ℂ in 𝓝 1, DirichletCharacter.LFunction χ s ≠ 0 :=
    hL.continuous.continuousAt.eventually_ne hL1
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min r₀ (1 / 4)
  have hr : 0 < r := lt_min hr₀ (by norm_num)
  have hr₀' : r ≤ r₀ := min_le_left _ _
  have hnr : ∀ s ∈ ball (1 : ℂ) r, DirichletCharacter.LFunction χ s ≠ 0 :=
    fun s hs => hball (ball_subset_ball hr₀' hs)
  obtain ⟨g, hg, hexp⟩ := exists_analyticOnNhd_exp_eq_ball hr
    (fun s _ => hL.analyticAt s) hnr
  let c : ℂ := ((1 + r / 2 : ℝ) : ℂ)
  have hc : c ∈ ball (1 : ℂ) r := by
    rw [mem_ball, dist_eq_norm]
    have hh : c - 1 = ((r / 2 : ℝ) : ℂ) := by dsimp only [c]; push_cast; ring
    rw [hh, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hr] : 0 < r / 2)]
    linarith only [hr]
  have hc1 : 1 < c.re := by dsimp only [c]; simp only [Complex.ofReal_re]; linarith only [hr]
  let G : ℂ → ℂ := fun s => g s + (eulerLog χ c - g c)
  have hG : AnalyticOnNhd ℂ G (ball 1 r) := fun s hs => (hg s hs).add analyticAt_const
  let D : Set ℂ := ball 1 r ∩ {s : ℂ | 1 < s.re}
  have hDo : IsOpen D := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hDc : IsPreconnected D := ((convex_ball (1 : ℂ) r).inter (convex_halfSpace_re_gt 1)).isPreconnected
  have hEq := hDo.eqOn_of_deriv_eq hDc
    (hG.differentiableOn.mono inter_subset_left)
    ((analyticOnNhd_characterEulerLog χ).differentiableOn.mono inter_subset_right)
    (fun s hs => by
      change deriv (fun s => g s + (eulerLog χ c - g c)) s = deriv (eulerLog χ) s
      rw [deriv_add_const, Sieve.deriv_analyticLog_eq hnr hg hexp hs.1,
        (hasDerivAt_eulerLog χ hs.2).deriv, logDeriv_apply])
    (show c ∈ D from ⟨hc, hc1⟩) (by dsimp only [G]; ring)
  exact ⟨r, hr, min_le_right _ _, G, hG, fun s hs hse => (hEq ⟨hs, hse⟩).symm⟩

/-- Nonprincipal character prime logarithms extend analytically through one. -/
theorem exists_characterPrimeLog_germ {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 1 r) ∧
      ∀ s : ℂ, s ∈ ball 1 r → 1 < s.re → characterPrimeLog χ s = F s := by
  obtain ⟨r, hr, hr4, G, hG, he⟩ := exists_characterEulerLog_germ hχ
  have hhalf (s : ℂ) (hs : s ∈ ball (1 : ℂ) r) : 1 / 2 < s.re := by
    have hn : ‖s - 1‖ < r := by simpa only [mem_ball, dist_eq_norm] using hs
    have hh := Complex.re_le_norm (1 - s)
    rw [norm_sub_rev] at hh
    simp only [Complex.sub_re, Complex.one_re] at hh
    linarith only [hn, hh, hr4]
  refine ⟨r, hr, fun s => G s - characterHigherPrimeLog χ s,
    fun s hs => (hG s hs).sub (analyticOnNhd_characterHigherPrimeLog χ s (hhalf s hs)), ?_⟩
  intro s hs hse
  change characterPrimeLog χ s = G s - characterHigherPrimeLog χ s
  rw [← he s hs hse, eulerLog_eq_characterPrimeLog_add χ hse, add_sub_cancel_right]

#print axioms analyticOnNhd_characterHigherPrimeLog
#print axioms exists_characterEulerLog_germ
#print axioms exists_characterPrimeLog_germ

/-- A horizontal rectangle of half-width `e` lies in the ball of radius `2e`. -/
private theorem character_box_norm {e : ℝ} {s : ℂ}
    (hleft : 1 - e < s.re) (hright : s.re ≤ 1 + e) (him : |s.im| < e) :
    ‖s - 1‖ < 2 * e := by
  have hre : |s.re - 1| ≤ e := abs_le.mpr ⟨by linarith only [hleft], by linarith only [hright]⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (s - 1)
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at hn
  linarith only [hre, him, hn]

/-- The actual character prime sum extends as a bounded holomorphic function on a
rightward horizontal tube through one. -/
theorem exists_bounded_characterPrimeLog_tube {χ : DirichletCharacter ℂ Q}
    (hχ : χ ≠ 1) :
    ∃ e : ℝ, 0 < e ∧ ∃ F : ℂ → ℂ, ∃ C : ℝ, 0 ≤ C ∧
      AnalyticOnNhd ℂ F {s : ℂ | 1 - e < s.re ∧ |s.im| < e} ∧
      (∀ s : ℂ, 1 - e < s.re → |s.im| < e → ‖F s‖ ≤ C) ∧
      (∀ s : ℂ, 1 < s.re → F s = characterPrimeLog χ s) := by
  obtain ⟨r, hr, g, hg, he⟩ := exists_characterPrimeLog_germ hχ
  let e := r / 8
  have he0 : 0 < e := by dsimp only [e]; positivity
  let F : ℂ → ℂ := fun s => if 1 < s.re then characterPrimeLog χ s else g s
  have hFr (s : ℂ) (hs : 1 < s.re) : F s = characterPrimeLog χ s := if_pos hs
  have hFg (s : ℂ) (hs : s ∈ ball 1 r) : F s = g s := by
    dsimp only [F]
    split_ifs with hs1
    · exact he s hs hs1
    · rfl
  have hball (s : ℂ) (hl : 1 - e < s.re) (hu : s.re ≤ 1 + e) (hi : |s.im| < e) :
      s ∈ ball (1 : ℂ) (r / 2) := by
    rw [mem_ball, dist_eq_norm]
    apply (character_box_norm hl hu hi).trans
    dsimp only [e]
    linarith only [hr]
  have hF : AnalyticOnNhd ℂ F {s : ℂ | 1 - e < s.re ∧ |s.im| < e} := by
    intro s hs
    by_cases hs1 : 1 < s.re
    · apply (analyticOnNhd_characterPrimeLog χ s hs1).congr
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1] with w hw
      exact (hFr w hw).symm
    · have hsr : s ∈ ball (1 : ℂ) r :=
        ball_subset_ball (by linarith only [hr])
          (hball s hs.1 (by linarith only [le_of_not_gt hs1, he0]) hs.2)
      apply (hg s hsr).congr
      filter_upwards [isOpen_ball.mem_nhds hsr] with w hw
      exact (hFg w hw).symm
  have hgc : ContinuousOn g (closedBall (1 : ℂ) (r / 2)) :=
    hg.continuousOn.mono (closedBall_subset_ball (by linarith only [hr]))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℂ) (r / 2)).exists_bound_of_continuousOn hgc
  let M : ℝ := ∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + e))
  have hsum : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 + e))) :=
    Nat.Primes.summable_rpow.mpr (by linarith only [he0])
  refine ⟨e, he0, F, max 0 (max B M), le_max_left _ _, hF, ?_, hFr⟩
  intro s hl hi
  by_cases hs : s.re ≤ 1 + e
  · have hsr := hball s hl hs hi
    rw [hFg s (ball_subset_ball (by linarith only [hr]) hsr)]
    exact (hB s (ball_subset_closedBall hsr)).trans ((le_max_left B M).trans (le_max_right _ _))
  · have hs1 : 1 < s.re := by linarith only [lt_of_not_ge hs, he0]
    rw [hFr s hs1]
    have hmajor (p : Nat.Primes) : ‖χ p * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 + e)) :=
      (norm_char_prime_cpow_le χ p).trans
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
          (by linarith only [lt_of_not_ge hs]))
    have hnorm := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor
    exact ((norm_tsum_le_tsum_norm hnorm).trans
      (hnorm.tsum_le_tsum hmajor hsum)).trans
      ((le_max_right B M).trans (le_max_right _ _))

#print axioms exists_bounded_characterPrimeLog_tube

/-- Nonnegative real translation preserves the horizontal continuation tube. -/
private theorem character_shift_mem {e t : ℝ} (ht : 0 ≤ t) (n : ℕ) {s : ℂ}
    (hs : 1 - e < s.re ∧ |s.im| < e) :
    1 - e < (s + (n : ℂ) * (t : ℂ)).re ∧ |(s + (n : ℂ) * (t : ℂ)).im| < e := by
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    Complex.add_im, Complex.mul_im, add_zero]
  exact ⟨hs.1.trans_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) ht)), hs.2⟩

/-- Absolutely summable profile coefficients can be shifted throughout the tube. -/
def characterShiftSeries (c : ℕ → ℂ) (F : ℂ → ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, c n * F (s + (n : ℂ) * (t : ℂ))

theorem analyticOnNhd_characterShiftSeries {e C : ℝ} {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hF : AnalyticOnNhd ℂ F {s : ℂ | 1 - e < s.re ∧ |s.im| < e})
    (hb : ∀ s : ℂ, 1 - e < s.re → |s.im| < e → ‖F s‖ ≤ C)
    (hc : Summable (fun n => ‖c n‖)) {t : ℝ} (ht : 0 ≤ t) :
    AnalyticOnNhd ℂ (characterShiftSeries c F t) {s : ℂ | 1 - e < s.re ∧ |s.im| < e} := by
  have ho : IsOpen {s : ℂ | 1 - e < s.re ∧ |s.im| < e} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hd : DifferentiableOn ℂ (characterShiftSeries c F t)
      {s : ℂ | 1 - e < s.re ∧ |s.im| < e} := by
    refine Complex.differentiableOn_tsum_of_summable_norm (hc.mul_right C) (fun n s hs => ?_) ho ?_
    · exact (analyticAt_const.mul ((hF _ (character_shift_mem ht n hs)).comp
        (f := fun w : ℂ => w + (n : ℂ) * (t : ℂ))
        (analyticAt_id.add analyticAt_const))).differentiableAt.differentiableWithinAt
    · intro n s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb _ (character_shift_mem ht n hs).1
        (character_shift_mem ht n hs).2) (norm_nonneg _)
  exact fun s hs => hd.analyticAt (ho.mem_nhds hs)

theorem continuousOn_characterShiftSeries {e C : ℝ} {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hF : AnalyticOnNhd ℂ F {s : ℂ | 1 - e < s.re ∧ |s.im| < e})
    (hb : ∀ s : ℂ, 1 - e < s.re → |s.im| < e → ‖F s‖ ≤ C)
    (hc : Summable (fun n => ‖c n‖)) :
    ContinuousOn (fun q : ℝ × ℂ => characterShiftSeries c F q.1 q.2)
      (Ici 0 ×ˢ {s : ℂ | 1 - e < s.re ∧ |s.im| < e}) := by
  refine continuousOn_tsum (fun n q hq => ?_) (hc.mul_right C) (fun n q hq => ?_)
  · have hmap : ContinuousAt (fun q : ℝ × ℂ => q.2 + (n : ℂ) * (q.1 : ℂ)) q := by fun_prop
    exact (((hF _ (character_shift_mem hq.1 n hq.2)).continuousAt.comp (g := F)
      (f := fun q : ℝ × ℂ => q.2 + (n : ℂ) * (q.1 : ℂ)) hmap).const_mul
      (c n)).continuousWithinAt
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _ (character_shift_mem hq.1 n hq.2).1
      (character_shift_mem hq.1 n hq.2).2) (norm_nonneg _)

theorem characterShiftSeries_zero {c : ℕ → ℂ} (F : ℂ → ℂ) (hc : ∑' n, c n = 0) (s : ℂ) :
    characterShiftSeries c F 0 s = 0 := by
  simp only [characterShiftSeries, Complex.ofReal_zero, mul_zero, add_zero, tsum_mul_right, hc, zero_mul]
#print axioms analyticOnNhd_characterShiftSeries
#print axioms continuousOn_characterShiftSeries
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
