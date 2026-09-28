import GaloisForLFunctions.RHTower.ThetaCompactTailInterpolation
import GaloisForLFunctions.RHTower.ThetaDerivativePacketSpectralBoundary

/-!
# Schwartz convergence of the logarithmic interpolants

Write `b_R - k_t = k_t (e^{φ_R} - 1)` with `φ_R = (χ_R - 1) L ≤ 0` on the tail. Every derivative of
`φ_R` of order `≤ n` is at most a fixed power `D = K q^d` of the tail scale, uniformly in `R`, since
the window derivatives are uniformly bounded and all derivatives of `L` are moderate; Faà di Bruno
for the exponential gives `|(e^{φ_R})^{(j)}| ≤ j! D^j`. Against the super-exponential decay of every
derivative of `k_t` this yields `|x|^p |(b_R - k_t)^{(n)}(x)| ≤ C e^{-R}` for all `x` and all large
`R`. Hence `b_R → k_t` in the Schwartz topology, in every exponentially weighted `L¹` norm, and in
every moment.
-/
open Filter Topology Set MeasureTheory
open scoped ContDiff

namespace RHTower

noncomputable section

theorem ThetaTailModerate.abs {f : ℝ → ℝ} (hf : ThetaTailModerate f) :
    ThetaTailModerate (fun x => |f x|) := by
  obtain ⟨C, d, h⟩ := hf
  exact ⟨C, d, h.mono fun x hx => by rwa [abs_abs]⟩

theorem iteratedDeriv_real_exp (j : ℕ) : iteratedDeriv j Real.exp = Real.exp := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

/-- Faà di Bruno for the exponential: if every derivative of order `1..j` of `φ` at `x` is at most
`D^i` and `φ(x) ≤ 0`, then `|(e^φ)^{(j)}(x)| ≤ j! D^j`. -/
theorem abs_iteratedDeriv_exp_comp_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : ℕ) {x D : ℝ}
    (hx : φ x ≤ 0) (hD : ∀ i, 1 ≤ i → i ≤ j → |iteratedDeriv i φ x| ≤ D ^ i) :
    |iteratedDeriv j (fun y => Real.exp (φ y)) x| ≤ j.factorial * D ^ j := by
  have h := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := φ) (n := j) (N := ∞)
    Real.contDiff_exp hφ (by norm_cast; exact le_top) x (C := 1) (D := D)
    (fun i _ => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_exp, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 hx)
    (fun i hi1 hij => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact hD i hi1 hij)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, mul_one] at h
  exact h

section Convergence

variable {m : ℕ} {t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) (hpos : ∀ x, 0 < thetaDerivativePacket m t x)
include hm ht hpos

/-- **Uniform tail bound for all derivatives of `b_R - k_t`.** For fixed `n, p` there are `X, C`
such that for every `R ≥ X`, `|x|^p |(b_R - k_t)^{(n)}(x)| ≤ C e^{-R}` on all of `ℝ`. -/
theorem exists_weighted_iteratedDeriv_thetaTailInterpolant_sub_le (n p : ℕ) :
    ∃ X C : ℝ, 0 ≤ C ∧ ∀ R ≥ X, ∀ x : ℝ,
      |x| ^ p * |iteratedDeriv n (fun y => thetaTailInterpolant m t R y -
        thetaDerivativePacket m t y) x| ≤ C * Real.exp (-R) := by
  -- uniform window bounds
  have hW : ∀ a, ∃ W : ℝ, 0 ≤ W ∧ ∀ R : ℝ, 0 < R → ∀ x,
      |iteratedDeriv a (fun y => thetaTailWindow R y - 1) x| ≤ W := by
    intro a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · refine ⟨1, zero_le_one, fun R _ x => ?_⟩
      rw [iteratedDeriv_zero, abs_le]
      constructor <;> linarith [thetaTailWindow_nonneg R x, thetaTailWindow_le_one R x]
    · obtain ⟨C, hC, hb⟩ := exists_bound_iteratedDeriv_thetaTailWindow a
      refine ⟨C, hC, fun R hR x => ?_⟩
      have hsub : iteratedDeriv a (fun y => thetaTailWindow R y - 1) x =
          iteratedDeriv a (thetaTailWindow R) x := by
        have h := iteratedDeriv_sub (f := thetaTailWindow R) (g := fun _ => (1 : ℝ)) (x := x)
          (n := a) ((contDiff_thetaTailWindow R).contDiffAt.of_le (by norm_cast; exact le_top))
          (contDiff_const.contDiffAt)
        rw [iteratedDeriv_const, if_neg ha.ne', sub_zero] at h
        exact h
      rw [hsub]
      exact hb R hR x
  choose W hW0 hWb using hW
  -- the moderate envelope for all derivatives of `φ_R = (χ_R - 1) L` up to order `n`
  set G : ℝ → ℝ := fun x => ∑ j ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (j + 1),
    (j.choose a : ℝ) * W a * |iteratedDeriv (j - a) (thetaPacketLogRatio m t) x|
  have hG : ThetaTailModerate G := by
    refine ThetaTailModerate.finset_sum _ fun j _ => ThetaTailModerate.finset_sum _ fun a _ => ?_
    exact (ThetaTailModerate.const _).mul
      (thetaTailModerate_iteratedDeriv_thetaPacketLogRatio m hm ht hpos (j - a)).abs
  obtain ⟨K, d, hK⟩ := hG
  -- the decay of `k_t` and its derivatives up to order `n`
  have hdec : ∀ i, ∃ Ci, ∀ x, Real.exp ((2 * d * n + 2 : ℝ) * |x|) *
      |iteratedDeriv i (thetaDerivativePacket m t) x| ≤ Ci :=
    fun i => (thetaExpDecaySource_thetaDerivativePacket m t).2.2 _ i
  choose Cd hCd using hdec
  have hCd0 : ∀ i, 0 ≤ Cd i := fun i => le_trans (by positivity) (hCd i 0)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 (hK.and ((eventually_thetaPacketLogRatio_nonneg m hm ht).and
    eventually_one_le_thetaTailScale))
  set Kp := max K 1
  set Hc := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cd i
  set C := p.factorial * (2 * n.factorial * Kp ^ n * Real.pi ^ (d * n) * Hc)
  have hHc : 0 ≤ Hc := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hCd0 i)
  refine ⟨max X₁ 1, C, by positivity, fun R hR x => ?_⟩
  have hR0 : 0 < R := by linarith [le_max_right X₁ 1]
  set φ : ℝ → ℝ := fun y => (thetaTailWindow R y - 1) * thetaPacketLogRatio m t y
  have hφ : ContDiff ℝ ∞ φ :=
    ((contDiff_thetaTailWindow R).sub contDiff_const).mul (contDiff_thetaPacketLogRatio m t hpos)
  have hfun : (fun y => thetaTailInterpolant m t R y - thetaDerivativePacket m t y) =
      fun y => thetaDerivativePacket m t y * Real.exp (φ y) - thetaDerivativePacket m t y := by
    funext y
    rw [thetaTailInterpolant_eq_mul_exp hpos]
  -- the estimate at points `y ≥ R`
  have hmain : ∀ y, R ≤ y → |y| ^ p * |iteratedDeriv n (fun z => thetaTailInterpolant m t R z -
      thetaDerivativePacket m t z) y| ≤ C * Real.exp (-R) := by
    intro y hy
    have hyX : X₁ ≤ y := (le_max_left _ _).trans (hR.trans hy)
    obtain ⟨hGy, hLy, hqy⟩ := hX₁ y hyX
    set q := thetaCuspSingleAtomReflectionScale 1 y
    set D := Kp * q ^ d
    have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hqy)
    have hφy : φ y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [thetaTailWindow_le_one R y]) hLy
    -- derivatives of `φ`
    have hφD : ∀ j ≤ n, |iteratedDeriv j φ y| ≤ D := by
      intro j hj
      have hmul := iteratedDeriv_fun_mul (n := j) (x := y)
        (f := fun z => thetaTailWindow R z - 1) (g := thetaPacketLogRatio m t)
        (((contDiff_thetaTailWindow R).sub (contDiff_const (c := (1 : ℝ)))).contDiffAt.of_le
          (by norm_cast; exact le_top))
        ((contDiff_thetaPacketLogRatio m t hpos).contDiffAt.of_le (by norm_cast; exact le_top))
      have hle : |iteratedDeriv j φ y| ≤ ∑ a ∈ Finset.range (j + 1),
          (j.choose a : ℝ) * W a * |iteratedDeriv (j - a) (thetaPacketLogRatio m t) y| := by
        change |iteratedDeriv j (fun z => (thetaTailWindow R z - 1) * thetaPacketLogRatio m t z) y| ≤ _
        rw [hmul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j.choose a)]
        gcongr
        exact hWb a R hR0 y
      have hGle : ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * W a *
          |iteratedDeriv (j - a) (thetaPacketLogRatio m t) y| ≤ G y :=
        Finset.single_le_sum (f := fun j => ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * W a *
          |iteratedDeriv (j - a) (thetaPacketLogRatio m t) y|)
          (fun j _ => Finset.sum_nonneg fun a _ => by
            have := hW0 a; positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
      have hGD : G y ≤ D := by
        have := (le_abs_self (G y)).trans hGy
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pow_nonneg (by linarith) _))
      exact hle.trans (hGle.trans hGD)
    have hexp : ∀ j ≤ n, |iteratedDeriv j (fun z => Real.exp (φ z)) y| ≤ n.factorial * D ^ n := by
      intro j hj
      have h := abs_iteratedDeriv_exp_comp_le hφ j hφy (D := D) fun i hi1 hij =>
        (hφD i (hij.trans hj)).trans (le_self_pow₀ hD1 (by omega))
      refine h.trans ?_
      have h1 : (j.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hj
      have h2 : D ^ j ≤ D ^ n := pow_le_pow_right₀ hD1 hj
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    -- Leibniz for `k_t e^φ`
    set H := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      |iteratedDeriv i (thetaDerivativePacket m t) y|
    have hkt := contDiff_thetaDerivativePacket m t
    have hprod : |iteratedDeriv n (fun z => thetaDerivativePacket m t z * Real.exp (φ z)) y| ≤
        n.factorial * D ^ n * H := by
      rw [iteratedDeriv_fun_mul (hkt.contDiffAt.of_le (by norm_cast; exact le_top))
        ((hφ.exp).contDiffAt.of_le (by norm_cast; exact le_top))]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n.choose i)]
      have := hexp (n - i) (Nat.sub_le n i)
      calc (n.choose i : ℝ) * |iteratedDeriv i (thetaDerivativePacket m t) y| *
            |iteratedDeriv (n - i) (fun z => Real.exp (φ z)) y|
          ≤ (n.choose i : ℝ) * |iteratedDeriv i (thetaDerivativePacket m t) y| *
            (n.factorial * D ^ n) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hsub : iteratedDeriv n (fun z => thetaTailInterpolant m t R z -
        thetaDerivativePacket m t z) y =
        iteratedDeriv n (fun z => thetaDerivativePacket m t z * Real.exp (φ z)) y -
          iteratedDeriv n (thetaDerivativePacket m t) y := by
      rw [hfun]
      exact iteratedDeriv_sub ((hkt.mul hφ.exp).contDiffAt.of_le (by norm_cast; exact le_top))
        (hkt.contDiffAt.of_le (by norm_cast; exact le_top))
    have hkn : |iteratedDeriv n (thetaDerivativePacket m t) y| ≤ H := by
      have := Finset.single_le_sum (f := fun i => (n.choose i : ℝ) *
          |iteratedDeriv i (thetaDerivativePacket m t) y|)
        (fun i _ => by positivity) (Finset.self_mem_range_succ n)
      simpa using this
    have hD1' : (1 : ℝ) ≤ n.factorial * D ^ n :=
      one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n))
        (one_le_pow₀ hD1)
    have hH0 : 0 ≤ H := Finset.sum_nonneg fun i _ => by positivity
    have hder : |iteratedDeriv n (fun z => thetaTailInterpolant m t R z -
        thetaDerivativePacket m t z) y| ≤ 2 * n.factorial * D ^ n * H := by
      rw [hsub]
      calc _ ≤ |iteratedDeriv n (fun z => thetaDerivativePacket m t z * Real.exp (φ z)) y| +
            |iteratedDeriv n (thetaDerivativePacket m t) y| := abs_sub _ _
        _ ≤ n.factorial * D ^ n * H + n.factorial * D ^ n * H := by nlinarith
        _ = _ := by ring
    -- decay: `H ≤ Hc e^{-(2dn+2) y}` and `q^{dn} = π^{dn} e^{2dny}`
    have hy0 : 0 ≤ y := by linarith
    have hHy : H ≤ Hc * Real.exp (-(2 * d * n + 2 : ℝ) * y) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h := hCd i y
      rw [abs_of_nonneg hy0] at h
      rw [show -(2 * d * n + 2 : ℝ) * y = -((2 * d * n + 2 : ℝ) * y) by ring, Real.exp_neg,
        le_mul_inv_iff₀ (Real.exp_pos _), mul_comm]
      exact h
    have hqy' : q ^ (d * n) = Real.pi ^ (d * n) * Real.exp ((2 * d * n : ℝ) * y) := by
      simp only [q, thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hpy : |y| ^ p ≤ p.factorial * Real.exp y := by
      rw [abs_of_nonneg hy0]
      have h := Real.pow_div_factorial_le_exp _ hy0 p
      rw [div_le_iff₀ (by positivity)] at h
      linarith
    have hDn : D ^ n = Kp ^ n * q ^ (d * n) := by
      simp only [D]; rw [mul_pow, ← pow_mul]
    calc |y| ^ p * |iteratedDeriv n (fun z => thetaTailInterpolant m t R z -
          thetaDerivativePacket m t z) y|
        ≤ (p.factorial * Real.exp y) * (2 * n.factorial * D ^ n * H) :=
          mul_le_mul hpy hder (abs_nonneg _) (by positivity)
      _ ≤ (p.factorial * Real.exp y) * (2 * n.factorial * (Kp ^ n * (Real.pi ^ (d * n) *
            Real.exp ((2 * d * n : ℝ) * y))) * (Hc * Real.exp (-(2 * d * n + 2 : ℝ) * y))) := by
          rw [hDn, hqy']
          gcongr
      _ = C * Real.exp (-y) := by
          simp only [C]
          rw [show Real.exp (-y) = Real.exp y * Real.exp ((2 * d * n : ℝ) * y) *
            Real.exp (-(2 * d * n + 2 : ℝ) * y) by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring]
          ring
      _ ≤ C * Real.exp (-R) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
  -- inside `(-R, R)` the difference vanishes near `x`; outside use evenness
  rcases lt_or_ge |x| R with hx | hx
  · have hzero : (fun z => thetaTailInterpolant m t R z - thetaDerivativePacket m t z) =ᶠ[𝓝 x]
        fun _ => 0 :=
      (thetaTailInterpolant_eventuallyEq_packet hpos hx).mono fun z hz => by simp [hz]
    rw [hzero.iteratedDeriv_eq, iteratedDeriv_const]
    split_ifs <;> simp [C] <;> positivity
  · rcases le_or_gt 0 x with hx0 | hx0
    · exact hmain x (by rwa [abs_of_nonneg hx0] at hx)
    · have heven : (fun z => thetaTailInterpolant m t R z - thetaDerivativePacket m t z) =
          fun z => (fun w => thetaTailInterpolant m t R w - thetaDerivativePacket m t w) (-z) := by
        funext z; simp only [thetaTailInterpolant_neg, thetaDerivativePacket_neg]
      have hsym : |iteratedDeriv n (fun z => thetaTailInterpolant m t R z -
          thetaDerivativePacket m t z) x| = |iteratedDeriv n (fun z => thetaTailInterpolant m t R z -
          thetaDerivativePacket m t z) (-x)| := by
        conv_lhs => rw [heven]
        rw [iteratedDeriv_comp_neg n (fun w => thetaTailInterpolant m t R w -
          thetaDerivativePacket m t w) x, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          one_mul]
      rw [hsym, ← abs_neg x]
      exact hmain (-x) (by rw [abs_of_neg hx0] at hx; exact hx)

end Convergence

/-! ## Schwartz convergence and weighted integral convergence -/

section Schwartz

variable {m : ℕ} {t : ℝ} (hpos : ∀ x, 0 < thetaDerivativePacket m t x)
include hpos

theorem contDiff_thetaTailInterpolant_sub_source (R : ℝ) :
    ContDiff ℝ ∞ (fun x => thetaTailInterpolant m t R x - thetaCuspFullSource x) :=
  (contDiff_thetaTailInterpolant hpos R).sub contDiff_thetaCuspFullSource

omit hpos in
theorem hasCompactSupport_thetaTailInterpolant_sub_source (R : ℝ) :
    HasCompactSupport (fun x => thetaTailInterpolant m t R x - thetaCuspFullSource x) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + 1)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hx
  rw [thetaTailInterpolant_eq_source hx.le, sub_self]

/-- The interpolant `b_R` as a Schwartz function. -/
def thetaTailInterpolantSchwartz (R : ℝ) : SchwartzMap ℝ ℝ :=
  thetaCuspSchwartzReal + (hasCompactSupport_thetaTailInterpolant_sub_source (m := m) (t := t) R
    ).toSchwartzMap (contDiff_thetaTailInterpolant_sub_source hpos R)

theorem thetaTailInterpolantSchwartz_apply (R x : ℝ) :
    thetaTailInterpolantSchwartz hpos R x = thetaTailInterpolant m t R x := by
  simp only [thetaTailInterpolantSchwartz, add_apply,
    HasCompactSupport.toSchwartzMap_toFun, thetaCuspSchwartzReal_apply]
  ring

variable (hm : 0 < m) (ht : 0 ≤ t)
include hm ht

/-- **`b_R → k_t` in the Schwartz topology as `R → ∞`.** -/
theorem tendsto_thetaTailInterpolantSchwartz :
    Tendsto (thetaTailInterpolantSchwartz hpos) atTop (𝓝 (thetaDerivativePacketSchwartz m t)) := by
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds]
  rintro ⟨p, n⟩ ε hε
  obtain ⟨X, C, hC, hbound⟩ := exists_weighted_iteratedDeriv_thetaTailInterpolant_sub_le hm ht hpos n p
  have hexp : Tendsto (fun R : ℝ => C * Real.exp (-R)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
  filter_upwards [eventually_ge_atTop X, hexp.eventually (gt_mem_nhds hε)] with R hR hRε
  refine lt_of_le_of_lt ?_ hRε
  refine SchwartzMap.seminorm_le_bound ℝ p n _ (by positivity) fun x => ?_
  have hcoe : (⇑(thetaTailInterpolantSchwartz hpos R - thetaDerivativePacketSchwartz m t)) =
      fun y => thetaTailInterpolant m t R y - thetaDerivativePacket m t y := by
    funext y
    simp [thetaTailInterpolantSchwartz_apply]
  rw [hcoe, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs]
  exact hbound R hR x

/-- Every exponentially weighted `L¹` distance from `b_R` to `k_t` tends to zero. -/
theorem tendsto_integral_exp_mul_abs_thetaTailInterpolant_sub (c : ℝ) :
    Tendsto (fun R => ∫ x, Real.exp (c * |x|) *
      |thetaTailInterpolant m t R x - thetaDerivativePacket m t x|) atTop (𝓝 0) := by
  obtain ⟨X, hX⟩ := eventually_abs_thetaTailInterpolant_sub_le hpos hm ht
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun x => Real.exp (c * |x|) * |thetaDerivativePacket m t x|)
    (F := fun R x => Real.exp (c * |x|) *
      |thetaTailInterpolant m t R x - thetaDerivativePacket m t x|) (f := fun _ => 0)
    (Eventually.of_forall fun R => by
      have := (contDiff_thetaTailInterpolant hpos R).continuous
      have := (contDiff_thetaDerivativePacket m t).continuous
      exact (by fun_prop : Continuous fun x => Real.exp (c * |x|) *
        |thetaTailInterpolant m t R x - thetaDerivativePacket m t x|).aestronglyMeasurable)
    ((eventually_ge_atTop X).mono fun R hR => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ((hX R hR x).trans ?_) (Real.exp_pos _).le
      split_ifs
      · exact le_abs_self _
      · exact abs_nonneg _)
    (integrable_exp_abs_mul_abs_thetaDerivativePacket m t c)
    (Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop |x|] with R hR
      rw [(thetaTailInterpolant_eventuallyEq_packet hpos hR).self_of_nhds, sub_self, abs_zero,
        mul_zero])
  simpa using h

/-- Every moment of `b_R` converges to the corresponding moment of `k_t`. -/
theorem tendsto_integral_pow_mul_thetaTailInterpolant (j : ℕ) :
    Tendsto (fun R => ∫ x, x ^ j * thetaTailInterpolant m t R x) atTop
      (𝓝 (∫ x, x ^ j * thetaDerivativePacket m t x)) := by
  obtain ⟨X, hX⟩ := eventually_abs_thetaTailInterpolant_sub_le hpos hm ht
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => 2 * |x ^ j * thetaDerivativePacket m t x|)
    (Eventually.of_forall fun R => by
      have := (contDiff_thetaTailInterpolant hpos R).continuous
      exact (by fun_prop : Continuous fun x => x ^ j * thetaTailInterpolant m t R x).aestronglyMeasurable)
    ((eventually_ge_atTop X).mono fun R hR => Eventually.of_forall fun x => ?_)
    ((integrable_pow_mul_thetaDerivativePacket m j t).norm.const_mul 2)
    (Eventually.of_forall fun x => ?_)
  · have h := hX R hR x
    have hk := hpos x
    have hle : |thetaTailInterpolant m t R x| ≤ 2 * thetaDerivativePacket m t x := by
      have : |thetaTailInterpolant m t R x - thetaDerivativePacket m t x| ≤
          thetaDerivativePacket m t x := h.trans (by split_ifs <;> linarith)
      have h2 := abs_sub_abs_le_abs_sub (thetaTailInterpolant m t R x) (thetaDerivativePacket m t x)
      rw [abs_of_pos hk] at h2
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hk]
    have := abs_nonneg (x ^ j)
    nlinarith
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop |x|] with R hR
    rw [(thetaTailInterpolant_eventuallyEq_packet hpos hR).self_of_nhds]

end Schwartz

end

end RHTower
