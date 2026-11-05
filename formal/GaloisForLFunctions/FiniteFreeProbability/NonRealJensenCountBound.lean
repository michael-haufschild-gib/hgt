import GaloisForLFunctions.FiniteFreeProbability.JensenSaddlePoint
import GaloisForLFunctions.FiniteFreeProbability.JensenCountsOffLineZeros

/-!
# At most `C √(d log d)` non-real roots: a finite degree Ki–Kim–Lee theorem

**Theorem.** For all large `d`, `R_d(Ξ)` has at least `d − 300 √(d log d)` distinct real roots. In particular the non-real count
`N_d` satisfies `N_d ≤ 300 √(d log d)`. This holds whether or not RH holds, and only `|x| ≲ √(d log d)` is used.

**Proof.** Along the saddle `a(x)`, `τ(x) = d/(a(x) − ix)`, the exact identity reads `R_d(x) = 2 Re[M(x)(1 + ε(x))]` with `‖ε‖ ≤ 1/2` and
`M(x) = (x + i a)^d G(τ) e^{−aτ}`. The phase `θ(x) = d arg(x + ia) + Im P(τ) − Im(aτ) + arg G(1)`, with `P = log(G/G(1))`, is continuous on `[0, X]`. At `x = 0` the saddle is real and
`θ(0) = dπ/2 + arg G(1)`. At `x = X`, `T = d/(X − 5)`: `d arg(X + ia) ≤ T L/2` and `|Im P(τ)|, |Im(aτ)| ≲ T L`. Where `θ(x) = kπ`, the sign of `R_d(x)` is `(−1)^k`. So the
intermediate value theorem gives `d/2 − O(T L)` sign changes on `(0, X]`, and parity doubles them. With `X = √(dL)/100`, `T L ≍ √(dL)`.

The theorem says that real-rootedness of `R_d(Ξ)` is decided by the `≲ √(d log d)` outermost roots.
-/

open Polynomial Filter Topology Complex Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

/-! ## Sign changes along a phase -/

/-- If `(−1)^k f > 0` wherever the continuous phase `g` equals `kπ`, then `m` descents of `g` by `π` give `m` zeros of `f`. -/
theorem exists_zeros_of_phase {f g : ℝ → ℝ} {b : ℝ} (hf : ContinuousOn f (Iic b)) (hg : ContinuousOn g (Iic b))
    (hsign : ∀ x ≤ b, ∀ k : ℤ, g x = k * π → 0 < (-1 : ℝ) ^ k * f x) :
    ∀ (m : ℕ) (k : ℤ) (c : ℝ), c ≤ b → k * π ≤ g c → g b ≤ (k - m) * π →
      ∃ S : Finset ℝ, S.card = m ∧ ∀ y ∈ S, c < y ∧ y ≤ b ∧ f y = 0 := by
  have hπ := Real.pi_pos
  intro m
  induction m with
  | zero => exact fun _ _ _ _ _ => ⟨∅, rfl, by simp⟩
  | succ m ih =>
    intro k c hc hk hb
    push_cast at hb
    have hgon : ∀ u v : ℝ, u ≤ v → v ≤ b → ContinuousOn g (Icc u v) := fun u v _ hv =>
      hg.mono fun t ht => ht.2.trans hv
    -- first the value `kπ`, then the value `(k − 1)π`
    have hk1 : (k : ℝ) * π ∈ Icc (g b) (g c) := ⟨by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)], hk⟩
    obtain ⟨x₁, hx₁, hgx₁⟩ := intermediate_value_Icc' hc (hgon c b hc le_rfl) hk1
    have hk2 : ((k - 1 : ℤ) : ℝ) * π ∈ Icc (g b) (g x₁) := by
      push_cast
      rw [hgx₁]
      refine ⟨by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)], by nlinarith⟩
    obtain ⟨x₂, hx₂, hgx₂⟩ := intermediate_value_Icc' hx₁.2 (hgon x₁ b hx₁.2 le_rfl) hk2
    have hlt : x₁ < x₂ := by
      refine lt_of_le_of_ne hx₂.1 fun h => ?_
      rw [← h, hgx₁] at hgx₂
      push_cast at hgx₂
      nlinarith
    have hs1 := hsign x₁ hx₁.2 k hgx₁.symm
    have hs2 := hsign x₂ hx₂.2 (k - 1) hgx₂.symm
    have hneg : f x₁ * f x₂ < 0 := by
      have hzpow : (-1 : ℝ) ^ (k - 1) = -(-1 : ℝ) ^ k := by
        rw [zpow_sub₀ (by norm_num), zpow_one]
        ring
      rw [hzpow] at hs2
      have hunit : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
        rw [← mul_zpow]
        simp
      have hmul := mul_pos hs1 hs2
      nlinarith
    have hfon : ContinuousOn f (uIcc x₁ x₂) := by
      rw [uIcc_of_le hlt.le]
      exact hf.mono fun t ht => ht.2.trans hx₂.2
    obtain ⟨y, hy, hfy⟩ : ∃ y ∈ Ioo x₁ x₂, f y = 0 := by
      have hc0 : ContinuousOn f (Icc x₁ x₂) := by rwa [uIcc_of_le hlt.le] at hfon
      rcases lt_or_gt_of_ne (show f x₁ ≠ 0 from fun h => by simp [h] at hneg) with h1 | h1
      · have h2 : 0 < f x₂ := by nlinarith
        have := intermediate_value_Ioo hlt.le hc0 (show (0 : ℝ) ∈ Ioo (f x₁) (f x₂) from ⟨h1, h2⟩)
        obtain ⟨y, hy, hfy⟩ := this
        exact ⟨y, hy, hfy⟩
      · have h2 : f x₂ < 0 := by nlinarith
        have := intermediate_value_Ioo' hlt.le hc0 (show (0 : ℝ) ∈ Ioo (f x₂) (f x₁) from ⟨h2, h1⟩)
        obtain ⟨y, hy, hfy⟩ := this
        exact ⟨y, hy, hfy⟩
    obtain ⟨S, hcard, hS⟩ := ih (k - 1) x₂ hx₂.2 (by rw [hgx₂]) (by push_cast; linarith)
    have hyS : y ∉ S := fun h => by
      have := (hS y h).1
      linarith [hy.2]
    refine ⟨insert y S, by rw [Finset.card_insert_of_notMem hyS, hcard], fun z hz => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨lt_of_le_of_lt hx₁.1 hy.1, hy.2.le.trans hx₂.2, hfy⟩
    · obtain ⟨h1, h2, h3⟩ := hS z hz
      exact ⟨by linarith [hx₁.1, hx₂.1], h2, h3⟩

/-! ## The phase on the saddle -/

variable {d : ℕ} {X : ℝ}

/-- `‖P(τ)‖ ≲ ‖τ‖ log ‖τ‖` for a primitive `P` of the slope, normalized at `1`. -/
theorem norm_primitive_le {P : ℂ → ℂ} (hP1 : P 1 = 0)
    (hP : ∀ z : ℂ, 1 / 2 < z.re → HasDerivAt P (gammaSlope z) z) {τ : ℂ} (hτ : 1 ≤ τ.re) :
    ‖P τ‖ ≤ (Real.log ‖τ‖ / 2 + 12) * (‖τ‖ + 1) := by
  have hτ1 : 1 ≤ ‖τ‖ := hτ.trans (Complex.re_le_norm τ)
  have hconv : Convex ℝ ({z : ℂ | 1 ≤ z.re} ∩ Metric.closedBall (0 : ℂ) ‖τ‖) :=
    (convex_halfSpace_re_ge 1).inter (convex_closedBall _ _)
  have hmem1 : (1 : ℂ) ∈ {z : ℂ | 1 ≤ z.re} ∩ Metric.closedBall (0 : ℂ) ‖τ‖ :=
    ⟨by simp, by simpa using hτ1⟩
  have hmemτ : τ ∈ {z : ℂ | 1 ≤ z.re} ∩ Metric.closedBall (0 : ℂ) ‖τ‖ := ⟨hτ, by simp⟩
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := P) (f' := gammaSlope)
    (C := Real.log ‖τ‖ / 2 + 12)
    (fun z hz => (hP z (by have : (1 : ℝ) ≤ z.re := hz.1; linarith)).hasDerivWithinAt)
    (fun z hz => by
      have hz1 : (1 : ℝ) ≤ z.re := hz.1
      refine (norm_gammaSlope_le hz1).trans ?_
      have hzn : ‖z‖ ≤ ‖τ‖ := by simpa using hz.2
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos (hz1.trans (Complex.re_le_norm z))
      have := Real.log_le_log hzpos hzn
      linarith) hmem1 hmemτ
  rw [hP1, sub_zero] at h
  refine h.trans ?_
  have hl : 0 ≤ Real.log ‖τ‖ := Real.log_nonneg hτ1
  gcongr
  exact (norm_sub_le _ _).trans (by simp)

/-- `arg(x + i a) ≤ Re a/(x − Im a)` for `x > Im a`. -/
theorem arg_le_of_re_pos {w : ℂ} (hre : 0 < w.re) (him : 0 ≤ w.im) : Complex.arg w ≤ w.im / w.re := by
  have h0 : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.2 him
  have hlt : Complex.arg w < π / 2 := (abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))).2
  have ht := Real.le_tan h0 hlt
  have hw : w ≠ 0 := fun h => by
    rw [h, zero_re] at hre
    exact lt_irrefl _ hre
  rwa [Complex.tan_arg] at ht

/-- `R_d(x)` at a phase node has the sign `(−1)^k`. -/
theorem sign_of_phase {R : ℝ} {ε : ℂ} {θ : ℝ} (hR : 0 < R) (hε : ‖ε‖ ≤ 1 / 2) {k : ℤ} (hθ : θ = k * π) :
    0 < (-1 : ℝ) ^ k * (2 * (((R : ℂ) * Complex.exp (θ * I)) * (1 + ε)).re) := by
  have hc : Real.cos θ = (-1 : ℝ) ^ k := by
    rw [hθ, Real.cos_int_mul_pi]
  have hs : Real.sin θ = 0 := by
    rw [hθ, Real.sin_int_mul_pi]
  have hexp : Complex.exp (θ * I) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    simp
  have hre : (((R : ℂ) * Complex.exp (θ * I)) * (1 + ε)).re = R * (-1 : ℝ) ^ k * (1 + ε.re) := by
    rw [hexp, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    simp
  have hεre : -(1 / 2) ≤ ε.re := by
    have := (abs_le.1 ((Complex.abs_re_le_norm ε).trans hε)).1
    linarith
  have hunit : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_zpow]
    simp
  rw [hre]
  have e : (-1 : ℝ) ^ k * (2 * (R * (-1 : ℝ) ^ k * (1 + ε.re))) =
      ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (2 * R * (1 + ε.re)) := by ring
  rw [e, hunit, one_mul]
  have : 0 < 1 + ε.re := by linarith
  positivity

/-- The real polynomial function of `R_d(Ξ)`. -/
theorem eval_xiJensenReal_ofReal (d : ℕ) (x : ℝ) :
    (((xiJensenReal d).eval x : ℝ) : ℂ) = (jensenRev d xiSeries).eval (x : ℂ) := by
  rw [jensenRev_xiSeries]
  have h := Polynomial.eval_map_apply (p := xiJensenReal d) (f := algebraMap ℝ ℂ) x
  simpa using h.symm

theorem eval_xiJensenReal_neg (d : ℕ) (x : ℝ) :
    (xiJensenReal d).eval (-x) = (-1) ^ d * (xiJensenReal d).eval x := by
  have h := eval_xiJensen_half_neg d (x : ℂ)
  rw [xiJensen, mk_xiShiftCoeff_half, ← Complex.ofReal_neg, ← eval_xiJensenReal_ofReal,
    ← eval_xiJensenReal_ofReal] at h
  exact_mod_cast h

/-- **The count on a saddle range.** -/
theorem SaddleRange.exists_real_roots (h : SaddleRange d X) (hX6 : 6 ≤ X) :
    ∃ S : Finset ℝ, (d : ℝ) - (2 / π * ((d / (X - 5)) * (2 * Real.log d)) + 4) ≤ S.card ∧
      ∀ x ∈ S, (xiJensenReal d).eval x = 0 := by
  have hπ := Real.pi_pos
  have hL := h.L_ge
  have hdR := h.d_pos
  obtain ⟨a, ha, hac, ha0⟩ := h.exists_saddle
  obtain ⟨P, hP1, hP, hPexp⟩ := exists_gammaFactor_log
  have habs : ∀ x ∈ Icc 0 X, |x| ≤ X := fun x hx => by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  set τ : ℝ → ℂ := fun x => saddleTau d (a x) x with hτ
  have hτre : ∀ x ∈ Icc 0 X, 400 ≤ (τ x).re := fun x hx => h.re_tau_ge (ha x hx).1 (habs x hx)
  have hsl : ∀ x ∈ Icc 0 X, gammaSlope (τ x) = a x := fun x hx => (ha x hx).2
  have hAge : ∀ x ∈ Icc 0 X, Real.log d / 5 ≤ (a x).re := fun x hx => (ha x hx).1.1
  have hApos : ∀ x ∈ Icc 0 X, 0 < (a x).re := fun x hx => lt_of_lt_of_le (by linarith) (hAge x hx)
  have hτc : ContinuousOn τ (Icc 0 X) := by
    simp only [hτ, saddleTau]
    refine ContinuousOn.div continuousOn_const (hac.sub (by fun_prop)) fun x hx =>
      h.denom_ne (ha x hx).1
  have hG1 : gammaFactor 1 ≠ 0 := gammaFactor_ne_zero (by norm_num) (by norm_num)
  -- the phase
  set w : ℝ → ℂ := fun x => (x : ℂ) + I * a x with hw
  have hwim : ∀ x ∈ Icc 0 X, (w x).im = (a x).re := fun x _ => by simp [hw]
  have hwpos : ∀ x ∈ Icc 0 X, w x ∈ slitPlane := fun x hx =>
    Or.inr (by rw [hwim x hx]; exact (hApos x hx).ne')
  have hwc : ContinuousOn w (Icc 0 X) := by
    simp only [hw]
    exact (by fun_prop : Continuous fun x : ℝ => (x : ℂ)).continuousOn.add (continuousOn_const.mul hac)
  set θ : ℝ → ℝ := fun x => d * Complex.arg (w x) + (P (τ x)).im - (a x * τ x).im + Complex.arg (gammaFactor 1)
    with hθ
  have hθc : ContinuousOn θ (Icc 0 X) := by
    have h1 : ContinuousOn (fun x => Complex.arg (w x)) (Icc 0 X) := fun x hx =>
      (Complex.continuousAt_arg (hwpos x hx)).comp_continuousWithinAt (hwc x hx)
    have h2 : ContinuousOn (fun x => P (τ x)) (Icc 0 X) := fun x hx =>
      ((hP (τ x) (by linarith [hτre x hx])).continuousAt).comp_continuousWithinAt (hτc x hx)
    have h3 : ContinuousOn (fun x => a x * τ x) (Icc 0 X) := hac.mul hτc
    exact (((continuousOn_const.mul h1).add (Complex.continuous_im.comp_continuousOn h2)).sub
      (Complex.continuous_im.comp_continuousOn h3)).add continuousOn_const
  -- extend `θ` and `f` to the half-line `x ≤ X` by freezing at `0`
  set f : ℝ → ℝ := fun x => (xiJensenReal d).eval x with hf
  have hfc : Continuous f := (xiJensenReal d).continuous
  set g : ℝ → ℝ := fun x => θ (max x 0) with hg
  have hgc : ContinuousOn g (Iic X) := by
    refine hθc.comp (by fun_prop : Continuous fun x : ℝ => max x 0).continuousOn fun x hx => ?_
    exact ⟨le_max_right _ _, max_le hx (by linarith)⟩
  -- the identity on the saddle
  have hid : ∀ x ∈ Icc 0 X, ∃ (R : ℝ) (ε : ℂ), 0 < R ∧ ‖ε‖ ≤ 1 / 2 ∧
      f x = 2 * (((R : ℂ) * Complex.exp (θ x * I)) * (1 + ε)).re := by
    intro x hx
    have hax := (ha x hx).1
    have hsad := h.saddle_identity (x := x) hax
    have hτ0 : τ x ≠ 0 := fun h0 => by
      have := hτre x hx
      rw [h0, zero_re] at this
      linarith
    have hne1 : τ x ≠ 1 / 2 := fun h0 => by
      have := hτre x hx
      rw [h0] at this
      norm_num at this
    have hGτ : gammaFactor (τ x) ≠ 0 := gammaFactor_ne_zero (by linarith [hτre x hx]) hne1
    have hid0 := eval_jensenRev_xiSeries_eq_saddle h.hd hτ0 hGτ hsad
    have hslope : gammaSlope (τ x) = a x := hsl x hx
    have hA8 : 8000 ≤ (gammaSlope (τ x)).re := by
      rw [hslope]
      linarith [hAge x hx]
    have hs' : (gammaSlope (τ x) - I * x) * τ x = d := by rw [hslope]; exact hsad
    have hεb := norm_saddleError_le_half h.hd hs' hA8 (hτre x hx)
    rw [hslope] at hεb
    set ε := saddleError d (a x) (τ x) with hε
    -- polar form of `M`
    have hGexp : gammaFactor (τ x) = gammaFactor 1 * Complex.exp (P (τ x)) := by
      rw [hPexp (τ x) (by linarith [hτre x hx])]
      field_simp
    set e := P (τ x) - a x * τ x with he
    have hpow : w x ^ d = ((‖w x‖ ^ d : ℝ) : ℂ) * Complex.exp ((d * Complex.arg (w x) : ℝ) * I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (w x)]
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast
      congr 2
      ring
    have hG1p : gammaFactor 1 = ((‖gammaFactor 1‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (gammaFactor 1) : ℝ) * I) :=
      (Complex.norm_mul_exp_arg_mul_I _).symm
    have hexp : Complex.exp e = ((Real.exp e.re : ℝ) : ℂ) * Complex.exp ((e.im : ℝ) * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      exact (Complex.re_add_im e).symm
    refine ⟨‖w x‖ ^ d * ‖gammaFactor 1‖ * Real.exp e.re, ε, ?_, hεb, ?_⟩
    · have hwn : 0 < ‖w x‖ := norm_pos_iff.2 (slitPlane_ne_zero (hwpos x hx))
      have hGn : 0 < ‖gammaFactor 1‖ := norm_pos_iff.2 hG1
      positivity
    · have hreal : ((f x : ℝ) : ℂ) = _ := (eval_xiJensenReal_ofReal d x).trans hid0
      have hfx := Complex.ofReal_injective hreal
      rw [hfx]
      congr 2
      have hM : ((x : ℂ) + I * a x) ^ d * gammaFactor (τ x) * Complex.exp (-(a x * τ x)) =
          ((‖w x‖ ^ d * ‖gammaFactor 1‖ * Real.exp e.re : ℝ) : ℂ) * Complex.exp (θ x * I) := by
        have hθexp : Complex.exp ((θ x : ℂ) * I) =
            Complex.exp ((d * Complex.arg (w x) : ℝ) * I) * Complex.exp ((e.im : ℝ) * I) *
              Complex.exp ((Complex.arg (gammaFactor 1) : ℝ) * I) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1
          simp only [hθ, he, sub_im]
          push_cast
          ring
        rw [hθexp, show (x : ℂ) + I * a x = w x from rfl, hpow, hGexp]
        have hsplit : Complex.exp (P (τ x)) * Complex.exp (-(a x * τ x)) = Complex.exp e := by
          rw [← Complex.exp_add, he]
          congr 1
          ring
        calc _ = ((‖w x‖ ^ d : ℝ) : ℂ) * Complex.exp ((d * Complex.arg (w x) : ℝ) * I) * gammaFactor 1 *
              (Complex.exp (P (τ x)) * Complex.exp (-(a x * τ x))) := by ring
          _ = _ := by
              rw [hsplit, hexp]
              conv_lhs => rw [hG1p]
              push_cast
              ring
      rw [hM]
  have hsign : ∀ x ≤ X, ∀ k : ℤ, g x = k * π → 0 < (-1 : ℝ) ^ k * f (max x 0) := by
    intro x hx k hk
    have hm : max x 0 ∈ Icc 0 X := ⟨le_max_right _ _, max_le hx (by linarith)⟩
    obtain ⟨R, ε, hR, hε, hfx⟩ := hid _ hm
    rw [hfx]
    exact sign_of_phase hR hε hk
  -- the values of the phase at the two ends
  have h0mem : (0 : ℝ) ∈ Icc 0 X := ⟨le_rfl, by linarith⟩
  have hXmem : X ∈ Icc 0 X := ⟨by linarith, le_rfl⟩
  have ha0real : a 0 = (((a 0).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [ha0])
  have hτ0real : (τ 0).im = 0 := by
    simp only [hτ, saddleTau]
    rw [ha0real]
    simp only [ofReal_zero, mul_zero, sub_zero]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_im]
  have hPreal : ∀ t : ℝ, 1 / 2 < t → (P (t : ℂ)).im = 0 := by
    -- the slope is real on the real axis, so `Im P` is constant there
    have hconj : ∀ t : ℝ, 1 / 2 < t → (gammaSlope (t : ℂ)).im = 0 := fun t _ => by
      have h1 := gammaSlope_conj (t : ℂ)
      rw [Complex.conj_ofReal] at h1
      exact Complex.conj_eq_iff_im.1 h1.symm
    have hder : ∀ t ∈ Ioi (1 / 2 : ℝ), HasDerivAt (fun u : ℝ => (P (u : ℂ)).im) 0 t := fun t ht => by
      have h1 : HasDerivAt (fun u : ℝ => P (u : ℂ)) (gammaSlope (t : ℂ)) t := by
        have h2 := (hP (t : ℂ) (by simpa using ht)).comp_ofReal
        simpa using h2
      have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h1
      simpa [hconj t ht] using h2
    intro t ht
    have hconst := (convex_Ioi (1 / 2 : ℝ)).is_const_of_fderivWithin_eq_zero
      (𝕜 := ℝ) (f := fun u : ℝ => (P (u : ℂ)).im)
      (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => by
        have := (hder u hu).hasFDerivAt.hasFDerivWithinAt.fderivWithin
          ((isOpen_Ioi.uniqueDiffOn) u hu)
        rw [this]
        ext
        simp) ht (show (1 : ℝ) ∈ Ioi (1 / 2 : ℝ) by norm_num)
    simp only at hconst
    rw [hconst]
    simp [hP1]
  have hτ0eq : τ 0 = (((τ 0).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hτ0real])
  have hθ0 : θ 0 = d * (π / 2) + Complex.arg (gammaFactor 1) := by
    have h1 : w 0 = I * (((a 0).re : ℝ) : ℂ) := by
      simp only [hw]
      rw [← ha0real]
      simp
    have harg : Complex.arg (w 0) = π / 2 := by
      rw [h1, mul_comm]
      exact Complex.arg_real_mul I (hApos 0 h0mem) ▸ Complex.arg_I
    have h2 : (P (τ 0)).im = 0 := by
      rw [hτ0eq]
      exact hPreal _ (by linarith [hτre 0 h0mem])
    have h3 : (a 0 * τ 0).im = 0 := by
      rw [ha0real, hτ0eq, ← Complex.ofReal_mul, Complex.ofReal_im]
    simp only [hθ, harg, h2, h3]
    ring
  set T := (d : ℝ) / (X - 5) with hT
  have hXpos : 0 < X - 5 := by linarith
  have hTpos : 0 < T := by positivity
  have hdenX := h.denom_ne (x := X) (ha X hXmem).1
  have hax := (ha X hXmem).1
  have haim := abs_le.1 hax.2.2
  have hdenim : X - 5 ≤ ‖a X - I * X‖ := by
    have h1 := Complex.abs_im_le_norm (a X - I * X)
    have h2 : (a X - I * X).im = (a X).im - X := by simp
    rw [h2] at h1
    have h3 := neg_abs_le ((a X).im - X)
    linarith [neg_le_abs ((a X).im - X)]
  have hρle : ‖τ X‖ ≤ T := by
    have h1 := h.norm_tau (x := X) hax
    rw [hT, le_div_iff₀ hXpos]
    calc ‖τ X‖ * (X - 5) ≤ ‖τ X‖ * ‖a X - I * X‖ := by gcongr
      _ = d := h1
  have hρ400 : 400 ≤ ‖τ X‖ := (hτre X hXmem).trans (Complex.re_le_norm _)
  have hT1 : 1 ≤ T := by linarith
  have hlogT : Real.log ‖τ X‖ ≤ Real.log d := by
    refine Real.log_le_log (by linarith) (hρle.trans ?_)
    rw [hT]
    exact div_le_self hdR.le (by linarith)
  -- the three bounds at `x = X`
  have hbarg : d * Complex.arg (w X) ≤ T * (Real.log d / 2) := by
    have hre : (w X).re = X - (a X).im := by simp [hw]
    have hrepos : X - 5 ≤ (w X).re := by rw [hre]; linarith [haim.2]
    have him : (w X).im = (a X).re := hwim X hXmem
    have harg := arg_le_of_re_pos (by linarith) (by rw [him]; exact (hApos X hXmem).le)
    rw [him] at harg
    have hle2 : (a X).re / (w X).re ≤ (Real.log d / 2) / (X - 5) := by
      apply div_le_div₀ (by linarith) hax.2.1 hXpos hrepos
    calc (d : ℝ) * Complex.arg (w X) ≤ d * ((Real.log d / 2) / (X - 5)) := by
          gcongr
          exact harg.trans hle2
      _ = _ := by rw [hT]; ring
  have hbP : |(P (τ X)).im| ≤ (Real.log d / 2 + 12) * (T + 1) := by
    refine (Complex.abs_im_le_norm _).trans ((norm_primitive_le hP1 hP (by linarith [hτre X hXmem])).trans ?_)
    gcongr
  have hbaτ : |(a X * τ X).im| ≤ (Real.log d / 2 + 5) * T := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul]
    have hna : ‖a X‖ ≤ Real.log d / 2 + 5 := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (a X)
      rw [abs_of_pos (hApos X hXmem)] at h1
      linarith [hax.2.1, hax.2.2]
    gcongr
  set Bd := (T * (Real.log d / 2)) + (Real.log d / 2 + 12) * (T + 1) + (Real.log d / 2 + 5) * T with hBd
  have hdrop : θ X ≤ θ 0 - d * (π / 2) + Bd := by
    rw [hθ0]
    simp only [hθ]
    have h1 := le_abs_self (P (τ X)).im
    have h2 := neg_le_abs (a X * τ X).im
    rw [hBd]
    linarith
  -- the sign changes on `(0, X]`
  set k₀ : ℤ := ⌊θ 0 / π⌋ with hk₀
  have hk₀le : (k₀ : ℝ) * π ≤ θ 0 := by
    have := Int.floor_le (θ 0 / π)
    rwa [le_div_iff₀ hπ] at this
  have hk₀gt : θ 0 - π < (k₀ : ℝ) * π := by
    have := Int.lt_floor_add_one (θ 0 / π)
    rw [div_lt_iff₀ hπ] at this
    linarith
  set m : ℕ := ⌊(d * (π / 2) - Bd) / π - 1⌋₊ with hm
  have hgX : g X = θ X := by simp only [hg, max_eq_left (show 0 ≤ X by linarith)]
  have hg0 : g 0 = θ 0 := by simp only [hg, max_self]
  have hBdbig : ∀ hbig : 0 ≤ (d * (π / 2) - Bd) / π - 1, (m : ℝ) * π ≤ d * (π / 2) - Bd - π := by
    intro hbig
    have := Nat.floor_le hbig
    rw [← hm, le_sub_iff_add_le, le_div_iff₀ hπ] at this
    nlinarith
  by_cases hbig : 0 ≤ (d * (π / 2) - Bd) / π - 1
  · have hk : g X ≤ ((k₀ : ℝ) - (m : ℝ)) * π := by
      rw [hgX]
      have := hBdbig hbig
      nlinarith
    obtain ⟨S, hScard, hS⟩ := exists_zeros_of_phase (f := fun x => f (max x 0)) (g := g) (b := X)
      ((hfc.comp (by fun_prop)).continuousOn) hgc (fun x hx k hk => hsign x hx k hk) m k₀ 0
      (by linarith) (by rw [hg0]; exact hk₀le) hk
    -- positive zeros and their reflections
    have hpos : ∀ y ∈ S, 0 < y ∧ f y = 0 := fun y hy => by
      obtain ⟨h1, -, h3⟩ := hS y hy
      refine ⟨h1, ?_⟩
      simpa [max_eq_left h1.le] using h3
    classical
    set S' := S.image (fun y : ℝ => -y) with hS'
    have hdisj : Disjoint S S' := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy'
      have h1 := (hpos _ hy).1
      have h2 := (hpos z hz).1
      linarith
    have hcard : (S ∪ S').card = 2 * m := by
      rw [Finset.card_union_of_disjoint hdisj, hS',
        Finset.card_image_of_injective _ neg_injective, hScard]
      ring
    refine ⟨S ∪ S', ?_, fun x hx => ?_⟩
    · rw [hcard]
      push_cast
      have hmfl : (d * (π / 2) - Bd) / π - 1 < m + 1 := by
        have := Nat.lt_floor_add_one ((d * (π / 2) - Bd) / π - 1)
        simpa [hm] using this
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hπ] at hmfl
      have hb2 : Bd ≤ (T * (2 * Real.log d)) := by
        rw [hBd]
        nlinarith
      have hmono : 2 / π * Bd ≤ 2 / π * (T * (2 * Real.log d)) := by gcongr
      have hrew : (d : ℝ) - 2 / π * Bd - 4 < 2 * (m : ℝ) := by
        have e : (d : ℝ) - 2 / π * Bd = 2 / π * (d * (π / 2) - Bd) := by
          field_simp
        rw [e]
        have h5 : 2 / π * (d * (π / 2) - Bd) < 2 / π * (((m : ℝ) + 1 + 1) * π) := by
          gcongr
        have h6 : 2 / π * (((m : ℝ) + 1 + 1) * π) = 2 * m + 4 := by
          field_simp
          ring
        linarith
      linarith
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact (hpos x hx).2
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
        rw [eval_xiJensenReal_neg, show (xiJensenReal d).eval z = f z from rfl, (hpos z hz).2, mul_zero]
  · refine ⟨∅, ?_, by simp⟩
    push Not at hbig
    rw [sub_lt_zero, div_lt_one hπ] at hbig
    simp only [Finset.card_empty, Nat.cast_zero]
    have hb2 : Bd ≤ (T * (2 * Real.log d)) := by
      rw [hBd]
      nlinarith
    have hmono : 2 / π * Bd ≤ 2 / π * (T * (2 * Real.log d)) := by gcongr
    have e : (d : ℝ) - 2 / π * Bd = 2 / π * (d * (π / 2) - Bd) := by
      field_simp
    have h5 : 2 / π * (d * (π / 2) - Bd) < 2 / π * π := by gcongr
    have h6 : 2 / π * π = 2 := by field_simp
    rw [hT] at hmono
    linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.SaddleRange.exists_real_roots
