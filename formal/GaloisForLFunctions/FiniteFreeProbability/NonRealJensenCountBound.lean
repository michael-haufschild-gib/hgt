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
theorem exists_zeros_of_phase {f g : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hsign : ∀ x ∈ Icc a b, ∀ k : ℤ, g x = k * π → 0 < (-1 : ℝ) ^ k * f x) :
    ∀ (m : ℕ) (k : ℤ) (c : ℝ), c ∈ Icc a b → k * π ≤ g c → g b ≤ (k - m) * π →
      ∃ S : Finset ℝ, S.card = m ∧ ∀ y ∈ S, c < y ∧ y ≤ b ∧ f y = 0 := by
  have hπ := Real.pi_pos
  intro m
  induction m with
  | zero => exact fun _ _ _ _ _ => ⟨∅, rfl, by simp⟩
  | succ m ih =>
    intro k c hc hk hb
    push_cast at hb
    have hsub : ∀ u v : ℝ, a ≤ u → v ≤ b → Icc u v ⊆ Icc a b := fun u v hu hv t ht =>
      ⟨hu.trans ht.1, ht.2.trans hv⟩
    have hmnn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    -- first the value `kπ`, then the value `(k − 1)π`
    have hk1 : (k : ℝ) * π ∈ Icc (g b) (g c) := ⟨by nlinarith, hk⟩
    obtain ⟨x₁, hx₁, hgx₁⟩ := intermediate_value_Icc' hc.2 (hg.mono (hsub c b hc.1 le_rfl)) hk1
    have hk2 : ((k - 1 : ℤ) : ℝ) * π ∈ Icc (g b) (g x₁) := by
      push_cast
      rw [hgx₁]
      exact ⟨by nlinarith, by nlinarith⟩
    have hx₁a : a ≤ x₁ := hc.1.trans hx₁.1
    obtain ⟨x₂, hx₂, hgx₂⟩ := intermediate_value_Icc' hx₁.2 (hg.mono (hsub x₁ b hx₁a le_rfl)) hk2
    have hlt : x₁ < x₂ := by
      refine lt_of_le_of_ne hx₂.1 fun h => ?_
      rw [← h, hgx₁] at hgx₂
      push_cast at hgx₂
      nlinarith
    have hx₁m : x₁ ∈ Icc a b := ⟨hx₁a, hx₁.2⟩
    have hx₂m : x₂ ∈ Icc a b := ⟨hx₁a.trans hx₂.1, hx₂.2⟩
    have hs1 := hsign x₁ hx₁m k hgx₁
    have hs2 := hsign x₂ hx₂m (k - 1) hgx₂
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
    have hc0 : ContinuousOn f (Icc x₁ x₂) := hf.mono (hsub x₁ x₂ hx₁a hx₂.2)
    obtain ⟨y, hy, hfy⟩ : ∃ y ∈ Ioo x₁ x₂, f y = 0 := by
      rcases lt_or_gt_of_ne (show f x₁ ≠ 0 from fun h => by simp [h] at hneg) with h1 | h1
      · have h2 : 0 < f x₂ := by nlinarith
        obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioo hlt.le hc0
          (show (0 : ℝ) ∈ Ioo (f x₁) (f x₂) from ⟨h1, h2⟩)
        exact ⟨y, hy, hfy⟩
      · have h2 : f x₂ < 0 := by nlinarith
        obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioo' hlt.le hc0
          (show (0 : ℝ) ∈ Ioo (f x₂) (f x₁) from ⟨h2, h1⟩)
        exact ⟨y, hy, hfy⟩
    obtain ⟨S, hcard, hS⟩ := ih (k - 1) x₂ hx₂m (by rw [hgx₂]) (by push_cast; linarith)
    have hyS : y ∉ S := fun h => by
      have := (hS y h).1
      linarith [hy.2]
    refine ⟨insert y S, by rw [Finset.card_insert_of_notMem hyS, hcard], fun z hz => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨lt_of_le_of_lt hx₁.1 hy.1, hy.2.le.trans hx₂.2, hfy⟩
    · obtain ⟨h1, h2, h3⟩ := hS z hz
      exact ⟨by linarith [hx₁.1, hx₂.1], h2, h3⟩

/-- A drop of the phase by `D` on `[0, X]` gives `(2/π) D − 4` real zeros of a function whose zero set is symmetric. -/
theorem exists_real_zeros_of_phase_drop {f g : ℝ → ℝ} {X D : ℝ} (hX : 0 ≤ X) (hfc : Continuous f)
    (hpar : ∀ x, f x = 0 → f (-x) = 0) (hg : ContinuousOn g (Icc 0 X))
    (hsign : ∀ x ∈ Icc 0 X, ∀ k : ℤ, g x = k * π → 0 < (-1 : ℝ) ^ k * f x) (hdrop : g X ≤ g 0 - D) :
    ∃ S : Finset ℝ, 2 / π * D - 4 ≤ S.card ∧ ∀ x ∈ S, f x = 0 := by
  have hπ := Real.pi_pos
  have e2 : 2 / π * D = 2 * (D / π) := by ring
  by_cases hbig : 0 ≤ D / π - 1
  · set m : ℕ := ⌊D / π - 1⌋₊ with hm
    set k₀ : ℤ := ⌊g 0 / π⌋ with hk₀
    have hk₀le : (k₀ : ℝ) * π ≤ g 0 := by
      have := Int.floor_le (g 0 / π)
      rwa [le_div_iff₀ hπ] at this
    have hk₀gt : g 0 - π < (k₀ : ℝ) * π := by
      have := Int.lt_floor_add_one (g 0 / π)
      rw [div_lt_iff₀ hπ] at this
      linarith
    have hm1 : ((m : ℝ) + 1) * π ≤ D := by
      have h1 : (m : ℝ) ≤ D / π - 1 := Nat.floor_le hbig
      exact (le_div_iff₀ hπ).1 (by linarith)
    have hk : g X ≤ ((k₀ : ℝ) - (m : ℝ)) * π := by
      have e : ((k₀ : ℝ) - (m : ℝ)) * π = k₀ * π - m * π := by ring
      have e' : ((m : ℝ) + 1) * π = m * π + π := by ring
      rw [e]
      linarith
    obtain ⟨S, hScard, hS⟩ := exists_zeros_of_phase hfc.continuousOn hg hsign m k₀ 0 ⟨le_rfl, hX⟩ hk₀le hk
    classical
    set S' := S.image (fun y : ℝ => -y) with hS'
    have hdisj : Disjoint S S' := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy'
      have h1 := (hS _ hy).1
      have h2 := (hS z hz).1
      linarith
    have hcard : (S ∪ S').card = 2 * m := by
      rw [Finset.card_union_of_disjoint hdisj, hS', Finset.card_image_of_injective _ neg_injective, hScard]
      ring
    refine ⟨S ∪ S', ?_, fun x hx => ?_⟩
    · rw [hcard, e2]
      push_cast
      have hmfl : D / π - 1 < m + 1 := Nat.lt_floor_add_one _
      linarith
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact (hS x hx).2.2
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
        exact hpar z (hS z hz).2.2
  · push Not at hbig
    refine ⟨∅, ?_, by simp⟩
    rw [e2]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

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

/-- Polar form of the main term. -/
theorem polar_form_saddle (w G p q : ℂ) (d : ℕ) :
    w ^ d * (G * Complex.exp p) * Complex.exp (-q) =
      ((‖w‖ ^ d * ‖G‖ * Real.exp (p - q).re : ℝ) : ℂ) *
        Complex.exp (((d * Complex.arg w + p.im - q.im + Complex.arg G : ℝ) : ℂ) * I) := by
  have h1 : ((‖w‖ ^ d : ℝ) : ℂ) * Complex.exp (((d * Complex.arg w : ℝ) : ℂ) * I) = w ^ d := by
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    congr 2
    ring
  have h3 : ((Real.exp (p - q).re : ℝ) : ℂ) * Complex.exp (((p - q).im : ℂ) * I) =
      Complex.exp p * Complex.exp (-q) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, Complex.re_add_im, sub_eq_add_neg]
  have h4 : Complex.exp (((d * Complex.arg w + p.im - q.im + Complex.arg G : ℝ) : ℂ) * I) =
      Complex.exp (((d * Complex.arg w : ℝ) : ℂ) * I) * Complex.exp (((p - q).im : ℂ) * I) *
        Complex.exp ((Complex.arg G : ℂ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [sub_im]
    push_cast
    ring
  rw [h4, Complex.ofReal_mul, Complex.ofReal_mul]
  have e : ((‖w‖ ^ d : ℝ) : ℂ) * ((‖G‖ : ℝ) : ℂ) * ((Real.exp (p - q).re : ℝ) : ℂ) *
      (Complex.exp (((d * Complex.arg w : ℝ) : ℂ) * I) * Complex.exp (((p - q).im : ℂ) * I) *
        Complex.exp ((Complex.arg G : ℂ) * I)) =
      (((‖w‖ ^ d : ℝ) : ℂ) * Complex.exp (((d * Complex.arg w : ℝ) : ℂ) * I)) *
        (((‖G‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg G : ℂ) * I)) *
        (((Real.exp (p - q).re : ℝ) : ℂ) * Complex.exp (((p - q).im : ℂ) * I)) := by ring
  rw [e, h1, h3, Complex.norm_mul_exp_arg_mul_I]
  ring

/-- The phase of the main term along the saddle. -/
def saddlePhase (d : ℕ) (P : ℂ → ℂ) (a : ℂ) (x : ℝ) : ℝ :=
  d * Complex.arg ((x : ℂ) + I * a) + (P (saddleTau d a x)).im - (a * saddleTau d a x).im +
    Complex.arg (gammaFactor 1)

/-- `R_d(x) = 2 Re[R e^{iθ}(1 + ε)]` at a saddle point, with `R > 0`, `‖ε‖ ≤ 1/2`. -/
theorem SaddleRange.eval_eq_polar (h : SaddleRange d X) {x : ℝ} (hx : |x| ≤ X) {a : ℂ}
    (ha : a ∈ saddleRect (Real.log d)) (hfix : gammaSlope (saddleTau d a x) = a) {P : ℂ → ℂ}
    (hPexp : ∀ z : ℂ, 1 / 2 < z.re → Complex.exp (P z) = gammaFactor z / gammaFactor 1) :
    ∃ (R : ℝ) (ε : ℂ), 0 < R ∧ ‖ε‖ ≤ 1 / 2 ∧
      (xiJensenReal d).eval x = 2 * (((R : ℂ) * Complex.exp (saddlePhase d P a x * I)) * (1 + ε)).re := by
  have hre := h.re_tau_ge ha hx
  have hsad := h.saddle_identity (x := x) ha
  set τ := saddleTau d a x with hτ
  have hL := h.L_ge
  have hτ0 : τ ≠ 0 := fun h0 => by
    rw [h0, zero_re] at hre
    linarith
  have hne1 : τ ≠ 1 / 2 := fun h0 => by
    rw [h0] at hre
    norm_num at hre
  have hGτ : gammaFactor τ ≠ 0 := gammaFactor_ne_zero (by linarith) hne1
  have hG1 : gammaFactor 1 ≠ 0 := gammaFactor_ne_zero (by norm_num) (by norm_num)
  have hid0 := eval_jensenRev_xiSeries_eq_saddle h.hd hτ0 hGτ hsad
  have hA8 : 8000 ≤ (gammaSlope τ).re := by
    rw [hfix]
    linarith [ha.1]
  have hs' : (gammaSlope τ - I * x) * τ = d := by rw [hfix]; exact hsad
  have hεb := norm_saddleError_le_half h.hd hs' hA8 hre
  rw [hfix] at hεb
  have hGexp : gammaFactor τ = gammaFactor 1 * Complex.exp (P τ) := by
    rw [hPexp τ (by linarith)]
    field_simp
  have hwne : (x : ℂ) + I * a ≠ 0 := fun h0 => by
    have h1 := congrArg Complex.im h0
    simp only [add_im, ofReal_im, mul_im, I_re, zero_mul, I_im, one_mul, zero_add, zero_im] at h1
    linarith [ha.1]
  refine ⟨‖(x : ℂ) + I * a‖ ^ d * ‖gammaFactor 1‖ * Real.exp (P τ - a * τ).re, saddleError d a τ, ?_, hεb, ?_⟩
  · have h1 : 0 < ‖(x : ℂ) + I * a‖ := norm_pos_iff.2 hwne
    have h2 : 0 < ‖gammaFactor 1‖ := norm_pos_iff.2 hG1
    positivity
  · have hreal := (eval_xiJensenReal_ofReal d x).trans hid0
    rw [Complex.ofReal_injective hreal, hGexp, polar_form_saddle]
    rfl

/-- The slope is real on the real axis, so a primitive normalized at `1` is real there. -/
theorem im_primitive_ofReal {P : ℂ → ℂ} (hP1 : P 1 = 0)
    (hP : ∀ z : ℂ, 1 / 2 < z.re → HasDerivAt P (gammaSlope z) z) {t : ℝ} (ht : 1 / 2 < t) :
    (P (t : ℂ)).im = 0 := by
  have hconj : ∀ u : ℝ, (gammaSlope (u : ℂ)).im = 0 := fun u => by
    have h1 := gammaSlope_conj (u : ℂ)
    rw [Complex.conj_ofReal] at h1
    exact Complex.conj_eq_iff_im.1 h1.symm
  have hder : ∀ u ∈ Ioi (1 / 2 : ℝ), HasDerivAt (fun v : ℝ => (P (v : ℂ)).im) 0 u := fun u hu => by
    have h1 : HasDerivAt (fun v : ℝ => P (v : ℂ)) (gammaSlope (u : ℂ)) u := by
      have h2 := (hP (u : ℂ) (by simpa using hu)).comp_ofReal
      simpa using h2
    have h3 : HasDerivAt (fun v : ℝ => (P (v : ℂ)).im) (gammaSlope (u : ℂ)).im u :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt u h1
    rwa [hconj u] at h3
  have hconst : (P (t : ℂ)).im = (P ((1 : ℝ) : ℂ)).im :=
    (convex_Ioi (1 / 2 : ℝ)).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
      (f := fun v : ℝ => (P (v : ℂ)).im)
      (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => by
        have h1 := (hder u hu).hasFDerivAt.hasFDerivWithinAt.fderivWithin
          ((isOpen_Ioi.uniqueDiffOn) u hu)
        rw [h1]
        ext
        simp) ht (show (1 : ℝ) ∈ Ioi (1 / 2 : ℝ) by norm_num)
  rw [hconst]
  simp [hP1]

/-- At `x = 0` the saddle is real and the phase is `dπ/2 + arg G(1)`. -/
theorem SaddleRange.saddlePhase_zero (h : SaddleRange d X) {a : ℂ} (ha : a ∈ saddleRect (Real.log d))
    (him : a.im = 0) {P : ℂ → ℂ} (hP1 : P 1 = 0)
    (hP : ∀ z : ℂ, 1 / 2 < z.re → HasDerivAt P (gammaSlope z) z) :
    saddlePhase d P a 0 = d * (π / 2) + Complex.arg (gammaFactor 1) := by
  have hA : 0 < a.re := lt_of_lt_of_le (by linarith [h.L_ge]) ha.1
  have hareal : a = ((a.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hre := h.re_tau_ge ha (x := 0) (by simpa using h.hX)
  have hτ : saddleTau d a 0 = (((d : ℝ) / a.re : ℝ) : ℂ) := by
    rw [saddleTau, hareal]
    simp
  have hτre : (1 : ℝ) / 2 < (d : ℝ) / a.re := by
    rw [hτ, Complex.ofReal_re] at hre
    linarith
  have harg : Complex.arg (((0 : ℝ) : ℂ) + I * a) = π / 2 := by
    rw [hareal, Complex.ofReal_zero, zero_add, mul_comm, Complex.arg_real_mul _ hA, Complex.arg_I]
  have hP0 : (P (saddleTau d a 0)).im = 0 := by
    rw [hτ]
    exact im_primitive_ofReal hP1 hP hτre
  have haτ : (a * saddleTau d a 0).im = 0 := by
    rw [hτ, hareal, ← Complex.ofReal_mul, Complex.ofReal_im]
  simp only [saddlePhase, harg, hP0, haτ]
  ring

/-- At the end of the range the phase has dropped: with `T = d/(X − 5)`, what remains is `≤ 2 T log d`. -/
theorem SaddleRange.saddlePhase_end_le (h : SaddleRange d X) (hX6 : 6 ≤ X) {a : ℂ}
    (ha : a ∈ saddleRect (Real.log d)) {P : ℂ → ℂ} (hP1 : P 1 = 0)
    (hP : ∀ z : ℂ, 1 / 2 < z.re → HasDerivAt P (gammaSlope z) z) :
    saddlePhase d P a X ≤ Complex.arg (gammaFactor 1) + (d : ℝ) / (X - 5) * (2 * Real.log d) := by
  have hL := h.L_ge
  have hdR := h.d_pos
  have hXabs : |X| ≤ X := by rw [abs_of_nonneg h.hX]
  have hre := h.re_tau_ge ha hXabs
  set τ := saddleTau d a X with hτ
  set L := Real.log (d : ℝ) with hLdef
  set T := (d : ℝ) / (X - 5) with hT
  have hXpos : 0 < X - 5 := by linarith
  have haim := abs_le.1 ha.2.2
  have hApos : 0 < a.re := lt_of_lt_of_le (by linarith) ha.1
  -- `‖τ‖ ≤ T`
  have hden : X - 5 ≤ ‖a - I * X‖ := by
    have h1 := Complex.abs_im_le_norm (a - I * X)
    have h2 : (a - I * X).im = a.im - X := by simp
    rw [h2] at h1
    linarith [neg_le_abs (a.im - X)]
  have hρT : ‖τ‖ ≤ T := by
    have h1 := h.norm_tau (x := X) ha
    rw [hT, le_div_iff₀ hXpos]
    calc ‖τ‖ * (X - 5) ≤ ‖τ‖ * ‖a - I * X‖ := by gcongr
      _ = d := h1
  have hρ400 : 400 ≤ ‖τ‖ := hre.trans (Complex.re_le_norm _)
  have hT400 : 400 ≤ T := hρ400.trans hρT
  have hlogρ : Real.log ‖τ‖ ≤ L := by
    refine Real.log_le_log (by linarith) (hρT.trans ?_)
    rw [hT]
    exact div_le_self hdR.le (by linarith)
  -- the argument of `X + ia`
  have hbarg : d * Complex.arg ((X : ℂ) + I * a) ≤ T * (L / 2) := by
    have hwre : ((X : ℂ) + I * a).re = X - a.im := by simp [sub_eq_add_neg]
    have hwim : ((X : ℂ) + I * a).im = a.re := by simp
    have hrepos : X - 5 ≤ ((X : ℂ) + I * a).re := by rw [hwre]; linarith [haim.2]
    have harg := arg_le_of_re_pos (w := (X : ℂ) + I * a) (by linarith) (by rw [hwim]; exact hApos.le)
    rw [hwim] at harg
    have hle2 : a.re / ((X : ℂ) + I * a).re ≤ (L / 2) / (X - 5) :=
      div_le_div₀ (by linarith) ha.2.1 hXpos hrepos
    calc (d : ℝ) * Complex.arg ((X : ℂ) + I * a) ≤ d * ((L / 2) / (X - 5)) := by
          gcongr
          exact harg.trans hle2
      _ = _ := by rw [hT]; ring
  -- the primitive and the product
  have hbP : (P τ).im ≤ (L / 2 + 12) * (T + 1) := by
    refine (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans
      ((norm_primitive_le hP1 hP (by linarith)).trans ?_))
    have h1 : Real.log ‖τ‖ / 2 + 12 ≤ L / 2 + 12 := by linarith
    have h2 : ‖τ‖ + 1 ≤ T + 1 := by linarith
    have h3 : 0 ≤ Real.log ‖τ‖ / 2 + 12 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ ‖τ‖)
      linarith
    exact mul_le_mul h1 h2 (by linarith) (by linarith)
  have hbaτ : -(a * τ).im ≤ (L / 2 + 5) * T := by
    refine (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans ?_)
    rw [norm_mul]
    have hna : ‖a‖ ≤ L / 2 + 5 := by
      have h1 := Complex.norm_le_abs_re_add_abs_im a
      rw [abs_of_pos hApos] at h1
      linarith [ha.2.1, ha.2.2]
    exact mul_le_mul hna hρT (norm_nonneg _) (by linarith)
  -- collect: `(3/2) T L + L/2 + 17 T + 12 ≤ 2 T L`
  have hsum : T * (L / 2) + (L / 2 + 12) * (T + 1) + (L / 2 + 5) * T ≤ T * (2 * L) := by
    have h1 : L / 2 ≤ T * L / 800 := by nlinarith
    have h2 : 17 * T ≤ T * L / 2000 := by nlinarith
    have h3 : 12 ≤ T * L / 2000 := by nlinarith
    nlinarith
  simp only [saddlePhase, ← hτ, ← hLdef]
  linarith

/-- The phase is continuous along a continuous saddle. -/
theorem SaddleRange.continuousOn_saddlePhase (h : SaddleRange d X) {a : ℝ → ℂ}
    (ha : ∀ x ∈ Icc 0 X, a x ∈ saddleRect (Real.log d)) (hac : ContinuousOn a (Icc 0 X)) {P : ℂ → ℂ}
    (hP : ∀ z : ℂ, 1 / 2 < z.re → HasDerivAt P (gammaSlope z) z) :
    ContinuousOn (fun x => saddlePhase d P (a x) x) (Icc 0 X) := by
  have hL := h.L_ge
  have habs : ∀ x ∈ Icc 0 X, |x| ≤ X := fun x hx => by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have hτc : ContinuousOn (fun x : ℝ => saddleTau d (a x) x) (Icc 0 X) := by
    simp only [saddleTau]
    exact ContinuousOn.div continuousOn_const (hac.sub (by fun_prop)) fun x hx => h.denom_ne (ha x hx)
  have hwc : ContinuousOn (fun x : ℝ => (x : ℂ) + I * a x) (Icc 0 X) :=
    (by fun_prop : Continuous fun x : ℝ => (x : ℂ)).continuousOn.add (continuousOn_const.mul hac)
  have h1 : ContinuousOn (fun x : ℝ => Complex.arg ((x : ℂ) + I * a x)) (Icc 0 X) := fun x hx => by
    have hne : (x : ℂ) + I * a x ∈ slitPlane := Or.inr (by
      have him : ((x : ℂ) + I * a x).im = (a x).re := by simp
      rw [him]
      exact (lt_of_lt_of_le (by linarith) (ha x hx).1).ne')
    exact (Complex.continuousAt_arg hne).comp_continuousWithinAt (hwc x hx)
  have h2 : ContinuousOn (fun x : ℝ => P (saddleTau d (a x) x)) (Icc 0 X) := fun x hx =>
    ((hP _ (by linarith [h.re_tau_ge (ha x hx) (habs x hx)])).continuousAt).comp_continuousWithinAt (hτc x hx)
  have h3 : ContinuousOn (fun x : ℝ => a x * saddleTau d (a x) x) (Icc 0 X) := hac.mul hτc
  exact (((continuousOn_const.mul h1).add (Complex.continuous_im.comp_continuousOn h2)).sub
    (Complex.continuous_im.comp_continuousOn h3)).add continuousOn_const

/-- **The count on a saddle range.** -/
theorem SaddleRange.exists_real_roots (h : SaddleRange d X) (hX6 : 6 ≤ X) :
    ∃ S : Finset ℝ, (d : ℝ) - (2 / π * ((d / (X - 5)) * (2 * Real.log d)) + 4) ≤ S.card ∧
      ∀ x ∈ S, (xiJensenReal d).eval x = 0 := by
  have hπ := Real.pi_pos
  obtain ⟨a, ha, hac, ha0⟩ := h.exists_saddle
  obtain ⟨P, hP1, hP, hPexp⟩ := exists_gammaFactor_log
  have habs : ∀ x ∈ Icc 0 X, |x| ≤ X := fun x hx => by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have h0mem : (0 : ℝ) ∈ Icc 0 X := ⟨le_rfl, h.hX⟩
  have hXmem : X ∈ Icc 0 X := ⟨h.hX, le_rfl⟩
  set B := (d : ℝ) / (X - 5) * (2 * Real.log d) with hB
  have hdrop : saddlePhase d P (a X) X ≤ saddlePhase d P (a 0) 0 - ((d : ℝ) * (π / 2) - B) := by
    rw [h.saddlePhase_zero (ha 0 h0mem).1 ha0 hP1 hP]
    have := h.saddlePhase_end_le hX6 (ha X hXmem).1 hP1 hP
    linarith
  have hsign : ∀ x ∈ Icc 0 X, ∀ k : ℤ, saddlePhase d P (a x) x = k * π →
      0 < (-1 : ℝ) ^ k * (xiJensenReal d).eval x := fun x hx k hk => by
    obtain ⟨R, ε, hR, hε, hfx⟩ := h.eval_eq_polar (habs x hx) (ha x hx).1 (ha x hx).2 hPexp
    rw [hfx]
    exact sign_of_phase hR hε hk
  obtain ⟨S, hS, hroots⟩ := exists_real_zeros_of_phase_drop (f := fun x => (xiJensenReal d).eval x)
    (g := fun x => saddlePhase d P (a x) x) h.hX (xiJensenReal d).continuous
    (fun x hx => by
      simp only at hx ⊢
      rw [eval_xiJensenReal_neg, hx, mul_zero])
    (h.continuousOn_saddlePhase (fun x hx => (ha x hx).1) hac hP) hsign hdrop
  refine ⟨S, ?_, hroots⟩
  have e : 2 / π * ((d : ℝ) * (π / 2) - B) = d - 2 / π * B := by
    field_simp
  rw [e] at hS
  linarith

/-! ## The range `X ≍ √(d log d)` -/

/-- `X_d = √(d log d)/100`. -/
def saddleX (d : ℕ) : ℝ := Real.sqrt (d * Real.log d) / 100

theorem tendsto_log_natCast : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Eventually `log d ≤ c d`. -/
theorem eventually_log_le_mul {c : ℝ} (hc : 0 < c) : ∀ᶠ d : ℕ in atTop, Real.log (d : ℝ) ≤ c * d := by
  have h := Real.isLittleO_log_id_atTop.def hc
  have h2 := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually h
  filter_upwards [h2, eventually_gt_atTop 0] with d hd hpos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hpos
  simp only [id, Real.norm_eq_abs, abs_of_pos hdR] at hd
  exact (le_abs_self _).trans hd

/-- Eventually `log log d ≤ (1/10) log d`. -/
theorem eventually_loglog_le : ∀ᶠ d : ℕ in atTop, Real.log (Real.log (d : ℝ)) ≤ 1 / 10 * Real.log d := by
  have h := Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < 1 / 10 by norm_num)
  have h2 := tendsto_log_natCast.eventually h
  filter_upwards [h2, tendsto_log_natCast.eventually_gt_atTop 0] with d hd hpos
  simp only [id, Real.norm_eq_abs, abs_of_pos hpos] at hd
  exact (le_abs_self _).trans hd

/-- **For large `d`, `X_d` is a saddle range.** -/
theorem eventually_saddleRange :
    ∀ᶠ d : ℕ in atTop, SaddleRange d (saddleX d) ∧ 10 ≤ saddleX d := by
  filter_upwards [eventually_gt_atTop 0, tendsto_log_natCast.eventually_ge_atTop (5 * Real.exp 14 + 1000),
    eventually_log_le_mul (show (0 : ℝ) < 1 / 200000 by norm_num), eventually_loglog_le,
    eventually_ge_atTop 1000000] with d hd hL hlog hll hd1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hexp : 0 < Real.exp 14 := Real.exp_pos _
  set L := Real.log (d : ℝ) with hLdef
  have hL1 : 1000 ≤ L := by linarith
  have hdL : 0 ≤ (d : ℝ) * L := by positivity
  set X := saddleX d with hX
  have hX0 : 0 ≤ X := by
    rw [hX, saddleX]
    positivity
  have hXsq : X ^ 2 = d * L / 10000 := by
    rw [hX, saddleX, div_pow, Real.sq_sqrt hdL]
    norm_num
  have hd1R : (1000000 : ℝ) ≤ d := by exact_mod_cast hd1
  have hX10 : 10 ≤ X := by
    have : (10 : ℝ) ^ 2 ≤ X ^ 2 := by
      rw [hXsq, le_div_iff₀ (by norm_num)]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hX0 (by norm_num)).1 this
  have hX5 : (X + 5) ^ 2 ≤ 2 * X ^ 2 + 50 := by nlinarith [sq_nonneg (X - 5)]
  have hL2 : L ≤ (d : ℝ) / 200000 := by linarith
  have hkey : 2000 * ((L / 2) ^ 2 + (X + 5) ^ 2) ≤ d * L := by
    have h1 : 500 * L ^ 2 ≤ (d : ℝ) * L / 400 := by nlinarith
    have h2 : (100000 : ℝ) ≤ (d : ℝ) * L / 400 := by nlinarith
    rw [hXsq] at hX5
    nlinarith
  refine ⟨⟨hd, hX0, by linarith, hkey, ?_⟩, hX10⟩
  have hN : (L / 2) ^ 2 + (X + 5) ^ 2 ≤ d * L := by nlinarith
  have hNpos : 0 < (L / 2) ^ 2 + (X + 5) ^ 2 := by positivity
  have hlogN := Real.log_le_log hNpos hN
  rw [Real.log_mul hdR.ne' (by linarith)] at hlogN
  linarith

/-- **Finite degree Ki–Kim–Lee.** For large `d`, `R_d(Ξ)` has at least `d − 300 √(d log d)` distinct real roots. -/
theorem eventually_exists_real_roots_sqrt :
    ∀ᶠ d : ℕ in atTop, ∃ S : Finset ℝ, (d : ℝ) - 300 * Real.sqrt (d * Real.log d) ≤ S.card ∧
      ∀ x ∈ S, (xiJensenReal d).IsRoot x := by
  filter_upwards [eventually_saddleRange] with d hd
  obtain ⟨hR, hX10⟩ := hd
  have hX6 : 6 ≤ saddleX d := by linarith
  obtain ⟨S, hS, hroots⟩ := hR.exists_real_roots hX6
  refine ⟨S, ?_, hroots⟩
  have hπ := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have hL := hR.L_ge
  have hdR := hR.d_pos
  set L := Real.log (d : ℝ) with hLdef
  have hdL : 0 < (d : ℝ) * L := by positivity
  set Y := Real.sqrt (d * L) with hY
  have hYpos : 0 < Y := Real.sqrt_pos.2 hdL
  have hYsq : Y ^ 2 = d * L := Real.sq_sqrt hdL.le
  have hXeq : saddleX d = Y / 100 := rfl
  have hX5 : saddleX d / 2 ≤ saddleX d - 5 := by linarith
  have hXpos : 0 < saddleX d := by linarith
  have hT : (d : ℝ) / (saddleX d - 5) * (2 * L) ≤ 400 * Y := by
    have h1 : (d : ℝ) / (saddleX d - 5) ≤ d / (saddleX d / 2) :=
      div_le_div_of_nonneg_left hdR.le (by positivity) hX5
    have h2 : (d : ℝ) / (saddleX d / 2) * (2 * L) = 400 * Y := by
      rw [hXeq]
      field_simp
      nlinarith
    calc _ ≤ (d : ℝ) / (saddleX d / 2) * (2 * L) := by gcongr
      _ = _ := h2
  have hbound : 2 / π * ((d : ℝ) / (saddleX d - 5) * (2 * L)) + 4 ≤ 300 * Y := by
    have h1 : 2 / π * ((d : ℝ) / (saddleX d - 5) * (2 * L)) ≤ 2 / 3 * (400 * Y) := by
      have h2 : 2 / π ≤ 2 / 3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ.le
      have h3 : 0 ≤ (d : ℝ) / (saddleX d - 5) * (2 * L) := by
        have : 0 < saddleX d - 5 := by linarith
        positivity
      exact mul_le_mul h2 hT h3 (by norm_num)
    have hY4 : 1 ≤ Y := by
      have : (10 : ℝ) ≤ Y / 100 := by rw [← hXeq]; exact hX10
      linarith
    linarith
  linarith

/-- **The non-real count of `R_d(Ξ)` is at most `300 √(d log d)` for all large `d`.** -/
theorem eventually_jensenNonrealCount_le_sqrt :
    ∀ᶠ d : ℕ in atTop, (jensenNonrealCount d : ℝ) ≤ 300 * Real.sqrt (d * Real.log d) := by
  filter_upwards [eventually_exists_real_roots_sqrt] with d hd
  obtain ⟨S, hS, hroots⟩ := hd
  classical
  have hP := xiJensenReal_ne_zero d
  have hsub : S ⊆ (xiJensenReal d).roots.toFinset := fun x hx =>
    Multiset.mem_toFinset.2 ((mem_roots hP).2 (hroots x hx))
  have hcard : S.card ≤ Multiset.card (xiJensenReal d).roots :=
    (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
  have hN : jensenNonrealCount d + Multiset.card (xiJensenReal d).roots = d := by
    rw [jensenNonrealCount_eq, nonrealRootCount, natDegree_xiJensenReal]
    have : Multiset.card (xiJensenReal d).roots ≤ (xiJensenReal d).natDegree := card_roots' _
    rw [natDegree_xiJensenReal] at this
    omega
  have hNR : (jensenNonrealCount d : ℝ) + (Multiset.card (xiJensenReal d).roots : ℝ) = d := by
    exact_mod_cast hN
  have hcardR : (S.card : ℝ) ≤ (Multiset.card (xiJensenReal d).roots : ℝ) := by exact_mod_cast hcard
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.SaddleRange.exists_real_roots
#print axioms FiniteFreeProbability.eventually_exists_real_roots_sqrt
#print axioms FiniteFreeProbability.eventually_jensenNonrealCount_le_sqrt
