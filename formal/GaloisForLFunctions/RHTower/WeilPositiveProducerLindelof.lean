import GaloisForLFunctions.RHTower.WeilPositiveShortIntervalSupport
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzCriticalHalfPlane
import GaloisForLFunctions.HTGeometry.ThreeCircles

/-!
# Lindelöf growth for the zeta function of every Weil-positive system

Let `lam` (with `lam(1) = 0`) be Weil-positive in Herglotz form for a datum `A` of logarithmic
growth: `Φ = A + 1/(s−1) − Σ lam(n)n^{−s}` on `Re s > 1` continues holomorphically to
`Re s > 1/2` with `Re Φ ≥ 0` there.  Its zeta function is `F = exp L`, where
`L(s) = Σ lam(n) n^{−s}/log n`.  For `lam = Λ` this is `ζ`.

**Theorem** (`exists_logZeta_lindelof`).  For every `0 < δ < 1/2` there are `C` and `θ < 1` such
that at every height `|t| ≥ 6` the series `L` continues holomorphically to the disc
`B(3 + it, 5/2 − δ/4)` and satisfies

`|L(σ + it)| ≤ C (log(|t| + 3))^θ`  for `1/2 + δ ≤ σ ≤ 5/2`.

Hence `F` and `1/F` are `O(|t|^ε)` on `Re s ≥ 1/2 + δ` for every `ε > 0`
(`exists_producerZeta_subpolynomial`).  This is Lindelöf-quality growth for every full-cone
producer (`exists_producerZeta_subpolynomial_of_weilPositiveFull`), obtained from positivity
alone, with no Euler product, functional equation or zero information.

**Proof.**  The function `L` has derivative `−D = −(E + 1/(s−1))` with `E = A − Φ`, and
`|E(σ+it)| ≪ log|t|/(σ − 1/2)` (Harnack strip bound, `norm_regularPart_le`).  On the disc, `L`
continues as a primitive of `−(E + 1/(s−1))`.  The mean-value inequality gives `|L| ≪ log|t|` on
the circle of radius `5/2 − δ/2`.  On the circle of radius `1/2`, `L` is a convergent Dirichlet
series and is bounded.  Hadamard's three circles interpolates these two bounds to
`(log|t|)^θ` with `θ < 1`.  This is Littlewood's argument for "RH ⇒ Lindelöf", with Weil
positivity in place of RH.
-/

open Complex Metric Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The coefficients `lam(n)/log n` of the logarithm of a producer's zeta function. -/
def logZetaCoeff (lam : ℕ → ℝ) (n : ℕ) : ℂ := ((lam n / Real.log n : ℝ) : ℂ)

theorem norm_logZetaCoeff_le (lam : ℕ → ℝ) (n : ℕ) :
    ‖logZetaCoeff lam n‖ ≤ |lam n| / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold logZetaCoeff
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp <;> positivity
  · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h)
    rw [abs_of_pos (hl2.trans_le hlog)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl2 hlog

theorem lseriesSummable_logZetaCoeff {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (logZetaCoeff lam) y := by
  unfold LSeriesSummable
  refine Summable.of_norm (((hsum y hy).div_const (Real.log 2)).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpos : (0 : ℝ) < (n : ℝ) ^ y := Real.rpow_pos_of_pos hn0 y
    simp only [Complex.ofReal_re]
    rw [div_right_comm]
    exact div_le_div_of_nonneg_right (norm_logZetaCoeff_le lam n) hpos.le

theorem abscissaOfAbsConv_logZetaCoeff_le {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    LSeries.abscissaOfAbsConv (logZetaCoeff lam) ≤ 1 := by
  have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := logZetaCoeff lam)
    (x := 1) fun y hy => lseriesSummable_logZetaCoeff hsum hy
  exact_mod_cast this

theorem LSeries_logMul_logZetaCoeff {lam : ℕ → ℝ} (h1 : lam 1 = 0) (s : ℂ) :
    LSeries (LSeries.logMul (logZetaCoeff lam)) s = LSeries (fun n => (lam n : ℂ)) s := by
  refine LSeries_congr (fun {n} hn => ?_) s
  simp only [LSeries.logMul, logZetaCoeff]
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    simp [h1]
  · have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast h)).ne'
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n), ← Complex.ofReal_mul,
      mul_div_cancel₀ _ hlog]

/-- On `Re s > 1` the logarithmic zeta function has derivative `−Σ lam(n) n^{−s}`. -/
theorem hasDerivAt_LSeries_logZetaCoeff {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) (h1 : lam 1 = 0)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (LSeries (logZetaCoeff lam)) (-LSeries (fun n => (lam n : ℂ)) s) s := by
  have habs : LSeries.abscissaOfAbsConv (logZetaCoeff lam) < s.re :=
    (abscissaOfAbsConv_logZetaCoeff_le hsum).trans_lt (by exact_mod_cast hs)
  have h := LSeries_hasDerivAt habs
  rwa [LSeries_logMul_logZetaCoeff h1] at h

theorem norm_LSeries_le_of_two_le {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 2 ≤ s.re) :
    ‖LSeries (fun n => (lam n : ℂ)) s‖ ≤ ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) := by
  have hbound : ∀ n : ℕ, ‖LSeries.term (fun n => (lam n : ℂ)) s n‖ ≤ |lam n| / (n : ℝ) ^ (2 : ℝ) := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        (Real.rpow_le_rpow_of_exponent_le hn1 hs)
  have hs2 := hsum 2 (by norm_num)
  have hsn : Summable fun n => ‖LSeries.term (fun n => (lam n : ℂ)) s n‖ :=
    hs2.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hbound hs2)

theorem norm_LSeries_logZetaCoeff_le_of_two_le {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 2 ≤ s.re) :
    ‖LSeries (logZetaCoeff lam) s‖ ≤ (∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : ∀ n : ℕ, ‖LSeries.term (logZetaCoeff lam) s n‖ ≤
      |lam n| / (n : ℝ) ^ (2 : ℝ) / Real.log 2 := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hp : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := by positivity
      rw [div_right_comm]
      calc ‖logZetaCoeff lam n‖ / (n : ℝ) ^ s.re ≤ ‖logZetaCoeff lam n‖ / (n : ℝ) ^ (2 : ℝ) :=
            div_le_div_of_nonneg_left (norm_nonneg _) hp (Real.rpow_le_rpow_of_exponent_le hn1 hs)
        _ ≤ |lam n| / Real.log 2 / (n : ℝ) ^ (2 : ℝ) :=
            div_le_div_of_nonneg_right (norm_logZetaCoeff_le lam n) hp.le
  have hs2 := (hsum 2 (by norm_num)).div_const (Real.log 2)
  have hsn : Summable fun n => ‖LSeries.term (logZetaCoeff lam) s n‖ :=
    hs2.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  refine (norm_tsum_le_tsum_norm hsn).trans ((hsn.tsum_le_tsum hbound hs2).trans (le_of_eq ?_))
  exact tsum_div_const

theorem norm_vertical_sub_center (σ t : ℝ) (hσ : σ ≤ 3) :
    ‖(σ : ℂ) + t * I - ((3 : ℂ) + t * I)‖ = 3 - σ := by
  have h : (σ : ℂ) + t * I - ((3 : ℂ) + t * I) = ((σ - 3 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  ring

theorem three_circles_interp_le {M₁ K₃ ℓ u θ : ℝ} (hM₁ : 1 ≤ M₁) (hK₃ : 1 ≤ K₃) (hℓ : 1 ≤ ℓ)
    (hu0 : 0 ≤ u) (huθ : u ≤ θ) (hθ1 : θ ≤ 1) :
    M₁ ^ (1 - u) * (K₃ * ℓ) ^ u ≤ M₁ * K₃ * ℓ ^ θ := by
  have hK₃ℓ : 1 ≤ K₃ * ℓ := by nlinarith
  calc M₁ ^ (1 - u) * (K₃ * ℓ) ^ u ≤ M₁ * (K₃ * ℓ) ^ θ := by
        refine mul_le_mul ?_ (Real.rpow_le_rpow_of_exponent_le hK₃ℓ huθ) (by positivity)
          (by positivity)
        calc M₁ ^ (1 - u) ≤ M₁ ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hM₁ (by linarith)
          _ = M₁ := Real.rpow_one M₁
    _ = M₁ * (K₃ ^ θ * ℓ ^ θ) := by rw [Real.mul_rpow (by linarith) (by linarith)]
    _ ≤ M₁ * (K₃ * ℓ ^ θ) := by
        gcongr
        calc K₃ ^ θ ≤ K₃ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK₃ hθ1
          _ = K₃ := Real.rpow_one K₃
    _ = M₁ * K₃ * ℓ ^ θ := by ring

/-! ## The Lindelöf bound -/

/-- The Harnack strip bound in the form used below: on `Re w ≥ 1/2 + δ/2`,
`‖A − Φ‖ ≤ (2K'/δ) log(|Im w| + 3) + L₂ + 1`, where `K' = 6(K + 1 + L₂)` and
`L₂ = Σ |lam(n)|/n²`. -/
theorem norm_regularPart_le_of_re_ge {lam : ℕ → ℝ} {A Φ : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦid : ∀ s : ℂ, 1 < s.re → Φ s = A s + 1 / (s - 1) - LSeries (fun n => (lam n : ℂ)) s)
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : 1 / 2 + δ / 2 ≤ w.re) :
    ‖A w - Φ w‖ ≤ 2 * (6 * (K + 1 + ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ))) / δ *
      Real.log (|w.im| + 3) + (∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) + 1 := by
  set L₂ : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) with hL₂def
  have hL₂ : 0 ≤ L₂ := tsum_nonneg fun n => by positivity
  set K' : ℝ := 6 * (K + 1 + L₂) with hK'def
  have hK'0 : 0 ≤ K' := by rw [hK'def]; positivity
  have hlog0 : 0 ≤ Real.log (|w.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg w.im])
  have hpos : 0 ≤ 2 * K' / δ * Real.log (|w.im| + 3) :=
    mul_nonneg (div_nonneg (by linarith) hδ.le) hlog0
  rcases le_or_gt w.re 2 with h2 | h2
  · have hid : ∀ t : ℝ, Φ (2 + t * I) = A (2 + t * I) + 1 / (2 + t * I - 1) -
        LSeries (fun n => (lam n : ℂ)) (2 + t * I) := fun t => hΦid _ (by simp)
    have hr := norm_regularPart_le hK (hsum 2 (by norm_num)) hΦd hΦre hAK hid
      (σ := w.re) (t := w.im) (by linarith) h2
    rw [Complex.re_add_im] at hr
    have hσ : δ / 2 ≤ w.re - 1 / 2 := by linarith
    have hstep : K' * Real.log (|w.im| + 3) / (w.re - 1 / 2) ≤
        2 * K' / δ * Real.log (|w.im| + 3) := by
      rw [div_le_iff₀ (by linarith)]
      have h' : 2 * K' / δ * Real.log (|w.im| + 3) * (δ / 2) = K' * Real.log (|w.im| + 3) := by
        field_simp
      have := mul_le_mul_of_nonneg_left hσ hpos
      linarith
    linarith [hr.trans hstep]
  · have hw1 : 1 < w.re := by linarith
    have hEq : A w - Φ w = LSeries (fun n => (lam n : ℂ)) w - 1 / (w - 1) := by
      rw [hΦid w hw1]
      ring
    have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have h := Complex.abs_re_le_norm (w - 1)
      rw [Complex.sub_re, Complex.one_re, abs_of_pos (by linarith)] at h
      exact (div_le_one (by linarith)).mpr (by linarith)
    rw [hEq]
    have hD := norm_LSeries_le_of_two_le hsum h2.le
    have := norm_sub_le (LSeries (fun n => (lam n : ℂ)) w) (1 / (w - 1))
    linarith

/-- **Continuation of the logarithmic zeta function to a disc.**  On `B(3 + it, R)` with
`R ≤ 5/2` and `|t| ≥ 6`, a primitive of `−(A − Φ + 1/(s−1))` agrees with
`Σ lam(n) n^{−s}/log n` on `Re s > 1`. -/
theorem exists_logZeta_continuation {lam : ℕ → ℝ} {A Φ : ℂ → ℂ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) (h1 : lam 1 = 0)
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦid : ∀ s : ℂ, 1 < s.re → Φ s = A s + 1 / (s - 1) - LSeries (fun n => (lam n : ℂ)) s)
    {t R : ℝ} (ht : 6 ≤ |t|) (hR : R ≤ 5 / 2) :
    ∃ g : ℂ → ℂ, g ((3 : ℂ) + t * I) = LSeries (logZetaCoeff lam) ((3 : ℂ) + t * I) ∧
      (∀ w ∈ ball ((3 : ℂ) + t * I) R, HasDerivAt g (-(A w - Φ w + 1 / (w - 1))) w) ∧
      ∀ s ∈ ball ((3 : ℂ) + t * I) R, 1 < s.re → g s = LSeries (logZetaCoeff lam) s := by
  set c : ℂ := (3 : ℂ) + t * I with hc
  have hcre : c.re = 3 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have hre : ∀ w ∈ ball c R, 1 / 2 < w.re := by
    intro w hw
    rw [mem_ball_iff_norm] at hw
    have h := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re, hcre] at h
    have := neg_abs_le (w.re - 3)
    linarith
  have hne : ∀ w ∈ ball c R, w - 1 ≠ 0 := by
    intro w hw h0
    rw [mem_ball_iff_norm] at hw
    have h := Complex.abs_im_le_norm (w - c)
    rw [Complex.sub_im, hcim] at h
    have hw1 : w.im = 0 := by
      have := congrArg Complex.im h0
      simpa using this
    rw [hw1, zero_sub, abs_neg] at h
    linarith
  have hHo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGd : DifferentiableOn ℂ (fun w => -(A w - Φ w + 1 / (w - 1))) (ball c R) := by
    intro w hw
    have hwH : w ∈ {s : ℂ | 1 / 2 < s.re} := hre w hw
    have hAw := (hA w hwH).differentiableAt (hHo.mem_nhds hwH)
    have hΦw := (hΦd w hwH).differentiableAt (hHo.mem_nhds hwH)
    exact ((hAw.sub hΦw).add ((differentiableAt_const _).div (differentiableAt_id.sub_const 1)
      (hne w hw))).neg.differentiableWithinAt
  obtain ⟨g, hgc, hg⟩ := (hGd.isExactOn_ball).with_val_at c (LSeries (logZetaCoeff lam) c)
  refine ⟨g, hgc, hg, ?_⟩
  set U : Set ℂ := ball c R ∩ {s : ℂ | 1 < s.re} with hU
  have hUo : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hUc : IsPreconnected U :=
    ((convex_ball c R).inter (convex_halfSpace_re_gt 1)).isPreconnected
  intro s hs hs1
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) (mem_ball_iff_norm.mp hs)
  have hcU : c ∈ U := ⟨mem_ball_self hR0, by show (1 : ℝ) < c.re; rw [hcre]; norm_num⟩
  have hLd : ∀ s ∈ U, HasDerivAt (LSeries (logZetaCoeff lam))
      (-LSeries (fun n => (lam n : ℂ)) s) s := fun s hs =>
    hasDerivAt_LSeries_logZetaCoeff hsum h1 hs.2
  have hGeq : ∀ s ∈ U, -(A s - Φ s + 1 / (s - 1)) = -LSeries (fun n => (lam n : ℂ)) s := by
    intro s hs
    rw [hΦid s hs.2]
    ring
  have heq := hUo.eqOn_of_deriv_eq hUc
    (fun s hs => (hg s hs.1).differentiableAt.differentiableWithinAt)
    (fun s hs => (hLd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hg s hs.1).deriv, (hLd s hs).deriv, hGeq s hs]) hcU hgc
  exact heq ⟨hs, hs1⟩

/-- Mean-value bound on a circle from a derivative bound on the closed disc. -/
theorem norm_le_of_norm_deriv_le_closedBall {g : ℂ → ℂ} {c : ℂ} {r R B : ℝ} (hrR : r < R)
    (hr : 0 ≤ r) (hg : ∀ w ∈ ball c R, DifferentiableAt ℂ g w)
    (hB : ∀ w ∈ closedBall c r, ‖deriv g w‖ ≤ B) {z : ℂ} (hz : ‖z - c‖ = r) :
    ‖g z‖ ≤ ‖g c‖ + B * r := by
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hzmem : z ∈ closedBall c r := by rw [mem_closedBall_iff_norm, hz]
  have hmv := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => hg w (hsub hw)) hB (mem_closedBall_self hr) hzmem
  rw [hz] at hmv
  have := norm_sub_norm_le (g z) (g c)
  linarith

/-- **Producer Lindelöf (logarithmic form).**  Let `lam` (with `lam 1 = 0`) be Weil-positive in
Herglotz form for a datum `A` of logarithmic growth.  For every `0 < δ < 1/2` there are `C` and
`θ < 1` such that, at every height `|t| ≥ 6`, the logarithmic zeta function
`L(s) = Σ lam(n) n^{−s}/log n` continues holomorphically to the disc `B(3 + it, 5/2 − δ/4)` and
satisfies `|L(σ + it)| ≤ C (log(|t| + 3))^θ` for `1/2 + δ ≤ σ ≤ 5/2`. -/
theorem exists_logZeta_lindelof {lam : ℕ → ℝ} {A : ℂ → ℂ} (hW : HerglotzWeilPositive lam A)
    (h1 : lam 1 = 0) {K : ℝ} (hK : 0 ≤ K) (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ C θ : ℝ, 0 < C ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ t : ℝ, 6 ≤ |t| → ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4)) ∧
      (∀ s ∈ ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4), 1 < s.re →
        g s = LSeries (logZetaCoeff lam) s) ∧
      ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 5 / 2 →
        ‖g ((σ : ℂ) + t * I)‖ ≤ C * Real.log (|t| + 3) ^ θ := by
  obtain ⟨Φ, hΦd, hΦre, hΦid⟩ := hW.herglotz
  have hsum := hW.summable
  obtain ⟨L₂, hL₂def⟩ : ∃ L₂, L₂ = ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) := ⟨_, rfl⟩
  have hL₂ : 0 ≤ L₂ := by rw [hL₂def]; exact tsum_nonneg fun n => by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M, hMdef⟩ : ∃ M, M = L₂ / Real.log 2 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; exact div_nonneg hL₂ hl2.le
  obtain ⟨K', hK'def⟩ : ∃ K', K' = 6 * (K + 1 + L₂) := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK'def]; positivity
  have hEbd : ∀ w : ℂ, 1 / 2 + δ / 2 ≤ w.re →
      ‖A w - Φ w‖ ≤ 2 * K' / δ * Real.log (|w.im| + 3) + L₂ + 1 := by
    intro w hw
    have := norm_regularPart_le_of_re_ge hK hsum hΦd hΦre hΦid hAK hδ hw
    rw [← hL₂def, ← hK'def] at this
    exact this
  obtain ⟨r₃, hr₃⟩ : ∃ r₃ : ℝ, r₃ = 5 / 2 - δ / 2 := ⟨_, rfl⟩
  have h1r : (0 : ℝ) < 1 / 2 := by norm_num
  have h13 : (1 / 2 : ℝ) < r₃ := by rw [hr₃]; linarith
  have h3R : r₃ < 5 / 2 - δ / 4 := by rw [hr₃]; linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ,
      θ = (Real.log (5 / 2 - δ) - Real.log (1 / 2)) / (Real.log r₃ - Real.log (1 / 2)) :=
    ⟨_, rfl⟩
  have hden : 0 < Real.log r₃ - Real.log (1 / 2) := by
    have := Real.log_lt_log h1r h13
    linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθ]
    refine div_nonneg ?_ hden.le
    have := Real.log_le_log h1r (show (1 / 2 : ℝ) ≤ 5 / 2 - δ by linarith)
    linarith
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hden]
    have := Real.log_lt_log (by linarith : (0 : ℝ) < 5 / 2 - δ)
      (show 5 / 2 - δ < r₃ by rw [hr₃]; linarith)
    linarith
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, M₁ = M + 1 := ⟨_, rfl⟩
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℝ, K₃ = M + 3 * (4 * K' / δ + L₂ + 2) + 1 := ⟨_, rfl⟩
  have hM₁1 : 1 ≤ M₁ := by rw [hM₁]; linarith
  have h4K : 0 ≤ 4 * K' / δ := div_nonneg (by linarith) hδ.le
  have hK₃1 : 1 ≤ K₃ := by rw [hK₃]; linarith
  refine ⟨M₁ * K₃, θ, by positivity, hθ0, hθ1, fun t ht => ?_⟩
  obtain ⟨g, hgc, hg, hagree⟩ := exists_logZeta_continuation hsum h1 hA hΦd hΦid ht
    (R := 5 / 2 - δ / 4) (by linarith)
  have hgd : DifferentiableOn ℂ g (ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4)) :=
    fun w hw => (hg w hw).differentiableAt.differentiableWithinAt
  refine ⟨g, hgd, hagree, fun σ hσ hσ2 => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (3 : ℂ) + t * I := ⟨_, rfl⟩
  rw [← hc] at hgc hg hagree hgd
  have hcre : c.re = 3 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (|t| + 3) := ⟨_, rfl⟩
  rw [← hℓ]
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
    linarith
  -- inner circle
  have hM1 : ∀ z : ℂ, ‖z - c‖ = 1 / 2 → ‖g z‖ ≤ M₁ := by
    intro z hz
    have hzre : 5 / 2 ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre, hz] at h
      have := neg_abs_le (z.re - 3)
      linarith
    have hzb : z ∈ ball c (5 / 2 - δ / 4) := by rw [mem_ball_iff_norm, hz]; linarith
    rw [hagree z hzb (by linarith)]
    have := norm_LSeries_logZetaCoeff_le_of_two_le hsum (by linarith : (2 : ℝ) ≤ z.re)
    rw [← hL₂def, ← hMdef] at this
    rw [hM₁]
    linarith
  -- outer circle
  have hderiv_bd : ∀ w ∈ closedBall c r₃, ‖deriv g w‖ ≤ 4 * K' / δ * ℓ + L₂ + 2 := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    have hwB : w ∈ ball c (5 / 2 - δ / 4) := by rw [mem_ball_iff_norm]; linarith
    rw [(hg w hwB).deriv, norm_neg]
    have hwre : 1 / 2 + δ / 2 ≤ w.re := by
      have h := Complex.abs_re_le_norm (w - c)
      rw [Complex.sub_re, hcre] at h
      have := neg_abs_le (w.re - 3)
      linarith
    have hwim : |w.im - t| ≤ 3 := by
      have h := Complex.abs_im_le_norm (w - c)
      rw [Complex.sub_im, hcim] at h
      linarith
    have hlog : Real.log (|w.im| + 3) ≤ 2 * ℓ := by
      have h1' : |w.im| + 3 ≤ (|t| + 3) ^ 2 := by
        have : |w.im| ≤ |t| + 3 := by
          have := abs_sub_abs_le_abs_sub w.im t
          linarith
        nlinarith [abs_nonneg t]
      have := Real.log_le_log (by positivity) h1'
      rw [Real.log_pow] at this
      rw [hℓ]
      push_cast at this
      linarith
    have hone : 1 ≤ ‖w - 1‖ := by
      have h := Complex.abs_im_le_norm (w - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero] at h
      have := abs_sub_abs_le_abs_sub t w.im
      rw [abs_sub_comm] at this
      linarith
    have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact (div_le_one (by linarith)).mpr hone
    have hK0' : 0 ≤ 2 * K' / δ := div_nonneg (by linarith) hδ.le
    have hmul : 2 * K' / δ * Real.log (|w.im| + 3) ≤ 2 * K' / δ * (2 * ℓ) :=
      mul_le_mul_of_nonneg_left hlog hK0'
    have h4 : 2 * K' / δ * (2 * ℓ) = 4 * K' / δ * ℓ := by ring
    have hadd := norm_add_le (A w - Φ w) (1 / (w - 1))
    linarith [hEbd w hwre]
  have hM3 : ∀ z : ℂ, ‖z - c‖ = r₃ → ‖g z‖ ≤ K₃ * ℓ := by
    intro z hz
    have hmv := norm_le_of_norm_deriv_le_closedBall h3R (by linarith)
      (fun w hw => (hg w hw).differentiableAt) hderiv_bd hz
    have hgcb : ‖g c‖ ≤ M := by
      rw [hgc]
      have := norm_LSeries_logZetaCoeff_le_of_two_le hsum (by rw [hcre]; norm_num : (2 : ℝ) ≤ c.re)
      rw [← hL₂def, ← hMdef] at this
      exact this
    have hr3 : r₃ ≤ 3 := by rw [hr₃]; linarith
    have hbd0 : 0 ≤ 4 * K' / δ * ℓ + L₂ + 2 := by
      have := mul_nonneg h4K (by linarith : (0 : ℝ) ≤ ℓ)
      linarith
    have h2' : (4 * K' / δ * ℓ + L₂ + 2) * r₃ ≤ (4 * K' / δ * ℓ + L₂ + 2) * 3 :=
      mul_le_mul_of_nonneg_left hr3 hbd0
    have hA0 : 0 ≤ M + 3 * (L₂ + 2) + 1 := by linarith
    have hk : (M + 3 * (L₂ + 2) + 1) * 1 ≤ (M + 3 * (L₂ + 2) + 1) * ℓ :=
      mul_le_mul_of_nonneg_left hℓ1 hA0
    have hexp : K₃ * ℓ = (M + 3 * (L₂ + 2) + 1) * ℓ + 3 * (4 * K' / δ * ℓ) := by
      rw [hK₃]; ring
    linarith
  -- three circles
  have hzc := norm_vertical_sub_center σ t (by linarith)
  rw [← hc] at hzc
  have hz1 : (1 / 2 : ℝ) ≤ ‖(σ : ℂ) + t * I - c‖ := by rw [hzc]; linarith
  have hz3 : ‖(σ : ℂ) + t * I - c‖ ≤ r₃ := by rw [hzc, hr₃]; linarith
  have h3c := norm_le_of_three_circles_center h1r h13 h3R hgd hM1 hM3 hz1 hz3
  rw [hzc] at h3c
  have hu0 : 0 ≤ (Real.log (3 - σ) - Real.log (1 / 2)) / (Real.log r₃ - Real.log (1 / 2)) := by
    refine div_nonneg ?_ hden.le
    have := Real.log_le_log h1r (show (1 / 2 : ℝ) ≤ 3 - σ by linarith)
    linarith
  have huθ : (Real.log (3 - σ) - Real.log (1 / 2)) / (Real.log r₃ - Real.log (1 / 2)) ≤ θ := by
    rw [hθ]
    refine div_le_div_of_nonneg_right ?_ hden.le
    have := Real.log_le_log (by linarith) (show 3 - σ ≤ 5 / 2 - δ by linarith)
    linarith
  exact h3c.trans (three_circles_interp_le hM₁1 hK₃1 hℓ1 hu0 huθ hθ1.le)

/-- **Producer Lindelöf.**  Under the hypotheses of `exists_logZeta_lindelof`, for every `ε > 0`
there is `T₀` such that at every height `|t| ≥ T₀` the zeta function `F = exp L` continues to the
disc `B(3 + it, 5/2 − δ/4)` and satisfies `(|t|+3)^{−ε} ≤ |F(σ+it)| ≤ (|t|+3)^ε` for
`1/2 + δ ≤ σ ≤ 5/2`. -/
theorem exists_producerZeta_subpolynomial {lam : ℕ → ℝ} {A : ℂ → ℂ}
    (hW : HerglotzWeilPositive lam A) (h1 : lam 1 = 0) {K : ℝ} (hK : 0 ≤ K)
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ |t| → ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4)) ∧
      (∀ s ∈ ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4), 1 < s.re →
        g s = LSeries (logZetaCoeff lam) s) ∧
      ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 5 / 2 →
        (|t| + 3) ^ (-ε) ≤ ‖cexp (g ((σ : ℂ) + t * I))‖ ∧
          ‖cexp (g ((σ : ℂ) + t * I))‖ ≤ (|t| + 3) ^ ε := by
  obtain ⟨C, θ, hC, hθ0, hθ1, hmain⟩ := exists_logZeta_lindelof hW h1 hK hA hAK hδ hδ1
  obtain ⟨L₀, hL₀⟩ := (eventually_const_mul_rpow_le (c := C) hθ1 hε).exists_forall_of_atTop
  refine ⟨max 6 (Real.exp (max L₀ 0)), fun t ht => ?_⟩
  have ht6 : 6 ≤ |t| := (le_max_left _ _).trans ht
  obtain ⟨g, hgd, hagree, hbd⟩ := hmain t ht6
  refine ⟨g, hgd, hagree, fun σ hσ hσ2 => ?_⟩
  have hpos : 0 < |t| + 3 := by positivity
  have hℓ : L₀ ≤ Real.log (|t| + 3) := by
    have h1' : Real.exp (max L₀ 0) ≤ |t| + 3 := by
      have := (le_max_right 6 (Real.exp (max L₀ 0))).trans ht
      linarith
    have := Real.log_le_log (Real.exp_pos _) h1'
    rw [Real.log_exp] at this
    exact (le_max_left _ _).trans this
  have hgz := (hbd σ hσ hσ2).trans (hL₀ _ hℓ)
  have hre := Complex.abs_re_le_norm (g ((σ : ℂ) + t * I))
  rw [Complex.norm_exp, Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hpos]
  constructor
  · apply Real.exp_le_exp.mpr
    have := neg_abs_le (g ((σ : ℂ) + t * I)).re
    nlinarith
  · apply Real.exp_le_exp.mpr
    have := le_abs_self (g ((σ : ℂ) + t * I)).re
    nlinarith

/-- **Lindelöf growth for every full-cone producer.**  If `lam` is full-cone Weil-positive, then
for every `0 < δ < 1/2` and `ε > 0` the zeta function `exp(Σ_{n≥2} lam(n) n^{−s}/log n)`
continues to `1/2 + δ ≤ Re s ≤ 5/2` at every large height with
`(|t|+3)^{−ε} ≤ |F(σ+it)| ≤ (|t|+3)^ε`.  For `lam = Λ` (a producer exactly under RH) this is
Littlewood's "RH ⇒ Lindelöf" for `ζ` and `1/ζ`. -/
theorem exists_producerZeta_subpolynomial_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ |t| → ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4)) ∧
      (∀ s ∈ ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4), 1 < s.re →
        g s = LSeries (logZetaCoeff fun n => if 2 ≤ n then lam n else 0) s) ∧
      ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 5 / 2 →
        (|t| + 3) ^ (-ε) ≤ ‖cexp (g ((σ : ℂ) + t * I))‖ ∧
          ‖cexp (g ((σ : ℂ) + t * I))‖ ≤ (|t| + 3) ^ ε := by
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_zetaArchimedeanDatum
  exact exists_producerZeta_subpolynomial (WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW)
    (by simp) hK (differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith) hAK hδ hδ1 hε

end RHTower

end
