import GaloisForLFunctions.RHTower.DQPTEtaBound

/-!
# DQPT: the Dirichlet eta derivative and its bound `|η′(s)| ≤ |s|/β² + 1/β`

**Supplementary Note 6 (6.5)** of arXiv:2511.11199 (published Supplementary Note 8):
for `s = β + it` with `β > 0`,

`|η′(s)| ≤ |s| / β² + 1 / β`.

The derivative is obtained by term-by-term differentiation of the paired eta series
`η(s) = ∑ₙ ((2n+1)^{−s} − (2n+2)^{−s})`, legitimate by a locally uniform summable bound on the
term derivatives.  The estimate then comes from the fencing mean-value theorem applied to
`φ(x) = log x · x^{−s}`, whose `x`-derivative is `(1 − s log x)x^{−s−1}`, compared against the
real antiderivative `D(x) = −x^{−β}/β − ‖s‖(log x/β + 1/β²)x^{−β}` of `(1 + ‖s‖ log x)x^{−β−1}`,
and the non-overlapping pairs telescope against `D(∞) − D(1) = 1/β + ‖s‖/β²`.

Main results:
* `hasDerivAt_etaPair` — **`η′(s) = ∑ₙ (log(2n+2)(2n+2)^{−s} − log(2n+1)(2n+1)^{−s})`**;
* `dqpt_norm_etaPairDeriv_le` — **`‖η′(s)‖ ≤ ‖s‖/β² + 1/β`**.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## The logarithmic power `log x · x^{−s}` -/

/-- `log x · x^{−s}`. -/
def dqptLogRp (s : ℂ) (x : ℝ) : ℂ := ((Real.log x : ℝ) : ℂ) * dqptRp s x

theorem dqptRp_succ_eq {s : ℂ} {x : ℝ} (hx : 0 < x) :
    dqptRp (s + 1) x = dqptRp s x * ((x : ℂ))⁻¹ := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [dqptRp, dqptRp, show (-(s + 1) : ℂ) = -s + (-1 : ℂ) by ring,
    Complex.cpow_add _ _ hx0, Complex.cpow_neg_one]

theorem norm_dqptLogRp {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖dqptLogRp s x‖ = |Real.log x| * x ^ (-s.re) := by
  rw [dqptLogRp, norm_mul, Complex.norm_real, Real.norm_eq_abs, dqptRp_norm hx]

/-- The `x`-derivative of `log x · x^{−s}` is `(1 − s log x) x^{−s−1}`. -/
theorem hasDerivAt_dqptLogRp {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => dqptLogRp s y)
      ((1 - s * ((Real.log x : ℝ) : ℂ)) * dqptRp (s + 1) x) x := by
  have hlog : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) (((x⁻¹ : ℝ) : ℂ)) x := by
    have h := (Real.hasDerivAt_log (ne_of_gt hx))
    exact h.ofReal_comp
  have hpow := hasDerivAt_dqptRp hs hx
  have hprod := hlog.mul hpow
  refine hprod.congr_deriv ?_
  rw [dqptRp_succ_eq hx]
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hinv : (((x⁻¹ : ℝ)) : ℂ) = ((x : ℝ) : ℂ)⁻¹ := by push_cast; ring
  rw [hinv]
  field_simp
  ring

/-! ## The term-wise derivative of the paired eta series -/

/-- The derivative in `s` of the `n`-th paired eta term. -/
def dqptEtaTermDeriv (s : ℂ) (n : ℕ) : ℂ :=
  dqptLogRp s (2 * (n : ℝ) + 2) - dqptLogRp s (2 * (n : ℝ) + 1)

theorem hasDerivAt_etaTerm (s : ℂ) (n : ℕ) :
    HasDerivAt (fun w : ℂ => etaTerm w n) (dqptEtaTermDeriv s n) s := by
  have ha : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
  have hane : ((2 * (n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hbne : ((2 * (n : ℝ) + 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb)
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) s := hasDerivAt_neg s
  have hA := hneg.const_cpow (c := ((2 * (n : ℝ) + 1 : ℝ) : ℂ)) (Or.inl hane)
  have hB := hneg.const_cpow (c := ((2 * (n : ℝ) + 2 : ℝ) : ℂ)) (Or.inl hbne)
  have hsub := hA.sub hB
  refine hsub.congr_deriv ?_
  rw [dqptEtaTermDeriv, dqptLogRp, dqptLogRp, dqptRp, dqptRp,
    Complex.ofReal_log (le_of_lt ha), Complex.ofReal_log (le_of_lt hb)]
  ring

/-! ## A locally uniform summable bound on the term derivatives -/

theorem dqpt_log_le_rpow_div {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    Real.log x ≤ x ^ δ / δ := by
  have hexp : δ * Real.log x + 1 ≤ Real.exp (δ * Real.log x) := by
    simpa [add_comm] using Real.add_one_le_exp (δ * Real.log x)
  have hrpow : x ^ δ = Real.exp (δ * Real.log x) := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  rw [le_div_iff₀ hδ]
  nlinarith [hexp, hrpow]

/-- The uniform bound on the `n`-th term derivative over a half-plane slab. -/
theorem norm_dqptEtaTermDeriv_le {w : ℂ} {β₀ M : ℝ} (hβ₀ : 0 < β₀) (hre : β₀ ≤ w.re)
    (hM : ‖w‖ ≤ M) (n : ℕ) :
    ‖dqptEtaTermDeriv w n‖
      ≤ (1 + M * Real.log (2 * (n : ℝ) + 2)) * (2 * (n : ℝ) + 1) ^ (-β₀ - 1) := by
  have hws : 0 < w.re := lt_of_lt_of_le hβ₀ hre
  have ha : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have ha1 : (1 : ℝ) ≤ 2 * (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  have hab : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2 := by linarith
  have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg w) hM
  set C : ℝ := (1 + M * Real.log (2 * (n : ℝ) + 2)) * (2 * (n : ℝ) + 1) ^ (-β₀ - 1) with hC
  have hderiv : ∀ x ∈ Icc (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2),
      HasDerivWithinAt (fun y : ℝ => dqptLogRp w y)
        ((1 - w * ((Real.log x : ℝ) : ℂ)) * dqptRp (w + 1) x)
        (Icc (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2)) x := by
    intro x hx
    exact (hasDerivAt_dqptLogRp hws (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2),
      ‖(1 - w * ((Real.log x : ℝ) : ℂ)) * dqptRp (w + 1) x‖ ≤ C := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    have hx1 : (1 : ℝ) ≤ x := le_trans ha1 hx.1
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlogle : Real.log x ≤ Real.log (2 * (n : ℝ) + 2) :=
      Real.log_le_log hx0 (le_of_lt hx.2)
    have h1 : ‖(1 : ℂ) - w * ((Real.log x : ℝ) : ℂ)‖ ≤ 1 + M * Real.log (2 * (n : ℝ) + 2) := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogx]
      have : ‖w‖ * Real.log x ≤ M * Real.log (2 * (n : ℝ) + 2) := by
        exact mul_le_mul hM hlogle hlogx hMnn
      linarith
    have hre1 : -(w + 1).re = -w.re - 1 := by
      rw [Complex.add_re, Complex.one_re]; ring
    have h2 : ‖dqptRp (w + 1) x‖ ≤ (2 * (n : ℝ) + 1) ^ (-β₀ - 1) := by
      rw [dqptRp_norm hx0, hre1]
      calc x ^ (-w.re - 1) ≤ (2 * (n : ℝ) + 1) ^ (-w.re - 1) :=
            Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)
        _ ≤ (2 * (n : ℝ) + 1) ^ (-β₀ - 1) :=
            Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    rw [norm_mul, hC]
    refine mul_le_mul h1 h2 (norm_nonneg _) ?_
    have : (0 : ℝ) ≤ M * Real.log (2 * (n : ℝ) + 2) := by
      have : (0 : ℝ) ≤ Real.log (2 * (n : ℝ) + 2) := Real.log_nonneg (by linarith)
      positivity
    linarith
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (2 * (n : ℝ) + 2)
    (right_mem_Icc.2 hab)
  have hlen : (2 * (n : ℝ) + 2) - (2 * (n : ℝ) + 1) = 1 := by ring
  rw [hlen, mul_one] at key
  rw [dqptEtaTermDeriv]
  exact key

/-- The summable majorant used for term-by-term differentiation. -/
def dqptDerivMajorant (β₀ M : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (-β₀ - 1)
    + (M * (2 : ℝ) ^ (β₀ / 2) / (β₀ / 2)) * ((n : ℝ) + 1) ^ (β₀ / 2 - β₀ - 1)

theorem summable_dqptDerivMajorant {β₀ M : ℝ} (hβ₀ : 0 < β₀) :
    Summable (dqptDerivMajorant β₀ M) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-β₀ - 1)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show -β₀ - 1 < -1 by linarith))
    refine h.congr (fun n => ?_)
    push_cast; ring_nf
  have h2 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (β₀ / 2 - β₀ - 1)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show β₀ / 2 - β₀ - 1 < -1 by linarith))
    refine h.congr (fun n => ?_)
    push_cast; ring_nf
  exact h1.add (h2.mul_left _)

theorem norm_dqptEtaTermDeriv_le_majorant {w : ℂ} {β₀ M : ℝ} (hβ₀ : 0 < β₀) (hre : β₀ ≤ w.re)
    (hM : ‖w‖ ≤ M) (n : ℕ) :
    ‖dqptEtaTermDeriv w n‖ ≤ dqptDerivMajorant β₀ M n := by
  have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg w) hM
  set δ : ℝ := β₀ / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have ha1 : (1 : ℝ) ≤ 2 * (n : ℝ) + 1 := by linarith
  have hb : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
  have hstep := norm_dqptEtaTermDeriv_le hβ₀ hre hM n
  have hpow1 : (2 * (n : ℝ) + 1) ^ (-β₀ - 1) ≤ ((n : ℝ) + 1) ^ (-β₀ - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hpowδ : (2 * (n : ℝ) + 1) ^ (δ - β₀ - 1) ≤ ((n : ℝ) + 1) ^ (δ - β₀ - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by rw [hδdef]; linarith)
  have hlog : Real.log (2 * (n : ℝ) + 2) ≤ (2 : ℝ) ^ δ * ((n : ℝ) + 1) ^ δ / δ := by
    have h := dqpt_log_le_rpow_div hδ (show (0 : ℝ) < 2 * (n : ℝ) + 2 by positivity)
    have hsplit : (2 * (n : ℝ) + 2) ^ δ = (2 : ℝ) ^ δ * ((n : ℝ) + 1) ^ δ := by
      rw [show (2 * (n : ℝ) + 2 : ℝ) = 2 * ((n : ℝ) + 1) by ring,
        Real.mul_rpow (by norm_num) (by linarith)]
    rw [hsplit] at h
    exact h
  have hpos1 : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ (-β₀ - 1) := Real.rpow_pos_of_pos ha _
  have hexpand : (1 + M * Real.log (2 * (n : ℝ) + 2)) * (2 * (n : ℝ) + 1) ^ (-β₀ - 1)
      ≤ (2 * (n : ℝ) + 1) ^ (-β₀ - 1)
        + (M * (2 : ℝ) ^ δ / δ) * (((n : ℝ) + 1) ^ δ * (2 * (n : ℝ) + 1) ^ (-β₀ - 1)) := by
    have hlogmul : M * Real.log (2 * (n : ℝ) + 2) ≤ M * ((2 : ℝ) ^ δ * ((n : ℝ) + 1) ^ δ / δ) :=
      mul_le_mul_of_nonneg_left hlog hMnn
    have hfin : (M * Real.log (2 * (n : ℝ) + 2)) * (2 * (n : ℝ) + 1) ^ (-β₀ - 1)
        ≤ (M * ((2 : ℝ) ^ δ * ((n : ℝ) + 1) ^ δ / δ)) * (2 * (n : ℝ) + 1) ^ (-β₀ - 1) :=
      mul_le_mul_of_nonneg_right hlogmul (le_of_lt hpos1)
    have hrw : (M * ((2 : ℝ) ^ δ * ((n : ℝ) + 1) ^ δ / δ)) * (2 * (n : ℝ) + 1) ^ (-β₀ - 1)
        = (M * (2 : ℝ) ^ δ / δ) * (((n : ℝ) + 1) ^ δ * (2 * (n : ℝ) + 1) ^ (-β₀ - 1)) := by
      field_simp
    rw [hrw] at hfin
    linarith
  have hmix : ((n : ℝ) + 1) ^ δ * (2 * (n : ℝ) + 1) ^ (-β₀ - 1)
      ≤ ((n : ℝ) + 1) ^ (δ - β₀ - 1) := by
    have hsplit : ((n : ℝ) + 1) ^ (δ - β₀ - 1) = ((n : ℝ) + 1) ^ δ * ((n : ℝ) + 1) ^ (-β₀ - 1) := by
      rw [← Real.rpow_add (by linarith)]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hpow1 (Real.rpow_nonneg (by linarith) _)
  have hcoef : (0 : ℝ) ≤ M * (2 : ℝ) ^ δ / δ := by positivity
  rw [dqptDerivMajorant, ← hδdef]
  calc ‖dqptEtaTermDeriv w n‖
      ≤ (1 + M * Real.log (2 * (n : ℝ) + 2)) * (2 * (n : ℝ) + 1) ^ (-β₀ - 1) := hstep
    _ ≤ (2 * (n : ℝ) + 1) ^ (-β₀ - 1)
        + (M * (2 : ℝ) ^ δ / δ) * (((n : ℝ) + 1) ^ δ * (2 * (n : ℝ) + 1) ^ (-β₀ - 1)) := hexpand
    _ ≤ ((n : ℝ) + 1) ^ (-β₀ - 1)
        + (M * (2 : ℝ) ^ δ / δ) * ((n : ℝ) + 1) ^ (δ - β₀ - 1) := by
        have := mul_le_mul_of_nonneg_left hmix hcoef
        linarith

/-! ## Term-by-term differentiation -/

set_option maxHeartbeats 1200000 in
/-- **The paired eta series may be differentiated term by term on `{Re s > 0}`.** -/
theorem hasDerivAt_etaPair {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt etaPair (∑' n : ℕ, dqptEtaTermDeriv s n) s := by
  have hβ₀ : 0 < s.re / 2 := by linarith
  have htopen : IsOpen (Metric.ball s (s.re / 2)) := Metric.isOpen_ball
  have htconn : IsPreconnected (Metric.ball s (s.re / 2)) :=
    (convex_ball s (s.re / 2)).isPreconnected
  have hst : s ∈ Metric.ball s (s.re / 2) := Metric.mem_ball_self hβ₀
  have hslab : ∀ w ∈ Metric.ball s (s.re / 2),
      s.re / 2 ≤ w.re ∧ ‖w‖ ≤ ‖s‖ + s.re / 2 := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    refine ⟨?_, ?_⟩
    · have hre : |(w - s).re| ≤ ‖w - s‖ := Complex.abs_re_le_norm _
      have hsub : (w - s).re = w.re - s.re := by simp
      rw [hsub] at hre
      have h2 : |w.re - s.re| < s.re / 2 := lt_of_le_of_lt hre hw
      have h3 := abs_lt.mp h2
      linarith [h3.1]
    · have := norm_sub_norm_le w s
      linarith
  have hsum0 : Summable fun n : ℕ => etaTerm s n := summable_etaTerm s hs
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (w : ℂ) => etaTerm w n)
    (g' := fun (n : ℕ) (w : ℂ) => dqptEtaTermDeriv w n)
    (u := dqptDerivMajorant (s.re / 2) (‖s‖ + s.re / 2))
    (summable_dqptDerivMajorant hβ₀) htopen htconn ?_ ?_ hst hsum0 hst
  · intro n w _
    exact hasDerivAt_etaTerm w n
  · intro n w hw
    obtain ⟨h1, h2⟩ := hslab w hw
    exact norm_dqptEtaTermDeriv_le_majorant hβ₀ h1 h2 n

/-! ## The `η′` bound -/

/-- The real comparison function for the `η′` bound:
`D(x) = −x^{−β}/β − ‖s‖(log x/β + 1/β²)x^{−β}`. -/
def dqptEtaDerivMajorant (s : ℂ) (x : ℝ) : ℝ :=
  -(x ^ (-s.re) / s.re)
    - ‖s‖ * ((Real.log x / s.re + 1 / s.re ^ 2) * x ^ (-s.re))

theorem hasDerivAt_dqptEtaDerivMajorant {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dqptEtaDerivMajorant s)
      ((1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ (-s.re)) ((-s.re) * x ^ (-s.re - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  have hinner : HasDerivAt (fun y : ℝ => Real.log y / s.re + 1 / s.re ^ 2) (x⁻¹ / s.re) x := by
    have := (hlog.div_const s.re).add_const (1 / s.re ^ 2)
    exact this
  have hmul : HasDerivAt (fun y : ℝ => (Real.log y / s.re + 1 / s.re ^ 2) * y ^ (-s.re))
      ((x⁻¹ / s.re) * x ^ (-s.re)
        + (Real.log x / s.re + 1 / s.re ^ 2) * ((-s.re) * x ^ (-s.re - 1))) x :=
    hinner.mul hpow
  have hfirst : HasDerivAt (fun y : ℝ => -(y ^ (-s.re) / s.re))
      (-(((-s.re) * x ^ (-s.re - 1)) / s.re)) x := (hpow.div_const s.re).neg
  have htotal := hfirst.sub (hmul.const_mul ‖s‖)
  refine htotal.congr_deriv ?_
  have hxsplit : x ^ (-s.re) = x * x ^ (-s.re - 1) := by
    have hadd : x ^ ((1 : ℝ) + (-s.re - 1)) = x ^ (1 : ℝ) * x ^ (-s.re - 1) :=
      Real.rpow_add hx 1 (-s.re - 1)
    rw [Real.rpow_one] at hadd
    rw [← hadd]
    congr 1
    ring
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsne : s.re ≠ 0 := ne_of_gt hs
  rw [hxsplit]
  field_simp
  ring

theorem dqptEtaDerivMajorant_nonpos {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 1 ≤ x) :
    dqptEtaDerivMajorant s x ≤ 0 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hpow : (0 : ℝ) < x ^ (-s.re) := Real.rpow_pos_of_pos hx0 _
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : (0 : ℝ) ≤ x ^ (-s.re) / s.re := by positivity
  have h2 : (0 : ℝ) ≤ ‖s‖ * ((Real.log x / s.re + 1 / s.re ^ 2) * x ^ (-s.re)) := by
    have : (0 : ℝ) ≤ Real.log x / s.re + 1 / s.re ^ 2 := by positivity
    positivity
  rw [dqptEtaDerivMajorant]
  linarith

theorem dqptEtaDerivMajorant_one {s : ℂ} (hs : 0 < s.re) :
    dqptEtaDerivMajorant s 1 = -(1 / s.re) - ‖s‖ / s.re ^ 2 := by
  have hsne : s.re ≠ 0 := ne_of_gt hs
  rw [dqptEtaDerivMajorant, Real.one_rpow, Real.log_one]
  field_simp
  ring

/-- A nonnegative derivative gives monotonicity, via the fencing bound applied to `0`. -/
theorem dqpt_mono_of_deriv_nonneg {B B' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, 0 ≤ B' x) : B a ≤ B b := by
  have h := dqpt_norm_sub_le_of_deriv_le (E := ℝ) (f := fun _ => (0 : ℝ))
    (f' := fun _ => (0 : ℝ)) hab continuousOn_const
    (fun x _ => (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt) hB hB'
    (by simpa using bound)
  simpa using h

theorem dqptEtaDerivMajorant_mono {s : ℂ} (hs : 0 < s.re) :
    ∀ x y : ℝ, 1 ≤ x → x ≤ y → dqptEtaDerivMajorant s x ≤ dqptEtaDerivMajorant s y := by
  intro x y hx hxy
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  refine dqpt_mono_of_deriv_nonneg (B' := fun z : ℝ => (1 + ‖s‖ * Real.log z) * z ^ (-s.re - 1))
    hxy ?_ ?_ ?_
  · intro z hz
    exact ((hasDerivAt_dqptEtaDerivMajorant hs
      (lt_of_lt_of_le hx0 hz.1)).continuousAt).continuousWithinAt
  · intro z hz
    exact (hasDerivAt_dqptEtaDerivMajorant hs (lt_of_lt_of_le hx0 hz.1)).hasDerivWithinAt
  · intro z hz
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le hx0 hz.1
    have hz1 : (1 : ℝ) ≤ z := le_trans hx hz.1
    have hlog : 0 ≤ Real.log z := Real.log_nonneg hz1
    have hpow : (0 : ℝ) < z ^ (-s.re - 1) := Real.rpow_pos_of_pos hz0 _
    have : (0 : ℝ) ≤ 1 + ‖s‖ * Real.log z := by positivity
    positivity

theorem norm_dqptEtaTermDeriv_le_derivMajorant {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dqptEtaTermDeriv s n‖
      ≤ dqptEtaDerivMajorant s (2 * (n : ℝ) + 2) - dqptEtaDerivMajorant s (2 * (n : ℝ) + 1) := by
  have ha : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hab : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2 := by linarith
  have hcont : ContinuousOn (fun x : ℝ => dqptLogRp s x)
      (Icc (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2)) := by
    intro x hx
    exact ((hasDerivAt_dqptLogRp hs (lt_of_lt_of_le ha hx.1)).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ Ico (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2),
      HasDerivWithinAt (fun y : ℝ => dqptLogRp s y)
        ((1 - s * ((Real.log x : ℝ) : ℂ)) * dqptRp (s + 1) x) (Ici x) x := by
    intro x hx
    exact (hasDerivAt_dqptLogRp hs (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  have hBcont : ContinuousOn (dqptEtaDerivMajorant s)
      (Icc (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2)) := by
    intro x hx
    exact ((hasDerivAt_dqptEtaDerivMajorant hs
      (lt_of_lt_of_le ha hx.1)).continuousAt).continuousWithinAt
  have hBderiv : ∀ x ∈ Ico (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2),
      HasDerivWithinAt (dqptEtaDerivMajorant s)
        ((1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) (Ici x) x := by
    intro x hx
    exact (hasDerivAt_dqptEtaDerivMajorant hs (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2),
      ‖(1 - s * ((Real.log x : ℝ) : ℂ)) * dqptRp (s + 1) x‖
        ≤ (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    have hx1 : (1 : ℝ) ≤ x := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [hx.1]
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h1 : ‖(1 : ℂ) - s * ((Real.log x : ℝ) : ℂ)‖ ≤ 1 + ‖s‖ * Real.log x := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogx]
    have hre1 : -(s + 1).re = -s.re - 1 := by
      rw [Complex.add_re, Complex.one_re]; ring
    have h2 : ‖dqptRp (s + 1) x‖ = x ^ (-s.re - 1) := by
      rw [dqptRp_norm hx0, hre1]
    rw [norm_mul, h2]
    refine mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.rpow_pos_of_pos hx0 _))
  have key := dqpt_norm_sub_le_of_deriv_le hab hcont hderiv hBcont hBderiv hbound
  rw [dqptEtaTermDeriv]
  exact key

/-- **Supplementary Note 6 (6.5).**  `‖η′(s)‖ ≤ ‖s‖/β² + 1/β`. -/
theorem dqpt_norm_etaPairDeriv_le {s : ℂ} (hs : 0 < s.re) :
    ‖∑' n : ℕ, dqptEtaTermDeriv s n‖ ≤ ‖s‖ / s.re ^ 2 + 1 / s.re := by
  set a : ℕ → ℝ := fun n => 2 * (n : ℝ) + 1 with hadef
  set b : ℕ → ℝ := fun n => 2 * (n : ℝ) + 2 with hbdef
  have hb1 : ∀ n : ℕ, (1 : ℝ) ≤ b n := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [hbdef]
    linarith
  have hstep : ∀ n : ℕ, b n ≤ a (n + 1) := by
    intro n; rw [hadef, hbdef]; push_cast; linarith
  have hpartial : ∀ K : ℕ, ∑ n ∈ Finset.range K, ‖dqptEtaTermDeriv s n‖
      ≤ ‖s‖ / s.re ^ 2 + 1 / s.re := by
    intro K
    have hcompare : ∑ n ∈ Finset.range K, ‖dqptEtaTermDeriv s n‖
        ≤ ∑ n ∈ Finset.range K,
            (dqptEtaDerivMajorant s (b n) - dqptEtaDerivMajorant s (a n)) :=
      Finset.sum_le_sum (fun n _ => norm_dqptEtaTermDeriv_le_derivMajorant hs n)
    have htel := dqpt_gap_telescope (dqptEtaDerivMajorant_mono hs) hb1 hstep K
    have haK : dqptEtaDerivMajorant s (a K) ≤ 0 := by
      refine dqptEtaDerivMajorant_nonpos hs ?_
      have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      simp only [hadef]
      linarith
    have ha0 : dqptEtaDerivMajorant s (a 0) = -(1 / s.re) - ‖s‖ / s.re ^ 2 := by
      have h0 : a 0 = 1 := by rw [hadef]; norm_num
      rw [h0, dqptEtaDerivMajorant_one hs]
    rw [ha0] at htel
    linarith
  have hsummable : Summable (fun n : ℕ => ‖dqptEtaTermDeriv s n‖) :=
    summable_of_sum_range_le (fun n => norm_nonneg _) hpartial
  have htsum : ∑' n : ℕ, ‖dqptEtaTermDeriv s n‖ ≤ ‖s‖ / s.re ^ 2 + 1 / s.re :=
    Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hpartial
  exact le_trans (norm_tsum_le_tsum_norm hsummable) htsum

end

end RHTower.DQPT
