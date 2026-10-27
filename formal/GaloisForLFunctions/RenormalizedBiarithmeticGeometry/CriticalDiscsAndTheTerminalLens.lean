import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalPairRay

/-!
# Critical discs and the terminal lens

Write a zero of `ξ` as `ρ = ½ + b + iγ` and a point as `s = ½ + x + iy`. The reflected pair
`{ρ, 1 − ρ̄}` contributes to `2 Re ξ′/ξ(s)` the amount

`2x (x² + (y − γ)² − b²) / (|s − ρ|² |s − (1 − ρ̄)|²)`,

so for `x > 0` the pair pulls `Re ξ′/ξ` negative exactly inside its **critical disc**, the open disc
of radius `|b|` about the foot `½ + iγ` (`xiLinePairRe_neg_of_inCriticalDisc`,
`xiLinePairRe_nonneg_of_not_inCriticalDisc`).

* **The Carathéodory region** (`re_logDeriv_xi_nonneg_of_outside_discs`). Right of the critical line
  and outside every critical disc, `Re ξ′/ξ ≥ 0`. RH says every disc is empty.
* **Terminals are the points outside every disc** (`isTerminal_iff_outside_discs`). The empty
  quadratic cone of a right zero `p` (ACP) is, read from the other side, the statement that `p`
  lies in no critical disc.
* **The terminal lens** (`outside_discs_of_mem_terminalLens`, `xi_ne_zero_of_mem_terminalLens`,
  `re_logDeriv_xi_nonneg_of_mem_terminalLens`). Let `p = ½ + a + iγ_p` be a terminal and
  `T = √(¼ − a²)`. The lens

  `{x > 0, |y − γ_p| ≤ T, x² − a² + (y − γ_p)² ≥ 2T|y − γ_p|}`,

  the region right of the two circles of radius `½` through `p` centred at `½ + i(γ_p ± T)`, lies
  outside every critical disc. It contains no zero other than `p` where `|y − γ_p| < T`, and
  `Re ξ′/ξ ≥ 0` on it. This extends the outward ray of ACP to a two-dimensional sector at `p` of
  half-angle `arctan(a/T)`.
-/

noncomputable section

open RHTower

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open ArithmeticCorrespondencePositivity

/-! ### The sign of a reflected pair -/

/-- `s` lies in the open critical disc of the zero copy `q`. -/
def InCriticalDisc (q : XiZeroCopy) (s : ℂ) : Prop :=
  (s.re - 1 / 2) ^ 2 + (s.im - (q.1 : ℂ).im) ^ 2 < ((q.1 : ℂ).re - 1 / 2) ^ 2

/-- Outside the disc `R² + u² ≥ a²` the pair is nonnegative (`R > 0`). -/
theorem xiLinePairRe_nonneg_of_not_inCriticalDisc {R a u : ℝ} (hR : 0 < R)
    (h : a ^ 2 ≤ R ^ 2 + u ^ 2) : 0 ≤ xiLinePairRe R a u := by
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨hd1, hd2⟩ := reflected_pair_denominators_pos hlt
    rw [xiLinePairRe_eq_div R a u hd1 hd2]
    have : 0 < R ^ 2 - a ^ 2 + u ^ 2 := by linarith
    positivity
  · -- On the boundary circle the pair vanishes, except at a singular point of the pair.
    unfold xiLinePairRe
    by_cases h1 : (R - a) ^ 2 + u ^ 2 = 0
    · have hu : u = 0 := by nlinarith [sq_nonneg (R - a), sq_nonneg u]
      have hRa : R = a := by nlinarith [sq_nonneg (R - a), sq_nonneg u]
      subst hu hRa
      simp only [sub_self, zero_div, zero_add]
      positivity
    by_cases h2 : (R + a) ^ 2 + u ^ 2 = 0
    · have hu : u = 0 := by nlinarith [sq_nonneg (R + a), sq_nonneg u]
      have hRa : a = -R := by nlinarith [sq_nonneg (R + a), sq_nonneg u]
      subst hu hRa
      simp only [add_neg_cancel, zero_div, add_zero]
      exact div_nonneg (by linarith) (by positivity)
    have hd1 : 0 < (R - a) ^ 2 + u ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h1)
    have hd2 : 0 < (R + a) ^ 2 + u ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h2)
    have := xiLinePairRe_eq_div R a u hd1 hd2
    unfold xiLinePairRe at this
    rw [this, show R ^ 2 - a ^ 2 + u ^ 2 = 0 by linarith]
    simp

/-- Inside the disc `R² + u² < a²` the pair is negative (`R > 0`). -/
theorem xiLinePairRe_neg_of_inCriticalDisc {R a u : ℝ} (hR : 0 < R)
    (h : R ^ 2 + u ^ 2 < a ^ 2) : xiLinePairRe R a u < 0 := by
  have hd1 : 0 < (R - a) ^ 2 + u ^ 2 := by
    by_contra hd
    have : (R - a) ^ 2 + u ^ 2 = 0 := le_antisymm (le_of_not_gt hd) (by positivity)
    have hRa : R = a := by nlinarith [sq_nonneg (R - a), sq_nonneg u]
    rw [hRa] at h; nlinarith [sq_nonneg u]
  have hd2 : 0 < (R + a) ^ 2 + u ^ 2 := by
    by_contra hd
    have : (R + a) ^ 2 + u ^ 2 = 0 := le_antisymm (le_of_not_gt hd) (by positivity)
    have hRa : R = -a := by nlinarith [sq_nonneg (R + a), sq_nonneg u]
    rw [hRa] at h; nlinarith [sq_nonneg u]
  rw [xiLinePairRe_eq_div R a u hd1 hd2]
  apply div_neg_of_neg_of_pos _ (by positivity)
  have : R ^ 2 - a ^ 2 + u ^ 2 < 0 := by linarith
  nlinarith

/-! ### The Carathéodory region -/

/-- **The Carathéodory region.** Right of the critical line, off the zeros and outside every
critical disc, `Re ξ′/ξ ≥ 0`. -/
theorem re_logDeriv_xi_nonneg_of_outside_discs {s : ℂ} (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0)
    (hout : ∀ q : XiZeroCopy, ¬ InCriticalDisc q s) : 0 ≤ (logDeriv xi s).re := by
  have h := two_mul_re_logDeriv_xi_eq_tsum_pair hxi
  have hnn : 0 ≤ ∑' q : XiZeroCopy,
      xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) :=
    tsum_nonneg fun q => xiLinePairRe_nonneg_of_not_inCriticalDisc (by linarith)
      (le_of_not_gt (hout q))
  linarith

/-- **RH empties every critical disc.** -/
theorem not_inCriticalDisc_of_riemannHypothesis (hRH : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2)
    (q : XiZeroCopy) (s : ℂ) : ¬ InCriticalDisc q s := by
  unfold InCriticalDisc
  rw [hRH q, sub_self]
  nlinarith [sq_nonneg (s.re - 1 / 2), sq_nonneg (s.im - (q.1 : ℂ).im)]

/-! ### Terminals and the lens -/

/-- The quadratic terminal condition of ACP: the cone of `p` contains no zero. -/
def IsTerminal (p : XiZeroCopy) : Prop :=
  ∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤ xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2

/-- **Terminals are the zeros outside every critical disc.** -/
theorem isTerminal_iff_outside_discs (p : XiZeroCopy) :
    IsTerminal p ↔ ∀ r : XiZeroCopy, ¬ InCriticalDisc r (p.1 : ℂ) := by
  unfold IsTerminal InCriticalDisc xiZeroDepth xiZeroHeight
  refine forall_congr' fun r => ?_
  rw [not_lt, sq_abs, sq_abs, show ((r.1 : ℂ).im - (p.1 : ℂ).im) ^ 2 =
    ((p.1 : ℂ).im - (r.1 : ℂ).im) ^ 2 by ring]

/-- The half-width `T = √(¼ − a²)` of the lens of a terminal of depth `a`. -/
def lensWidth (a : ℝ) : ℝ := Real.sqrt (1 / 4 - a ^ 2)

/-- The terminal lens of `p`: right of the two circles of radius `½` through `p` centred at
`½ + i(γ_p ± T)`. -/
def InTerminalLens (p : XiZeroCopy) (s : ℂ) : Prop :=
  0 < s.re - 1 / 2 ∧ |s.im - xiZeroHeight p| ≤ lensWidth (xiZeroDepth p) ∧
    2 * lensWidth (xiZeroDepth p) * |s.im - xiZeroHeight p| ≤
      (s.re - 1 / 2) ^ 2 - xiZeroDepth p ^ 2 + (s.im - xiZeroHeight p) ^ 2

/-- **The lens lies outside every critical disc.** -/
theorem outside_discs_of_mem_terminalLens {p : XiZeroCopy} (hp : IsTerminal p) {s : ℂ}
    (hs : InTerminalLens p s) (r : XiZeroCopy) : ¬ InCriticalDisc r s := by
  obtain ⟨hx, hdT, hlens⟩ := hs
  set a := xiZeroDepth p
  set T := lensWidth a
  set x := s.re - 1 / 2
  set d := s.im - xiZeroHeight p
  set t := xiZeroHeight r - xiZeroHeight p
  set b := (r.1 : ℂ).re - 1 / 2
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hTsq : T ^ 2 = 1 / 4 - a ^ 2 := by
    have h1 := (xiZeroDepth_bounds p).2
    have h0 := (xiZeroDepth_bounds p).1
    rw [show T = Real.sqrt (1 / 4 - a ^ 2) from rfl, Real.sq_sqrt (by nlinarith)]
  have hcone : b ^ 2 ≤ a ^ 2 + t ^ 2 := by
    have h := hp r
    have hb' : xiZeroDepth r ^ 2 = b ^ 2 := by simp only [xiZeroDepth, b, sq_abs]
    rw [hb'] at h
    exact h
  have hb : b ^ 2 ≤ 1 / 4 := by
    have h := xiZeroDepth_bounds r
    have : |b| ≤ 1 / 2 := h.2
    nlinarith [abs_nonneg b, sq_abs b]
  unfold InCriticalDisc
  rw [not_lt]
  have hsd : s.im - (r.1 : ℂ).im = d - t := by
    simp only [d, t, xiZeroHeight]; ring
  rw [hsd]
  change b ^ 2 ≤ x ^ 2 + (d - t) ^ 2
  have hdabs : 0 ≤ |d| := abs_nonneg d
  rcases le_or_gt |t| T with htT | htT
  · -- `|t| ≤ T`: compare with the cone.
    have hdt : d * t ≤ |d| * T := by
      calc d * t ≤ |d * t| := le_abs_self _
        _ = |d| * |t| := abs_mul d t
        _ ≤ |d| * T := mul_le_mul_of_nonneg_left htT hdabs
    nlinarith
  · -- `|t| > T`: compare with the strip.
    have h1 : T - |d| ≤ |t| - |d| := by linarith
    have h2 : 0 ≤ T - |d| := by linarith
    have h3 : (T - |d|) ^ 2 ≤ (d - t) ^ 2 := by
      have : |t| - |d| ≤ |d - t| := by
        have h4 := abs_sub_abs_le_abs_sub t d
        have h5 : |t - d| = |d - t| := abs_sub_comm t d
        linarith
      nlinarith [sq_abs (d - t), abs_nonneg (d - t)]
    nlinarith [sq_abs d]

/-- **The lens is zero-free** away from `p` in its open part `|y − γ_p| < T`. -/
theorem xi_ne_zero_of_mem_terminalLens {p : XiZeroCopy} (hp : IsTerminal p)
    (hright : 1 / 2 < (p.1 : ℂ).re) {s : ℂ} (hs : InTerminalLens p s)
    (hlt : |s.im - xiZeroHeight p| < lensWidth (xiZeroDepth p)) (hsp : s ≠ (p.1 : ℂ)) :
    xi s ≠ 0 := by
  intro hz
  obtain ⟨r, hr⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
  obtain ⟨hx, -, hlens⟩ := hs
  have hcone := hp r
  set a := xiZeroDepth p
  set T := lensWidth a
  have ha : a = (p.1 : ℂ).re - 1 / 2 := by
    simp only [a, xiZeroDepth]; rw [abs_of_pos (by linarith)]
  have hbr : xiZeroDepth r = s.re - 1 / 2 := by
    simp only [xiZeroDepth]; rw [hr, abs_of_pos hx]
  have hhr : xiZeroHeight r = s.im := by simp only [xiZeroHeight]; rw [hr]
  rw [hbr, hhr] at hcone
  set d := s.im - xiZeroHeight p
  -- Cone and lens force `2T|d| ≤ 2d²`, hence `d = 0`, then `s = p`.
  have hT : 2 * T * |d| ≤ 2 * d ^ 2 := by nlinarith
  have hd0 : d = 0 := by
    by_contra hd
    have hdpos : 0 < |d| := abs_pos.mpr hd
    have : T ≤ |d| := by nlinarith [sq_abs d]
    linarith
  have hx' : (s.re - 1 / 2) ^ 2 = a ^ 2 := by
    rw [hd0] at hcone hlens
    nlinarith
  have hxa : s.re - 1 / 2 = a := by
    have ha0 : 0 ≤ a := (xiZeroDepth_bounds p).1
    nlinarith [sq_nonneg (s.re - 1 / 2 - a), sq_nonneg (s.re - 1 / 2 + a)]
  apply hsp
  apply Complex.ext
  · rw [ha] at hxa; linarith
  · simp only [d, xiZeroHeight] at hd0; linarith

/-- **`Re ξ′/ξ ≥ 0` on the terminal lens.** -/
theorem re_logDeriv_xi_nonneg_of_mem_terminalLens {p : XiZeroCopy} (hp : IsTerminal p) {s : ℂ}
    (hs : InTerminalLens p s) (hxi : xi s ≠ 0) : 0 ≤ (logDeriv xi s).re :=
  re_logDeriv_xi_nonneg_of_outside_discs (by linarith [hs.1]) hxi
    (outside_discs_of_mem_terminalLens hp hs)

/-- The outward ray `p + h` lies in the lens. -/
theorem mem_terminalLens_of_ray {p : XiZeroCopy} (hright : 1 / 2 < (p.1 : ℂ).re) {h : ℝ}
    (hh : 0 ≤ h) : InTerminalLens p ((p.1 : ℂ) + h) := by
  have ha : xiZeroDepth p = (p.1 : ℂ).re - 1 / 2 := by
    simp only [xiZeroDepth]; rw [abs_of_pos (by linarith)]
  refine ⟨by simp; linarith, ?_, ?_⟩
  · simp [xiZeroHeight, Real.sqrt_nonneg, lensWidth]
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero,
      xiZeroHeight, sub_self, abs_zero, mul_zero, ha]
    nlinarith

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
