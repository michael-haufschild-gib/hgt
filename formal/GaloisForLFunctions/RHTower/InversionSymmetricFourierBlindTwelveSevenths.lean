import GaloisForLFunctions.RHTower.InversionSymmetricFourierBlindGaussTransfer

/-!
# Inversion-symmetric Fourier-blind functions of support ratio below `12/7`

Let `G : ℝ → ℝ` be continuous and even, with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, c)`,
and with Fourier transform vanishing at every integer `|n| ≥ 2`.

**Theorem** (`eq_zero_of_inversionSymmetric_fourierBlind_of_twelve_sevenths`).  If `12c > 7`, so
that the support `[c, 1/c]` has `1/c < 12/7`, then `G = 0`.  This passes the threshold `1 + 1/√2`
of `eq_zero_of_inversionSymmetric_fourierBlind_of_sqrt_two` (`12/7 > 1 + 1/√2`).

**Proof** for `2 − √2 ≥ c > 7/12`, with `H(v) = G(1 − 1/v)/v`, `τ(v) = 2 + 1/(v − 1)`,
`F = fareySeriesR (a₀ + 2a₁) (2a₁)`, `w₂ = 1/(1 − c)`, `v* = c/(2c − 1) ∈ (3, 7/2)` and the Gauss
transfer series `S` (`gaussTransferSeries`).
* The window `[p, q] = [v* − 1, 1 + 1/(v* − 3)]` is mapped into itself by `τ` (`τ(q) = p`, and
  `τ(p) ≤ q` because `v*² − 5v* + 5 ≤ 0`).  On it `v + 1 ≥ v*`, so
  `H(v) + H(τv)/(v − 1) = F(v)`, and therefore `H = S` (`eq_of_gaussWindow_equation`).
* For `2 < v < min(w₂, 1/(v* − 3))` both `v + 1` and `τv` lie in `[p, q]` while `H(v) = 0`.  So
  `S(v + 1) + S(τv)/(v − 1) = F(v) + F(v + 1)` on an interval, hence on `Re z > 1`.  With the
  transfer equation this gives `S(z + 1) − S(z) = F(z + 1)`, and then `S(v) = −S(2 + 1/v)/v` for
  real `v > 2`.
* On `(2, 5/2]` this halves `sup |S|`, so `S = 0` there and, by the identity theorem, on `Re z > 2`.
  Then `F = 0` on `(3, ∞)`, the Farey recursion at `4` and `6` gives `a₀ = a₁ = 0`, and `H = S = 0`
  on `[p, q]`.
* On the rest of `[w₂, v*]` the homogeneous equation halves `|H|` along `τ` or along
  `v ↦ τ(v + 1)` (`eq_zero_of_halving`), so `H = 0` on `[2, ∞)` and `G = 0`.
-/

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- The Gauss branch is antitone on `(1, ∞)`. -/
theorem gaussBranch_le_gaussBranch {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    gaussBranch y ≤ gaussBranch x := by
  unfold gaussBranch
  have : 1 / (y - 1) ≤ 1 / (x - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
  linarith

/-- **Halving.**  A function bounded on `K` whose modulus at every point of `K` is either zero or
at most half its modulus at another point of `K` vanishes on `K`. -/
theorem eq_zero_of_halving {f : ℝ → ℝ} {K : Set ℝ} {B : ℝ} (hB : ∀ v ∈ K, |f v| ≤ B)
    (hstep : ∀ v ∈ K, f v = 0 ∨ ∃ u ∈ K, |f v| ≤ |f u| / 2) : ∀ v ∈ K, f v = 0 := by
  have hiter : ∀ n : ℕ, ∀ v ∈ K, |f v| ≤ B / 2 ^ n := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hB v hv
    | succ n ih =>
      intro v hv
      rcases hstep v hv with h | ⟨u, hu, h⟩
      · have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB v hv)
        rw [h, abs_zero]
        positivity
      · calc |f v| ≤ |f u| / 2 := h
          _ ≤ B / 2 ^ n / 2 := by gcongr; exact ih u hu
          _ = B / 2 ^ (n + 1) := by rw [pow_succ]; ring
  intro v hv
  have hlim : Tendsto (fun n : ℕ => B / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  exact abs_nonpos_iff.mp (ge_of_tendsto' hlim fun n => hiter n v hv)

theorem gaussTransferSeries_zero (z : ℂ) : gaussTransferSeries 0 0 z = 0 := by
  unfold gaussTransferSeries gaussTransferTerm fareySeries
  simp

/-- **A shift identity forces the trivial Farey series.**  If the Gauss transfer series
`S = gaussTransferSeries a b` satisfies `S(x + 1) + S(τx)/(x − 1) = F(x) + F(x + 1)` on a real
interval `(2, m)`, then `a = b = 0`.  By the identity theorem the relation holds on `Re z > 1`;
with the transfer equation it gives `S(v) = −S(2 + 1/v)/v` for real `v > 2`, which halves
`sup |S|` on `(2, 5/2]`.  So `S = 0`, then `F = 0` on `(3, ∞)`, and the Farey recursion at `4`
and `6` gives `a = b = 0`. -/
theorem eq_zero_of_gaussTransferSeries_shift_identity (a b : ℝ) {m : ℝ} (hm2 : 2 < m)
    (hI : ∀ x : ℝ, 2 < x → x < m →
      gaussTransferSeries a b ((x : ℂ) + 1) +
          gaussTransferSeries a b (gaussBranchC x) / ((x : ℂ) - 1) -
        fareySeries a b x - fareySeries a b ((x : ℂ) + 1) = 0) :
    a = 0 ∧ b = 0 := by
  set S := gaussTransferSeries a b with hS
  set F := fareySeriesR a b with hF
  obtain ⟨CS, hCS⟩ := exists_norm_gaussTransferSeries_le a b
  set U₁ : Set ℂ := {z | 1 < z.re} with hU₁
  have hU₁o : IsOpen U₁ := isOpen_lt continuous_const Complex.continuous_re
  have hU₁sub : U₁ ⊆ halfPlaneHalf := fun z hz => by
    show 1 / 2 < z.re; have : 1 < z.re := hz; linarith
  have hshift : MapsTo (fun z : ℂ => z + 1) U₁ {z : ℂ | 2 < z.re} := fun z hz => by
    show 2 < (z + 1).re; have : 1 < z.re := hz; simp; linarith
  have hshift' : MapsTo (fun z : ℂ => z + 1) U₁ halfPlaneHalf := fun z hz => by
    show 1 / 2 < (z + 1).re; have : 1 < z.re := hz; simp; linarith
  set Φ : ℂ → ℂ := fun z => S (z + 1) + S (gaussBranchC z) / (z - 1) -
    fareySeries a b z - fareySeries a b (z + 1) with hΦ
  have hΦd : DifferentiableOn ℂ Φ U₁ := by
    have hS := differentiableOn_gaussTransferSeries a b
    refine ((((hS.comp (differentiableOn_id.add_const 1) hshift).add
      ((hS.comp differentiableOn_gaussBranchC mapsTo_gaussBranchC).div
        (differentiableOn_id.sub_const 1) fun z hz => sub_one_ne_zero_of_one_lt_re hz)).sub
      ((differentiableOn_fareySeries a b).mono hU₁sub)).sub
      ((differentiableOn_fareySeries a b).comp (differentiableOn_id.add_const 1) hshift'))
  have hΦzero := eqOn_zero_of_real_interval (hΦd.analyticOnNhd hU₁o)
    (convex_halfSpace_re_gt 1).isPreconnected hm2
    (by show 1 < (((2 + m) / 2 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith)
    fun x hx1 hx2 => by simp only [hΦ]; exact hI x hx1 hx2
  -- `S(v) = −S(2 + 1/v)/v`, hence `S = 0`
  have hSrec : ∀ v : ℝ, 2 < v → S v = -(S ((2 + 1 / v : ℝ) : ℂ) / v) := by
    intro v hv
    have hv' : 2 < (v : ℂ).re := by rw [Complex.ofReal_re]; exact hv
    have hv1 : 2 < ((v : ℂ) + 1).re := by simp; linarith
    have hΦv := hΦzero (show (v : ℂ) ∈ U₁ by show 1 < (v : ℂ).re; linarith)
    simp only [hΦ, Pi.zero_apply] at hΦv
    have e1 := gaussTransferSeries_add_div a b hv'
    have e2 := gaussTransferSeries_add_div a b hv1
    rw [← hS] at e1 e2
    have hτ : gaussBranchC ((v : ℂ) + 1) = ((2 + 1 / v : ℝ) : ℂ) := by
      unfold gaussBranchC; push_cast; ring
    rw [hτ, show (v : ℂ) + 1 - 1 = v by ring] at e2
    have hv0 : (v : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    linear_combination e2 - hΦv + e1
  have hSzero : ∀ v : ℝ, 2 < v → v ≤ 5 / 2 → S v = 0 := by
    have hK := eq_zero_of_halving (f := fun v : ℝ => ‖S v‖) (K := Ioc 2 (5 / 2)) (B := CS)
      (fun v hv => by
        rw [abs_of_nonneg (norm_nonneg _)]
        exact hCS _ (by rw [Complex.ofReal_re]; exact hv.1))
      (fun v hv => by
        right
        refine ⟨2 + 1 / v, ⟨?_, ?_⟩, ?_⟩
        · have : 0 < 1 / v := one_div_pos.mpr (by linarith [hv.1])
          linarith
        · have : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv.1.le
          linarith
        · rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _), hSrec v hv.1,
            norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith [hv.1])]
          exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hv.1.le)
    intro v hv1 hv2
    exact norm_eq_zero.mp (hK v ⟨hv1, hv2⟩)
  have hU₂o : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hS0 := eqOn_zero_of_real_interval
    ((differentiableOn_gaussTransferSeries a b).analyticOnNhd hU₂o)
    (convex_halfSpace_re_gt 2).isPreconnected (show (2 : ℝ) < 5 / 2 by norm_num)
    (by show 2 < (((2 + 5 / 2) / 2 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; norm_num)
    fun x hx1 hx2 => hSzero x hx1 hx2.le
  have hSall : ∀ z : ℂ, 2 < z.re → S z = 0 := fun z hz => by
    have := hS0 (show z ∈ {z : ℂ | 2 < z.re} from hz); simpa using this
  -- `F = 0`
  have hF3 : ∀ w : ℝ, 3 < w → F w = 0 := by
    intro w hw
    have hw' : 2 < ((w - 1 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
    have hΦv := hΦzero (show ((w - 1 : ℝ) : ℂ) ∈ U₁ by
      show 1 < ((w - 1 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith)
    simp only [hΦ, Pi.zero_apply] at hΦv
    have e1 := gaussTransferSeries_add_div a b hw'
    rw [← hS] at e1
    have h1 : S (((w - 1 : ℝ) : ℂ) + 1) = 0 := hSall _ (by simp; linarith)
    have h2 : S ((w - 1 : ℝ) : ℂ) = 0 := hSall _ hw'
    have hFw : fareySeries a b (((w - 1 : ℝ) : ℂ) + 1) = 0 := by
      linear_combination -hΦv + e1 + h1 - h2
    rw [show ((w - 1 : ℝ) : ℂ) + 1 = (w : ℂ) by push_cast; ring, fareySeries_ofReal, ← hF] at hFw
    exact_mod_cast hFw
  have hab : a = 0 ∧ b = 0 := by
    have e4 := fareySeriesR_add_one a b (v := 4) (by norm_num)
    have e6 := fareySeriesR_add_one a b (v := 6) (by norm_num)
    rw [← hF, hF3 4 (by norm_num), hF3 (4 + 1) (by norm_num)] at e4
    rw [← hF, hF3 6 (by norm_num), hF3 (6 + 1) (by norm_num)] at e6
    have c4 : Real.cos (2 * π / 4) = 0 := by
      rw [show 2 * π / 4 = π / 2 by ring, Real.cos_pi_div_two]
    have c6 : Real.cos (2 * π / 6) = 1 / 2 := by
      rw [show 2 * π / 6 = π / 3 by ring, Real.cos_pi_div_three]
    rw [c4] at e4
    rw [c6] at e6
    have e4' : a + b * (0 - 1) = 0 := by
      have := e4; rw [add_zero, eq_comm, div_eq_zero_iff] at this
      exact this.resolve_right (by norm_num)
    have e6' : a + b * (1 / 2 - 1) = 0 := by
      have := e6; rw [add_zero, eq_comm, div_eq_zero_iff] at this
      exact this.resolve_right (by norm_num)
    exact ⟨by linarith only [e4', e6'], by linarith only [e4', e6']⟩
  exact hab

/-- **The homogeneous window.**  Let `2 < w₂ ≤ p < q`, `v* = p + 1 < 4`, `3 ≤ q`, with
`τ(q) = p`, `τ(v*) = w₂`, `p ≤ τ(p)` and `τ(w₂) ≤ q`.  If a bounded `H` solves the homogeneous
Gauss–Farey equation on `[2, ∞)` and vanishes on `[p, q]` and on `[v*, ∞)`, then `H = 0` on
`[w₂, v*]`: each value is zero or at most half of a value at `τv` or `τ(v + 1)` in the window. -/
theorem eq_zero_on_gaussWindow_of_halving {H : ℝ → ℝ} {w₂ p q vs B : ℝ} (hw₂2 : 2 < w₂)
    (hw₂p : w₂ ≤ p) (hvs : vs = p + 1) (hvs4 : vs < 4) (hq3 : 3 ≤ q)
    (hB : ∀ v, 1 ≤ v → |H v| ≤ B)
    (hgf0 : ∀ v, 2 ≤ v → H v + H (v + 1) + H (gaussBranch v) / (v - 1) = 0)
    (hHpq : ∀ v, p ≤ v → v ≤ q → H v = 0) (hHbig : ∀ v, vs ≤ v → H v = 0)
    (hτq : gaussBranch q = p) (hτvs : gaussBranch vs = w₂) (hpτp : p ≤ gaussBranch p)
    (hτw₂ : gaussBranch w₂ ≤ q) : ∀ v ∈ Icc w₂ vs, H v = 0 := by
  refine eq_zero_of_halving (B := B) (fun v hv => hB v (by linarith [hv.1])) (fun v hv => ?_)
  obtain ⟨hv1, hv2⟩ := hv
  rcases lt_or_ge v p with hvp | hvp
  · -- `w₂ ≤ v < p`: `τv ∈ [p, q]`, so `H(v) = −H(v + 1)`
    have hτv1 : p ≤ gaussBranch v := hpτp.trans (gaussBranch_le_gaussBranch (by linarith) hvp.le)
    have hτv2 : gaussBranch v ≤ q := (gaussBranch_le_gaussBranch (by linarith) hv1).trans hτw₂
    have e := hgf0 v (by linarith)
    rw [hHpq _ hτv1 hτv2, zero_div, add_zero] at e
    rcases le_or_gt (v + 1) q with hq1 | hq1
    · left
      rw [hHpq (v + 1) (by linarith) hq1] at e
      linarith
    · right
      have e1 := hgf0 (v + 1) (by linarith)
      rw [hHbig (v + 1 + 1) (by linarith), add_zero, show v + 1 - 1 = v by ring] at e1
      refine ⟨gaussBranch (v + 1), ⟨?_, ?_⟩, ?_⟩
      · rw [← hτvs]; exact gaussBranch_le_gaussBranch (by linarith) (by linarith)
      · have := gaussBranch_le_gaussBranch (x := q) (y := v + 1) (by linarith) hq1.le
        rw [hτq] at this; linarith
      · have hv0 : 0 < v := by linarith
        have hHv : H v = H (gaussBranch (v + 1)) / v := by linarith
        rw [hHv, abs_div, abs_of_pos hv0]
        exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by linarith)
  rcases le_or_gt v q with hvq | hvq
  · left; exact hHpq v hvp hvq
  · -- `q < v ≤ v*`: `H(v) = −H(τv)/(v − 1)` with `τv ∈ [w₂, p]`
    right
    have e := hgf0 v (by linarith)
    rw [hHbig (v + 1) (by linarith), add_zero] at e
    refine ⟨gaussBranch v, ⟨?_, ?_⟩, ?_⟩
    · rw [← hτvs]; exact gaussBranch_le_gaussBranch (by linarith) hv2
    · have := gaussBranch_le_gaussBranch (x := q) (y := v) (by linarith) hvq.le
      rw [hτq] at this; linarith
    · have hHv : H v = -(H (gaussBranch v) / (v - 1)) := by linarith
      rw [hHv, abs_neg, abs_div, abs_of_pos (show (0 : ℝ) < v - 1 by linarith)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by linarith)

/-- **Inversion-symmetric Fourier-blind functions of support ratio below `12/7` vanish.** -/
theorem eq_zero_of_inversionSymmetric_fourierBlind_of_twelve_sevenths {G : ℝ → ℝ}
    (hG : Continuous G) (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x)
    {c : ℝ} (hc : 7 < 12 * c) (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) (y : ℝ) : G y = 0 := by
  rcases lt_or_ge ((1 - c) ^ 2) (2 * c - 1) with hs | hs
  · exact eq_zero_of_inversionSymmetric_fourierBlind_of_sqrt_two hG heven hinv hs hsupp hblind y
  rcases le_or_gt 1 c with hc1 | hc1
  · exact eq_zero_of_inversionSymmetric_of_zero_on_Ico hG heven hinv
      (fun x hx hx1 => hsupp x hx (lt_of_lt_of_le hx1 hc1)) y
  have hhalf : 1 / 2 < c := by linarith
  have hc0 : 0 < c := by linarith
  have hc35 : c < 3 / 5 := by nlinarith
  have hsupp' := inversionSymmetric_eq_zero_of_le hG hc0 hsupp
  set a₀ := (𝓕 (fun x => (G x : ℂ)) 0).re with ha₀
  set a₁ := (𝓕 (fun x => (G x : ℂ)) 1).re with ha₁
  set a := a₀ + 2 * a₁ with ha
  set b := 2 * a₁ with hb
  set F := fareySeriesR a b with hF
  set H : ℝ → ℝ := fun v => G (1 - 1 / v) / v with hH
  have h2c : 0 < 2 * c - 1 := by linarith
  have h1c : 0 < 1 - c := by linarith
  set vs := c / (2 * c - 1) with hvs
  have hvs3 : 3 < vs := by rw [hvs, lt_div_iff₀ h2c]; linarith
  have hvs72 : vs < 7 / 2 := by rw [hvs, div_lt_iff₀ h2c]; linarith
  set w₂ := 1 / (1 - c) with hw₂
  have hw₂2 : 2 < w₂ := by rw [hw₂, lt_div_iff₀ h1c]; linarith
  have hvs1 : vs - 1 = (1 - c) / (2 * c - 1) := by
    rw [hvs, eq_div_iff h2c.ne', sub_mul, div_mul_cancel₀ _ h2c.ne']; ring
  have hw₂p : w₂ ≤ vs - 1 := by
    rw [hvs1, hw₂, div_le_div_iff₀ h1c h2c]
    nlinarith
  -- the window `[p, q]`
  set p := vs - 1 with hp
  set q := 1 + 1 / (vs - 3) with hq
  have hA : 0 < vs - 3 := by linarith
  have hq3 : 3 ≤ q := by
    have : 2 ≤ 1 / (vs - 3) := by rw [le_div_iff₀ hA]; linarith
    rw [hq]; linarith
  have hp2 : 2 < p := by rw [hp]; linarith
  have hτq : gaussBranch q = p := by
    unfold gaussBranch
    rw [hq, show 1 + 1 / (vs - 3) - 1 = 1 / (vs - 3) by ring, one_div_one_div, hp]
    ring
  have hτp : gaussBranch p ≤ q := by
    unfold gaussBranch
    rw [hp, hq, show vs - 1 - 1 = vs - 2 by ring]
    have hB0 : 0 < vs - 2 := by linarith
    have h1 : 1 / (vs - 3) - 1 / (vs - 2) = 1 / ((vs - 3) * (vs - 2)) := by
      field_simp; ring
    have h2 : 1 ≤ 1 / ((vs - 3) * (vs - 2)) := by
      rw [le_div_iff₀ (mul_pos hA hB0)]; nlinarith
    linarith
  have hpτp : p ≤ gaussBranch p := by
    unfold gaussBranch
    rw [hp, show vs - 1 - 1 = vs - 2 by ring]
    have hB0 : 0 < vs - 2 := by linarith
    have : vs - 3 ≤ 1 / (vs - 2) := by rw [le_div_iff₀ hB0]; nlinarith
    linarith
  have hτvs : gaussBranch vs = w₂ := by
    unfold gaussBranch
    rw [show vs - 1 = (1 - c) / (2 * c - 1) from hvs1, one_div_div, hw₂]
    rw [eq_div_iff h1c.ne', add_mul, div_mul_cancel₀ _ h1c.ne']
    ring
  have hτw₂ : gaussBranch w₂ ≤ q := by
    have e : gaussBranch w₂ = 1 + 1 / c := by
      unfold gaussBranch
      rw [hw₂, show 1 / (1 - c) - 1 = c / (1 - c) by
        rw [eq_div_iff h1c.ne', sub_mul, div_mul_cancel₀ _ h1c.ne']; ring, one_div_div]
      rw [eq_comm, ← sub_eq_zero]
      field_simp
      ring
    rw [e, hq]
    have hvc : vs - 3 ≤ c := by
      rw [hvs, div_sub' h2c.ne', div_le_iff₀ h2c]
      nlinarith
    have : 1 / c ≤ 1 / (vs - 3) := one_div_le_one_div_of_le hA hvc
    linarith
  have hτmaps : ∀ v, p ≤ v → v ≤ q → p ≤ gaussBranch v ∧ gaussBranch v ≤ q := fun v h1 h2 =>
    ⟨hτq ▸ gaussBranch_le_gaussBranch (by linarith) h2,
      (gaussBranch_le_gaussBranch (by linarith) h1).trans hτp⟩
  -- profile, support and the Gauss–Farey equation
  have hHF : ∀ v, vs ≤ v → H v = F v := fun v hv =>
    inversionSymmetric_profile_eq_fareySeriesR hG heven hinv hhalf hsupp hblind
      (max_le (by linarith) hv)
  have hHzero : ∀ v, 2 ≤ v → v ≤ w₂ → H v = 0 := by
    intro v hv2 hvw
    have hv0 : 0 < v := by linarith
    have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
    have hle : 1 - 1 / v ≤ c := by
      rw [hw₂, le_div_iff₀ h1c] at hvw
      rw [show 1 - 1 / v = (v - 1) / v by field_simp, div_le_iff₀ hv0]
      linarith
    simp only [hH]
    rw [hsupp' _ (by linarith) hle, zero_div]
  have hgf : ∀ v, 2 ≤ v →
      H v + H (v + 1) + H (gaussBranch v) / (v - 1) = F v + F (v + 1) := by
    intro v hv2
    have e : H v + H (v + 1) + H (gaussBranch v) / (v - 1) =
        (a₀ + 2 * a₁ * Real.cos (2 * π / v)) / v :=
      inversionSymmetric_gauss_farey_equation hG heven hinv hhalf hsupp hblind hv2
    rw [e, fareySeriesR_add_one a b (by linarith)]
    rw [ha, hb]; ring
  -- `H` is the transfer series on the window
  set S := gaussTransferSeries a b with hS
  obtain ⟨CS, hCS⟩ := exists_norm_gaussTransferSeries_le a b
  obtain ⟨CG, hCG⟩ : ∃ C, ∀ r, |G r| ≤ C := by
    obtain ⟨C, hC⟩ := (hasCompactSupport_of_inversionSymmetric hG heven hinv hc0
      hsupp).exists_bound_of_continuous hG
    exact ⟨C, fun r => by rw [← Real.norm_eq_abs]; exact hC r⟩
  have hHb : ∀ v, 1 ≤ v → |H v| ≤ CG := by
    intro v hv
    have hv0 : 0 < v := by linarith
    simp only [hH]
    rw [abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
    have := hCG (1 - 1 / v)
    nlinarith [abs_nonneg (G (1 - 1 / v))]
  have hSeq : ∀ v, p ≤ v → v ≤ q → ((H v : ℝ) : ℂ) = S v := by
    refine eq_of_gaussWindow_equation hp2 hτmaps (fun v h1 h2 => ?_) ?_
    · have hv2 : 2 < (v : ℂ).re := by rw [Complex.ofReal_re]; linarith
      have eS := gaussTransferSeries_add_div a b hv2
      rw [gaussBranchC_ofReal] at eS
      have e := hgf v (by linarith)
      rw [hHF (v + 1) (by linarith)] at e
      rw [eS, fareySeries_ofReal, ← hF]
      have e' : H v + H (gaussBranch v) / (v - 1) = F v := by linarith
      rw [← e']
      push_cast
      ring
    · refine ⟨CG + CS, fun v h1 _ => ?_⟩
      calc ‖((H v : ℝ) : ℂ) - S v‖ ≤ ‖((H v : ℝ) : ℂ)‖ + ‖S v‖ := norm_sub_le _ _
        _ ≤ CG + CS := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add (hHb v (by linarith)) (hCS _ (by rw [Complex.ofReal_re]; linarith))
  -- the identity `S(x + 1) + S(τx)/(x − 1) = F(x) + F(x + 1)` on an interval
  set m := min w₂ (1 / (vs - 3)) with hm
  have hm2 : 2 < m := by
    rw [hm, lt_min_iff]
    exact ⟨hw₂2, by rw [lt_div_iff₀ hA]; linarith⟩
  have hab := eq_zero_of_gaussTransferSeries_shift_identity a b hm2 fun x hx1 hx2 => by
    have hxw : x ≤ w₂ := hx2.le.trans (min_le_left _ _)
    have hxA : x ≤ 1 / (vs - 3) := hx2.le.trans (min_le_right _ _)
    have hx1p : p ≤ x + 1 := by rw [hp]; linarith
    have hx1q : x + 1 ≤ q := by rw [hq]; linarith
    have hτx1 : p ≤ gaussBranch x :=
      hτq ▸ gaussBranch_le_gaussBranch (by linarith) (by rw [hq]; linarith)
    have hτx2 : gaussBranch x ≤ q := by
      have h3 : gaussBranch x ≤ gaussBranch 2 := gaussBranch_le_gaussBranch (by norm_num) hx1.le
      have h4 : gaussBranch 2 = 3 := by unfold gaussBranch; norm_num
      linarith
    have e := hgf x hx1.le
    rw [hHzero x hx1.le hxw, zero_add] at e
    rw [← hS, gaussBranchC_ofReal, show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
      ← hSeq _ hx1p hx1q, ← hSeq _ hτx1 hτx2, fareySeries_ofReal, fareySeries_ofReal, ← hF]
    have e' : (((H (x + 1) + H (gaussBranch x) / (x - 1) - F x - F (x + 1) : ℝ)) : ℂ) = 0 := by
      rw [show H (x + 1) + H (gaussBranch x) / (x - 1) - F x - F (x + 1) = 0 by linarith]
      simp
    rw [← e']
    push_cast
    ring
  have hFall : ∀ w, F w = 0 := fun w => by
    show fareySeriesR a b w = 0
    unfold fareySeriesR
    rw [hab.1, hab.2]
    ring
  -- `H = 0` on `[p, q]`, then on `[w₂, vs]` by halving
  have hHpq : ∀ v, p ≤ v → v ≤ q → H v = 0 := by
    intro v h1 h2
    have := hSeq v h1 h2
    rw [hS, hab.1, hab.2, gaussTransferSeries_zero] at this
    exact_mod_cast this
  have hgf0 : ∀ v, 2 ≤ v → H v + H (v + 1) + H (gaussBranch v) / (v - 1) = 0 := by
    intro v hv; rw [hgf v hv, hFall, hFall, add_zero]
  have hHbig : ∀ v, vs ≤ v → H v = 0 := fun v hv => by rw [hHF v hv, hFall]
  have hwin : ∀ v ∈ Icc w₂ vs, H v = 0 :=
    eq_zero_on_gaussWindow_of_halving hw₂2 hw₂p (by rw [hp]; ring) (by linarith) hq3 hHb hgf0 hHpq
      hHbig hτq hτvs hpτp hτw₂
  have hHall : ∀ v, 2 ≤ v → H v = 0 := by
    intro v hv
    rcases le_or_gt v w₂ with h | h
    · exact hHzero v hv h
    rcases le_or_gt v vs with h' | h'
    · exact hwin v ⟨h.le, h'⟩
    · exact hHbig v h'.le
  refine eq_zero_of_inversionSymmetric_of_profile_zero hG heven hinv
    (fun x hx hx2 => hsupp x hx (by linarith)) (fun v hv => ?_) y
  have h := hHall v hv
  simp only [hH] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by linarith)

end

end RHTower
