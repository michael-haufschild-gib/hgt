import GaloisForLFunctions.RHTower.WeilLogPeriodicLockRigidity
import GaloisForLFunctions.RHTower.WeilLowerRegionContour

/-!
# Regularly varying lock phases are impossible

Let `G` be a Herglotz producer and `L` holomorphic on `Re s > ½`, continuous on `Re s ≥ ½`, with
`Re L ≤ A` on the lower strip `½ ≤ Re s ≤ 3/2`, `Im s ≤ −1`, and on the lower critical line.
Suppose that on the edge `Re s = 3/2`, as `y → −∞`,

`|y| · Re L'(3/2 + iy) → −∞`  and  `L''(3/2 + iy) / (Re L'(3/2 + iy))² → 0`.

**Theorem** (`regular_twist_lock_impossible`).  No Herglotz producer satisfies the lower-line lock
`G(1 − s) = κ₀ e^{L(s)} G(s)`, `s = ½ + 2iτ`, `τ < 0`, not even on super-polynomially long windows
(`windowed_regular_twist_lock_impossible`).

For a lock phase `θ` with holomorphic extension (`L' = −Θ'/2`) the hypotheses say: the spectral
density `ρ = θ'/2π` satisfies `xρ(x) → ∞` and varies regularly, `ρ'/ρ² → 0`.  The density may tend
to `0` (for instance `ρ = 1/log x`, non-integer mass `x/log x`), stay bounded or oscillate, or grow.
This contains the margin theorem (`margin_twist_lock_impossible`) and fills the gap between it and
the power-growth theorems (`abelian_twist_power_rigidity`, mass `O(x^α)`, `α < 1`): every regularly
varying, holomorphically extendable non-integer spectral mass that is not `O(log x)` is impossible.

**Proof.**  As in the margin theorem, the twisted right edge splits into Dirichlet terms whose
leading parts are `∫_{y ≤ −Y} e^{h}`, `h(y) = L(3/2 + iy) + y(κ_τ − i log n)`, with
`Im h' = Re L' + log‖τ‖ − log n`.  Since `log‖ε + i‖ ≤ ε²/2`, on `−ε^{−2} ≤ y ≤ −Y` the density
condition gives `|Re L'| ≥ ε² ≥ 2 log‖τ‖`, so `|h'| ≥ |Re L'|/2` for every `n ≥ 1`.  Integration by
parts on this interval (`norm_intervalIntegral_exp_le`) costs `4η'/δ` from `|h''|/|h'|² ≤ 4η'`, and the
two boundary terms; below `−ε^{−2}` the trivial bound costs `e^{−1/(2ε)}`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### Integration by parts on a bounded edge interval -/

/-- **Integration by parts on `[a, B]`.**  With `h(y) = L(3/2 + iy) + y w` and `g = h'`,
`‖∫_a^B e^{h}‖ ≤ ‖e^{h(B)}‖/‖g(B)‖ + ‖e^{h(a)}‖/‖g(a)‖ + ∫_a^B ‖e^{h}‖ ‖L''‖/‖g‖²`. -/
theorem norm_intervalIntegral_exp_le {L L1 L2 : ℂ → ℂ} {w : ℂ} {a B : ℝ} (hab : a ≤ B)
    (h1 : ∀ y ∈ Icc a B, HasDerivAt L (L1 (edgePt y)) (edgePt y))
    (h2 : ∀ y ∈ Icc a B, HasDerivAt L1 (L2 (edgePt y)) (edgePt y))
    (hc2 : ∀ y ∈ Icc a B, ContinuousAt L2 (edgePt y))
    (hg0 : ∀ y ∈ Icc a B, I * L1 (edgePt y) + w ≠ 0) :
    ‖∫ y in a..B, cexp (L (edgePt y) + (y : ℂ) * w)‖ ≤
      ‖cexp (L (edgePt B) + (B : ℂ) * w)‖ / ‖I * L1 (edgePt B) + w‖ +
      ‖cexp (L (edgePt a) + (a : ℂ) * w)‖ / ‖I * L1 (edgePt a) + w‖ +
      ∫ y in a..B, ‖cexp (L (edgePt y) + (y : ℂ) * w)‖ * ‖L2 (edgePt y)‖ /
        ‖I * L1 (edgePt y) + w‖ ^ 2 := by
  set hf : ℝ → ℂ := fun y => L (edgePt y) + (y : ℂ) * w with hhf
  set gf : ℝ → ℂ := fun y => I * L1 (edgePt y) + w with hgf
  set Wf : ℝ → ℂ := fun y => cexp (hf y) * L2 (edgePt y) / gf y ^ 2 with hWf
  set Uf : ℝ → ℂ := fun y => cexp (hf y) / gf y with hUf
  have hhd : ∀ y ∈ Icc a B, HasDerivAt hf (gf y) y := by
    intro y hy
    have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * w) w y := by
      simpa using ((hasDerivAt_id (y : ℂ)).comp_ofReal).mul_const w
    have h := ((h1 y hy).comp y (hasDerivAt_edgePt y)).add hlin
    refine h.congr_deriv ?_
    simp only [hgf]; ring
  have hgd : ∀ y ∈ Icc a B, HasDerivAt gf (-(L2 (edgePt y))) y := by
    intro y hy
    have h := (((h2 y hy).comp y (hasDerivAt_edgePt y)).const_mul I).add_const w
    refine h.congr_deriv ?_
    rw [mul_comm (L2 (edgePt y)) I, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hUd : ∀ y ∈ Icc a B, HasDerivAt Uf (cexp (hf y) + Wf y) y := by
    intro y hy
    have h := ((hhd y hy).cexp).div (hgd y hy) (hg0 y hy)
    refine h.congr_deriv ?_
    simp only [hWf]
    have hg : gf y ≠ 0 := hg0 y hy
    field_simp
    ring
  have hcont_h : ContinuousOn (fun y => cexp (hf y)) (Icc a B) := fun y hy =>
    ((hhd y hy).cexp).continuousAt.continuousWithinAt
  have hcont_g : ContinuousOn gf (Icc a B) := fun y hy =>
    (hgd y hy).continuousAt.continuousWithinAt
  have hcont_L2 : ContinuousOn (fun y => L2 (edgePt y)) (Icc a B) := fun y hy =>
    ((hc2 y hy).comp continuous_edgePt.continuousAt).continuousWithinAt
  have hcont_W : ContinuousOn Wf (Icc a B) :=
    (hcont_h.mul hcont_L2).div (hcont_g.pow 2) fun y hy => pow_ne_zero 2 (hg0 y hy)
  have hu : uIcc a B = Icc a B := uIcc_of_le hab
  have hint_h : IntervalIntegrable (fun y => cexp (hf y)) volume a B :=
    ContinuousOn.intervalIntegrable (by rw [hu]; exact hcont_h)
  have hint_W : IntervalIntegrable Wf volume a B :=
    ContinuousOn.intervalIntegrable (by rw [hu]; exact hcont_W)
  have hFTC : ∫ y in a..B, (cexp (hf y) + Wf y) = Uf B - Uf a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hUd y (by rw [hu] at hy; exact hy))
      (hint_h.add hint_W)
  have hsplit : ∫ y in a..B, cexp (hf y) = (Uf B - Uf a) - ∫ y in a..B, Wf y := by
    have h' := intervalIntegral.integral_add hint_h hint_W
    rw [hFTC] at h'
    rw [h']; ring
  have hgoal : ∫ y in a..B, cexp (L (edgePt y) + (y : ℂ) * w) = ∫ y in a..B, cexp (hf y) := rfl
  rw [hgoal, hsplit]
  have hWn : ‖∫ y in a..B, Wf y‖ ≤ ∫ y in a..B, ‖cexp (L (edgePt y) + (y : ℂ) * w)‖ *
      ‖L2 (edgePt y)‖ / ‖I * L1 (edgePt y) + w‖ ^ 2 := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [hWf, hhf, hgf, norm_div, norm_mul, norm_pow]
  calc ‖(Uf B - Uf a) - ∫ y in a..B, Wf y‖ ≤ ‖Uf B‖ + ‖Uf a‖ + ‖∫ y in a..B, Wf y‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ _ := by
        simp only [hUf, hhf, hgf, norm_div]
        gcongr

theorem exp_neg_inv_two_mul_le {ε : ℝ} (hε : 0 < ε) : Real.exp (-(1 / (2 * ε))) ≤ 8 * ε ^ 2 := by
  have hx : 0 ≤ 1 / (2 * ε) := by positivity
  have h := Real.quadratic_le_exp_of_nonneg hx
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
  have h2 : 1 / (8 * ε ^ 2) ≤ Real.exp (1 / (2 * ε)) := by
    have e : 1 / (8 * ε ^ 2) = (1 / (2 * ε)) ^ 2 / 2 := by field_simp; ring
    rw [e]; nlinarith
  exact le_of_eq_of_le (by rw [one_div]) h2

/-! ### The leading integral -/

/-- **The leading integral under regular variation.**  If on `[a, B]` the frequency satisfies
`‖h'‖ ≥ |Re L'|/2` and `‖L''‖ ≤ η' (Re L')²`, then
`‖∫_{y ≤ B} e^{h}‖ ≤ e^{A}e^{κa}/κ + 2e^{A}e^{κB}/μ_B + 2e^{A}e^{κa}/μ_a + 4η'e^{A}e^{κB}/κ`. -/
theorem norm_lead_le_of_regular {L L1 L2 : ℂ → ℂ} {w : ℂ} (hw : 0 < w.re)
    {a B A η' μa μB : ℝ} (hab : a ≤ B) (hμa : 0 < μa) (hμB : 0 < μB) (hη' : 0 ≤ η')
    (hLc : ∀ y : ℝ, y ≤ B → ContinuousAt L (edgePt y))
    (h1 : ∀ y ∈ Icc a B, HasDerivAt L (L1 (edgePt y)) (edgePt y))
    (h2 : ∀ y ∈ Icc a B, HasDerivAt L1 (L2 (edgePt y)) (edgePt y))
    (hc2 : ∀ y ∈ Icc a B, ContinuousAt L2 (edgePt y))
    (hA : ∀ y : ℝ, y ≤ B → (L (edgePt y)).re ≤ A)
    (hpos : ∀ y ∈ Icc a B, 0 < -(L1 (edgePt y)).re)
    (hg : ∀ y ∈ Icc a B, -(L1 (edgePt y)).re / 2 ≤ ‖I * L1 (edgePt y) + w‖)
    (hrat : ∀ y ∈ Icc a B, ‖L2 (edgePt y)‖ ≤ η' * (L1 (edgePt y)).re ^ 2)
    (hma : μa ≤ -(L1 (edgePt a)).re) (hmB : μB ≤ -(L1 (edgePt B)).re) :
    ‖∫ y in Iic B, cexp (L (edgePt y) + (y : ℂ) * w)‖ ≤
      Real.exp A * Real.exp (w.re * a) / w.re + 2 * Real.exp A * Real.exp (w.re * B) / μB +
        2 * Real.exp A * Real.exp (w.re * a) / μa +
          4 * η' * Real.exp A * Real.exp (w.re * B) / w.re := by
  have heA := Real.exp_pos A
  set f : ℝ → ℂ := fun y => cexp (L (edgePt y) + (y : ℂ) * w) with hf
  have hexp_le : ∀ y : ℝ, y ≤ B → ‖f y‖ ≤ Real.exp A * Real.exp (w.re * y) := by
    intro y hy
    simp only [hf]
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : (L (edgePt y) + (y : ℂ) * w).re = (L (edgePt y)).re + w.re * y := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    rw [this]; linarith [hA y hy]
  have hexpInt : ∀ c : ℝ, IntegrableOn (fun y : ℝ => Real.exp (w.re * y)) (Iic c) := by
    intro c
    have h : IntegrableOn (fun y : ℝ => ‖cexp ((w.re : ℂ) * (y : ℂ))‖) (Iic c) :=
      (integrableOn_exp_mul_complex_Iic (a := (w.re : ℂ)) (by simpa using hw) c).norm
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [Complex.norm_exp]
    congr 1; simp
  have hfc : ContinuousOn f (Iic B) := fun y hy =>
    (Complex.continuous_exp.continuousAt.comp (((hLc y hy).comp continuous_edgePt.continuousAt).add
      (by fun_prop : Continuous fun y : ℝ => (y : ℂ) * w).continuousAt)).continuousWithinAt
  have hfint : IntegrableOn f (Iic B) :=
    ((hexpInt B).const_mul (Real.exp A)).mono' (hfc.aestronglyMeasurable measurableSet_Iic)
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => hexp_le y hy))
  have hfint_a : IntegrableOn f (Iic a) := hfint.mono_set (Iic_subset_Iic.mpr hab)
  have hsplit : ∫ y in Iic B, f y = (∫ y in Iic a, f y) + ∫ y in a..B, f y := by
    rw [← intervalIntegral.integral_Iic_sub_Iic hfint_a hfint]; ring
  have hgoal : ∫ y in Iic B, cexp (L (edgePt y) + (y : ℂ) * w) = ∫ y in Iic B, f y := rfl
  rw [hgoal, hsplit]
  refine (norm_add_le _ _).trans ?_
  -- the tail below `a`
  have htail : ‖∫ y in Iic a, f y‖ ≤ Real.exp A * Real.exp (w.re * a) / w.re := by
    refine (norm_integral_le_of_norm_le ((hexpInt a).const_mul (Real.exp A))
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy =>
        hexp_le y (le_trans hy hab)))).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_exp_mul_Iic_real hw]; ring
  -- the interval `[a, B]` by parts
  have hg0 : ∀ y ∈ Icc a B, I * L1 (edgePt y) + w ≠ 0 := by
    intro y hy h
    have := hg y hy
    rw [h, norm_zero] at this
    linarith [hpos y hy]
  have hIBP := norm_intervalIntegral_exp_le hab h1 h2 hc2 hg0
  have hB1 : ‖f B‖ / ‖I * L1 (edgePt B) + w‖ ≤ 2 * Real.exp A * Real.exp (w.re * B) / μB := by
    have hgB : μB / 2 ≤ ‖I * L1 (edgePt B) + w‖ :=
      le_trans (by linarith) (hg B ⟨hab, le_rfl⟩)
    rw [div_le_div_iff₀ (by linarith) hμB]
    have := hexp_le B le_rfl
    nlinarith [norm_nonneg (f B), Real.exp_pos (w.re * B)]
  have ha1 : ‖f a‖ / ‖I * L1 (edgePt a) + w‖ ≤ 2 * Real.exp A * Real.exp (w.re * a) / μa := by
    have hga : μa / 2 ≤ ‖I * L1 (edgePt a) + w‖ :=
      le_trans (by linarith) (hg a ⟨le_rfl, hab⟩)
    rw [div_le_div_iff₀ (by linarith) hμa]
    have := hexp_le a hab
    nlinarith [norm_nonneg (f a), Real.exp_pos (w.re * a)]
  have hmid : ∫ y in a..B, ‖f y‖ * ‖L2 (edgePt y)‖ / ‖I * L1 (edgePt y) + w‖ ^ 2 ≤
      4 * η' * Real.exp A * Real.exp (w.re * B) / w.re := by
    have hpt : ∀ y ∈ Icc a B, ‖f y‖ * ‖L2 (edgePt y)‖ / ‖I * L1 (edgePt y) + w‖ ^ 2 ≤
        4 * η' * Real.exp A * Real.exp (w.re * y) := by
      intro y hy
      have hp := hpos y hy
      have hgy := hg y hy
      have hgy2 : ((L1 (edgePt y)).re) ^ 2 / 4 ≤ ‖I * L1 (edgePt y) + w‖ ^ 2 := by
        have : (-(L1 (edgePt y)).re / 2) ^ 2 ≤ ‖I * L1 (edgePt y) + w‖ ^ 2 :=
          pow_le_pow_left₀ (by linarith) hgy 2
        nlinarith
      have hden : 0 < ‖I * L1 (edgePt y) + w‖ ^ 2 := by
        have : 0 < ‖I * L1 (edgePt y) + w‖ := lt_of_lt_of_le (by linarith) hgy
        positivity
      rw [div_le_iff₀ hden]
      have hfy := hexp_le y hy.2
      have hr := hrat y hy
      calc ‖f y‖ * ‖L2 (edgePt y)‖
          ≤ (Real.exp A * Real.exp (w.re * y)) * (η' * (L1 (edgePt y)).re ^ 2) :=
            mul_le_mul hfy hr (norm_nonneg _) (by positivity)
        _ = 4 * η' * Real.exp A * Real.exp (w.re * y) * (((L1 (edgePt y)).re) ^ 2 / 4) := by ring
        _ ≤ 4 * η' * Real.exp A * Real.exp (w.re * y) * ‖I * L1 (edgePt y) + w‖ ^ 2 := by
            gcongr
    have hcmp : ∫ y in a..B, ‖f y‖ * ‖L2 (edgePt y)‖ / ‖I * L1 (edgePt y) + w‖ ^ 2 ≤
        ∫ y in a..B, 4 * η' * Real.exp A * Real.exp (w.re * y) := by
      refine intervalIntegral.integral_mono_on hab ?_ ?_ hpt
      · have hgc : ContinuousOn (fun y => ‖I * L1 (edgePt y) + w‖ ^ 2) (Icc a B) := by
          intro y hy
          have hd : HasDerivAt (fun y : ℝ => I * L1 (edgePt y) + w) (I * (L2 (edgePt y) * I)) y :=
            (((h2 y hy).comp y (hasDerivAt_edgePt y)).const_mul I).add_const w
          exact hd.continuousAt.continuousWithinAt.norm.pow 2
        have hc : ContinuousOn (fun y => ‖f y‖ * ‖L2 (edgePt y)‖ /
            ‖I * L1 (edgePt y) + w‖ ^ 2) (Icc a B) :=
          ((hfc.mono (fun y hy => hy.2)).norm.mul (fun y hy =>
            ((hc2 y hy).comp continuous_edgePt.continuousAt).continuousWithinAt.norm)).div hgc
            (fun y hy => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hg0 y hy)))
        exact ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hab]; exact hc)
      · exact (by fun_prop : Continuous fun y : ℝ =>
          4 * η' * Real.exp A * Real.exp (w.re * y)).intervalIntegrable _ _
    refine hcmp.trans ?_
    have hI := intervalIntegral.integral_Iic_sub_Iic (μ := volume)
      (((hexpInt a).const_mul (4 * η' * Real.exp A)))
      (((hexpInt B).const_mul (4 * η' * Real.exp A)))
    rw [← hI, integral_const_mul, integral_const_mul, integral_exp_mul_Iic_real hw,
      integral_exp_mul_Iic_real hw]
    have h0 : 0 ≤ 4 * η' * Real.exp A * (Real.exp (w.re * a) / w.re) := by positivity
    have e : 4 * η' * Real.exp A * (Real.exp (w.re * B) / w.re) =
        4 * η' * Real.exp A * Real.exp (w.re * B) / w.re := by ring
    linarith
  have hIBP' : ‖∫ y in a..B, f y‖ ≤ 2 * Real.exp A * Real.exp (w.re * B) / μB +
      2 * Real.exp A * Real.exp (w.re * a) / μa +
        4 * η' * Real.exp A * Real.exp (w.re * B) / w.re := by
    refine hIBP.trans ?_
    linarith [hB1, ha1, hmid]
  linarith [htail, hIBP']

/-! ### One twisted term -/

theorem norm_expEdgeTerm_le_of_lead (a : ℕ → ℂ) {L : ℂ → ℂ} {τ : ℂ} (hτ : 0 < τ.re) {n : ℕ}
    (hn : 1 ≤ n) {B A X : ℝ} (hB : B ≤ -1)
    (hLc : ∀ y : ℝ, y ≤ B → ContinuousAt L (edgePt y))
    (hA : ∀ y : ℝ, y ≤ B → (L (edgePt y)).re ≤ A)
    (hlead : ‖∫ y in Iic B, cexp (L (edgePt y) +
      (y : ℂ) * (edgeExp τ - ((Real.log n : ℝ) : ℂ) * I))‖ ≤ X) :
    ‖expEdgeTerm a L τ B n‖ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ *
      (2 * ‖τ‖ ^ (1 / 2 : ℝ) * X +
        Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * B) / Real.pi))) := by
  have hpi := Real.pi_pos
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set T₀ : ℂ := LSeries.term a (((3 / 2 : ℝ) : ℂ)) n with hT₀
  set w : ℂ := edgeExp τ - ((Real.log n : ℝ) : ℂ) * I with hw
  have hwre : w.re = (edgeExp τ).re := by
    simp only [hw, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hwim : w.im = Real.log ‖τ‖ - Real.log n := by
    simp only [hw, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, edgeExp_im]
    ring
  have hκ : 0 < (edgeExp τ).re := by
    rw [edgeExp_re]
    have h := abs_arg_pi_mul_sq_le hτ
    have := le_abs_self ((Real.pi : ℂ) * τ ^ 2).arg
    have hδ : 0 < τ.re / ‖τ‖ := div_pos hτ hτn
    linarith
  set Rk : ℝ → ℂ := fun y => offKernel τ (edgePt y) - edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ)
    with hRk
  have hRk_le : ∀ y : ℝ, y ≤ B →
      ‖Rk y‖ ≤ 4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * y) := fun y hy =>
    norm_offKernel_three_halves_sub_le hτ (by linarith)
  have hsplit : ∀ y : ℝ, LSeries.term a (edgePt y) n * cexp (L (edgePt y)) *
      offKernel τ (edgePt y) =
      T₀ * edgeCoeff τ * cexp (L (edgePt y) + (y : ℂ) * w) +
        T₀ * (cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) * Rk y) := by
    intro y
    rw [term_edgePt_eq hn y]
    have hk : offKernel τ (edgePt y) = edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ) + Rk y := by
      simp only [hRk]; ring
    rw [hk]
    have he : cexp (L (edgePt y) + (y : ℂ) * w) =
        cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) *
          cexp ((y : ℂ) * edgeExp τ) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hw]; ring
    rw [he]; ring
  -- integrability of the two pieces
  have hcL : ∀ y : ℝ, y ≤ B → ContinuousAt (fun y : ℝ => L (edgePt y)) y := fun y hy =>
    (hLc y hy).comp continuous_edgePt.continuousAt
  have hRkc : Continuous Rk := by
    simp only [hRk]
    exact (continuous_offKernel_edgePt hτ0).sub (continuous_const.mul (by fun_prop))
  have hexpInt : IntegrableOn (fun y : ℝ => Real.exp ((edgeExp τ).re * y)) (Iic B) := by
    have h : IntegrableOn (fun y : ℝ => ‖cexp (((edgeExp τ).re : ℂ) * (y : ℂ))‖) (Iic B) :=
      (integrableOn_exp_mul_complex_Iic (a := ((edgeExp τ).re : ℂ)) (by simpa using hκ) B).norm
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [Complex.norm_exp]
    congr 1; simp
  have hpiInt : IntegrableOn (fun y : ℝ => Real.exp (Real.pi * y)) (Iic B) := by
    have h : IntegrableOn (fun y : ℝ => ‖cexp ((Real.pi : ℂ) * (y : ℂ))‖) (Iic B) :=
      (integrableOn_exp_mul_complex_Iic (a := (Real.pi : ℂ)) (by simpa using hpi) B).norm
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [Complex.norm_exp]
    congr 1; simp
  have hlead_le : ∀ y : ℝ, y ≤ B → ‖cexp (L (edgePt y) + (y : ℂ) * w)‖ ≤
      Real.exp A * Real.exp ((edgeExp τ).re * y) := by
    intro y hy
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : (L (edgePt y) + (y : ℂ) * w).re = (L (edgePt y)).re + (edgeExp τ).re * y := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, hwre]
      ring
    rw [this]; linarith [hA y hy]
  have hrest_le : ∀ y : ℝ, y ≤ B →
      ‖cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) * Rk y‖ ≤
        Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * y)) := by
    intro y hy
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h0 : (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))).re = 0 := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [h0, Real.exp_zero, one_mul]
    exact mul_le_mul (Real.exp_le_exp.mpr (hA y hy)) (hRk_le y hy) (norm_nonneg _)
      (Real.exp_pos _).le
  have hcont_lead : ContinuousOn (fun y : ℝ => cexp (L (edgePt y) + (y : ℂ) * w)) (Iic B) :=
    fun y hy => (Complex.continuous_exp.continuousAt.comp ((hcL y hy).add
      (by fun_prop : Continuous fun y : ℝ => (y : ℂ) * w).continuousAt)).continuousWithinAt
  have hcont_rest : ContinuousOn (fun y : ℝ =>
      cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) * Rk y) (Iic B) :=
    fun y hy => (((by fun_prop : Continuous fun y : ℝ =>
      cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I)))).continuousAt.mul
        (Complex.continuous_exp.continuousAt.comp (hcL y hy))).mul
          hRkc.continuousAt).continuousWithinAt
  have hint_lead : IntegrableOn (fun y : ℝ => cexp (L (edgePt y) + (y : ℂ) * w)) (Iic B) :=
    (hexpInt.const_mul (Real.exp A)).mono' (hcont_lead.aestronglyMeasurable measurableSet_Iic)
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => hlead_le y hy))
  have hint_rest : IntegrableOn (fun y : ℝ =>
      cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) * Rk y) (Iic B) :=
    ((hpiInt.const_mul (4 * ‖τ‖ ^ (1 / 2 : ℝ))).const_mul (Real.exp A)).mono'
      (hcont_rest.aestronglyMeasurable measurableSet_Iic)
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => by
        simpa [mul_assoc] using hrest_le y hy))
  have hIBP : ‖∫ y in Iic B, cexp (L (edgePt y) + (y : ℂ) * w)‖ ≤ X := hlead
  -- assemble
  unfold expEdgeTerm
  simp only [hsplit]
  rw [integral_add (hint_lead.const_mul _) (hint_rest.const_mul _), integral_const_mul,
    integral_const_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_edgeCoeff hτ0]
  have hrest_int : ‖∫ y in Iic B, cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) *
      cexp (L (edgePt y)) * Rk y‖ ≤
      Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * B) / Real.pi)) := by
    have hdom : IntegrableOn (fun y : ℝ => Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) *
        Real.exp (Real.pi * y))) (Iic B) :=
      (hpiInt.const_mul (4 * ‖τ‖ ^ (1 / 2 : ℝ))).const_mul (Real.exp A)
    refine (norm_integral_le_of_norm_le hdom ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall fun y hy => hrest_le y hy))).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_const_mul, integral_exp_mul_Iic_real hpi]
  have hT0 : 0 ≤ ‖T₀‖ := norm_nonneg _
  calc ‖T₀‖ * (2 * ‖τ‖ ^ (1 / 2 : ℝ)) *
        ‖∫ y in Iic B, cexp (L (edgePt y) + (y : ℂ) * w)‖ +
        ‖T₀‖ * ‖∫ y in Iic B, cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) *
          cexp (L (edgePt y)) * Rk y‖
      ≤ ‖T₀‖ * (2 * ‖τ‖ ^ (1 / 2 : ℝ)) * X +
        ‖T₀‖ * (Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * B) / Real.pi))) := by
        gcongr
    _ = _ := by ring


/-! ### One twisted term below the margin height -/

/-- **One twisted term under regular variation**, below the height `−Y`. -/
theorem norm_expEdgeTerm_le_regular (a : ℕ → ℂ) {L : ℂ → ℂ}
    (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hd1 : ∀ y : ℝ, y < 0 → HasDerivAt L (deriv L (edgePt y)) (edgePt y))
    (hd2 : ∀ y : ℝ, y < 0 → HasDerivAt (deriv L) (deriv (deriv L) (edgePt y)) (edgePt y))
    (hc2 : ∀ y : ℝ, y < 0 → ContinuousAt (deriv (deriv L)) (edgePt y)) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    {η' Y X : ℝ} (hη' : 0 < η') (hY2 : 2 ≤ Y) (hYX : Y ≤ X)
    (htail : ∀ y : ℝ, y ≤ -Y → 0 < -(deriv L (edgePt y)).re ∧
      ‖deriv (deriv L) (edgePt y)‖ ≤ η' * (deriv L (edgePt y)).re ^ 2 ∧
      1 ≤ |y| * -(deriv L (edgePt y)).re)
    {τ : ℂ} (hτre0 : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) (hτ2 : ‖τ‖ ≤ 2)
    (hτc : Real.log ‖τ‖ ≤ 1 / (2 * X)) (n : ℕ) :
    ‖expEdgeTerm a L τ (-Y) n‖ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ *
      (4 * (Real.exp A * (Real.exp (-(τ.re / ‖τ‖ * X)) / (τ.re / ‖τ‖) + 2 * Y +
        2 * X * Real.exp (-(τ.re / ‖τ‖ * X)) + 4 * η' / (τ.re / ‖τ‖))) +
        8 * Real.exp A / Real.pi) := by
  have hpi := Real.pi_pos
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
  have hτpos : 0 < ‖τ‖ := by linarith
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre0 hτpos
  have hκδ : δ ≤ (edgeExp τ).re := by
    rw [edgeExp_re]
    have h := abs_arg_pi_mul_sq_le hτre0
    have := le_abs_self ((Real.pi : ℂ) * τ ^ 2).arg
    linarith
  have hκ0 : 0 < (edgeExp τ).re := lt_of_lt_of_le hδ0 hκδ
  have hτh : ‖τ‖ ^ (1 / 2 : ℝ) ≤ 2 := by
    calc ‖τ‖ ^ (1 / 2 : ℝ) ≤ ‖τ‖ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hτ1 (by norm_num)
      _ = ‖τ‖ := Real.rpow_one _
      _ ≤ 2 := hτ2
  have hedge_im : ∀ y : ℝ, (edgePt y).im = y := fun y => by
    simp only [edgePt, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  set X' : ℝ := eA * (Real.exp (-(δ * X)) / δ + 2 * Y + 2 * X * Real.exp (-(δ * X)) + 4 * η' / δ)
    with hX'
  have hX'0 : 0 ≤ X' := by positivity
  by_cases hn0 : n = 0
  · subst hn0
    have : expEdgeTerm a L τ (-Y) 0 = 0 := by simp [expEdgeTerm]
    rw [this, norm_zero]
    exact mul_nonneg (norm_nonneg _) (by positivity)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  set w : ℂ := edgeExp τ - ((Real.log n : ℝ) : ℂ) * I with hw
  have hwre : w.re = (edgeExp τ).re := by
    simp only [hw, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hwim : w.im = Real.log ‖τ‖ - Real.log n := by
    simp only [hw, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, edgeExp_im]
    ring
  have hIcc : ∀ y ∈ Icc (-X) (-Y), y ≤ -Y := fun y hy => hy.2
  have hden : ∀ y ∈ Icc (-X) (-Y), 1 / X ≤ -(deriv L (edgePt y)).re := by
    intro y hy
    have h := (htail y hy.2).2.2
    have hp := (htail y hy.2).1
    have hy0 : |y| ≤ X := by rw [abs_of_neg (by linarith [hy.2])]; linarith [hy.1]
    rw [div_le_iff₀ hX0]
    calc (1 : ℝ) ≤ |y| * -(deriv L (edgePt y)).re := h
      _ ≤ X * -(deriv L (edgePt y)).re := mul_le_mul_of_nonneg_right hy0 hp.le
      _ = -(deriv L (edgePt y)).re * X := by ring
  have hg : ∀ y ∈ Icc (-X) (-Y),
      -(deriv L (edgePt y)).re / 2 ≤ ‖I * deriv L (edgePt y) + w‖ := by
    intro y hy
    have him : (I * deriv L (edgePt y) + w).im =
        (deriv L (edgePt y)).re + (Real.log ‖τ‖ - Real.log n) := by
      rw [Complex.add_im, hwim]; simp
    have h := Complex.abs_im_le_norm (I * deriv L (edgePt y) + w)
    rw [him] at h
    have hd := hden y hy
    have hτX : Real.log ‖τ‖ ≤ -(deriv L (edgePt y)).re / 2 := by
      have : 1 / (2 * X) = (1 / X) / 2 := by ring
      rw [this] at hτc; linarith
    have hneg : (deriv L (edgePt y)).re + (Real.log ‖τ‖ - Real.log n) ≤
        (deriv L (edgePt y)).re / 2 := by linarith
    have hp := (htail y hy.2).1
    rw [abs_of_neg (by linarith)] at h
    linarith
  have hma : 1 / X ≤ -(deriv L (edgePt (-X))).re := hden (-X) ⟨le_rfl, by linarith⟩
  have hmB : 1 / Y ≤ -(deriv L (edgePt (-Y))).re := by
    have h := (htail (-Y) le_rfl).2.2
    rw [abs_neg, abs_of_pos hY0] at h
    rw [div_le_iff₀ hY0]; linarith
  have hlead := norm_lead_le_of_regular (L := L) (L1 := deriv L) (L2 := deriv (deriv L))
    (w := w) (by rw [hwre]; exact hκ0) (a := -X) (B := -Y) (A := A) (η' := η')
    (μa := 1 / X) (μB := 1 / Y) (by linarith) (by positivity) (by positivity) hη'.le
    (fun y hy => hLc _ (by rw [edgePt_re]; norm_num) (by rw [hedge_im]; linarith))
    (fun y hy => hd1 y (by linarith [hy.2])) (fun y hy => hd2 y (by linarith [hy.2]))
    (fun y hy => hc2 y (by linarith [hy.2]))
    (fun y hy => hLs _ (by rw [edgePt_re]; norm_num) (by rw [edgePt_re])
      (by rw [hedge_im]; linarith))
    (fun y hy => (htail y hy.2).1) hg (fun y hy => (htail y hy.2).2.1) hma hmB
  rw [hwre] at hlead
  have hlead' : ‖∫ y in Iic (-Y), cexp (L (edgePt y) +
      (y : ℂ) * (edgeExp τ - ((Real.log n : ℝ) : ℂ) * I))‖ ≤ X' := by
    refine hlead.trans ?_
    have hκd : 1 / (edgeExp τ).re ≤ 1 / δ := one_div_le_one_div_of_le hδ0 hκδ
    have hE1 : Real.exp ((edgeExp τ).re * -X) ≤ Real.exp (-(δ * X)) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_right hκδ hX0.le
      linarith
    have hE2 : Real.exp ((edgeExp τ).re * -Y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := mul_pos hκ0 hY0; linarith
    have hE1p := Real.exp_pos ((edgeExp τ).re * -X)
    have hE2p := Real.exp_pos ((edgeExp τ).re * -Y)
    have t1 : eA * Real.exp ((edgeExp τ).re * -X) / (edgeExp τ).re ≤
        eA * (Real.exp (-(δ * X)) / δ) := by
      have : Real.exp ((edgeExp τ).re * -X) * (1 / (edgeExp τ).re) ≤
          Real.exp (-(δ * X)) * (1 / δ) := mul_le_mul hE1 hκd (by positivity) (by positivity)
      calc eA * Real.exp ((edgeExp τ).re * -X) / (edgeExp τ).re
          = eA * (Real.exp ((edgeExp τ).re * -X) * (1 / (edgeExp τ).re)) := by ring
        _ ≤ eA * (Real.exp (-(δ * X)) * (1 / δ)) := mul_le_mul_of_nonneg_left this heA0.le
        _ = _ := by ring
    have t2 : 2 * eA * Real.exp ((edgeExp τ).re * -Y) / (1 / Y) ≤ eA * (2 * Y) := by
      rw [div_eq_mul_inv, one_div, inv_inv]
      calc 2 * eA * Real.exp ((edgeExp τ).re * -Y) * Y
          = (2 * eA * Y) * Real.exp ((edgeExp τ).re * -Y) := by ring
        _ ≤ (2 * eA * Y) * 1 := mul_le_mul_of_nonneg_left hE2 (by positivity)
        _ = eA * (2 * Y) := by ring
    have t3 : 2 * eA * Real.exp ((edgeExp τ).re * -X) / (1 / X) ≤
        eA * (2 * X * Real.exp (-(δ * X))) := by
      rw [div_eq_mul_inv, one_div, inv_inv]
      calc 2 * eA * Real.exp ((edgeExp τ).re * -X) * X
          = (2 * eA * X) * Real.exp ((edgeExp τ).re * -X) := by ring
        _ ≤ (2 * eA * X) * Real.exp (-(δ * X)) := mul_le_mul_of_nonneg_left hE1 (by positivity)
        _ = eA * (2 * X * Real.exp (-(δ * X))) := by ring
    have t4 : 4 * η' * eA * Real.exp ((edgeExp τ).re * -Y) / (edgeExp τ).re ≤
        eA * (4 * η' / δ) := by
      have : Real.exp ((edgeExp τ).re * -Y) * (1 / (edgeExp τ).re) ≤ 1 * (1 / δ) :=
        mul_le_mul hE2 hκd (by positivity) (by norm_num)
      calc 4 * η' * eA * Real.exp ((edgeExp τ).re * -Y) / (edgeExp τ).re
          = 4 * η' * eA * (Real.exp ((edgeExp τ).re * -Y) * (1 / (edgeExp τ).re)) := by ring
        _ ≤ 4 * η' * eA * (1 * (1 / δ)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hsum : X' = eA * (Real.exp (-(δ * X)) / δ) + eA * (2 * Y) +
        eA * (2 * X * Real.exp (-(δ * X))) + eA * (4 * η' / δ) := by rw [hX']; ring
    rw [hsum]
    linarith
  have hpt := norm_expEdgeTerm_le_of_lead a hτre0 hn1 (B := -Y) (A := A) (by linarith)
    (fun y hy => hLc _ (by rw [edgePt_re]; norm_num) (by rw [hedge_im]; linarith))
    (fun y hy => hLs _ (by rw [edgePt_re]; norm_num) (by rw [edgePt_re])
      (by rw [hedge_im]; linarith)) hlead'
  refine hpt.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have hE3 : Real.exp (Real.pi * -Y) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := mul_pos hpi hY0; linarith
  have h1 : 2 * ‖τ‖ ^ (1 / 2 : ℝ) * X' ≤ 4 * X' := by
    have := mul_le_mul_of_nonneg_right (show 2 * ‖τ‖ ^ (1 / 2 : ℝ) ≤ 4 by linarith) hX'0
    linarith
  have h2 : Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * -Y) / Real.pi)) ≤
      8 * eA / Real.pi := by
    have : 4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * -Y) / Real.pi) ≤ 4 * 2 * (1 / Real.pi) := by
      gcongr
    calc Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * -Y) / Real.pi))
        ≤ eA * (4 * 2 * (1 / Real.pi)) := mul_le_mul_of_nonneg_left this heA0.le
      _ = 8 * eA / Real.pi := by ring
  linarith

/-! ### The right edge -/

/-- **The twisted right edge under regular variation.**  Suppose `Re L ≤ A` on the lower strip
and, below `−Y`, `Re L' < 0`, `‖L''‖ ≤ η' (Re L')²` and `|y| |Re L'| ≥ 1`.  For `τ` with
`Re τ > 0`, `1 ≤ ‖τ‖ ≤ 2` and `log‖τ‖ ≤ 1/(2X)`, `X ≥ Y`, the right edge `∫_{y ≤ −2}` of `e^{L} G`
is at most `S_a(4X' + 8e^{A}/π) + e^{S} K‖τ‖ e^{A}(Y − 2)`,
`X' = e^{A}(e^{−δX}/δ + 2Y + 2Xe^{−δX} + 4η'/δ)`, `δ = Re τ/‖τ‖`. -/
theorem norm_regular_rightEdge_le {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hd1 : ∀ y : ℝ, y < 0 → HasDerivAt L (deriv L (edgePt y)) (edgePt y))
    (hd2 : ∀ y : ℝ, y < 0 → HasDerivAt (deriv L) (deriv (deriv L) (edgePt y)) (edgePt y))
    (hc2 : ∀ y : ℝ, y < 0 → ContinuousAt (deriv (deriv L)) (edgePt y)) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    {η' Y X : ℝ} (hη' : 0 < η') (hY2 : 2 ≤ Y) (hYX : Y ≤ X)
    (htail : ∀ y : ℝ, y ≤ -Y → 0 < -(deriv L (edgePt y)).re ∧
      ‖deriv (deriv L) (edgePt y)‖ ≤ η' * (deriv L (edgePt y)).re ^ 2 ∧
      1 ≤ |y| * -(deriv L (edgePt y)).re)
    {τ : ℂ} (hτre0 : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) (hτ2 : ‖τ‖ ≤ 2)
    (hτc : Real.log ‖τ‖ ≤ 1 / (2 * X)) :
    ‖∫ y in Iic (-2 : ℝ), edgeIntegrand (expTwistG L G) τ (edgePt y)‖ ≤
      (∑' n, ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖) *
        (4 * (Real.exp A * (Real.exp (-(τ.re / ‖τ‖ * X)) / (τ.re / ‖τ‖) + 2 * Y +
          2 * X * Real.exp (-(τ.re / ‖τ‖ * X)) + 4 * η' / (τ.re / ‖τ‖))) + 8 * Real.exp A / Real.pi) +
      Real.exp (∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖) *
        (4 * Real.pi ^ (3 / 4 : ℝ)) * ‖τ‖ * Real.exp A * (Y - 2) := by
  have hpi := Real.pi_pos
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set a : ℕ → ℂ := dirichletExp (lamLog lam) with ha
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have hSa_summ : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ :=
    (hLa _ (by simp; norm_num)).1.norm
  set Sa : ℝ := ∑' n, ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ with hSa
  set K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) with hK
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  set H : ℂ → ℂ := expTwistG L G with hH
  have hHc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt H s := fun s hs him =>
    (Complex.continuous_exp.continuousAt.comp (hLc s hs him)).mul (hGc s hs)
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
  have hτpos : 0 < ‖τ‖ := by linarith
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre0 hτpos
  have hκδ : δ ≤ (edgeExp τ).re := by
    rw [edgeExp_re]
    have h := abs_arg_pi_mul_sq_le hτre0
    have := le_abs_self ((Real.pi : ℂ) * τ ^ 2).arg
    linarith
  have hκ0 : 0 < (edgeExp τ).re := lt_of_lt_of_le hδ0 hκδ
  have hτh : ‖τ‖ ^ (1 / 2 : ℝ) ≤ 2 := by
    calc ‖τ‖ ^ (1 / 2 : ℝ) ≤ ‖τ‖ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hτ1 (by norm_num)
      _ = ‖τ‖ := Real.rpow_one _
      _ ≤ 2 := hτ2
  have hedge0 : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand H τ (edgePt y)‖ ≤
      Real.exp (L (edgePt y)).re * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) := by
    intro y hy
    rw [hH, edgeIntegrand_expTwistG, norm_mul, Complex.norm_exp]
    have hE := norm_edgeIntegrand_three_halves_le hsl hid hGd hG2 hτre0 hτ1
      (show 1 ≤ |y| by rw [abs_of_neg (by linarith)]; linarith)
    have hE' : ‖edgeIntegrand G τ (edgePt y)‖ ≤
        Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := hE
    exact mul_le_mul_of_nonneg_left hE' (Real.exp_pos _).le
  have hedge_im : ∀ y : ℝ, (edgePt y).im = y := fun y => by
    simp only [edgePt, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hLe : ∀ y : ℝ, y ≤ -1 → Real.exp (L (edgePt y)).re ≤ eA := fun y hy =>
    Real.exp_le_exp.mpr (hLs _ (by rw [edgePt_re]; norm_num) (by rw [edgePt_re])
      (by rw [hedge_im]; exact hy))
  have hec : ContinuousOn (fun y : ℝ => edgeIntegrand H τ (edgePt y)) (Iic (-2)) := by
    intro y hy
    have hy' : y ≤ -2 := hy
    have hre : (edgePt y).re = 3 / 2 := edgePt_re y
    have h0 : edgePt y ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [hre] at this; simp at this
    have h1 : edgePt y ≠ 1 := fun h => by
      have := congrArg Complex.re h; rw [hre] at this; norm_num at this
    refine (ContinuousAt.comp (g := edgeIntegrand H τ) ?_
      continuous_edgePt.continuousAt).continuousWithinAt
    exact (continuousAt_prodF_of_continuousAt (hHc _ (by rw [hre]; norm_num)
      (by rw [hedge_im]; linarith)) (by rw [hre]; norm_num) h0 h1).mul
      (differentiableAt_offKernel hτ0 (by rw [hre]; norm_num) (by rw [hre]; norm_num)).continuousAt
  have heint : IntegrableOn (fun y : ℝ => edgeIntegrand H τ (edgePt y)) (Iic (-2)) := by
    refine ((integrableOn_exp_neg_abs_mul_Iic hδ0 (by norm_num : (-2 : ℝ) ≤ 0)).const_mul
      (eA * (Real.exp S * (K * ‖τ‖)))).mono' (hec.aestronglyMeasurable measurableSet_Iic)
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => ?_))
    have hy' : y ≤ -2 := hy
    refine (hedge0 y (by linarith)).trans ?_
    have h0 : 0 ≤ Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := by positivity
    calc _ ≤ eA * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) :=
          mul_le_mul_of_nonneg_right (hLe y (by linarith)) h0
      _ = _ := by ring
  have hdisj : Disjoint (Iic (-Y)) (Ioc (-Y) (-2 : ℝ)) :=
    Set.disjoint_left.mpr fun y h1 h2 => absurd (show y ≤ -Y from h1) (not_le.mpr h2.1)
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  set X' : ℝ := eA * (Real.exp (-(δ * X)) / δ + 2 * Y + 2 * X * Real.exp (-(δ * X)) + 4 * η' / δ)
    with hX'
  have hX'0 : 0 ≤ X' := by positivity
  have hterm : ∀ n : ℕ, ‖expEdgeTerm a L τ (-Y) n‖ ≤
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * (4 * X' + 8 * eA / Real.pi) := fun n =>
    norm_expEdgeTerm_le_regular a hLc hd1 hd2 hc2 hLs hη' hY2 hYX htail hτre0 hτ1 hτ2 hτc n
  have htail_bd : ‖∫ y in Iic (-Y), edgeIntegrand H τ (edgePt y)‖ ≤
      Sa * (4 * X' + 8 * eA / Real.pi) := by
    have hhs : HasSum (expEdgeTerm a L τ (-Y))
        (∫ y in Iic (-Y), edgeIntegrand H τ (edgePt y)) :=
      hasSum_expEdgeTerm hsl hid hGd hG2 hτre0 hτ1 (by linarith)
        (fun y hy => hLc _ (by rw [edgePt_re]; norm_num) (by rw [hedge_im]; linarith))
        (fun y hy => hLs _ (by rw [edgePt_re]; norm_num) (by rw [edgePt_re])
          (by rw [hedge_im]; linarith))
    rw [← hhs.tsum_eq]
    have hsumm : Summable fun n => ‖expEdgeTerm a L τ (-Y) n‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hSa_summ.mul_right _)
    refine (norm_tsum_le_tsum_norm hsumm).trans ?_
    rw [hSa, ← tsum_mul_right]
    exact hsumm.tsum_le_tsum hterm (hSa_summ.mul_right _)
  rw [← Iic_union_Ioc_eq_Iic (show -Y ≤ -2 by linarith),
    setIntegral_union hdisj measurableSet_Ioc
      (heint.mono_set (Iic_subset_Iic.mpr (by linarith))) (heint.mono_set Ioc_subset_Iic_self)]
  refine (norm_add_le _ _).trans (add_le_add htail_bd ?_)
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-Y) (-2 : ℝ))
    (f := fun y : ℝ => edgeIntegrand H τ (edgePt y))
    (C := Real.exp S * K * ‖τ‖ * eA) measure_Ioc_lt_top (fun y hy => ?_)
  · rw [Real.volume_real_Ioc_of_le (by linarith)] at h
    refine h.trans (le_of_eq ?_)
    ring
  · have hy2 : y ≤ -2 := hy.2
    refine (hedge0 y (by linarith)).trans ?_
    have he : Real.exp (-(|y| * δ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := abs_nonneg y; nlinarith
    have h0 : 0 ≤ Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := by positivity
    calc _ ≤ eA * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) :=
          mul_le_mul_of_nonneg_right (hLe y (by linarith)) h0
      _ ≤ eA * (Real.exp S * (K * ‖τ‖ * 1)) := by gcongr
      _ = _ := by ring



/-! ### The far part of the radial integral -/

/-- The arithmetic of the far bound. -/
theorem regular_far_arith {Sa eA η' Y ε δ e : ℝ} (hSa : 0 ≤ Sa) (heA : 0 < eA) (hη' : 0 < η')
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : ε / 2 ≤ δ) (he0 : 0 ≤ e)
    (he : e ≤ 8 * ε ^ 2) :
    ε * (1 / 2) * (Sa * (4 * (eA * (e / δ + 2 * Y + 2 * (1 / ε ^ 2) * e + 4 * η' / δ)) +
      8 * eA / Real.pi)) ≤ 16 * Sa * eA * η' + Sa * eA * (64 + 4 * Y + 4 / Real.pi) * ε := by
  have hδ0 : 0 < δ := by linarith
  have hq : ε / δ ≤ 2 := by rw [div_le_iff₀ hδ0]; linarith
  have hq0 : 0 ≤ ε / δ := by positivity
  have h1 : ε * (e / δ) ≤ 16 * ε := by
    have e1 : ε * (e / δ) = (ε / δ) * e := by ring
    rw [e1]
    have := mul_le_mul hq he he0 (by norm_num)
    nlinarith
  have h2 : ε * (2 * (1 / ε ^ 2) * e) ≤ 16 * ε := by
    have e1 : ε * (2 * (1 / ε ^ 2) * e) = 2 * e / ε := by field_simp
    rw [e1, div_le_iff₀ hε]
    nlinarith
  have h3 : ε * (4 * η' / δ) ≤ 8 * η' := by
    have e1 : ε * (4 * η' / δ) = 4 * η' * (ε / δ) := by ring
    rw [e1]; nlinarith
  have hsum : ε * (e / δ) + 2 * Y * ε + ε * (2 * (1 / ε ^ 2) * e) + ε * (4 * η' / δ) ≤
      16 * ε + 2 * Y * ε + 16 * ε + 8 * η' := by linarith
  have hpos : 0 ≤ 2 * Sa * eA := by positivity
  have hmain := mul_le_mul_of_nonneg_left hsum hpos
  have e2 : ε * (1 / 2) * (Sa * (4 * (eA * (e / δ + 2 * Y + 2 * (1 / ε ^ 2) * e + 4 * η' / δ)) +
      8 * eA / Real.pi)) = 2 * Sa * eA * (ε * (e / δ) + 2 * Y * ε + ε * (2 * (1 / ε ^ 2) * e) +
        ε * (4 * η' / δ)) + Sa * eA * (4 / Real.pi) * ε := by ring
  rw [e2]
  have e3 : 2 * Sa * eA * (16 * ε + 2 * Y * ε + 16 * ε + 8 * η') =
      16 * Sa * eA * η' + Sa * eA * (64 + 4 * Y) * ε := by ring
  have e4 : Sa * eA * (64 + 4 * Y + 4 / Real.pi) * ε =
      Sa * eA * (64 + 4 * Y) * ε + Sa * eA * (4 / Real.pi) * ε := by ring
  linarith

/-- **The far part under regular variation.**  For `0 < ε ≤ 1` with `ε²Y ≤ 1`,
`ε ‖∫_{t ≤ −1} e^{L(½+2it)} φ(t) k(2t, ε + i) dt‖ ≤ C₁ η' + (C₂ + C₃ Y) ε`. -/
theorem norm_regular_far_le {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → s.im < 0 → DifferentiableAt ℂ L s)
    (hd1 : ∀ y : ℝ, y < 0 → HasDerivAt L (deriv L (edgePt y)) (edgePt y))
    (hd2 : ∀ y : ℝ, y < 0 → HasDerivAt (deriv L) (deriv (deriv L) (edgePt y)) (edgePt y))
    (hc2 : ∀ y : ℝ, y < 0 → ContinuousAt (deriv (deriv L)) (edgePt y)) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    {η' Y : ℝ} (hη' : 0 < η') (hY2 : 2 ≤ Y)
    (htail : ∀ y : ℝ, y ≤ -Y → 0 < -(deriv L (edgePt y)).re ∧
      ‖deriv (deriv L) (edgePt y)‖ ≤ η' * (deriv L (edgePt y)).re ^ 2 ∧
      1 ≤ |y| * -(deriv L (edgePt y)).re)
    {CF₀ : ℝ} (hCF₀ : 0 ≤ CF₀)
    (hF₀ : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF₀ * (1 + |y|) ^ (1 / 2 : ℝ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hεY : ε ^ 2 * Y ≤ 1) :
    ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))‖ ≤
      16 * (∑' n, ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖) *
          Real.exp A * η' +
        (∑' n, ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖) * Real.exp A *
          (64 + 4 * Y + 4 / Real.pi) * ε +
        Real.exp (∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖) *
          (4 * Real.pi ^ (3 / 4 : ℝ)) * Real.exp A * Y * ε +
        Real.exp A * CF₀ * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ)) * ε := by
  have hpi := Real.pi_pos
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set Sa : ℝ := ∑' n, ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖ with hSa
  have hSa0 : 0 ≤ Sa := tsum_nonneg fun n => norm_nonneg _
  set K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  set CF : ℝ := eA * CF₀ with hCF
  have hCF0 : 0 ≤ CF := by positivity
  set H : ℂ → ℂ := expTwistG L G with hH
  have hHc' : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → ContinuousAt H s :=
    fun s hs _ him =>
    (Complex.continuous_exp.continuousAt.comp (hLc s hs (by linarith))).mul (hGc s hs)
  have hHd' : ∀ s : ℂ, 1 / 2 < s.re → s.re < 3 / 2 → s.im < -1 → DifferentiableAt ℂ H s :=
    fun s hs _ him =>
    ((hLd s hs (by linarith)).cexp).mul (hGd s hs).differentiableAt
  have hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → y ≤ -2 →
      ‖prodF H ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ) := by
    intro x y hx1 hx2 hy
    have hre : (1 / 2 : ℝ) ≤ ((x : ℂ) + (y : ℂ) * I).re := by simpa using hx1
    have hre2 : ((x : ℂ) + (y : ℂ) * I).re ≤ 3 / 2 := by simpa using hx2
    have him : ((x : ℂ) + (y : ℂ) * I).im ≤ -1 := by simp; linarith
    rw [hH, prodF_expTwistG, norm_mul, Complex.norm_exp, hCF]
    have h1 : Real.exp (L ((x : ℂ) + (y : ℂ) * I)).re ≤ eA :=
      Real.exp_le_exp.mpr (hLs _ hre hre2 him)
    have h3 := hF₀ x y hx1 hx2 (by rw [abs_of_neg (by linarith)]; linarith)
    calc Real.exp (L ((x : ℂ) + (y : ℂ) * I)).re * ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖
        ≤ eA * (CF₀ * (1 + |y|) ^ (1 / 2 : ℝ)) :=
          mul_le_mul h1 h3 (norm_nonneg _) heA0.le
      _ = eA * CF₀ * (1 + |y|) ^ (1 / 2 : ℝ) := by ring
  set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = 1 := by simp [hτ]
    rw [him, abs_one] at h; exact h
  have hτ2 : ‖τ‖ ≤ 2 := by
    have h := norm_add_le (ε : ℂ) (((1 : ℕ) : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Nat.cast_one, norm_one,
      Real.norm_eq_abs, abs_of_pos hε] at h
    have e : τ = (ε : ℂ) + 1 * I := by rw [hτ, Nat.cast_one]
    rw [e]; linarith
  have hτpos : 0 < ‖τ‖ := by linarith
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre0 hτpos
  have hδε : ε / 2 ≤ δ := by
    rw [hδ, hτre]; exact div_le_div_of_nonneg_left hε.le hτpos hτ2
  set X : ℝ := 1 / ε ^ 2 with hX
  have hτc : Real.log ‖τ‖ ≤ 1 / (2 * X) := by
    have h : Real.log ‖τ‖ ≤ Real.log ((1 : ℕ) : ℝ) + ε ^ 2 / 2 :=
      (log_norm_eps_add_mI_le (ε := ε) (le_refl 1)).2
    rw [Nat.cast_one, Real.log_one, zero_add] at h
    have e : 1 / (2 * X) = ε ^ 2 / 2 := by rw [hX]; field_simp
    rw [e]; exact h
  have hYX : Y ≤ X := by
    rw [hX, le_div_iff₀ (by positivity)]; linarith
  have hδX : 1 / (2 * ε) ≤ δ * X := by
    rw [hX]
    have h2 : ε / 2 * (1 / ε ^ 2) ≤ δ * (1 / ε ^ 2) :=
      mul_le_mul_of_nonneg_right hδε (by positivity)
    have e : ε / 2 * (1 / ε ^ 2) = 1 / (2 * ε) := by field_simp
    linarith
  have hexpδ : Real.exp (-(δ * X)) ≤ 8 * ε ^ 2 :=
    (Real.exp_le_exp.mpr (by linarith)).trans (exp_neg_inv_two_mul_le hε)
  have hedge : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      (eA * Real.exp S) *
        (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
    intro y hy
    rw [hH, edgeIntegrand_expTwistG, norm_mul, Complex.norm_exp]
    have hE := norm_edgeIntegrand_three_halves_le hsl hid hGd hG2 hτre0 hτ1
      (show 1 ≤ |y| by rw [abs_of_neg (by linarith)]; linarith)
    have hLe : Real.exp (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re ≤ eA :=
      Real.exp_le_exp.mpr (hLs _ (by norm_num) (by norm_num) (by simpa using hy))
    calc _ ≤ eA * (Real.exp S * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
          Real.exp (-(|y| * (τ.re / ‖τ‖))))) := mul_le_mul hLe hE (norm_nonneg _) heA0.le
      _ = _ := by ring
  have hfint : IntegrableOn (fun t => phiG H t * pairKernel (2 * t) τ) (Iic (-1)) := by
    have h := ((MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
      hτre0).norm.const_mul eA).integrableOn (s := Iic (-1))
    refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Iic).mpr
      (Filter.Eventually.of_forall fun t ht => ?_))
    · have hc : ContinuousOn (fun t : ℝ => cexp (L (lineS t)) * phiG G t *
          pairKernel (2 * t) τ) (Iic (-1)) := by
        intro t ht
        have ht0 : t ≤ -1 := ht
        have hl : Continuous lineS := by unfold lineS; fun_prop
        have him : (lineS t).im < 0 := by unfold lineS; simp; linarith
        have hL1 : ContinuousAt (fun t : ℝ => cexp (L (lineS t))) t :=
          Complex.continuous_exp.continuousAt.comp
            ((hLc _ (le_of_eq (lineS_re t).symm) him).comp hl.continuousAt)
        exact ((hL1.mul (continuous_phiG hGc).continuousAt).mul
          (continuous_pairKernel_two_mul hτ0).continuousAt).continuousWithinAt
      refine (hc.congr fun t _ => ?_).aestronglyMeasurable measurableSet_Iic
      simp only [hH, phiG_expTwistG]
    · have ht0 : t < 0 := lt_of_le_of_lt ht (by norm_num)
      rw [hH, phiG_expTwistG, mul_assoc, norm_mul, Complex.norm_exp]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hLl t ht0)) (norm_nonneg _)
  have hcont := setIntegral_Iic_radial_eq_of_lowerRegion hHc' hHd' hCF0 hF hτre0 hτ1 hedge le_rfl
    hfint
  have hrewrite : ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) τ) =
      ∫ t in Iic (-1 : ℝ), phiG H t * pairKernel (2 * t) τ := by
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    rw [hH, phiG_expTwistG]; ring
  rw [hrewrite, hcont]
  have hright0 := norm_regular_rightEdge_le hsl hid hGc hGd hG2 hLc hd1 hd2 hc2 hLs hη' hY2
    hYX htail hτre0 hτ1 hτ2 hτc
  have hright : ‖∫ y in Iic (2 * (-1 : ℝ)),
      edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      Sa * (4 * (eA * (Real.exp (-(δ * X)) / δ + 2 * Y + 2 * X * Real.exp (-(δ * X)) +
        4 * η' / δ)) + 8 * eA / Real.pi) + Real.exp S * K * ‖τ‖ * eA * (Y - 2) := by
    rw [show (2 * (-1 : ℝ)) = -2 by norm_num]
    exact hright0
  have htop : ‖∫ x in (1 / 2 : ℝ)..(3 / 2),
      edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖ ≤
      CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) := by
    have h := norm_horizontalEdge_le_lower hF hτre0 hτ1 (y := 2 * (-1 : ℝ)) (by norm_num)
    refine h.trans ?_
    have habs : |2 * (-1 : ℝ)| = 2 := by norm_num
    rw [habs]
    have he : Real.exp (-(2 * (τ.re / ‖τ‖))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := div_pos hτre0 hτpos; linarith
    have h0 : 0 ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) := by positivity
    calc CF * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
          Real.exp (-(2 * (τ.re / ‖τ‖))))
        ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * 2 * 1) := by gcongr
      _ = CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) := by rw [hK]; ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_mul,
    show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
  have htri := norm_add_le (∫ y in Iic (2 * (-1 : ℝ)),
    edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
    (I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I))
  rw [norm_mul (I : ℂ), Complex.norm_I, one_mul] at htri
  have hτh' : ‖τ‖ / 2 ≤ 1 := by linarith
  have hεδ : ε * (1 / δ) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ hδ0]; linarith
  have ta : ε * (1 / 2) * (Sa * (4 * (eA * (Real.exp (-(δ * X)) / δ + 2 * Y +
      2 * X * Real.exp (-(δ * X)) + 4 * η' / δ)) + 8 * eA / Real.pi)) ≤
      16 * Sa * eA * η' + Sa * eA * (64 + 4 * Y + 4 / Real.pi) * ε :=
    regular_far_arith hSa0 heA0 hη' hε hε1 hδε (Real.exp_pos _).le hexpδ
  have tb : ε * (1 / 2) * (Real.exp S * K * ‖τ‖ * eA * (Y - 2)) ≤
      Real.exp S * K * eA * Y * ε := by
    have e1 : ε * (1 / 2) * (Real.exp S * K * ‖τ‖ * eA * (Y - 2)) =
        (Real.exp S * K * eA * ε) * ((‖τ‖ / 2) * (Y - 2)) := by ring
    have h' : (‖τ‖ / 2) * (Y - 2) ≤ 1 * Y :=
      mul_le_mul hτh' (by linarith) (by linarith) (by norm_num)
    have h'' := mul_le_mul_of_nonneg_left h' (show 0 ≤ Real.exp S * K * eA * ε by positivity)
    calc _ = _ := e1
      _ ≤ (Real.exp S * K * eA * ε) * (1 * Y) := h''
      _ = Real.exp S * K * eA * Y * ε := by ring
  have tc : ε * (1 / 2) * (CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2)) =
      eA * CF₀ * (1 + 2) ^ (1 / 2 : ℝ) * K * ε := by rw [hCF]; ring
  calc ε * (1 / 2 * ‖(∫ y in Iic (2 * (-1 : ℝ)),
          edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2),
          edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖)
      ≤ ε * (1 / 2 * ((Sa * (4 * (eA * (Real.exp (-(δ * X)) / δ + 2 * Y +
          2 * X * Real.exp (-(δ * X)) + 4 * η' / δ)) + 8 * eA / Real.pi) +
          Real.exp S * K * ‖τ‖ * eA * (Y - 2)) + CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2))) := by
        gcongr
        exact htri.trans (add_le_add hright htop)
    _ = ε * (1 / 2) * (Sa * (4 * (eA * (Real.exp (-(δ * X)) / δ + 2 * Y +
          2 * X * Real.exp (-(δ * X)) + 4 * η' / δ)) + 8 * eA / Real.pi)) +
          ε * (1 / 2) * (Real.exp S * K * ‖τ‖ * eA * (Y - 2)) +
          ε * (1 / 2) * (CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2)) := by ring
    _ ≤ 16 * Sa * eA * η' + Sa * eA * (64 + 4 * Y + 4 / Real.pi) * ε +
          Real.exp S * K * eA * Y * ε + eA * CF₀ * (1 + 2) ^ (1 / 2 : ℝ) * K * ε := by
        rw [tc]; linarith [ta, tb]



/-! ### The twisted radial integral vanishes -/

/-- **The regular-twist radial integral tends to `0`.** -/
theorem tendsto_regular_twist_radial {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → s.im < 0 → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    (hden : Tendsto (fun y : ℝ => y * (deriv L (edgePt y)).re) atBot atTop)
    (hrat : Tendsto (fun y : ℝ => ‖deriv (deriv L) (edgePt y)‖ / (deriv L (edgePt y)).re ^ 2)
      atBot (𝓝 0)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  obtain ⟨CF₀, hCF₀, hF₀⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  -- derivatives of `L` on the edge
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.im < 0} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im continuous_const)
  have hLon : DifferentiableOn ℂ L U := fun s hs => (hLd s hs.1 hs.2).differentiableWithinAt
  have hL1on : DifferentiableOn ℂ (deriv L) U := hLon.deriv hUo
  have hL2on : DifferentiableOn ℂ (deriv (deriv L)) U := hL1on.deriv hUo
  have hmem : ∀ y : ℝ, y < 0 → edgePt y ∈ U := fun y hy => by
    refine ⟨?_, ?_⟩
    · show (1 / 2 : ℝ) < (edgePt y).re
      rw [edgePt_re]; norm_num
    · show (edgePt y).im < 0
      simp [edgePt]; exact hy
  have hd1 : ∀ y : ℝ, y < 0 → HasDerivAt L (deriv L (edgePt y)) (edgePt y) := fun y hy =>
    (hLd _ (hmem y hy).1 (hmem y hy).2).hasDerivAt
  have hd2 : ∀ y : ℝ, y < 0 → HasDerivAt (deriv L) (deriv (deriv L) (edgePt y)) (edgePt y) :=
    fun y hy => ((hL1on _ (hmem y hy)).differentiableAt (hUo.mem_nhds (hmem y hy))).hasDerivAt
  have hc2 : ∀ y : ℝ, y < 0 → ContinuousAt (deriv (deriv L)) (edgePt y) := fun y hy =>
    ((hL2on _ (hmem y hy)).differentiableAt (hUo.mem_nhds (hmem y hy))).continuousAt
  -- the near part
  have hnear : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
    refine (tendsto_eps_mul_setIntegral_Ioo (h := fun t => cexp (L (lineS t)) * phiG G t)
      (B := eA * (CB * 2 ^ N)) (fun t ht => ?_) le_rfl).congr fun ε => ?_
    · rw [norm_mul, Complex.norm_exp]
      have h1 : Real.exp (L (lineS t)).re ≤ eA := Real.exp_le_exp.mpr (hLl t ht.2)
      have h2 : ‖phiG G t‖ ≤ CB * 2 ^ N := by
        refine (hpoly t).1.trans ?_
        have hta : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        gcongr; linarith
      exact mul_le_mul h1 h2 (norm_nonneg _) heA0.le
    · simp only [mul_assoc]
  -- the far part
  have hfar : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
    set Sa : ℝ := ∑' n, ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖
      with hSa
    have hSa0 : 0 ≤ Sa := tsum_nonneg fun n => norm_nonneg _
    set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
    set K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) with hK
    have hK0 : 0 ≤ K := by positivity
    rw [Metric.tendsto_nhds]
    intro e he
    set C₁ : ℝ := 16 * Sa * Real.exp A with hC₁
    have hC₁0 : 0 ≤ C₁ := by positivity
    set η' : ℝ := e / (4 * (C₁ + 1)) with hη'
    have hη'0 : 0 < η' := by positivity
    have hev := (hden.eventually (eventually_ge_atTop 1)).and (hrat.eventually (gt_mem_nhds hη'0))
    obtain ⟨a₀, ha₀⟩ := Filter.eventually_atBot.mp hev
    set Y : ℝ := max 2 (-a₀) with hY
    have hY2 : 2 ≤ Y := le_max_left _ _
    have htail : ∀ y : ℝ, y ≤ -Y → 0 < -(deriv L (edgePt y)).re ∧
        ‖deriv (deriv L) (edgePt y)‖ ≤ η' * (deriv L (edgePt y)).re ^ 2 ∧
        1 ≤ |y| * -(deriv L (edgePt y)).re := by
      intro y hy
      have h := ha₀ y (by have := le_max_right 2 (-a₀); linarith)
      have hy0 : y < 0 := by linarith
      have h1 : 1 ≤ y * (deriv L (edgePt y)).re := h.1
      have hneg : 0 < -(deriv L (edgePt y)).re := by
        by_contra hc
        push Not at hc
        have : y * (deriv L (edgePt y)).re ≤ 0 := by nlinarith
        linarith
      refine ⟨hneg, ?_, ?_⟩
      · have hne : (deriv L (edgePt y)).re ≠ 0 := by linarith
        have hsq : 0 < (deriv L (edgePt y)).re ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
        have h2 := h.2
        rw [div_lt_iff₀ hsq] at h2
        linarith
      · rw [abs_of_neg hy0]
        linarith
    set C₂ : ℝ := Sa * Real.exp A * (64 + 4 * Y + 4 / Real.pi) + Real.exp S * K * Real.exp A * Y +
      Real.exp A * CF₀ * (1 + 2) ^ (1 / 2 : ℝ) * K with hC₂
    have hC₂0 : 0 ≤ C₂ := by positivity
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (min 1 (1 / (Y + 1))) (e / (2 * (C₂ + 1)))
      by positivity)] with ε hε
    rw [dist_zero_right]
    have hε1 : ε ≤ 1 := hε.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hεY' : ε ≤ 1 / (Y + 1) := hε.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hεY : ε ^ 2 * Y ≤ 1 := by
      have h1 : ε * (Y + 1) ≤ 1 := by rwa [le_div_iff₀ (by linarith)] at hεY'
      have h2 : ε ^ 2 ≤ ε := by nlinarith [hε.1]
      nlinarith [hε.1]
    have hb := norm_regular_far_le hsl hΦre hid hGc hGd hG2 hLc hLd hd1 hd2 hc2 hLs hLl hη'0
      hY2 htail hCF₀ hF₀ hε.1 hε1 hεY
    have hε2 : ε * (2 * (C₂ + 1)) < e :=
      (lt_div_iff₀ (by positivity)).mp (lt_of_lt_of_le hε.2 (min_le_right _ _))
    have hη'e : η' * (4 * (C₁ + 1)) = e := by rw [hη']; field_simp
    have h1 : C₂ * ε < e / 2 := by nlinarith [hε.1]
    have h2 : C₁ * η' < e / 2 := by nlinarith
    calc _ ≤ _ := hb
      _ = C₁ * η' + C₂ * ε := by rw [hC₂, hC₁]; ring
      _ < e / 2 + e / 2 := add_lt_add h2 h1
      _ = e := by ring
  -- combine
  have hsum := hfar.add hnear
  rw [add_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have hε' : (0 : ℝ) < ε := hε
  set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
  have hτre : 0 < τ.re := by simp [hτ]; exact hε'
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hint : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Iio 0) := by
    have h := ((MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
      hτre).norm.const_mul eA).integrableOn (s := Iio (0 : ℝ))
    refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Iio).mpr
      (Eventually.of_forall fun t ht => ?_))
    · have hc : ContinuousOn (fun t : ℝ => cexp (L (lineS t)) * (phiG G t *
          pairKernel (2 * t) τ)) (Iio 0) := by
        intro t ht
        have ht0 : t < 0 := ht
        have hl : Continuous lineS := by unfold lineS; fun_prop
        have him : (lineS t).im < 0 := by unfold lineS; simp; linarith
        have hL1 : ContinuousAt (fun t : ℝ => cexp (L (lineS t))) t :=
          Complex.continuous_exp.continuousAt.comp
            ((hLc _ (le_of_eq (lineS_re t).symm) him).comp hl.continuousAt)
        exact (hL1.mul ((continuous_phiG hGc).continuousAt.mul
          (continuous_pairKernel_two_mul hτ0).continuousAt)).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Iio
    · have ht0 : t < 0 := ht
      rw [norm_mul, Complex.norm_exp]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hLl t ht0)) (norm_nonneg _)
  have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
    ext t
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro h
      by_cases h1 : t ≤ -1
      · exact Or.inl h1
      · exact Or.inr ⟨by linarith, h⟩
    · rintro (h | h)
      · linarith
      · exact h.2
  have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
    Set.disjoint_left.mpr fun t h1 h2 => by
      simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
  have h1 : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Iic (-1)) := hint.mono_set (by rw [hsplit]; exact subset_union_left)
  have h2 : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Ioo (-1) 0) := hint.mono_set (by rw [hsplit]; exact subset_union_right)
  simp only
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioo h1 h2]
  ring

/-! ### The theorems -/

/-- **Regularly varying lock phases are impossible.**  Let `L` be holomorphic on `Re s > ½`,
continuous on `Re s ≥ ½`, with `Re L ≤ A` on the lower strip and the lower line,
`y Re L'(3/2 + iy) → +∞` and `‖L''(3/2 + iy)‖/(Re L'(3/2 + iy))² → 0` as `y → −∞`.  Then no
Herglotz producer satisfies `G(1 − s) = κ₀ e^{L(s)} G(s)` at `s = ½ + 2iτ`, `τ < 0`. -/
theorem regular_twist_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → s.im < 0 → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    (hden : Tendsto (fun y : ℝ => y * (deriv L (edgePt y)).re) atBot atTop)
    (hrat : Tendsto (fun y : ℝ => ‖deriv (deriv L) (edgePt y)‖ / (deriv L (edgePt y)).re ^ 2)
      atBot (𝓝 0))
    {κ₀ : ℂ} (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = κ₀ * cexp (L (lineS τ)) * G (lineS τ)) :
    False := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hpi := Real.pi_pos
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  set R : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
    phiStar G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) with hR
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (2 * betaG G)) := by
    have h := (tendsto_lower_reflected_radial hsl hΦre hidT hGc hGd hG2 (le_refl 1)).const_mul
      ((2 * Real.pi : ℝ) : ℂ)
    have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) = 2 * betaG G := by
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      push_cast; field_simp
    rw [hval] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    simp only [hR]
    linear_combination ((ε : ℂ) * ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ) * h2pi
  have hR0 : Tendsto R (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_regular_twist_radial hsl hΦre hidT hGc hGd hG2 hLc hLd hLs hLl hden
      hrat).const_mul κ₀
    rw [mul_zero] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    simp only [hR]
    rw [← mul_assoc, mul_comm κ₀, mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
    have ht0 : t < 0 := ht
    simp only [phiStar, phiG]
    rw [hlock t ht0]
    ring
  have h0 : (2 : ℂ) * betaG G = 0 := tendsto_nhds_unique hRlim hR0
  exact hβ ((mul_eq_zero.mp h0).resolve_left two_ne_zero)

/-- **Windowed regular locks are impossible.**  The lock of `regular_twist_lock_impossible` holding
only on windows `−Y_j ≤ τ ≤ −X_j` (`X_j → ∞`, `Y_j ≥ (1 + X_j)^p` eventually for every `p`,
`‖κ_j‖ ≤ K₀`) is already impossible. -/
theorem windowed_regular_twist_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → s.im < 0 → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    (hden : Tendsto (fun y : ℝ => y * (deriv L (edgePt y)).re) atBot atTop)
    (hrat : Tendsto (fun y : ℝ => ‖deriv (deriv L) (edgePt y)‖ / (deriv L (edgePt y)).re ^ 2)
      atBot (𝓝 0))
    {K₀ : ℝ} {X Y : ℕ → ℝ} {κ : ℕ → ℂ}
    (hX : Tendsto X atTop atTop) (hY : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X j) ^ p ≤ Y j)
    (hκ : ∀ j, ‖κ j‖ ≤ K₀)
    (hlock : ∀ j, ∀ τ : ℝ, -Y j ≤ τ → τ ≤ -X j →
      G (1 - lineS τ) = κ j * cexp (L (lineS τ)) * G (lineS τ)) :
    False := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  set w : ℝ → ℂ := (Iio (0 : ℝ)).indicator fun τ => cexp (L (lineS τ)) with hw
  have hwc : ContinuousOn (fun τ : ℝ => cexp (L (lineS τ))) (Iio 0) := by
    intro τ hτ
    have hτ0 : τ < 0 := hτ
    have hl : Continuous lineS := by unfold lineS; fun_prop
    have him : (lineS τ).im < 0 := by unfold lineS; simp; linarith
    exact (Complex.continuous_exp.continuousAt.comp
      ((hLc _ (le_of_eq (lineS_re τ).symm) him).comp hl.continuousAt)).continuousWithinAt
  have hwm : AEStronglyMeasurable w volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).mpr
      (hwc.aestronglyMeasurable measurableSet_Iio)
  have hwb : ∀ t, ‖w t‖ ≤ Real.exp A := by
    intro t
    by_cases ht : t < 0
    · rw [hw, Set.indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht), Complex.norm_exp]
      exact Real.exp_le_exp.mpr (hLl t ht)
    · rw [hw, Set.indicator_of_notMem (show t ∉ Iio (0 : ℝ) from ht), norm_zero]
      exact (Real.exp_pos _).le
  have hXpos : ∀ᶠ j in atTop, 0 < X j := hX.eventually_gt_atTop 0
  obtain ⟨j₀, hj₀⟩ := hXpos.exists_forall_of_atTop
  have hX' : Tendsto (fun j => X (j + j₀)) atTop atTop := hX.comp (tendsto_add_atTop_nat j₀)
  have hY' : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X (j + j₀)) ^ p ≤ Y (j + j₀) := fun p =>
    (tendsto_add_atTop_nat j₀).eventually (hY p)
  refine windowed_lock_impossible_of_tendsto hsl hΦd hΦre hidT hGc hGd hG2 (η := 0) (K₀ := K₀)
    hwm hwb hX' hY' (fun j => hκ (j + j₀)) (fun j τ h1 h2 => ?_) ?_
  · have hτ0 : τ < 0 := by have := hj₀ (j + j₀) (by omega); linarith
    rw [hlock (j + j₀) τ h1 h2, hw, Set.indicator_of_mem (show τ ∈ Iio (0 : ℝ) from hτ0)]
    simp
  · rw [twistG_zero_eq_self]
    refine (tendsto_regular_twist_radial hsl hΦre hidT hGc hGd hG2 hLc hLd hLs hLl hden
      hrat).congr fun ε => ?_
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
    rw [hw, Set.indicator_of_mem ht]


/-! ### The margin theorem as a special case -/

/-- A uniform density margin and `L'' → 0` imply the regular-variation hypotheses, so
`regular_twist_lock_impossible` contains `margin_twist_lock_impossible`. -/
theorem regular_hyps_of_margin {L : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hmar : ∀ᶠ y in atBot, (deriv L (edgePt y)).re ≤ -c)
    (hL2 : Tendsto (fun y : ℝ => deriv (deriv L) (edgePt y)) atBot (𝓝 0)) :
    Tendsto (fun y : ℝ => y * (deriv L (edgePt y)).re) atBot atTop ∧
      Tendsto (fun y : ℝ => ‖deriv (deriv L) (edgePt y)‖ / (deriv L (edgePt y)).re ^ 2) atBot
        (𝓝 0) := by
  constructor
  · have hlin : Tendsto (fun y : ℝ => -y * c) atBot atTop :=
      (tendsto_neg_atBot_atTop.atTop_mul_const hc)
    refine tendsto_atTop_mono' _ ?_ hlin
    filter_upwards [hmar, eventually_le_atBot (0 : ℝ)] with y hy hy0
    nlinarith
  · have hlim : Tendsto (fun y : ℝ => ‖deriv (deriv L) (edgePt y)‖ / c ^ 2) atBot (𝓝 0) := by
      have := (hL2.norm).div_const (c ^ 2)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun y => by positivity) ?_ hlim
    filter_upwards [hmar] with y hy
    have hc2 : c ^ 2 ≤ (deriv L (edgePt y)).re ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hc2

end

end AbelianTwist

end RHTower
