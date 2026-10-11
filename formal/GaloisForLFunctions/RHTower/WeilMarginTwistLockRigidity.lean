import GaloisForLFunctions.RHTower.WeilDecayingTwistLockRigidity

/-!
# Locks of positive density margin are impossible

Let `G` be a Herglotz producer and `L` holomorphic on `Re s > ½`, continuous on `Re s ≥ ½`, with
`Re L ≤ A` on the lower strip `½ ≤ Re s ≤ 3/2`, `Im s ≤ −1`, and on the lower critical line.
Suppose that on the edge `Re s = 3/2`, as `y → −∞`,

`Re L'(3/2 + iy) ≤ −c < 0`  and  `L''(3/2 + iy) → 0`.

**Theorem** (`margin_twist_lock_impossible`).  No Herglotz producer satisfies the lower-line lock
`G(1 − s) = κ₀ e^{L(s)} G(s)`, `s = ½ + 2iτ`, `τ < 0`.

For a lock phase `θ(x)` (`x = −τ`) with holomorphic extension `L = iΘ(i(s − ½)/2)`, one has
`L' = −Θ'/2`, so the hypotheses say: the spectral density `θ'/2π` of the lock has a positive lower
bound and varies slowly.  The density may oscillate forever (log-periodic densities
`ρ₀ + a sin(β log x)`, `ρ₀ > |a|`), which neither the linear quantization theorem nor the
decaying-twist theorem covers.  It contains the positive linear slopes and the constant-rate
evaporation twists.

**Proof.**
* On `Re s = 3/2` the twisted edge integrand is `Σ_n a(n) n^{−s} e^{L(s)} k_τ(s)`, and
  `k_τ(3/2 + iy) = c_τ e^{yκ_τ} + O(e^{πy})` with `Im κ_τ = log‖τ‖`, `Re κ_τ ≥ δ`
  (`norm_offKernel_three_halves_sub_le`).
* The `n`-th leading term is `∫_{y ≤ B} e^{h(y)} dy` with `h(y) = L(3/2 + iy) + y(κ_τ − i log n)`.
  Its frequency is `Im h' = Re L' + log‖τ‖ − log n ≤ −c/2` for every `n ≥ 1`, so integration by
  parts (`norm_integral_Iic_exp_le_of_margin`) bounds it by `e^{A}/m + e^{A}‖L''‖_∞/(m²δ)`,
  `m = c/2`.  No term resonates.
* Below the height where `‖L''‖ ≤ η'`, `ε` times the right edge is `O(ε) + O(η')`.  So the twisted
  radial integral tends to `0`, while Hamburger's reflected radial limit is `2β ≠ 0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

theorem hasDerivAt_edgePt (y : ℝ) : HasDerivAt edgePt I y := by
  have h := ((hasDerivAt_id (y : ℂ)).comp_ofReal.mul_const I).const_add (((3 / 2 : ℝ) : ℂ))
  simp only [id, one_mul] at h
  exact h

theorem continuous_edgePt : Continuous edgePt := by unfold edgePt; fun_prop

/-! ### Integration by parts on the right edge -/

/-- **Integration by parts on the right edge.**  Let `h(y) = L(3/2 + iy) + y w` with `Re w > 0`,
`Re L ≤ A`, `‖h'‖ ≥ m` and `‖L''‖ ≤ D` on `y ≤ B`.  Then
`‖∫_{y ≤ B} e^{h}‖ ≤ e^{A} e^{B Re w}/m + (D/m²) e^{A} e^{B Re w}/Re w`. -/
theorem norm_integral_Iic_exp_le_of_margin {L L1 L2 : ℂ → ℂ} {w : ℂ} (hw : 0 < w.re)
    {B A m D : ℝ} (hm : 0 < m)
    (h1 : ∀ y : ℝ, y ≤ B → HasDerivAt L (L1 (edgePt y)) (edgePt y))
    (h2 : ∀ y : ℝ, y ≤ B → HasDerivAt L1 (L2 (edgePt y)) (edgePt y))
    (hc2 : ∀ y : ℝ, y ≤ B → ContinuousAt L2 (edgePt y))
    (hA : ∀ y : ℝ, y ≤ B → (L (edgePt y)).re ≤ A)
    (hmar : ∀ y : ℝ, y ≤ B → m ≤ ‖I * L1 (edgePt y) + w‖)
    (hD : ∀ y : ℝ, y ≤ B → ‖L2 (edgePt y)‖ ≤ D) :
    ‖∫ y in Iic B, cexp (L (edgePt y) + (y : ℂ) * w)‖ ≤
      Real.exp A * Real.exp (w.re * B) / m +
        D / m ^ 2 * (Real.exp A * (Real.exp (w.re * B) / w.re)) := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD B le_rfl)
  set hf : ℝ → ℂ := fun y => L (edgePt y) + (y : ℂ) * w with hhf
  set gf : ℝ → ℂ := fun y => I * L1 (edgePt y) + w with hgf
  set Wf : ℝ → ℂ := fun y => cexp (hf y) * L2 (edgePt y) / gf y ^ 2 with hWf
  set Uf : ℝ → ℂ := fun y => cexp (hf y) / gf y with hUf
  have hg0 : ∀ y : ℝ, y ≤ B → gf y ≠ 0 := by
    intro y hy h
    have := hmar y hy
    rw [show I * L1 (edgePt y) + w = gf y from rfl, h, norm_zero] at this
    linarith
  have hhd : ∀ y : ℝ, y ≤ B → HasDerivAt hf (gf y) y := by
    intro y hy
    have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * w) w y := by
      simpa using ((hasDerivAt_id (y : ℂ)).comp_ofReal).mul_const w
    have h := ((h1 y hy).comp y (hasDerivAt_edgePt y)).add hlin
    refine h.congr_deriv ?_
    simp only [hgf]; ring
  have hgd : ∀ y : ℝ, y ≤ B → HasDerivAt gf (-(L2 (edgePt y))) y := by
    intro y hy
    have h := (((h2 y hy).comp y (hasDerivAt_edgePt y)).const_mul I).add_const w
    refine h.congr_deriv ?_
    rw [mul_comm (L2 (edgePt y)) I, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hUd : ∀ y : ℝ, y ≤ B → HasDerivAt Uf (cexp (hf y) + Wf y) y := by
    intro y hy
    have h := ((hhd y hy).cexp).div (hgd y hy) (hg0 y hy)
    refine h.congr_deriv ?_
    simp only [hWf]
    have hg := hg0 y hy
    field_simp
    ring
  have hexp_le : ∀ y : ℝ, y ≤ B → ‖cexp (hf y)‖ ≤ Real.exp A * Real.exp (w.re * y) := by
    intro y hy
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : (hf y).re = (L (edgePt y)).re + w.re * y := by
      simp only [hhf, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    rw [this]; linarith [hA y hy]
  have hW_le : ∀ y : ℝ, y ≤ B → ‖Wf y‖ ≤ D / m ^ 2 * (Real.exp A * Real.exp (w.re * y)) := by
    intro y hy
    simp only [hWf]
    rw [norm_div, norm_mul, norm_pow]
    have hgm : m ^ 2 ≤ ‖gf y‖ ^ 2 := by
      have := hmar y hy
      exact pow_le_pow_left₀ hm.le this 2
    calc ‖cexp (hf y)‖ * ‖L2 (edgePt y)‖ / ‖gf y‖ ^ 2
        ≤ (Real.exp A * Real.exp (w.re * y)) * D / m ^ 2 := by
          gcongr
          · exact hexp_le y hy
          · exact hD y hy
      _ = _ := by ring
  have hexpInt : IntegrableOn (fun y : ℝ => Real.exp (w.re * y)) (Iic B) := by
    have h : IntegrableOn (fun y : ℝ => ‖cexp ((w.re : ℂ) * (y : ℂ))‖) (Iic B) :=
      (integrableOn_exp_mul_complex_Iic (a := (w.re : ℂ)) (by simpa using hw) B).norm
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [Complex.norm_exp]
    congr 1; simp
  have hcont_h : ContinuousOn (fun y => cexp (hf y)) (Iic B) := fun y hy =>
    ((hhd y hy).cexp).continuousAt.continuousWithinAt
  have hcont_g : ContinuousOn gf (Iic B) := fun y hy => (hgd y hy).continuousAt.continuousWithinAt
  have hcont_L2 : ContinuousOn (fun y => L2 (edgePt y)) (Iic B) := fun y hy =>
    ((hc2 y hy).comp continuous_edgePt.continuousAt).continuousWithinAt
  have hcont_W : ContinuousOn Wf (Iic B) := by
    refine ((hcont_h.mul hcont_L2).div (hcont_g.pow 2) fun y hy => ?_)
    exact pow_ne_zero 2 (hg0 y hy)
  have hint_h : IntegrableOn (fun y => cexp (hf y)) (Iic B) :=
    (hexpInt.const_mul (Real.exp A)).mono' (hcont_h.aestronglyMeasurable measurableSet_Iic)
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => hexp_le y hy))
  have hint_W : IntegrableOn Wf (Iic B) :=
    ((hexpInt.const_mul (Real.exp A)).const_mul (D / m ^ 2)).mono'
      (hcont_W.aestronglyMeasurable measurableSet_Iic)
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => by
        simpa [mul_assoc] using hW_le y hy))
  have hU_lim : Tendsto Uf atBot (𝓝 0) := by
    have hlim : Tendsto (fun y : ℝ => Real.exp A * Real.exp (w.re * y) / m) atBot (𝓝 0) := by
      have h : Tendsto (fun y : ℝ => w.re * y) atBot atBot := tendsto_id.const_mul_atBot hw
      have h2 := ((Real.tendsto_exp_atBot.comp h).const_mul (Real.exp A)).div_const m
      simpa using h2
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_le_atBot B] with y hy
    simp only [hUf]
    rw [norm_div]
    have hgm := hmar y hy
    calc ‖cexp (hf y)‖ / ‖gf y‖ ≤ Real.exp A * Real.exp (w.re * y) / m := by
          gcongr
          exact hexp_le y hy
      _ = _ := rfl
  have hFTC : ∫ y in Iic B, (cexp (hf y) + Wf y) = Uf B - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto (hUd B le_rfl).continuousAt.continuousWithinAt
      (fun y hy => hUd y (le_of_lt hy)) (hint_h.add hint_W) hU_lim
  have hsplit : ∫ y in Iic B, cexp (hf y) = Uf B - ∫ y in Iic B, Wf y := by
    have h' := integral_add hint_h hint_W
    rw [hFTC, sub_zero] at h'
    rw [h']; ring
  have hgoal : ∫ y in Iic B, cexp (L (edgePt y) + (y : ℂ) * w) = ∫ y in Iic B, cexp (hf y) := rfl
  rw [hgoal, hsplit]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · simp only [hUf]
    rw [norm_div]
    have hgm := hmar B le_rfl
    calc ‖cexp (hf B)‖ / ‖gf B‖ ≤ Real.exp A * Real.exp (w.re * B) / m := by
          gcongr
          exact hexp_le B le_rfl
      _ = _ := rfl
  · have hdom : IntegrableOn (fun y : ℝ => D / m ^ 2 * (Real.exp A * Real.exp (w.re * y)))
        (Iic B) := (hexpInt.const_mul (Real.exp A)).const_mul (D / m ^ 2)
    refine (norm_integral_le_of_norm_le hdom ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall fun y hy => hW_le y hy))).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_const_mul, integral_exp_mul_Iic_real hw]

/-! ### The twisted Dirichlet terms on the right edge -/

/-- The `n`-th twisted right-edge term `∫_{y ≤ B} a(n) n^{−s} e^{L(s)} k_τ(s) dy`, `s = 3/2 + iy`. -/
def expEdgeTerm (a : ℕ → ℂ) (L : ℂ → ℂ) (τ : ℂ) (B : ℝ) (n : ℕ) : ℂ :=
  ∫ y in Iic B, LSeries.term a (edgePt y) n * cexp (L (edgePt y)) * offKernel τ (edgePt y)

theorem term_edgePt_eq {a : ℕ → ℂ} {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    LSeries.term a (edgePt y) n =
      LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) := by
  have hn0 : n ≠ 0 := by omega
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0, edgePt,
    Complex.cpow_add _ _ hnc, natCast_cpow_eq_exp hn ((y : ℂ) * I), div_mul_eq_div_div,
    div_eq_mul_inv _ (cexp _), ← Complex.exp_neg]

/-- **The margin bound for one twisted term.**  If `Re L' ≤ −c` and `‖L''‖ ≤ D` on `y ≤ B` and
`log‖τ‖ ≤ c/2`, the `n`-th term (`n ≥ 1`) is at most
`‖a(n) n^{−3/2}‖ (2‖τ‖^{1/2}(e^{A}e^{Bκ}/(c/2) + D e^{A} e^{Bκ}/((c/2)²κ)) + 4e^{A}‖τ‖^{1/2}e^{πB}/π)`,
`κ = Re κ_τ`. -/
theorem norm_expEdgeTerm_le (a : ℕ → ℂ) {L L1 L2 : ℂ → ℂ} {τ : ℂ} (hτ : 0 < τ.re) {n : ℕ}
    (hn : 1 ≤ n) {B A c D : ℝ} (hB : B ≤ -1) (hc : 0 < c)
    (h1 : ∀ y : ℝ, y ≤ B → HasDerivAt L (L1 (edgePt y)) (edgePt y))
    (h2 : ∀ y : ℝ, y ≤ B → HasDerivAt L1 (L2 (edgePt y)) (edgePt y))
    (hc2 : ∀ y : ℝ, y ≤ B → ContinuousAt L2 (edgePt y))
    (hA : ∀ y : ℝ, y ≤ B → (L (edgePt y)).re ≤ A)
    (hmar : ∀ y : ℝ, y ≤ B → (L1 (edgePt y)).re ≤ -c)
    (hD : ∀ y : ℝ, y ≤ B → ‖L2 (edgePt y)‖ ≤ D) (hτc : Real.log ‖τ‖ ≤ c / 2) :
    ‖expEdgeTerm a L τ B n‖ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ *
      (2 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp A * Real.exp ((edgeExp τ).re * B) / (c / 2) +
        D / (c / 2) ^ 2 * (Real.exp A * (Real.exp ((edgeExp τ).re * B) / (edgeExp τ).re))) +
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
    ((h1 y hy).continuousAt).comp continuous_edgePt.continuousAt
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
  -- the leading integral by parts
  have hmargin : ∀ y : ℝ, y ≤ B → c / 2 ≤ ‖I * L1 (edgePt y) + w‖ := by
    intro y hy
    have him : (I * L1 (edgePt y) + w).im = (L1 (edgePt y)).re + (Real.log ‖τ‖ - Real.log n) := by
      rw [Complex.add_im, hwim]; simp
    have h := Complex.abs_im_le_norm (I * L1 (edgePt y) + w)
    rw [him] at h
    have hneg : (L1 (edgePt y)).re + (Real.log ‖τ‖ - Real.log n) ≤ -(c / 2) := by
      linarith [hmar y hy]
    rw [abs_of_neg (by linarith)] at h
    linarith
  have hIBP := norm_integral_Iic_exp_le_of_margin (by rw [hwre]; exact hκ) (half_pos hc) h1 h2
    hc2 hA hmargin hD
  rw [hwre] at hIBP
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
      ≤ ‖T₀‖ * (2 * ‖τ‖ ^ (1 / 2 : ℝ)) *
          (Real.exp A * Real.exp ((edgeExp τ).re * B) / (c / 2) +
            D / (c / 2) ^ 2 * (Real.exp A * (Real.exp ((edgeExp τ).re * B) / (edgeExp τ).re))) +
        ‖T₀‖ * (Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * B) / Real.pi))) := by
        gcongr
    _ = _ := by ring


/-- **Dirichlet expansion of the twisted right edge** below a height `B ≤ −1` where `Re L ≤ A`. -/
theorem hasSum_expEdgeTerm {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B A : ℝ} (hB : B ≤ -1)
    (hLc : ∀ y : ℝ, y ≤ B → ContinuousAt L (edgePt y))
    (hA : ∀ y : ℝ, y ≤ B → (L (edgePt y)).re ≤ A) :
    HasSum (expEdgeTerm (dirichletExp (lamLog lam)) L τ B)
      (∫ y in Iic B, edgeIntegrand (expTwistG L G) τ (edgePt y)) := by
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have h32 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by simp; norm_num
  have hSa : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ := (hLa _ h32).1.norm
  have hkint := integrableOn_offKernel_edgePt hτre hτ1 hB
  have hWc : ContinuousOn (fun y : ℝ => cexp (L (edgePt y))) (Iic B) := fun y hy =>
    (Complex.continuous_exp.continuousAt.comp
      ((hLc y hy).comp continuous_edgePt.continuousAt)).continuousWithinAt
  have hpt : ∀ n y, y ≤ B → ‖LSeries.term a (edgePt y) n * cexp (L (edgePt y)) *
      offKernel τ (edgePt y)‖ ≤
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp A * ‖offKernel τ (edgePt y)‖ := by
    intro n y hy
    rw [norm_mul, norm_mul, norm_term_edgePt, Complex.norm_exp]
    gcongr
    exact hA y hy
  have hFint : ∀ n, Integrable (fun y => LSeries.term a (edgePt y) n * cexp (L (edgePt y)) *
      offKernel τ (edgePt y)) (volume.restrict (Iic B)) := by
    intro n
    refine (hkint.norm.const_mul (‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp A)).mono'
      ((((continuous_term_edgePt a n).continuousOn.mul hWc).mul
        (continuous_offKernel_edgePt hτ0).continuousOn).aestronglyMeasurable measurableSet_Iic)
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => hpt n y hy))
  have hFnorm : ∀ n, ∫ y in Iic B, ‖LSeries.term a (edgePt y) n * cexp (L (edgePt y)) *
      offKernel τ (edgePt y)‖ ≤
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp A *
        ∫ y in Iic B, ‖offKernel τ (edgePt y)‖ := by
    intro n
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hFint n).norm (hkint.norm.const_mul _) measurableSet_Iic
      fun y hy => hpt n y hy
  have hsum : Summable fun n => ∫ y in Iic B, ‖LSeries.term a (edgePt y) n *
      cexp (L (edgePt y)) * offKernel τ (edgePt y)‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) hFnorm
      ((hSa.mul_right _).mul_right _)
  have hsumm : Summable (expEdgeTerm a L τ B) :=
    Summable.of_norm_bounded hsum fun n => norm_integral_le_integral_norm _
  have hedge : ∀ y, edgeIntegrand (expTwistG L G) τ (edgePt y) =
      ∑' n, LSeries.term a (edgePt y) n * cexp (L (edgePt y)) * offKernel τ (edgePt y) := by
    intro y
    have h1 : 1 < (edgePt y).re := by rw [edgePt_re]; norm_num
    unfold edgeIntegrand
    rw [prodF_expTwistG, prodF_eq_zetaOf hsl hid hGd hG2 h1, ← (hLa _ h1).2, LSeries,
      ← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext n; ring
  have hint : ∫ y in Iic B, edgeIntegrand (expTwistG L G) τ (edgePt y) =
      ∑' n, expEdgeTerm a L τ B n := by
    simp only [hedge, expEdgeTerm]
    exact (integral_tsum_of_summable_integral_norm hFint hsum).symm
  rw [hint]
  exact hsumm.hasSum


/-! ### The right edge below the margin height -/

/-- **The twisted right edge.**  Suppose `Re L ≤ A` on the lower strip, and `Re L' ≤ −c`,
`‖L''‖ ≤ η'` on the edge below `−Y`.  For `τ` with `Re τ > 0`, `1 ≤ ‖τ‖ ≤ 2` and
`log‖τ‖ ≤ c/2` the right edge `∫_{y ≤ −2}` of `e^{L} G` is at most
`S_a e^{A}(8/c + 16η'/(c²δ) + 8/π) + e^{S} K‖τ‖ e^{A}(Y − 2)`, `δ = Re τ/‖τ‖`. -/
theorem norm_margin_rightEdge_le {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s)
    (hd1 : ∀ y : ℝ, HasDerivAt L (deriv L (edgePt y)) (edgePt y))
    (hd2 : ∀ y : ℝ, HasDerivAt (deriv L) (deriv (deriv L) (edgePt y)) (edgePt y))
    (hc2 : ∀ y : ℝ, ContinuousAt (deriv (deriv L)) (edgePt y)) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    {c η' Y : ℝ} (hc : 0 < c) (hη' : 0 < η') (hY2 : 2 ≤ Y)
    (htail : ∀ y : ℝ, y ≤ -Y →
      (deriv L (edgePt y)).re ≤ -c ∧ ‖deriv (deriv L) (edgePt y)‖ ≤ η')
    {τ : ℂ} (hτre0 : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) (hτ2 : ‖τ‖ ≤ 2) (hτc : Real.log ‖τ‖ ≤ c / 2) :
    ‖∫ y in Iic (-2 : ℝ), edgeIntegrand (expTwistG L G) τ (edgePt y)‖ ≤
      (∑' n, ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖) *
        (Real.exp A * (8 / c + 16 * η' / (c ^ 2 * (τ.re / ‖τ‖)) + 8 / Real.pi)) +
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
  have hHc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt H s := fun s hs =>
    continuousAt_expTwistG hGc hLc hs
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
  have hec : Continuous fun y : ℝ => edgeIntegrand H τ (edgePt y) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : (edgePt y).re = 3 / 2 := edgePt_re y
    have h0 : edgePt y ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [hre] at this; simp at this
    have h1 : edgePt y ≠ 1 := fun h => by
      have := congrArg Complex.re h; rw [hre] at this; norm_num at this
    refine ContinuousAt.comp (g := edgeIntegrand H τ) ?_ continuous_edgePt.continuousAt
    exact (continuousAt_prodF hHc (by rw [hre]; norm_num) h0 h1).mul
      (differentiableAt_offKernel hτ0 (by rw [hre]; norm_num) (by rw [hre]; norm_num)).continuousAt
  have heint : IntegrableOn (fun y : ℝ => edgeIntegrand H τ (edgePt y)) (Iic (-2)) := by
    refine ((integrableOn_exp_neg_abs_mul_Iic hδ0 (by norm_num : (-2 : ℝ) ≤ 0)).const_mul
      (eA * (Real.exp S * (K * ‖τ‖)))).mono' hec.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => ?_))
    have hy' : y ≤ -2 := hy
    refine (hedge0 y (by linarith)).trans ?_
    have h0 : 0 ≤ Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := by positivity
    calc _ ≤ eA * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) :=
          mul_le_mul_of_nonneg_right (hLe y (by linarith)) h0
      _ = _ := by ring
  have hdisj : Disjoint (Iic (-Y)) (Ioc (-Y) (-2 : ℝ)) :=
    Set.disjoint_left.mpr fun y h1 h2 => absurd (show y ≤ -Y from h1) (not_le.mpr h2.1)
  set X' : ℝ := eA * (8 / c + 16 * η' / (c ^ 2 * δ) + 8 / Real.pi) with hX'
  have hterm : ∀ n : ℕ, ‖expEdgeTerm a L τ (-Y) n‖ ≤
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * X' := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      have : expEdgeTerm a L τ (-Y) 0 = 0 := by simp [expEdgeTerm]
      rw [this, norm_zero]
      exact mul_nonneg (norm_nonneg _) (by positivity)
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    refine (norm_expEdgeTerm_le a hτre0 hn1 (by linarith) hc (fun y _ => hd1 y)
      (fun y _ => hd2 y) (fun y _ => hc2 y)
      (fun y hy => hLs _ (by rw [edgePt_re]; norm_num) (by rw [edgePt_re])
        (by rw [hedge_im]; linarith))
      (fun y hy => (htail y hy).1) (fun y hy => (htail y hy).2) hτc).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hE1 : Real.exp ((edgeExp τ).re * -Y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hE2 : Real.exp (Real.pi * -Y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hE1' : Real.exp ((edgeExp τ).re * -Y) / (edgeExp τ).re ≤ 1 / δ := by
      rw [div_le_div_iff₀ hκ0 hδ0]; nlinarith [Real.exp_pos ((edgeExp τ).re * -Y)]
    have hb1 : eA * Real.exp ((edgeExp τ).re * -Y) / (c / 2) ≤ eA * (2 / c) := by
      rw [div_le_iff₀ (by positivity)]
      have : eA * (2 / c) * (c / 2) = eA := by field_simp
      rw [this]
      exact mul_le_of_le_one_right heA0.le hE1
    have hb2 : η' / (c / 2) ^ 2 * (eA * (Real.exp ((edgeExp τ).re * -Y) / (edgeExp τ).re)) ≤
        η' / (c / 2) ^ 2 * (eA * (1 / δ)) := by gcongr
    have hb3 : Real.exp (Real.pi * -Y) / Real.pi ≤ 1 / Real.pi := by gcongr
    have hsum1 : eA * Real.exp ((edgeExp τ).re * -Y) / (c / 2) +
        η' / (c / 2) ^ 2 * (eA * (Real.exp ((edgeExp τ).re * -Y) / (edgeExp τ).re)) ≤
        eA * (2 / c) + η' / (c / 2) ^ 2 * (eA * (1 / δ)) := add_le_add hb1 hb2
    have hpos1 : 0 ≤ eA * Real.exp ((edgeExp τ).re * -Y) / (c / 2) +
        η' / (c / 2) ^ 2 * (eA * (Real.exp ((edgeExp τ).re * -Y) / (edgeExp τ).re)) := by
      positivity
    calc 2 * ‖τ‖ ^ (1 / 2 : ℝ) * (eA * Real.exp ((edgeExp τ).re * -Y) / (c / 2) +
          η' / (c / 2) ^ 2 * (eA * (Real.exp ((edgeExp τ).re * -Y) / (edgeExp τ).re))) +
          eA * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * -Y) / Real.pi))
        ≤ 2 * 2 * (eA * (2 / c) + η' / (c / 2) ^ 2 * (eA * (1 / δ))) +
          eA * (4 * 2 * (1 / Real.pi)) := by
          have h1 : 2 * ‖τ‖ ^ (1 / 2 : ℝ) * (eA * Real.exp ((edgeExp τ).re * -Y) / (c / 2) +
              η' / (c / 2) ^ 2 * (eA * (Real.exp ((edgeExp τ).re * -Y) / (edgeExp τ).re))) ≤
              2 * 2 * (eA * (2 / c) + η' / (c / 2) ^ 2 * (eA * (1 / δ))) :=
            mul_le_mul (by linarith) hsum1 hpos1 (by norm_num)
          have h2 : eA * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * -Y) / Real.pi)) ≤
              eA * (4 * 2 * (1 / Real.pi)) := by
            gcongr
          linarith
      _ = X' := by rw [hX']; field_simp; ring
  have htail_bd : ‖∫ y in Iic (-Y), edgeIntegrand H τ (edgePt y)‖ ≤ Sa * X' := by
    have hhs : HasSum (expEdgeTerm a L τ (-Y))
        (∫ y in Iic (-Y), edgeIntegrand H τ (edgePt y)) :=
      hasSum_expEdgeTerm hsl hid hGd hG2 hτre0 hτ1 (by linarith)
        (fun y hy => hLc _ (by rw [edgePt_re]; norm_num))
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

/-- **The far part.**  Under the hypotheses of `norm_margin_rightEdge_le`, for `0 < ε ≤ min 1 c`,
`ε ‖∫_{t ≤ −1} e^{L(½+2it)} φ(t) k(2t, ε + i) dt‖ ≤ C₁ η' + (C₂ + C₃ Y) ε`. -/
theorem norm_margin_far_le {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ L s)
    (hd1 : ∀ y : ℝ, HasDerivAt L (deriv L (edgePt y)) (edgePt y))
    (hd2 : ∀ y : ℝ, HasDerivAt (deriv L) (deriv (deriv L) (edgePt y)) (edgePt y))
    (hc2 : ∀ y : ℝ, ContinuousAt (deriv (deriv L)) (edgePt y)) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    {c η' Y : ℝ} (hc : 0 < c) (hη' : 0 < η') (hY2 : 2 ≤ Y)
    (htail : ∀ y : ℝ, y ≤ -Y →
      (deriv L (edgePt y)).re ≤ -c ∧ ‖deriv (deriv L) (edgePt y)‖ ≤ η')
    {CF₀ : ℝ} (hCF₀ : 0 ≤ CF₀)
    (hF₀ : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF₀ * (1 + |y|) ^ (1 / 2 : ℝ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hεc : ε ≤ c) :
    ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))‖ ≤
      (∑' n, ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖) * Real.exp A *
          (4 / c + 4 / Real.pi) * ε +
        16 * (∑' n, ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖) *
          Real.exp A / c ^ 2 * η' +
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
  have hHc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt H s := fun s hs =>
    continuousAt_expTwistG hGc hLc hs
  have hHd := fun (s : ℂ) (hs : 1 / 2 < s.re) => hasDerivAt_expTwistG hGd hLd hs
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
  have hτc : Real.log ‖τ‖ ≤ c / 2 := by
    have h : Real.log ‖τ‖ ≤ Real.log ((1 : ℕ) : ℝ) + ε ^ 2 / 2 :=
      (log_norm_eps_add_mI_le (ε := ε) (le_refl 1)).2
    rw [Nat.cast_one, Real.log_one, zero_add] at h
    have : ε ^ 2 ≤ ε * c := by nlinarith
    nlinarith
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
    · exact ((continuous_phiG hHc).mul (continuous_pairKernel_two_mul hτ0)).aestronglyMeasurable
    · have ht0 : t < 0 := lt_of_le_of_lt ht (by norm_num)
      rw [hH, phiG_expTwistG, mul_assoc, norm_mul, Complex.norm_exp]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hLl t ht0)) (norm_nonneg _)
  have hcont := setIntegral_Iic_radial_eq_of_lower hHc hHd hCF0 hF hτre0 hτ1 hedge le_rfl hfint
  have hrewrite : ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) τ) =
      ∫ t in Iic (-1 : ℝ), phiG H t * pairKernel (2 * t) τ := by
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    rw [hH, phiG_expTwistG]; ring
  rw [hrewrite, hcont]
  have hright0 := norm_margin_rightEdge_le hsl hid hGc hGd hG2 hLc hd1 hd2 hc2 hLs hc hη' hY2
    htail hτre0 hτ1 hτ2 hτc
  have hright : ‖∫ y in Iic (2 * (-1 : ℝ)),
      edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      Sa * (eA * (8 / c + 16 * η' / (c ^ 2 * δ) + 8 / Real.pi)) +
        Real.exp S * K * ‖τ‖ * eA * (Y - 2) := by
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
  have ta : ε * (1 / 2) * (Sa * (eA * (8 / c + 16 * η' / (c ^ 2 * δ) + 8 / Real.pi))) ≤
      Sa * eA * (4 / c + 4 / Real.pi) * ε + 16 * Sa * eA / c ^ 2 * η' := by
    have e1 : ε * (1 / 2) * (Sa * (eA * (8 / c + 16 * η' / (c ^ 2 * δ) + 8 / Real.pi))) =
        Sa * eA * (4 / c + 4 / Real.pi) * ε + (8 * Sa * eA / c ^ 2 * η') * (ε * (1 / δ)) := by
      field_simp; ring
    rw [e1]
    have h' : (8 * Sa * eA / c ^ 2 * η') * (ε * (1 / δ)) ≤ (8 * Sa * eA / c ^ 2 * η') * 2 :=
      mul_le_mul_of_nonneg_left hεδ (by positivity)
    have h'' : (8 * Sa * eA / c ^ 2 * η') * 2 = 16 * Sa * eA / c ^ 2 * η' := by ring
    linarith
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
      ≤ ε * (1 / 2 * ((Sa * (eA * (8 / c + 16 * η' / (c ^ 2 * δ) + 8 / Real.pi)) +
          Real.exp S * K * ‖τ‖ * eA * (Y - 2)) + CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2))) := by
        gcongr
        exact htri.trans (add_le_add hright htop)
    _ = ε * (1 / 2) * (Sa * (eA * (8 / c + 16 * η' / (c ^ 2 * δ) + 8 / Real.pi))) +
          ε * (1 / 2) * (Real.exp S * K * ‖τ‖ * eA * (Y - 2)) +
          ε * (1 / 2) * (CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2)) := by ring
    _ ≤ Sa * eA * (4 / c + 4 / Real.pi) * ε + 16 * Sa * eA / c ^ 2 * η' +
          Real.exp S * K * eA * Y * ε + eA * CF₀ * (1 + 2) ^ (1 / 2 : ℝ) * K * ε := by
        rw [tc]; linarith [ta, tb]


/-! ### The twisted radial integral vanishes -/

/-- **The margin-twist radial integral tends to `0`.** -/
theorem tendsto_margin_twist_radial {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A) {c : ℝ} (hc : 0 < c)
    (hmar : ∀ᶠ y in atBot, (deriv L (edgePt y)).re ≤ -c)
    (hL2 : Tendsto (fun y : ℝ => deriv (deriv L) (edgePt y)) atBot (𝓝 0)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  obtain ⟨CF₀, hCF₀, hF₀⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  -- derivatives of `L` on the edge
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hLon : DifferentiableOn ℂ L U := fun s hs => (hLd s hs).differentiableWithinAt
  have hL1on : DifferentiableOn ℂ (deriv L) U := hLon.deriv hUo
  have hL2on : DifferentiableOn ℂ (deriv (deriv L)) U := hL1on.deriv hUo
  have hmem : ∀ y : ℝ, edgePt y ∈ U := fun y => by
    show (1 / 2 : ℝ) < (edgePt y).re
    rw [edgePt_re]; norm_num
  have hd1 : ∀ y : ℝ, HasDerivAt L (deriv L (edgePt y)) (edgePt y) := fun y =>
    (hLd _ (hmem y)).hasDerivAt
  have hd2 : ∀ y : ℝ, HasDerivAt (deriv L) (deriv (deriv L) (edgePt y)) (edgePt y) := fun y =>
    ((hL1on _ (hmem y)).differentiableAt (hUo.mem_nhds (hmem y))).hasDerivAt
  have hc2 : ∀ y : ℝ, ContinuousAt (deriv (deriv L)) (edgePt y) := fun y =>
    ((hL2on _ (hmem y)).differentiableAt (hUo.mem_nhds (hmem y))).continuousAt
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
    set C₁ : ℝ := 16 * Sa * eA / c ^ 2 with hC₁
    have hC₁0 : 0 ≤ C₁ := by positivity
    set η' : ℝ := e / (4 * (C₁ + 1)) with hη'
    have hη'0 : 0 < η' := by positivity
    have hev := hmar.and (hL2.eventually (Metric.closedBall_mem_nhds (0 : ℂ) hη'0))
    obtain ⟨a₀, ha₀⟩ := Filter.eventually_atBot.mp hev
    set Y : ℝ := max 2 (-a₀) with hY
    have hY2 : 2 ≤ Y := le_max_left _ _
    have htail : ∀ y : ℝ, y ≤ -Y →
        (deriv L (edgePt y)).re ≤ -c ∧ ‖deriv (deriv L) (edgePt y)‖ ≤ η' := by
      intro y hy
      have h := ha₀ y (by have := le_max_right 2 (-a₀); linarith)
      refine ⟨h.1, ?_⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using h.2
    set C₂ : ℝ := Sa * eA * (4 / c + 4 / Real.pi) + Real.exp S * K * eA * Y +
      eA * CF₀ * (1 + 2) ^ (1 / 2 : ℝ) * K with hC₂
    have hC₂0 : 0 ≤ C₂ := by positivity
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (min 1 c) (e / (2 * (C₂ + 1))) by
      positivity)] with ε hε
    rw [dist_zero_right]
    have hε1 : ε ≤ 1 := hε.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hεc : ε ≤ c := hε.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hb := norm_margin_far_le hsl hΦre hid hGc hGd hG2 hLc hLd hd1 hd2 hc2 hLs hLl hc hη'0
      hY2 htail hCF₀ hF₀ hε.1 hε1 hεc
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
  have hHc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt (expTwistG L G) s := fun s hs =>
    continuousAt_expTwistG hGc hLc hs
  have hint : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Iio 0) := by
    have h := ((MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
      hτre).norm.const_mul eA).integrableOn (s := Iio (0 : ℝ))
    refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Iio).mpr
      (Eventually.of_forall fun t ht => ?_))
    · have hc : Continuous fun t : ℝ => phiG (expTwistG L G) t * pairKernel (2 * t) τ :=
        (continuous_phiG hHc).mul (continuous_pairKernel_two_mul hτ0)
      refine (hc.congr fun t => ?_).aestronglyMeasurable
      rw [phiG_expTwistG]; ring
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

/-- **Locks of positive density margin are impossible.**  Let `L` be holomorphic on `Re s > ½`,
continuous on `Re s ≥ ½`, with `Re L ≤ A` on the lower strip and the lower line,
`Re L'(3/2 + iy) ≤ −c < 0` for all sufficiently negative `y`, and `L''(3/2 + iy) → 0` as
`y → −∞`.  Then no Herglotz producer satisfies `G(1 − s) = κ₀ e^{L(s)} G(s)` at `s = ½ + 2iτ`,
`τ < 0`. -/
theorem margin_twist_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A) {c : ℝ} (hc : 0 < c)
    (hmar : ∀ᶠ y in atBot, (deriv L (edgePt y)).re ≤ -c)
    (hL2 : Tendsto (fun y : ℝ => deriv (deriv L) (edgePt y)) atBot (𝓝 0))
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
    have h := (tendsto_margin_twist_radial hsl hΦre hidT hGc hGd hG2 hLc hLd hLs hLl hc hmar
      hL2).const_mul κ₀
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

/-- **Windowed margin locks are impossible.**  The lock of `margin_twist_lock_impossible` holding
only on windows `−Y_j ≤ τ ≤ −X_j` (`X_j → ∞`, `Y_j ≥ (1 + X_j)^p` eventually for every `p`,
`‖κ_j‖ ≤ K₀`) is already impossible. -/
theorem windowed_margin_twist_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A) {c : ℝ} (hc : 0 < c)
    (hmar : ∀ᶠ y in atBot, (deriv L (edgePt y)).re ≤ -c)
    (hL2 : Tendsto (fun y : ℝ => deriv (deriv L) (edgePt y)) atBot (𝓝 0))
    {K₀ : ℝ} {X Y : ℕ → ℝ} {κ : ℕ → ℂ}
    (hX : Tendsto X atTop atTop) (hY : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X j) ^ p ≤ Y j)
    (hκ : ∀ j, ‖κ j‖ ≤ K₀)
    (hlock : ∀ j, ∀ τ : ℝ, -Y j ≤ τ → τ ≤ -X j →
      G (1 - lineS τ) = κ j * cexp (L (lineS τ)) * G (lineS τ)) :
    False := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  set w : ℝ → ℂ := (Iio (0 : ℝ)).indicator fun τ => cexp (L (lineS τ)) with hw
  have hwc : Continuous fun τ : ℝ => cexp (L (lineS τ)) := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    have hl : Continuous lineS := by unfold lineS; fun_prop
    exact Complex.continuous_exp.continuousAt.comp
      ((hLc _ (le_of_eq (lineS_re τ).symm)).comp hl.continuousAt)
  have hwm : AEStronglyMeasurable w volume :=
    (hwc.measurable.indicator measurableSet_Iio).aestronglyMeasurable
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
    refine (tendsto_margin_twist_radial hsl hΦre hidT hGc hGd hG2 hLc hLd hLs hLl hc hmar
      hL2).congr fun ε => ?_
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
    rw [hw, Set.indicator_of_mem ht]

end

end AbelianTwist

end RHTower
