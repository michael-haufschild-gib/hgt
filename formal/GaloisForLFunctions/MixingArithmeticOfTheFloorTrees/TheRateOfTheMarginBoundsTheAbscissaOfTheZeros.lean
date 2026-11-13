import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.AUniformLowerBoundOnTheMarginForcesTheRiemannHypothesis
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormOnStepPacketsIsDeterminedByItsValuesOnWindows
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The rate of the margin bounds the abscissa of the zeros

At infinite block size the margin of a window `[−L, L]` is the second eigenvalue of its neutral
form. Its binding energy, the first eigenvalue, is at least of order `e^{L}` without hypothesis,
carried by the poles. RH is a bounded margin (`riemannHypothesis_iff_margin_bddBelow`). A margin that sinks
at a smaller exponential rate still confines the zeros:

  **if the margin of `[−L, L]` is at least `−C e^{2θL}` with `θ < ½`, every zero has
  `|Re ρ − ½| ≤ θ`** (`zetaZeroWidth_le_of_marginRate`).

So a Poincaré inequality `gap ≥ μ − C ρ^θ` with a loss `ρ^θ = o(μ)`, `ρ = e^{2L}` the ratio of the
window, is a zero-free strip; the trivial loss `μ ≍ ρ^{½}` is the trivial strip.

The plane is that of a charged even state and the antisymmetric state of the two ends at the same
lag `v`.

* **The binding state** (`twoEndSpline`): the spline `U` at `∓v/2` with equal signs. Its charges
  are `2 cosh(v/4) A(U)` (`charges_twoEndSpline`), so its pole term is at least `2 e^{v/2} A(U)²`,
  while its sum over the zeros is `2 Re S_U(0) + 2 Re S_U(v) = o(e^{v/2})`: every zero has
  `Re ρ < 1`, and dominated convergence (`tendsto_two_re_lagStructure_mul_exp`) kills every
  exponent `e^{(Re ρ − 1) v}`. Its depth `≍ e^{v/2}` beats `e^{θ v}`.
* **Parity** (`neutralForm_even_add_odd_charged`): the reflection fixes Weil's form and the
  antisymmetric state carries no charge, so the plane is diagonal for the neutral form and for the
  mass. A margin `−C e^{θ v}` on the plane forces the antisymmetric state above `−C e^{θ v}`, and
  the rate law (`zetaZeroWidth_le_iff_twoEndOdd_rate`) reads this as the zero width.
-/

open MeasureTheory Complex Filter Topology
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx)
open GaloisForLFunctions.SquareRootThreshold (lagStructure twoBump lagPoint evenCoeff)
open Zeta23

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- **The margin of `[−L, L]` is at least `−C e^{2θL}`**: every plane of smooth packets on the
window, with contacts up to `Q > e^{2L}`, contains a nonzero packet with
`N ≥ −C e^{2θL} · mass`. For `θ = 0` this is `MarginBoundedBelow C`. -/
def MarginRate (C θ : ℝ) : Prop :=
  ∀ (x y : ℝ → ℝ) (L : ℝ), ContDiff ℝ 2 x → ContDiff ℝ 2 y →
    (∀ u, L < |u| → x u = 0 ∧ y u = 0) → ∀ Q : ℕ, Real.exp (2 * L) < Q →
      ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
        -(C * Real.exp (2 * θ * L) * ∫ u, (a * x u + b * y u) ^ 2) ≤
          neutralForm Q (fun u => a * x u + b * y u)

/-! ### Lag structures grow slower than `e^{v/2}` -/

theorem re_lt_half_of_evenCoeff_ne_zero {b : ℝ → ℂ} {z : ℂ}
    (hz : evenCoeff zetaZeroConfig b z ≠ 0) : z.re < 1 / 2 := by
  rcases SquareRootThreshold.mem_of_evenCoeff_ne_zero hz with h | h
  · have := (zetaZeroConfig.strip _ h).2; simp at this; linarith
  · have := (zetaZeroConfig.strip _ h).2; simp at this; linarith

/-- **`2 Re S(v) = o(e^{v/2})`**: every exponent of the lag structure has real part below `½`. -/
theorem tendsto_two_re_lagStructure_mul_exp {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    Tendsto (fun v : ℝ => 2 * (lagStructure zetaZeroConfig b v).re * Real.exp (-(v / 2))) atTop
      (𝓝 0) := by
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  have hsum : Summable fun z : ℂ => ‖evenCoeff zetaZeroConfig b z‖ := by
    have h0 := (SquareRootThreshold.two_re_lagStructure_eq zetaZeroConfig hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hlim : Tendsto (fun v : ℝ => ∑' z : ℂ,
      evenCoeff zetaZeroConfig b z * cexp ((z - 1 / 2) * v)) atTop (𝓝 (∑' _z : ℂ, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun z => ?_) ?_
    · by_cases hz : evenCoeff zetaZeroConfig b z = 0
      · simp [hz]
      · have hre := re_lt_half_of_evenCoeff_ne_zero hz
        have hexp : Tendsto (fun v : ℝ => cexp ((z - 1 / 2) * v)) atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have e : (fun v : ℝ => ‖cexp ((z - 1 / 2) * v)‖) =
              fun v => Real.exp (-((1 / 2 - z.re) * v)) := by
            funext v
            have hv : ((z - 1 / 2) * (v : ℂ)).re = (z.re - 1 / 2) * v := by simp
            rw [Complex.norm_exp, hv]
            congr 1
            ring
          rw [e]
          exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
            (tendsto_id.const_mul_atTop (by linarith))
        simpa using hexp.const_mul (evenCoeff zetaZeroConfig b z)
    · filter_upwards [eventually_ge_atTop 0] with v hv z
      by_cases hz : evenCoeff zetaZeroConfig b z = 0
      · simp [hz]
      · have hre := re_lt_half_of_evenCoeff_ne_zero hz
        rw [norm_mul, Complex.norm_exp]
        have e : ((z - 1 / 2) * (v : ℂ)).re = (z.re - 1 / 2) * v := by simp
        rw [e]
        calc ‖evenCoeff zetaZeroConfig b z‖ * Real.exp ((z.re - 1 / 2) * v)
            ≤ ‖evenCoeff zetaZeroConfig b z‖ * 1 :=
              mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
                (mul_nonpos_of_nonpos_of_nonneg (by linarith) hv)) (norm_nonneg _)
          _ = ‖evenCoeff zetaZeroConfig b z‖ := mul_one _
  rw [tsum_zero] at hlim
  have hid : ∀ v : ℝ, ((2 * (lagStructure zetaZeroConfig b v).re * Real.exp (-(v / 2)) : ℝ) : ℂ) =
      ∑' z : ℂ, evenCoeff zetaZeroConfig b z * cexp ((z - 1 / 2) * v) := by
    intro v
    obtain ⟨_, he⟩ := SquareRootThreshold.two_re_lagStructure_eq zetaZeroConfig hZ hb hbs v
    rw [Complex.ofReal_mul, he, Complex.ofReal_exp, ← tsum_mul_right]
    refine tsum_congr fun z => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hlim' : Tendsto (fun v : ℝ =>
      ((2 * (lagStructure zetaZeroConfig b v).re * Real.exp (-(v / 2)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    simp only [hid]
    exact hlim
  have h := (Complex.continuous_re.tendsto 0).comp hlim'
  simpa using h

/-! ### The binding state of the two ends -/

theorem cx_spline_support : ∀ u, cx spline u ≠ 0 → |u| ≤ 4 := fun u hu => by
  by_contra h
  exact hu (by simp [cx, spline_eq_zero (not_le.mp h)])

theorem contDiff_cx_spline : ContDiff ℝ 2 (cx spline) :=
  Complex.ofRealCLM.contDiff.comp contDiff_spline

/-- **The binding state of the two ends**: the spline at `∓v/2` with equal signs. -/
def twoEndSpline (v u : ℝ) : ℝ := spline (u + v / 2) + spline (u - v / 2)

theorem twoEndSpline_neg (v u : ℝ) : twoEndSpline v (-u) = twoEndSpline v u := by
  unfold twoEndSpline
  rw [show -u + v / 2 = -(u - v / 2) by ring, show -u - v / 2 = -(u + v / 2) by ring,
    spline_neg, spline_neg]
  ring

theorem contDiff_twoEndSpline (v : ℝ) : ContDiff ℝ 2 (twoEndSpline v) :=
  (contDiff_spline.comp (contDiff_id.add contDiff_const)).add
    (contDiff_spline.comp (contDiff_id.sub contDiff_const))

theorem twoEndSpline_eq_zero (v : ℝ) {u : ℝ} (hu : 4 + |v| / 2 < |u|) : twoEndSpline v u = 0 := by
  have h1 : 4 < |u + v / 2| := by
    have h := abs_sub_abs_le_abs_sub u (-(v / 2))
    rw [sub_neg_eq_add, abs_neg, abs_div, abs_two] at h
    linarith
  have h2 : 4 < |u - v / 2| := by
    have h := abs_sub_abs_le_abs_sub u (v / 2)
    rw [abs_div, abs_two] at h
    linarith
  unfold twoEndSpline
  rw [spline_eq_zero h1, spline_eq_zero h2, add_zero]

theorem cx_twoEndSpline (v : ℝ) : cx (twoEndSpline v) = twoBump (cx spline) v 1 := by
  have l0 : lagPoint 2 v 0 = -(v / 2) := by
    simp only [lagPoint, Fin.val_zero, Nat.cast_zero, Nat.cast_ofNat]; ring
  have l1 : lagPoint 2 v 1 = v / 2 := by
    simp only [lagPoint, Fin.val_one, Nat.cast_one, Nat.cast_ofNat]; ring
  funext t
  simp only [twoBump, SquareRootThreshold.bumpTest, Fin.sum_univ_two, l0, l1,
    Matrix.cons_val_zero, Matrix.cons_val_one, cx, twoEndSpline, sub_neg_eq_add]
  push_cast
  ring

/-- The sum over the zeros of the binding state is `2 Re S_U(0) + 2 Re S_U(v)`. -/
theorem zeroSum_twoEndSpline (v : ℝ) :
    zeroSum (twoEndSpline v) = 2 * (lagStructure zetaZeroConfig (cx spline) 0).re +
      2 * (lagStructure zetaZeroConfig (cx spline) v).re := by
  have h := SquareRootThreshold.re_W_unit_twoBump zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_spline cx_spline_support v
    (τ := 1) (by simp)
  rw [SquareRootThreshold.conj_lagStructure_neg zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_spline cx_spline_support v,
    one_mul, Complex.add_re, ← cx_twoEndSpline] at h
  unfold zeroSum
  refine h.trans ?_
  ring

theorem integrable_mul_exp_of_vanishing {g : ℝ → ℝ} (hg : Continuous g) {L : ℝ}
    (hv : ∀ u, L < |u| → g u = 0) (s : ℝ) : Integrable fun u => g u * Real.exp (s * u) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_of_vanishing hv).mul_right

/-- `∫ g(u + c) e^{s u} du = e^{−sc} ∫ g e^{s u}`. -/
theorem integral_comp_add_mul_exp (g : ℝ → ℝ) (c s : ℝ) :
    ∫ u, g (u + c) * Real.exp (s * u) = Real.exp (-(s * c)) * ∫ u, g u * Real.exp (s * u) := by
  have h := integral_add_right_eq_self (fun u => g u * Real.exp (s * u)) c
  have e : (fun u => g (u + c) * Real.exp (s * u)) =
      fun u => Real.exp (-(s * c)) * (g (u + c) * Real.exp (s * (u + c))) := by
    funext u
    rw [show s * (u + c) = s * u + s * c by ring, Real.exp_add]
    have : Real.exp (-(s * c)) * Real.exp (s * c) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc g (u + c) * Real.exp (s * u)
        = g (u + c) * Real.exp (s * u) * (Real.exp (-(s * c)) * Real.exp (s * c)) := by
          rw [this, mul_one]
      _ = _ := by ring
  rw [e, integral_const_mul, h]

/-- The first charge of the spline. -/
def splineCharge : ℝ := ∫ u, spline u * Real.exp (-u / 2)

theorem splineCharge_ne_zero : splineCharge ≠ 0 := by
  intro h0
  have e : paperFT (cx spline) (I / 2) = ((splineCharge : ℝ) : ℂ) :=
    _root_.RHTower.WeilLevyPole.paperFT_ofReal_I_div_two spline
  have hne := SquareRootThreshold.paperFT_boxSpline_ne_zero one_pos 3
    (z := I / 2) (by simp)
  apply hne
  have : SquareRootThreshold.boxSpline 1 3 = cx spline := rfl
  rw [this, e, h0, Complex.ofReal_zero]

/-- **The charges of the binding state** are `2 cosh(v/4)` times the charge of the spline. -/
theorem charges_twoEndSpline (v : ℝ) :
    (∫ u, twoEndSpline v u * Real.exp (-u / 2)) =
        (Real.exp (v / 4) + Real.exp (-(v / 4))) * splineCharge ∧
      (∫ u, twoEndSpline v u * Real.exp (u / 2)) =
        (Real.exp (v / 4) + Real.exp (-(v / 4))) * splineCharge := by
  have hvan : ∀ u, 4 < |u| → spline u = 0 := fun u hu => spline_eq_zero hu
  have hU := integrable_mul_exp_of_vanishing contDiff_spline.continuous hvan (-1 / 2)
  have hV := integrable_mul_exp_of_vanishing contDiff_spline.continuous hvan (1 / 2)
  -- the second charge of the spline equals the first, by evenness
  have hB : ∫ u, spline u * Real.exp (1 / 2 * u) = splineCharge := by
    unfold splineCharge
    rw [← integral_neg_eq_self (fun u => spline u * Real.exp (1 / 2 * u))]
    congr 1
    funext u
    simp only [spline_neg]
    rw [show 1 / 2 * -u = -u / 2 by ring]
  have hA : ∫ u, spline u * Real.exp (-1 / 2 * u) = splineCharge := by
    unfold splineCharge
    rw [show (fun u => spline u * Real.exp (-1 / 2 * u)) = fun u => spline u * Real.exp (-u / 2)
      from funext fun u => by rw [show -1 / 2 * u = -u / 2 by ring]]
  -- the translates of the spline vanish off a window
  have hvt : ∀ c : ℝ, ∀ u, 4 + |c| < |u| → spline (u + c) = 0 := fun c u hu => spline_eq_zero (by
    have h := abs_sub_abs_le_abs_sub u (-c)
    rw [sub_neg_eq_add, abs_neg] at h
    linarith)
  have hsplit : ∀ s : ℝ,
      ∫ u, twoEndSpline v u * Real.exp (s * u) =
        (∫ u, spline (u + v / 2) * Real.exp (s * u)) +
          ∫ u, spline (u + -(v / 2)) * Real.exp (s * u) := by
    intro s
    have h1 := integrable_mul_exp_of_vanishing
      (contDiff_spline.continuous.comp (continuous_id.add continuous_const)) (hvt (v / 2)) s
    have h2 := integrable_mul_exp_of_vanishing
      (contDiff_spline.continuous.comp (continuous_id.add continuous_const)) (hvt (-(v / 2))) s
    rw [← integral_add h1 h2]
    congr 1
    funext u
    simp only [Function.comp, id, twoEndSpline, sub_eq_add_neg]
    ring
  constructor
  · have h := hsplit (-1 / 2)
    rw [integral_comp_add_mul_exp, integral_comp_add_mul_exp, hA] at h
    rw [show (fun u => twoEndSpline v u * Real.exp (-u / 2)) =
      fun u => twoEndSpline v u * Real.exp (-1 / 2 * u) from
        funext fun u => by rw [show -u / 2 = -1 / 2 * u by ring], h,
      show -(-1 / 2 * (v / 2)) = v / 4 by ring, show -(-1 / 2 * -(v / 2)) = -(v / 4) by ring]
    ring
  · have h := hsplit (1 / 2)
    rw [integral_comp_add_mul_exp, integral_comp_add_mul_exp, hB] at h
    rw [show (fun u => twoEndSpline v u * Real.exp (u / 2)) =
      fun u => twoEndSpline v u * Real.exp (1 / 2 * u) from
        funext fun u => by rw [show u / 2 = 1 / 2 * u by ring], h,
      show -(1 / 2 * (v / 2)) = -(v / 4) by ring, show -(1 / 2 * -(v / 2)) = v / 4 by ring]
    ring

/-- The mass of the binding state is at most four times that of the spline. -/
theorem integral_twoEndSpline_sq_le (v : ℝ) :
    ∫ u, twoEndSpline v u ^ 2 ≤ 4 * ∫ u, spline u ^ 2 := by
  have hc : Continuous fun u => spline u ^ 2 := contDiff_spline.continuous.pow 2
  have hi : Integrable fun u => spline u ^ 2 :=
    hc.integrable_of_hasCompactSupport (hasCompactSupport_of_vanishing (L := 4)
      fun u hu => by rw [spline_eq_zero hu]; ring)
  have hshift : ∀ c : ℝ, ∫ u, spline (u + c) ^ 2 = ∫ u, spline u ^ 2 :=
    fun c => integral_add_right_eq_self (fun u => spline u ^ 2) c
  have hi1 : Integrable fun u => 2 * spline (u + v / 2) ^ 2 :=
    (hi.comp_add_right (v / 2)).const_mul 2
  have hi2 : Integrable fun u => 2 * spline (u + -(v / 2)) ^ 2 :=
    (hi.comp_add_right (-(v / 2))).const_mul 2
  have hint : Integrable fun u => twoEndSpline v u ^ 2 :=
    ((contDiff_twoEndSpline v).continuous.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanishing (L := 4 + |v| / 2)
        fun u hu => by rw [twoEndSpline_eq_zero v hu]; ring)
  have h1 : ∫ u, (2 * spline (u + v / 2) ^ 2 + 2 * spline (u + -(v / 2)) ^ 2) =
      (∫ u, 2 * spline (u + v / 2) ^ 2) + ∫ u, 2 * spline (u + -(v / 2)) ^ 2 :=
    integral_add hi1 hi2
  calc ∫ u, twoEndSpline v u ^ 2 ≤
        ∫ u, (2 * spline (u + v / 2) ^ 2 + 2 * spline (u + -(v / 2)) ^ 2) :=
        integral_mono hint (hi1.add hi2) fun u => by
          simp only [twoEndSpline, sub_eq_add_neg]
          nlinarith [sq_nonneg (spline (u + v / 2) - spline (u + -(v / 2)))]
    _ = 4 * ∫ u, spline u ^ 2 := by
        rw [h1, integral_const_mul, integral_const_mul, hshift, hshift]
        ring

/-! ### Parity with a charged even part -/

/-- On a packet of the window, Weil's form `𝔚` is Weil's quadratic form of the real tests. -/
theorem packetForm_eq_weilQuad {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {L : ℝ}
    (hv : ∀ u, L < |u| → g u = 0) {Q : ℕ} (hQ : Real.exp (2 * L) < Q) :
    packetForm Q g = SpacingScaleHarmonicAnalysis.weilQuad g := by
  rw [← zeroSum_eq_packetForm hg (hasCompactSupport_of_vanishing hv)
    (packetAutocorr_log_eq_zero_of_vanishing hv hQ),
    ArithmeticCastelnuovoSeveri.LogCells.weilQuad_eq_zetaW hg (hasCompactSupport_of_vanishing hv)]
  rfl

/-- **On the plane of an even packet and an odd pole-free packet the neutral form is diagonal**,
even when the even packet carries charges: `N(e + t o) = N(e) + t² N(o)`. The reflection kills the
cross term of Weil's form, and the odd packet adds nothing to the charges. -/
theorem neutralForm_even_add_odd_charged {e o : ℝ → ℝ} (he : ContDiff ℝ 2 e)
    (ho : ContDiff ℝ 2 o) {L : ℝ} (hv : ∀ u, L < |u| → e u = 0 ∧ o u = 0)
    (heven : ∀ u, e (-u) = e u) (hodd : ∀ u, o (-u) = -o u)
    (hAo : ∫ u, o u * Real.exp (-u / 2) = 0) {Q : ℕ} (hQ : Real.exp (2 * L) < Q) (t : ℝ) :
    neutralForm Q (fun u => e u + t * o u) = neutralForm Q e + t ^ 2 * neutralForm Q o := by
  have hve : ∀ u, L < |u| → e u = 0 := fun u hu => (hv u hu).1
  have hvo : ∀ u, L < |u| → o u = 0 := fun u hu => (hv u hu).2
  have hvs : ∀ s : ℝ, ∀ u, L < |u| → e u + s * o u = 0 := fun s u hu => by
    rw [(hv u hu).1, (hv u hu).2, mul_zero, add_zero]
  have hsmooth : ∀ s : ℝ, ContDiff ℝ 2 fun u => e u + s * o u := fun s =>
    he.add (contDiff_const.mul ho)
  have hreal : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, L < |u| → f u = 0) →
      f ∈ ArithmeticCastelnuovoSeveri.realTests := fun f hf hfv =>
    ⟨hf, hasCompactSupport_of_vanishing hfv⟩
  have hexp := CohomologyOfWindowsOfSpecZ.weilQuad_add_smul (hreal e he hve) (hreal o ho hvo)
  -- the reflection kills the cross term
  have hrefl : packetForm Q (fun u => e u + 1 * o u) = packetForm Q (fun u => e u + -1 * o u) := by
    have h := packetForm_reflect Q 0 (fun u => e u + 1 * o u)
    have hr : reflectPacket 0 (fun u => e u + 1 * o u) = fun u => e u + -1 * o u := by
      funext u
      simp only [reflectPacket, zero_sub, heven, hodd]
      ring
    rw [hr] at h
    exact h.symm
  rw [packetForm_eq_weilQuad (hsmooth 1) (hvs 1) hQ, packetForm_eq_weilQuad (hsmooth (-1)) (hvs (-1)) hQ,
    hexp 1, hexp (-1)] at hrefl
  have hP : ArithmeticCastelnuovoSeveri.weilPair e o = 0 := by linarith
  -- the odd packet carries no charge
  have hBo : ∫ u, o u * Real.exp (u / 2) = 0 := by
    rw [integral_mul_exp_of_odd (c := 0) fun u => by rw [zero_sub]; exact hodd u, hAo, mul_zero,
      neg_zero]
  have hie := integrable_mul_exp_of_vanishing he.continuous hve
  have hio := integrable_mul_exp_of_vanishing ho.continuous hvo
  have hcharge : ∀ s : ℝ, (∫ u, (e u + t * o u) * Real.exp (s * u)) =
      (∫ u, e u * Real.exp (s * u)) + t * ∫ u, o u * Real.exp (s * u) := fun s => by
    have e1 : (fun u => (e u + t * o u) * Real.exp (s * u)) =
        fun u => e u * Real.exp (s * u) + t * (o u * Real.exp (s * u)) := by
      funext u; ring
    rw [e1, integral_add (hie s) ((hio s).const_mul t), integral_const_mul]
  have hA1 := hcharge (-1 / 2)
  have hB1 := hcharge (1 / 2)
  have hneg : ∀ g : ℝ → ℝ, (∫ u, g u * Real.exp (-u / 2)) = ∫ u, g u * Real.exp (-1 / 2 * u) :=
    fun g => by
      rw [show (fun u => g u * Real.exp (-u / 2)) = fun u => g u * Real.exp (-1 / 2 * u) from
        funext fun u => by rw [show -u / 2 = -1 / 2 * u by ring]]
  have hpos : ∀ g : ℝ → ℝ, (∫ u, g u * Real.exp (u / 2)) = ∫ u, g u * Real.exp (1 / 2 * u) :=
    fun g => by
      rw [show (fun u => g u * Real.exp (u / 2)) = fun u => g u * Real.exp (1 / 2 * u) from
        funext fun u => by rw [show u / 2 = 1 / 2 * u by ring]]
  have hAo' : ∫ u, o u * Real.exp (-1 / 2 * u) = 0 := by rw [← hneg]; exact hAo
  have hBo' : ∫ u, o u * Real.exp (1 / 2 * u) = 0 := by rw [← hpos]; exact hBo
  rw [hAo', mul_zero, add_zero] at hA1
  rw [hBo', mul_zero, add_zero] at hB1
  unfold neutralForm
  rw [packetForm_eq_weilQuad (hsmooth t) (hvs t) hQ, packetForm_eq_weilQuad he hve hQ,
    packetForm_eq_weilQuad ho hvo hQ, hexp t, hP, hneg, hpos, hneg, hpos, hneg, hpos, hA1, hB1,
    hAo', hBo']
  ring

/-! ### The theorem -/

/-- **A margin of exponential rate `θ < ½` confines the zeros to the strip `|Re ρ − ½| ≤ θ`.** -/
theorem zetaZeroWidth_le_of_marginRate {C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (h : MarginRate C θ) : SquareRootThreshold.zetaZeroWidth ≤ θ := by
  -- constants
  obtain ⟨S0, hS0⟩ : ∃ S, S = 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re :=
    ⟨_, rfl⟩
  obtain ⟨T0, hT0⟩ : ∃ S, S = 2 * (lagStructure zetaZeroConfig (cx spline) 0).re := ⟨_, rfl⟩
  obtain ⟨m₀, hm₀⟩ : ∃ m, m = ∫ u, poleFreeProfile u ^ 2 := ⟨_, rfl⟩
  obtain ⟨mU, hmU⟩ : ∃ m, m = ∫ u, spline u ^ 2 := ⟨_, rfl⟩
  have hm₀0 : 0 ≤ m₀ := by rw [hm₀]; exact integral_nonneg fun u => sq_nonneg _
  have hmU0 : 0 ≤ mU := by rw [hmU]; exact integral_nonneg fun u => sq_nonneg _
  obtain ⟨E, hE⟩ : ∃ E, E = |C| * Real.exp (10 * θ) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hA2 : 0 < 2 * splineCharge ^ 2 := by
    have := pow_pos (abs_pos.mpr splineCharge_ne_zero) 2
    rw [_root_.sq_abs] at this
    linarith
  -- the binding state is eventually deeper than the allowed margin
  have hdeep : ∀ᶠ v : ℝ in atTop,
      T0 + 2 * (lagStructure zetaZeroConfig (cx spline) v).re + 4 * E * mU * Real.exp (θ * v) <
        2 * splineCharge ^ 2 * Real.exp (v / 2) := by
    have h1 := tendsto_two_re_lagStructure_mul_exp contDiff_cx_spline cx_spline_support
    have h2 : Tendsto (fun v : ℝ => Real.exp (-(v / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num))
    have h3 : Tendsto (fun v : ℝ => Real.exp (-((1 / 2 - θ) * v))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by linarith))
    have hF := ((h2.const_mul T0).add h1).add (h3.const_mul (4 * E * mU))
    simp only [mul_zero, add_zero] at hF
    filter_upwards [hF.eventually (gt_mem_nhds hA2)] with v hv
    have hv' : T0 * Real.exp (-(v / 2)) +
        2 * (lagStructure zetaZeroConfig (cx spline) v).re * Real.exp (-(v / 2)) +
        4 * E * mU * Real.exp (-((1 / 2 - θ) * v)) < 2 * splineCharge ^ 2 := hv
    have he : 0 < Real.exp (v / 2) := Real.exp_pos _
    have e1 : Real.exp (-(v / 2)) * Real.exp (v / 2) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have e2 : Real.exp (-((1 / 2 - θ) * v)) * Real.exp (v / 2) = Real.exp (θ * v) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmul := mul_lt_mul_of_pos_right hv' he
    have e3 : (T0 * Real.exp (-(v / 2)) +
          2 * (lagStructure zetaZeroConfig (cx spline) v).re * Real.exp (-(v / 2)) +
          4 * E * mU * Real.exp (-((1 / 2 - θ) * v))) * Real.exp (v / 2) =
        T0 + 2 * (lagStructure zetaZeroConfig (cx spline) v).re + 4 * E * mU * Real.exp (θ * v) := by
      rw [← e2]
      linear_combination (T0 + 2 * (lagStructure zetaZeroConfig (cx spline) v).re) * e1
    rw [e3] at hmul
    linarith
  obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp hdeep
  -- on the plane of the two states the antisymmetric state stays above the margin
  have hodd : ∀ v : ℝ, max V₁ 0 ≤ v →
      2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re ≤
        S0 + 4 * E * m₀ * Real.exp (θ * v) := by
    intro v hv
    have hv0 : 0 ≤ v := (le_max_right _ _).trans hv
    have hvV : V₁ ≤ v := (le_max_left _ _).trans hv
    obtain ⟨L, hL⟩ : ∃ L, L = 5 + v / 2 := ⟨_, rfl⟩
    have hvan : ∀ u, L < |u| → twoEndSpline v u = 0 ∧ twoEndOdd v u = 0 := fun u hu =>
      ⟨twoEndSpline_eq_zero v (by rw [abs_of_nonneg hv0]; linarith),
        twoEndOdd_eq_zero v (by rw [abs_of_nonneg hv0]; linarith)⟩
    have hvx : ∀ u, L < |u| → twoEndSpline v u = 0 := fun u hu => (hvan u hu).1
    have hvy : ∀ u, L < |u| → twoEndOdd v u = 0 := fun u hu => (hvan u hu).2
    obtain ⟨Q, hQ⟩ := exists_nat_gt (Real.exp (2 * L))
    obtain ⟨a, b, hab, hineq⟩ := h (twoEndSpline v) (twoEndOdd v) L (contDiff_twoEndSpline v)
      (contDiff_twoEndOdd v) hvan Q hQ
    -- the plane is diagonal for the form and for the mass
    have hmass := integral_even_add_odd_sq (contDiff_twoEndSpline v).continuous
      (contDiff_twoEndOdd v).continuous hvan (twoEndSpline_neg v) (twoEndOdd_neg v) a b
    have hform : neutralForm Q (fun u => a * twoEndSpline v u + b * twoEndOdd v u) =
        a ^ 2 * neutralForm Q (twoEndSpline v) + b ^ 2 * neutralForm Q (twoEndOdd v) := by
      by_cases ha : a = 0
      · subst ha
        have e1 : (fun u => 0 * twoEndSpline v u + b * twoEndOdd v u) =
            fun u => b * twoEndOdd v u := by funext u; ring
        rw [e1, neutralForm_smul]
        ring
      · have e1 : (fun u => a * twoEndSpline v u + b * twoEndOdd v u) =
            fun u => a * (twoEndSpline v u + b / a * twoEndOdd v u) := by
          funext u; field_simp
        have hab2 : a ^ 2 * (b / a) ^ 2 = b ^ 2 := by rw [← mul_pow, mul_div_cancel₀ b ha]
        rw [e1, neutralForm_smul, neutralForm_even_add_odd_charged (contDiff_twoEndSpline v)
          (contDiff_twoEndOdd v) hvan (twoEndSpline_neg v) (twoEndOdd_neg v) (charge_twoEndOdd v)
          hQ (b / a), mul_add, ← mul_assoc, hab2]
    rw [hform, hmass] at hineq
    -- the two diagonal entries
    have hNy := neutralForm_twoEndOdd v (packetAutocorr_log_eq_zero_of_vanishing hvy hQ)
    rw [← hS0] at hNy
    have hNx : neutralForm Q (twoEndSpline v) ≤
        T0 + 2 * (lagStructure zetaZeroConfig (cx spline) v).re -
          2 * splineCharge ^ 2 * Real.exp (v / 2) := by
      obtain ⟨hA, hB⟩ := charges_twoEndSpline v
      unfold neutralForm
      rw [← zeroSum_eq_packetForm (contDiff_twoEndSpline v)
        (hasCompactSupport_of_vanishing hvx) (packetAutocorr_log_eq_zero_of_vanishing hvx hQ),
        zeroSum_twoEndSpline, ← hT0, hA, hB]
      have hcosh : Real.exp (v / 2) ≤ (Real.exp (v / 4) + Real.exp (-(v / 4))) ^ 2 := by
        have h1 : Real.exp (v / 2) = Real.exp (v / 4) ^ 2 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [h1]
        have := Real.exp_pos (-(v / 4))
        have := Real.exp_pos (v / 4)
        nlinarith
      have := mul_le_mul_of_nonneg_left hcosh (sq_nonneg splineCharge)
      nlinarith
    have hmx := integral_twoEndSpline_sq_le v
    have hmy := integral_twoEndOdd_sq_le v
    rw [← hmU] at hmx
    rw [← hm₀] at hmy
    have hmx0 : 0 ≤ ∫ u, twoEndSpline v u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hmy0 : 0 ≤ ∫ u, twoEndOdd v u ^ 2 := integral_nonneg fun u => sq_nonneg _
    -- the allowed depth on this window
    have hexpL : Real.exp (2 * θ * L) = Real.exp (10 * θ) * Real.exp (θ * v) := by
      rw [← Real.exp_add]; congr 1; rw [hL]; ring
    obtain ⟨D, hD⟩ : ∃ D, D = |C| * Real.exp (2 * θ * L) := ⟨_, rfl⟩
    have hDE : D = E * Real.exp (θ * v) := by rw [hD, hexpL, hE]; ring
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hCD : C * Real.exp (2 * θ * L) ≤ D := by
      rw [hD]; exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    -- the binding state is below `−D` times its mass
    have hxdeep : neutralForm Q (twoEndSpline v) + D * ∫ u, twoEndSpline v u ^ 2 < 0 := by
      have h1 := hV₁ v hvV
      have h2 : D * ∫ u, twoEndSpline v u ^ 2 ≤ 4 * E * mU * Real.exp (θ * v) := by
        rw [hDE]
        have := mul_le_mul_of_nonneg_left hmx (mul_nonneg hE0 (Real.exp_pos (θ * v)).le)
        linarith
      linarith
    -- hence the antisymmetric state is above `−D` times its mass
    have hyup : 0 ≤ neutralForm Q (twoEndOdd v) + D * ∫ u, twoEndOdd v u ^ 2 := by
      by_contra hneg
      push Not at hneg
      have hsum : a ^ 2 * (neutralForm Q (twoEndSpline v) + D * ∫ u, twoEndSpline v u ^ 2) +
          b ^ 2 * (neutralForm Q (twoEndOdd v) + D * ∫ u, twoEndOdd v u ^ 2) < 0 := by
        rcases hab with ha | hb
        · have ha2 : 0 < a ^ 2 := by
            have := pow_pos (abs_pos.mpr ha) 2
            rwa [_root_.sq_abs] at this
          have := mul_neg_of_pos_of_neg ha2 hxdeep
          have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) hneg.le
          linarith
        · have hb2 : 0 < b ^ 2 := by
            have := pow_pos (abs_pos.mpr hb) 2
            rwa [_root_.sq_abs] at this
          have := mul_neg_of_pos_of_neg hb2 hneg
          have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hxdeep.le
          linarith
      have hmass0 : 0 ≤ a ^ 2 * (∫ u, twoEndSpline v u ^ 2) + b ^ 2 * ∫ u, twoEndOdd v u ^ 2 :=
        add_nonneg (mul_nonneg (sq_nonneg a) hmx0) (mul_nonneg (sq_nonneg b) hmy0)
      have hCm := mul_le_mul_of_nonneg_right hCD hmass0
      linarith
    rw [hNy] at hyup
    have h3 : D * ∫ u, twoEndOdd v u ^ 2 ≤ 4 * E * m₀ * Real.exp (θ * v) := by
      rw [hDE]
      have := mul_le_mul_of_nonneg_left hmy (mul_nonneg hE0 (Real.exp_pos (θ * v)).le)
      linarith
    linarith
  -- small lags: the trivial bound `2 Re S(v) ≤ K e^{v/2}`
  obtain ⟨K, hK⟩ : ∃ K, K = ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (cx poleFreeProfile) z‖ :=
    ⟨_, rfl⟩
  refine (zetaZeroWidth_le_iff_twoEndOdd_rate hθ0 hθ).mpr
    ⟨4 * E * m₀ + |S0| + K * Real.exp (|V₁| / 2), fun v hv Q hQ => ?_⟩
  rw [neutralForm_twoEndOdd v hQ, ← hS0]
  have he1 : 1 ≤ Real.exp (θ * v) := Real.one_le_exp (mul_nonneg hθ0 hv)
  have hK0 : 0 ≤ K := by rw [hK]; exact tsum_nonneg fun _ => norm_nonneg _
  have hKV : 0 ≤ K * Real.exp (|V₁| / 2) := mul_nonneg hK0 (Real.exp_pos _).le
  have hS1 : |S0| ≤ |S0| * Real.exp (θ * v) := le_mul_of_one_le_right (abs_nonneg _) he1
  have hK1 : K * Real.exp (|V₁| / 2) ≤ K * Real.exp (|V₁| / 2) * Real.exp (θ * v) :=
    le_mul_of_one_le_right hKV he1
  have hrhs : (4 * E * m₀ + |S0| + K * Real.exp (|V₁| / 2)) * Real.exp (θ * v) =
      4 * E * m₀ * Real.exp (θ * v) + |S0| * Real.exp (θ * v) +
        K * Real.exp (|V₁| / 2) * Real.exp (θ * v) := by ring
  rw [hrhs]
  rcases le_or_gt (max V₁ 0) v with hvV | hvV
  · have := hodd v hvV
    have h0 : 0 ≤ K * Real.exp (|V₁| / 2) * Real.exp (θ * v) :=
      mul_nonneg hKV (Real.exp_pos _).le
    linarith [le_abs_self S0, neg_abs_le S0]
  · have h1 := SquareRootThreshold.two_re_lagStructure_le_mul_exp zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
      cx_poleFreeProfile_support (τ := 1 / 2)
      (fun z hz => SquareRootThreshold.re_le_of_evenCoeff_ne_zero hz) hv
    rw [← hK] at h1
    have h2 : K * Real.exp (1 / 2 * v) ≤ K * Real.exp (|V₁| / 2) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
      have := (le_max_left V₁ 0)
      have := le_abs_self V₁
      have := lt_max_iff.mp hvV
      rcases this with h | h
      · linarith
      · linarith
    have h3 : 0 ≤ 4 * E * m₀ * Real.exp (θ * v) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hE0) hm₀0) (Real.exp_pos _).le
    linarith [le_abs_self S0, neg_abs_le S0]

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
