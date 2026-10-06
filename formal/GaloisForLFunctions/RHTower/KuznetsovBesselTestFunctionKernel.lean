import GaloisForLFunctions.RHTower.KuznetsovBesselTestFunctionWeight

/-!
# The same-sign kernel of the weight of a test function

For a test function `φ` with `φ̃(1) = 0` and its same-sign weight `G_φ` (`besselWeight`), the
kernel `Ψ^{G_φ}(X) = 2 ∫ G_φ(w) tanh w sin(X cosh w) dw` is, for `X > 0`,

`Ψ^{G_φ}(X) = (π/2) φ(X)/X - ∑_{l ≥ 3 odd} π l φ̃(l) J_l(X)/X`

(`weightKernel_besselWeight`), i.e. `φ = (2X/π) Ψ^{G_φ} + ∑_{l≥3 odd} 2l φ̃(l) J_l`.

Proof: the integrand is even, and on `w > 0`,
`4 G_φ tanh w = sinh w S(cosh w) - 2 sinh w P(e^{-w})`.  The first part becomes
`∫_1^∞ S(u) sin(Xu) du = (π/2)φ(X)/X - ∫_0^{π/2} S(sin θ) sin(X sin θ) cos θ dθ` by `u = cosh w`,
sine inversion and `u = sin θ`; Jacobi–Anger expands `S(sin θ)` and `P(e^{-w})` in odd Bessel
coefficients, and the two resulting integrals combine through the sine-profile identity
`∫_0^{π/2} sin(lθ) sin(X sin θ) cos θ dθ + sin(lπ/2) ∫_0^∞ e^{-lw} sinh w sin(X cosh w) dw
  = (πl/2) J_l(X)/X` for odd `l ≥ 3`.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

variable (T : BesselTestFunction)

theorem self_le_cosh (u : ℝ) : u ≤ Real.cosh u := by
  rcases le_total u 0 with h | h
  · linarith [Real.one_le_cosh u]
  · rw [Real.cosh_eq]
    have := Real.quadratic_le_exp_of_nonneg h
    have := Real.exp_pos (-u)
    nlinarith [sq_nonneg (u - 1)]

theorem tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop :=
  tendsto_atTop_mono self_le_cosh tendsto_id

theorem continuous_tanh' : Continuous Real.tanh := by
  have : Real.tanh = fun w => Real.sinh w / Real.cosh w := funext Real.tanh_eq_sinh_div_cosh
  rw [this]
  exact Real.continuous_sinh.div Real.continuous_cosh fun w => (Real.cosh_pos w).ne'

/-! ## The angular integral -/

/-- `A_k(X) = ∫_0^{π/2} sin((2k+1)θ) sin(X sin θ) cos θ dθ`. -/
def sineProfileTheta (X : ℝ) (k : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) * (Real.sin (X * Real.sin θ) * Real.cos θ)

theorem summable_norm_besselCoeff_odd :
    Summable fun k : ℕ => ‖T.besselCoeff (2 * k + 1)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => T.norm_besselCoeff_le _) ?_
  have := T.summable_besselMajor_mul_pow 1
  simp only [one_pow, mul_one] at this
  exact this.mul_right _

/-- **`∫_0^{π/2} cos θ S(sin θ) sin(X sin θ) dθ = 2 ∑_k φ̃(2k+1) A_k(X)`.** -/
theorem hasSum_integral_theta (X : ℝ) :
    HasSum (fun k => 2 * T.besselCoeff (2 * k + 1) * (sineProfileTheta X k : ℂ))
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        (Real.cos θ : ℂ) * (T.sineTransform (Real.sin θ) * (Real.sin (X * Real.sin θ) : ℂ))) := by
  have hH := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := Real.pi / 2)
    (F := fun k θ => 2 * T.besselCoeff (2 * k + 1) *
      ((Real.sin ((2 * k + 1 : ℕ) * θ) * (Real.sin (X * Real.sin θ) * Real.cos θ) : ℝ) : ℂ))
    (f := fun θ => (Real.cos θ : ℂ) * (T.sineTransform (Real.sin θ) * (Real.sin (X * Real.sin θ) : ℂ)))
    (fun k _ => 2 * ‖T.besselCoeff (2 * k + 1)‖)
    (fun k => (Continuous.aestronglyMeasurable (by fun_prop)))
    (fun k => Eventually.of_forall fun θ _ => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, abs_mul, abs_mul]
      have h1 := Real.abs_sin_le_one ((2 * k + 1 : ℕ) * θ)
      have h2 := Real.abs_sin_le_one (X * Real.sin θ)
      have h3 := Real.abs_cos_le_one θ
      have h4 : |Real.sin ((2 * k + 1 : ℕ) * θ)| * (|Real.sin (X * Real.sin θ)| * |Real.cos θ|) ≤ 1 := by
        have := mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one) (by positivity) zero_le_one
        simpa using this
      nlinarith [norm_nonneg (T.besselCoeff (2 * k + 1))])
    (Eventually.of_forall fun _ _ => (summable_norm_besselCoeff_odd T).mul_left 2)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ => by
      have := (T.hasSum_sineTransform_sin θ).mul_right
        ((Real.sin (X * Real.sin θ) : ℂ) * (Real.cos θ : ℂ))
      rw [show (Real.cos θ : ℂ) * (T.sineTransform (Real.sin θ) * (Real.sin (X * Real.sin θ) : ℂ)) =
        T.sineTransform (Real.sin θ) * ((Real.sin (X * Real.sin θ) : ℂ) * (Real.cos θ : ℂ)) by ring]
      exact this.congr_fun fun k => by push_cast; ring)
  refine hH.congr_fun fun k => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, sineProfileTheta]

/-! ## The radial integral of the main part -/

theorem integrable_sinh_mul_sineTransform_cosh :
    Integrable fun w : ℝ => (Real.sinh w : ℂ) * T.sineTransform (Real.cosh w) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_of_mem_coshSchwartzSpan
    (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0) T.sinh_mul_sineTransform_cosh_mem 1
  refine (integrable_exp_neg_abs'.const_mul C).mono'
    (Continuous.aestronglyMeasurable (by
      have := T.continuous_sineTransform
      fun_prop)) (Eventually.of_forall fun w => ?_)
  have := hb w
  simpa using this

/-- **`∫_0^∞ sinh w S(cosh w) sin(X cosh w) dw = (π/2) ψ(X) - ∫_0^{π/2} cos θ S(sin θ) sin(X sin θ) dθ`.** -/
theorem integral_Ioi_sinh_sineTransform_cosh {X : ℝ} (hX : 0 < X) :
    ∫ w in Ioi (0 : ℝ), (Real.sinh w : ℂ) * T.sineTransform (Real.cosh w) *
        (Real.sin (X * Real.cosh w) : ℂ) =
      Real.pi / 2 * T.ψ X - ∫ θ in (0 : ℝ)..Real.pi / 2,
        (Real.cos θ : ℂ) * (T.sineTransform (Real.sin θ) * (Real.sin (X * Real.sin θ) : ℂ)) := by
  set g : ℝ → ℂ := fun u => T.sineTransform u * (Real.sin (X * u) : ℂ) with hg
  have hcS := T.continuous_sineTransform
  have hgc : Continuous g := by fun_prop
  have hgi : Integrable g :=
    T.integrable_sineTransform.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hA : Integrable fun w : ℝ => (Real.sinh w : ℂ) * T.sineTransform (Real.cosh w) *
      (Real.sin (X * Real.cosh w) : ℂ) :=
    (integrable_sinh_mul_sineTransform_cosh T).mul_bdd (c := 1)
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hsub := integral_deriv_smul_comp_Ioi (f := Real.cosh) (f' := Real.sinh) (g := g) (a := 0)
    Real.continuous_cosh.continuousOn tendsto_cosh_atTop
    (fun x _ => (Real.hasDerivAt_cosh x).hasDerivWithinAt) hgc.continuousOn hgi.integrableOn
    (by
      refine hA.integrableOn.congr_fun (fun w _ => ?_) measurableSet_Ici
      simp only [g, Function.comp, Complex.real_smul]; ring)
  have e1 : (fun x : ℝ => Real.sinh x • (g ∘ Real.cosh) x) =
      fun w => (Real.sinh w : ℂ) * T.sineTransform (Real.cosh w) * (Real.sin (X * Real.cosh w) : ℂ) := by
    funext w; simp only [g, Function.comp, Complex.real_smul]; ring
  rw [e1, Real.cosh_zero] at hsub
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hgi.integrableOn (zero_le_one' ℝ)
  have hsin := intervalIntegral.integral_deriv_smul_comp (a := 0) (b := Real.pi / 2)
    (f := Real.sin) (f' := Real.cos) (g := g) (fun x _ => Real.hasDerivAt_sin x)
    Real.continuous_cos.continuousOn hgc
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsin
  have e2 : (fun x : ℝ => Real.cos x • (g ∘ Real.sin) x) =
      fun θ => (Real.cos θ : ℂ) * (T.sineTransform (Real.sin θ) * (Real.sin (X * Real.sin θ) : ℂ)) := by
    funext θ; simp only [g, Function.comp, Complex.real_smul]
  rw [e2] at hsin
  rw [hsub, hsin, ← hsplit, T.integral_Ioi_sineTransform_mul_sin hX]
  ring

/-! ## The radial integral of the tail -/

/-- `E_k(X) = ∫_0^∞ e^{-(2k+1)w} sinh w sin(X cosh w) dw`. -/
def sineProfileExp (X : ℝ) (k : ℕ) : ℝ :=
  ∫ w in Ioi (0 : ℝ), Real.exp (-((2 * k + 1 : ℕ) * w)) * (Real.sinh w * Real.sin (X * Real.cosh w))

theorem exp_neg_mul_sinh_le {l : ℕ} (hl : 3 ≤ l) {w : ℝ} (hw : 0 < w) :
    Real.exp (-(l * w)) * Real.sinh w ≤ Real.exp (-w) := by
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  calc Real.exp (-(l * w)) * Real.sinh w ≤ Real.exp (-(l * w)) * Real.exp w := by
        gcongr; rw [Real.sinh_eq]; linarith [Real.exp_pos (-w), Real.exp_pos w]
    _ = Real.exp (-(l * w) + w) := by rw [Real.exp_add]
    _ ≤ Real.exp (-w) := Real.exp_le_exp.2 (by nlinarith)

theorem integrableOn_exp_neg_mul_sinh_sin {l : ℕ} (hl : 3 ≤ l) (X : ℝ) :
    IntegrableOn (fun w : ℝ => Real.exp (-(l * w)) * (Real.sinh w * Real.sin (X * Real.cosh w)))
      (Ioi 0) := by
  refine (integrableOn_Ioi_exp_neg 0).mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
  have hw0 : (0 : ℝ) < w := hw
  have hs := Real.sinh_nonneg_iff.2 hw0.le
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hs]
  have h1 := Real.abs_sin_le_one (X * Real.cosh w)
  calc Real.exp (-(l * w)) * (Real.sinh w * |Real.sin (X * Real.cosh w)|)
      ≤ Real.exp (-(l * w)) * (Real.sinh w * 1) := by gcongr
    _ ≤ Real.exp (-w) := by rw [mul_one]; exact exp_neg_mul_sinh_le hl hw0
where
  integrableOn_Ioi_exp_neg (a : ℝ) : IntegrableOn (fun w : ℝ => Real.exp (-w)) (Ioi a) := by
    simpa using exp_neg_integrableOn_Ioi a (by norm_num : (0 : ℝ) < 1)

theorem summable_norm_besselOddCoeff_succ :
    Summable fun k : ℕ => ‖besselOddCoeff T (k + 1)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_besselOddCoeff_le T _) ?_
  have := (T.summable_besselMajor_mul_pow 1).comp_injective Nat.succ_injective
  simp only [one_pow, mul_one] at this
  exact this.mul_right _

/-- **`∫_0^∞ sinh w P(e^{-w}) sin(X cosh w) dw = ∑_k c_{k+1} E_{k+1}(X)`** when `φ̃(1) = 0`. -/
theorem hasSum_integral_tail (h1 : T.besselCoeff 1 = 0) (X : ℝ) :
    HasSum (fun k => besselOddCoeff T (k + 1) * (sineProfileExp X (k + 1) : ℂ))
      (∫ w in Ioi (0 : ℝ), (Real.sinh w : ℂ) * T.oddSeries (Real.exp (-w)) *
        (Real.sin (X * Real.cosh w) : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun k w => besselOddCoeff T (k + 1) *
    ((Real.exp (-((2 * (k + 1) + 1 : ℕ) * w)) * (Real.sinh w * Real.sin (X * Real.cosh w)) : ℝ) : ℂ)
    with hF
  have hl : ∀ k : ℕ, 3 ≤ 2 * (k + 1) + 1 := fun k => by omega
  have hFint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k =>
    ((integrableOn_exp_neg_mul_sinh_sin (hl k) X).ofReal).const_mul _
  have hFnorm : ∀ k, ∫ w in Ioi (0 : ℝ), ‖F k w‖ ≤ ‖besselOddCoeff T (k + 1)‖ := fun k => by
    have hb : ∫ w in Ioi (0 : ℝ), ‖F k w‖ ≤ ∫ w in Ioi (0 : ℝ), ‖besselOddCoeff T (k + 1)‖ * Real.exp (-w) := by
      refine setIntegral_mono_on (hFint k).norm
        ((integrableOn_exp_neg_mul_sinh_sin.integrableOn_Ioi_exp_neg 0).const_mul _) measurableSet_Ioi
        fun w hw => ?_
      have hw0 : (0 : ℝ) < w := hw
      have hs := Real.sinh_nonneg_iff.2 hw0.le
      simp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg hs]
      have h1 := Real.abs_sin_le_one (X * Real.cosh w)
      have h2 := exp_neg_mul_sinh_le (hl k) hw0
      gcongr
      calc Real.exp (-(((2 * (k + 1) + 1 : ℕ) : ℝ) * w)) * (Real.sinh w * |Real.sin (X * Real.cosh w)|)
          ≤ Real.exp (-(((2 * (k + 1) + 1 : ℕ) : ℝ) * w)) * (Real.sinh w * 1) := by gcongr
        _ ≤ Real.exp (-w) := by rw [mul_one]; exact h2
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] at hb
    exact hb
  have hsum : Summable fun k => ∫ w in Ioi (0 : ℝ), ‖F k w‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hFnorm
      (summable_norm_besselOddCoeff_succ T)
  have hH := hasSum_integral_of_summable_integral_norm hFint hsum
  have hpt : (fun w => ∑' k, F k w) = fun w => (Real.sinh w : ℂ) * T.oddSeries (Real.exp (-w)) *
      (Real.sin (X * Real.cosh w) : ℂ) := by
    funext w
    rw [oddSeries_eq_tail T h1]
    have e : ∀ k : ℕ, F k w = besselOddCoeff T (k + 1) *
        ((Real.exp (-w) ^ (2 * (k + 1) + 1) : ℝ) : ℂ) *
          ((Real.sinh w * Real.sin (X * Real.cosh w) : ℝ) : ℂ) := fun k => by
      simp only [F]
      rw [← Real.exp_nat_mul, show ((2 * (k + 1) + 1 : ℕ) : ℝ) * -w = -(((2 * (k + 1) + 1 : ℕ) : ℝ) * w)
        by ring]
      push_cast; ring
    simp only [e]
    rw [tsum_mul_right]
    push_cast; ring
  have hval : (fun k => ∫ w in Ioi (0 : ℝ), F k w) =
      fun k => besselOddCoeff T (k + 1) * (sineProfileExp X (k + 1) : ℂ) := by
    funext k
    simp only [F]
    rw [integral_const_mul, integral_complex_ofReal, sineProfileExp]
  rw [hpt, hval] at hH
  exact hH

/-! ## The kernel identity -/

/-- **The same-sign kernel of `G_φ`**: for `X > 0`,
`Ψ^{G_φ}(X) = (π/2) ψ(X) - 2 ∑_{k} φ̃(2k+3) (π(2k+3)/2) J_{2k+3}(X)/X`. -/
theorem weightKernel_besselWeight (h1 : T.besselCoeff 1 = 0) {X : ℝ} (hX : 0 < X) :
    weightKernel (besselWeight T h1) 1 X =
      Real.pi / 2 * T.ψ X - ∑' k : ℕ, 2 * T.besselCoeff (2 * (k + 1) + 1) *
        ((Real.pi * (2 * (k + 1) + 1 : ℕ) / 2 * (besselJ (2 * (k + 1) + 1) X / X) : ℝ) : ℂ) := by
  rw [weightKernel_one _ hX, besselWeight_G]
  set W := besselWeight T h1
  set A : ℝ → ℂ := fun w => (Real.sinh w : ℂ) * T.sineTransform (Real.cosh w) *
    (Real.sin (X * Real.cosh w) : ℂ) with hAdef
  set B : ℝ → ℂ := fun w => (Real.sinh w : ℂ) * T.oddSeries (Real.exp (-w)) *
    (Real.sin (X * Real.cosh w) : ℂ) with hBdef
  have hfint : Integrable fun w => besselProfile T w * ((Real.tanh w * Real.sin (X * Real.cosh w) : ℝ) : ℂ) := by
    have := W.integrable_G
    rw [besselWeight_G] at this
    have ht := continuous_tanh'
    refine this.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun w => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc |Real.tanh w| * |Real.sin (X * Real.cosh w)| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_tanh_lt_one w).le (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have heven : ∀ w, besselProfile T (-w) * ((Real.tanh (-w) * Real.sin (X * Real.cosh (-w)) : ℝ) : ℂ) =
      besselProfile T w * ((Real.tanh w * Real.sin (X * Real.cosh w) : ℝ) : ℂ) := fun w => by
    rw [besselProfile_neg T h1, Real.tanh_neg, Real.cosh_neg]; push_cast; ring
  rw [_root_.HTGeometry.integral_even_eq_two_mul_complex hfint heven]
  have hfAB : ∀ w, besselProfile T w * ((Real.tanh w * Real.sin (X * Real.cosh w) : ℝ) : ℂ) =
      A w / 4 - B w / 2 := fun w => by
    have hc : Complex.cosh (w : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_cosh]; exact_mod_cast (Real.cosh_pos w).ne'
    simp only [A, B, besselProfile, Pi.sub_apply, mainProfile, tailProfile_eq T h1, Real.tanh_eq_sinh_div_cosh]
    push_cast
    field_simp
  have hAint : IntegrableOn A (Ioi 0) := by
    have hcS := T.continuous_sineTransform
    exact ((integrable_sinh_mul_sineTransform_cosh T).mul_bdd (c := 1)
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)).integrableOn
  have hBint : IntegrableOn B (Ioi 0) := by
    obtain ⟨C, hC, hb⟩ := exists_bound_iteratedDeriv_tailProfile T 0
    have hct : Continuous (tailProfile T) := (contDiff_tailProfile T 0).continuous
    have ht := continuous_tanh'
    have hB' : ∀ w, B w = 2 * ((Real.tanh w : ℝ) : ℂ) * tailProfile T w * (Real.sin (X * Real.cosh w) : ℂ) :=
      fun w => by
        have hc : Complex.cosh (w : ℂ) ≠ 0 := by
          rw [← Complex.ofReal_cosh]; exact_mod_cast (Real.cosh_pos w).ne'
        simp only [B, tailProfile_eq T h1, Real.tanh_eq_sinh_div_cosh]
        push_cast; field_simp
    refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 2)).const_mul (2 * C)).mono'
      (by
        rw [show B = fun w => 2 * ((Real.tanh w : ℝ) : ℂ) * tailProfile T w *
          (Real.sin (X * Real.cosh w) : ℂ) from funext hB']
        exact Continuous.aestronglyMeasurable (by fun_prop))
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_))
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    have htail := hb w hw0
    rw [iteratedDeriv_zero] at htail
    rw [hB', norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h1' := (Real.abs_tanh_lt_one w).le
    have h2' := Real.abs_sin_le_one (X * Real.cosh w)
    calc 2 * |Real.tanh w| * ‖tailProfile T w‖ * |Real.sin (X * Real.cosh w)|
        ≤ 2 * 1 * (C * Real.exp (-(2 * w))) * 1 := by gcongr
      _ = 2 * C * Real.exp (-2 * w) := by ring_nf
  have hsplitInt : ∫ w in Ioi (0 : ℝ), besselProfile T w *
      ((Real.tanh w * Real.sin (X * Real.cosh w) : ℝ) : ℂ) =
      (∫ w in Ioi (0 : ℝ), A w) / 4 - (∫ w in Ioi (0 : ℝ), B w) / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun w _ => hfAB w),
      integral_sub (hAint.div_const 4) (hBint.div_const 2), integral_div, integral_div]
  rw [hsplitInt, integral_Ioi_sinh_sineTransform_cosh T hX]
  -- the two Bessel expansions
  have hθ := hasSum_integral_theta T X
  have hθ' : HasSum (fun k => 2 * T.besselCoeff (2 * (k + 1) + 1) * (sineProfileTheta X (k + 1) : ℂ))
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        (Real.cos θ : ℂ) * (T.sineTransform (Real.sin θ) * (Real.sin (X * Real.sin θ) : ℂ))) := by
    have := (hasSum_nat_add_iff' 1).2 hθ
    simpa [h1] using this
  have hB := hasSum_integral_tail T h1 X
  have hcomb := hθ'.add (hB.mul_left 2)
  have hterm : ∀ k : ℕ, 2 * T.besselCoeff (2 * (k + 1) + 1) * (sineProfileTheta X (k + 1) : ℂ) +
      2 * (besselOddCoeff T (k + 1) * (sineProfileExp X (k + 1) : ℂ)) =
      2 * T.besselCoeff (2 * (k + 1) + 1) *
        ((Real.pi * (2 * (k + 1) + 1 : ℕ) / 2 * (besselJ (2 * (k + 1) + 1) X / X) : ℝ) : ℂ) := fun k => by
    have hprof := integral_sine_profile_eq (k := k + 1) (by omega) hX
    rw [sin_odd_mul_pi_div_two] at hprof
    rw [← hprof, sineProfileTheta, sineProfileExp, besselOddCoeff]
    push_cast
    ring
  simp only [hterm] at hcomb
  rw [hcomb.tsum_eq]
  simp only [hBdef]
  ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
