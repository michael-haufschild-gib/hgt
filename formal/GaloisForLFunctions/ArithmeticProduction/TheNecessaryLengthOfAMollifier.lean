import GaloisForLFunctions.ArithmeticProduction.TheInterpolationAtALargeHeight

/-!
# The necessary length of a mollifier

**Theorem** (`necessary_length`).  For every `θ > 0` and all large `T`, every real Dirichlet polynomial `M` of length `N ≤ T^θ` with `b₁ = 1`,
`|b_n| ≤ 1` satisfies

  `∫_T^{2T} |ζ(½+it) M(½+it)|² dt ≥ (1 + 1/(8 + 6θ)) T`.

A mollified second moment tending to `1` therefore forces the length exponent to infinity
(`length_exponent_tendsto_of_second_moment_tendsto_one`).  Three ingredients enter:

* the floors `∫|ζM(½+a+it)|² ≳ T` (first moment) and `∫|ζM(½−a+it)|² ≳ e^{2a log T} T` (Littlewood and the count of zeros);
* the profile `x ↦ ∫|F(½+x+it)|²` is a Laplace transform of a measure on `u ∈ [0, log(T²N^{3/2})]`;
* the interpolation `e^{La}Φ(a) + e^{−La}Φ(−a) ≤ 2cosh(aL)Φ(0)` at `aL ≈ log 2` forbids the kink between the two floors.

The only fact about the zeros that enters is their number; no bound on pair correlation is used.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-- `2 cosh(log 2) = 5/2`. -/
private theorem two_mul_cosh_log_two : 2 * Real.cosh (Real.log 2) = 5 / 2 := by
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log two_pos]
  norm_num

/-- The mollified zeta function is continuous along a vertical line away from the pole. -/
theorem continuous_norm_sq_zeta_mul_edPoly (b : ℕ → ℂ) (N : ℕ) {c : ℝ} (hc : c ≠ 1) :
    Continuous fun t : ℝ => ‖riemannZeta ((c : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hG : Continuous fun t : ℝ => riemannZeta ((c : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) ((c : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : (c : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hc this
    have h1 : ContinuousAt (fun s : ℂ => riemannZeta s * edPoly b (Finset.Icc 1 N) s)
        ((c : ℂ) + (t : ℂ) * I) :=
      (differentiableAt_riemannZeta hne).continuousAt.mul
        (differentiable_edPoly b (fun n hn => (Finset.mem_Icc.mp hn).1) _).continuousAt
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
      (g := fun s : ℂ => riemannZeta s * edPoly b (Finset.Icc 1 N) s) h1 (by fun_prop)
  exact hG.norm.pow 2

/-- The second moment of the body on the line is below that of `ζM`. -/
theorem integral_linePower_zero_le (b : ℕ → ℂ) (N : ℕ) {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    (∫ t in T₁..T₂, linePower b N 0 t) ≤
      ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
  intervalIntegral.integral_mono_on h
    ((continuous_linePower b N (by norm_num)).intervalIntegrable _ _)
    ((continuous_norm_sq_zeta_mul_edPoly b N (by norm_num)).intervalIntegrable _ _)
    fun t _ => linePower_zero_le b N t

/-- Left of the line, the second moment of the body is that of `ζM` up to `1 − ε`, at large heights. -/
theorem le_integral_linePower_left (b : ℕ → ℂ) (N : ℕ) {ε a T₁ T₂ : ℝ} (hε : 0 < ε) (ha0 : 0 < a)
    (ha1 : a ≤ 1 / 4) (hT12 : T₁ ≤ T₂) (hT₁ : 2 ≤ T₁) (hTε : 4 / ε ≤ T₁) :
    (1 - ε) * (∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      ∫ t in T₁..T₂, linePower b N (-a) t := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hT12
    ((continuous_const.mul
      (continuous_norm_sq_zeta_mul_edPoly b N (by linarith))).intervalIntegrable _ _)
    ((continuous_linePower b N (by linarith)).intervalIntegrable _ _) fun t ht => ?_
  have ht2 : 2 ≤ t := hT₁.trans ht.1
  have h3 := le_linePower_left b N ha0.le (by linarith) ht2
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) h3
  have h4 : 4 / t ^ 2 ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    have h5 := (div_le_iff₀ hε).mp hTε
    have h6 : T₁ ≤ t ^ 2 := by
      have h7 : t * 1 ≤ t * t := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h8 : t ^ 2 = t * t := by ring
      rw [h8]
      linarith [ht.1]
    have h9 := mul_le_mul_of_nonneg_right h6 hε.le
    linarith
  linarith

/-- A part of the Gaussian integral of the body left of the line is below the whole window. -/
theorem integral_gauss_linePower_left_le (t₀ : ℝ) {w a T₁ T₂ : ℝ} {b : ℕ → ℂ} {N : ℕ} (hw : 0 < w)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hT12 : T₁ ≤ T₂) (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∫ t in T₁..T₂, linePower b N (-a) t * gaussKernel w t t₀) ≤
      ∫ t, ‖lineFun (mollifiedWindow t₀ w b N) (-a) t‖ ^ 2 := by
  obtain ⟨Cs, hCs⟩ := exists_stripDecay_mollifiedWindow t₀ hw hb
  have hmem : -a ∈ Icc (-1 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
  have hint : Integrable fun t => ‖lineFun (mollifiedWindow t₀ w b N) (-a) t‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (hCs.continuous_lineFun hmem).aestronglyMeasurable).mp
      (hCs.memLp_two_lineFun hmem)
  rw [intervalIntegral.integral_of_le hT12]
  refine le_trans ?_ (setIntegral_le_integral (s := Ioc T₁ T₂) hint
    (Filter.Eventually.of_forall fun t => by
      show 0 ≤ _
      positivity))
  have hc : Continuous fun t => linePower b N (-a) t * gaussKernel w t t₀ :=
    (continuous_linePower b N (by linarith)).mul
      ((continuous_gaussKernel_uncurry w).comp (continuous_id.prodMk continuous_const))
  refine setIntegral_mono_on (hc.continuousOn.integrableOn_compact isCompact_Icc
    |>.mono_set Ioc_subset_Icc_self) hint.integrableOn measurableSet_Ioc fun t _ => ?_
  rw [norm_sq_lineFun_mollifiedWindow t₀ hw]
  have hE : 1 ≤ Real.exp ((-a) ^ 2 / w ^ 2) := Real.one_le_exp (by positivity)
  have hnn : 0 ≤ linePower b N (-a) t * gaussKernel w t t₀ :=
    mul_nonneg (linePower_nonneg _ _ _ _) (gaussKernel_pos _ _ _).le
  calc linePower b N (-a) t * gaussKernel w t t₀
      ≤ linePower b N (-a) t * gaussKernel w t t₀ * Real.exp ((-a) ^ 2 / w ^ 2) :=
        le_mul_of_one_le_right hnn hE
    _ = _ := by ring

/-- The floor of the window right of the line, in the form with one small parameter. -/
theorem le_integral_window_right {t₀ w a K ε : ℝ} {b : ℕ → ℂ} {N : ℕ} (ht₀ : 0 < t₀) (hw : 0 < w)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hK : 5 ≤ K) (hN : 1 ≤ N) (hb1 : b 1 = 1)
    (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2000)
    (he : Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
      (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2)))) ≤ ε / 8)
    (hw4 : 1 / (4 * ε) ≤ w ^ 2) :
    (1 - ε) * (w * √Real.pi) ≤ ∫ t, ‖lineFun (mollifiedWindow t₀ w b N) a t‖ ^ 2 := by
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
      (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2)))) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  rw [← hedef] at he
  have hfloor := right_floor (a := a) (K := K) ht₀ hw ha0.le (by linarith) hK hN hb1 hb
    (by rw [← hedef]; linarith)
  rw [← hedef] at hfloor
  have hz : a ^ 2 / w ^ 2 ≤ ε / 4 := by
    have h3 : a ^ 2 ≤ 1 / 16 := by
      calc a ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ ha0.le ha1 2
        _ = 1 / 16 := by norm_num
    have h4 : 0 < w ^ 2 := by positivity
    rw [div_le_iff₀ h4]
    have h5 := (div_le_iff₀ (by positivity : 0 < 4 * ε)).mp hw4
    have h6 : ε / 4 * w ^ 2 = (w ^ 2 * (4 * ε)) / 16 := by ring
    rw [h6]
    linarith
  have hz0 : 0 ≤ a ^ 2 / w ^ 2 := by positivity
  have hfac : 1 - ε ≤ (1 - e) ^ 2 * Real.exp (-(a ^ 2 / w ^ 2)) := by
    have h3 : 1 - a ^ 2 / w ^ 2 ≤ Real.exp (-(a ^ 2 / w ^ 2)) := by
      linarith [Real.add_one_le_exp (-(a ^ 2 / w ^ 2))]
    have h4 : 1 - 2 * e ≤ (1 - e) ^ 2 := by
      have h9 : (1 - e) ^ 2 = 1 - 2 * e + e ^ 2 := by ring
      rw [h9]
      linarith [sq_nonneg e]
    have h5 : 0 ≤ 1 - 2 * e := by linarith
    have h6 : 0 ≤ 1 - a ^ 2 / w ^ 2 := by linarith
    have h7 : 0 ≤ e * (a ^ 2 / w ^ 2) := mul_nonneg he0 hz0
    have h8 : (1 - 2 * e) * (1 - a ^ 2 / w ^ 2) = 1 - 2 * e - a ^ 2 / w ^ 2 + 2 * (e * (a ^ 2 / w ^ 2)) := by
      ring
    calc 1 - ε ≤ (1 - 2 * e) * (1 - a ^ 2 / w ^ 2) := by
          rw [h8]
          linarith
      _ ≤ _ := mul_le_mul h4 h3 h6 (sq_nonneg _)
  refine le_trans ?_ hfloor
  calc (1 - ε) * (w * √Real.pi) ≤ ((1 - e) ^ 2 * Real.exp (-(a ^ 2 / w ^ 2))) * (w * √Real.pi) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = _ := by ring

/-- At distance `R` from the ends of the range, with `R²/(2w²) = w/2`, a Gaussian has almost all its mass inside. -/
theorem gaussKernel_mass_far {w ε t A B R : ℝ} (hw : 0 < w) (hε0 : 0 < ε) (hAB : A ≤ B) (hR : 0 ≤ R)
    (hA : A + R ≤ t) (hB : t ≤ B - R) (hRw : R ^ 2 / (2 * w ^ 2) = w / 2) (hwε : 8 / ε ≤ w) :
    (1 - ε) * (w * √Real.pi) ≤ ∫ t₀ in A..B, gaussKernel w t t₀ := by
  refine le_trans ?_ (gaussKernel_mass_ge hw hAB hR hA hB)
  rw [hRw]
  have hexp : Real.exp (-(w / 2)) ≤ ε / 2 := by
    have h4 : w / 2 + 1 ≤ Real.exp (w / 2) := Real.add_one_le_exp _
    rw [Real.exp_neg]
    have h5 : 2 / ε ≤ Real.exp (w / 2) := by
      have h8 : 8 / ε = 4 * (2 / ε) := by ring
      rw [h8] at hwε
      have h9 : 0 ≤ 2 / ε := by positivity
      linarith
    rw [inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    calc (ε / 2)⁻¹ = 2 / ε := by rw [inv_div]
      _ ≤ _ := h5
  have hsqrt2 : √(2 * Real.pi) ≤ 2 * √Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
      (Real.sqrt_nonneg _)
  have h4 : Real.exp (-(w / 2)) * (w * √(2 * Real.pi)) ≤ ε / 2 * (w * (2 * √Real.pi)) :=
    mul_le_mul hexp (mul_le_mul_of_nonneg_left hsqrt2 hw.le) (by positivity) (by positivity)
  have h5 : ε / 2 * (w * (2 * √Real.pi)) = ε * (w * √Real.pi) := by ring
  have h6 : (1 - ε) * (w * √Real.pi) = w * √Real.pi - ε * (w * √Real.pi) := by ring
  rw [h6]
  linarith

/-- **The inequality at one height.**  For a window centred inside `[T, 2T]`: the interpolation, with the floor on the right, and all errors absorbed. -/
theorem eventually_height_inequality {θ ε : ℝ} (hθ : 0 < θ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2000) :
    ∀ᶠ T : ℝ in atTop, ∀ (b : ℕ → ℂ) (N : ℕ) (a T₁ T₂ t₀ : ℝ), 1 ≤ N → (N : ℝ) ≤ T ^ θ → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) → 0 < a → a ≤ 1 / 4 →
      a * ((2 + 3 / 2 * θ + 3 / 100) * Real.log T) = Real.log 2 → T₁ ≤ T₂ →
      T + Real.log T ^ 3 ≤ t₀ → t₀ ≤ 2 * T - Real.log T ^ 3 →
      Real.exp ((2 + 3 / 2 * θ + 1 / 100) * Real.log T * a) * ((1 - ε) * (Real.log T ^ 2 * √Real.pi)) +
        Real.exp (-((2 + 3 / 2 * θ + 1 / 100) * Real.log T * a)) *
          (∫ t in T₁..T₂, linePower b N (-a) t * gaussKernel (Real.log T ^ 2) t t₀) ≤
      5 / 2 * (∫ t in T..(2 * T), linePower b N 0 t * gaussKernel (Real.log T ^ 2) t t₀) +
        ε / 2 * (Real.log T ^ 2 * √Real.pi) := by
  obtain ⟨A, -, hwin⟩ := exists_window_inequality
  obtain ⟨Cc, hCc, hcenter⟩ := exists_center_tail
  obtain ⟨K, hK, hKev⟩ := exists_right_floor_error_le (ε := ε / 8) (by positivity)
  have hpow4 : Tendsto (fun T : ℝ => (Real.log T ^ 2) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp
      ((tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop)
  filter_upwards [eventually_remainder_le (A := A) hθ (ε := ε / 8) (by positivity), hKev,
    eventually_center_remainder_le hθ hCc (ε := ε / 8) (by positivity),
    hpow4.eventually_ge_atTop (1 / (4 * ε)), eventually_ge_atTop (100 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with T hrem hright hcen hw4 hT100 hℓ2
    b N a T₁ T₂ t₀ hN hNT hb1 hb ha0 ha1 haq hT12 hA1 hB1
  set ℓ := Real.log T with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  set w := ℓ ^ 2 with hw
  have hw0 : 0 < w := by positivity
  set R := ℓ ^ 3 with hR
  have hR0 : 0 ≤ R := by positivity
  set L := (2 + 3 / 2 * θ + 1 / 100) * ℓ with hL
  set B := ℓ / 100 with hB
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have ht₁ : T ≤ t₀ := by linarith
  have ht₂ : t₀ ≤ 2 * T := by linarith
  have ht₀0 : 0 < t₀ := by linarith
  have hcosh : 2 * Real.cosh (a * (L + 2 * B)) = 5 / 2 := by
    have h3 : a * (L + 2 * B) = Real.log 2 := by
      rw [← haq, hL, hB]
      ring
    rw [h3]
    exact two_mul_cosh_log_two
  have hmain := hwin t₀ hw0 ha0 ha1 hL0 hB0 hb
  rw [hcosh] at hmain
  have hmain2 := hmain.trans (add_le_add le_rfl (hrem N t₀ a hNT ht₁ ht₂ ha0 ha1 haq))
  have hA₀ := le_integral_window_right ht₀0 hw0 ha0 ha1 hK hN hb1 hb hε0 hε1 (hright t₀ ht₁) hw4
  have hX := integral_gauss_linePower_left_le t₀ hw0 ha0 ha1 hT12 hb
  have hF₀ := (hcenter t₀ hw0 hR0 (T₃ := T) (T₄ := 2 * T) hA1 (by linarith) hb).trans
    (add_le_add le_rfl (hcen N t₀ hNT ht₁ ht₂))
  have h3 := mul_le_mul_of_nonneg_left hA₀ (Real.exp_pos (L * a)).le
  have h4 := mul_le_mul_of_nonneg_left hX (Real.exp_pos (-(L * a))).le
  have h5 := mul_le_mul_of_nonneg_left hF₀ (by norm_num : (0 : ℝ) ≤ 5 / 2)
  have hD : 0 ≤ ε * (w * √Real.pi) := by positivity
  linarith

/-- The arithmetic of the integrated interpolation. -/
private theorem length_combine {x y z ε T D δ I₀ Il J : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 2000) (hT0 : 0 < T) (hD0 : 0 < D) (hδ1 : (1 - ε) * T ≤ δ) (hδ2 : δ ≤ T)
    (hJ : I₀ ≤ J) (hI : (1 - ε) ^ 2 * z * T ≤ Il)
    (h : x * ((1 - ε) * D) * δ + y * ((1 - ε) * D) * Il ≤ 5 / 2 * D * I₀ + ε / 2 * D * δ) :
    (1 - ε) ^ 2 * x * T + y * ((1 - ε) ^ 3 * z * T) ≤ 5 / 2 * J + 2 * ε * T := by
  have hε' : 0 ≤ 1 - ε := by linarith
  have hdiv : x * (1 - ε) * δ + y * (1 - ε) * Il ≤ 5 / 2 * I₀ + ε / 2 * δ := by
    refine le_of_mul_le_mul_right ?_ hD0
    calc (x * (1 - ε) * δ + y * (1 - ε) * Il) * D
        = x * ((1 - ε) * D) * δ + y * ((1 - ε) * D) * Il := by ring
      _ ≤ 5 / 2 * D * I₀ + ε / 2 * D * δ := h
      _ = _ := by ring
  have h3 : (1 - ε) ^ 2 * x * T ≤ x * (1 - ε) * δ := by
    have h4 := mul_le_mul_of_nonneg_left hδ1 (mul_nonneg hx0 hε')
    calc (1 - ε) ^ 2 * x * T = x * (1 - ε) * ((1 - ε) * T) := by ring
      _ ≤ _ := h4
  have h5 : y * ((1 - ε) ^ 3 * z * T) ≤ y * (1 - ε) * Il := by
    have h6 := mul_le_mul_of_nonneg_left hI (mul_nonneg hy0 hε')
    calc y * ((1 - ε) ^ 3 * z * T) = y * (1 - ε) * ((1 - ε) ^ 2 * z * T) := by ring
      _ ≤ _ := h6
  have h7 : ε / 2 * δ ≤ ε / 2 * T := mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have h8 : 0 ≤ ε * T := by positivity
  have h9 := mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℝ) ≤ 5 / 2)
  linarith

/-- The constant of the theorem. -/
private theorem length_constant {θ q p : ℝ} (hθ : 0 < θ) (hq : q = 2 + 3 / 2 * θ + 3 / 100)
    (hp0 : 0 < p) (hpq : p * q = 2) : 1 / (8 + 6 * θ) ≤ 129 / 1000 * p := by
  have h8 : 0 < 8 + 6 * θ := by positivity
  rw [div_le_iff₀ h8]
  have h1 : q ≤ 258 / 1000 * (8 + 6 * θ) := by
    rw [hq]
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hp0.le
  rw [hpq] at h2
  linarith

/-- **The necessary length of a mollifier.** -/
theorem necessary_length {θ : ℝ} (hθ : 0 < θ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N : ℝ) ≤ T ^ θ → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      (1 + 1 / (8 + 6 * θ)) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 2 + 3 / 2 * θ + 3 / 100 := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq2 : 2 ≤ q := by rw [hq]; linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 2 / q := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hq0]
    exact hq2
  have hpq : p * q = 2 := by
    rw [hp]
    exact div_mul_cancel₀ _ hq0.ne'
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = p / 2000 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 / 2000 := by rw [hε]; linarith
  have hpow2 : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((eventually_height_inequality hθ hε0 hε1).and ((eventually_left_floor hθ).and
      ((eventually_log_pow_mul_exp_le 3 (c := 1) (ε := ε / 16000) one_pos (by positivity)).and
        ((eventually_ge_atTop (32000 / ε)).and ((eventually_ge_atTop (100 : ℝ)).and
          ((Real.tendsto_log_atTop.eventually_ge_atTop 2).and
            ((hpow2.eventually_ge_atTop (8 / ε)).and (eventually_ge_atTop (4 / ε)))))))))
  refine ⟨T₀, fun T hT b N hN hNT hb1 hb hbr => ?_⟩
  obtain ⟨hheight, hleft, hR1, hT32, hT100, hℓ2, hw2, hTε⟩ := hT₀ T hT
  rw [← hq, ← hp] at hleft
  rw [← hq] at hheight
  have hT0 : 0 < T := by linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log T := ⟨_, rfl⟩
  rw [← hℓdef] at hheight hleft hR1 hℓ2 hw2
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ℓ ^ 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ℓ ^ 3 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (2 + 3 / 2 * θ + 1 / 100) * ℓ := ⟨_, rfl⟩
  rw [← hw, ← hR, ← hL] at hheight
  rw [← hw] at hw2
  rw [← hR] at hR1
  have hw0 : 0 < w := by rw [hw]; positivity
  have hR0 : 0 < R := by rw [hR]; positivity
  -- `R` is small against `T`
  have hRT : R ≤ ε / 16000 * T := by
    have hTe : Real.exp (-(1 * ℓ)) = T⁻¹ := by
      rw [one_mul, Real.exp_neg, hℓdef, Real.exp_log hT0]
    rw [hTe, ← div_eq_mul_inv, div_le_iff₀ hT0] at hR1
    exact hR1
  have h2T : 2 ≤ ε / 16000 * T := by
    have h3 := (div_le_iff₀ hε0).mp hT32
    linarith
  have hεT : 0 < ε * T := by positivity
  have hεT2 : ε * T ≤ T / 2000 := by
    have := mul_le_mul_of_nonneg_right hε1 hT0.le
    linarith
  have hsmallR : 4 * R + 2 ≤ ε * T / 1000 := by linarith
  -- the parameters of the interpolation
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.log 2 / (q * ℓ) := ⟨_, rfl⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  have haq : a * (q * ℓ) = Real.log 2 := by
    rw [ha]
    exact div_mul_cancel₀ _ (mul_pos hq0 hℓ0).ne'
  have ha4 : a ≤ 1 / 4 := by
    have h4 : (2 : ℝ) * 2 ≤ q * ℓ := mul_le_mul hq2 hℓ2 (by norm_num) hq0.le
    rw [ha, div_le_iff₀ (mul_pos hq0 hℓ0)]
    linarith
  have hLa : L * a = (1 - p / 100) * Real.log 2 := by
    have h3 : L = (q - 2 / 100) * ℓ := by
      rw [hL, hq]
      ring
    rw [h3, ← haq]
    linear_combination (a * ℓ / 100) * hpq
  -- the range of the centres and the slices
  have hAB : T + R ≤ 2 * T - R := by linarith
  obtain ⟨T₁, hT₁, T₂, hT₂, hs1, hs2⟩ := exists_admissible_slices (b := b) (N := N) hN hb1 hb
    (A₁ := T + 2 * R) (B₁ := T + 2 * R + 1) (A₂ := 2 * T - 2 * R - 1) (B₂ := 2 * T - 2 * R)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨hT₁a, hT₁b⟩ := hT₁
  obtain ⟨hT₂a, hT₂b⟩ := hT₂
  have hT12 : T₁ ≤ T₂ := by linarith
  have hm1 : -3 / 2 < -a := by linarith
  have hm0 : -3 / 2 < (0 : ℝ) := by norm_num
  have hRw : R ^ 2 / (2 * w ^ 2) = w / 2 := by
    rw [hR, hw, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  have hψ : ∀ t ∈ Icc T₁ T₂, (1 - ε) * (w * √Real.pi) ≤
      ∫ t₀ in (T + R)..(2 * T - R), gaussKernel w t t₀ := fun t ht =>
    gaussKernel_mass_far hw0 hε0 hAB hR0.le (by linarith [ht.1]) (by linarith [ht.2]) hRw
      hw2
  have hint := integrated_gauss_inequality (c₁ := Real.exp (L * a) * ((1 - ε) * (w * √Real.pi)))
    (c₂ := Real.exp (-(L * a))) (c₃ := 5 / 2) (τ := ε / 2 * (w * √Real.pi))
    (T₃ := T) (T₄ := 2 * T) hw0 hAB hT12 (by linarith)
    (continuous_linePower b N hm1) (continuous_linePower b N hm0)
    (linePower_nonneg b N _) (linePower_nonneg b N _) (Real.exp_pos _).le (by norm_num)
    (fun t₀ ht₀ => hheight b N a T₁ T₂ t₀ hN hNT hb1 hb ha0 ha4 haq hT12 ht₀.1 ht₀.2) hψ
  -- the left integral
  have hzval := hleft b N a T₁ T₂ hN hNT hb1 hb hbr ha0 ha4 haq (by linarith) (by linarith)
    (by linarith) (by linarith) hs1 hs2
  have hIlow := le_integral_linePower_left b N hε0 ha0 ha4 hT12 (by linarith) (by linarith)
  have hε' : 0 ≤ 1 - ε := by linarith
  have hlen12 : (1 - ε) * T ≤ T₂ - T₁ := by linarith
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Real.exp (99 / 100 * p * Real.log 2) := ⟨_, rfl⟩
  rw [← hz] at hzval
  have hz0 : 0 < z := by rw [hz]; positivity
  have hIz : (1 - ε) ^ 2 * z * T ≤ ∫ t in T₁..T₂, linePower b N (-a) t := by
    have h3 := (mul_le_mul_of_nonneg_left hzval hε').trans hIlow
    have h4 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hlen12 hz0.le) hε'
    calc (1 - ε) ^ 2 * z * T = (1 - ε) * ((1 - ε) * T * z) := by ring
      _ ≤ _ := h4
      _ ≤ _ := h3
  have hfinal := length_combine (x := Real.exp (L * a)) (y := Real.exp (-(L * a))) (z := z)
    (Real.exp_pos _).le (Real.exp_pos _).le hε0 hε1 hT0 (by positivity : 0 < w * √Real.pi)
    (δ := 2 * T - R - (T + R)) (by linarith) (by linarith)
    (integral_linePower_zero_le b N (by linarith : T ≤ 2 * T)) hIz hint
  have hnum := final_numeric hp0 hp1 hε (congrArg Real.exp hLa) (by rw [hLa]) hz hT0 hfinal
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hT0.le) hnum
  have hcomp := length_constant hθ hq hp0 hpq
  linarith

/-- **A second moment tending to one forces the length exponent to infinity.**  If real mollifiers `M_T` with bounded coefficients have `(1/T)∫_T^{2T}|ζM_T|² → 1`, then
their lengths eventually exceed every power of `T`. -/
theorem length_exponent_tendsto_of_second_moment_tendsto_one (b : ℝ → ℕ → ℂ) (N : ℝ → ℕ)
    (hN : ∀ T, 1 ≤ N T) (hb1 : ∀ T, b T 1 = 1) (hb : ∀ T, ∀ n ∈ Finset.Icc 1 (N T), ‖b T n‖ ≤ 1)
    (hbr : ∀ T, ∀ n ∈ Finset.Icc 1 (N T), (starRingEnd ℂ) (b T n) = b T n)
    (hm : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly (b T) (Finset.Icc 1 (N T)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) atTop (𝓝 1))
    {θ : ℝ} (hθ : 0 < θ) : ∀ᶠ T : ℝ in atTop, T ^ θ < (N T : ℝ) := by
  obtain ⟨T₀, hT₀⟩ := necessary_length hθ
  have hc : 0 < 1 / (8 + 6 * θ) := by positivity
  filter_upwards [hm.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + 1 / (8 + 6 * θ))),
    eventually_ge_atTop T₀, eventually_gt_atTop (0 : ℝ)] with T h1 h2 h3
  by_contra hcontra
  have h4 := hT₀ T h2 (b T) (N T) (hN T) (not_lt.mp hcontra) (hb1 T) (hb T) (hbr T)
  have h5 := mul_le_mul_of_nonneg_left h4 (inv_pos.mpr h3).le
  rw [mul_comm (1 + 1 / (8 + 6 * θ)) T, ← mul_assoc, inv_mul_cancel₀ h3.ne', one_mul] at h5
  linarith

end GaloisForLFunctions.ArithmeticProduction
