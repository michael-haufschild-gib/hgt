import GaloisForLFunctions.ArithmeticProduction.TheInterpolationAtALargeHeight

/-!
# The necessary length of a mollifier

**Theorem** (`necessary_length_uniform`).  For all large `T` and every `0 < θ ≤ (log T)/24`, every real Dirichlet polynomial `M` of length `N ≤ T^θ` with `b₁ = 1`,
`|b_n| ≤ 1` satisfies

  `∫_T^{2T} |ζ(½+it) M(½+it)|² dt ≥ (1 + 1/(8 + 6θ)) T`.

The exponent may grow with `T`.  So an excess `κ` forces `log N ≥ min(log²T/24, log T/(14κ))` (`log_length_ge_of_excess`), and a mollified second moment tending to `1` forces the length
exponent to infinity (`length_exponent_tendsto_of_second_moment_tendsto_one`).  Three ingredients enter:

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

/-- The band parameter `q`. -/
def lengthQ (θ : ℝ) : ℝ := 2 + 3 / 2 * θ + 3 / 100

/-- The precision `ε = (2/q)/2000`. -/
def lengthEps (θ : ℝ) : ℝ := 2 / lengthQ θ / 2000

theorem lengthQ_pos {θ : ℝ} (hθ : 0 < θ) : 0 < lengthQ θ := by
  unfold lengthQ
  positivity

theorem lengthEps_pos {θ : ℝ} (hθ : 0 < θ) : 0 < lengthEps θ := by
  have := lengthQ_pos hθ
  unfold lengthEps
  positivity

theorem lengthEps_le {θ : ℝ} (hθ : 0 < θ) : lengthEps θ ≤ 1 / 2000 := by
  have hq := lengthQ_pos hθ
  have h2 : 2 ≤ lengthQ θ := by
    unfold lengthQ
    linarith
  have h1 : 2 / lengthQ θ ≤ 1 := by
    rw [div_le_one hq]
    exact h2
  unfold lengthEps
  linarith

/-- The smallness conditions under which the interpolation closes at height `T` and exponent `θ`. -/
structure LengthSmall (A Cc C K₁ θ T : ℝ) : Prop where
  r₁ : Real.log T ^ 2 * Real.exp (-(1 / 50 * Real.log T)) ≤ lengthEps θ / 8 / (2 * 288)
  r₂ : Real.log T ^ 10 * Real.exp (-(1 / 25 * Real.log T)) ≤
    lengthEps θ / 8 / (2 * (4 * (A ^ 2 * 9 * 432 ^ 2) + 1))
  f₁ : Real.log T ^ 4 * Real.exp (-(1 * Real.log T)) ≤ 1 / 16
  f₂ : 128 / (lengthEps θ / 8) ≤ T
  f₃ : 96 / (lengthEps θ / 8) ≤ T
  f₄ : 2 * (rightFloorParam (lengthEps θ / 8) - 1 / 2) ^ 2 + 1 ≤ (Real.log T ^ 2) ^ 2
  c₁ : Real.log T ^ 8 * Real.exp (-(1 * Real.log T)) ≤
    lengthEps θ / 8 / (Cc * 8100 * (2 * Real.exp 1) * 2 + 1)
  c₂ : 4 * (3 * θ + 5) ≤ Real.log T
  w₄ : 1 / (4 * lengthEps θ) ≤ (Real.log T ^ 2) ^ 2
  m₁ : Real.log T ^ 3 * Real.exp (-(1 * Real.log T)) ≤ lengthEps θ / 16000
  m₂ : 32000 / lengthEps θ ≤ T
  m₃ : 100 ≤ T
  m₄ : 2 ≤ Real.log T
  m₅ : 8 / lengthEps θ ≤ Real.log T ^ 2
  m₆ : 4 / lengthEps θ ≤ T
  l₁ : Real.log T ^ 1 * Real.exp (-(1 * Real.log T)) ≤
    6 / 1000 * (Real.log 2 / lengthQ θ) / (2 * (K₁ * (1 + 5 * θ) + C + K₁ + 1))
  l₂ : ∀ T₁ T₂ : ℝ, T ≤ T₁ → T₁ ≤ 1001 / 1000 * T → 1999 / 1000 * T ≤ T₂ → T₂ ≤ 2 * T →
    996 / 1000 * (T * Real.log T) ≤ 2 * Real.pi * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)

/-- **The inequality at one height.**  For a window centred inside `[T, 2T]`: the interpolation, with the floor on the right, and all errors absorbed. -/
theorem exists_height_inequality :
    ∃ A Cc : ℝ, 0 ≤ Cc ∧ ∀ C K₁ θ T : ℝ, 0 < θ → LengthSmall A Cc C K₁ θ T →
      ∀ (b : ℕ → ℂ) (N : ℕ) (a T₁ T₂ t₀ : ℝ), 1 ≤ N → (N : ℝ) ≤ T ^ θ → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) → 0 < a → a ≤ 1 / 4 →
      a * ((2 + 3 / 2 * θ + 3 / 100) * Real.log T) = Real.log 2 → T₁ ≤ T₂ →
      T + Real.log T ^ 3 ≤ t₀ → t₀ ≤ 2 * T - Real.log T ^ 3 →
      Real.exp ((2 + 3 / 2 * θ + 1 / 100) * Real.log T * a) *
          ((1 - lengthEps θ) * (Real.log T ^ 2 * √Real.pi)) +
        Real.exp (-((2 + 3 / 2 * θ + 1 / 100) * Real.log T * a)) *
          (∫ t in T₁..T₂, linePower b N (-a) t * gaussKernel (Real.log T ^ 2) t t₀) ≤
      5 / 2 * (∫ t in T..(2 * T), linePower b N 0 t * gaussKernel (Real.log T ^ 2) t t₀) +
        lengthEps θ / 2 * (Real.log T ^ 2 * √Real.pi) := by
  obtain ⟨A, -, hwin⟩ := exists_window_inequality
  obtain ⟨Cc, hCc, hcenter⟩ := exists_center_tail
  refine ⟨A, Cc, hCc, ?_⟩
  intro C K₁ θ T hθ hs b N a T₁ T₂ t₀ hN hNT hb1 hb ha0 ha1 haq hT12 hA1 hB1
  have hε0 := lengthEps_pos hθ
  have hε1 := lengthEps_le hθ
  have hT100 := hs.m₃
  have hℓ2 := hs.m₄
  have hT1 : 1 < T := by linarith
  have hcube : 0 ≤ Real.log T ^ 3 := by positivity
  have ht₁ : T ≤ t₀ := by linarith
  have ht₂ : t₀ ≤ 2 * T := by linarith
  have hrem := remainder_le_of_small (A := A) (ε := lengthEps θ / 8) hθ (by positivity) hs.r₁ hs.r₂ hℓ2
    hT1 N t₀ a hNT ht₁ ht₂ ha0 ha1 haq
  have hright := right_floor_error_le_of_small (ε := lengthEps θ / 8) (t₀ := t₀) (by positivity) hs.f₁
    hs.f₂ hs.f₃ hT1 hs.f₄ (by linarith) ht₁
  have hcen := center_remainder_le_of_small (ε := lengthEps θ / 8) hCc hs.c₁ hs.c₂ (by linarith) hT1.le
    N t₀ hNT ht₁ ht₂
  have hw4 := hs.w₄
  have hK := five_le_rightFloorParam (lengthEps θ / 8)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = rightFloorParam (lengthEps θ / 8) := ⟨_, rfl⟩
  rw [← hKdef] at hright hK
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = lengthEps θ := ⟨_, rfl⟩
  rw [← hεdef] at hrem hright hcen hw4 hε0 hε1 ⊢
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
  have ht₀0 : 0 < t₀ := by linarith
  have hcosh : 2 * Real.cosh (a * (L + 2 * B)) = 5 / 2 := by
    have h3 : a * (L + 2 * B) = Real.log 2 := by
      rw [← haq, hL, hB]
      ring
    rw [h3]
    exact two_mul_cosh_log_two
  have hmain := hwin t₀ hw0 ha0 ha1 hL0 hB0 hb
  rw [hcosh] at hmain
  have hmain2 := hmain.trans (add_le_add le_rfl hrem)
  have hA₀ := le_integral_window_right ht₀0 hw0 ha0 ha1 hK hN hb1 hb hε0 hε1 hright hw4
  have hX := integral_gauss_linePower_left_le t₀ hw0 ha0 ha1 hT12 hb
  have hF₀ := (hcenter t₀ hw0 hR0 (T₃ := T) (T₄ := 2 * T) hA1 (by linarith) hb).trans
    (add_le_add le_rfl hcen)
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

/-- **The core of the necessary length.**  Under the smallness conditions at `(θ, T)`, the excess of every mollifier of length `T^θ` is at least `1/(8+6θ)`. -/
theorem exists_necessary_length_core :
    ∃ A Cc C K₁ : ℝ, 0 ≤ Cc ∧ 0 < C ∧ 0 < K₁ ∧ ∀ θ T : ℝ, 0 < θ → LengthSmall A Cc C K₁ θ T →
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N : ℝ) ≤ T ^ θ → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      (1 + 1 / (8 + 6 * θ)) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨A, Cc, hCc, hheight0⟩ := exists_height_inequality
  obtain ⟨C, K₁, hC, hK₁, hleft0⟩ := exists_left_floor_of_small
  refine ⟨A, Cc, C, K₁, hCc, hC, hK₁, ?_⟩
  intro θ T hθ hsm b N hN hNT hb1 hb hbr
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
  have hεdef : lengthEps θ = ε := by
    rw [hε, hp, hq]
    rfl
  have hheight := hheight0 C K₁ θ T hθ hsm
  rw [hεdef] at hheight
  have hleft := hleft0 θ T hθ hsm.l₁ hsm.l₂ (by linarith [hsm.m₃]) (by linarith [hsm.m₄])
  have hR1 : Real.log T ^ 3 * Real.exp (-(1 * Real.log T)) ≤ ε / 16000 := by
    rw [← hεdef]
    exact hsm.m₁
  have hT32 : 32000 / ε ≤ T := by
    rw [← hεdef]
    exact hsm.m₂
  have hT100 := hsm.m₃
  have hℓ2 := hsm.m₄
  have hw2 : 8 / ε ≤ Real.log T ^ 2 := by
    rw [← hεdef]
    exact hsm.m₅
  have hTε : 4 / ε ≤ T := by
    rw [← hεdef]
    exact hsm.m₆
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

/-! ### The smallness conditions, uniformly in the exponent -/

private theorem lengthQ_le {θ ℓ : ℝ} (hθ : θ ≤ ℓ / 24) (hℓ : 3 ≤ ℓ) : lengthQ θ ≤ ℓ := by
  unfold lengthQ
  linarith

private theorem le_lengthEps {θ ℓ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ ℓ / 24) (hℓ : 3 ≤ ℓ) :
    1 / (1000 * ℓ) ≤ lengthEps θ := by
  have hq := lengthQ_pos hθ0
  have hqℓ := lengthQ_le hθ hℓ
  have hval : lengthEps θ = 1 / (1000 * lengthQ θ) := by
    unfold lengthEps
    field_simp
    norm_num
  rw [hval]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

private theorem pow_mul_le_of_succ {k : ℕ} {ℓ E D ε : ℝ} (hℓ : 0 < ℓ) (hD : 0 < D)
    (h : ℓ ^ (k + 1) * E ≤ 1 / (1000 * D)) (hε : 1 / (1000 * ℓ) ≤ ε) : ℓ ^ k * E ≤ ε / D := by
  have h1 : ℓ ^ k * E = ℓ ^ (k + 1) * E / ℓ := by
    field_simp
    ring
  rw [h1, div_le_iff₀ hℓ]
  refine h.trans ?_
  have h2 := div_le_div_of_nonneg_right hε hD.le
  have h3 := mul_le_mul_of_nonneg_right h2 hℓ.le
  refine le_trans (le_of_eq ?_) h3
  field_simp

private theorem div_le_of_eps {a ε X ℓ : ℝ} (ha : 0 ≤ a) (hℓ : 0 < ℓ) (hε : 1 / (1000 * ℓ) ≤ ε)
    (h : a * (1000 * ℓ) ≤ X) : a / ε ≤ X := by
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε
  rw [div_le_iff₀ hε0]
  have h1 : X * (1 / (1000 * ℓ)) ≤ X * ε :=
    mul_le_mul_of_nonneg_left hε (le_trans (by positivity) h)
  refine le_trans ?_ h1
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  exact h

private theorem rightFloorParam_le {ε ℓ : ℝ} (hε : 1 / (8000 * ℓ) ≤ ε) (hℓ : 25 ≤ ℓ)
    (hlog : Real.log ℓ ≤ ℓ / 10) : rightFloorParam ε ≤ ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h69 : 69 / 100 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  refine max_le (by linarith) ?_
  rw [div_le_iff₀ hlog2]
  have h1 : 152 / ε ≤ 2 ^ 21 * ℓ := by
    rw [div_le_iff₀ hε0]
    have h2 := mul_le_mul_of_nonneg_left hε (by positivity : 0 ≤ (2 : ℝ) ^ 21 * ℓ)
    refine le_trans ?_ h2
    have h3 : (2 : ℝ) ^ 21 * ℓ * (1 / (8000 * ℓ)) = 2 ^ 21 / 8000 := by
      field_simp
    rw [h3]
    norm_num
  have h4 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by positivity) hℓ0.ne', Real.log_pow] at h4
  push_cast at h4
  have h5 : (ℓ - 21) * (69 / 100) ≤ (ℓ - 21) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h69 (by linarith)
  linarith

private theorem lengthFloor_param_bound {ε ℓ : ℝ} (hε : 1 / (8000 * ℓ) ≤ ε) (hℓ : 25 ≤ ℓ)
    (hlog : Real.log ℓ ≤ ℓ / 10) : 2 * (rightFloorParam ε - 1 / 2) ^ 2 + 1 ≤ (ℓ ^ 2) ^ 2 := by
  have h1 := rightFloorParam_le hε hℓ hlog
  have h2 := five_le_rightFloorParam ε
  have h3 : (rightFloorParam ε - 1 / 2) ^ 2 ≤ ℓ ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h4 : (4 : ℝ) ≤ ℓ ^ 2 := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ ℓ ^ 2)
  have h6 : (ℓ ^ 2) ^ 2 = ℓ ^ 2 * ℓ ^ 2 := by ring
  rw [h6]
  linarith

private theorem left_floor_small_uniform {θ ℓ E C K₁ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ ℓ / 24) (hℓ : 3 ≤ ℓ)
    (hC : 0 < C) (hK₁ : 0 < K₁)
    (h : ℓ ^ 3 * E ≤ 6 / 1000 * (69 / 100) / (2 * (K₁ * 2 + C + K₁ + 1))) :
    ℓ ^ 1 * E ≤ 6 / 1000 * (Real.log 2 / lengthQ θ) / (2 * (K₁ * (1 + 5 * θ) + C + K₁ + 1)) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hq := lengthQ_pos hθ0
  have hqℓ := lengthQ_le hθ hℓ
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ, D₁ = K₁ * 2 + C + K₁ + 1 := ⟨_, rfl⟩
  have hD₁0 : 0 < D₁ := by rw [hD₁]; positivity
  rw [← hD₁] at h
  have h69 : 69 / 100 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hDθ : K₁ * (1 + 5 * θ) + C + K₁ + 1 ≤ D₁ * ℓ := by
    have h1 : 1 + 5 * θ ≤ 2 * ℓ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hK₁.le
    rw [hD₁]
    have h3 : 0 ≤ (C + K₁ + 1) * (ℓ - 1) := mul_nonneg (by positivity) (by linarith)
    have h4 : (K₁ * 2 + C + K₁ + 1) * ℓ = K₁ * (2 * ℓ) + (C + K₁ + 1) * ℓ := by ring
    rw [h4]
    have h5 : (C + K₁ + 1) * (ℓ - 1) = (C + K₁ + 1) * ℓ - (C + K₁ + 1) := by ring
    linarith
  have hDθ0 : 0 < K₁ * (1 + 5 * θ) + C + K₁ + 1 := by positivity
  have h1 : 69 / 100 / ℓ ≤ Real.log 2 / lengthQ θ := div_le_div₀ hlog2.le h69 hq hqℓ
  have h2 : 6 / 1000 * (69 / 100 / ℓ) / (2 * (D₁ * ℓ)) ≤
      6 / 1000 * (Real.log 2 / lengthQ θ) / (2 * (K₁ * (1 + 5 * θ) + C + K₁ + 1)) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by positivity)
      (by linarith)
  refine le_trans ?_ h2
  have h3 : 6 / 1000 * (69 / 100 / ℓ) / (2 * (D₁ * ℓ)) =
      6 / 1000 * (69 / 100) / (2 * D₁) / ℓ ^ 2 := by
    field_simp
  rw [h3, le_div_iff₀ (by positivity)]
  refine le_trans (le_of_eq ?_) h
  ring

/-- **The conditions hold at all large heights, for all exponents up to `(log T)/24`.** -/
theorem eventually_lengthSmall {A Cc C K₁ : ℝ} (hCc : 0 ≤ Cc) (hC : 0 < C) (hK₁ : 0 < K₁) :
    ∀ᶠ T : ℝ in atTop, ∀ θ : ℝ, 0 < θ → θ ≤ Real.log T / 24 → LengthSmall A Cc C K₁ θ T := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * (A ^ 2 * 9 * 432 ^ 2) + 1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = Cc * 8100 * (2 * Real.exp 1) * 2 + 1 := ⟨_, rfl⟩
  have hC'0 : 0 < C' := by rw [hC']; positivity
  have hloglog : ∀ᶠ T : ℝ in atTop, Real.log (Real.log T) ≤ Real.log T / 10 := by
    have h1 := Real.isLittleO_log_id_atTop.def (c := 1 / 10) (by norm_num)
    filter_upwards [Real.tendsto_log_atTop.eventually h1, Real.tendsto_log_atTop.eventually_gt_atTop 0]
      with T hT hT0
    simp only [id_eq] at hT
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hT0.le] at hT
    linarith [le_abs_self (Real.log (Real.log T))]
  filter_upwards [eventually_log_pow_mul_exp_le 3 (c := 1 / 50) (ε := 1 / (1000 * (8 * (2 * 288))))
      (by norm_num) (by norm_num),
    eventually_log_pow_mul_exp_le 11 (c := 1 / 25) (ε := 1 / (1000 * (8 * (2 * B)))) (by norm_num)
      (by positivity),
    eventually_log_pow_mul_exp_le 4 (c := 1) (ε := 1 / (1000 * 16000)) one_pos (by norm_num),
    eventually_log_pow_mul_exp_le 9 (c := 1) (ε := 1 / (1000 * (8 * C'))) one_pos (by positivity),
    eventually_log_pow_mul_exp_le 1 (c := 1) (ε := 1 / 32000000) one_pos (by norm_num),
    eventually_log_pow_mul_exp_le 3 (c := 1)
      (ε := 6 / 1000 * (69 / 100) / (2 * (K₁ * 2 + C + K₁ + 1))) one_pos (by positivity),
    Real.tendsto_log_atTop.eventually_ge_atTop (8000 : ℝ), eventually_ge_atTop (100 : ℝ), hloglog,
    eventually_zero_count_increment] with T e1 e2 e3 e4 e5 e6 hℓ hT100 hll hcount θ hθ0 hθ
  set ℓ := Real.log T with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have hT0 : 0 < T := by linarith
  have hε := le_lengthEps hθ0 hθ (by linarith)
  have hε8 : 1 / (8000 * ℓ) ≤ lengthEps θ / 8 := by
    have h1 : 1 / (8000 * ℓ) = 1 / (1000 * ℓ) / 8 := by
      field_simp
      norm_num
    rw [h1]
    exact div_le_div_of_nonneg_right hε (by norm_num)
  have hε8' : 1 / (1000 * ℓ) ≤ lengthEps θ / 8 * 8 := by linarith
  have hTe : Real.exp (-(1 * ℓ)) = T⁻¹ := by
    rw [one_mul, Real.exp_neg, hℓdef, Real.exp_log hT0]
  have hℓT : 32000000 * ℓ ≤ T := by
    have h1 := e5
    rw [hTe, pow_one, ← div_eq_mul_inv, div_le_iff₀ hT0] at h1
    linarith
  have hexp1 : 0 ≤ Real.exp (-(1 * ℓ)) := (Real.exp_pos _).le
  have heps8 : ∀ a : ℝ, 0 ≤ a → a * 8 * (1000 * ℓ) ≤ T → a / (lengthEps θ / 8) ≤ T := by
    intro a ha h
    have h1 : a / (lengthEps θ / 8) = a * 8 / lengthEps θ := by
      have := lengthEps_pos hθ0
      field_simp
    rw [h1]
    exact div_le_of_eps (by positivity) hℓ0 hε h
  exact
    { r₁ := by
        rw [div_div]
        exact pow_mul_le_of_succ hℓ0 (by norm_num) e1 hε
      r₂ := by
        rw [div_div, ← hB]
        exact pow_mul_le_of_succ hℓ0 (by positivity) e2 hε
      f₁ := by
        have h1 : ℓ ^ 4 * Real.exp (-(1 * ℓ)) ≤ 1 / (1000 * 16000) := e3
        linarith
      f₂ := heps8 128 (by norm_num) (by linarith)
      f₃ := heps8 96 (by norm_num) (by linarith)
      f₄ := lengthFloor_param_bound hε8 (by linarith) hll
      c₁ := by
        rw [div_div, ← hC']
        exact pow_mul_le_of_succ hℓ0 (by positivity) e4 hε
      c₂ := by linarith
      w₄ := by
        have h1 : 1 / (4 * lengthEps θ) = (1 / 4) / lengthEps θ := by
          have := lengthEps_pos hθ0
          field_simp
        rw [h1]
        refine div_le_of_eps (by norm_num) hℓ0 hε ?_
        have h2 : (ℓ ^ 2) ^ 2 = ℓ ^ 3 * ℓ := by ring
        rw [h2]
        have h3 : (250 : ℝ) ≤ ℓ ^ 3 := by
          calc (250 : ℝ) ≤ 8 ^ 3 := by norm_num
            _ ≤ ℓ ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
        have h4 := mul_le_mul_of_nonneg_right h3 hℓ0.le
        linarith
      m₁ := pow_mul_le_of_succ hℓ0 (by norm_num) e3 hε
      m₂ := div_le_of_eps (by norm_num) hℓ0 hε (by linarith)
      m₃ := hT100
      m₄ := by linarith
      m₅ := by
        refine div_le_of_eps (by norm_num) hℓ0 hε ?_
        have h2 : ℓ ^ 2 = ℓ * ℓ := by ring
        rw [h2]
        have h3 := mul_le_mul_of_nonneg_right hℓ hℓ0.le
        linarith
      m₆ := div_le_of_eps (by norm_num) hℓ0 hε (by linarith)
      l₁ := left_floor_small_uniform hθ0 hθ (by linarith) hC hK₁ e6
      l₂ := hcount }

/-- **The necessary length of a mollifier, uniformly in the exponent.** -/
theorem necessary_length_uniform :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ θ : ℝ, 0 < θ → θ ≤ Real.log T / 24 →
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N : ℝ) ≤ T ^ θ → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      (1 + 1 / (8 + 6 * θ)) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨A, Cc, C, K₁, hCc, hC, hK₁, hcore⟩ := exists_necessary_length_core
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (eventually_lengthSmall (A := A) hCc hC hK₁)
  exact ⟨T₀, fun T hT θ hθ0 hθ b N hN hNT hb1 hb hbr =>
    hcore θ T hθ0 (hT₀ T hT θ hθ0 hθ) b N hN hNT hb1 hb hbr⟩

/-- **The necessary length of a mollifier.** -/
theorem necessary_length {θ : ℝ} (hθ : 0 < θ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N : ℝ) ≤ T ^ θ → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      (1 + 1 / (8 + 6 * θ)) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨T₀, hT₀⟩ := necessary_length_uniform
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (24 * θ))
  refine ⟨max T₀ T₁, fun T hT b N hN hNT hb1 hb hbr => ?_⟩
  have h1 := hT₁ T ((le_max_right _ _).trans hT)
  exact hT₀ T ((le_max_left _ _).trans hT) θ hθ (by linarith) b N hN hNT hb1 hb hbr

/-- **An excess forces length.**  A mollifier with excess `κ < 1/14` has `log N ≥ min(log²T/24, log T/(14κ))`. -/
theorem log_length_ge_of_excess :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) → ∀ κ : ℝ, 0 < κ → κ < 1 / 14 →
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + κ) * T →
      min (Real.log T ^ 2 / 24) (Real.log T / (14 * κ)) ≤ Real.log N := by
  obtain ⟨T₀, hT₀⟩ := necessary_length_uniform
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually_ge_atTop (24 : ℝ))
  refine ⟨max (max T₀ T₁) 1, fun T hT b N hN hb1 hb hbr κ hκ0 hκ hmom => ?_⟩
  have hTT₀ : T₀ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hℓ : 24 ≤ Real.log T := hT₁ T ((le_max_right _ _).trans ((le_max_left _ _).trans hT))
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < Real.log T := by linarith
  by_contra hcon
  obtain ⟨h1, h2⟩ := lt_min_iff.mp (not_le.mp hcon)
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = max 1 (Real.log N / Real.log T) := ⟨_, rfl⟩
  have hθ1 : 1 ≤ θ := by rw [hθdef]; exact le_max_left _ _
  have hθN : Real.log N / Real.log T ≤ θ := by rw [hθdef]; exact le_max_right _ _
  have hθℓ : θ ≤ Real.log T / 24 := by
    rw [hθdef]
    refine max_le (by linarith) ?_
    rw [div_le_iff₀ hℓ0]
    have h3 : Real.log T / 24 * Real.log T = Real.log T ^ 2 / 24 := by ring
    rw [h3]
    exact h1.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNT : (N : ℝ) ≤ T ^ θ := by
    rw [Real.rpow_def_of_pos hT0, ← Real.log_le_iff_le_exp hN0]
    rw [div_le_iff₀ hℓ0] at hθN
    linarith [mul_comm θ (Real.log T)]
  have hfl := hT₀ T hTT₀ θ (by linarith) hθℓ b N hN hNT hb1 hb hbr
  have hex := le_of_mul_le_mul_right (hfl.trans hmom) hT0
  have h14 : 1 / (14 * θ) ≤ κ := by
    have h3 : 1 / (14 * θ) ≤ 1 / (8 + 6 * θ) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hθκ : 1 / (14 * κ) ≤ θ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h14
    linarith
  have hgt : 1 < 1 / (14 * κ) := by
    rw [one_lt_div (by positivity)]
    linarith
  have hθne : θ = Real.log N / Real.log T := by
    rw [hθdef] at hθκ ⊢
    rcases le_total 1 (Real.log N / Real.log T) with h3 | h3
    · exact max_eq_right h3
    · rw [max_eq_left h3] at hθκ
      linarith
  rw [hθne, le_div_iff₀ hℓ0] at hθκ
  have h3 : Real.log T / (14 * κ) = 1 / (14 * κ) * Real.log T := by ring
  rw [h3] at h2
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
