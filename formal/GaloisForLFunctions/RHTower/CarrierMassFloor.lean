/-
Point-to-mass conversion for the completed carrier on the critical line.

An anchor value `c ≤ |f τ|` together with a derivative sup `D` on `[τ−rz, τ+rz]` forces
`|f| ≥ c/2` on the concentric subinterval of radius `min rz (c/(2D))`, so the short-interval
square integral is at least `(c/2)²·2·min rz (c/(2D))` — a pointwise floor becomes an
interval mass floor.  For `Re Φ̃_N` along the line the derivative is computed termwise from
the envelope calculus and bounded by `4√N·(M₁ + M₀·log N)`, and the anchor is the product of
the archimedean floor with the carrier anchor already present in the window certificates:
the short-interval second-moment face of the sign-bracket certificate is thereby discharged
into faces the certificates already carry.
-/
import GaloisForLFunctions.RHTower.HardySignChange
import GaloisForLFunctions.RHTower.SeamSignTransport

open Complex Metric MeasureTheory

namespace RHTower

/-! ### §1 The point-to-mass converter -/

/-- **Point-to-mass conversion.**  A pointwise anchor `c ≤ |f τ|` and a derivative sup `D`
on the window `[τ−rz, τ+rz]` force `|f| ≥ c/2` on the concentric subinterval of radius
`min rz (c/(2D))`, so the window square integral is at least `(c/2)²·2·min rz (c/(2D))`. -/
theorem sq_integral_floor_of_anchor_slope {f f' : ℝ → ℝ} {τ rz c D : ℝ}
    (hrz : 0 < rz) (hc : 0 < c) (hD : 0 < D)
    (hf : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), HasDerivAt f (f' u) u)
    (hf'le : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), |f' u| ≤ D)
    (hanchor : c ≤ |f τ|) :
    (c / 2) ^ 2 * (2 * min rz (c / (2 * D))) ≤
      ∫ u in (τ - rz)..(τ + rz), (f u) ^ 2 := by
  set δ := min rz (c / (2 * D)) with hδ_def
  have hδ0 : 0 < δ := lt_min hrz (by positivity)
  have hδrz : δ ≤ rz := min_le_left _ _
  have hDδ : D * δ ≤ c / 2 := by
    have h1 : δ ≤ c / (2 * D) := min_le_right _ _
    calc D * δ ≤ D * (c / (2 * D)) := by nlinarith
      _ = c / 2 := by field_simp
  have hτmem : τ ∈ Set.Icc (τ - rz) (τ + rz) := ⟨by linarith, by linarith⟩
  have hMVT : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), |f u - f τ| ≤ D * |u - τ| := by
    intro u hu
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f') (s := Set.Icc (τ - rz) (τ + rz)) (C := D)
      (fun x hx => (hf x hx).hasDerivWithinAt)
      (fun x hx => by simpa [Real.norm_eq_abs] using hf'le x hx)
      (convex_Icc _ _) hτmem hu
    simpa [Real.norm_eq_abs] using h
  have hsub : Set.Icc (τ - δ) (τ + δ) ⊆ Set.Icc (τ - rz) (τ + rz) :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have hfloor : ∀ u ∈ Set.Icc (τ - δ) (τ + δ), (c / 2) ^ 2 ≤ (f u) ^ 2 := by
    intro u hu
    have hclose : |u - τ| ≤ δ := by
      rw [abs_le]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h1 : |f u - f τ| ≤ c / 2 := by
      have h2 : D * |u - τ| ≤ D * δ := mul_le_mul_of_nonneg_left hclose hD.le
      linarith [hMVT u (hsub hu)]
    have h2 : c / 2 ≤ |f u| := by
      have h3 := abs_sub_abs_le_abs_sub (f τ) (f u)
      have h4 : |f τ - f u| = |f u - f τ| := abs_sub_comm _ _
      linarith
    nlinarith [sq_abs (f u), abs_nonneg (f u)]
  have hcontf : ContinuousOn f (Set.Icc (τ - rz) (τ + rz)) :=
    fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun u => (f u) ^ 2) volume (τ - rz) (τ + rz) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact hcontf.pow 2
  have hint2 : IntervalIntegrable (fun u => (f u) ^ 2) volume (τ - δ) (τ + δ) := by
    apply hint.mono_set
    rw [Set.uIcc_of_le (by linarith : τ - δ ≤ τ + δ), Set.uIcc_of_le (by linarith)]
    exact hsub
  have hmid : (c / 2) ^ 2 * (2 * δ) ≤ ∫ u in (τ - δ)..(τ + δ), (f u) ^ 2 := by
    have hconst : (∫ _ in (τ - δ)..(τ + δ), (c / 2) ^ 2) = (c / 2) ^ 2 * (2 * δ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hconst]
    exact intervalIntegral.integral_mono_on (by linarith)
      intervalIntegrable_const hint2 hfloor
  have hmono : (∫ u in (τ - δ)..(τ + δ), (f u) ^ 2) ≤
      ∫ u in (τ - rz)..(τ + rz), (f u) ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (ae_of_all _ fun u => sq_nonneg (f u)) hint
  linarith

/-! ### §2 The line slope of the completed carrier -/

/-- Termwise line slope of the completed carrier: the product-rule derivative of the
critical-line term `carrierLineTerm n`, with both envelopes differentiated through the
envelope calculus and both oscillations through their linear frequencies `∓log n`. -/
noncomputable def carrierLineSlopeTerm (n : ℕ) (u : ℝ) : ℂ :=
  (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
    ((archFactorDeriv (linePt u) * Complex.I *
        Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u) +
      archFactor (linePt u) *
        (Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u) *
          -(Complex.I * (Real.log n : ℂ)))) +
     (archFactorDeriv (1 - linePt u) * -Complex.I *
        Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u) +
      archFactor (1 - linePt u) *
        (Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u) *
          -(Complex.I * ((-Real.log n : ℝ) : ℂ)))))

/-- Line slope of the completed carrier: the sum of the termwise slopes. -/
noncomputable def carrierLineSlope (N : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, carrierLineSlopeTerm n u

/-- Each critical-line term of the completed carrier is differentiable in the height, with
derivative the termwise line slope. -/
theorem hasDerivAt_carrierLineTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => carrierLineTerm n v) (carrierLineSlopeTerm n u) u := by
  have hexp : ∀ cc : ℂ, HasDerivAt (fun v : ℝ => Complex.exp (cc * v))
      (Complex.exp (cc * u) * cc) u := by
    intro cc
    have hlin : HasDerivAt (fun v : ℝ => cc * (v : ℂ)) cc u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul cc
    exact hlin.cexp
  have hfun : (fun v : ℝ => carrierLineTerm n v) = fun v : ℝ =>
      (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        (archFactor (linePt v) * Complex.exp (-(Complex.I * (Real.log n : ℂ)) * v) +
         archFactor (1 - linePt v) *
           Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * v)) := by
    funext v
    unfold carrierLineTerm
    rw [archFactor_mul_zetaChi (Gammaℝ_ne_zero_of_re_pos (by rw [linePt_re]; norm_num))]
  rw [hfun]
  unfold carrierLineSlopeTerm
  exact (((hasDerivAt_archFactor_line u).mul
      (hexp (-(Complex.I * (Real.log n : ℂ))))).add
    ((hasDerivAt_archFactor_line_reflected u).mul
      (hexp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)))))).const_mul _

/-- **The completed carrier is differentiable along the critical line**, with derivative the
line slope. -/
theorem hasDerivAt_completedGN_line (N : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => completedGN N (linePt v)) (carrierLineSlope N u) u := by
  have hfun : (fun v : ℝ => completedGN N (linePt v)) =
      fun v : ℝ => ∑ n ∈ Finset.Icc 1 N, carrierLineTerm n v :=
    funext fun v => completedGN_line_term_decomp N v
  have hpi : (∑ n ∈ Finset.Icc 1 N, fun v : ℝ => carrierLineTerm n v) =
      fun v : ℝ => ∑ n ∈ Finset.Icc 1 N, carrierLineTerm n v := by
    funext v
    simp
  rw [hfun, ← hpi]
  exact HasDerivAt.sum fun n _ => hasDerivAt_carrierLineTerm n u

/-- The real part of the completed carrier is differentiable along the critical line, with
derivative the real part of the line slope. -/
theorem hasDerivAt_re_completedGN_line (N : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => (completedGN N (linePt v)).re)
      ((carrierLineSlope N u).re) u := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_completedGN_line N u)
  simpa using h

/-! ### §3 The closed-form slope bound -/

/-- Unimodularity of the line oscillations: the exponent is purely imaginary. -/
theorem norm_exp_neg_I_mul_real (r u : ℝ) :
    ‖Complex.exp (-(Complex.I * (r : ℂ)) * (u : ℝ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : ((-(Complex.I * (r : ℂ)) * (u : ℝ)).re) = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- Termwise slope bound: envelope-derivative sups `M₁` and envelope sups `M₀` on both sides
of the reflection bound each termwise slope by `n^{−1/2}·2(M₁ + M₀·log N)`. -/
theorem norm_carrierLineSlopeTerm_le {n N : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N)
    {u M₀ M₁ : ℝ}
    (hM₀ : ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁) :
    ‖carrierLineSlopeTerm n u‖ ≤
      ((n : ℝ) ^ (-(1/2 : ℝ))) * (2 * (M₁ + M₀ * Real.log N)) := by
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) hM₀
  have hlogn0 : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast hn1)
  have hlognN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)
  have hfreq : ‖-(Complex.I * (Real.log n : ℂ))‖ = Real.log n := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlogn0]
  have hfreqr : ‖-(Complex.I * ((-Real.log n : ℝ) : ℂ))‖ = Real.log n := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg hlogn0]
  have hd1 : ‖archFactorDeriv (linePt u) * Complex.I *
      Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u)‖ ≤ M₁ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_exp_neg_I_mul_real, mul_one]
    exact hM₁
  have hd2 : ‖archFactor (linePt u) *
      (Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u) *
        -(Complex.I * (Real.log n : ℂ)))‖ ≤ M₀ * Real.log N := by
    rw [norm_mul, norm_mul, norm_exp_neg_I_mul_real, one_mul, hfreq]
    exact mul_le_mul hM₀ hlognN hlogn0 hM₀0
  have hr1 : ‖archFactorDeriv (1 - linePt u) * -Complex.I *
      Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u)‖ ≤ M₁ := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, mul_one,
      norm_exp_neg_I_mul_real, mul_one]
    exact hM₁r
  have hr2 : ‖archFactor (1 - linePt u) *
      (Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u) *
        -(Complex.I * ((-Real.log n : ℝ) : ℂ)))‖ ≤ M₀ * Real.log N := by
    rw [norm_mul, norm_mul, norm_exp_neg_I_mul_real, one_mul, hfreqr]
    exact mul_le_mul hM₀r hlognN hlogn0 hM₀0
  have hcoef : ‖(((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ)‖ = ((n : ℝ) ^ (-(1/2 : ℝ))) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  unfold carrierLineSlopeTerm
  rw [norm_mul, hcoef]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  calc ‖_ + _‖ ≤ ‖_ + _‖ + ‖_ + _‖ := norm_add_le _ _
    _ ≤ (‖_‖ + ‖_‖) + (‖_‖ + ‖_‖) := add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ (M₁ + M₀ * Real.log N) + (M₁ + M₀ * Real.log N) :=
        add_le_add (add_le_add hd1 hd2) (add_le_add hr1 hr2)
    _ = 2 * (M₁ + M₀ * Real.log N) := by ring

/-- The closed-form line-slope budget: `4√N·(M₁ + M₀·log N)`. -/
noncomputable def carrierSlopeLineBudget (N : ℕ) (M₀ M₁ : ℝ) : ℝ :=
  2 * Real.sqrt N * (2 * (M₁ + M₀ * Real.log N))

/-- **Closed-form bound for the carrier line slope**: with envelope sups `M₀` and
envelope-derivative sups `M₁` on both sides of the reflection, the slope of the completed
carrier along the line is at most `4√N·(M₁ + M₀·log N)` — the square-root telescope carries
the coefficient sum and `log N` carries the frequencies. -/
theorem norm_carrierLineSlope_le (N : ℕ) {u M₀ M₁ : ℝ}
    (hM₀ : ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁) :
    ‖carrierLineSlope N u‖ ≤ carrierSlopeLineBudget N M₀ M₁ := by
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) hM₀
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) hM₁
  have hlogN0 : 0 ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hfac0 : 0 ≤ 2 * (M₁ + M₀ * Real.log N) := by
    have := mul_nonneg hM₀0 hlogN0
    linarith
  unfold carrierLineSlope carrierSlopeLineBudget
  calc ‖∑ n ∈ Finset.Icc 1 N, carrierLineSlopeTerm n u‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖carrierLineSlopeTerm n u‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
          ((n : ℝ) ^ (-(1/2 : ℝ))) * (2 * (M₁ + M₀ * Real.log N)) :=
        Finset.sum_le_sum fun n hn =>
          norm_carrierLineSlopeTerm_le (Finset.mem_Icc.mp hn).1
            (Finset.mem_Icc.mp hn).2 hM₀ hM₀r hM₁ hM₁r
    _ = (∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-(1/2 : ℝ)))) *
          (2 * (M₁ + M₀ * Real.log N)) := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * Real.sqrt N * (2 * (M₁ + M₀ * Real.log N)) :=
        mul_le_mul_of_nonneg_right (sum_rpow_neg_half_le N) hfac0

/-! ### §4 The mass floor for the completed carrier -/

/-- On the critical line the completed carrier is real, so its real part carries the full
modulus. -/
theorem abs_re_completedGN_line_eq_norm (N : ℕ) (u : ℝ) :
    |(completedGN N (linePt u)).re| = ‖completedGN N (linePt u)‖ := by
  have him : (completedGN N (linePt u)).im = 0 :=
    completedGN_im_eq_zero_on_line (by rw [linePt_re])
  have hz : completedGN N (linePt u) = (((completedGN N (linePt u)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simp [him])
  conv_rhs => rw [hz]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- **Anchor bridge**: the product of an archimedean floor with a carrier anchor is a
pointwise floor for `|Re Φ̃_N|` on the line — reality of the completed carrier converts the
modulus product into real-part data. -/
theorem anchor_re_completedGN_line_of_floors (N : ℕ) {τ a₀ m : ℝ}
    (hm0 : 0 ≤ m)
    (ha₀ : a₀ ≤ ‖archFactor (linePt τ)‖)
    (hm : m ≤ ‖gN N (linePt τ)‖) :
    a₀ * m ≤ |(completedGN N (linePt τ)).re| := by
  rw [abs_re_completedGN_line_eq_norm]
  calc a₀ * m ≤ ‖archFactor (linePt τ)‖ * ‖gN N (linePt τ)‖ :=
        mul_le_mul ha₀ hm hm0 (norm_nonneg _)
    _ = ‖completedGN N (linePt τ)‖ := (norm_mul _ _).symm

/-- **Short-interval mass floor for the completed carrier.**  An anchor `c` at the window
center and envelope/derivative sups on the window produce the explicit second-moment floor
`(c/2)²·2·min rz (c/(2·slopeBudget))` — the `S_b` face of the sign-bracket certificates is
a consequence of the anchor face and the envelope calculus. -/
theorem sq_integral_re_completedGN_line_floor_of_anchor (N : ℕ)
    {τ rz c M₀ M₁ : ℝ} (hrz : 0 < rz) (hc : 0 < c)
    (hD : 0 < carrierSlopeLineBudget N M₀ M₁)
    (hM₀ : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hanchor : c ≤ |(completedGN N (linePt τ)).re|) :
    (c / 2) ^ 2 * (2 * min rz (c / (2 * carrierSlopeLineBudget N M₀ M₁))) ≤
      ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2 :=
  sq_integral_floor_of_anchor_slope hrz hc hD
    (fun u _ => hasDerivAt_re_completedGN_line N u)
    (fun u hu =>
      le_trans (Complex.abs_re_le_norm _)
        (norm_carrierLineSlope_le N (hM₀ u hu) (hM₀r u hu) (hM₁ u hu) (hM₁r u hu)))
    hanchor

/-- **Sign bracket from anchor and slope data alone.**  In a window `[τ−rz, τ+rz]` carrying
an anchor `c` at its center, envelope/derivative sups, a line sup `M_line`, and a first
moment strictly below the anchor-generated mass floor, the completed carrier changes sign:
the short-interval second-moment supply of the moment-gap engine is manufactured from the
anchor rather than assumed. -/
theorem exists_completedGN_sign_bracket_of_anchor_slope (N : ℕ)
    {τ rz c M₀ M₁ M_line : ℝ} (hrz : 0 < rz) (hc : 0 < c)
    (hD : 0 < carrierSlopeLineBudget N M₀ M₁)
    (hM₀ : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hanchor : c ≤ |(completedGN N (linePt τ)).re|)
    (hsup : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), |(completedGN N (linePt u)).re| ≤ M_line)
    (hfm : M_line * |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| <
      (c / 2) ^ 2 * (2 * min rz (c / (2 * carrierSlopeLineBudget N M₀ M₁)))) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc (τ - rz) (τ + rz) ∧ t₂ ∈ Set.Icc (τ - rz) (τ + rz) ∧
      t₁ ≤ t₂ ∧ (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0 := by
  have hmin0 : 0 < min rz (c / (2 * carrierSlopeLineBudget N M₀ M₁)) :=
    lt_min hrz (by positivity)
  exact exists_completedGN_sign_bracket_of_moments N (by linarith)
    (by positivity)
    (sq_integral_re_completedGN_line_floor_of_anchor N hrz hc hD
      hM₀ hM₀r hM₁ hM₁r hanchor)
    hsup hfm

end RHTower

namespace RHTower

/-- **Anchor-mass integral ledger endpoint.**  The per-zero window certificate carries no
independent short-interval second-moment face: the long-window energy budget selects an
anchor height `τ` with `m_J ≤ ‖g_N‖`, the archimedean floor upgrades it to the pointwise
anchor `a₀·m_J ≤ |Re Φ̃_N|`, and the point-to-mass converter manufactures the local mass
floor `(a₀m_J/2)²·2·min rz (a₀m_J/(2·slopeBudget))` from the envelope calculus.  The sign
face is the single strict comparison of the local first moment against that floor; all
other sign-face data are envelope sups on the expanded window. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_anchor_mass_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ M₀ M₁ M_line : ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        0 < carrierSlopeLineBudget N M₀ M₁ ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), ‖archFactor (linePt u)‖ ≤ M₀) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), ‖archFactor (1 - linePt u)‖ ≤ M₀) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), ‖archFactorDeriv (linePt u)‖ ≤ M₁) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz),
          |(completedGN N (linePt u)).re| ≤ M_line) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          M_line * |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| <
            (a₀ * m_J / 2) ^ 2 *
              (2 * min rz (a₀ * m_J / (2 * carrierSlopeLineBudget N M₀ M₁)))) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, M₀, M₁, M_line,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hDbud, hM₀, hM₀r, hM₁, hM₁r, hMline, hfm,
    hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  let ε₁ : ℝ := (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
    (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)
  let Rprime : ℝ := R - rz
  let Rτ : ℝ := max |ρ.im - T| |ρ.im - (T + U)|
  have hR'0 : 0 < Rprime := by
    dsimp [Rprime]
    linarith
  have hR'rz : Rprime + rz ≤ R := by
    dsimp [Rprime]
    linarith
  have hρT : |ρ.im - T| ≤ Rτ := le_max_left _ _
  have hρTU : |ρ.im - (T + U)| ≤ Rτ := le_max_right _ _
  have hρquad' : (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < Rprime ^ 2 := by
    simpa [Rτ, Rprime] using hρquad
  have hR0 : 0 ≤ R := (lt_trans h0 hrR).le
  have hP0 : 0 < P := lt_of_lt_of_le (lt_trans h0 hrR) hRP
  have hMJ0 : 0 < M_J := lt_of_lt_of_le zero_lt_one hMJ
  have hrzJ : rz < rJ := by linarith
  have hRJ0 : 0 < RJ := by linarith [h0, hrR, hRrzJ, hrJR, hrz0]
  have hε₁0 : 0 ≤ ε₁ := by
    have hden0 : 0 < 1 / 2 - RJ := by linarith
    have hpow_nonneg : 0 ≤ (M : ℝ) ^ (-(1 / 2 - RJ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    have hmax_nonneg : 0 ≤ max ‖linePt T‖ ‖linePt (T + U)‖ :=
      le_trans (norm_nonneg (linePt T)) (le_max_left _ _)
    have hlhs_nonneg : 0 ≤ (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
        (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ) := by
      exact div_nonneg (mul_nonneg (add_nonneg hmax_nonneg hRJ0.le) hpow_nonneg) hden0.le
    simpa [ε₁] using hlhs_nonneg
  have hδ0 : 0 ≤ δ := by
    have hτT : T ∈ Set.Icc T (T + U) := ⟨le_rfl, by linarith [hU]⟩
    have hsample : linePt T + (RJ : ℂ) ∈
        sphere (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) RJ := by
      simpa [linePt] using linePt_add_radius_mem_sphere (τ := T) hRJ0.le
    exact le_trans (norm_nonneg (emCarrier M (linePt T + (RJ : ℂ)) -
      gN N (linePt T + (RJ : ℂ)))) (hclose T hτT (linePt T + (RJ : ℂ)) hsample)
  have hεδ : 0 ≤ ε₁ + δ := add_nonneg hε₁0 hδ0
  obtain ⟨τ, hτ, hAnchor⟩ :=
    exists_gN_line_anchor_in_window_of_secondMoment_orthogonal_energy N hU hmJ0.le henergy
  have hwinsub : Set.Icc (τ - rz) (τ + rz) ⊆ Set.Icc (T - rz) (T + U + rz) :=
    Set.Icc_subset_Icc (by linarith [hτ.1]) (by linarith [hτ.2])
  have hτexp : τ ∈ Set.Icc (T - rz) (T + U + rz) :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hgNτ : m_J ≤ ‖gN N (linePt τ)‖ := by
    simpa [linePt] using hAnchor
  have hanchor : a₀ * m_J ≤ |(completedGN N (linePt τ)).re| :=
    anchor_re_completedGN_line_of_floors N hmJ0.le (ha₀ τ hτexp) hgNτ
  have hcpos : 0 < a₀ * m_J := mul_pos ha₀0 hmJ0
  obtain ⟨t₁, t₂, ht₁, ht₂, h12, hsign⟩ :=
    exists_completedGN_sign_bracket_of_anchor_slope N hrz0 hcpos hDbud
      (fun u hu => hM₀ u (hwinsub hu)) (fun u hu => hM₀r u (hwinsub hu))
      (fun u hu => hM₁ u (hwinsub hu)) (fun u hu => hM₁r u (hwinsub hu))
      hanchor
      (fun u hu => hMline u (hwinsub hu))
      (hfm τ hτ)
  have ht₁0 : 0 < t₁ := by linarith [ht₁.1, hτ.1]
  have hMG_ball := completedGN_norm_le_line_closedBall_of_sphere hRJ0 hRJ12 (hMG τ hτ)
  have hE_ball : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁ := by
    intro z hz
    exact em_remainder_norm_le_window_closedBall_of_endpoint_bound
      (M := M) (T := T) (U := U) (RJ := RJ) (ε₁ := ε₁) hM hRJ12
      (by dsimp [ε₁]; exact le_rfl)
      τ hτ z (by simpa [linePt] using hz)
  have hclose_ball :=
    emCarrier_gN_norm_le_line_closedBall_of_sphere hM hRJ0 hRJ12 (hclose τ hτ)
  have ha₀_ball : ∀ z : ℂ, z.re = 1 / 2 →
      z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz → a₀ ≤ ‖archFactor z‖ := by
    intro z hzre hz
    have him : z.im ∈ Set.Icc (T - rz) (T + U + rz) :=
      im_mem_expanded_window_of_mem_line_center_closedBall hτ hz
    have hzline : z = linePt z.im := eq_linePt_of_re_eq_half hzre
    rw [hzline]
    exact ha₀ z.im him
  obtain ⟨hcross, hfl⟩ :=
    canonical_cross_em_budgets_of_outer_power_floor_max
      (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ) (R := R)
      (P := P) (M_G := M_G) (a₀ := a₀) (r₀ := r₀) (ε₁ := ε₁) (δ := δ)
      hmJ0 hrz0 hMJ0 hrzJ hengine hP0 ha₀0 h0 hR0 hRrzJ (by
        dsimp [ε₁]
        exact hbudget_outer)
  refine ⟨N, M, ε₁, δ, ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I,
    t₁, t₂, rz, r₀, R, Rprime, P, rJ, RJ, m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁0, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    point_mem_line_center_ball_of_quadratic hR'0
      ((quadratic_target_of_endpoint_abs_im_bounds hρT hρTU hρquad') τ hτ),
    hR'rz, line_center_closedBall_strip hRJ12,
    (fun u hu => line_interval_mem_closedBall_line_center_of_endpoint_bounds
      (T := τ) (U := 0) (by linarith [ht₁.1]) (by linarith [ht₂.2])
      ⟨le_rfl, by linarith⟩ hu),
    (by simpa [linePt] using hsign), hmJ0, hAnchor, hMJ,
    (fun z hz => hbound τ hτ z hz),
    hjensen_floor, hengine, ha₀_ball, ha₀0, hMG_ball, hcross,
    hE_ball, hclose_ball, hfl⟩

end RHTower
