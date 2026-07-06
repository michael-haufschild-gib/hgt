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
