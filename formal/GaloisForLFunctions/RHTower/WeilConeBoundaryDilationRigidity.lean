import GaloisForLFunctions.RHTower.WeilConeBoundaryDilationLogAveraging
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient
import GaloisForLFunctions.RHTower.WeilAbscissaRigidity

/-!
# Boundary-class dilation rigidity of the Weil cone

Let `a, v : ℕ → ℝ` satisfy `Σ |a(n)| n^{−½} (1 + log n) < ∞`, `Σ |v(n)| n^{−½} < ∞` and
`v(0) = v(1) = 0`, and let `λ = Λ ⋆ a + v` be full-cone Weil-positive. Then `a = δ₁` and `v = 0`,
so `Λ` is Weil-positive and the Riemann hypothesis holds.

**Proof.** Put `A(s) = Σ a(n) n^{−s}`, `V(s) = Σ v(n) n^{−s}`, `u = Re A(½ + it)`.

1. *Boundary inequality* (`boundary_ineq_sq`): `(u − 1)·θ'·Z² ≤ Im A·Z Z' − Re V·Z²` at every
   height.
2. *Excess forces a linear-logarithmic mass.* If `u(t₁) > 1`, almost periodicity of `A` on the line
   (an absolutely convergent exponential series) gives relatively dense windows where
   `u ≥ 1 + δ/2`. With the smooth weight `w = S((u − 1)/ε)`, where `S` is the smooth transition,
   `(u − 1)w ≥ 0` everywhere and `≥ ε` on the windows. Since `θ'(t) ≥ ¼ log t`, the integral of
   `(u − 1)θ'w` over `[T, 2T]` is at least `κ T log T`.
3. *The right side is `O(T log log T)`.* After integration by parts against `L_η = ½ log(Z² + η²)`
   with `η = 1/T₂`, it is controlled by `‖V‖_∞ T`, by `∫ log(1 + Z²) ≤ T log(1 + M)` with
   `M ≪ log² T` (mean square), and Littlewood's floor `∫ L_η ≥ −C − K log T`. The same quantities bound the loss of
   the softening factor `Z²/(Z² + η²)`. Comparing `κ T log T` with `O(T log log T)` gives a
   contradiction, so `u ≤ 1` on the line.
4. *Phragmén–Lindelöf* for the bounded function `exp A` gives `Re A ≤ 1` on `Re s ≥ ½`. Since
   `A(1) = 1`, the maximum modulus principle makes `exp A`, hence `A`, constant on `Re s > ½`.
   Uniqueness of Dirichlet coefficients gives `a = δ₁`. Then `λ − Λ = v` has absolute abscissa
   `≤ ½ < 1`, and abscissa rigidity gives `v = 0`.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace RHTower.WeilBoundaryDilation

open RHTower.WeilInfiniteDilation RHTower.WeilFiniteType

variable {a v : ℕ → ℝ}

/-! ## Almost periodicity on the line -/

theorem term_linePt_eq (f : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    LSeries.term f (linePt t) n =
      LSeries.term f (1 / 2) n * GaloisForLFunctions.expChar (-Real.log n) t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlog : Complex.log n = (Real.log n : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
      GaloisForLFunctions.expChar, Complex.cpow_def_of_ne_zero hn0,
      Complex.cpow_def_of_ne_zero hn0, hlog]
    have e : Complex.exp ((Real.log n : ℂ) * linePt t) =
        Complex.exp ((Real.log n : ℂ) * (1 / 2)) *
          (Complex.exp (((-Real.log n * t : ℝ) : ℂ) * I))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      unfold linePt
      push_cast
      ring
    rw [e]
    field_simp

theorem isBohrAlmostPeriodic_LSeries_linePt {f : ℕ → ℂ} (hf : LSeriesSummable f (1 / 2)) :
    HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => LSeries f (linePt t) := by
  have h : (fun t : ℝ => LSeries f (linePt t)) = GaloisForLFunctions.expSeriesCarrier
      (fun n => LSeries.term f (1 / 2) n) (fun n => -Real.log n) := by
    funext t
    simp only [LSeries, GaloisForLFunctions.expSeriesCarrier]
    exact tsum_congr fun n => term_linePt_eq f n t
  rw [h]
  exact GaloisForLFunctions.isBohrAlmostPeriodic_expSeriesCarrier (summable_norm_iff.mpr hf) _

/-! ## Windows of excess and the block lower bound -/

/-- An almost-periodic function exceeding `1 + δ` once exceeds `1 + δ/2` on relatively dense
windows of a fixed width. -/
theorem exists_excess_windows {g : ℝ → ℂ} (hap : HTGeometry.IsBohrAlmostPeriodic g)
    (hgc : Continuous g) {t₁ δ : ℝ} (hδ : 0 < δ) (h1 : 1 + δ ≤ (g t₁).re) :
    ∃ r > 0, ∃ L > 0, ∀ b : ℝ, ∃ s, b ≤ s - r ∧ s + r ≤ b + L ∧
      ∀ x ∈ Icc (s - r) (s + r), 1 + δ / 2 ≤ (g x).re := by
  obtain ⟨r, hr, hball⟩ := Metric.continuous_iff.mp hgc t₁ (δ / 4) (by linarith)
  obtain ⟨L, hL, hdense⟩ := hap (δ / 4) (by linarith)
  refine ⟨r / 2, by linarith, L + r, by linarith, fun b => ?_⟩
  obtain ⟨τ, hτ, hper⟩ := hdense (b - t₁ + r / 2)
  refine ⟨t₁ + τ, by linarith [hτ.1], by linarith [hτ.2], fun x hx => ?_⟩
  have hy : dist (x - τ) t₁ < r := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
  have h2 := hball (x - τ) hy
  have h3 := hper (x - τ)
  rw [sub_add_cancel] at h3
  rw [dist_eq_norm] at h2
  have e1 := Complex.abs_re_le_norm (g (x - τ) - g t₁)
  have e2 := Complex.abs_re_le_norm (g x - g (x - τ))
  rw [Complex.sub_re] at e1 e2
  have := abs_le.mp (e1.trans h2.le)
  have := abs_le.mp (e2.trans h3)
  linarith

/-- Integrating a nonnegative function over `k` consecutive blocks, each containing a window of
width `2r` where it is at least `c`. -/
theorem block_integral_ge {f : ℝ → ℝ} (hfc : Continuous f) (hf0 : ∀ t, 0 ≤ f t) {r L c : ℝ}
    (hr : 0 ≤ r)
    (hwin : ∀ b : ℝ, ∃ s, b ≤ s - r ∧ s + r ≤ b + L ∧ ∀ x ∈ Icc (s - r) (s + r), c ≤ f x)
    (b : ℝ) (k : ℕ) : (k : ℝ) * (2 * r * c) ≤ ∫ t in b..b + k * L, f t := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨s, hs1, hs2, hs3⟩ := hwin (b + k * L)
    have hsplit : ∫ t in b..b + ((k + 1 : ℕ) : ℝ) * L, f t =
        (∫ t in b..b + k * L, f t) + ∫ t in b + k * L..b + ((k + 1 : ℕ) : ℝ) * L, f t :=
      (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
        (hfc.intervalIntegrable _ _)).symm
    have hwin_int : 2 * r * c ≤ ∫ t in b + k * L..b + ((k + 1 : ℕ) : ℝ) * L, f t := by
      have h1 : ∫ t in (s - r)..(s + r), f t ≤
          ∫ t in b + k * L..b + ((k + 1 : ℕ) : ℝ) * L, f t :=
        intervalIntegral.integral_mono_interval hs1 (by linarith) (by push_cast; linarith)
          (Filter.Eventually.of_forall hf0) (hfc.intervalIntegrable _ _)
      have h2 : ∫ t in (s - r)..(s + r), c ≤ ∫ t in (s - r)..(s + r), f t :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          (hfc.intervalIntegrable _ _) hs3
      rw [intervalIntegral.integral_const, smul_eq_mul] at h2
      linarith
    rw [hsplit]
    push_cast at hwin_int ⊢
    linarith

theorem integral_ge_of_windows {f : ℝ → ℝ} (hfc : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {r L c : ℝ} (hL : 0 < L) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hwin : ∀ b : ℝ, ∃ s, b ≤ s - r ∧ s + r ≤ b + L ∧ ∀ x ∈ Icc (s - r) (s + r), c ≤ f x)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    ((T₂ - T₁) / L - 1) * (2 * r * c) ≤ ∫ t in T₁..T₂, f t := by
  set k := ⌊(T₂ - T₁) / L⌋₊ with hk
  have hq : 0 ≤ (T₂ - T₁) / L := div_nonneg (by linarith) hL.le
  have hkle : (k : ℝ) * L ≤ T₂ - T₁ := by
    have := Nat.floor_le hq
    rwa [le_div_iff₀ hL] at this
  have hklt : (T₂ - T₁) / L - 1 ≤ k := by linarith [Nat.lt_floor_add_one ((T₂ - T₁) / L)]
  have h1 := block_integral_ge hfc hf0 hr hwin T₁ k
  have h2 : ∫ t in T₁..T₁ + k * L, f t ≤ ∫ t in T₁..T₂, f t :=
    intervalIntegral.integral_mono_interval le_rfl
      (le_add_of_nonneg_right (by positivity)) (by linarith)
      (Filter.Eventually.of_forall hf0) (hfc.intervalIntegrable _ _)
  have h3 : ((T₂ - T₁) / L - 1) * (2 * r * c) ≤ k * (2 * r * c) :=
    mul_le_mul_of_nonneg_right hklt (by positivity)
  linarith

/-! ## The smooth transition -/

theorem exists_bound_deriv_smoothTransition :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ x, |deriv Real.smoothTransition x| ≤ S := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)
  have hsupp : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hx] with y hy using
          Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [this.deriv_eq]; simp
    · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds hx] with y hy using
          Real.smoothTransition.one_of_one_le (le_of_lt hy)
      rw [this.deriv_eq]; simp
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hsupp
  exact ⟨max C 0, le_max_right _ _, fun x => (by simpa [Real.norm_eq_abs] using hC x :
    |deriv Real.smoothTransition x| ≤ C).trans (le_max_left _ _)⟩

theorem hasDerivAt_smoothTransition (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt

/-! ## The asymptotic comparison -/

theorem eventually_log_log_le {D ε : ℝ} (hD : 0 ≤ D) (hε : 0 < ε) :
    ∀ᶠ T in atTop, Real.log (1 + D * (1 + Real.log (3 * T)) ^ 2) ≤ ε * Real.log T := by
  have hg : Tendsto (fun T : ℝ => 1 + Real.log (3 * T)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)))
  have ho := (Real.isLittleO_log_id_atTop.comp_tendsto hg).bound
    (show (0 : ℝ) < ε / 8 by positivity)
  have hlogT := Real.tendsto_log_atTop.eventually_ge_atTop
    (max 2 (4 * Real.log (1 + D) / ε))
  filter_upwards [ho, hlogT, eventually_ge_atTop (1 : ℝ)] with T h1 h2 hT1
  simp only [Function.comp, id, Real.norm_eq_abs] at h1
  have hT0 : 0 < T := by linarith
  set g := 1 + Real.log (3 * T) with hgdef
  have hlog3 : Real.log (3 * T) = Real.log 3 + Real.log T := Real.log_mul (by norm_num) hT0.ne'
  have hl3 : Real.log 3 < 2 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3) (by norm_num); linarith
  have hl3' : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hm1 : 2 ≤ Real.log T := (le_max_left _ _).trans h2
  have hm2 : 4 * Real.log (1 + D) / ε ≤ Real.log T := (le_max_right _ _).trans h2
  have hg1 : 1 ≤ g := by rw [hgdef, hlog3]; linarith
  have hg3 : g ≤ 3 * Real.log T := by rw [hgdef, hlog3]; linarith
  have hgabs : |g| = g := abs_of_pos (by linarith)
  have hlg : Real.log g ≤ ε / 8 * g := by
    rw [hgabs] at h1; exact (le_abs_self _).trans h1
  have hsplit : Real.log (1 + D * g ^ 2) ≤ Real.log (1 + D) + 2 * Real.log g := by
    have hpos : 0 < 1 + D * g ^ 2 := by positivity
    have hle : 1 + D * g ^ 2 ≤ (1 + D) * g ^ 2 := by nlinarith
    calc Real.log (1 + D * g ^ 2) ≤ Real.log ((1 + D) * g ^ 2) := Real.log_le_log hpos hle
      _ = Real.log (1 + D) + 2 * Real.log g := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have hD' : Real.log (1 + D) ≤ ε / 4 * Real.log T := by
    rw [div_le_iff₀ hε] at hm2; linarith
  nlinarith

theorem eventually_comparison {κ P₁ P₂ P₃ P₄ D : ℝ} (hκ : 0 < κ) (hP₁ : 0 ≤ P₁) (hP₄ : 0 ≤ P₄)
    (hD : 0 ≤ D) :
    ∀ᶠ T in atTop, P₁ * ((T + 1) * Real.log (1 + D * (1 + Real.log (3 * T)) ^ 2)) +
      P₂ * Real.log T + P₃ + P₄ * (T + 1) < κ * ((T - 1) * Real.log T) := by
  have hε : 0 < κ / (4 * (P₁ + 1)) := by positivity
  filter_upwards [eventually_log_log_le hD hε,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (8 * P₄ / κ)),
    eventually_ge_atTop (4 * (|P₂| + |P₃| + 1) / κ + 3)] with T h1 h2' h3
  have h2 : 1 ≤ Real.log T := (le_max_left _ _).trans h2'
  have h2'' : 8 * P₄ / κ ≤ Real.log T := (le_max_right _ _).trans h2'
  set ℓ := Real.log (1 + D * (1 + Real.log (3 * T)) ^ 2)
  have hT3 : 3 ≤ T := by
    have : 0 ≤ 4 * (|P₂| + |P₃| + 1) / κ := by positivity
    linarith
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by nlinarith [sq_nonneg (1 + Real.log (3 * T))])
  have hP1 : P₁ * ((T + 1) * ℓ) ≤ κ / 2 * (T * Real.log T) := by
    have hle : P₁ * ℓ ≤ κ / 4 * Real.log T := by
      have := mul_le_mul_of_nonneg_left h1 hP₁
      have hk : P₁ * (κ / (4 * (P₁ + 1))) ≤ κ / 4 := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]; nlinarith
      nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ T by linarith)]
    have hT1 : T + 1 ≤ 2 * T := by linarith
    nlinarith [mul_nonneg hP₁ hℓ0]
  have hmain : (|P₂| + |P₃| + 1) * Real.log T ≤ κ / 4 * ((T - 3) * Real.log T) := by
    have hq : 4 * (|P₂| + |P₃| + 1) / κ ≤ T - 3 := by linarith
    rw [div_le_iff₀ hκ] at hq
    have hl0 : 0 ≤ Real.log T := by linarith
    nlinarith
  have hP2 : P₂ * Real.log T ≤ |P₂| * Real.log T :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have hP3 : P₃ ≤ |P₃| * Real.log T := by
    have := le_abs_self P₃
    nlinarith [abs_nonneg P₃]
  have hpos : 0 ≤ κ * ((T - 1) * Real.log T) :=
    mul_nonneg hκ.le (mul_nonneg (by linarith) (by linarith))
  have hP4 : P₄ * (T + 1) ≤ κ / 4 * ((T - 1) * Real.log T) := by
    rw [div_le_iff₀ hκ] at h2''
    have hT1 : T + 1 ≤ 2 * (T - 1) := by linarith
    have hl0 : 0 ≤ Real.log T := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hT1 hP₄]
  linarith

/-! ## The per-height inequality -/

/-- **The integrated boundary inequality, bounded on both sides.**  For a weight `w ∈ [0, 1]`
with `|w'| ≤ W₁`, if `f = (Re A − 1) w` satisfies `0 ≤ f ≤ β` and `θ' ∈ [Θmin, Θmax]` on
`[T₁, T₂]`, then the excess mass `Θmin ∫ f` is bounded by the logarithmic averages of `Z`. -/
theorem per_height_ineq (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2))
    {η T₁ T₂ Θmin Θmax β W₁ : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hT : T₁ ≤ T₂)
    (hΘ : ∀ t ∈ Icc T₁ T₂, Θmin ≤ gammaHardyPhaseRate t ∧ gammaHardyPhaseRate t ≤ Θmax)
    (hΘ0 : 0 ≤ Θmin) (hβ : 0 ≤ β)
    {w w' : ℝ → ℝ} (hw : ∀ t, HasDerivAt w (w' t) t) (hwc : Continuous w')
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∀ t, w t ≤ 1) (hw' : ∀ t, |w' t| ≤ W₁)
    (hf0 : ∀ t, 0 ≤ ((dilSeries a (linePt t)).re - 1) * w t)
    (hfβ : ∀ t, ((dilSeries a (linePt t)).re - 1) * w t ≤ β) :
    Θmin * (∫ t in T₁..T₂, ((dilSeries a (linePt t)).re - 1) * w t) -
        β * Θmax * (η * (T₂ - T₁) + ((∫ t in T₁..T₂, Real.log (1 + hardyZ t ^ 2)) -
          2 * ∫ t in T₁..T₂, softLog η t) / Real.log (1 / (2 * η))) ≤
      (∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖) *
          (|softLog η T₂| + |softLog η T₁|) +
        ((∑' n, ‖LSeries.term (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) n‖) +
          (∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖) * W₁) *
        ((∫ t in T₁..T₂, Real.log (1 + hardyZ t ^ 2)) - ∫ t in T₁..T₂, softLog η t) +
      (∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖) * (T₂ - T₁) := by
  set α := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ with hα
  set α₁ := ∑' n, ‖LSeries.term (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) n‖ with hα₁
  set Λ := Real.log (1 / (2 * η)) with hΛ
  have hΛ0 : 0 < Λ := Real.log_pos (by rw [lt_div_iff₀ (by positivity)]; linarith)
  have hBn : ∀ t, ‖dilSeries a (linePt t)‖ ≤ α := fun t => norm_LSeries_linePt_le ha.half t
  have hB'n : ∀ t, ‖lineDeriv a t‖ ≤ α₁ := fun t => by
    unfold lineDeriv
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact norm_LSeries_linePt_le hlog t
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hBn 0)
  have hBc := continuous_lineSeries ha
  have hB'c := continuous_lineDeriv hlog
  have hwcont : Continuous w := continuous_iff_continuousAt.2 fun t => (hw t).continuousAt
  have hZc : Continuous hardyZ := differentiable_hardyZ.continuous
  have hpos : ∀ t, hardyZ t ^ 2 + η ^ 2 ≠ 0 := fun t => by positivity
  have hfc : Continuous fun t => ((dilSeries a (linePt t)).re - 1) * w t :=
    ((Complex.continuous_re.comp hBc).sub continuous_const).mul hwcont
  have hL1c : Continuous fun t => Real.log (1 + hardyZ t ^ 2) :=
    (continuous_const.add (hZc.pow 2)).log fun t =>
      (show (0 : ℝ) < 1 + hardyZ t ^ 2 by positivity).ne'
  have hsLc := continuous_softLog hη
  have hq : Continuous fun t => hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2) :=
    (hZc.pow 2).div ((hZc.pow 2).add continuous_const) hpos
  -- the lower bound of the regularized integrand
  have hlow : ∀ t ∈ Icc T₁ T₂,
      Θmin * (((dilSeries a (linePt t)).re - 1) * w t) -
          β * Θmax * (η + (Real.log (1 + hardyZ t ^ 2) - 2 * softLog η t) / Λ) ≤
        ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * w t *
          (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)) := by
    intro t ht
    obtain ⟨hΘl, hΘu⟩ := hΘ t ht
    have hf := hf0 t
    have hfb := hfβ t
    have hΘt0 : 0 ≤ gammaHardyPhaseRate t := hΘ0.trans hΘl
    have hp : 0 < hardyZ t ^ 2 + η ^ 2 := by positivity
    have hqe : hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2) = 1 - η ^ 2 / (hardyZ t ^ 2 + η ^ 2) := by
      field_simp; ring
    have hd := softening_defect_le hη hη4 t
    have hd0 : 0 ≤ η ^ 2 / (hardyZ t ^ 2 + η ^ 2) := by positivity
    set f := ((dilSeries a (linePt t)).re - 1) * w t with hfdef
    have e : ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * w t *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)) =
        f * gammaHardyPhaseRate t -
          (f * gammaHardyPhaseRate t) * (η ^ 2 / (hardyZ t ^ 2 + η ^ 2)) := by
      rw [hqe, hfdef]; ring
    rw [e]
    have h1 : Θmin * f ≤ f * gammaHardyPhaseRate t := by
      nlinarith [mul_le_mul_of_nonneg_left hΘl hf]
    have h2 : f * gammaHardyPhaseRate t ≤ β * Θmax := by
      nlinarith [mul_le_mul_of_nonneg_right hfb hΘt0, mul_le_mul_of_nonneg_left hΘu hβ]
    have hd' : η ^ 2 / (hardyZ t ^ 2 + η ^ 2) ≤
        η + (Real.log (1 + hardyZ t ^ 2) - 2 * softLog η t) / Λ := by
      have : 2 * (Real.log (1 + hardyZ t ^ 2) / 2 - softLog η t) / Λ =
          (Real.log (1 + hardyZ t ^ 2) - 2 * softLog η t) / Λ := by ring
      linarith
    have hβΘ : 0 ≤ β * Θmax := mul_nonneg hβ (hΘt0.trans hΘu)
    have h3 : (f * gammaHardyPhaseRate t) * (η ^ 2 / (hardyZ t ^ 2 + η ^ 2)) ≤
        β * Θmax * (η + (Real.log (1 + hardyZ t ^ 2) - 2 * softLog η t) / Λ) :=
      (mul_le_mul_of_nonneg_right h2 hd0).trans (mul_le_mul_of_nonneg_left hd' hβΘ)
    linarith
  -- integrate the lower bound
  have hI1 : IntervalIntegrable (fun t => Θmin * (((dilSeries a (linePt t)).re - 1) * w t))
      volume T₁ T₂ := (continuous_const.mul hfc).intervalIntegrable _ _
  have hI3 : IntervalIntegrable
      (fun t => (Real.log (1 + hardyZ t ^ 2) - 2 * softLog η t) / Λ) volume T₁ T₂ :=
    ((hL1c.sub (continuous_const.mul hsLc)).div_const _).intervalIntegrable _ _
  have hI2 : IntervalIntegrable
      (fun t => β * Θmax * (η + (Real.log (1 + hardyZ t ^ 2) - 2 * softLog η t) / Λ))
      volume T₁ T₂ :=
    (continuous_const.mul (continuous_const.add
      ((hL1c.sub (continuous_const.mul hsLc)).div_const _))).intervalIntegrable _ _
  have hIreg : IntervalIntegrable (fun t => ((dilSeries a (linePt t)).re - 1) *
      gammaHardyPhaseRate t * w t * (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))) volume T₁ T₂ :=
    (((((Complex.continuous_re.comp hBc).sub continuous_const).mul
      continuous_gammaHardyPhaseRate).mul hwcont).mul hq).intervalIntegrable _ _
  have hlowint : ∫ t in T₁..T₂, (Θmin * (((dilSeries a (linePt t)).re - 1) * w t) -
        β * Θmax * (η + (Real.log (1 + hardyZ t ^ 2) - 2 * softLog η t) / Λ)) ≤
      ∫ t in T₁..T₂, ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * w t *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)) :=
    intervalIntegral.integral_mono_on hT (hI1.sub hI2) hIreg hlow
  have hI4 : IntervalIntegrable (fun t => 2 * softLog η t) volume T₁ T₂ :=
    (continuous_const.mul hsLc).intervalIntegrable _ _
  have heval : ∫ t in T₁..T₂, (Θmin * (((dilSeries a (linePt t)).re - 1) * w t) -
        β * Θmax * (η + (Real.log (1 + hardyZ t ^ 2) - 2 * softLog η t) / Λ)) =
      Θmin * (∫ t in T₁..T₂, ((dilSeries a (linePt t)).re - 1) * w t) -
        β * Θmax * (η * (T₂ - T₁) + ((∫ t in T₁..T₂, Real.log (1 + hardyZ t ^ 2)) -
          2 * ∫ t in T₁..T₂, softLog η t) / Λ) := by
    rw [intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const hI3, intervalIntegral.integral_const,
      intervalIntegral.integral_div,
      intervalIntegral.integral_sub (hL1c.intervalIntegrable _ _) hI4,
      intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  rw [heval] at hlowint
  -- the integration by parts
  have hibp := integral_regularized_le ha hv hW hlog hη hT hw hwc hw0
  -- the regular part
  set αV := ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖ with hαV
  have hVn : ∀ t, ‖regSeries v (linePt t)‖ ≤ αV := fun t => norm_LSeries_linePt_le hv.summable t
  have hVc : Continuous fun t => regSeries v (linePt t) := continuous_LSeries_linePt hv.summable
  have hreg : -(∫ t in T₁..T₂, (regSeries v (linePt t)).re * w t *
      (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))) ≤ αV * (T₂ - T₁) := by
    have hpt : ∀ t ∈ Icc T₁ T₂, -((regSeries v (linePt t)).re * w t *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))) ≤ αV := by
      intro t _
      have hp : 0 < hardyZ t ^ 2 + η ^ 2 := by positivity
      have hq0 : 0 ≤ hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2) := by positivity
      have hq1 : hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2) ≤ 1 := by
        rw [div_le_one hp]; nlinarith
      have hre : |(regSeries v (linePt t)).re| ≤ αV := (Complex.abs_re_le_norm _).trans (hVn t)
      have hwq : |w t * (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (hw0 t), abs_of_nonneg hq0]
        nlinarith [hw0 t, hw1 t]
      have h := neg_le_abs ((regSeries v (linePt t)).re * (w t *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))))
      rw [abs_mul] at h
      have hαV0 : 0 ≤ αV := (abs_nonneg _).trans hre
      have : |(regSeries v (linePt t)).re| * |w t * (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))| ≤
          αV := by nlinarith [abs_nonneg ((regSeries v (linePt t)).re),
            abs_nonneg (w t * (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)))]
      calc -((regSeries v (linePt t)).re * w t * (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)))
          = -((regSeries v (linePt t)).re * (w t *
            (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2)))) := by ring
        _ ≤ αV := h.trans this
    have hm : ∫ t in T₁..T₂, -((regSeries v (linePt t)).re * w t *
        (hardyZ t ^ 2 / (hardyZ t ^ 2 + η ^ 2))) ≤ ∫ _ in T₁..T₂, αV :=
      intervalIntegral.integral_mono_on hT
        ((((Complex.continuous_re.comp hVc).mul hwcont).mul hq).neg.intervalIntegrable _ _)
        intervalIntegrable_const hpt
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const, smul_eq_mul] at hm
    linarith
  -- endpoint bounds
  have hend : ∀ T', (dilSeries a (linePt T')).im * w T' * softLog η T' ≤ α * |softLog η T'| ∧
      -((dilSeries a (linePt T')).im * w T' * softLog η T') ≤ α * |softLog η T'| := by
    intro T'
    have hv : |(dilSeries a (linePt T')).im| ≤ α :=
      (Complex.abs_im_le_norm _).trans (hBn T')
    have hwa : |w T'| ≤ 1 := by rw [abs_of_nonneg (hw0 T')]; exact hw1 T'
    have habs : |(dilSeries a (linePt T')).im * w T' * softLog η T'| ≤ α * |softLog η T'| := by
      rw [abs_mul, abs_mul]
      calc |(dilSeries a (linePt T')).im| * |w T'| * |softLog η T'|
          ≤ α * 1 * |softLog η T'| := by gcongr
        _ = α * |softLog η T'| := by ring
    exact ⟨(le_abs_self _).trans habs, (neg_le_abs _).trans habs⟩
  -- the interior term
  set B₁ := α₁ + α * W₁ with hB₁
  have hgb : ∀ t, |(lineDeriv a t).im * w t + (dilSeries a (linePt t)).im * w' t| ≤ B₁ := by
    intro t
    have h1 : |(lineDeriv a t).im| ≤ α₁ := (Complex.abs_im_le_norm _).trans (hB'n t)
    have h2 : |(dilSeries a (linePt t)).im| ≤ α := (Complex.abs_im_le_norm _).trans (hBn t)
    have hwa : |w t| ≤ 1 := by rw [abs_of_nonneg (hw0 t)]; exact hw1 t
    calc |(lineDeriv a t).im * w t + (dilSeries a (linePt t)).im * w' t|
        ≤ |(lineDeriv a t).im| * |w t| + |(dilSeries a (linePt t)).im| * |w' t| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ α₁ * 1 + α * W₁ := by gcongr; exact hw' t
      _ = B₁ := by ring
  have hB₁0 : 0 ≤ B₁ := (abs_nonneg _).trans (hgb 0)
  have hgc : Continuous fun t => (lineDeriv a t).im * w t + (dilSeries a (linePt t)).im * w' t :=
    ((Complex.continuous_im.comp hB'c).mul hwcont).add ((Complex.continuous_im.comp hBc).mul hwc)
  have hmid : -(∫ t in T₁..T₂, ((lineDeriv a t).im * w t +
      (dilSeries a (linePt t)).im * w' t) * softLog η t) ≤
      B₁ * ((∫ t in T₁..T₂, Real.log (1 + hardyZ t ^ 2)) - ∫ t in T₁..T₂, softLog η t) := by
    have hpt : ∀ t ∈ Icc T₁ T₂, -(((lineDeriv a t).im * w t +
        (dilSeries a (linePt t)).im * w' t) * softLog η t) ≤
        B₁ * (Real.log (1 + hardyZ t ^ 2) - softLog η t) := by
      intro t _
      have h1 := hgb t
      have h2 := abs_softLog_le hη (by linarith) t
      have h3 : -(((lineDeriv a t).im * w t + (dilSeries a (linePt t)).im * w' t) *
          softLog η t) ≤ |(lineDeriv a t).im * w t + (dilSeries a (linePt t)).im * w' t| *
            |softLog η t| := by
        rw [← abs_mul]; exact neg_le_abs _
      calc _ ≤ _ := h3
        _ ≤ B₁ * |softLog η t| := by gcongr
        _ ≤ B₁ * (Real.log (1 + hardyZ t ^ 2) - softLog η t) :=
          mul_le_mul_of_nonneg_left h2 hB₁0
    have hm : ∫ t in T₁..T₂, -(((lineDeriv a t).im * w t +
        (dilSeries a (linePt t)).im * w' t) * softLog η t) ≤
        ∫ t in T₁..T₂, B₁ * (Real.log (1 + hardyZ t ^ 2) - softLog η t) :=
      intervalIntegral.integral_mono_on hT ((hgc.mul hsLc).neg.intervalIntegrable _ _)
        ((continuous_const.mul (hL1c.sub hsLc)).intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hL1c.intervalIntegrable _ _)
        (hsLc.intervalIntegrable _ _)] at hm
    exact hm
  linarith [(hend T₂).1, (hend T₁).2]

/-! ## Bounds for the archimedean phase rate -/

theorem log_two_pi_lt_two : Real.log (2 * Real.pi) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hpi := Real.pi_lt_d2
  nlinarith

theorem gammaHardyPhaseRate_bounds {t : ℝ} (ht : 20 ≤ t) :
    Real.log t / 2 - 2 ≤ gammaHardyPhaseRate t ∧ gammaHardyPhaseRate t ≤ Real.log t / 2 + 1 := by
  have ht0 : 0 < t := by linarith
  have hb := gammaHardyPhaseRate_sub_log_conductor_bound ht0
  have hsmall : 33 / (16 * t ^ 2) + Real.pi / (2 * t) ≤ 1 := by
    have hpi := Real.pi_lt_d2
    have h1 : 33 / (16 * t ^ 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : Real.pi / (2 * t) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hlog : Real.log (t / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) :=
    Real.log_div ht0.ne' (by positivity)
  have h2pi := log_two_pi_lt_two
  have h2pi0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  rw [hlog] at hb
  obtain ⟨hb1, hb2⟩ := abs_le.mp (hb.trans hsmall)
  constructor <;> linarith

/-! ## Numerical bookkeeping -/

theorem log_le_log_add_two {T T₂ : ℝ} (hT : 0 < T) (h1 : T ≤ T₂) (h2 : T₂ ≤ 3 * T) :
    Real.log T ≤ Real.log T₂ ∧ Real.log T₂ ≤ Real.log T + 2 := by
  have hlog3 : Real.log 3 < 2 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3) (by norm_num); linarith
  refine ⟨Real.log_le_log hT h1, ?_⟩
  have h := Real.log_le_log (by linarith) h2
  rw [Real.log_mul (by norm_num) hT.ne'] at h
  linarith

/-- The concavity bound with the mean square, on a window `[T₁, T₂] ⊆ [T, 2T + 1]`. -/
theorem integral_log_one_add_hardyZ_sq_le {D T T₁ T₂ : ℝ} (hD : 0 ≤ D)
    (hT : 40 ≤ T) (h1 : T ≤ T₁) (h1' : T₁ ≤ T + 1) (h2 : 2 * T ≤ T₂) (h2' : T₂ ≤ 2 * T + 1)
    (hms : ∫ t in T₁..T₂, hardyZ t ^ 2 ≤ D * (T₂ + 1) * (1 + Real.log (T₂ + 1)) ^ 2) :
    ∫ t in T₁..T₂, Real.log (1 + hardyZ t ^ 2) ≤
      (T + 1) * Real.log (1 + 6 * D * (1 + Real.log (3 * T)) ^ 2) := by
  have hlen : 0 < T₂ - T₁ := by linarith
  obtain ⟨M, hM⟩ : ∃ M, M = D * (T₂ + 1) * (1 + Real.log (T₂ + 1)) ^ 2 / (T₂ - T₁) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; have : 0 ≤ T₂ + 1 := by linarith
                         positivity
  have hmean : ∫ t in T₁..T₂, hardyZ t ^ 2 ≤ M * (T₂ - T₁) := by
    rw [hM, div_mul_cancel₀ _ hlen.ne']; exact hms
  have hc := integral_log_one_add_le (f := fun t => hardyZ t ^ 2)
    (differentiable_hardyZ.continuous.pow 2) (fun t => sq_nonneg _) (by linarith) hM0 hmean
  have hr6 : (T₂ + 1) / (T₂ - T₁) ≤ 6 := by
    rw [div_le_iff₀ hlen]; linarith
  have hl : (1 + Real.log (T₂ + 1)) ^ 2 ≤ (1 + Real.log (3 * T)) ^ 2 := by
    have h0 : 0 ≤ Real.log (T₂ + 1) := Real.log_nonneg (by linarith)
    have h3 : Real.log (T₂ + 1) ≤ Real.log (3 * T) := Real.log_le_log (by linarith) (by linarith)
    have : 1 + Real.log (T₂ + 1) ≤ 1 + Real.log (3 * T) := by linarith
    exact pow_le_pow_left₀ (by linarith) this 2
  have hMle : M ≤ 6 * D * (1 + Real.log (3 * T)) ^ 2 := by
    have e : M = D * ((T₂ + 1) / (T₂ - T₁)) * (1 + Real.log (T₂ + 1)) ^ 2 := by
      rw [hM]; ring
    rw [e]
    calc D * ((T₂ + 1) / (T₂ - T₁)) * (1 + Real.log (T₂ + 1)) ^ 2
        ≤ D * 6 * (1 + Real.log (3 * T)) ^ 2 := by gcongr
      _ = 6 * D * (1 + Real.log (3 * T)) ^ 2 := by ring
  have hlM : Real.log (1 + M) ≤ Real.log (1 + 6 * D * (1 + Real.log (3 * T)) ^ 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlM0 : 0 ≤ Real.log (1 + M) := Real.log_nonneg (by linarith)
  calc ∫ t in T₁..T₂, Real.log (1 + hardyZ t ^ 2) ≤ (T₂ - T₁) * Real.log (1 + M) := hc
    _ ≤ (T + 1) * Real.log (1 + M) := mul_le_mul_of_nonneg_right (by linarith) hlM0
    _ ≤ (T + 1) * Real.log (1 + 6 * D * (1 + Real.log (3 * T)) ^ 2) :=
        mul_le_mul_of_nonneg_left hlM (by linarith)

/-- The softened logarithm at a height `T' ∈ [T, 3T]`, with `η = 1/T₂`, `T₂ ≤ 3T`. -/
theorem abs_softLog_endpoint_le {T T' T₂ : ℝ} (hT : 40 ≤ T) (h1 : T ≤ T') (h2 : T' ≤ 3 * T)
    (h3 : T ≤ T₂) (h4 : T₂ ≤ 3 * T) :
    |softLog (1 / T₂) T'| ≤ 3 * Real.log T + 8 := by
  have hT0 : 0 < T := by linarith
  have hT₂0 : 0 < T₂ := by linarith
  have h := abs_softLog_le_log (η := 1 / T₂) (by positivity)
    (by rw [div_le_one hT₂0]; linarith) T'
  rw [one_div_one_div] at h
  have hlT₂ := (log_le_log_add_two hT0 h3 h4).2
  have hT'2 : 2 ≤ |T'| := by rw [abs_of_pos (by linarith)]; linarith
  have hz := norm_riemannZeta_le_of_half_le_re (le_refl (1 / 2 : ℝ)) hT'2
  rw [ofReal_half_add_eq_linePt, norm_riemannZeta_linePt, abs_of_pos (by linarith : (0 : ℝ) < T')]
    at hz
  have hZ2 : hardyZ T' ^ 2 ≤ (2 + 4 * T') ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have hbig : 1 + hardyZ T' ^ 2 ≤ 225 * T ^ 2 := by nlinarith
  have hl225 : Real.log 225 < 6 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hp := pow_lt_pow_left₀ he (by norm_num) (by norm_num : (6 : ℕ) ≠ 0)
    rw [h6]; norm_num at hp; linarith
  have hl1 : Real.log (1 + hardyZ T' ^ 2) ≤ Real.log 225 + 2 * Real.log T := by
    have := Real.log_le_log (by positivity) hbig
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  linarith

/-- **The final comparison**, in purely numerical form. -/
theorem excess_comparison {κ r ε L X T l₂ ℓ J₁ J₂ C K α β B₁ η len Λ I s₁ s₂ γ αV : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hL : 0 < L) (hκ : κ = r * ε / (2 * L)) (hX : 8 ≤ X)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hB₁ : 0 ≤ B₁) (hK : 0 ≤ K)
    (H : X / 4 * I - β * l₂ * (η * len + (J₁ - 2 * J₂) / Λ) ≤
      α * (|s₂| + |s₁|) + B₁ * (J₁ - J₂) + γ) (hγ : γ ≤ αV * (T + 1))
    (hI : ((T - 1) / L - 1) * (2 * r * ε) ≤ I)
    (hJ₁ : J₁ ≤ (T + 1) * ℓ) (hJ₂ : -(C + K * l₂) ≤ J₂) (hJ12 : 0 ≤ J₁ - 2 * J₂)
    (hs₁ : |s₁| ≤ 3 * X + 8) (hs₂ : |s₂| ≤ 3 * X + 8)
    (hl1 : X ≤ l₂) (hl2 : l₂ ≤ X + 2) (hΛ : X ≤ Λ) (hη1 : η * len ≤ 1) :
    κ * ((T - 1) * X) ≤ (2 * β + B₁) * ((T + 1) * ℓ) +
      (r * ε / 2 + β + 4 * β * K + 6 * α + B₁ * K) * X +
      (2 * β + 4 * β * C + 8 * β * K + 16 * α + B₁ * C + 2 * B₁ * K) + αV * (T + 1) := by
  have hX0 : 0 ≤ X / 4 := by linarith
  have hLHS : κ * ((T - 1) * X) - r * ε / 2 * X ≤ X / 4 * I := by
    have h := mul_le_mul_of_nonneg_left hI hX0
    have e : X / 4 * (((T - 1) / L - 1) * (2 * r * ε)) = κ * ((T - 1) * X) - r * ε / 2 * X := by
      rw [hκ]; field_simp; ring
    linarith
  have hΛ0 : 0 < Λ := by linarith
  have hQ : (J₁ - 2 * J₂) / Λ ≤ (J₁ - 2 * J₂) / X :=
    div_le_div_of_nonneg_left hJ12 (by linarith) hΛ
  have hl0 : 0 ≤ l₂ := by linarith
  have hΘQ : l₂ * ((J₁ - 2 * J₂) / X) ≤ 2 * (J₁ - 2 * J₂) := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have h1 : l₂ * (η * len) ≤ X + 2 := by nlinarith
  have h2 : l₂ * ((J₁ - 2 * J₂) / Λ) ≤ 2 * (J₁ - 2 * J₂) :=
    (mul_le_mul_of_nonneg_left hQ hl0).trans hΘQ
  have h3 : J₁ - 2 * J₂ ≤ (T + 1) * ℓ + 2 * C + 2 * K * (X + 2) := by nlinarith
  have hpen : β * l₂ * (η * len + (J₁ - 2 * J₂) / Λ) ≤
      β * ((X + 2) + 2 * ((T + 1) * ℓ + 2 * C + 2 * K * (X + 2))) := by
    have : l₂ * (η * len + (J₁ - 2 * J₂) / Λ) ≤
        (X + 2) + 2 * ((T + 1) * ℓ + 2 * C + 2 * K * (X + 2)) := by
      rw [mul_add]; linarith
    calc β * l₂ * (η * len + (J₁ - 2 * J₂) / Λ)
        = β * (l₂ * (η * len + (J₁ - 2 * J₂) / Λ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hβ
  have hend : α * (|s₂| + |s₁|) ≤ α * (2 * (3 * X + 8)) :=
    mul_le_mul_of_nonneg_left (by linarith) hα
  have h4 : J₁ - J₂ ≤ (T + 1) * ℓ + C + K * (X + 2) := by nlinarith
  have hint : B₁ * (J₁ - J₂) ≤ B₁ * ((T + 1) * ℓ + C + K * (X + 2)) :=
    mul_le_mul_of_nonneg_left h4 hB₁
  linarith

/-! ## Re A ≤ 1 on the critical line -/

/-- The excess weight: if `Re A(½ + it₁) > 1`, a smooth weight `w ∈ [0, 1]` makes
`(Re A − 1) w` nonnegative, bounded, and at least `ε` on relatively dense windows. -/
theorem exists_excess_weight (ha : HalfSummable a)
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) {t₁ : ℝ}
    (h : 1 < (dilSeries a (linePt t₁)).re) :
    ∃ r > 0, ∃ L > 0, ∃ ε > 0, ∃ W₁ ≥ 0, ∃ w w' : ℝ → ℝ, (∀ t, HasDerivAt w (w' t) t) ∧
      Continuous w' ∧ (∀ t, 0 ≤ w t) ∧ (∀ t, w t ≤ 1) ∧ (∀ t, |w' t| ≤ W₁) ∧
      (∀ t, 0 ≤ ((dilSeries a (linePt t)).re - 1) * w t) ∧
      (∀ t, ((dilSeries a (linePt t)).re - 1) * w t ≤
        ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ + 1) ∧
      Continuous (fun t => ((dilSeries a (linePt t)).re - 1) * w t) ∧
      ∀ b : ℝ, ∃ s, b ≤ s - r ∧ s + r ≤ b + L ∧
        ∀ x ∈ Icc (s - r) (s + r), ε ≤ ((dilSeries a (linePt x)).re - 1) * w x := by
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = (dilSeries a (linePt t₁)).re - 1 := ⟨_, rfl⟩
  have hδ : 0 < δ := by linarith
  obtain ⟨r, hr, L, hL, hwin⟩ := exists_excess_windows
    (isBohrAlmostPeriodic_LSeries_linePt ha.half) (continuous_lineSeries ha) hδ
    (show 1 + δ ≤ (dilSeries a (linePt t₁)).re by linarith)
  have hε : 0 < δ / 2 := by positivity
  obtain ⟨S, hS0, hS⟩ := exists_bound_deriv_smoothTransition
  have hBn : ∀ t, ‖dilSeries a (linePt t)‖ ≤ ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ :=
    fun t => norm_LSeries_linePt_le ha.half t
  have hB'n : ∀ t, ‖lineDeriv a t‖ ≤
      ∑' n, ‖LSeries.term (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) n‖ := fun t => by
    unfold lineDeriv
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact norm_LSeries_linePt_le hlog t
  have hα₁0 : 0 ≤ ∑' n, ‖LSeries.term (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) n‖ :=
    (norm_nonneg _).trans (hB'n 0)
  have hu : ∀ t, HasDerivAt (fun t => (dilSeries a (linePt t)).re) (lineDeriv a t).re t :=
    fun t => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_lineSeries ha hlog t)
  have huc : Continuous fun t => (dilSeries a (linePt t)).re :=
    Complex.continuous_re.comp (continuous_lineSeries ha)
  refine ⟨r, hr, L, hL, δ / 2, hε,
    S * ((∑' n, ‖LSeries.term (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) n‖) / (δ / 2)),
    by positivity,
    fun t => Real.smoothTransition (((dilSeries a (linePt t)).re - 1) / (δ / 2)),
    fun t => deriv Real.smoothTransition (((dilSeries a (linePt t)).re - 1) / (δ / 2)) *
      ((lineDeriv a t).re / (δ / 2)), fun t => ?_, ?_, fun t => Real.smoothTransition.nonneg _,
    fun t => Real.smoothTransition.le_one _, fun t => ?_, fun t => ?_, fun t => ?_, ?_,
    fun b => ?_⟩
  · exact (hasDerivAt_smoothTransition _).comp t (((hu t).sub_const 1).div_const (δ / 2))
  · exact (((Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)).comp
      ((huc.sub continuous_const).div_const _)).mul
      ((Complex.continuous_re.comp (continuous_lineDeriv hlog)).div_const _)
  · rw [abs_mul, abs_div, abs_of_pos hε]
    have h1 : |(lineDeriv a t).re| ≤
        ∑' n, ‖LSeries.term (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) n‖ :=
      (Complex.abs_re_le_norm _).trans (hB'n t)
    gcongr
    exact hS _
  · beta_reduce
    by_cases hc : (dilSeries a (linePt t)).re - 1 ≤ 0
    · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hc hε.le),
        mul_zero]
    · exact mul_nonneg (by linarith) (Real.smoothTransition.nonneg _)
  · have h1 : (dilSeries a (linePt t)).re ≤ ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ :=
      (Complex.re_le_norm _).trans (hBn t)
    have h0 := Real.smoothTransition.nonneg (((dilSeries a (linePt t)).re - 1) / (δ / 2))
    have h1' := Real.smoothTransition.le_one (((dilSeries a (linePt t)).re - 1) / (δ / 2))
    by_cases hc : (dilSeries a (linePt t)).re - 1 ≤ 0
    · nlinarith [norm_nonneg (dilSeries a (linePt t)), hBn t]
    · nlinarith
  · exact (huc.sub continuous_const).mul
      ((Real.smoothTransition.contDiff (n := 0)).continuous.comp
        ((huc.sub continuous_const).div_const _))
  · obtain ⟨s, h1, h2, h3⟩ := hwin b
    refine ⟨s, h1, h2, fun x hx => ?_⟩
    have hx := h3 x hx
    beta_reduce
    rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith), mul_one]
    linarith

/-- **The boundary values of `A` have real part at most one.** -/
theorem re_lineSeries_le_one (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) (t₁ : ℝ) :
    (dilSeries a (linePt t₁)).re ≤ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hr, L, hL, ε, hε, W₁, hW₁, w, w', hw, hwc, hw0, hw1, hw', hf0, hfβ, hfc, hfwin⟩ :=
    exists_excess_weight ha hlog hcon
  obtain ⟨α, hα⟩ : ∃ α, α = ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ := ⟨_, rfl⟩
  obtain ⟨α₁, hα₁⟩ : ∃ α₁,
      α₁ = ∑' n, ‖LSeries.term (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) n‖ := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; exact tsum_nonneg fun n => norm_nonneg _
  have hα₁0 : 0 ≤ α₁ := by rw [hα₁]; exact tsum_nonneg fun n => norm_nonneg _
  rw [← hα] at hfβ
  obtain ⟨αV, hαV⟩ : ∃ αV, αV = ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖ := ⟨_, rfl⟩
  have hαV0 : 0 ≤ αV := by rw [hαV]; exact tsum_nonneg fun n => norm_nonneg _
  obtain ⟨D, hD, hms⟩ := exists_integral_hardyZ_sq_le
  obtain ⟨C, K, hC, hK, hfloor⟩ := exists_integral_softLog_ge
  have hβ0 : 0 ≤ α + 1 := by linarith
  have hB₁0 : 0 ≤ α₁ + α * W₁ := by positivity
  have hκ0 : 0 < r * ε / (2 * L) := by positivity
  have hcomp := eventually_comparison (κ := r * ε / (2 * L)) (P₁ := 2 * (α + 1) + (α₁ + α * W₁))
    (P₂ := r * ε / 2 + (α + 1) + 4 * (α + 1) * K + 6 * α + (α₁ + α * W₁) * K)
    (P₃ := 2 * (α + 1) + 4 * (α + 1) * C + 8 * (α + 1) * K + 16 * α + (α₁ + α * W₁) * C +
      2 * (α₁ + α * W₁) * K) (P₄ := αV) (D := 6 * D) hκ0 (by positivity) hαV0 (by positivity)
  obtain ⟨T, hTc, hT40, hX8⟩ := (hcomp.and ((eventually_ge_atTop (40 : ℝ)).and
    (Real.tendsto_log_atTop.eventually_ge_atTop 8))).exists
  obtain ⟨T₁, hT₁, hG₁⟩ := exists_zeroFree_height (show (20 : ℝ) ≤ T by linarith)
  obtain ⟨T₂, hT₂, hG₂⟩ := exists_zeroFree_height (show (20 : ℝ) ≤ 2 * T by linarith)
  have hT0 : 0 < T := by linarith
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hT₂0 : 0 < T₂ := by linarith [hT₂.1]
  have hη : (0 : ℝ) < 1 / T₂ := by positivity
  have hη4 : 1 / T₂ ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hT₂0 (by norm_num)]; linarith [hT₂.1]
  obtain ⟨hl1, hl2⟩ := log_le_log_add_two (T₂ := T₂) hT0 (by linarith [hT₂.1])
    (by linarith [hT₂.2])
  have hΘ : ∀ t ∈ Icc T₁ T₂, Real.log T / 4 ≤ gammaHardyPhaseRate t ∧
      gammaHardyPhaseRate t ≤ Real.log T₂ := by
    intro t ht
    have ht20 : 20 ≤ t := by linarith [hT₁.1, ht.1]
    obtain ⟨h1, h2⟩ := gammaHardyPhaseRate_bounds ht20
    have hlt : Real.log T ≤ Real.log t := Real.log_le_log hT0 (by linarith [hT₁.1, ht.1])
    have hlt' : Real.log t ≤ Real.log T₂ := Real.log_le_log (by linarith) ht.2
    constructor <;> linarith
  have H := per_height_ineq ha hv hW hlog hη hη4 hT12.le hΘ (by linarith) hβ0
    hw hwc hw0 hw1 hw' hf0 hfβ
  rw [← hα, ← hα₁, ← hαV] at H
  have hγ : αV * (T₂ - T₁) ≤ αV * (T + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hT₁.1, hT₂.2]) hαV0
  have hI := integral_ge_of_windows hfc hf0 hL hε.le hr.le hfwin hT12.le
  have hI' : ((T - 1) / L - 1) * (2 * r * ε) ≤
      ∫ t in T₁..T₂, ((dilSeries a (linePt t)).re - 1) * w t := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) hI
    have : (T - 1) / L ≤ (T₂ - T₁) / L :=
      div_le_div_of_nonneg_right (by linarith [hT₁.2, hT₂.1]) hL.le
    linarith
  have hJ₁ := integral_log_one_add_hardyZ_sq_le hD hT40 hT₁.1 hT₁.2 hT₂.1 hT₂.2
    (hms (by linarith [hT₁.1]) hT12.le (by linarith [hT₂.1]))
  have hJ₂ := hfloor hη (by linarith [hT₁.1]) hT12 hG₁ hG₂
  have hJ12 : 0 ≤ (∫ t in T₁..T₂, Real.log (1 + hardyZ t ^ 2)) -
      2 * ∫ t in T₁..T₂, softLog (1 / T₂) t := by
    have hm : ∫ t in T₁..T₂, 2 * softLog (1 / T₂) t ≤
        ∫ t in T₁..T₂, Real.log (1 + hardyZ t ^ 2) :=
      intervalIntegral.integral_mono_on hT12.le
        ((continuous_const.mul (continuous_softLog hη)).intervalIntegrable _ _)
        ((((continuous_const.add (differentiable_hardyZ.continuous.pow 2)).log fun t =>
          (show (0 : ℝ) < 1 + hardyZ t ^ 2 by positivity).ne')).intervalIntegrable _ _)
        (fun t _ => (by linarith [softLog_le hη (by linarith) t] :
          2 * softLog (1 / T₂) t ≤ Real.log (1 + hardyZ t ^ 2)))
    rw [intervalIntegral.integral_const_mul] at hm
    linarith
  have hs₂ := abs_softLog_endpoint_le (T' := T₂) (T₂ := T₂) hT40 (by linarith [hT₂.1])
    (by linarith [hT₂.2]) (by linarith [hT₂.1]) (by linarith [hT₂.2])
  have hs₁ := abs_softLog_endpoint_le (T' := T₁) (T₂ := T₂) hT40 hT₁.1 (by linarith [hT₁.2])
    (by linarith [hT₂.1]) (by linarith [hT₂.2])
  have hΛ : Real.log T ≤ Real.log (1 / (2 * (1 / T₂))) := by
    have : 1 / (2 * (1 / T₂)) = T₂ / 2 := by field_simp
    rw [this]
    exact Real.log_le_log hT0 (by linarith [hT₂.1])
  have hη1 : 1 / T₂ * (T₂ - T₁) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hT₂0]; linarith [hT₁.1]
  have hfinal := excess_comparison hr hε hL rfl hX8 hα0 hβ0 hB₁0 hK.le H hγ hI' hJ₁ hJ₂ hJ12
    hs₁ hs₂ hl1 hl2 hΛ hη1
  linarith

/-! ## Phragmén–Lindelöf and the maximum principle -/

theorem norm_dilSeries_le_half (ha : HalfSummable a) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖dilSeries a s‖ ≤ ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ := by
  have hsum : Summable fun n => ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ :=
    summable_norm_iff.mpr ha.half
  have hle : ∀ n, ‖LSeries.term (fun n => (a n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ :=
    LSeries.norm_term_le_of_re_le_re _ (by simpa using hs)
  have hs' := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsum
  exact (norm_tsum_le_tsum_norm hs').trans (Summable.tsum_le_tsum hle hs' hsum)

theorem differentiableOn_dilSeries_half (ha : HalfSummable a) :
    DifferentiableOn ℂ (dilSeries a) {s : ℂ | 1 / 2 < s.re} :=
  (differentiableOn_dilSeries (δ := 0) ha).mono fun z hz => by
    simp only [Set.mem_setOf_eq] at hz ⊢; linarith

/-- **Phragmén–Lindelöf**: `Re A ≤ 1` on the closed half-plane `Re s ≥ ½`. -/
theorem re_dilSeries_le_one (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : (dilSeries a s).re ≤ 1 := by
  obtain ⟨α, hα⟩ : ∃ α, α = ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ := ⟨_, rfl⟩
  have hshift : ∀ z : ℂ, 0 ≤ z.re → 1 / 2 ≤ (1 / 2 + z).re := fun z hz => by
    simp only [Complex.add_re]; norm_num; linarith
  have hbound : ∀ z : ℂ, 0 ≤ z.re → ‖Complex.exp (dilSeries a (1 / 2 + z))‖ ≤ Real.exp α := by
    intro z hz
    rw [Complex.norm_exp, hα]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans
      (norm_dilSeries_le_half ha (hshift z hz)))
  have hd : DiffContOnCl ℂ (fun z => Complex.exp (dilSeries a (1 / 2 + z))) {z | 0 < z.re} := by
    refine ⟨fun z hz => ?_, ?_⟩
    · have hz' : 1 / 2 < (1 / 2 + z).re := by
        simp only [Complex.add_re]; norm_num; exact hz
      have hA : DifferentiableAt ℂ (dilSeries a) (1 / 2 + z) :=
        (differentiableOn_dilSeries_half ha).differentiableAt
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz')
      exact ((hA.comp z ((differentiableAt_const _).add
        differentiableAt_id)).cexp).differentiableWithinAt
    · rw [Complex.closure_setOf_lt_re]
      exact Complex.continuous_exp.comp_continuousOn ((continuousOn_dilSeries ha).comp
        (continuous_const.add continuous_id).continuousOn fun z hz => hshift z hz)
  have hexp : ∃ c < (2 : ℝ), ∃ B, (fun z => Complex.exp (dilSeries a (1 / 2 + z))) =O[
      Bornology.cobounded ℂ ⊓ Filter.principal {z | 0 < z.re}] fun z => Real.exp (B * ‖z‖ ^ c) := by
    refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound (Real.exp α) ?_⟩
    filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z hz
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    exact hbound z (le_of_lt hz)
  have hre : Filter.IsBoundedUnder (· ≤ ·) atTop
      fun x : ℝ => ‖Complex.exp (dilSeries a (1 / 2 + (x : ℂ)))‖ :=
    ⟨Real.exp α, Filter.eventually_map.mpr (Filter.eventually_atTop.mpr
      ⟨0, fun x hx => hbound x (by simpa using hx)⟩)⟩
  have him : ∀ x : ℝ, ‖Complex.exp (dilSeries a (1 / 2 + (x : ℂ) * I))‖ ≤ Real.exp 1 := by
    intro x
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have e : (1 / 2 : ℂ) + (x : ℂ) * I = linePt x := by
      rw [← ofReal_half_add_eq_linePt]; push_cast; ring
    rw [e]
    exact re_lineSeries_le_one ha hv hW hlog x
  have key := PhragmenLindelof.right_half_plane_of_bounded_on_real hd hexp hre him
    (z := s - 1 / 2) (by simp only [Complex.sub_re]; norm_num; linarith)
  rw [Complex.norm_exp, show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring] at key
  exact Real.exp_le_exp.mp key

/-- **The maximum principle**: `A ≡ 1` on `Re s > ½`. -/
theorem dilSeries_eq_one (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) {s : ℂ}
    (hs : 1 / 2 < s.re) : dilSeries a s = 1 := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hA := differentiableOn_dilSeries_half ha
  have h1 : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (1 : ℂ).re; norm_num
  have hone := dilSeries_one_eq_one_half ha hv hW
  have hmax : IsMaxOn (norm ∘ fun s => Complex.exp (dilSeries a s)) {s : ℂ | 1 / 2 < s.re} 1 := by
    intro z hz
    simp only [Set.mem_setOf_eq, Function.comp, Complex.norm_exp, hone, Complex.one_re]
    exact Real.exp_le_exp.mpr (re_dilSeries_le_one ha hv hW hlog (le_of_lt hz))
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hU
    (fun z hz => (hA z hz).cexp) h1 hmax
  have hderiv : Set.EqOn (deriv (dilSeries a)) 0 {s : ℂ | 1 / 2 < s.re} := by
    intro z hz
    have hAz : DifferentiableAt ℂ (dilSeries a) z := hA.differentiableAt (hU.mem_nhds hz)
    have hev : (fun s => Complex.exp (dilSeries a s)) =ᶠ[𝓝 z]
        fun _ => Complex.exp (dilSeries a 1) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun y hy => heq hy
    have h0 : deriv (fun s => Complex.exp (dilSeries a s)) z = 0 := by
      rw [hev.deriv_eq]; simp
    rw [deriv_cexp hAz] at h0
    simpa [Complex.exp_ne_zero] using h0
  rw [hU.is_const_of_deriv_eq_zero hUc hA hderiv hs h1, hone]

/-! ## Rigidity -/

/-- **Boundary-class dilation rigidity.**  If `Σ |a(n)| n^{−½}(1 + log n) < ∞`, `v` is regular
on the boundary and `Λ ⋆ a + v` is full-cone Weil-positive, then `a = δ₁`. -/
theorem eq_delta_of_weilPositiveFull_boundary (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) :
    a 1 = 1 ∧ ∀ n, 2 ≤ n → a n = 0 := by
  classical
  set e : ℕ → ℂ := fun n => if n = 1 then 1 else 0 with he
  have heS : ∀ s : ℂ, LSeriesSummable e s := fun s =>
    summable_of_ne_finset_zero (s := {1}) fun n hn => by
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, he, this]
  have hLe : ∀ s : ℂ, LSeries e s = 1 := by
    intro s
    rw [LSeries, tsum_eq_single 1 fun n hn => by simp [LSeries.term, he, hn]]
    simp [LSeries.term, he]
  have hbS : LSeriesSummable ((fun n => (a n : ℂ)) - e) (1 / 2) := ha.half.sub (heS _)
  have hLb : (fun x : ℝ => LSeries ((fun n => (a n : ℂ)) - e) x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with σ hσ
    have hσ' : 1 / 2 < ((σ : ℂ)).re := by simp only [Complex.ofReal_re]; linarith
    rw [LSeries_sub (ha.half.of_re_le_re (by simpa using hσ'.le)) (heS _), hLe]
    have h := dilSeries_eq_one ha hv hW hlog hσ'
    simp only [Pi.zero_apply]
    rw [show LSeries (fun n => (a n : ℂ)) σ = dilSeries a σ from rfl, h, sub_self]
  rcases LSeries_eventually_eq_zero_iff'.mp hLb with hzero | htop
  · refine ⟨?_, fun n hn => ?_⟩
    · have h := hzero 1 one_ne_zero
      simp [he, sub_eq_zero] at h
      exact_mod_cast h
    · have h := hzero n (by omega)
      simp only [Pi.sub_apply, he, if_neg (show n ≠ 1 by omega), sub_zero] at h
      exact_mod_cast h
  · exfalso
    have := hbS.abscissaOfAbsConv_le
    rw [htop] at this
    exact absurd this (not_le.mpr (EReal.coe_lt_top _))

/-- **Full boundary-class rigidity**: `a = δ₁` and `v = 0`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_boundary (ha : HalfSummable a)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a 0 v))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) :
    (a 1 = 1 ∧ ∀ n, 2 ≤ n → a n = 0) ∧ ∀ n, v n = 0 := by
  obtain ⟨h1, h2⟩ := eq_delta_of_weilPositiveFull_boundary ha hv hW hlog
  refine ⟨⟨h1, h2⟩, fun n => ?_⟩
  have hsum : Summable fun n : ℕ => |finiteTypeSeq a 0 v n - ArithmeticFunction.vonMangoldt n| *
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hs := summable_norm_iff.mpr hv.summable
    refine hs.congr fun n => ?_
    rw [WeilDilationRealness.finiteTypeSeq_eq_vonMangoldt_add h1 h2, add_sub_cancel_left]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, hv.zero]
    · rw [LSeries.norm_term_eq, if_neg hn.ne', Complex.norm_real, Real.norm_eq_abs,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      norm_num
  have hrig := WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_rpow_summable hW
    (by norm_num) hsum
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact hv.zero
    · exact hv.one
  · have := hrig n hn
    rw [WeilDilationRealness.finiteTypeSeq_eq_vonMangoldt_add h1 h2] at this
    linarith

/-- **A boundary-class Weil-positive system `Λ ⋆ a + v` forces RH.** -/
theorem riemannHypothesis_of_weilPositiveFull_boundary (ha : HalfSummable a)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a 0 v))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)) : RiemannHypothesis := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := eq_vonMangoldt_of_weilPositiveFull_boundary ha hv hW hlog
  have hlam : finiteTypeSeq a 0 v = fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
    funext n
    rw [WeilDilationRealness.finiteTypeSeq_eq_vonMangoldt_add h1 h2, h3, add_zero]
  rw [hlam] at hW
  refine RHTower.WeilSpectral.riemannHypothesis_of_weilPositiveFull_of_summable_deviationPos hW
    fun σ _ => ?_
  simp [RHTower.WeilSpectral.deviationPos]

theorem boundaryRegular_zero : BoundaryRegular (0 : ℕ → ℝ) := by
  refine ⟨rfl, rfl, ?_⟩
  have h : (fun n => (((0 : ℕ → ℝ) n : ℝ) : ℂ)) = 0 := by funext n; simp
  rw [h]
  exact LSeriesSummable_zero

/-- **A boundary-class Weil-positive dilation of `Λ` forces RH.** -/
theorem riemannHypothesis_of_weilPositiveFull_boundaryDilation
    (ha : LSeriesSummable (fun n => (a n : ℂ)) (1 / 2))
    (hlog : LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2))
    (hW : WeilPositiveFull (finiteTypeSeq a 0 0)) : RiemannHypothesis := by
  have ha' : HalfSummable a := by
    have e : ((1 / 2 - 0 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
    show LSeriesSummable _ _
    rw [e]; exact ha
  exact riemannHypothesis_of_weilPositiveFull_boundary ha' boundaryRegular_zero hW hlog

/-- **Within the boundary class, a Weil-positive system `Λ ⋆ a + v` exists iff RH.**  The class
consists of `Λ ⋆ a + v` with `Σ |a(n)| n^{−½}(1 + log n) < ∞`, `Σ |v(n)| n^{−½} < ∞` and
`v(0) = v(1) = 0`. -/
theorem exists_boundaryDilation_weilPositive_iff :
    (∃ a v : ℕ → ℝ, LSeriesSummable (fun n => (a n : ℂ)) (1 / 2) ∧
      LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) ∧ BoundaryRegular v ∧
      WeilPositiveFull (finiteTypeSeq a 0 v)) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨a, v, ha, hlog, hv, hW⟩
    have ha' : HalfSummable a := by
      have e : ((1 / 2 - 0 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
      show LSeriesSummable _ _
      rw [e]; exact ha
    exact riemannHypothesis_of_weilPositiveFull_boundary ha' hv hW hlog
  · intro hRH
    have hW := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH
    refine ⟨fun n => if n = 1 then 1 else 0, 0, ?_, ?_, boundaryRegular_zero, ?_⟩
    · refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, this]
    · refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, LSeries.logMul, this]
    · have e0 : (0 : ℕ → ℝ) = fun _ => 0 := rfl
      rw [e0, WeilFiniteType.finiteTypeSeq_delta_zero_zero]
      exact hW

end RHTower.WeilBoundaryDilation
