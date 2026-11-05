import GaloisForLFunctions.FiniteFreeProbability.BoundedImaginaryPartsCriterion

/-!
# Bounded or linear: the dichotomy of finite free imaginary parts

For the Möbius-mollified function `F = Ξ·e^{icw}Π_{p∈S}(1 − p^{−σ−iw})` (any finite `S`, `σ > 0`,
any phase `c`), the imaginary parts of the roots of the reversed Jensen polynomials `R_d(F)` admit
no intermediate growth:

* under RH they are at most `θ_S/2 − c` for every `d`;
* if RH fails there is `κ > 0` such that, for all large `d`, some root has imaginary part `≥ κ d`.

The second alternative is Hurwitz in the existence direction: a zero `ρ` of `F` with `Im ρ < 0`
attracts zeros `u_d` of the scaled approximants `Φ_d`, and the corresponding roots `d/u_d` have
`Im(d/u_d) = −d Im u_d/|u_d|² ≥ κ d`. Consequently RH holds iff for every `ε > 0` the imaginary
parts are `≤ εd` along infinitely many degrees.
-/

open Polynomial Filter Topology Complex Metric
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-- **Hurwitz, existence direction.** A zero `z₀` of `F = Σ f_k u^k` attracts zeros of the scaled
approximants: every ball around `z₀` contains a zero of `Φ_d` for all large `d`. -/
theorem eventually_exists_zero_scaledJensen {f : ℕ → ℂ}
    (hf : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k) (hf0 : f 0 ≠ 0) {z₀ : ℂ}
    (hz₀ : ∑' k, f k * z₀ ^ k = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ d : ℕ in atTop, ∃ u ∈ ball z₀ r, scaledJensen f d u = 0 := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hcon
  have hconv := tendstoLocallyUniformly_scaledJensen hf hφ.tendsto_atTop
  have hdiff : ∀ n, Differentiable ℂ (scaledJensen f (φ n)) := fun n => by
    unfold scaledJensen; fun_prop
  have hF : Differentiable ℂ fun u => ∑' k, f k * u ^ k := by
    have := (tendstoLocallyUniformlyOn_univ.2 hconv).differentiableOn
      (Eventually.of_forall fun n => (hdiff n).differentiableOn) isOpen_univ
    exact differentiableOn_univ.1 this
  have hmem := RHTower.zero_mem_closed_of_tendstoLocallyUniformly hconv
    (fun w _ => hF.analyticAt w) (Eventually.of_forall hdiff) isOpen_ball.isClosed_compl
    (Eventually.of_forall fun n w hw hwb => hP n ⟨w, hwb, hw⟩) (a := 0) (by
      rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero])]
      simpa using hf0) hz₀
  exact hmem (mem_ball_self hr)

/-- A zero of `F` in the open lower half-plane forces roots of `R_d(F)` with imaginary part `≥ κ d`
for all large `d`. -/
theorem eventually_exists_root_im_ge {f : ℕ → ℂ}
    (hf : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k) (hf0 : f 0 ≠ 0) {z₀ : ℂ}
    (hz₀ : ∑' k, f k * z₀ ^ k = 0) (him : z₀.im < 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ d : ℕ in atTop,
      ∃ x, (jensenRev d (PowerSeries.mk f)).IsRoot x ∧ κ * d ≤ x.im := by
  set r := -z₀.im / 2
  have hr : 0 < r := by simp only [r]; linarith
  set B := ‖z₀‖ + r
  have hB : 0 < B := by positivity
  refine ⟨r / B ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_exists_zero_scaledJensen hf hf0 hz₀ hr, eventually_gt_atTop 0] with
    d ⟨u, hu, hu0⟩ hd
  rw [mem_ball, dist_eq_norm] at hu
  have himu : u.im ≤ -r := by
    have := Complex.abs_im_le_norm (u - z₀)
    rw [sub_im] at this
    have := (abs_le.1 (this.trans hu.le)).2
    simp only [r] at *; linarith
  have hu0' : u ≠ 0 := by rintro rfl; simp at himu; linarith
  have hnorm : ‖u‖ ≤ B := by
    have h2 : ‖u‖ ≤ ‖z₀‖ + ‖u - z₀‖ := by
      calc ‖u‖ = ‖z₀ + (u - z₀)‖ := by ring_nf
        _ ≤ ‖z₀‖ + ‖u - z₀‖ := norm_add_le _ _
    simp only [B]; linarith
  refine ⟨(d : ℂ) / u, by rw [IsRoot, eval_jensenRev_div f hd hu0', hu0, mul_zero], ?_⟩
  rw [Complex.div_im]
  simp only [natCast_im, zero_mul, natCast_re, zero_div, zero_sub]
  have hns : 0 < Complex.normSq u := Complex.normSq_pos.2 hu0'
  have hnsB : Complex.normSq u ≤ B ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg u) hnorm 2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  calc r / B ^ 2 * d = (d * r) / B ^ 2 := by ring
    _ ≤ (d * r) / Complex.normSq u := div_le_div_of_nonneg_left (by positivity) hns hnsB
    _ ≤ (d * (-u.im)) / Complex.normSq u := by gcongr; linarith
    _ = -(d * u.im / Complex.normSq u) := by ring

/-- The coefficients of the mollified `Ξ` and their entire sum. -/
theorem hasSum_mollifiedXiSeries (S : Finset Nat.Primes) (σ c : ℝ) (z : ℂ) :
    HasSum (fun k => PowerSeries.coeff k (mollifiedXiSeries S σ c) * z ^ k)
      (XiC z * ∑ T ∈ S.powerset, (mobiusWeight σ T : ℂ) *
        Complex.exp (I * ((c - logFrequency T : ℝ) : ℂ) * z)) := by
  have := hasSum_coeff_mul (f := fun k => PowerSeries.coeff k xiSeries)
    (g := fun k => PowerSeries.coeff k (translatedMobiusProduct S σ c))
    hasSum_xiSeries (hasSum_translatedMobiusProduct S σ c) z
  have e1 : PowerSeries.mk (fun k => PowerSeries.coeff k xiSeries) = xiSeries := by ext k; simp
  have e2 : PowerSeries.mk (fun k => PowerSeries.coeff k (translatedMobiusProduct S σ c)) =
      translatedMobiusProduct S σ c := by ext k; simp
  rw [e1, e2] at this
  exact this

theorem coeff_zero_mollifiedXiSeries_ne {S : Finset Nat.Primes} {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    PowerSeries.coeff 0 (mollifiedXiSeries S σ c) ≠ 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, mollifiedXiSeries, map_mul,
    constantCoeff_xiSeries, constantCoeff_translatedMobiusProduct]
  refine mul_ne_zero XiC_zero_ne (Finset.prod_ne_zero_iff.2 fun p _ => ?_)
  rw [sub_ne_zero]; intro h
  have := congrArg Complex.re h
  simp only [one_re, ofReal_re] at this
  have := Real.rpow_lt_one_of_one_lt_of_neg (x := ((p : ℕ) : ℝ)) (z := -σ)
    (by exact_mod_cast p.prop.one_lt) (by linarith)
  linarith

/-- **The dichotomy.** If RH fails, some root of `R_d(Ξ·e^{icw}Π_{p∈S}(1 − p^{−σ−iw}))` has
imaginary part `≥ κ d` for all large `d`. -/
theorem exists_linear_im_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis)
    (S : Finset Nat.Primes) {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ d : ℕ in atTop,
      ∃ x, (jensenRev d (mollifiedXiSeries S σ c)).IsRoot x ∧ κ * d ≤ x.im := by
  set f : ℕ → ℂ := fun k => PowerSeries.coeff k (mollifiedXiSeries S σ c)
  have hmk : PowerSeries.mk f = mollifiedXiSeries S σ c := by ext k; simp [f]
  have hsum := hasSum_mollifiedXiSeries S σ c
  have hf : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k :=
    summable_norm_mul_pow_of_summable fun z => (hsum z).summable
  rw [riemannHypothesis_iff_XiC_zeros_real] at hRH
  push Not at hRH
  obtain ⟨z, hz, hzim⟩ := hRH
  -- a zero of `Ξ` in the open lower half-plane
  obtain ⟨w, hw, hwim⟩ : ∃ w, XiC w = 0 ∧ w.im < 0 := by
    rcases lt_or_gt_of_ne hzim with h | h
    · exact ⟨z, hz, h⟩
    · exact ⟨conj z, by rw [XiC_conj, hz, map_zero], by rw [conj_im]; linarith⟩
  have hFw : ∑' k, f k * w ^ k = 0 := by rw [(hsum w).tsum_eq, hw, zero_mul]
  simpa only [hmk] using eventually_exists_root_im_ge hf
    (coeff_zero_mollifiedXiSeries_ne hσ c) hFw hwim

/-- **Sublinear growth decides RH.** RH holds iff for every `ε > 0`, along infinitely many `d`,
all roots of `R_d(Ξ·e^{icw}Π_{p∈S}(1 − p^{−σ−iw}))` have imaginary part `≤ ε d`. -/
theorem riemannHypothesis_iff_forall_frequently_im_le_mul (S : Finset Nat.Primes) {σ : ℝ}
    (hσ : 0 < σ) (c : ℝ) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ᶠ d : ℕ in atTop,
      ∀ x, (jensenRev d (mollifiedXiSeries S σ c)).IsRoot x → x.im ≤ ε * d := by
  constructor
  · intro hRH ε hε
    refine (Filter.eventually_ge_atTop ⌈(logFrequency S / 2 - c) / ε⌉₊).frequently.mono
      fun d hd x hx => ?_
    have h1 := im_le_of_isRoot_jensenRev_mollifiedXiSeries hRH S hσ c hx
    have h2 : (logFrequency S / 2 - c) / ε ≤ d := (Nat.le_ceil _).trans (by exact_mod_cast hd)
    rw [div_le_iff₀ hε] at h2
    linarith
  · intro h
    by_contra hRH
    obtain ⟨κ, hκ, hev⟩ := exists_linear_im_of_not_riemannHypothesis hRH S hσ c
    obtain ⟨d, hd, hall⟩ := ((h (κ / 2) (by positivity)).and_eventually
      (hev.and (eventually_gt_atTop 0))).exists
    obtain ⟨⟨x, hx, hxim⟩, hd0⟩ := hall
    have := hd x hx
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
    nlinarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.exists_linear_im_of_not_riemannHypothesis
#print axioms FiniteFreeProbability.riemannHypothesis_iff_forall_frequently_im_le_mul
