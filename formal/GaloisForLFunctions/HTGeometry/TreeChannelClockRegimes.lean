import GaloisForLFunctions.HTGeometry.ParabolicAbelHypertranscendence
import GaloisForLFunctions.HTGeometry.RittTreeChannelClock
import GaloisForLFunctions.HTGeometry.RGTowerCoherence
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA
import GaloisForLFunctions.HTGeometry.HypertranscendentalAddConst

/-!
# The exact clock of a noisy binary tree channel, in every regime and every chart

Exact homogeneous belief propagation for a binary channel with signal parameters `u, v`
(`−1 < v < u < 1`) on a `p`-ary tree (`p ≥ 2`) is the rational map

`R(y) = ((1+uy)^p − (1+vy)^p)/((1+uy)^p + (1+vy)^p)`,   `R'(0) = p(u − v)/2`.

* **Attracting and repelling regimes** (`p(u−v)/2 ≠ 1`): the linearizer, the Schröder or Poincaré
  function and the beta field are hypertranscendental (`treeRG_interior_clock_hypertranscendental`).
* **Parabolic regime** (`p(u−v)/2 = 1`): every Abel function and its velocity field are
  hypertranscendental (`treeRG_parabolic_abel_hypertranscendental`).
* **Charts.**  Hypertranscendence survives every locally invertible differentially algebraic change
  of message coordinate (`not_differentiallyAlgebraicOn_comp_chart`).
* **Endpoints.**  The noiseless channel `u = 1, v = −1` is conjugate to `t ↦ t^p` by the odds
  coordinate `(1+y)/(1−y)` (`noiselessTree_odds`).

The binary symmetric channel is `u = a, v = −a` (`0 < a < 1`, multiplier `pa`); the diagonal
population sector of the generalized amplitude damping channel is `u = 1 − 2dN`, `v = 2d(1−N) − 1`
(`0 < d, N < 1`, multiplier `p(1 − d)`).  Its sequential population recursion is affine, and its
continuous interpolation is differentially algebraic.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Change of message coordinate -/

/-- **Hypertranscendence survives every locally invertible differentially algebraic chart.**  Let
`κ` satisfy no algebraic differential equation on any nonempty open subset of `U`, and let `χ` be a
differentially algebraic analytic chart on `U` with an analytic inverse `ξ : W → U`
(`χ ∘ ξ = id` on `W`).  Then the function `κ ∘ ξ`, which is `κ` read in the new coordinate,
satisfies no algebraic differential equation on `W`. -/
theorem not_differentiallyAlgebraicOn_comp_chart {κ ξ χ : ℂ → ℂ} {U W : Set ℂ} (hUo : IsOpen U)
    (hκ : AnalyticOnNhd ℂ κ U)
    (hHT : ∀ U' ⊆ U, IsOpen U' → U'.Nonempty → ¬ DifferentiallyAlgebraicOn κ U')
    (hWo : IsOpen W) (hWc : IsPreconnected W) (hWne : W.Nonempty) (hξ : AnalyticOnNhd ℂ ξ W)
    (hξU : MapsTo ξ W U) (hχ : AnalyticOnNhd ℂ χ U) (hχDA : DifferentiallyAlgebraicOn χ U)
    (hχξ : ∀ w ∈ W, χ (ξ w) = w) : ¬ DifferentiallyAlgebraicOn (fun w => κ (ξ w)) W := by
  intro hDA
  obtain ⟨w₀, hw₀⟩ := hWne
  have hy₀U : ξ w₀ ∈ U := hξU hw₀
  have hχy₀ : χ (ξ w₀) = w₀ := hχξ w₀ hw₀
  -- `χ` is noncritical at `ξ w₀`
  have hχ' : deriv χ (ξ w₀) ≠ 0 := by
    have hev : (χ ∘ ξ) =ᶠ[𝓝 w₀] id := by
      filter_upwards [hWo.mem_nhds hw₀] with w hw using hχξ w hw
    have h1 := hev.deriv_eq
    rw [deriv_comp w₀ (hχ _ hy₀U).differentiableAt (hξ w₀ hw₀).differentiableAt, deriv_id] at h1
    intro h
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  -- `ξ` inverts `χ` near `ξ w₀`
  obtain ⟨γ, -, hγχ, -⟩ := exists_localInverse_analytic (hχ _ hy₀U) hχ'
  have hχcont : ContinuousAt χ (ξ w₀) := (hχ _ hy₀U).continuousAt
  have hcomp : Tendsto (fun y => ξ (χ y)) (𝓝 (ξ w₀)) (𝓝 (ξ w₀)) := by
    have hξc : ContinuousAt ξ (χ (ξ w₀)) := by rw [hχy₀]; exact (hξ w₀ hw₀).continuousAt
    have h := (ContinuousAt.comp hξc hχcont).tendsto
    rwa [Function.comp_apply, hχy₀] at h
  have hloc : ∀ᶠ y in 𝓝 (ξ w₀), y ∈ U ∧ χ y ∈ W ∧ ξ (χ y) = y := by
    have h1 : ∀ᶠ y in 𝓝 (ξ w₀), χ y ∈ W :=
      hχcont.preimage_mem_nhds (by rw [hχy₀]; exact hWo.mem_nhds hw₀)
    filter_upwards [hUo.mem_nhds hy₀U, h1, hγχ, hcomp.eventually hγχ] with y hyU hyW hγy hγξ
    refine ⟨hyU, hyW, ?_⟩
    rw [hχξ _ hyW] at hγξ
    rw [← hγξ]
    exact hγy
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hloc
  set U₀ := Metric.ball (ξ w₀) ε with hU₀
  have hU₀U : U₀ ⊆ U := fun y hy => (hball y hy).1
  have hmaps : MapsTo χ U₀ W := fun y hy => (hball y hy).2.1
  have hU₀ne : U₀.Nonempty := Metric.nonempty_ball.mpr hε
  have hU₀inf : U₀.Infinite :=
    infinite_of_mem_nhds (ξ w₀) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  have hWinf : W.Infinite := infinite_of_mem_nhds w₀ (hWo.mem_nhds hw₀)
  have hfaith : SubstitutionFaithful U₀ W χ :=
    substitutionFaithful_of_deriv_ne_zero Metric.isOpen_ball hWo hWc (hχ.mono hU₀U) hmaps
      (Metric.mem_ball_self hε) hχ'
  have hχDA₀ : DifferentiallyAlgebraicOn χ U₀ := by
    obtain ⟨n, P, hP, hrel⟩ := hχDA
    exact ⟨n, P, hP, fun z hz => hrel z (hU₀U hz)⟩
  have hstep := differentiallyAlgebraicOn_comp Metric.isOpen_ball
    (convex_ball (ξ w₀) ε).isPreconnected hU₀ne hU₀inf hWo hWc ⟨w₀, hw₀⟩ hWinf
    (hκ.comp hξ hξU) (hχ.mono hU₀U) hmaps hfaith hDA hχDA₀
  exact hHT U₀ hU₀U Metric.isOpen_ball hU₀ne
    (differentiallyAlgebraicOn_of_eqOn Metric.isOpen_ball
      (fun y hy => by show κ (ξ (χ y)) = κ y; rw [(hball y hy).2.2]) hstep)

/-! ### The standard message charts -/

/-- The odds chart `y ↦ (1 + y)/(1 − y)` is differentially algebraic away from `y = 1`. -/
theorem differentiallyAlgebraicOn_odds {U : Set ℂ} (hU : ∀ y ∈ U, y ≠ 1) :
    DifferentiallyAlgebraicOn (fun y => (1 + y) / (1 - y)) U := by
  refine ⟨0, (1 - MvPolynomial.X 0) * MvPolynomial.X 1 - (1 + MvPolynomial.X 0), fun h => ?_,
    fun z hz => ?_⟩
  · have := congrArg (MvPolynomial.eval (Fin.cons (0 : ℂ) fun _ : Fin 1 => (0 : ℂ))) h
    simp at this
  · have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hU z hz))
    simp only [map_sub, map_mul, map_add, map_one, MvPolynomial.eval_X, Fin.cons_zero]
    rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
    simp only [Fin.val_zero, iteratedDeriv_zero]
    field_simp
    ring

/-- A function whose derivative is `c/((1 − y)(1 + y))` on a set is differentially algebraic
there. -/
theorem differentiallyAlgebraicOn_of_deriv_eq_artanh {f : ℂ → ℂ} {U : Set ℂ} (c : ℂ)
    (hU : ∀ y ∈ U, y ≠ 1 ∧ y ≠ -1) (hf : ∀ y ∈ U, deriv f y = c / ((1 - y) * (1 + y))) :
    DifferentiallyAlgebraicOn f U := by
  apply differentiallyAlgebraicOn_of_deriv
  refine ⟨0, (1 - MvPolynomial.X 0 ^ 2) * MvPolynomial.X 1 - MvPolynomial.C c, fun h => ?_,
    fun z hz => ?_⟩
  · have := congrArg (MvPolynomial.eval (Fin.cons (0 : ℂ) fun _ : Fin 1 => c + 1)) h
    simp only [map_sub, map_mul, map_pow, map_one, MvPolynomial.eval_X, MvPolynomial.eval_C,
      Fin.cons_zero, map_zero] at this
    rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ] at this
    norm_num at this
  · obtain ⟨h1, h2⟩ := hU z hz
    have hs : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have ha : (1 : ℂ) + z ≠ 0 := fun h => h2 (by linear_combination h)
    simp only [map_sub, map_mul, map_pow, map_one, MvPolynomial.eval_X, MvPolynomial.eval_C,
      Fin.cons_zero]
    rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
    simp only [Fin.val_zero, iteratedDeriv_zero, hf z hz]
    field_simp
    ring

theorem hasDerivAt_odds {y : ℂ} (hy : (1 : ℂ) - y ≠ 0) :
    HasDerivAt (fun t => (1 + t) / (1 - t)) (2 / (1 - y) ^ 2) y := by
  have h := ((hasDerivAt_id' y).const_add 1).div ((hasDerivAt_id' y).const_sub 1) hy
  rw [show (1 * (1 - y) - (1 + y) * -1) / (1 - y) ^ 2 = 2 / (1 - y) ^ 2 by ring] at h
  exact h

/-- The log-likelihood-ratio chart `y ↦ log((1 + y)/(1 − y))` is differentially algebraic on every
set where it is analytic. -/
theorem differentiallyAlgebraicOn_logLikelihoodRatio {U : Set ℂ}
    (hU : ∀ y ∈ U, y ≠ 1 ∧ y ≠ -1 ∧ (1 + y) / (1 - y) ∈ Complex.slitPlane) :
    DifferentiallyAlgebraicOn (fun y => Complex.log ((1 + y) / (1 - y))) U := by
  refine differentiallyAlgebraicOn_of_deriv_eq_artanh 2
    (fun y hy => ⟨(hU y hy).1, (hU y hy).2.1⟩) fun y hy => ?_
  obtain ⟨h1, h2, h3⟩ := hU y hy
  have hs : (1 : ℂ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have ha : (1 : ℂ) + y ≠ 0 := fun h => h2 (by linear_combination h)
  rw [((hasDerivAt_odds hs).clog h3).deriv]
  field_simp

/-- The cavity-field chart `y ↦ artanh y = log((1 + y)/(1 − y))/2` is differentially algebraic on
every set where it is analytic. -/
theorem differentiallyAlgebraicOn_cavityField {U : Set ℂ}
    (hU : ∀ y ∈ U, y ≠ 1 ∧ y ≠ -1 ∧ (1 + y) / (1 - y) ∈ Complex.slitPlane) :
    DifferentiallyAlgebraicOn (fun y => Complex.log ((1 + y) / (1 - y)) / 2) U := by
  refine differentiallyAlgebraicOn_of_deriv_eq_artanh 1
    (fun y hy => ⟨(hU y hy).1, (hU y hy).2.1⟩) fun y hy => ?_
  obtain ⟨h1, h2, h3⟩ := hU y hy
  have hs : (1 : ℂ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have ha : (1 : ℂ) + y ≠ 0 := fun h => h2 (by linear_combination h)
  rw [(((hasDerivAt_odds hs).clog h3).div_const 2).deriv]
  field_simp

/-! ### The noiseless endpoint -/

/-- **The noiseless channel is conjugate to the power map**: in the odds coordinate
`(1 + y)/(1 − y)` the map `((1+y)^p − (1−y)^p)/((1+y)^p + (1−y)^p)` becomes `t ↦ t^p`. -/
theorem noiselessTree_odds (p : ℕ) {y : ℂ} (hy : 1 - y ≠ 0)
    (hden : (1 + y) ^ p + (1 - y) ^ p ≠ 0) :
    (1 + ((1 + y) ^ p - (1 - y) ^ p) / ((1 + y) ^ p + (1 - y) ^ p))
        / (1 - ((1 + y) ^ p - (1 - y) ^ p) / ((1 + y) ^ p + (1 - y) ^ p))
      = ((1 + y) / (1 - y)) ^ p := by
  have hq : (1 - y) ^ p ≠ 0 := pow_ne_zero _ hy
  have h1 : 1 + ((1 + y) ^ p - (1 - y) ^ p) / ((1 + y) ^ p + (1 - y) ^ p)
      = 2 * (1 + y) ^ p / ((1 + y) ^ p + (1 - y) ^ p) := by
    field_simp
    ring
  have h2 : 1 - ((1 + y) ^ p - (1 - y) ^ p) / ((1 + y) ^ p + (1 - y) ^ p)
      = 2 * (1 - y) ^ p / ((1 + y) ^ p + (1 - y) ^ p) := by
    field_simp
    ring
  rw [h1, h2, div_pow, div_div_div_cancel_right₀ hden, mul_div_mul_left _ _ two_ne_zero]

/-! ### The binary symmetric channel -/

variable {p : ℕ}

theorem bsc_signal_eq (a : ℝ) (y : ℂ) : (1 + ((-a : ℝ) : ℂ) * y) = 1 - (a : ℂ) * y := by
  push_cast
  ring

/-- **The binary symmetric channel away from its Bethe point.**  For `0 < a < 1`, `p ≥ 2` and
`pa ≠ 1`, the linearizer `κ` of `R(y) = ((1+ay)^p − (1−ay)^p)/((1+ay)^p + (1−ay)^p)` at `0`, its
inverse `Φ` (Schröder function for `pa < 1`, Poincaré function for `pa > 1`) and the beta field
satisfy no algebraic differential equation on any nonempty open set of their domains. -/
theorem bsc_clock_hypertranscendental (hp : 2 ≤ p) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hpar : (p : ℝ) * a ≠ 1) {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {Φ κ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ V) (hκ : AnalyticOnNhd ℂ κ U) (hκV : MapsTo κ U V)
    (hΦU : MapsTo Φ V U) (hΦκ : ∀ t ∈ U, Φ (κ t) = t) (hκΦ : ∀ z ∈ V, κ (Φ z) = z)
    (h0U : (0 : ℂ) ∈ U) {q : ℂ} (hq : q ≠ 0)
    (hfe : ∀ᶠ y in 𝓝 (0 : ℂ), κ (((1 + a * y) ^ p - (1 - a * y) ^ p)
      / ((1 + a * y) ^ p + (1 - a * y) ^ p)) = q * κ y) :
    (∀ W ⊆ U, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn κ W) ∧
      (∀ W ⊆ V, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn Φ W) ∧
      (∀ W ⊆ U, IsOpen W → IsPreconnected W → W.Nonempty → W.Infinite →
        (∀ t ∈ W, κ t ≠ 0) → (∀ t ∈ W, deriv κ t ≠ 0) →
        ∀ {lamLog : ℂ}, lamLog ≠ 0 → ¬ DifferentiallyAlgebraicOn (rgBeta lamLog κ) W) := by
  refine treeRG_interior_clock_hypertranscendental hp (u := a) (v := -a) (by linarith)
    (by linarith) ha1 (by contrapose! hpar; linarith) hUo hUc hVo hVc hVne hVinf hΦ hκ hκV
    hΦU hΦκ hκΦ h0U hq ?_
  filter_upwards [hfe] with y hy
  rw [bsc_signal_eq]
  exact hy

/-- **The binary symmetric channel at its Bethe point.**  For `0 < a < 1`, `p ≥ 2` and `pa = 1`,
every nonconstant analytic Abel function `A(R(y)) = A(y) + 1` on an open connected pole-free
`R`-invariant set `D`, and its velocity field `1/A'`, satisfy no algebraic differential equation on
any nonempty open subset of `D`. -/
theorem bsc_abel_hypertranscendental (hp : 2 ≤ p) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hpar : (p : ℝ) * a = 1) {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hden : ∀ y ∈ D, (1 + a * y) ^ p + (1 - a * y) ^ p ≠ 0)
    (hmaps : MapsTo (fun y : ℂ => ((1 + a * y) ^ p - (1 - a * y) ^ p)
      / ((1 + a * y) ^ p + (1 - a * y) ^ p)) D D)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A D)
    (habel : ∀ y ∈ D, A (((1 + a * y) ^ p - (1 - a * y) ^ p)
      / ((1 + a * y) ^ p + (1 - a * y) ^ p)) = A y + 1)
    (hAnc : ∃ t₀ ∈ D, deriv A t₀ ≠ 0) :
    (∀ W ⊆ D, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn A W) ∧
      (∀ W ⊆ D, IsOpen W → W.Nonempty → (∀ y ∈ W, deriv A y ≠ 0) →
        ¬ DifferentiallyAlgebraicOn (fun y => (deriv A y)⁻¹) W) := by
  refine treeRG_parabolic_abel_hypertranscendental hp (u := a) (v := -a) (by linarith)
    (by linarith) ha1 (by linarith) hDo hDc (fun y hy => ?_) (fun y hy => ?_) hA
    (fun y hy => ?_) hAnc
  · rw [bsc_signal_eq]
    exact hden y hy
  · simp only [bsc_signal_eq]
    exact hmaps hy
  · simp only [bsc_signal_eq]
    exact habel y hy

/-- The Bethe threshold `pa = 1` and the Kesten–Stigum threshold `pa² = 1` of a binary symmetric
channel are distinct: `pa² < pa` for every `0 < a < 1`. -/
theorem bsc_kestenStigum_lt_bethe {a : ℝ} (hp : 0 < p) (ha0 : 0 < a) (ha1 : a < 1) :
    (p : ℝ) * a ^ 2 < (p : ℝ) * a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have : a ^ 2 < a := by nlinarith
  exact mul_lt_mul_of_pos_left this hp0

/-! ### The generalized amplitude damping channel -/

theorem gadc_signal_bounds {d N : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hN0 : 0 < N) (hN1 : N < 1) :
    -1 < 2 * d * (1 - N) - 1 ∧ 2 * d * (1 - N) - 1 < 1 - 2 * d * N ∧ 1 - 2 * d * N < 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hd0 hN0, mul_pos hd0 (sub_pos.mpr hN1)]

theorem gadc_multiplier (d N : ℝ) :
    (p : ℝ) * ((1 - 2 * d * N) - (2 * d * (1 - N) - 1)) / 2 = (p : ℝ) * (1 - d) := by
  ring

/-- **The GADC population clock away from the damping threshold.**  For `0 < d, N < 1`, `p ≥ 2`
and `p(1 − d) ≠ 1`, with `u = 1 − 2dN` and `v = 2d(1 − N) − 1`, the linearizer, its inverse and the
beta field of the exact population update satisfy no algebraic differential equation on any
nonempty open set of their domains. -/
theorem gadc_clock_hypertranscendental (hp : 2 ≤ p) {d N : ℝ} (hd0 : 0 < d) (hd1 : d < 1)
    (hN0 : 0 < N) (hN1 : N < 1) (hpar : (p : ℝ) * (1 - d) ≠ 1) {U V : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (hVinf : V.Infinite) {Φ κ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ V) (hκ : AnalyticOnNhd ℂ κ U)
    (hκV : MapsTo κ U V) (hΦU : MapsTo Φ V U) (hΦκ : ∀ t ∈ U, Φ (κ t) = t)
    (hκΦ : ∀ z ∈ V, κ (Φ z) = z) (h0U : (0 : ℂ) ∈ U) {q : ℂ} (hq : q ≠ 0)
    (hfe : ∀ᶠ y in 𝓝 (0 : ℂ),
      κ (((1 + ((1 - 2 * d * N : ℝ) : ℂ) * y) ^ p - (1 + ((2 * d * (1 - N) - 1 : ℝ) : ℂ) * y) ^ p)
        / ((1 + ((1 - 2 * d * N : ℝ) : ℂ) * y) ^ p
          + (1 + ((2 * d * (1 - N) - 1 : ℝ) : ℂ) * y) ^ p)) = q * κ y) :
    (∀ W ⊆ U, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn κ W) ∧
      (∀ W ⊆ V, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn Φ W) ∧
      (∀ W ⊆ U, IsOpen W → IsPreconnected W → W.Nonempty → W.Infinite →
        (∀ t ∈ W, κ t ≠ 0) → (∀ t ∈ W, deriv κ t ≠ 0) →
        ∀ {lamLog : ℂ}, lamLog ≠ 0 → ¬ DifferentiallyAlgebraicOn (rgBeta lamLog κ) W) := by
  obtain ⟨hv, huv, hu⟩ := gadc_signal_bounds hd0 hd1 hN0 hN1
  exact treeRG_interior_clock_hypertranscendental hp hv huv hu
    (by rw [gadc_multiplier]; exact hpar) hUo hUc hVo hVc hVne hVinf hΦ hκ hκV hΦU hΦκ hκΦ h0U
    hq hfe

/-- **The GADC population clock at the damping threshold `d = 1 − 1/p`.**  Every nonconstant
analytic Abel function of the exact population update on an open connected pole-free invariant set,
and its velocity field, satisfy no algebraic differential equation on any nonempty open subset. -/
theorem gadc_abel_hypertranscendental (hp : 2 ≤ p) {d N : ℝ} (hd0 : 0 < d) (hd1 : d < 1)
    (hN0 : 0 < N) (hN1 : N < 1) (hpar : (p : ℝ) * (1 - d) = 1) {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsPreconnected D)
    (hden : ∀ y ∈ D, (1 + ((1 - 2 * d * N : ℝ) : ℂ) * y) ^ p
      + (1 + ((2 * d * (1 - N) - 1 : ℝ) : ℂ) * y) ^ p ≠ 0)
    (hmaps : MapsTo (fun y : ℂ =>
      ((1 + ((1 - 2 * d * N : ℝ) : ℂ) * y) ^ p - (1 + ((2 * d * (1 - N) - 1 : ℝ) : ℂ) * y) ^ p)
        / ((1 + ((1 - 2 * d * N : ℝ) : ℂ) * y) ^ p
          + (1 + ((2 * d * (1 - N) - 1 : ℝ) : ℂ) * y) ^ p)) D D)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A D)
    (habel : ∀ y ∈ D,
      A (((1 + ((1 - 2 * d * N : ℝ) : ℂ) * y) ^ p - (1 + ((2 * d * (1 - N) - 1 : ℝ) : ℂ) * y) ^ p)
        / ((1 + ((1 - 2 * d * N : ℝ) : ℂ) * y) ^ p
          + (1 + ((2 * d * (1 - N) - 1 : ℝ) : ℂ) * y) ^ p)) = A y + 1)
    (hAnc : ∃ t₀ ∈ D, deriv A t₀ ≠ 0) :
    (∀ W ⊆ D, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn A W) ∧
      (∀ W ⊆ D, IsOpen W → W.Nonempty → (∀ y ∈ W, deriv A y ≠ 0) →
        ¬ DifferentiallyAlgebraicOn (fun y => (deriv A y)⁻¹) W) := by
  obtain ⟨hv, huv, hu⟩ := gadc_signal_bounds hd0 hd1 hN0 hN1
  exact treeRG_parabolic_abel_hypertranscendental hp hv huv hu
    (by rw [gadc_multiplier]; exact hpar) hDo hDc hden hmaps hA habel hAnc

/-- The sequential GADC population recursion `r ↦ (1 − d)r + d(1 − 2N)` has iterates
`(1 − 2N) + (1 − d)^n (r − (1 − 2N))`. -/
theorem gadcSequential_iterate (d N r : ℂ) (n : ℕ) :
    (fun s => (1 - d) * s + d * (1 - 2 * N))^[n] r
      = (1 - 2 * N) + (1 - d) ^ n * (r - (1 - 2 * N)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ring

/-- The exponential `t ↦ (1 − 2N) + e^{t log(1 − d)} (r − (1 − 2N))` interpolates the sequential
iterates. -/
theorem gadcSequential_interpolation (d N r : ℂ) (hd : d ≠ 1) (n : ℕ) :
    (1 - 2 * N) + Complex.exp (Complex.log (1 - d) * n) * (r - (1 - 2 * N))
      = (fun s => (1 - d) * s + d * (1 - 2 * N))^[n] r := by
  rw [gadcSequential_iterate, mul_comm (Complex.log (1 - d)) (n : ℂ), Complex.exp_nat_mul,
    Complex.exp_log (sub_ne_zero.mpr (Ne.symm hd))]

/-- **The sequential population dynamics is differentially algebraic**: its continuous
interpolation satisfies an algebraic differential equation. -/
theorem differentiallyAlgebraic_gadcSequential_interpolation (d N r : ℂ) :
    DifferentiallyAlgebraic
      (fun t => (1 - 2 * N) + Complex.exp (Complex.log (1 - d) * t) * (r - (1 - 2 * N))) := by
  have h := differentiallyAlgebraic_cexp_mul_polynomial (Complex.log (1 - d))
    (Polynomial.C (r - (1 - 2 * N)))
  simp only [Polynomial.eval_C] at h
  refine differentiallyAlgebraic_add_const (-(1 - 2 * N)) ?_
  have hfun : (fun t => (1 - 2 * N) + Complex.exp (Complex.log (1 - d) * t) * (r - (1 - 2 * N))
      + -(1 - 2 * N)) = fun t => Complex.exp (Complex.log (1 - d) * t) * (r - (1 - 2 * N)) := by
    funext t
    ring
  rw [hfun]
  exact h

end

end GaloisForLFunctions.HTGeometry
