import GaloisForLFunctions.RHTower.ProlateSecondMoment

/-!
# A uniform lower bound for the oscillator separation constant

The prolate Rayleigh identity says

`μ ∫Φ² = (∫(1−x²)Φ′²)/c + c ∫x²Φ² ,     μ = c·s = −χ/c ,`

so both the gradient and the potential term are individually at most `μ∫Φ²`.  An uncertainty
argument turns that into a lower bound for `μ` itself.

Integrating `(xΦ²)′ = Φ² + 2xΦΦ′` over a symmetric window `[−δ, δ]` and using
`−2xΦΦ′ ≤ c x²Φ² + Φ′²/c` gives

`∫_{−δ}^{δ} Φ² ≤ 2δ Φ(δ)² + μ ∫Φ² / (1 − 4δ₀²)`

whenever `δ ≤ 2δ₀ ≤ 1/2`, because on that window `1 − x² ≥ 1 − 4δ₀²`.  The second moment bound
`∫x²Φ² ≤ (μ/c)∫Φ²` makes the mass outside the window and the endpoint value both `O(μ/(cδ₀²))`
times the total.  Hence

`1 ≤ μ · (5/(cδ₀²) + 1/(1 − 4δ₀²))` ,

so at fixed `δ₀` the separation constant is asymptotically at least `1 − 4δ₀²`, and letting `δ₀`
shrink, at least `1`.  No eigenfunction asymptotics are used: only one integration by parts, the
arithmetic–geometric mean inequality and Chebyshev.
-/

open MeasureTheory Set

namespace RHTower

/-- Derivative of the virial weight `xΦ²`. -/
theorem hasDerivAt_virialWeight {Phi : ℝ → ℝ} (h1 : Differentiable ℝ Phi) (x : ℝ) :
    HasDerivAt (fun y => y * Phi y ^ 2)
      (Phi x ^ 2 + 2 * x * (Phi x * deriv Phi x)) x := by
  have hb : HasDerivAt (fun y => Phi y ^ 2) (2 * Phi x * deriv Phi x) x := by
    refine (((h1 x).hasDerivAt).pow 2).congr_deriv ?_
    push_cast
    ring
  refine ((hasDerivAt_id x).mul hb).congr_deriv ?_
  simp only [id_eq]
  ring

/-- **Virial identity on a symmetric window.** -/
theorem integral_sq_window {Phi : ℝ → ℝ} (h1 : Differentiable ℝ Phi)
    (h2 : Continuous (deriv Phi)) (heven : Function.Even Phi) (delta : ℝ) :
    (∫ x in (-delta)..delta, Phi x ^ 2)
      = 2 * delta * Phi delta ^ 2
        - 2 * ∫ x in (-delta)..delta, x * (Phi x * deriv Phi x) := by
  have hcont : Continuous fun x : ℝ => Phi x ^ 2 + 2 * x * (Phi x * deriv Phi x) := by
    exact (h1.continuous.pow 2).add
      ((continuous_const.mul continuous_id).mul (h1.continuous.mul h2))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => y * Phi y ^ 2)
    (f' := fun x : ℝ => Phi x ^ 2 + 2 * x * (Phi x * deriv Phi x))
    (a := -delta) (b := delta) (fun x _ => hasDerivAt_virialWeight h1 x)
    (hcont.intervalIntegrable _ _)
  have hsq : Continuous fun x : ℝ => Phi x ^ 2 := h1.continuous.pow 2
  have hmix : Continuous fun x : ℝ => 2 * x * (Phi x * deriv Phi x) :=
    (continuous_const.mul continuous_id).mul (h1.continuous.mul h2)
  have hsplit : (∫ x in (-delta)..delta, (Phi x ^ 2 + 2 * x * (Phi x * deriv Phi x)))
      = (∫ x in (-delta)..delta, Phi x ^ 2)
        + ∫ x in (-delta)..delta, 2 * x * (Phi x * deriv Phi x) :=
    intervalIntegral.integral_add (hsq.intervalIntegrable _ _) (hmix.intervalIntegrable _ _)
  have hconst : (∫ x in (-delta)..delta, 2 * x * (Phi x * deriv Phi x))
      = 2 * ∫ x in (-delta)..delta, x * (Phi x * deriv Phi x) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  have hend : (-delta) * Phi (-delta) ^ 2 = -(delta * Phi delta ^ 2) := by
    rw [heven delta]
    ring
  rw [hsplit, hconst, hend] at hFTC
  linarith

/-- A nonnegative integrand's integral over a symmetric subwindow is at most its integral over the
aperture. -/
theorem integral_window_le_aperture {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x)
    {delta : ℝ} (_hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    (∫ x in (-delta)..delta, f x) ≤ ∫ x in (-1 : ℝ)..1, f x := by
  have hi : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    hf.intervalIntegrable _ _
  have hleft : (0 : ℝ) ≤ ∫ x in (-1 : ℝ)..(-delta), f x :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => hnn x
  have hright : (0 : ℝ) ≤ ∫ x in delta..(1 : ℝ), f x :=
    intervalIntegral.integral_nonneg hd1 fun x _ => hnn x
  have h1 : (∫ x in (-1 : ℝ)..(-delta), f x) + (∫ x in (-delta)..delta, f x)
      = ∫ x in (-1 : ℝ)..delta, f x :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
  have h2 : (∫ x in (-1 : ℝ)..delta, f x) + (∫ x in delta..(1 : ℝ), f x)
      = ∫ x in (-1 : ℝ)..1, f x :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
  linarith

/-- **Chebyshev on the aperture.**  The mass outside a symmetric window is at most `δ⁻²` times the
second moment. -/
theorem integral_sq_outside_le {Phi : ℝ → ℝ} (hf : Continuous Phi)
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (∫ x in (-1 : ℝ)..1, Phi x ^ 2) - (∫ x in (-delta)..delta, Phi x ^ 2)
      ≤ (1 / delta ^ 2) * ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2 := by
  have hsq : Continuous fun x : ℝ => Phi x ^ 2 := hf.pow 2
  have hmom : Continuous fun x : ℝ => x ^ 2 * Phi x ^ 2 :=
    (continuous_id.pow 2).mul hsq
  have hi : ∀ (g : ℝ → ℝ), Continuous g → ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun g hg a b => hg.intervalIntegrable _ _
  -- the outside is the two flanks
  have h1 : (∫ x in (-1 : ℝ)..(-delta), Phi x ^ 2) + (∫ x in (-delta)..delta, Phi x ^ 2)
      = ∫ x in (-1 : ℝ)..delta, Phi x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ hsq _ _) (hi _ hsq _ _)
  have h2 : (∫ x in (-1 : ℝ)..delta, Phi x ^ 2) + (∫ x in delta..(1 : ℝ), Phi x ^ 2)
      = ∫ x in (-1 : ℝ)..1, Phi x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ hsq _ _) (hi _ hsq _ _)
  -- each flank is dominated by the weighted moment
  have hleft : (∫ x in (-1 : ℝ)..(-delta), Phi x ^ 2)
      ≤ (1 / delta ^ 2) * ∫ x in (-1 : ℝ)..(-delta), x ^ 2 * Phi x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) (hi _ hsq _ _)
      ((hmom.const_mul _).intervalIntegrable _ _) ?_
    intro x hx
    have hx2 : delta ^ 2 ≤ x ^ 2 := by nlinarith [hx.1, hx.2]
    have hd2 : (0 : ℝ) < delta ^ 2 := by positivity
    rw [← sub_nonneg]
    have : 1 / delta ^ 2 * (x ^ 2 * Phi x ^ 2) - Phi x ^ 2
        = (x ^ 2 - delta ^ 2) / delta ^ 2 * Phi x ^ 2 := by
      field_simp
    rw [this]
    have : (0 : ℝ) ≤ (x ^ 2 - delta ^ 2) / delta ^ 2 := by
      apply div_nonneg (by linarith) hd2.le
    positivity
  have hright : (∫ x in delta..(1 : ℝ), Phi x ^ 2)
      ≤ (1 / delta ^ 2) * ∫ x in delta..(1 : ℝ), x ^ 2 * Phi x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hd1 (hi _ hsq _ _)
      ((hmom.const_mul _).intervalIntegrable _ _) ?_
    intro x hx
    have hx2 : delta ^ 2 ≤ x ^ 2 := by nlinarith [hx.1, hx.2]
    have hd2 : (0 : ℝ) < delta ^ 2 := by positivity
    rw [← sub_nonneg]
    have : 1 / delta ^ 2 * (x ^ 2 * Phi x ^ 2) - Phi x ^ 2
        = (x ^ 2 - delta ^ 2) / delta ^ 2 * Phi x ^ 2 := by
      field_simp
    rw [this]
    have : (0 : ℝ) ≤ (x ^ 2 - delta ^ 2) / delta ^ 2 := by
      apply div_nonneg (by linarith) hd2.le
    positivity
  -- and the two weighted flanks together are at most the whole weighted moment
  have hm1 : (∫ x in (-1 : ℝ)..(-delta), x ^ 2 * Phi x ^ 2)
      + (∫ x in (-delta)..delta, x ^ 2 * Phi x ^ 2)
      = ∫ x in (-1 : ℝ)..delta, x ^ 2 * Phi x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ hmom _ _) (hi _ hmom _ _)
  have hm2 : (∫ x in (-1 : ℝ)..delta, x ^ 2 * Phi x ^ 2)
      + (∫ x in delta..(1 : ℝ), x ^ 2 * Phi x ^ 2)
      = ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ hmom _ _) (hi _ hmom _ _)
  have hmid : (0 : ℝ) ≤ ∫ x in (-delta)..delta, x ^ 2 * Phi x ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => by positivity
  have hdinv : (0 : ℝ) < 1 / delta ^ 2 := by positivity
  nlinarith [hleft, hright, hm1, hm2, hmid]


/-- A nonnegative integrand's integral over a subinterval of the aperture is at most its integral
over the aperture. -/
theorem integral_sub_le_aperture {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ f x) {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ x in a..b, f x) ≤ ∫ x in (-1 : ℝ)..1, f x := by
  have hi : ∀ p q : ℝ, IntervalIntegrable f volume p q := fun p q => hf.intervalIntegrable _ _
  have hleft : (0 : ℝ) ≤ ∫ x in (-1 : ℝ)..a, f x :=
    intervalIntegral.integral_nonneg ha fun x hx =>
      hnn x ⟨hx.1, le_trans hx.2 (le_trans hab hb)⟩
  have hright : (0 : ℝ) ≤ ∫ x in b..(1 : ℝ), f x :=
    intervalIntegral.integral_nonneg hb fun x hx =>
      hnn x ⟨le_trans (le_trans ha hab) hx.1, hx.2⟩
  have h1 : (∫ x in (-1 : ℝ)..a, f x) + (∫ x in a..b, f x) = ∫ x in (-1 : ℝ)..b, f x :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
  have h2 : (∫ x in (-1 : ℝ)..b, f x) + (∫ x in b..(1 : ℝ), f x) = ∫ x in (-1 : ℝ)..1, f x :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
  linarith

/-- A continuous function meets its average on any interval. -/
theorem exists_le_average {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Icc a b, (b - a) * f x ≤ ∫ t in a..b, f t := by
  obtain ⟨x0, hx0mem, hx0min⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab.le) hf.continuousOn
  refine ⟨x0, hx0mem, ?_⟩
  have hmono : (∫ _t in a..b, f x0) ≤ ∫ t in a..b, f t :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      (hf.intervalIntegrable _ _) fun t ht => hx0min ht
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono

/-- **Pointwise arithmetic--geometric split of the virial integrand.** -/
theorem virial_amgm {c x p q : ℝ} (hc : 0 < c) :
    -(2 * (x * (p * q))) ≤ c * (x ^ 2 * p ^ 2) + q ^ 2 / c := by
  have hkey := sq_nonneg (c * x * p + q)
  have hcinv : (0 : ℝ) < 1 / c := by positivity
  have h := mul_nonneg hcinv.le hkey
  have hexp : (1 / c) * (c * x * p + q) ^ 2
      = c * (x ^ 2 * p ^ 2) + 2 * (x * (p * q)) + q ^ 2 / c := by
    field_simp
    ring
  rw [hexp] at h
  linarith

/-- A window bound transfers to the square. -/
theorem sq_le_four_mul_sq {x d d0 : ℝ} (hx : |x| ≤ d) (hd : d ≤ 2 * d0) : x ^ 2 ≤ 4 * d0 ^ 2 := by
  nlinarith [sq_abs x, abs_nonneg x]

/-- The degenerate prolate weight is nonnegative on the aperture. -/
theorem prolateWeight_nonneg {x q : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : 0 ≤ (1 - x ^ 2) * q ^ 2 :=
  mul_nonneg (by nlinarith) (sq_nonneg q)

/-- The final algebra of the separation lower bound, isolated from the integrals. -/
theorem separation_algebra {A g S W E mu : ℝ}
    (hg : 0 < g) (hA : 0 < A) (hS : 0 < S)
    (hWlow : A * S - mu * S ≤ A * W)
    (hWup : g * W ≤ g * E + mu * S)
    (hEnd : A * E ≤ 4 * (mu * S)) :
    A * g ≤ mu * (5 * g + A) := by
  have h1 := mul_le_mul_of_nonneg_left hWlow hg.le
  have h2 := mul_le_mul_of_nonneg_left hWup hA.le
  have h3 := mul_le_mul_of_nonneg_left hEnd hg.le
  have hkey : (A * g) * S ≤ (mu * (5 * g + A)) * S := by linarith [h1, h2, h3]
  exact le_of_mul_le_mul_right hkey hS

set_option maxHeartbeats 2000000 in
/-- **Gaussian defect bound.**  On a window `[−δ, δ]` with `δ ∈ [δ₀, 2δ₀]` the deviation of the
prolate eigenfunction from the Gaussian shape, measured by `∫ (Φ′ + cxΦ)²`, is controlled by how far
the separation constant `μ = c·s` exceeds the first oscillator rung:

`δ₀²(1 − 4δ₀²) ∫_{−δ}^{δ}(Φ′ + cxΦ)² ≤ ∫Φ² · (5μ(1 − 4δ₀²) + cδ₀²μ − cδ₀²(1 − 4δ₀²))` .

Nonnegativity of the left side is the uniform lower bound for `μ`; the estimate itself is the
quantitative form, saying that once `μ` approaches `1` the mode approaches `e^{−cx²/2}`. -/
theorem exists_bandwidthSeparation_defect {c chi delta0 : ℝ} {Phi : ℝ → ℝ}
    (hc : 0 < c) (hd0 : 0 < delta0) (hd1 : delta0 ≤ 1 / 4)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heven : Function.Even Phi)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    ∃ delta ∈ Icc delta0 (2 * delta0),
      delta0 ^ 2 * (1 - 4 * delta0 ^ 2)
          * (∫ x in (-delta)..delta, (deriv Phi x + c * x * Phi x) ^ 2)
        ≤ (∫ x in (-1 : ℝ)..1, Phi x ^ 2)
          * (5 * (c * radialSeparationRatio c chi) * (1 - 4 * delta0 ^ 2)
            + c * delta0 ^ 2 * (c * radialSeparationRatio c chi)
            - c * delta0 ^ 2 * (1 - 4 * delta0 ^ 2)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have h1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hsm).1
  have hdd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Phi) := (contDiff_infty_iff_deriv.mp hsm).2
  have h2c : Continuous (deriv Phi) := ((contDiff_infty_iff_deriv.mp hdd).1).continuous
  have hcPhi : Continuous Phi := h1.continuous
  have hRay := GaloisForLFunctions.RHTower.neg_separation_div_sq_mul_integral_sq_eq hcne hsm heig
  have hbase := integral_sq_mul_sq_le_separation hcne hsm heig
  have hGnn : (0 : ℝ) ≤ ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (deriv Phi x) ^ 2 :=
    integral_prolateGradient_nonneg
  have hMnn : (0 : ℝ) ≤ ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => by positivity
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∫ x in (-1 : ℝ)..1, Phi x ^ 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (deriv Phi x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨mu, hmu⟩ : ∃ mu : ℝ, mu = c * radialSeparationRatio c chi := ⟨_, rfl⟩
  rw [← hS] at hRay
  rw [← hM] at hMnn hbase hRay
  rw [← hS] at hbase
  rw [← hG] at hGnn hRay
  have hmuval : mu = -chi / c := by
    rw [hmu, radialSeparationRatio]
    field_simp
  have hmuS : mu * S = G / c + c * M := by
    rw [hmuval]
    field_simp at hRay ⊢
    linarith
  have hMle : c * M ≤ mu * S := by
    have hstep : c * M ≤ c * (radialSeparationRatio c chi * S) :=
      mul_le_mul_of_nonneg_left hbase hc.le
    rw [hmu]
    linarith [hstep]
  have hmunn : (0 : ℝ) ≤ mu * S := by
    have hG' : (0 : ℝ) ≤ G / c := div_nonneg hGnn hc.le
    have hM' : (0 : ℝ) ≤ c * M := mul_nonneg hc.le hMnn
    linarith [hmuS]
  have hd0sq : (0 : ℝ) < delta0 ^ 2 := by positivity
  have hgap : (0 : ℝ) < 1 - 4 * delta0 ^ 2 := by nlinarith
  have hgap1 : 1 - 4 * delta0 ^ 2 ≤ 1 := by nlinarith
  have hd0lt : delta0 < 2 * delta0 := by linarith
  obtain ⟨delta, hdmem, hdavg⟩ :=
    exists_le_average (f := fun x : ℝ => Phi x ^ 2) (hcPhi.pow 2) hd0lt
  have hdlow : delta0 ≤ delta := hdmem.1
  have hdhigh : delta ≤ 2 * delta0 := hdmem.2
  have hdpos : 0 < delta := lt_of_lt_of_le hd0 hdlow
  have hdle1 : delta ≤ 1 := by nlinarith
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∫ x in (-delta)..delta, Phi x ^ 2 := ⟨_, rfl⟩
  obtain ⟨Mw, hMw⟩ : ∃ Mw : ℝ, Mw = ∫ x in (-delta)..delta, x ^ 2 * Phi x ^ 2 := ⟨_, rfl⟩
  obtain ⟨Vw, hVw⟩ : ∃ Vw : ℝ, Vw = ∫ x in (-delta)..delta, (deriv Phi x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 2 * delta * Phi delta ^ 2 := ⟨_, rfl⟩
  -- Chebyshev lower bound for the window mass
  have hcheb : S - W ≤ (1 / delta ^ 2) * M := by
    rw [hS, hW, hM]
    exact integral_sq_outside_le hcPhi hdpos hdle1
  have hchebs : S - W ≤ (1 / delta0 ^ 2) * M := by
    have hinv : (1 : ℝ) / delta ^ 2 ≤ 1 / delta0 ^ 2 := by
      apply one_div_le_one_div_of_le hd0sq
      nlinarith
    nlinarith [hcheb, hMnn, hinv]
  have hWlow : c * delta0 ^ 2 * S - mu * S ≤ c * delta0 ^ 2 * W := by
    have h := mul_le_mul_of_nonneg_left hchebs (mul_nonneg hc.le (sq_nonneg delta0))
    have hid : c * delta0 ^ 2 * ((1 / delta0 ^ 2) * M) = c * M := by field_simp
    rw [hid] at h
    linarith [hMle]
  -- the virial upper bound for the window mass
  have hvir : W = E - 2 * ∫ x in (-delta)..delta, x * (Phi x * deriv Phi x) := by
    rw [hW, hE]
    exact integral_sq_window h1 h2c heven delta
  have hcont1 : Continuous fun x : ℝ => x * (Phi x * deriv Phi x) :=
    continuous_id.mul (hcPhi.mul h2c)
  have hcont2 : Continuous fun x : ℝ => c * (x ^ 2 * Phi x ^ 2) + (deriv Phi x) ^ 2 / c := by
    fun_prop
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∫ x in (-delta)..delta, (deriv Phi x + c * x * Phi x) ^ 2 :=
    ⟨_, rfl⟩
  have hDnn : (0 : ℝ) ≤ D := by
    rw [hD]
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hcontD : Continuous fun x : ℝ => (deriv Phi x + c * x * Phi x) ^ 2 := by fun_prop
  have hstep : (∫ x in (-delta)..delta, -(2 * (x * (Phi x * deriv Phi x))))
      = (∫ x in (-delta)..delta, (c * (x ^ 2 * Phi x ^ 2) + (deriv Phi x) ^ 2 / c))
        - D / c := by
    rw [hD, ← intervalIntegral.integral_div, ← intervalIntegral.integral_sub
      (hcont2.intervalIntegrable _ _) ((hcontD.div_const c).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    field_simp
    ring
  have hleft : (∫ x in (-delta)..delta, -(2 * (x * (Phi x * deriv Phi x))))
      = -(2 * ∫ x in (-delta)..delta, x * (Phi x * deriv Phi x)) := by
    have hcongr : (∫ x in (-delta)..delta, -(2 * (x * (Phi x * deriv Phi x))))
        = ∫ x in (-delta)..delta, (-2 : ℝ) * (x * (Phi x * deriv Phi x)) :=
      intervalIntegral.integral_congr fun x _ => by ring
    rw [hcongr, intervalIntegral.integral_const_mul]
    ring
  have hsplit : (∫ x in (-delta)..delta, (c * (x ^ 2 * Phi x ^ 2) + (deriv Phi x) ^ 2 / c))
      = c * Mw + Vw / c := by
    have ha : Continuous fun x : ℝ => c * (x ^ 2 * Phi x ^ 2) :=
      continuous_const.mul ((continuous_id.pow 2).mul (hcPhi.pow 2))
    have hb : Continuous fun x : ℝ => (deriv Phi x) ^ 2 / c := by fun_prop
    rw [hMw, hVw,
      intervalIntegral.integral_add (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
  have hmom : Mw ≤ M := by
    rw [hMw, hM]
    exact integral_sub_le_aperture ((continuous_id.pow 2).mul (hcPhi.pow 2))
      (fun x _ => mul_nonneg (sq_nonneg x) (sq_nonneg (Phi x))) (by linarith) (by linarith) hdle1
  have hmomnn : (0 : ℝ) ≤ Mw := by
    rw [hMw]
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ =>
      mul_nonneg (sq_nonneg x) (sq_nonneg (Phi x))
  have hgrad : (1 - 4 * delta0 ^ 2) * Vw ≤ G := by
    have hin : (1 - 4 * delta0 ^ 2) * Vw
        ≤ ∫ x in (-delta)..delta, (1 - x ^ 2) * (deriv Phi x) ^ 2 := by
      rw [hVw, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by linarith)
        (((h2c.pow 2).const_mul _).intervalIntegrable _ _)
        (((continuous_const.sub (continuous_id.pow 2)).mul (h2c.pow 2)).intervalIntegrable _ _) ?_
      intro x hx
      have hx2 : x ^ 2 ≤ 4 * delta0 ^ 2 :=
        sq_le_four_mul_sq (abs_le.2 ⟨hx.1, hx.2⟩) hdhigh
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (deriv Phi x))
    have hout : (∫ x in (-delta)..delta, (1 - x ^ 2) * (deriv Phi x) ^ 2) ≤ G := by
      rw [hG]
      exact integral_sub_le_aperture
        ((continuous_const.sub (continuous_id.pow 2)).mul (h2c.pow 2))
        (fun x hx => prolateWeight_nonneg hx.1 hx.2)
        (by linarith) (by linarith) hdle1
    linarith
  have hWeq : W = E + (c * Mw + Vw / c) - D / c := by
    rw [hleft, hsplit] at hstep
    linarith [hvir, hstep]
  have hWeq' : c * W = c * E + (c * (c * Mw) + Vw) - D := by
    rw [hWeq]
    field_simp
  have hA : (1 - 4 * delta0 ^ 2) * (c * Mw) ≤ c * M := by
    have hp1 : (0 : ℝ) ≤ c * Mw := mul_nonneg hc.le hmomnn
    have hp2 : c * Mw ≤ c * M := mul_le_mul_of_nonneg_left hmom hc.le
    nlinarith [hp1, hp2, hgap1]
  have hmuSc : c * (mu * S) = G + c * (c * M) := by
    rw [hmuS]
    field_simp
  have hAB : (1 - 4 * delta0 ^ 2) * (c * (c * Mw) + Vw) ≤ c * (mu * S) := by
    have hAc : (1 - 4 * delta0 ^ 2) * (c * (c * Mw)) ≤ c * (c * M) := by
      have := mul_le_mul_of_nonneg_left hA hc.le
      nlinarith [this]
    linarith [hAc, hgrad, hmuSc]
  -- the endpoint contribution
  have hEnd : c * delta0 ^ 2 * E ≤ 4 * (mu * S) := by
    have hstep2 : delta0 * Phi delta ^ 2 ≤ (1 / delta0 ^ 2) * M := by
      have hsub2 : (∫ t in delta0..(2 * delta0), t ^ 2 * Phi t ^ 2) ≤ M := by
        rw [hM]
        exact integral_sub_le_aperture ((continuous_id.pow 2).mul (hcPhi.pow 2))
          (fun x _ => mul_nonneg (sq_nonneg x) (sq_nonneg (Phi x))) (by linarith) (by linarith)
          (by nlinarith)
      have hmono : (∫ t in delta0..(2 * delta0), Phi t ^ 2)
          ≤ (1 / delta0 ^ 2) * ∫ t in delta0..(2 * delta0), t ^ 2 * Phi t ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on (by linarith)
          ((hcPhi.pow 2).intervalIntegrable _ _)
          ((((continuous_id.pow 2).mul (hcPhi.pow 2)).const_mul _).intervalIntegrable _ _) ?_
        intro t ht
        have ht2 : delta0 ^ 2 ≤ t ^ 2 := by nlinarith [ht.1, ht.2]
        rw [← sub_nonneg]
        have hid : 1 / delta0 ^ 2 * (t ^ 2 * Phi t ^ 2) - Phi t ^ 2
            = (t ^ 2 - delta0 ^ 2) / delta0 ^ 2 * Phi t ^ 2 := by field_simp
        rw [hid]
        have hnn : (0 : ℝ) ≤ (t ^ 2 - delta0 ^ 2) / delta0 ^ 2 :=
          div_nonneg (by linarith) hd0sq.le
        positivity
      have hinv : (0 : ℝ) < 1 / delta0 ^ 2 := by positivity
      nlinarith [hmono, hsub2, hinv, hdavg]
    have hphi : Phi delta ^ 2 * delta0 ^ 3 ≤ M := by
      have h := mul_le_mul_of_nonneg_right hstep2 hd0sq.le
      have hid : (1 / delta0 ^ 2 * M) * delta0 ^ 2 = M := by field_simp
      rw [hid] at h
      nlinarith [h]
    have hsqnn : (0 : ℝ) ≤ Phi delta ^ 2 := sq_nonneg _
    have hnn : (0 : ℝ) ≤ c * delta0 ^ 2 := mul_nonneg hc.le (sq_nonneg delta0)
    have hchain : c * delta0 ^ 2 * E ≤ c * delta0 ^ 2 * (4 * delta0 * Phi delta ^ 2) := by
      rw [hE]
      have hstep3 : 2 * delta * Phi delta ^ 2 ≤ 4 * delta0 * Phi delta ^ 2 := by
        nlinarith [hsqnn, hdhigh]
      exact mul_le_mul_of_nonneg_left hstep3 hnn
    have hnext : c * delta0 ^ 2 * (4 * delta0 * Phi delta ^ 2) ≤ 4 * (c * M) := by
      nlinarith [hphi, hc]
    linarith [hMle]
  -- assemble the defect bound
  refine ⟨delta, hdmem, ?_⟩
  rw [← hD, ← hS, ← hmu]
  have hEbd : (1 - 4 * delta0 ^ 2) * (c * delta0 ^ 2 * E)
      ≤ (1 - 4 * delta0 ^ 2) * (4 * (mu * S)) := mul_le_mul_of_nonneg_left hEnd hgap.le
  have hABd : delta0 ^ 2 * ((1 - 4 * delta0 ^ 2) * (c * (c * Mw) + Vw))
      ≤ delta0 ^ 2 * (c * (mu * S)) := mul_le_mul_of_nonneg_left hAB hd0sq.le
  have hWd : (1 - 4 * delta0 ^ 2) * (c * delta0 ^ 2 * S - mu * S)
      ≤ (1 - 4 * delta0 ^ 2) * (c * delta0 ^ 2 * W) :=
    mul_le_mul_of_nonneg_left hWlow hgap.le
  have hDeq : delta0 ^ 2 * (1 - 4 * delta0 ^ 2) * D
      = (1 - 4 * delta0 ^ 2) * (c * delta0 ^ 2 * E)
        + delta0 ^ 2 * ((1 - 4 * delta0 ^ 2) * (c * (c * Mw) + Vw))
        - (1 - 4 * delta0 ^ 2) * (c * delta0 ^ 2 * W) := by
    linear_combination (delta0 ^ 2 * (1 - 4 * delta0 ^ 2)) * hWeq'
  linarith [hDeq, hEbd, hABd, hWd]

/-- **Uniform lower bound for the oscillator separation constant.**  For every window scale
`δ₀ ∈ (0, 1/4]` the separation constant `μ = c·s` of a nonzero even smooth prolate eigenfunction
satisfies `c δ₀² (1 − 4δ₀²) ≤ μ (5(1 − 4δ₀²) + c δ₀²)`, so at fixed `δ₀` it is asymptotically at
least `1 − 4δ₀²`. -/
theorem bandwidthSeparation_lower {c chi delta0 : ℝ} {Phi : ℝ → ℝ}
    (hc : 0 < c) (hd0 : 0 < delta0) (hd1 : delta0 ≤ 1 / 4)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heven : Function.Even Phi)
    (hpos : 0 < ∫ x in (-1 : ℝ)..1, Phi x ^ 2)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    c * delta0 ^ 2 * (1 - 4 * delta0 ^ 2)
      ≤ (c * radialSeparationRatio c chi) * (5 * (1 - 4 * delta0 ^ 2) + c * delta0 ^ 2) := by
  obtain ⟨delta, hdmem, hbd⟩ :=
    exists_bandwidthSeparation_defect hc hd0 hd1 hsm heven heig
  have hd0sq : (0 : ℝ) < delta0 ^ 2 := by positivity
  have hgap : (0 : ℝ) < 1 - 4 * delta0 ^ 2 := by nlinarith
  have hDnn : (0 : ℝ) ≤ ∫ x in (-delta)..delta, (deriv Phi x + c * x * Phi x) ^ 2 := by
    have hdpos : 0 < delta := lt_of_lt_of_le hd0 hdmem.1
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hlhs : (0 : ℝ) ≤ delta0 ^ 2 * (1 - 4 * delta0 ^ 2)
      * (∫ x in (-delta)..delta, (deriv Phi x + c * x * Phi x) ^ 2) := by positivity
  have hkey : (0 : ℝ) ≤ (∫ x in (-1 : ℝ)..1, Phi x ^ 2)
      * (5 * (c * radialSeparationRatio c chi) * (1 - 4 * delta0 ^ 2)
        + c * delta0 ^ 2 * (c * radialSeparationRatio c chi)
        - c * delta0 ^ 2 * (1 - 4 * delta0 ^ 2)) := le_trans hlhs hbd
  have hfac := (mul_nonneg_iff_of_pos_left hpos).1 hkey
  linarith

end RHTower
