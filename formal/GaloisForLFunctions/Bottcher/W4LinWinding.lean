/-
# Iterated quadratic-image winding doubling (W4-lin, period chain step 1)

The winding calculus for the linear-gap pair close (task #139): for `‖c‖ ≥ 2` and a loop
staying beyond `√(2‖c‖)`, the `n`-fold quadratic image loop `f_c^{[n]} ∘ γ` winds exactly
`2ⁿ` times the base winding about `0` — and about EVERY point of `closedBall 0 √(2‖c‖)`.

Mechanism: `{√(2‖c‖) < ‖z‖}` is forward invariant (`‖f_c z‖ ≥ ‖z‖² − ‖c‖ > ‖c‖ ≥ √(2‖c‖)`);
both square roots `±u` of `−c` have norm `√‖c‖ ≤ √(2‖c‖)`, so the pair rule
`windInt ℓ u + windInt ℓ (−u) = windInt (ℓ.quadImage c) 0` combines with winding constancy on
the closed ball (`windInt_eq_on_preconnected`) to double the winding at each step.

Since the filled Julia set, all preimages of `0`, and all critical structure of `f_c` lie in
`closedBall 0 √(2‖c‖)` (crude escape), this pins the `dlog`-periods of `φ_c ∘ f_c^{[n]}` along
every tower cycle of a second parameter's norm-floored tower to `2πi·2ⁿ·(integer)` — the
divisibility input of the `2ⁿ`-th-root extension.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.WindingCertificates
import GaloisForLFunctions.Bottcher.PolyAsymptotic
import GaloisForLFunctions.Bottcher.SectionInverse
import GaloisForLFunctions.Bottcher.GreenSuperlevel
import GaloisForLFunctions.Bottcher.GreenPullback
import GaloisForLFunctions.Bottcher.HolomorphicBranch
import GaloisForLFunctions.Bottcher.SlitAnnulus
import GaloisForLFunctions.Bottcher.LoopGlue

open Complex Set Metric

namespace Bottcher

/-- **Forward invariance of the far region** `{√(2‖c‖) < ‖z‖}` under `f_c`, for `‖c‖ ≥ 2`. -/
theorem sqrt_lt_norm_quadratic {c z : ℂ} (hc : (2:ℝ) ≤ ‖c‖)
    (hz : Real.sqrt (2 * ‖c‖) < ‖z‖) : Real.sqrt (2 * ‖c‖) < ‖quadratic c z‖ := by
  have hs0 : (0:ℝ) ≤ Real.sqrt (2 * ‖c‖) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * ‖c‖) ^ 2 = 2 * ‖c‖ := Real.sq_sqrt (by positivity)
  have hzsq : 2 * ‖c‖ < ‖z‖ ^ 2 := by nlinarith
  have h1 : ‖z ^ 2‖ ≤ ‖quadratic c z‖ + ‖c‖ := by
    have h2 : quadratic c z = z ^ 2 + c := rfl
    calc ‖z ^ 2‖ = ‖(z ^ 2 + c) + (-c)‖ := by ring_nf
      _ ≤ ‖z ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
      _ = ‖quadratic c z‖ + ‖c‖ := by rw [← h2, norm_neg]
  have h3 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic c z‖ := by
    rw [← norm_pow] at hzsq ⊢
    linarith
  have hcsqrt : Real.sqrt (2 * ‖c‖) ≤ ‖c‖ := by
    have h4 : Real.sqrt (2 * ‖c‖) ≤ Real.sqrt (‖c‖ ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (norm_nonneg c)] at h4
  have h5 : ‖z‖ ^ 2 - ‖c‖ > ‖c‖ := by
    rw [← norm_pow] at hzsq
    have : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
    nlinarith [norm_pow z 2]
  linarith

/-- **Iterated winding doubling about the ball.**  For `‖c‖ ≥ 2` and a loop beyond `√(2‖c‖)`,
the `n`-fold quadratic image loop winds `2ⁿ` times the base winding about `0`. -/
theorem windInt_iterate_quadImage_zero {c : ℂ} (hc : (2:ℝ) ≤ ‖c‖) (ℓ : C1Loop)
    (hfar : ∀ θ, Real.sqrt (2 * ‖c‖) < ‖ℓ.γ θ‖) (n : ℕ) :
    windInt ((fun ℓ' => C1Loop.quadImage ℓ' c)^[n] ℓ) 0 = 2 ^ n * windInt ℓ 0 := by
  -- a square root of `−c`
  have hcne : (-c : ℂ) ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h, norm_zero] at hc
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u ^ 2 = -c := by
    refine ⟨Complex.exp (Complex.log (-c) / 2), ?_⟩
    rw [← Complex.exp_nat_mul]
    rw [show ((2 : ℕ) : ℂ) * (Complex.log (-c) / 2) = Complex.log (-c) by push_cast; ring]
    exact Complex.exp_log hcne
  have hu2 : ‖u‖ ^ 2 = ‖c‖ := by rw [← norm_pow, hu, norm_neg]
  have hus : ‖u‖ ≤ Real.sqrt (2 * ‖c‖) := by
    have h1 : ‖u‖ = Real.sqrt (‖c‖) := by
      rw [← hu2, Real.sqrt_sq (norm_nonneg u)]
    rw [h1]
    exact Real.sqrt_le_sqrt (by linarith)
  have hquadu : quadratic c u = 0 := by
    show u ^ 2 + c = 0
    rw [hu]
    ring
  -- the invariant far bound along the iterated image loops
  have hγ_iter : ∀ m : ℕ, ∀ θ : ℝ,
      Real.sqrt (2 * ‖c‖) < ‖((fun ℓ' => C1Loop.quadImage ℓ' c)^[m] ℓ).γ θ‖ := by
    intro m
    induction m with
    | zero => exact hfar
    | succ k ih =>
        intro θ
        rw [Function.iterate_succ_apply']
        exact sqrt_lt_norm_quadratic hc (ih θ)
  -- winding constancy on the closed ball, per level
  have hconst : ∀ m : ℕ, ∀ p q : ℂ, ‖p‖ ≤ Real.sqrt (2 * ‖c‖) →
      ‖q‖ ≤ Real.sqrt (2 * ‖c‖) →
      windInt ((fun ℓ' => C1Loop.quadImage ℓ' c)^[m] ℓ) p
        = windInt ((fun ℓ' => C1Loop.quadImage ℓ' c)^[m] ℓ) q := by
    intro m p q hp hq
    apply windInt_eq_on_preconnected _ (convex_closedBall (0:ℂ)
      (Real.sqrt (2 * ‖c‖))).isPreconnected
    · intro z hz θ hcon
      rw [mem_closedBall, dist_zero_right] at hz
      have := hγ_iter m θ
      rw [hcon] at this
      linarith
    · rw [mem_closedBall, dist_zero_right]
      exact hp
    · rw [mem_closedBall, dist_zero_right]
      exact hq
  -- the doubling induction
  induction n with
  | zero => simp
  | succ k ih =>
      set ℓk : C1Loop := (fun ℓ' => C1Loop.quadImage ℓ' c)^[k] ℓ with hℓkdef
      have havu : ℓk.Avoids u := by
        intro θ h
        have h1 := hγ_iter k θ
        rw [h] at h1
        linarith [hus]
      have havnu : ℓk.Avoids (-u) := by
        intro θ h
        have h1 := hγ_iter k θ
        rw [h] at h1
        rw [norm_neg] at h1
        linarith [hus]
      have hpair := windInt_add_neg_eq_quadImage ℓk c u havu havnu
      rw [hquadu] at hpair
      have hstep : windInt ((fun ℓ' => C1Loop.quadImage ℓ' c)^[k+1] ℓ) 0
          = windInt ℓk u + windInt ℓk (-u) := by
        rw [Function.iterate_succ_apply']
        exact hpair.symm
      have hcu : windInt ℓk u = windInt ℓk 0 :=
        hconst k u 0 hus (by simp [Real.sqrt_nonneg])
      have hcnu : windInt ℓk (-u) = windInt ℓk 0 := by
        apply hconst k (-u) 0 _ (by simp [Real.sqrt_nonneg])
        rw [norm_neg]
        exact hus
      rw [hstep, hcu, hcnu, ih]
      ring

/-- **Iterated winding doubling at any ball point.**  The `n`-fold quadratic image loop winds
`2ⁿ · windInt ℓ 0` about every point of `closedBall 0 √(2‖c‖)` — in particular about every
point of the filled Julia set `K_c` and every `f_c`-preimage of `0`. -/
theorem windInt_iterate_quadImage_ball {c : ℂ} (hc : (2:ℝ) ≤ ‖c‖) (ℓ : C1Loop)
    (hfar : ∀ θ, Real.sqrt (2 * ‖c‖) < ‖ℓ.γ θ‖) (n : ℕ)
    {p : ℂ} (hp : ‖p‖ ≤ Real.sqrt (2 * ‖c‖)) :
    windInt ((fun ℓ' => C1Loop.quadImage ℓ' c)^[n] ℓ) p = 2 ^ n * windInt ℓ 0 := by
  have hγ_iter : ∀ m : ℕ, ∀ θ : ℝ,
      Real.sqrt (2 * ‖c‖) < ‖((fun ℓ' => C1Loop.quadImage ℓ' c)^[m] ℓ).γ θ‖ := by
    intro m
    induction m with
    | zero => exact hfar
    | succ k ih =>
        intro θ
        rw [Function.iterate_succ_apply']
        exact sqrt_lt_norm_quadratic hc (ih θ)
  have hconst : windInt ((fun ℓ' => C1Loop.quadImage ℓ' c)^[n] ℓ) p
      = windInt ((fun ℓ' => C1Loop.quadImage ℓ' c)^[n] ℓ) 0 := by
    apply windInt_eq_on_preconnected _ (convex_closedBall (0:ℂ)
      (Real.sqrt (2 * ‖c‖))).isPreconnected
    · intro z hz θ hcon
      rw [mem_closedBall, dist_zero_right] at hz
      have := hγ_iter n θ
      rw [hcon] at this
      linarith
    · rw [mem_closedBall, dist_zero_right]
      exact hp
    · rw [mem_closedBall, dist_zero_right]
      simp [Real.sqrt_nonneg]
  rw [hconst]
  exact windInt_iterate_quadImage_zero hc ℓ hfar n

end Bottcher

namespace Bottcher

/-- The image loop `f ∘ γ` under an analytic `f`, with chain-rule velocity. -/
noncomputable def C1Loop.analyticImage (ℓ : C1Loop) {f : ℂ → ℂ} {A : Set ℂ}
    (hf : AnalyticOnNhd ℂ f A) (hmem : ∀ θ : ℝ, ℓ.γ θ ∈ A) : C1Loop where
  γ := fun θ => f (ℓ.γ θ)
  γ' := fun θ => _root_.deriv f (ℓ.γ θ) * ℓ.γ' θ
  cont := (hf.continuousOn).comp_continuous ℓ.cont hmem
  cont' := ((hf.deriv.continuousOn).comp_continuous ℓ.cont hmem).mul ℓ.cont'
  deriv := by
    intro θ hθ
    have h1 : HasDerivAt f (_root_.deriv f (ℓ.γ θ)) (ℓ.γ θ) :=
      (hf _ (hmem θ)).differentiableAt.hasDerivAt
    exact h1.comp θ (ℓ.deriv θ hθ)
  closed := by simp only [ℓ.closed]

/-- The winding of an analytic image loop about `0` is the `dlog`-period of `f` along the
base loop. -/
theorem windInt_analyticImage_zero (ℓ : C1Loop) {f : ℂ → ℂ} {A : Set ℂ}
    (hf : AnalyticOnNhd ℂ f A) (hmem : ∀ θ : ℝ, ℓ.γ θ ∈ A)
    (hne : ∀ θ : ℝ, f (ℓ.γ θ) ≠ 0) :
    windInt (ℓ.analyticImage hf hmem) 0
      = ∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv f (ℓ.γ θ) * ℓ.γ' θ := by
  apply intervalIntegral.integral_congr
  intro θ _
  show (f (ℓ.γ θ) - 0)⁻¹ * (_root_.deriv f (ℓ.γ θ) * ℓ.γ' θ) = logDeriv f (ℓ.γ θ) * ℓ.γ' θ
  rw [sub_zero, logDeriv, Pi.div_apply]
  field_simp [hne θ]

/-- Pointwise description of the iterated quadratic image loop: positions. -/
theorem iterate_quadImage_γ (c : ℂ) (ℓ : C1Loop) (m : ℕ) (θ : ℝ) :
    ((fun ℓ' => C1Loop.quadImage ℓ' c)^[m] ℓ).γ θ = (quadratic c)^[m] (ℓ.γ θ) := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show quadratic c (((fun ℓ' => C1Loop.quadImage ℓ' c)^[k] ℓ).γ θ) = _
      rw [ih]

/-- Pointwise description of the iterated quadratic image loop: velocities. -/
theorem iterate_quadImage_γ' (c : ℂ) (ℓ : C1Loop) (m : ℕ) (θ : ℝ) :
    ((fun ℓ' => C1Loop.quadImage ℓ' c)^[m] ℓ).γ' θ
      = deriv ((quadratic c)^[m]) (ℓ.γ θ) * ℓ.γ' θ := by
  have hdq : ∀ z : ℂ, deriv (quadratic c) z = 2 * z := by
    intro z
    have h1 : HasDerivAt (quadratic c) (2 * z) z := by
      have h0 : HasDerivAt (fun x : ℂ => x ^ 2 + c) (2 * z) z := by
        simpa using (hasDerivAt_pow 2 z).add_const c
      exact h0
    exact h1.deriv
  have hdiff : ∀ j : ℕ, ∀ z : ℂ, DifferentiableAt ℂ ((quadratic c)^[j]) z := by
    intro j
    induction j with
    | zero => intro z; simp
    | succ k ih =>
        intro z
        rw [Function.iterate_succ']
        have h1 : DifferentiableAt ℂ (quadratic c) (((quadratic c)^[k]) z) := by
          have h0 : HasDerivAt (fun x : ℂ => x ^ 2 + c) (2 * ((quadratic c)^[k]) z)
              (((quadratic c)^[k]) z) := by
            simpa using (hasDerivAt_pow 2 (((quadratic c)^[k]) z)).add_const c
          exact h0.differentiableAt
        exact h1.comp z (ih z)
  induction m with
  | zero =>
      show ℓ.γ' θ = deriv (fun z : ℂ => z) (ℓ.γ θ) * ℓ.γ' θ
      rw [deriv_id'']
      ring
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show 2 * ((fun ℓ' => C1Loop.quadImage ℓ' c)^[k] ℓ).γ θ
            * ((fun ℓ' => C1Loop.quadImage ℓ' c)^[k] ℓ).γ' θ = _
      rw [ih, iterate_quadImage_γ]
      have hcomp : deriv ((quadratic c)^[k+1]) (ℓ.γ θ)
          = deriv (quadratic c) ((quadratic c)^[k] (ℓ.γ θ))
            * deriv ((quadratic c)^[k]) (ℓ.γ θ) := by
        have h1 : (quadratic c)^[k+1] = quadratic c ∘ (quadratic c)^[k] := by
          funext z
          exact Function.iterate_succ_apply' _ _ _
        rw [h1]
        apply deriv_comp
        · have : HasDerivAt (quadratic c) (2 * ((quadratic c)^[k]) (ℓ.γ θ))
              (((quadratic c)^[k]) (ℓ.γ θ)) := by
            have h0 : HasDerivAt (fun x : ℂ => x ^ 2 + c)
                (2 * ((quadratic c)^[k]) (ℓ.γ θ)) (((quadratic c)^[k]) (ℓ.γ θ)) := by
              simpa using (hasDerivAt_pow 2 (((quadratic c)^[k]) (ℓ.γ θ))).add_const c
            exact h0
          exact this.differentiableAt
        · exact hdiff k _
      rw [hcomp, hdq]
      ring

/-- **The pushed period is `2^m` times the base winding.**  For `‖c‖ ≥ 2`, a loop `ℓ` beyond
`√(2‖c‖)`, and an analytic `φ` on `A` containing the `m`-th image loop, nonvanishing there and
leashed to the identity (`‖φ(w) − w‖ < ‖w‖`), the `dlog`-period of `φ ∘ f_c^{[m]}` along `ℓ`
equals `2^m · windInt ℓ 0` — the divisibility input of the `2^m`-th-root extension. -/
theorem period_push_eq_two_pow_windInt {c : ℂ} (hc : (2:ℝ) ≤ ‖c‖) (ℓ : C1Loop)
    (hfar : ∀ θ, Real.sqrt (2 * ‖c‖) < ‖ℓ.γ θ‖) (m : ℕ)
    {φ : ℂ → ℂ} {A : Set ℂ} (hφ : AnalyticOnNhd ℂ φ A)
    (hmem : ∀ θ : ℝ, (quadratic c)^[m] (ℓ.γ θ) ∈ A)
    (hφne : ∀ θ : ℝ, φ ((quadratic c)^[m] (ℓ.γ θ)) ≠ 0)
    (hleash : ∀ θ : ℝ, ‖φ ((quadratic c)^[m] (ℓ.γ θ)) - (quadratic c)^[m] (ℓ.γ θ)‖
      < ‖(quadratic c)^[m] (ℓ.γ θ)‖) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (φ ∘ (quadratic c)^[m]) (ℓ.γ θ) * ℓ.γ' θ)
      = 2 ^ m * windInt ℓ 0 := by
  set Γ : C1Loop := (fun ℓ' => C1Loop.quadImage ℓ' c)^[m] ℓ with hΓdef
  have hΓγ : ∀ θ, Γ.γ θ = (quadratic c)^[m] (ℓ.γ θ) := iterate_quadImage_γ c ℓ m
  have hmemΓ : ∀ θ : ℝ, Γ.γ θ ∈ A := fun θ => by rw [hΓγ]; exact hmem θ
  have hφneΓ : ∀ θ : ℝ, φ (Γ.γ θ) ≠ 0 := fun θ => by rw [hΓγ]; exact hφne θ
  have hdiff : ∀ j : ℕ, ∀ z : ℂ, DifferentiableAt ℂ ((quadratic c)^[j]) z := by
    intro j
    induction j with
    | zero => intro z; simp
    | succ k ih =>
        intro z
        rw [Function.iterate_succ']
        have h1 : DifferentiableAt ℂ (quadratic c) (((quadratic c)^[k]) z) := by
          have h0 : HasDerivAt (fun x : ℂ => x ^ 2 + c) (2 * ((quadratic c)^[k]) z)
              (((quadratic c)^[k]) z) := by
            simpa using (hasDerivAt_pow 2 (((quadratic c)^[k]) z)).add_const c
          exact h0.differentiableAt
        exact h1.comp z (ih z)
  -- the period along `ℓ` is the winding of the `φ`-image of the pushed loop
  have hstep1 : (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (φ ∘ (quadratic c)^[m]) (ℓ.γ θ) * ℓ.γ' θ)
      = windInt (Γ.analyticImage hφ hmemΓ) 0 := by
    rw [windInt_analyticImage_zero Γ hφ hmemΓ hφneΓ]
    apply intervalIntegral.integral_congr
    intro θ _
    show logDeriv (φ ∘ (quadratic c)^[m]) (ℓ.γ θ) * ℓ.γ' θ
        = logDeriv φ (Γ.γ θ) * Γ.γ' θ
    have hld : logDeriv (φ ∘ (quadratic c)^[m]) (ℓ.γ θ)
        = logDeriv φ ((quadratic c)^[m] (ℓ.γ θ)) * _root_.deriv ((quadratic c)^[m]) (ℓ.γ θ) :=
      logDeriv_comp ((hφ _ (hmem θ)).differentiableAt) (hdiff m _)
    rw [hld, hΓγ, hΓdef, iterate_quadImage_γ']
    ring
  -- the leash collapses `φ` to the identity
  have hstep2 : windInt (Γ.analyticImage hφ hmemΓ) 0 = windInt Γ 0 := by
    apply windInt_eq_of_leash
    intro θ
    show ‖φ (Γ.γ θ) - Γ.γ θ‖ < ‖Γ.γ θ - 0‖
    rw [sub_zero, hΓγ]
    exact hleash θ
  rw [hstep1, hstep2, hΓdef]
  exact windInt_iterate_quadImage_zero hc ℓ hfar m

end Bottcher

namespace Bottcher

/-- **The pushed Böttcher period along a floored loop.**  For `‖c‖ ≥ 2`, a loop beyond
`√(2‖c‖)`, and a push depth `m` sending the loop past `4‖c‖ + 2`, the `dlog`-period of
`φ_c ∘ f_c^{[m]}` along the loop is exactly `2^m · windInt ℓ 0` — every such period is
divisible by `2^m` once the base winding is an integer multiple of `2πi`. -/
theorem period_push_bottcher {c : ℂ} (hc2 : (2:ℝ) ≤ ‖c‖) (ℓ : C1Loop)
    (hfar : ∀ θ, Real.sqrt (2 * ‖c‖) < ‖ℓ.γ θ‖) (m : ℕ)
    (hpush : ∀ θ : ℝ, 4 * ‖c‖ + 2 < ‖(quadratic c)^[m] (ℓ.γ θ)‖) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (bottcherCoord c ∘ (quadratic c)^[m]) (ℓ.γ θ) * ℓ.γ' θ)
      = 2 ^ m * windInt ℓ 0 := by
  have hc0 : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  apply period_push_eq_two_pow_windInt hc2 ℓ hfar m (analyticOnNhd_bottcherCoord_full c)
  · intro θ
    show max 2 ‖c‖ < ‖(quadratic c)^[m] (ℓ.γ θ)‖
    have h1 := hpush θ
    apply max_lt
    · linarith
    · linarith
  · intro θ
    exact bottcherCoord_ne_zero c _
  · intro θ
    set w : ℂ := (quadratic c)^[m] (ℓ.γ θ) with hwdef
    have h1 : 4 * ‖c‖ + 2 < ‖w‖ := hpush θ
    have hb := norm_bottcherCoord_sub_id_le (show ‖c‖ ≤ ‖w‖ by linarith)
      (show (2:ℝ) < ‖w‖ by linarith)
    have h2 : 4 * ‖c‖ / ‖w‖ < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith

end Bottcher

namespace Bottcher

/-- **The `2^m`-th root of the pushed second Böttcher coordinate on a section image.**  For a
tower section `S` (any first parameter) whose image is floored beyond `√(2‖c₂‖)` and pushed by
`f_{c₂}^{[m]}` past `4‖c₂‖ + 2`, the function `φ_{c₂} ∘ f_{c₂}^{[m]}` has an analytic
nonvanishing `2^m`-th root on the whole image `S.T '' annulus` — the unit winding of the section
(`S.wind`) turns the pushed period `2^m · 2πi` into exactly the dyadic divisibility that the
annulus root brick consumes. -/
theorem exists_pow_root_on_towerSection_image {c c₂ : ℂ} {rlo R₀ : ℝ}
    (S : TowerSection c rlo R₀) (hrlo : 1 < rlo) (hR : rlo < R₀)
    (hc2 : (2:ℝ) ≤ ‖c₂‖) (m : ℕ)
    (hfloor : ∀ w ∈ annulusSet rlo R₀, Real.sqrt (2 * ‖c₂‖) < ‖S.T w‖)
    (hpush : ∀ w ∈ annulusSet rlo R₀, 4 * ‖c₂‖ + 2 < ‖(quadratic c₂)^[m] (S.T w)‖) :
    ∃ Φ : ℂ → ℂ, AnalyticOnNhd ℂ Φ (S.T '' annulusSet rlo R₀) ∧
      (∀ z ∈ S.T '' annulusSet rlo R₀,
        Φ z ^ (2 ^ m) = bottcherCoord c₂ ((quadratic c₂)^[m] z)) ∧
      (∀ z ∈ S.T '' annulusSet rlo R₀, Φ z ≠ 0) := by
  classical
  have hrlo0 : (0:ℝ) < rlo := by linarith
  set ρ : ℝ := (rlo + R₀) / 2 with hρdef
  have hρ1 : rlo < ρ := by rw [hρdef]; linarith
  have hρ2 : ρ < R₀ := by rw [hρdef]; linarith
  have hρ0 : (0:ℝ) < ρ := by linarith
  have hcirc : ∀ θ : ℝ, circleMap 0 ρ θ ∈ annulusSet rlo R₀ := by
    intro θ
    have hnorm : ‖circleMap 0 ρ θ‖ = ρ := by
      simp [circleMap, Complex.norm_exp, abs_of_pos hρ0]
    exact ⟨by rw [hnorm]; exact hρ1, by rw [hnorm]; exact hρ2⟩
  -- the section circle as a loop, with unit winding
  set ℓ : C1Loop := sectionLoop S.an hcirc with hℓdef
  have hℓγ : ∀ θ, ℓ.γ θ = S.T (circleMap 0 ρ θ) := fun θ => rfl
  have hwind0 : windInt ℓ 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    have h1 := S.wind ρ hρ1 hρ2
    show (∫ θ in (0:ℝ)..(2 * Real.pi), (ℓ.γ θ - 0)⁻¹ * ℓ.γ' θ) = _
    rw [← h1]
    apply intervalIntegral.integral_congr
    intro θ _
    show (ℓ.γ θ - 0)⁻¹ * ℓ.γ' θ = _
    rw [sub_zero]
    rfl
  -- iterate analyticity
  have hquad_an : ∀ (j : ℕ) (z : ℂ), AnalyticAt ℂ ((quadratic c₂)^[j]) z := by
    intro j
    induction j with
    | zero => intro z; simpa using analyticAt_id
    | succ k ih =>
        intro z
        rw [show (quadratic c₂)^[k+1] = (quadratic c₂)^[k] ∘ quadratic c₂ from
          Function.iterate_succ _ _]
        have h2 : AnalyticAt ℂ (quadratic c₂) z := by
          unfold quadratic
          exact (analyticAt_id.pow 2).add analyticAt_const
        exact (ih (quadratic c₂ z)).comp h2
  -- the pushed function pulled back to the round annulus
  set G : ℂ → ℂ := fun w => bottcherCoord c₂ ((quadratic c₂)^[m] (S.T w)) with hGdef
  have hesc : ∀ w ∈ annulusSet rlo R₀, (quadratic c₂)^[m] (S.T w) ∈ escapeOpen c₂ := by
    intro w hw
    show max 2 ‖c₂‖ < ‖(quadratic c₂)^[m] (S.T w)‖
    have h1 := hpush w hw
    have h2 := norm_nonneg c₂
    apply max_lt
    · linarith
    · linarith
  have hG_an : AnalyticOnNhd ℂ G (annulusSet rlo R₀) := by
    intro w hw
    have h1 : AnalyticAt ℂ (bottcherCoord c₂) ((quadratic c₂)^[m] (S.T w)) :=
      analyticOnNhd_bottcherCoord_full c₂ _ (hesc w hw)
    exact (h1.comp (hquad_an m (S.T w))).comp (S.an w hw)
  have hG_ne : ∀ w ∈ annulusSet rlo R₀, G w ≠ 0 := fun w _ => bottcherCoord_ne_zero c₂ _
  -- core winding of the pullback: the pushed period at the section circle
  have hfarℓ : ∀ θ, Real.sqrt (2 * ‖c₂‖) < ‖ℓ.γ θ‖ := fun θ => hfloor _ (hcirc θ)
  have hpushℓ : ∀ θ : ℝ, 4 * ‖c₂‖ + 2 < ‖(quadratic c₂)^[m] (ℓ.γ θ)‖ :=
    fun θ => hpush _ (hcirc θ)
  have hperiod := period_push_bottcher hc2 ℓ hfarℓ m hpushℓ
  have hint : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      logDeriv G (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)
        = logDeriv (bottcherCoord c₂ ∘ (quadratic c₂)^[m]) (ℓ.γ θ) * ℓ.γ' θ := by
    intro θ _
    have hld : logDeriv G (circleMap 0 ρ θ)
        = logDeriv (bottcherCoord c₂ ∘ (quadratic c₂)^[m]) (S.T (circleMap 0 ρ θ))
          * _root_.deriv S.T (circleMap 0 ρ θ) := by
      have hcomp : G = (bottcherCoord c₂ ∘ (quadratic c₂)^[m]) ∘ S.T := rfl
      rw [hcomp]
      apply logDeriv_comp
      · exact ((analyticOnNhd_bottcherCoord_full c₂ _ (hesc _ (hcirc θ))).comp
          (hquad_an m _)).differentiableAt
      · exact (S.an _ (hcirc θ)).differentiableAt
    rw [hld]
    show _ = logDeriv (bottcherCoord c₂ ∘ (quadratic c₂)^[m]) (S.T (circleMap 0 ρ θ))
        * (_root_.deriv S.T (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
    ring
  have hcore : (∫ θ in (0:ℝ)..(2 * Real.pi),
      logDeriv G (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
      = ((2 ^ m * 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    calc (∫ θ in (0:ℝ)..(2 * Real.pi),
          logDeriv G (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            logDeriv (bottcherCoord c₂ ∘ (quadratic c₂)^[m]) (ℓ.γ θ) * ℓ.γ' θ :=
          intervalIntegral.integral_congr hint
      _ = 2 ^ m * windInt ℓ 0 := hperiod
      _ = ((2 ^ m * 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          rw [hwind0]
          push_cast
          ring
  obtain ⟨sroot, hs_an, hs_pow, hs_ne⟩ :=
    exists_pow_root_on_annulus hrlo0 hρ1 hρ2 hG_an hG_ne m 1 hcore
  refine ⟨fun z => sroot (S.inv z), ?_, ?_, ?_⟩
  · intro z hz
    have h1 : AnalyticAt ℂ sroot (S.inv z) := hs_an _ (S.inv_mem hz)
    exact h1.comp (S.inv_analytic z hz)
  · intro z hz
    have h1 := hs_pow (S.inv z) (S.inv_mem hz)
    have h2 : S.T (S.inv z) = z := S.inv_right hz
    calc sroot (S.inv z) ^ 2 ^ m = G (S.inv z) := h1
      _ = bottcherCoord c₂ ((quadratic c₂)^[m] z) := by
          rw [hGdef]
          simp only
          rw [h2]
  · intro z hz
    exact hs_ne _ (S.inv_mem hz)

end Bottcher


namespace Bottcher

section BiholoImage

variable {T : ℂ → ℂ} {r R : ℝ}

/-- Generic global inverse on an annulus image (junk off the image). -/
noncomputable def annulusInv (T : ℂ → ℂ) (r R : ℝ) : ℂ → ℂ :=
  Function.invFunOn T (annulusSet r R)

theorem annulusInv_left (hT_inj : Set.InjOn T (annulusSet r R))
    {w : ℂ} (hw : w ∈ annulusSet r R) : annulusInv T r R (T w) = w :=
  hT_inj.leftInvOn_invFunOn hw

theorem annulusInv_right {z : ℂ} (hz : z ∈ T '' annulusSet r R) :
    T (annulusInv T r R z) = z := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact Function.invFunOn_eq ⟨w, hw, rfl⟩

theorem annulusInv_mem {z : ℂ} (hz : z ∈ T '' annulusSet r R) :
    annulusInv T r R z ∈ annulusSet r R := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact Function.invFunOn_mem ⟨w, hw, rfl⟩

/-- **Generic analytic inverse on an annulus image** — the `SectionInverse` pattern with the
tower-section fields replaced by raw hypotheses. -/
theorem annulusInv_analytic (hT_an : AnalyticOnNhd ℂ T (annulusSet r R))
    (hT_inj : Set.InjOn T (annulusSet r R))
    (hT_dne : ∀ w ∈ annulusSet r R, _root_.deriv T w ≠ 0) :
    AnalyticOnNhd ℂ (annulusInv T r R) (T '' annulusSet r R) := by
  rintro z ⟨w₀, hw₀, rfl⟩
  have han : AnalyticAt ℂ T w₀ := hT_an w₀ hw₀
  have hsd : HasStrictDerivAt T (_root_.deriv T w₀) w₀ := han.hasStrictDerivAt
  have hd0 : _root_.deriv T w₀ ≠ 0 := hT_dne w₀ hw₀
  set ι : ℂ → ℂ := hsd.localInverse _ _ _ hd0 with hιdef
  have hι : AnalyticAt ℂ ι (T w₀) := han.analyticAt_localInverse hd0
  have hl : ∀ᶠ w in nhds w₀, ι (T w) = w := hsd.eventually_left_inverse hd0
  have hr : ∀ᶠ z in nhds (T w₀), T (ι z) = z := hsd.eventually_right_inverse hd0
  have hcont : ContinuousAt ι (T w₀) := hι.continuousAt
  have hι₀ : ι (T w₀) = w₀ := hl.self_of_nhds
  have hlocInA : ∀ᶠ z in nhds (T w₀), ι z ∈ annulusSet r R := by
    apply hcont.preimage_mem_nhds
    rw [hι₀]
    exact (isOpen_annulusSet _ _).mem_nhds hw₀
  have hagree : annulusInv T r R =ᶠ[nhds (T w₀)] ι := by
    filter_upwards [hlocInA, hr] with z hzA hzR
    have hex : ∃ a ∈ annulusSet r R, T a = z := ⟨ι z, hzA, hzR⟩
    have h1 : T (annulusInv T r R z) = z := Function.invFunOn_eq hex
    have h2 : annulusInv T r R z ∈ annulusSet r R := Function.invFunOn_mem hex
    exact hT_inj h2 hzA (by rw [h1, hzR])
  exact hι.congr hagree.symm

/-- **Dyadic root on a biholomorphic annulus image.**  If the pullback `g ∘ T` has core winding
`2πi·(2^k·m₀)` on the annulus, then `g` has an analytic nonvanishing `2^k`-th root on the whole
image `T '' annulus`. -/
theorem exists_pow_root_on_biholoImage (hr1 : 1 < r) (hrR : r < R)
    (hT_an : AnalyticOnNhd ℂ T (annulusSet r R)) (hT_inj : Set.InjOn T (annulusSet r R))
    (hT_dne : ∀ w ∈ annulusSet r R, _root_.deriv T w ≠ 0)
    {g : ℂ → ℂ} (hg_an : AnalyticOnNhd ℂ g (T '' annulusSet r R))
    (hg_ne : ∀ z ∈ T '' annulusSet r R, g z ≠ 0)
    (k : ℕ) (m₀ : ℤ)
    (hwind : (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (fun w => g (T w)) (circleMap 0 ((r + R) / 2) θ)
          * (circleMap 0 ((r + R) / 2) θ * Complex.I))
      = ((2 ^ k * m₀ : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) :
    ∃ Φ : ℂ → ℂ, AnalyticOnNhd ℂ Φ (T '' annulusSet r R) ∧
      (∀ z ∈ T '' annulusSet r R, Φ z ^ (2 ^ k) = g z) ∧
      (∀ z ∈ T '' annulusSet r R, Φ z ≠ 0) := by
  have hr0 : (0:ℝ) < r := by linarith
  have hρ1 : r < (r + R) / 2 := by linarith
  have hρ2 : (r + R) / 2 < R := by linarith
  have hG_an : AnalyticOnNhd ℂ (fun w => g (T w)) (annulusSet r R) := fun w hw =>
    (hg_an _ ⟨w, hw, rfl⟩).comp (hT_an w hw)
  have hG_ne : ∀ w ∈ annulusSet r R, g (T w) ≠ 0 := fun w hw => hg_ne _ ⟨w, hw, rfl⟩
  obtain ⟨sroot, hs_an, hs_pow, hs_ne⟩ :=
    exists_pow_root_on_annulus hr0 hρ1 hρ2 hG_an hG_ne k m₀ hwind
  refine ⟨fun z => sroot (annulusInv T r R z), ?_, ?_, ?_⟩
  · intro z hz
    exact (hs_an _ (annulusInv_mem hz)).comp
      (annulusInv_analytic hT_an hT_inj hT_dne z hz)
  · intro z hz
    have h1 := hs_pow (annulusInv T r R z) (annulusInv_mem hz)
    have h2 : T (annulusInv T r R z) = z := annulusInv_right hz
    calc sroot (annulusInv T r R z) ^ 2 ^ k = g (T (annulusInv T r R z)) := h1
      _ = g z := by rw [h2]
  · intro z hz
    exact hs_ne _ (annulusInv_mem hz)

end BiholoImage

end Bottcher

namespace Bottcher

section OpenImage

variable {T : ℂ → ℂ} {U : Set ℂ}

/-- Generic global inverse on an open image (junk off the image). -/
noncomputable def imageInv (T : ℂ → ℂ) (U : Set ℂ) : ℂ → ℂ :=
  Function.invFunOn T U

theorem imageInv_right {z : ℂ} (hz : z ∈ T '' U) : T (imageInv T U z) = z := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact Function.invFunOn_eq ⟨w, hw, rfl⟩

theorem imageInv_mem {z : ℂ} (hz : z ∈ T '' U) : imageInv T U z ∈ U := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact Function.invFunOn_mem ⟨w, hw, rfl⟩

/-- **Generic analytic inverse on an open injective image.** -/
theorem imageInv_analytic (hUo : IsOpen U) (hT_an : AnalyticOnNhd ℂ T U)
    (hT_inj : Set.InjOn T U)
    (hT_dne : ∀ w ∈ U, _root_.deriv T w ≠ 0) :
    AnalyticOnNhd ℂ (imageInv T U) (T '' U) := by
  rintro z ⟨w₀, hw₀, rfl⟩
  have han : AnalyticAt ℂ T w₀ := hT_an w₀ hw₀
  have hsd : HasStrictDerivAt T (_root_.deriv T w₀) w₀ := han.hasStrictDerivAt
  have hd0 : _root_.deriv T w₀ ≠ 0 := hT_dne w₀ hw₀
  set ι : ℂ → ℂ := hsd.localInverse _ _ _ hd0 with hιdef
  have hι : AnalyticAt ℂ ι (T w₀) := han.analyticAt_localInverse hd0
  have hl : ∀ᶠ w in nhds w₀, ι (T w) = w := hsd.eventually_left_inverse hd0
  have hr : ∀ᶠ z in nhds (T w₀), T (ι z) = z := hsd.eventually_right_inverse hd0
  have hcont : ContinuousAt ι (T w₀) := hι.continuousAt
  have hι₀ : ι (T w₀) = w₀ := hl.self_of_nhds
  have hlocInU : ∀ᶠ z in nhds (T w₀), ι z ∈ U := by
    apply hcont.preimage_mem_nhds
    rw [hι₀]
    exact hUo.mem_nhds hw₀
  have hagree : imageInv T U =ᶠ[nhds (T w₀)] ι := by
    filter_upwards [hlocInU, hr] with z hzU hzR
    have hex : ∃ a ∈ U, T a = z := ⟨ι z, hzU, hzR⟩
    have h1 : T (imageInv T U z) = z := Function.invFunOn_eq hex
    have h2 : imageInv T U z ∈ U := Function.invFunOn_mem hex
    exact hT_inj h2 hzU (by rw [h1, hzR])
  exact hι.congr hagree.symm

/-- **Dyadic root on a simply connected injective image.**  On the image of a simply connected
open set under an injective analytic map, every nonvanishing analytic `g` has an analytic
nonvanishing `2^k`-th root — pull back, take the simply-connected logarithm, exponentiate a
`2^k`-th of it, push forward.  This is the scaffold-piece root of the linear-gap glue. -/
theorem exists_pow_root_on_simplyConnImage (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    (hT_an : AnalyticOnNhd ℂ T U) (hT_inj : Set.InjOn T U)
    (hT_dne : ∀ w ∈ U, _root_.deriv T w ≠ 0)
    {g : ℂ → ℂ} (hg_an : AnalyticOnNhd ℂ g (T '' U))
    (hg_ne : ∀ z ∈ T '' U, g z ≠ 0) (k : ℕ) :
    ∃ Φ : ℂ → ℂ, AnalyticOnNhd ℂ Φ (T '' U) ∧
      (∀ z ∈ T '' U, Φ z ^ (2 ^ k) = g z) ∧
      (∀ z ∈ T '' U, Φ z ≠ 0) := by
  have hh_an : AnalyticOnNhd ℂ (fun w => g (T w)) U := fun w hw =>
    (hg_an _ ⟨w, hw, rfl⟩).comp (hT_an w hw)
  have hh_ne : ∀ w ∈ U, g (T w) ≠ 0 := fun w hw => hg_ne _ ⟨w, hw, rfl⟩
  obtain ⟨L, hLd, hLe⟩ := exists_differentiableOn_exp_eq hUsc hUo
    (fun w hw => ((hh_an w hw).differentiableAt).differentiableWithinAt)
    (by rintro ⟨w, hw, h0⟩; exact hh_ne w hw h0)
  have hL_an : AnalyticOnNhd ℂ L U := hLd.analyticOnNhd hUo
  set sroot : ℂ → ℂ := fun w => Complex.exp (L w / 2 ^ k) with hsdef
  have hexpan : AnalyticOnNhd ℂ Complex.exp univ :=
    Complex.differentiable_exp.differentiableOn.analyticOnNhd isOpen_univ
  have hs_an : AnalyticOnNhd ℂ sroot U := by
    intro w hw
    exact (hexpan _ (mem_univ _)).comp ((hL_an w hw).div analyticAt_const
      (pow_ne_zero _ two_ne_zero))
  have hs_pow : ∀ w ∈ U, sroot w ^ (2 ^ k) = g (T w) := by
    intro w hw
    rw [hsdef]
    simp only
    rw [← Complex.exp_nat_mul]
    have h1 : (2 ^ k : ℕ) * (L w / 2 ^ k) = L w := by
      have h2 : ((2:ℂ) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
      push_cast
      field_simp
    rw [h1]
    exact hLe hw
  refine ⟨fun z => sroot (imageInv T U z), ?_, ?_, ?_⟩
  · intro z hz
    exact (hs_an _ (imageInv_mem hz)).comp (imageInv_analytic hUo hT_an hT_inj hT_dne z hz)
  · intro z hz
    have h1 := hs_pow (imageInv T U z) (imageInv_mem hz)
    have h2 : T (imageInv T U z) = z := imageInv_right hz
    calc sroot (imageInv T U z) ^ 2 ^ k = g (T (imageInv T U z)) := h1
      _ = g z := by rw [h2]
  · intro z _
    exact Complex.exp_ne_zero _

end OpenImage

end Bottcher

namespace Bottcher

/-- **Consecutive scaffold overlaps are square-forced.**  If a depth-`(j+1)` scaffold point
coincides with a depth-`j` one, `σ_{j+1}(v) = σ_j(w)`, then `v = w²`: the Green levels force
`‖v‖ = ‖w‖²`, the iterate identities push both sides to the section, and the section's
functional equation plus injectivity identify the parameters.  This pins every consecutive
overlap `Pσ_j ∩ Pσ_{j+1}` as `σ_j''(sign-matching part of {w ∈ A : w² ∈ A})` — the input of
the root-glue chain. -/
theorem scaffold_overlap_forcing {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo)
    {ra RW α β : ℝ} (hra : rlo < ra) (hraRW : ra < RW) (hRWR : RW < R₀)
    {σ : ℕ → ℂ → ℂ} {j : ℕ}
    (hlevj : ∀ v ∈ arcAnnulus ra RW α β,
      greenFunctionDyn c (σ j v) = Real.log ‖v‖ / 2 ^ j)
    (hlevj1 : ∀ v ∈ arcAnnulus ra RW α β,
      greenFunctionDyn c (σ (j+1) v) = Real.log ‖v‖ / 2 ^ (j+1))
    (hitj : ∀ v ∈ arcAnnulus ra RW α β, (quadratic c)^[j] (σ j v) = S.T v)
    (hitj1 : ∀ v ∈ arcAnnulus ra RW α β, (quadratic c)^[j+1] (σ (j+1) v) = S.T v)
    {v w : ℂ} (hv : v ∈ arcAnnulus ra RW α β) (hw : w ∈ arcAnnulus ra RW α β)
    (heq : σ (j+1) v = σ j w) : v = w ^ 2 := by
  have hrapos : (0:ℝ) < ra := by linarith
  have hvn := arcAnnulus_subset α β hrapos hraRW hv
  have hwn := arcAnnulus_subset α β hrapos hraRW hw
  have hvpos : (0:ℝ) < ‖v‖ := lt_trans hrapos hvn.1
  have hwpos : (0:ℝ) < ‖w‖ := lt_trans hrapos hwn.1
  -- Green levels force the modulus relation `‖v‖ = ‖w‖²`
  have hglev : Real.log ‖v‖ / 2 ^ (j+1) = Real.log ‖w‖ / 2 ^ j := by
    rw [← hlevj1 v hv, ← hlevj w hw, heq]
  have hlog : Real.log ‖v‖ = 2 * Real.log ‖w‖ := by
    have h2j : (0:ℝ) < 2 ^ j := by positivity
    have h1 : Real.log ‖v‖ = Real.log ‖w‖ / 2 ^ j * 2 ^ (j+1) := by
      rw [← hglev]
      field_simp
    rw [h1, pow_succ]
    field_simp
  have hnorm : ‖v‖ = ‖w‖ ^ 2 := by
    calc ‖v‖ = Real.exp (Real.log ‖v‖) := (Real.exp_log hvpos).symm
      _ = Real.exp (2 * Real.log ‖w‖) := by rw [hlog]
      _ = Real.exp (Real.log ‖w‖) ^ 2 := by
          rw [← Real.exp_nat_mul]
          norm_num
      _ = ‖w‖ ^ 2 := by rw [Real.exp_log hwpos]
  -- push both sides to the section through the iterate identities
  have h1 : (quadratic c)^[j+1] (σ (j+1) v) = S.T v := hitj1 v hv
  rw [heq] at h1
  have h2 : (quadratic c)^[j+1] (σ j w) = quadratic c (S.T w) := by
    rw [Function.iterate_succ_apply', hitj w hw]
  have hkey : S.T v = quadratic c (S.T w) := by rw [← h1, h2]
  -- the section functional equation turns the image into `S.T (w²)`
  have hwann : w ∈ annulusSet rlo R₀ := ⟨lt_trans hra hwn.1, lt_trans hwn.2 hRWR⟩
  have hw2ann : w ^ 2 ∈ annulusSet rlo R₀ := by
    constructor
    · rw [norm_pow, ← hnorm]
      exact lt_trans hra hvn.1
    · rw [norm_pow, ← hnorm]
      exact lt_trans hvn.2 hRWR
  have hfe : S.T (w ^ 2) = (S.T w) ^ 2 + c := S.fe w hwann hw2ann
  have hkey2 : S.T v = S.T (w ^ 2) := by
    rw [hkey, hfe]
    show quadratic c (S.T w) = _
    rw [quadratic_apply]
  -- injectivity closes
  have hvann : v ∈ annulusSet rlo R₀ := ⟨lt_trans hra hvn.1, lt_trans hvn.2 hRWR⟩
  exact S.inj hvann hw2ann hkey2

end Bottcher

namespace Bottcher

/-- **The section–scaffold overlap is connected.**  With band surjectivity, the section image
is the exact Green shell, so membership of a depth-1 scaffold point in it is purely radial:
the overlap `P0 ∩ Pσ₁` equals `σ₁''(arcAnnulus with inner radius raised to e^{2·log rlo})` —
a connected set.  The first gluing step of the root chain is therefore unit-consistent. -/
theorem overlap_section_scaffold_connected {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo)
    {ra RW α β : ℝ} (hra : rlo < ra) (hraRW : ra < RW) (hRWR : RW < R₀) (hαβ : α < β)
    (hgap : Real.exp (2 * Real.log rlo) < RW)
    {σ1 : ℂ → ℂ}
    (han : AnalyticOnNhd ℂ σ1 (arcAnnulus ra RW α β))
    (hlev : ∀ v ∈ arcAnnulus ra RW α β,
      greenFunctionDyn c (σ1 v) = Real.log ‖v‖ / 2 ^ (1:ℕ))
    (hsurj : ∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
      greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀) :
    IsConnected (S.T '' annulusSet rlo R₀ ∩ σ1 '' arcAnnulus ra RW α β) := by
  have hrlo0 : (0:ℝ) < rlo := by linarith
  have hrapos : (0:ℝ) < ra := by linarith
  have hR₀1 : (1:ℝ) < R₀ := by nlinarith
  set s : ℝ := Real.exp (2 * Real.log rlo) with hsdef
  have hs0 : (0:ℝ) < s := Real.exp_pos _
  set r' : ℝ := max ra s with hr'def
  have hr'0 : (0:ℝ) < r' := lt_of_lt_of_le hrapos (le_max_left _ _)
  have hr'RW : r' < RW := max_lt hraRW hgap
  -- the raised arc is the exact parameter set of the overlap
  have hset : S.T '' annulusSet rlo R₀ ∩ σ1 '' arcAnnulus ra RW α β
      = σ1 '' arcAnnulus r' RW α β := by
    ext z
    constructor
    · rintro ⟨hzP0, v, hv, rfl⟩
      -- Green value of a section point is in the open band
      obtain ⟨u, hu, huT⟩ := hzP0
      have hG : greenFunctionDyn c (σ1 v) = Real.log ‖u‖ := by
        rw [← huT, S.level u hu]
      have hGlo : Real.log rlo < greenFunctionDyn c (σ1 v) := by
        rw [hG]
        exact Real.log_lt_log hrlo0 hu.1
      have hlevv := hlev v hv
      obtain ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩ := hv
      have hre : Real.log ‖Complex.exp ξ‖ = ξ.re := by
        rw [Complex.norm_exp, Real.log_exp]
      refine ⟨Complex.exp ξ, ⟨ξ, ⟨?_, h2, h3, h4⟩, rfl⟩, rfl⟩
      -- raised inner bound: log r' < ξ.re
      have h5 : 2 * Real.log rlo < ξ.re := by
        rw [hlevv, hre] at hGlo
        have h6 : (0:ℝ) < 2 ^ (1:ℕ) := by norm_num
        rw [lt_div_iff₀ h6] at hGlo
        norm_num at hGlo
        linarith
      have h7 : Real.log r' < ξ.re := by
        rw [hr'def]
        rcases max_cases ra s with ⟨hm, _⟩ | ⟨hm, _⟩
        · rw [hm]; exact h1
        · rw [hm, hsdef, Real.log_exp]; exact h5
      exact h7
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩ := hv
      have hre : Real.log ‖Complex.exp ξ‖ = ξ.re := by
        rw [Complex.norm_exp, Real.log_exp]
      have hmemA : Complex.exp ξ ∈ arcAnnulus ra RW α β := by
        refine ⟨ξ, ⟨?_, h2, h3, h4⟩, rfl⟩
        have h5 : Real.log ra ≤ Real.log r' :=
          Real.log_le_log hrapos (le_max_left _ _)
        linarith
      refine ⟨?_, Complex.exp ξ, hmemA, rfl⟩
      -- the Green band membership, then surjectivity
      have hlevv := hlev _ hmemA
      apply hsurj
      · rw [hlevv, hre]
        have h5 : Real.log s ≤ Real.log r' :=
          Real.log_le_log hs0 (le_max_right _ _)
        rw [hsdef, Real.log_exp] at h5
        have h6 : 2 * Real.log rlo < ξ.re := by linarith
        rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2 ^ (1:ℕ))]
        norm_num
        linarith
      · rw [hlevv, hre]
        have h5 : ξ.re < Real.log RW := h2
        have h6 : Real.log RW < Real.log R₀ := Real.log_lt_log (by linarith) hRWR
        have h7 : (0:ℝ) < Real.log R₀ := Real.log_pos hR₀1
        rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2 ^ (1:ℕ))]
        norm_num
        nlinarith
  rw [hset]
  exact (isConnected_arcAnnulus hr'0 hr'RW hαβ).image _
    ((han.mono (fun v hv => by
      obtain ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩ := hv
      refine ⟨ξ, ⟨?_, h2, h3, h4⟩, rfl⟩
      have h5 : Real.log ra ≤ Real.log r' := Real.log_le_log hrapos (le_max_left _ _)
      linarith)).continuousOn)

end Bottcher


namespace Bottcher

/-- **Green-band disjointness, generic form**: two sets confined to Green bands with separated
endpoints are disjoint. -/
theorem disjoint_of_green_bands {c : ℂ} {X Y : Set ℂ} {aX bX aY bY : ℝ}
    (hX : ∀ z ∈ X, aX < greenFunctionDyn c z ∧ greenFunctionDyn c z < bX)
    (hY : ∀ z ∈ Y, aY < greenFunctionDyn c z ∧ greenFunctionDyn c z < bY)
    (hsep : bY ≤ aX) : X ∩ Y = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hzX hzY
  have h1 := (hX z hzX).1
  have h2 := (hY z hzY).2
  linarith

/-- **Scaffold band separation**: non-consecutive scaffold levels have disjoint Green bands —
`log RW / 2^j ≤ log ra / 2^i` whenever `j ≥ i + 2`, for the working radii
(`log ra ≥ 5h/4`, `log RW ≤ 7h/2`).  The gluing chain is a path graph. -/
theorem green_band_separation {ra RW h : ℝ} (hra : 5 * h / 4 ≤ Real.log ra)
    (hRW : Real.log RW ≤ 7 * h / 2) (hRW0 : 0 ≤ Real.log RW) (hh : 0 < h)
    {i j : ℕ} (hij : i + 2 ≤ j) :
    Real.log RW / 2 ^ j ≤ Real.log ra / 2 ^ i := by
  have h2i : (0:ℝ) < 2 ^ i := by positivity
  have h4 : (4:ℝ) ≤ 2 ^ (j - i) := by
    calc (4:ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j - i) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
  have hkey : Real.log RW / 2 ^ (j - i) ≤ Real.log ra := by
    have h1 : Real.log RW / 2 ^ (j - i) ≤ Real.log RW / 4 :=
      div_le_div_of_nonneg_left hRW0 (by norm_num) h4
    linarith
  calc Real.log RW / 2 ^ j = Real.log RW / 2 ^ (j - i) / 2 ^ i := by
        rw [div_div, ← pow_add]
        congr 2
        omega
    _ ≤ Real.log ra / 2 ^ i := (div_le_div_iff_of_pos_right h2i).mpr hkey

/-- **Deep scaffold bands sit below the section**: `log RW / 2^j ≤ lr` for `j ≥ 2`, so only
the depth-1 scaffold piece meets the section image. -/
theorem green_band_separation_section {RW lr h : ℝ}
    (hRW : Real.log RW ≤ 7 * h / 2) (hRW0 : 0 ≤ Real.log RW)
    (hlr : h ≤ lr) (hh : 0 < h) {j : ℕ} (hj : 2 ≤ j) :
    Real.log RW / 2 ^ j ≤ lr := by
  have h4 : (4:ℝ) ≤ 2 ^ j := by
    calc (4:ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
  have h1 : Real.log RW / 2 ^ j ≤ Real.log RW / 4 :=
    div_le_div_of_nonneg_left hRW0 (by norm_num) h4
  linarith

end Bottcher

namespace Bottcher

/-- **Two `n`-th roots of the same function differ by a constant unit** on a preconnected open
set: the ratio is analytic with constant `n`-th power `1`, hence has vanishing derivative and is
constant.  This supplies the single overlap constant of the root-glue cocycle on every
connected overlap. -/
theorem exists_unit_of_pow_eq_pow {V : Set ℂ} (hVo : IsOpen V) (hVc : IsPreconnected V)
    {Φ Ψ : ℂ → ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hΦ : AnalyticOnNhd ℂ Φ V) (hΨ : AnalyticOnNhd ℂ Ψ V)
    (hΨne : ∀ z ∈ V, Ψ z ≠ 0)
    (hpow : ∀ z ∈ V, Φ z ^ n = Ψ z ^ n) :
    ∃ u : ℂ, u ^ n = 1 ∧ Set.EqOn Φ (fun z => u * Ψ z) V := by
  rcases V.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨1, one_pow n, fun z hz => absurd hz (by simp)⟩
  set r : ℂ → ℂ := fun z => Φ z / Ψ z with hrdef
  have hr_an : AnalyticOnNhd ℂ r V := fun z hz => (hΦ z hz).div (hΨ z hz) (hΨne z hz)
  have hrn : ∀ z ∈ V, r z ^ n = 1 := by
    intro z hz
    rw [hrdef]
    simp only
    rw [div_pow, hpow z hz, div_self (pow_ne_zero n (hΨne z hz))]
  have hrne : ∀ z ∈ V, r z ≠ 0 := by
    intro z hz h0
    have h1 := hrn z hz
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  -- the ratio has vanishing derivative
  have hr' : Set.EqOn (deriv r) 0 V := by
    intro z hz
    have hd : HasDerivAt r (deriv r z) z := (hr_an z hz).differentiableAt.hasDerivAt
    have hpowd : HasDerivAt (fun w => r w ^ n)
        ((n : ℂ) * r z ^ (n - 1) * deriv r z) z := hd.pow n
    have hconst : HasDerivAt (fun w => r w ^ n) 0 z := by
      have hev : (fun w => r w ^ n) =ᶠ[nhds z] (fun _ => (1:ℂ)) := by
        filter_upwards [hVo.mem_nhds hz] with w hw
        exact hrn w hw
      exact (hasDerivAt_const z (1:ℂ)).congr_of_eventuallyEq hev
    have heq : (n : ℂ) * r z ^ (n - 1) * deriv r z = 0 :=
      hpowd.unique hconst
    have hnne : (n : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hrpne : r z ^ (n - 1) ≠ 0 := pow_ne_zero _ (hrne z hz)
    have h2 : deriv r z = 0 := by
      rcases mul_eq_zero.mp heq with h3 | h3
      · exact absurd h3 (mul_ne_zero hnne hrpne)
      · exact h3
    exact h2
  -- constancy on the preconnected open set
  refine ⟨r z₀, hrn z₀ hz₀, ?_⟩
  intro z hz
  have hconst := hVo.is_const_of_deriv_eq_zero hVc
    (fun w hw => ((hr_an w hw).differentiableAt).differentiableWithinAt) hr' hz hz₀
  show Φ z = r z₀ * Ψ z
  rw [← hconst, hrdef]
  simp only
  rw [div_mul_cancel₀ _ (hΨne z hz)]

end Bottcher

namespace Bottcher

/-- **The conditional root-glue along a chain.**  A path family of open pieces (consecutive-only
overlaps, last-to-first empty), each carrying an analytic `N`-th root of a global nonvanishing
`g`, with every consecutive overlap NONEMPTY and PRECONNECTED (the named connectivity input),
glues to a single analytic `N`-th root of `g` on the union, normalized to agree with the root on
any distinguished piece.  The per-overlap units come from `exists_unit_of_pow_eq_pow`, the
assembly from `exists_global_lift_of_cyclic_cocycle`, and the root property survives because the
primitive constants have equal `N`-th powers along the connected chain. -/
theorem exists_pow_root_glue_of_chain {n : ℕ} (U : Fin (n + 1) → Set ℂ)
    (β : Fin (n + 1) → ℂ → ℂ) {g : ℂ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hUo : ∀ i, IsOpen (U i))
    (hg_ne : ∀ z ∈ ⋃ i, U i, g z ≠ 0)
    (hβ_an : ∀ i, AnalyticOnNhd ℂ (β i) (U i))
    (hβ_pow : ∀ i, ∀ z ∈ U i, β i z ^ N = g z)
    (hdisj : ∀ i j, (U i ∩ U j).Nonempty → (j = i ∨ j = i + 1 ∨ i = j + 1))
    (hlast : U (Fin.last n) ∩ U 0 = ∅)
    (hne : ∀ i : Fin (n + 1), i ≠ Fin.last n → (U i ∩ U (i + 1)).Nonempty)
    (hconn : ∀ i : Fin (n + 1), IsPreconnected (U i ∩ U (i + 1)))
    (i₀ : Fin (n + 1)) :
    ∃ Φ : ℂ → ℂ, AnalyticOnNhd ℂ Φ (⋃ i, U i) ∧
      (∀ z ∈ ⋃ i, U i, Φ z ^ N = g z) ∧
      (∀ z ∈ ⋃ i, U i, Φ z ≠ 0) ∧
      Set.EqOn Φ (β i₀) (U i₀) := by
  classical
  have hβ_ne : ∀ i, ∀ z ∈ U i, β i z ≠ 0 := by
    intro i z hz h0
    have h1 := hβ_pow i z hz
    rw [h0, zero_pow (by omega)] at h1
    exact hg_ne z (Set.mem_iUnion.mpr ⟨i, hz⟩) h1.symm
  -- per-overlap units from the ratio lemma
  have hunits : ∀ i : Fin (n + 1), ∃ u : ℂ, u ^ N = 1 ∧
      Set.EqOn (β i) (fun z => u * β (i + 1) z) (U i ∩ U (i + 1)) := by
    intro i
    apply exists_unit_of_pow_eq_pow ((hUo i).inter (hUo (i + 1))) (hconn i) hN
      ((hβ_an i).mono Set.inter_subset_left)
      ((hβ_an (i + 1)).mono Set.inter_subset_right)
      (fun z hz => hβ_ne (i + 1) z hz.2)
    intro z hz
    rw [hβ_pow i z hz.1, hβ_pow (i + 1) z hz.2]
  choose u₀ hu₀pow hu₀coc using hunits
  -- close the cocycle at the (empty) wrap-around overlap
  set u : Fin (n + 1) → ℂ := Function.update u₀ (Fin.last n)
    ((∏ j ∈ Finset.univ.erase (Fin.last n), u₀ j)⁻¹) with hudef
  have hu₀ne : ∀ i, u₀ i ≠ 0 := by
    intro i h0
    have h1 := hu₀pow i
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have huprodne : (∏ j ∈ Finset.univ.erase (Fin.last n), u₀ j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hu₀ne j)
  have hu_ne : ∀ i, u i ≠ 0 := by
    intro i
    rw [hudef]
    rcases eq_or_ne i (Fin.last n) with rfl | hi
    · rw [Function.update_self]
      exact inv_ne_zero huprodne
    · rw [Function.update_of_ne hi]
      exact hu₀ne i
  have hu_prod : ∏ i, u i = 1 := by
    rw [hudef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (Fin.last n)),
      Function.update_self]
    have h1 : ∀ j ∈ Finset.univ.erase (Fin.last n),
        Function.update u₀ (Fin.last n)
          ((∏ j ∈ Finset.univ.erase (Fin.last n), u₀ j)⁻¹) j = u₀ j := by
      intro j hj
      exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    rw [Finset.prod_congr rfl h1]
    exact mul_inv_cancel₀ huprodne
  have hu_coc : ∀ i, Set.EqOn (β i) (fun z => u i * β (i + 1) z) (U i ∩ U (i + 1)) := by
    intro i
    rcases eq_or_ne i (Fin.last n) with rfl | hi
    · intro z hz
      have h0 : (Fin.last n : Fin (n + 1)) + 1 = 0 := Fin.last_add_one n
      rw [h0, hlast] at hz
      exact absurd hz (by simp)
    · rw [hudef, Function.update_of_ne hi]
      exact hu₀coc i
  -- the abstract glue
  obtain ⟨F, c, hFan, hc0, hFeq, _⟩ :=
    exists_global_lift_of_cyclic_cocycle U β u hUo hβ_an hu_ne hu_prod hu_coc hdisj
  -- the primitive constants have equal `N`-th powers along the chain
  have hstep : ∀ i : Fin (n + 1), i ≠ Fin.last n → c i ^ N = c (i + 1) ^ N := by
    intro i hi
    obtain ⟨z, hz⟩ := hne i hi
    have h1 : F z = c i * β i z := hFeq i hz.1
    have h2 : F z = c (i + 1) * β (i + 1) z := hFeq (i + 1) hz.2
    have h3 : (c i * β i z) ^ N = (c (i + 1) * β (i + 1) z) ^ N := by rw [← h1, ← h2]
    rw [mul_pow, mul_pow, hβ_pow i z hz.1, hβ_pow (i + 1) z hz.2] at h3
    have h4 := hg_ne z (Set.mem_iUnion.mpr ⟨i, hz.1⟩)
    field_simp at h3
    exact h3
  have hallpow : ∀ i : Fin (n + 1), c i ^ N = c 0 ^ N := by
    have hval : ∀ v : ℕ, ∀ hv : v < n + 1, c ⟨v, hv⟩ ^ N = c 0 ^ N := by
      intro v
      induction v with
      | zero => intro hv; rfl
      | succ w ih =>
          intro hv
          have hwlt : w < n + 1 := by omega
          have hwne : (⟨w, hwlt⟩ : Fin (n + 1)) ≠ Fin.last n := by
            intro h
            have := congrArg Fin.val h
            simp only [Fin.last] at this
            omega
          have hlt : (⟨w, hwlt⟩ : Fin (n + 1)) < Fin.last n := by
            simp only [Fin.lt_def, Fin.val_last]
            omega
          have hsucc : (⟨w, hwlt⟩ : Fin (n + 1)) + 1 = ⟨w + 1, hv⟩ := by
            apply Fin.ext
            rw [Fin.val_add_one_of_lt hlt]
          rw [← hsucc, ← hstep ⟨w, hwlt⟩ hwne]
          exact ih hwlt
    intro i
    have h1 : i = ⟨i.val, i.isLt⟩ := by rfl
    rw [h1]
    exact hval i.val i.isLt
  -- normalize by the distinguished constant
  refine ⟨fun z => F z / c i₀, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ((hFan z hz).div analyticAt_const (hc0 i₀))
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    have h1 : F z = c i * β i z := hFeq i hi
    rw [div_pow, h1, mul_pow, hβ_pow i z hi, hallpow i, ← hallpow i₀,
      mul_comm, mul_div_assoc, div_self (pow_ne_zero N (hc0 i₀)), mul_one]
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    have h1 : F z = c i * β i z := hFeq i hi
    apply div_ne_zero _ (hc0 i₀)
    rw [h1]
    exact mul_ne_zero (hc0 i) (hβ_ne i z hi)
  · intro z hz
    have h1 : F z = c i₀ * β i₀ z := hFeq i₀ hz
    show F z / c i₀ = β i₀ z
    rw [h1, mul_comm, mul_div_assoc, div_self (hc0 i₀), mul_one]
end Bottcher

namespace Bottcher

/-- **Uniform push past any threshold.**  Beyond `√(2‖c‖) + 1` the quadratic expands norms by a
uniform factor `3/2`, so some fixed iterate carries the whole region past `4‖c‖ + 2` — the push
depth of the root construction, with no compactness needed. -/
theorem exists_uniform_push {c : ℂ} (hc : (2:ℝ) ≤ ‖c‖) {s : ℝ}
    (hs : Real.sqrt (2 * ‖c‖) + 1 ≤ s) :
    ∃ m : ℕ, ∀ z : ℂ, s ≤ ‖z‖ → 4 * ‖c‖ + 2 < ‖(quadratic c)^[m] z‖ := by
  set σ : ℝ := Real.sqrt (2 * ‖c‖) with hσdef
  have hσsq : σ ^ 2 = 2 * ‖c‖ := Real.sq_sqrt (by positivity)
  have hσ2 : (2:ℝ) ≤ σ := by
    have h1 : Real.sqrt 4 ≤ σ := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hs3 : (3:ℝ) ≤ s := by linarith
  -- one-step uniform expansion
  have hstep : ∀ z : ℂ, s ≤ ‖z‖ → (3/2) * ‖z‖ ≤ ‖quadratic c z‖ ∧ s ≤ ‖quadratic c z‖ := by
    intro z hz
    have hz3 : (3:ℝ) ≤ ‖z‖ := le_trans hs3 hz
    have hzσ : σ + 1 ≤ ‖z‖ := le_trans hs hz
    have h1 : ‖z ^ 2‖ ≤ ‖quadratic c z‖ + ‖c‖ := by
      have h2 : quadratic c z = z ^ 2 + c := rfl
      calc ‖z ^ 2‖ = ‖(z ^ 2 + c) + (-c)‖ := by ring_nf
        _ ≤ ‖z ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
        _ = ‖quadratic c z‖ + ‖c‖ := by rw [← h2, norm_neg]
    have h3 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic c z‖ := by
      rw [norm_pow] at h1
      linarith
    have h4 : ‖z‖ ^ 2 ≥ σ ^ 2 + 2 * σ + 1 := by nlinarith
    have h5 : (3/2) * ‖z‖ ≤ ‖quadratic c z‖ := by nlinarith
    exact ⟨h5, by nlinarith⟩
  -- iterated expansion
  have hiter : ∀ m : ℕ, ∀ z : ℂ, s ≤ ‖z‖ →
      (3/2) ^ m * s ≤ ‖(quadratic c)^[m] z‖ ∧ s ≤ ‖(quadratic c)^[m] z‖ := by
    intro m
    induction m with
    | zero =>
        intro z hz
        constructor
        · simpa using hz
        · simpa using hz
    | succ k ih =>
        intro z hz
        obtain ⟨h1, h2⟩ := ih z hz
        rw [Function.iterate_succ_apply']
        obtain ⟨h3, h4⟩ := hstep _ h2
        refine ⟨?_, h4⟩
        calc (3/2 : ℝ) ^ (k+1) * s = (3/2) * ((3/2) ^ k * s) := by ring
          _ ≤ (3/2) * ‖(quadratic c)^[k] z‖ :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ ≤ ‖quadratic c ((quadratic c)^[k] z)‖ := h3
  -- choose the depth
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((4 * ‖c‖ + 2) / s) (by norm_num : (1:ℝ) < 3/2)
  refine ⟨m, fun z hz => ?_⟩
  have h1 := (hiter m z hz).1
  have hspos : (0:ℝ) < s := by linarith
  have h2 : 4 * ‖c‖ + 2 < (3/2) ^ m * s := by
    rw [div_lt_iff₀ hspos] at hm
    linarith
  linarith

end Bottcher

namespace Bottcher

/-- **Two-piece root glue.**  Roots of the same nonvanishing `g` on two open pieces with
preconnected overlap glue to a root on the union agreeing with the first piece's root — the
inductive step of the chain assembly.  An empty overlap is allowed (unit `1`). -/
theorem glue_pow_root_pair {E Q : Set ℂ} (hEo : IsOpen E) (hQo : IsOpen Q)
    (hover_conn : IsPreconnected (E ∩ Q))
    {g Φ ψ : ℂ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hg_ne : ∀ z ∈ E ∪ Q, g z ≠ 0)
    (hΦ_an : AnalyticOnNhd ℂ Φ E) (hΦ_pow : ∀ z ∈ E, Φ z ^ N = g z)
    (hψ_an : AnalyticOnNhd ℂ ψ Q) (hψ_pow : ∀ z ∈ Q, ψ z ^ N = g z) :
    ∃ Φ' : ℂ → ℂ, AnalyticOnNhd ℂ Φ' (E ∪ Q) ∧ (∀ z ∈ E ∪ Q, Φ' z ^ N = g z) ∧
      (∀ z ∈ E ∪ Q, Φ' z ≠ 0) ∧ Set.EqOn Φ' Φ E := by
  classical
  have hψ_ne : ∀ z ∈ Q, ψ z ≠ 0 := by
    intro z hz h0
    have h1 := hψ_pow z hz
    rw [h0, zero_pow (by omega)] at h1
    exact hg_ne z (Set.mem_union_right E hz) h1.symm
  obtain ⟨u, huN, hueq⟩ := exists_unit_of_pow_eq_pow (hEo.inter hQo) hover_conn hN
    (hΦ_an.mono Set.inter_subset_left) (hψ_an.mono Set.inter_subset_right)
    (fun z hz => hψ_ne z hz.2)
    (fun z hz => by rw [hΦ_pow z hz.1, hψ_pow z hz.2])
  have hune : u ≠ 0 := by
    intro h0
    have h1 := huN
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  set Φ' : ℂ → ℂ := E.piecewise Φ (fun z => u * ψ z) with hΦ'def
  have hΦ'E : ∀ z ∈ E, Φ' z = Φ z := fun z hz => Set.piecewise_eq_of_mem E _ _ hz
  have hΦ'Q : ∀ z : ℂ, z ∉ E → Φ' z = u * ψ z := fun z hz =>
    Set.piecewise_eq_of_notMem E _ _ hz
  refine ⟨Φ', ?_, ?_, ?_, hΦ'E⟩
  · rintro z (hzE | hzQ)
    · apply (hΦ_an z hzE).congr
      filter_upwards [hEo.mem_nhds hzE] with w hw
      exact (hΦ'E w hw).symm
    · by_cases hzE : z ∈ E
      · apply (hΦ_an z hzE).congr
        filter_upwards [hEo.mem_nhds hzE] with w hw
        exact (hΦ'E w hw).symm
      · apply ((analyticOnNhd_const.mul hψ_an) z hzQ).congr
        filter_upwards [hQo.mem_nhds hzQ] with w hw
        by_cases hwE : w ∈ E
        · rw [hΦ'E w hwE]
          exact (hueq ⟨hwE, hw⟩).symm
        · exact (hΦ'Q w hwE).symm
  · rintro z (hzE | hzQ)
    · rw [hΦ'E z hzE]
      exact hΦ_pow z hzE
    · by_cases hzE : z ∈ E
      · rw [hΦ'E z hzE]
        exact hΦ_pow z hzE
      · rw [hΦ'Q z hzE, mul_pow, huN, one_mul]
        exact hψ_pow z hzQ
  · rintro z (hzE | hzQ)
    · rw [hΦ'E z hzE]
      intro h0
      have h1 := hΦ_pow z hzE
      rw [h0, zero_pow (by omega)] at h1
      exact hg_ne z (Set.mem_union_left Q hzE) h1.symm
    · by_cases hzE : z ∈ E
      · rw [hΦ'E z hzE]
        intro h0
        have h1 := hΦ_pow z hzE
        rw [h0, zero_pow (by omega)] at h1
        exact hg_ne z (Set.mem_union_left Q hzE) h1.symm
      · rw [hΦ'Q z hzE]
        exact mul_ne_zero hune (hψ_ne z hzQ)

end Bottcher

namespace Bottcher

/-- **Sequential root glue along a chain of pieces.**  Open pieces `V 0, …, V K`, each carrying
an analytic `N`-th root of a global nonvanishing `g`, glue to a single root on the union
agreeing with the root on `V 0`, provided each cumulative overlap
`(V 0 ∪ ⋯ ∪ V (j-1)) ∩ V j` is preconnected — the sequential form of the chain assembly,
consumed with the tower pieces in order (far region, section, scaffold levels, deep lobe). -/
theorem exists_pow_root_glue_of_seq {g : ℂ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (V : ℕ → Set ℂ) (β : ℕ → ℂ → ℂ) (K : ℕ)
    (hVo : ∀ i, i ≤ K → IsOpen (V i))
    (hg_ne : ∀ z ∈ ⋃ i ∈ Finset.range (K + 1), V i, g z ≠ 0)
    (hβ_an : ∀ i, i ≤ K → AnalyticOnNhd ℂ (β i) (V i))
    (hβ_pow : ∀ i, i ≤ K → ∀ z ∈ V i, β i z ^ N = g z)
    (hconn : ∀ j, j ≤ K →
      IsPreconnected ((⋃ i ∈ Finset.range j, V i) ∩ V j)) :
    ∃ Φ : ℂ → ℂ, AnalyticOnNhd ℂ Φ (⋃ i ∈ Finset.range (K + 1), V i) ∧
      (∀ z ∈ ⋃ i ∈ Finset.range (K + 1), V i, Φ z ^ N = g z) ∧
      (∀ z ∈ ⋃ i ∈ Finset.range (K + 1), V i, Φ z ≠ 0) ∧
      Set.EqOn Φ (β 0) (V 0) := by
  induction K with
  | zero =>
      have e1 : (0:ℕ) + 1 = 1 := rfl
      have h0 : (⋃ i ∈ Finset.range (0 + 1), V i) = V 0 := by
        rw [e1, Finset.range_one]
        simp
      rw [h0]
      have hg0 : ∀ z ∈ V 0, g z ≠ 0 := fun z hz => hg_ne z (h0.symm ▸ hz)
      refine ⟨β 0, hβ_an 0 le_rfl, hβ_pow 0 le_rfl, ?_, fun z _ => rfl⟩
      intro z hz hz0
      have h1 := hβ_pow 0 le_rfl z hz
      rw [hz0, zero_pow (by omega)] at h1
      exact hg0 z hz h1.symm
  | succ K ih =>
      have hsub : (⋃ i ∈ Finset.range (K + 1), V i)
          ⊆ ⋃ i ∈ Finset.range (K + 2), V i := by
        intro z hz
        rw [Set.mem_iUnion₂] at hz ⊢
        obtain ⟨i, hi, hzi⟩ := hz
        refine ⟨i, ?_, hzi⟩
        simp only [Finset.mem_range] at hi ⊢
        omega
      obtain ⟨Φ, hΦan, hΦpow, hΦne, hΦeq⟩ := ih
        (fun i hi => hVo i (by omega))
        (fun z hz => hg_ne z (hsub hz))
        (fun i hi => hβ_an i (by omega))
        (fun i hi => hβ_pow i (by omega))
        (fun j hj => hconn j (by omega))
      have hEo : IsOpen (⋃ i ∈ Finset.range (K + 1), V i) := by
        apply isOpen_biUnion
        intro i hi
        simp only [Finset.mem_coe, Finset.mem_range] at hi
        exact hVo i (by omega)
      have hsplit : (⋃ i ∈ Finset.range (K + 2), V i)
          = (⋃ i ∈ Finset.range (K + 1), V i) ∪ V (K + 1) := by
        have h2 : K + 2 = (K + 1) + 1 := by omega
        rw [h2, Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
      obtain ⟨Φ', hΦ'an, hΦ'pow, hΦ'ne, hΦ'eq⟩ :=
        glue_pow_root_pair hEo (hVo (K + 1) le_rfl) (hconn (K + 1) le_rfl) hN
          (fun z hz => hg_ne z (by rw [hsplit]; exact hz))
          hΦan hΦpow (hβ_an (K + 1) le_rfl) (hβ_pow (K + 1) le_rfl)
      rw [← hsplit] at hΦ'an hΦ'pow hΦ'ne
      refine ⟨Φ', hΦ'an, hΦ'pow, hΦ'ne, ?_⟩
      intro z hz
      have h1 : z ∈ ⋃ i ∈ Finset.range (K + 1), V i := by
        apply Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hz
      rw [hΦ'eq h1]
      exact hΦeq hz

end Bottcher

namespace Bottcher

/-- **The far region misses every Green-bounded piece**: a set with Green values `< L` is
disjoint from `{B < ‖z‖}` once `B` clears the far-Green threshold for `L` — the Afar-vs-deep
clause of the chain's consecutive-only overlap structure. -/
theorem disjoint_far_of_green_lt {c : ℂ} {X : Set ℂ} {L B : ℝ}
    (hX : ∀ z ∈ X, greenFunctionDyn c z < L)
    (hB : max (‖c‖ + 3) (Real.exp (L + 2)) ≤ B) :
    {z : ℂ | B < ‖z‖} ∩ X = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hzB hzX
  have h1 : L < greenFunctionDyn c z := by
    apply green_far_gt c L
    calc max (‖c‖ + 3) (Real.exp (L + 2)) ≤ B := hB
      _ < ‖z‖ := hzB
  have h2 := hX z hzX
  linarith

end Bottcher
