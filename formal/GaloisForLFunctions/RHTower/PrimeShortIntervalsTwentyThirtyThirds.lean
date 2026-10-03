import GaloisForLFunctions.RHTower.PrimeShortIntervalsFiveEighths
import GaloisForLFunctions.RHTower.ZetaZeroDensityThirtyThreeThirteenths
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRayleighFloor

/-!
# Prime mass in every window of length `x^α`, `α > 20/33`

The weighted zero sum `Σ_ρ x^{β-1} min(1, c x^{2u}/(|ρ||1-ρ|))` tends to `0` whenever a
zero-density estimate with exponent `A < 4` holds and `uA < 1`
(`tendsto_tsum_zeroShortWeight_of_density`): the dyadic majorant of `tsum_zeroShortWeight_le` and
the Route-T zero-free region need nothing else.  The density exponent `33/13` therefore gives
vanishing for `u < 13/33`.

The two-window lower bound turns vanishing at `u = 1 - α` into `ψ(x + x^α/2) - ψ(x) ≥ (5/8)(x^α/2)`
(`eventually_psi_short_window_of_tendsto`); for `α > 1/2` the prime powers cost only
`2√x log x`, so `θ(x + x^α/2) - θ(x) ≥ x^α/4` (`eventually_theta_short_window_of_tendsto`), and
chaining the windows gives, for every `20/33 < α < 1`,

`θ(y + L) - θ(y) ≥ (L - (y + L)^α)/2`   (`y ≥ X`, `L ≥ 0`).
-/

namespace RHTower

noncomputable section

open Filter Topology RHTower.Sieve

/-- **The weighted zero sum vanishes under any density exponent `A < 4` with `uA < 1`.** -/
theorem tendsto_tsum_zeroShortWeight_of_density {A u c D T₀d : ℝ} {B : ℕ} (hA0 : 0 ≤ A)
    (hA4 : A < 4) (hu : 0 < u) (hu2 : u ≤ 1 / 2) (huA : u * A < 1) (hc : 1 ≤ c) (hD : 0 ≤ D)
    (hdens : ∀ T : ℝ, T₀d ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ))) :
    Tendsto (fun x : ℝ => ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨Ap, T₁, hT₁, hfree⟩ := exists_zeroHeightBox_zeroFree
  have hδ : 0 < 1 - u * A := by linarith
  set δ := 1 - u * A with hδdef
  set c₁ : ℝ := 2 - A / 2 with hc₁
  have hc₁0 : 0 < c₁ := by rw [hc₁]; linarith
  set T₀ : ℝ := max (max T₀d T₁) 1 with hT₀
  have hT₀1 : 1 ≤ T₀ := le_max_right _ _
  set w : ℝ → ℝ := fun T => routeTWidthPolylogLower Ap (4 * T / 3) with hw
  set P : ℝ := (1 + (B + 1) / (c₁ / 4)) ^ B with hP
  have hPb : ∀ T : ℝ, 1 ≤ T → (1 + Real.log T) ^ B ≤ P * T ^ (c₁ / 4) :=
    fun T hT => one_add_log_pow_le_rpow B (by positivity) hT
  have hdens' : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ)) :=
    fun T hT σ h1 h2 => hdens T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT) σ h1 h2
  have hfree' : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, (zeroHeightBox σ T).Nonempty → σ ≤ 1 - w T :=
    fun T hT σ hN => hfree T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT) σ hN
  have hw0 : ∀ T : ℝ, 0 ≤ w T := fun T => (routeTWidthPolylogLower_pos Ap _).le
  have hwanti : ∀ T T' : ℝ, T₀ ≤ T → T ≤ T' → w T' ≤ w T := by
    intro T T' hT hTT'
    have hT0 : 0 ≤ T := by linarith
    refine routeTWidthPolylogLower_antitone ?_
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  set Low := (finite_xiOrdinateWindow T₀ 0).toFinset with hLow
  set C : ℝ := 10 * routeTZeroFreeDeltaEnvelopeConstant Ap with hC
  have hC0 : 0 < C := by
    rw [hC]
    have := routeTZeroFreeDeltaEnvelopeConstant_pos Ap
    positivity
  set κ : ℝ := δ / (4 * C) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  set G : ℝ := 1 / (1 - (2 : ℝ) ^ (-(c₁ / 8))) with hG
  set H₁ : ℝ → ℝ := fun x => (1 + Real.log (x ^ (2 * u)) / Real.log 2)
      * (1 + Real.log (x ^ (2 * u))) ^ B * x ^ (-(δ * w (x ^ (2 * u)))) with hH₁
  set U : ℝ → ℝ := fun x => ∑ q ∈ Low, x ^ ((q.1 : ℂ).re - 1)
      + 8 * c * D * ((Real.log x + 2) * H₁ x)
      + 8 * c * D * P * G * ((Real.log x + 2) * x ^ (-(u * c₁ / 4))) with hU
  -- the majorant tends to zero
  have hLowT : Tendsto (fun x : ℝ => ∑ q ∈ Low, x ^ ((q.1 : ℂ).re - 1)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Low (f := fun (q : XiZeroCopy) (x : ℝ) => x ^ ((q.1 : ℂ).re - 1))
      (a := fun _ => (0 : ℝ)) (x := atTop) (fun q _ => by
        have hpos : 0 < 1 - (q.1 : ℂ).re := by linarith [xiZeroCopy_re_lt_one q]
        have := tendsto_rpow_neg_atTop hpos
        refine this.congr fun x => ?_
        congr 1
        ring)
    simpa using h
  have hmidT : Tendsto (fun x : ℝ => (Real.log x + 2) * H₁ x) atTop (𝓝 0) := by
    have hcomp := (tendsto_pow_mul_exp_neg_log_ratio (B + 2) hκ0).comp Real.tendsto_log_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hL := Real.log_nonneg hx
      have hX1 : 1 ≤ x ^ (2 * u) := Real.one_le_rpow hx (by linarith)
      have hlX := Real.log_nonneg hX1
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      rw [hH₁]
      dsimp only
      have : 0 ≤ x ^ (-(δ * w (x ^ (2 * u)))) := Real.rpow_nonneg (by linarith) _
      positivity
    · filter_upwards [eventually_ge_atTop (Real.exp 12)] with x hx
      have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 12) hx
      have hL12 : 12 ≤ Real.log x := by
        rw [Real.le_log_iff_exp_le hx0]
        exact hx
      have hx1 : 1 ≤ x := by
        have := Real.add_one_le_exp 12
        linarith
      set L := Real.log x with hLdef
      have hlogX : Real.log (x ^ (2 * u)) = 2 * u * L := by rw [Real.log_rpow hx0]
      have hwid := rpow_neg_width_le_exp (A := Ap) hx1 (by linarith) hu.le hu2 hδ.le
      rw [← hC, ← hκ, ← hLdef] at hwid
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      have hf1 : L + 2 ≤ 3 * L := by linarith
      have hf2 : 1 + Real.log (x ^ (2 * u)) / Real.log 2 ≤ 3 * L := by
        rw [hlogX]
        have : 2 * u * L / Real.log 2 ≤ 2 * L := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        linarith
      have hf3 : 1 + Real.log (x ^ (2 * u)) ≤ 3 * L := by rw [hlogX]; nlinarith
      have hf3' : 0 ≤ 1 + Real.log (x ^ (2 * u)) := by rw [hlogX]; positivity
      have hf2' : 0 ≤ 1 + Real.log (x ^ (2 * u)) / Real.log 2 := by
        rw [hlogX]
        have : 0 ≤ 2 * u * L / Real.log 2 := by positivity
        linarith
      have hE0 : 0 ≤ x ^ (-(δ * w (x ^ (2 * u)))) := Real.rpow_nonneg hx0.le _
      have hwx : w (x ^ (2 * u)) = routeTWidthPolylogLower Ap (4 * x ^ (2 * u) / 3) := rfl
      rw [hH₁]
      dsimp only
      rw [hwx] at hE0 ⊢
      calc (L + 2) * ((1 + Real.log (x ^ (2 * u)) / Real.log 2) * (1 + Real.log (x ^ (2 * u))) ^ B
            * x ^ (-(δ * routeTWidthPolylogLower Ap (4 * x ^ (2 * u) / 3))))
          ≤ (3 * L) * ((3 * L) * (3 * L) ^ B
            * Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2))) := by
            gcongr
        _ = (3 * L) ^ (B + 2)
              * Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2)) := by
            ring
  have htailT : Tendsto (fun x : ℝ => (Real.log x + 2) * x ^ (-(u * c₁ / 4))) atTop (𝓝 0) :=
    tendsto_log_add_two_mul_rpow_neg (by positivity)
  have hUT : Tendsto U atTop (𝓝 0) := by
    have h := (hLowT.add (hmidT.const_mul (8 * c * D))).add (htailT.const_mul (8 * c * D * P * G))
    simpa [hU] using h
  -- squeeze
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUT ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact tsum_nonneg fun q => zeroShortWeight_nonneg (by linarith)
      (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)) _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hmaj := tsum_zeroShortWeight_le w hx hu.le hA0 hA4 hδ.le hc hD hT₀1 hPb hdens' hfree'
      hw0 hwanti
    refine le_trans hmaj ?_
    have h4 := four_mul_ceil_rpow_le hx
    have hL := Real.log_nonneg hx
    have hX1 : 1 ≤ x ^ (2 * u) := Real.one_le_rpow hx (by linarith)
    have hlX := Real.log_nonneg hX1
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hG0 : 0 ≤ G := by
      rw [hG]
      have : (2 : ℝ) ^ (-(c₁ / 8)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have : 0 < 1 - (2 : ℝ) ^ (-(c₁ / 8)) := by linarith
      positivity
    have hP0 : 0 ≤ P := by
      rw [hP]
      positivity
    have hbr : 0 ≤ c * D * (H₁ x + P * x ^ (-(u * c₁ / 4)) * G) := by
      rw [hH₁]
      dsimp only
      have : 0 ≤ x ^ (-(δ * w (x ^ (2 * u)))) := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ x ^ (-(u * c₁ / 4)) := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ c := by linarith
      positivity
    exact majorant_rearrange_le hbr h4

/-- **The weighted zero sum vanishes below the exponent `13/33`.** -/
theorem tendsto_tsum_zeroShortWeight_thirtyThree_thirteenths {u c : ℝ} (hu : 0 < u)
    (hu' : u < 13 / 33) (hc : 1 ≤ c) :
    Tendsto (fun x : ℝ => ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨D, hD, T₀, -, hdens⟩ := exists_zeroHeightBox_ncard_le_thirtyThree_thirteenths
  exact tendsto_tsum_zeroShortWeight_of_density (by norm_num) (by norm_num) hu (by linarith)
    (by linarith) hc hD hdens

/-- **Short `ψ` windows from vanishing.**  If the weighted zero sum at `u = 1 - α`, `c = 512` tends
to `0`, then `ψ(x + x^α/2) - ψ(x) ≥ (5/8)(x^α/2)` for all large `x`. -/
theorem eventually_psi_short_window_of_tendsto {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hzero : Tendsto (fun x : ℝ =>
      ∑' q : XiZeroCopy, zeroShortWeight x (512 * x ^ (2 * (1 - α))) (q.1 : ℂ)) atTop (𝓝 0)) :
    ∀ᶠ x : ℝ in atTop, (5 / 8) * (x ^ α / 2)
      ≤ Chebyshev.psi (x + x ^ α / 2) - Chebyshev.psi x := by
  have hsmall := hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hdecay : Tendsto (fun x : ℝ => x ^ (-(1 + 2 * α))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hdec := hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4096))
  filter_upwards [hsmall, hdec, eventually_ge_atTop (2 : ℝ)] with x hS hd hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set h := x ^ α / 2 with hh
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hh0 : 0 < h := by rw [hh]; positivity
  have hhx : h ≤ x := by
    rw [hh]
    have : x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hα1.le
    rw [Real.rpow_one] at this
    linarith
  have hmain := psi_window_ge_sub_zeroShortWeight (h := h) (h' := h / 16) hx (by positivity)
    (by linarith) hhx
  have hY : 8 * x ^ 2 / (h * (h / 16)) = 512 * x ^ (2 * (1 - α)) := by
    have e1 : x ^ (2 * (1 - α)) = x ^ 2 / (x ^ α * x ^ α) := by
      rw [show 2 * (1 - α) = (2 : ℝ) - (α + α) by ring, Real.rpow_sub hx0, Real.rpow_add hx0,
        Real.rpow_two]
    rw [e1, hh]
    field_simp
    ring
  rw [hY] at hmain
  -- the trivial-zero term
  have htriv : 4 / (x * (h / 16)) ≤ h / 16 := by
    have hpow : x ^ (-(1 + 2 * α)) = 1 / (x * x ^ α * x ^ α) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_add hx0, Real.rpow_one, Real.rpow_mul hx0.le]
      rw [show (x ^ (2 : ℝ)) ^ α = x ^ α * x ^ α by
        rw [← Real.rpow_mul hx0.le, mul_comm, Real.rpow_mul hx0.le, Real.rpow_two]; ring]
      rw [inv_eq_one_div]
      ring
    rw [hpow, div_lt_iff₀ (by positivity)] at hd
    rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]
    have e : x ^ α / 2 * (x * (x ^ α / 2 / 16)) = (x * x ^ α * x ^ α) / 64 := by ring
    rw [e]
    linarith
  have hzs : 2 * h * ∑' q : XiZeroCopy, zeroShortWeight x (512 * x ^ (2 * (1 - α))) (q.1 : ℂ)
      ≤ h / 8 := by
    have := hS.le
    nlinarith
  linarith

/-- **Short `θ` windows from vanishing.**  For `1/2 < α < 1`, vanishing of the weighted zero sum at
`u = 1 - α`, `c = 512` gives `θ(x + x^α/2) - θ(x) ≥ x^α/4` for all large `x`. -/
theorem eventually_theta_short_window_of_tendsto {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1)
    (hzero : Tendsto (fun x : ℝ =>
      ∑' q : XiZeroCopy, zeroShortWeight x (512 * x ^ (2 * (1 - α))) (q.1 : ℂ)) atTop (𝓝 0)) :
    ∀ᶠ x : ℝ in atTop, x ^ α / 2 / 2 ≤ Chebyshev.theta (x + x ^ α / 2) - Chebyshev.theta x := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by linarith : (0 : ℝ) < α - 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 256)
  filter_upwards [eventually_psi_short_window_of_tendsto (by linarith) hα1 hzero, hlo,
    eventually_ge_atTop (2 : ℝ)]
    with x hψ hlog hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set h := x ^ α / 2 with hh
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hhx : h ≤ x := by
    rw [hh]
    have : x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hα1.le
    rw [Real.rpow_one] at this
    linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlogx,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hlog
  -- prime powers
  have hpt := Chebyshev.psi_sub_theta_le (x := x + h) (by linarith)
  have htp := Chebyshev.theta_le_psi x
  have hsqrt : √(x + h) ≤ 2 * x ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc (x + h) ^ (1 / 2 : ℝ) ≤ (4 * x) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 * x ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hx0.le]
          congr 1
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hlog2 : Real.log (x + h) ≤ 2 * Real.log x := by
    have h1 : Real.log (x + h) ≤ Real.log (x * x) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_mul hx0.ne' hx0.ne'] at h1
    linarith
  have hsplit : x ^ α = x ^ (1 / 2 : ℝ) * x ^ (α - 1 / 2) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hpp : 2 * √(x + h) * Real.log (x + h) ≤ h / 8 := by
    have hl0 : 0 ≤ Real.log (x + h) := Real.log_nonneg (by linarith)
    have hsq0 : 0 ≤ √(x + h) := Real.sqrt_nonneg _
    calc 2 * √(x + h) * Real.log (x + h) ≤ 2 * (2 * x ^ (1 / 2 : ℝ)) * (2 * Real.log x) := by
          gcongr
      _ = 8 * (x ^ (1 / 2 : ℝ) * Real.log x) := by ring
      _ ≤ 8 * (x ^ (1 / 2 : ℝ) * (1 / 256 * x ^ (α - 1 / 2))) := by gcongr
      _ = h / 16 := by rw [hh, hsplit]; ring
      _ ≤ h / 8 := by
          have : 0 < h := by rw [hh]; positivity
          linarith
  linarith

/-- **Prime mass in every short window, exponent `20/33`.**  For every `20/33 < α < 1` there is
`X ≥ 1` with `θ(y + L) - θ(y) ≥ (L - (y + L)^α)/2` for all `y ≥ X` and `L ≥ 0`. -/
theorem exists_theta_window_lower_twenty_thirtyThirds {α : ℝ} (hα : 20 / 33 < α) (hα1 : α < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y := by
  have hzero := tendsto_tsum_zeroShortWeight_thirtyThree_thirteenths (u := 1 - α) (c := 512)
    (by linarith) (by linarith) (by norm_num)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1
    (eventually_theta_short_window_of_tendsto (by linarith) hα1 hzero)
  refine ⟨max X₀ 1, le_max_right _ _, ?_⟩
  exact theta_window_lower_of_step (by linarith) (by norm_num) (le_max_right _ _)
    (fun z hz => hX₀ z (le_trans (le_max_left _ _) hz))

/-- **A prime in every short interval, exponent `20/33`.**  For every `20/33 < α < 1`, every large
`x` has a prime in `(x, x + x^α]`. -/
theorem eventually_exists_prime_short_interval_twenty_thirtyThirds {α : ℝ} (hα : 20 / 33 < α)
    (hα1 : α < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ α := by
  set α' : ℝ := (20 / 33 + α) / 2 with hα'
  have hα'1 : 20 / 33 < α' := by rw [hα']; linarith
  have hα'2 : α' < α := by rw [hα']; linarith
  obtain ⟨X, hX1, hX⟩ := exists_theta_window_lower_twenty_thirtyThirds hα'1 (by linarith)
  have hgap : ∀ᶠ x : ℝ in atTop, 2 * x ^ α' < x ^ α := by
    filter_upwards [(tendsto_rpow_atTop (show 0 < α - α' by linarith)).eventually_gt_atTop 2,
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hsplit : x ^ α = x ^ α' * x ^ (α - α') := by rw [← Real.rpow_add hx0]; ring_nf
    rw [hsplit]
    have hpos : 0 < x ^ α' := Real.rpow_pos_of_pos hx0 _
    nlinarith
  filter_upwards [hgap, eventually_ge_atTop X] with x hgx hxX
  have hx1 : 1 ≤ x := le_trans hX1 hxX
  have hx0 : 0 < x := by linarith
  have hxa0 : 0 ≤ x ^ α := Real.rpow_nonneg hx0.le _
  have hle : x ^ α ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 hα1.le
    rwa [Real.rpow_one] at this
  have hθ := hX x (x ^ α) hxX hxa0
  have h2 : (2 : ℝ) ^ α' ≤ 2 := by
    calc (2 : ℝ) ^ α' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hpow : (x + x ^ α) ^ α' ≤ 2 * x ^ α' := by
    calc (x + x ^ α) ^ α' ≤ (2 * x) ^ α' :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = 2 ^ α' * x ^ α' := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ α' := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
  have hpos : 0 < Chebyshev.theta (x + x ^ α) - Chebyshev.theta x := by linarith
  rw [Sieve.theta_sub_eq_sum_Ioc (by linarith)] at hpos
  obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨p, hp.2, ?_, ?_⟩
  · have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
    linarith [Nat.lt_floor_add_one x]
  · have h1 : (p : ℝ) ≤ (⌊x + x ^ α⌋₊ : ℝ) := by exact_mod_cast hp.1.2
    linarith [Nat.floor_le (show 0 ≤ x + x ^ α by linarith)]

end

end RHTower
