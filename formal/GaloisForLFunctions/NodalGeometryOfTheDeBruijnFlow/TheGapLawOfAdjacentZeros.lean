import GaloisForLFunctions.RHTower.Heat.HeatLocalizedEnergyEvolution

/-!
# The gap law of adjacent zeros

Along any path of zeros of the flow, a simple zero moves at the velocity `V = H″/H′`
(`hasDerivAt_zero_path`). At large height the packet of zeros in a unit window separates off an exterior field `Q`
with `‖Q′‖ ≪ log X`, and the velocity is the local Dyson force `2(Σ_b m_b/(z − b) + Q(z))`. For two real simple zeros
`x < x'`, with `g = x' − x`, this gives the exact local gap law (`gap_rate_eq`)

`g (V(x') − V(x)) = 4 − 2g² Σ_b m_b/((x' − b)(x − b)) + 2g (Q(x') − Q(x))`,

so that `d(g²)/dt = 8 − g² S + O(g² log X)`, with `S` the compression of the other zeros. Each term of `S` has
nonnegative real part as soon as `b` lies outside the Jensen disc of the pair (`re_inv_mul_nonneg`): its centre is the
midpoint and its radius `√(h² + (Im b)²)`, `h = g/2`. So gaps cannot open faster than `8` per unit of time
(`gap_sq_le_of_paths`), and a pair born at a simple collision at `t₀` has `g² ≤ 8(t − t₀)(1 + o(1))`
(`gap_sq_le_of_collision`).
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The velocity of a zero -/

/-- The zero velocity `H″/H′`. -/
def zeroVelocity (t : ℝ) (z : ℂ) : ℂ := deriv (deriv (riemannHeat t)) z / deriv (riemannHeat t) z

/-- **The velocity of a zero along a path.** A continuous path of zeros through a simple zero moves at the velocity
`H″/H′`, in both time directions. -/
theorem hasDerivAt_zero_path {s₀ : ℝ} (hs₀ : 0 < s₀) {z₀ : ℂ} (hz : riemannHeat s₀ z₀ = 0)
    (hd : deriv (riemannHeat s₀) z₀ ≠ 0) {y : ℝ → ℂ} (hy0 : y s₀ = z₀) (hyc : ContinuousAt y s₀)
    (hyz : ∀ᶠ s in 𝓝 s₀, riemannHeat s (y s) = 0) : HasDerivAt y (zeroVelocity s₀ z₀) s₀ := by
  set a := deriv (riemannHeat s₀) z₀ with ha
  set b := deriv (deriv (riemannHeat s₀)) z₀ with hb
  set c₀ := |z₀.im| + 1 with hc₀
  set M := ∫ x, |x| ^ 2 * ‖heatWeight s₀ x‖ * Real.exp ((|z₀.im| + 1) * |x|) with hM
  set L := ∫ x, |x| ^ 3 * ‖heatWeight s₀ x‖ * Real.exp ((|z₀.im| + 1) * |x|) with hL
  set K := ∫ x, |x| ^ 4 * ‖heatWeight (s₀ + 1) x‖ * Real.exp (c₀ * |x|) with hK
  have hM0 : 0 ≤ M := integral_nonneg fun x => by positivity
  have hL0 : 0 ≤ L := integral_nonneg fun x => by positivity
  have hK0 : 0 ≤ K := integral_nonneg fun x => by positivity
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr hd
  set D := 2 * (‖b‖ + K) / ‖a‖ with hD
  have hD0 : 0 ≤ D := by positivity
  set C := (M * D ^ 2 + L * D + K) / ‖a‖ with hC
  have hC0 : 0 ≤ C := by positivity
  -- smallness of the displacement and of the time step
  have hyt : Tendsto (fun s => ‖y s - z₀‖) (𝓝 s₀) (𝓝 0) := by
    have := (hyc.tendsto.sub_const z₀).norm
    simpa [hy0] using this
  have hsmallΔ : ∀ᶠ s in 𝓝 s₀, ‖y s - z₀‖ < min 1 (‖a‖ / (4 * (M + 1))) :=
    hyt.eventually (gt_mem_nhds (lt_min one_pos (by positivity)))
  have hsmallh : ∀ᶠ s in 𝓝 s₀, |s - s₀| < min (min 1 s₀) (‖a‖ / (4 * (L + 1))) := by
    have : Tendsto (fun s : ℝ => |s - s₀|) (𝓝 s₀) (𝓝 0) := by
      have := (continuous_id.sub (continuous_const (y := s₀))).abs.tendsto s₀
      simpa using this
    exact this.eventually (gt_mem_nhds (lt_min (lt_min one_pos hs₀) (by positivity)))
  -- the quadratic bound
  have hquad : ∀ᶠ s in 𝓝 s₀, ‖y s - z₀ - (s - s₀) • (b / a)‖ ≤ C * (s - s₀) ^ 2 := by
    filter_upwards [hyz, hsmallΔ, hsmallh] with s hzero hΔ hh
    set h := s - s₀ with hhdef
    set z := y s with hzdef
    set Δ := z - z₀ with hΔdef
    have hΔ1 : ‖Δ‖ ≤ 1 := (hΔ.trans_le (min_le_left _ _)).le
    have hh1 : |h| ≤ 1 := (hh.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
    have hhs : -s₀ ≤ h := by
      have := hh.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      linarith only [(abs_lt.mp this).1]
    have hzim : |z.im| ≤ c₀ := by
      have h1 : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h1
      have h2 := abs_sub_abs_le_abs_sub z.im z₀.im
      rw [hc₀]
      linarith only [h1, h2, hΔ1]
    have hsum : s₀ + h = s := by rw [hhdef]; ring
    -- the time expansion, in both directions
    have hE : ‖riemannHeat s z - riemannHeat s₀ z + (h : ℂ) * deriv (deriv (riemannHeat s₀)) z‖ ≤
        K * h ^ 2 := by
      have h2 := norm_riemannHeat_time_taylor_le hs₀.le (by linarith only [hhs]) hh1 2 z
      rw [hsum] at h2
      have hsumrange : ∑ m ∈ Finset.range 2, (-h : ℂ) ^ m / m.factorial *
          iteratedDeriv (2 * m) (riemannHeat s₀) z =
          riemannHeat s₀ z - (h : ℂ) * deriv (deriv (riemannHeat s₀)) z := by
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        have h20 : iteratedDeriv (2 * 1) (riemannHeat s₀) = deriv (deriv (riemannHeat s₀)) := by
          rw [mul_one, iteratedDeriv_succ, iteratedDeriv_one]
        simp only [mul_zero, iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
          one_mul, pow_one, Nat.factorial_one, h20]
        ring
      rw [hsumrange] at h2
      have h3 : riemannHeat s z - (riemannHeat s₀ z - (h : ℂ) * deriv (deriv (riemannHeat s₀)) z) =
          riemannHeat s z - riemannHeat s₀ z + (h : ℂ) * deriv (deriv (riemannHeat s₀)) z := by ring
      rw [h3] at h2
      refine h2.trans ?_
      rw [show |h| ^ 2 = h ^ 2 from sq_abs h]
      gcongr
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
        (integrable_pow_mul_heatWeight (by linarith only [hs₀]) 4 c₀)
        (Eventually.of_forall fun x => ?_)
      simp only
      gcongr
    -- the spatial expansions
    have hR₁ : ‖riemannHeat s₀ z - a * Δ‖ ≤ M * ‖Δ‖ ^ 2 := by
      have := norm_riemannHeat_taylor_le hs₀.le (z₀ := z₀) (z := z) hΔ1
      rwa [hz, sub_zero] at this
    have hR₂ : ‖deriv (deriv (riemannHeat s₀)) z - b‖ ≤ L * ‖Δ‖ :=
      norm_deriv_deriv_riemannHeat_sub_le hs₀.le (z₀ := z₀) (z := z) hΔ1
    -- the main relation
    have hrel : a * Δ - (h : ℂ) * b = -(riemannHeat s₀ z - a * Δ) +
        (h : ℂ) * (deriv (deriv (riemannHeat s₀)) z - b) -
        (riemannHeat s z - riemannHeat s₀ z + (h : ℂ) * deriv (deriv (riemannHeat s₀)) z) := by
      rw [hzero]
      ring
    have hnorm : ‖a * Δ - (h : ℂ) * b‖ ≤ M * ‖Δ‖ ^ 2 + |h| * (L * ‖Δ‖) + K * h ^ 2 := by
      rw [hrel]
      have hhn : ‖(h : ℂ) * (deriv (deriv (riemannHeat s₀)) z - b)‖ ≤ |h| * (L * ‖Δ‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hR₂ (abs_nonneg h)
      calc _ ≤ ‖-(riemannHeat s₀ z - a * Δ) + (h : ℂ) * (deriv (deriv (riemannHeat s₀)) z - b)‖ +
            ‖riemannHeat s z - riemannHeat s₀ z + (h : ℂ) * deriv (deriv (riemannHeat s₀)) z‖ :=
            norm_sub_le _ _
        _ ≤ ‖-(riemannHeat s₀ z - a * Δ)‖ + ‖(h : ℂ) * (deriv (deriv (riemannHeat s₀)) z - b)‖ +
            ‖riemannHeat s z - riemannHeat s₀ z + (h : ℂ) * deriv (deriv (riemannHeat s₀)) z‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
            rw [norm_neg]
            linarith only [hR₁, hhn, hE]
    -- the displacement is linear in the time step
    have hMΔ : M * ‖Δ‖ ≤ ‖a‖ / 4 := by
      have h1 : ‖Δ‖ ≤ ‖a‖ / (4 * (M + 1)) := (hΔ.trans_le (min_le_right _ _)).le
      have h2 := mul_le_mul_of_nonneg_left h1 hM0
      have h3 : M * (‖a‖ / (4 * (M + 1))) ≤ ‖a‖ / 4 := by
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm M ‖a‖, mul_assoc, ← div_eq_mul_inv]
        have : M / (4 * (M + 1)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith only [hM0]
        calc ‖a‖ * (M / (4 * (M + 1))) ≤ ‖a‖ * (1 / 4) := by gcongr
          _ = _ := by ring
      linarith only [h2, h3]
    have hLh : L * |h| ≤ ‖a‖ / 4 := by
      have h1 : |h| ≤ ‖a‖ / (4 * (L + 1)) := (hh.trans_le (min_le_right _ _)).le
      have h2 := mul_le_mul_of_nonneg_left h1 hL0
      have h3 : L * (‖a‖ / (4 * (L + 1))) ≤ ‖a‖ / 4 := by
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm L ‖a‖, mul_assoc, ← div_eq_mul_inv]
        have : L / (4 * (L + 1)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith only [hL0]
        calc ‖a‖ * (L / (4 * (L + 1))) ≤ ‖a‖ * (1 / 4) := by gcongr
          _ = _ := by ring
      linarith only [h2, h3]
    have hΔn := norm_nonneg Δ
    have hhn := abs_nonneg h
    have hlin : ‖Δ‖ ≤ D * |h| := by
      have h1 : ‖a * Δ‖ ≤ ‖a * Δ - (h : ℂ) * b‖ + ‖(h : ℂ) * b‖ := by
        simpa using norm_add_le (a * Δ - (h : ℂ) * b) ((h : ℂ) * b)
      rw [norm_mul a Δ, norm_mul (h : ℂ) b, Complex.norm_real, Real.norm_eq_abs] at h1
      have h2 : M * ‖Δ‖ ^ 2 ≤ ‖a‖ / 4 * ‖Δ‖ := by
        have := mul_le_mul_of_nonneg_right hMΔ hΔn
        nlinarith only [this]
      have h3 : |h| * (L * ‖Δ‖) ≤ ‖a‖ / 4 * ‖Δ‖ := by
        have := mul_le_mul_of_nonneg_right hLh hΔn
        nlinarith only [this]
      have h4 : h ^ 2 ≤ |h| := by
        rw [← sq_abs]
        nlinarith only [hh1, hhn]
      have h5 : K * h ^ 2 ≤ K * |h| := mul_le_mul_of_nonneg_left h4 hK0
      have h6 : ‖a‖ / 2 * ‖Δ‖ ≤ (‖b‖ + K) * |h| := by
        nlinarith only [h1, hnorm, h2, h3, h5]
      rw [hD]
      have heq : 2 * (‖b‖ + K) / ‖a‖ * |h| = ((‖b‖ + K) * |h|) / (‖a‖ / 2) := by
        field_simp
      rw [heq, le_div_iff₀ (by positivity)]
      linarith only [h6]
    -- the conclusion
    have hfinal : ‖a * Δ - (h : ℂ) * b‖ ≤ (M * D ^ 2 + L * D + K) * h ^ 2 := by
      have h1 : ‖Δ‖ ^ 2 ≤ (D * |h|) ^ 2 := pow_le_pow_left₀ hΔn hlin 2
      have h2 : M * ‖Δ‖ ^ 2 ≤ M * (D ^ 2 * h ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        rwa [mul_pow, sq_abs] at h1
      have h3 : |h| * (L * ‖Δ‖) ≤ L * D * h ^ 2 := by
        have := mul_le_mul_of_nonneg_left hlin (mul_nonneg hhn hL0)
        calc |h| * (L * ‖Δ‖) = |h| * L * ‖Δ‖ := by ring
          _ ≤ |h| * L * (D * |h|) := this
          _ = L * D * |h| ^ 2 := by ring
          _ = L * D * h ^ 2 := by rw [sq_abs]
      nlinarith only [hnorm, h2, h3]
    have heq : Δ - (h : ℝ) • (b / a) = (a * Δ - (h : ℂ) * b) / a := by
      rw [Complex.real_smul]
      have ha0 : a ≠ 0 := hd
      field_simp
    rw [heq, norm_div, div_le_iff₀ hna]
    calc _ ≤ _ := hfinal
      _ = C * h ^ 2 * ‖a‖ := by
        rw [hC]
        field_simp
  -- from the quadratic bound to the derivative
  have hlittle : (fun s : ℝ => y s - y s₀ - (s - s₀) • (b / a)) =o[𝓝 s₀] fun s => s - s₀ := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hsm : ∀ᶠ s in 𝓝 s₀, C * |s - s₀| ≤ c := by
      have : Tendsto (fun s : ℝ => C * |s - s₀|) (𝓝 s₀) (𝓝 0) := by
        have := ((continuous_id.sub (continuous_const (y := s₀))).abs.const_mul C).tendsto s₀
        simpa using this
      exact (this.eventually (gt_mem_nhds hc)).mono fun _ h => h.le
    filter_upwards [hquad, hsm] with s h1 h2
    rw [hy0, Real.norm_eq_abs]
    calc _ ≤ C * (s - s₀) ^ 2 := h1
      _ = (C * |s - s₀|) * |s - s₀| := by rw [mul_assoc, ← sq, sq_abs]
      _ ≤ c * |s - s₀| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  exact hasDerivAt_iff_isLittleO.mpr hlittle

/-- The real form of the velocity law: a continuous real path of simple zeros moves at `Re(H″/H′)`. -/
theorem hasDerivAt_real_zero_path {s₀ : ℝ} (hs₀ : 0 < s₀) {x : ℝ → ℝ}
    (hxc : ContinuousAt x s₀) (hxz : ∀ᶠ s in 𝓝 s₀, riemannHeat s (x s : ℂ) = 0)
    (hd : deriv (riemannHeat s₀) (x s₀ : ℂ) ≠ 0) :
    HasDerivAt x (zeroVelocity s₀ (x s₀ : ℂ)).re s₀ := by
  have hc : ContinuousAt (fun s => (x s : ℂ)) s₀ := Complex.continuous_ofReal.continuousAt.comp hxc
  have h := hasDerivAt_zero_path hs₀ hxz.self_of_nhds hd rfl hc hxz
  have h2 : HasDerivAt (fun s => ((x s : ℂ)).re) (zeroVelocity s₀ (x s₀ : ℂ)).re s₀ :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt s₀ h
  simpa only [Complex.ofReal_re] using h2

/-! ## The local gap law -/

/-- The compression of the other zeros of a packet on a pair `x, x'`. -/
def pairCompression (t : ℝ) (T : Finset ℂ) (x x' : ℝ) : ℂ :=
  ∑ b ∈ T, (zeroMult (riemannHeat t) b : ℂ) / (((x' : ℂ) - b) * ((x : ℂ) - b))

/-- **The exact local gap law.** Two real simple zeros in the inner window interact by `4`, the rest of the packet by the
compression, and the exterior through the increment of its field. -/
theorem gap_rate_eq {t X : ℝ} {S : Finset ℂ} {Q : ℂ → ℂ} (ht : 0 < t)
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z = (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z))
    {x x' : ℝ} (hx : riemannHeat t (x : ℂ) = 0) (hx' : riemannHeat t (x' : ℂ) = 0)
    (hd : deriv (riemannHeat t) (x : ℂ) ≠ 0) (hd' : deriv (riemannHeat t) (x' : ℂ) ≠ 0)
    (hxx' : x < x') (hxX : |x - X| < 1) (hx'X : |x' - X| < 1) :
    ((x' - x : ℝ) : ℂ) * (zeroVelocity t (x' : ℂ) - zeroVelocity t (x : ℂ)) =
      4 - 2 * ((x' - x : ℝ) : ℂ) ^ 2 * pairCompression t ((S.erase (x : ℂ)).erase (x' : ℂ)) x x' +
        2 * ((x' - x : ℝ) : ℂ) * (Q (x' : ℂ) - Q (x : ℂ)) := by
  classical
  have hxre : ((x : ℂ)).re = x := Complex.ofReal_re x
  have hx're : ((x' : ℂ)).re = x' := Complex.ofReal_re x'
  have hne : (x : ℂ) ≠ (x' : ℂ) := fun h => hxx'.ne (Complex.ofReal_injective h)
  have hxS : (x : ℂ) ∈ S := (hpacket _).mpr ⟨hx, by rw [hxre]; linarith only [hxX]⟩
  have hx'S : (x' : ℂ) ∈ S := (hpacket _).mpr ⟨hx', by rw [hx're]; linarith only [hx'X]⟩
  have hmx : zeroMult (riemannHeat t) (x : ℂ) = 1 := zeroMult_riemannHeat_eq_one ht.le hx hd
  have hmx' : zeroMult (riemannHeat t) (x' : ℂ) = 1 := zeroMult_riemannHeat_eq_one ht.le hx' hd'
  have hv := simple_heat_zero_velocity_eq_exterior ht hpacket hQ hx hd (by rwa [hxre])
  have hv' := simple_heat_zero_velocity_eq_exterior ht hpacket hQ hx' hd' (by rwa [hx're])
  set T := (S.erase (x : ℂ)).erase (x' : ℂ) with hT
  have hx'E : (x' : ℂ) ∈ S.erase (x : ℂ) := Finset.mem_erase.mpr ⟨hne.symm, hx'S⟩
  have hxE : (x : ℂ) ∈ S.erase (x' : ℂ) := Finset.mem_erase.mpr ⟨hne, hxS⟩
  have hT' : (S.erase (x' : ℂ)).erase (x : ℂ) = T := by
    rw [hT, Finset.erase_right_comm]
  have hsum : ∑ b ∈ S.erase (x : ℂ), (zeroMult (riemannHeat t) b : ℂ) / ((x : ℂ) - b) =
      1 / ((x : ℂ) - x') + ∑ b ∈ T, (zeroMult (riemannHeat t) b : ℂ) / ((x : ℂ) - b) := by
    rw [← Finset.add_sum_erase _ _ hx'E, hmx', Nat.cast_one]
  have hsum' : ∑ b ∈ S.erase (x' : ℂ), (zeroMult (riemannHeat t) b : ℂ) / ((x' : ℂ) - b) =
      1 / ((x' : ℂ) - x) + ∑ b ∈ T, (zeroMult (riemannHeat t) b : ℂ) / ((x' : ℂ) - b) := by
    rw [← Finset.add_sum_erase _ _ hxE, hmx, Nat.cast_one, hT']
  have hgne : (x' : ℂ) - x ≠ 0 := sub_ne_zero.mpr hne.symm
  have hxne : (x : ℂ) - x' ≠ 0 := sub_ne_zero.mpr hne
  -- the sum over the rest of the packet
  have hrest : ∑ b ∈ T, (zeroMult (riemannHeat t) b : ℂ) / ((x' : ℂ) - b) -
      ∑ b ∈ T, (zeroMult (riemannHeat t) b : ℂ) / ((x : ℂ) - b) =
      -((x' : ℂ) - x) * pairCompression t T x x' := by
    rw [pairCompression, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbx' : (x' : ℂ) - b ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm
    have hbx : (x : ℂ) - b ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1.symm
    field_simp
    ring
  simp only [zeroVelocity]
  rw [hv, hv', hsum, hsum']
  push_cast
  have hinv : 1 / ((x : ℂ) - x') = -(1 / ((x' : ℂ) - x)) := by
    rw [show (x : ℂ) - x' = -((x' : ℂ) - x) by ring, one_div, one_div, inv_neg]
  rw [hinv]
  have hone : ((x' : ℂ) - x) * (1 / ((x' : ℂ) - x)) = 1 := by field_simp
  linear_combination (4 : ℂ) * hone + 2 * ((x' : ℂ) - x) * hrest

/-- A zero outside the Jensen disc of a pair compresses the pair: the term has nonnegative real part. -/
theorem re_inv_mul_nonneg {x x' : ℝ} {b : ℂ}
    (hb : ((x' - x) / 2) ^ 2 + b.im ^ 2 ≤ (b.re - (x + x') / 2) ^ 2) :
    0 ≤ (1 / (((x' : ℂ) - b) * ((x : ℂ) - b))).re := by
  rw [one_div, Complex.inv_re]
  refine div_nonneg ?_ (Complex.normSq_nonneg _)
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  nlinarith only [hb]

/-- The compression has nonnegative real part when all other zeros lie outside the Jensen disc. -/
theorem re_pairCompression_nonneg {t x x' : ℝ} {T : Finset ℂ}
    (hT : ∀ b ∈ T, ((x' - x) / 2) ^ 2 + b.im ^ 2 ≤ (b.re - (x + x') / 2) ^ 2) :
    0 ≤ (pairCompression t T x x').re := by
  rw [pairCompression, Complex.re_sum]
  refine Finset.sum_nonneg fun b hb => ?_
  have h := re_inv_mul_nonneg (hT b hb)
  have heq : (zeroMult (riemannHeat t) b : ℂ) / (((x' : ℂ) - b) * ((x : ℂ) - b)) =
      ((zeroMult (riemannHeat t) b : ℝ) : ℂ) * (1 / (((x' : ℂ) - b) * ((x : ℂ) - b))) := by
    push_cast
    ring
  rw [heq, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) h

/-- **The one-sided gap law at one time.** Outside the Jensen disc, `2g Re(V' − V) ≤ 8 + 4Kg²`. -/
theorem gap_rate_le {t X K : ℝ} {S : Finset ℂ} {Q : ℂ → ℂ} (ht : 0 < t)
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ ‖deriv Q z‖ ≤ K ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z = (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z))
    {x x' : ℝ} (hx : riemannHeat t (x : ℂ) = 0) (hx' : riemannHeat t (x' : ℂ) = 0)
    (hd : deriv (riemannHeat t) (x : ℂ) ≠ 0) (hd' : deriv (riemannHeat t) (x' : ℂ) ≠ 0)
    (hxx' : x < x') (hxX : |x - X| < 1) (hx'X : |x' - X| < 1)
    (hJ : ∀ b, riemannHeat t b = 0 → |b.re - X| ≤ 2 → b ≠ (x : ℂ) → b ≠ (x' : ℂ) →
      ((x' - x) / 2) ^ 2 + b.im ^ 2 ≤ (b.re - (x + x') / 2) ^ 2) :
    2 * (x' - x) * ((zeroVelocity t (x' : ℂ)).re - (zeroVelocity t (x : ℂ)).re) ≤
      8 + 4 * K * (x' - x) ^ 2 := by
  classical
  have hK0 : 0 ≤ K := by
    have hin : |((x : ℂ)).re - X| ≤ 1 ∧ |((x : ℂ)).im| ≤ 1 / 2 := by
      constructor
      · rw [Complex.ofReal_re]; exact hxX.le
      · rw [Complex.ofReal_im, abs_zero]; norm_num
    exact (norm_nonneg _).trans (hQ _ hin.1 hin.2).2.1
  have hid := gap_rate_eq ht hpacket (fun z h1 h2 => ⟨(hQ z h1 h2).1, (hQ z h1 h2).2.2⟩) hx hx' hd hd'
    hxx' hxX hx'X
  set T := (S.erase (x : ℂ)).erase (x' : ℂ) with hT
  have hC : 0 ≤ (pairCompression t T x x').re := by
    refine re_pairCompression_nonneg fun b hb => ?_
    obtain ⟨hb1, hb2⟩ := Finset.mem_erase.mp hb
    obtain ⟨hb3, hb4⟩ := Finset.mem_erase.mp hb2
    obtain ⟨hb5, hb6⟩ := (hpacket b).mp hb4
    exact hJ b hb5 hb6 hb3 hb1
  -- the exterior increment on the segment
  set g := x' - x with hg
  have hgpos : 0 < g := sub_pos.mpr hxx'
  have hincr : ‖Q (x' : ℂ) - Q (x : ℂ)‖ ≤ K * g := by
    set D : Set ℂ := {z | |z.re - X| ≤ 1 ∧ |z.im| ≤ 1 / 2} with hDdef
    have hDc : Convex ℝ D := by
      have h1 : Convex ℝ {z : ℂ | |z.re - X| ≤ 1} := by
        have : {z : ℂ | |z.re - X| ≤ 1} = Complex.re ⁻¹' (Set.Icc (X - 1) (X + 1)) := by
          ext z
          simp only [mem_setOf_eq, mem_preimage, mem_Icc, abs_le]
          constructor
          · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
          · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
        rw [this]
        exact (convex_Icc _ _).is_linear_preimage Complex.reLm.isLinear
      have h2 : Convex ℝ {z : ℂ | |z.im| ≤ 1 / 2} := by
        have : {z : ℂ | |z.im| ≤ 1 / 2} = Complex.im ⁻¹' (Set.Icc (-(1 / 2)) (1 / 2)) := by
          ext z
          simp only [mem_setOf_eq, mem_preimage, mem_Icc, abs_le]
        rw [this]
        exact (convex_Icc _ _).is_linear_preimage Complex.imLm.isLinear
      exact h1.inter h2
    have hinD (y : ℝ) (hy : |y - X| < 1) : (y : ℂ) ∈ D := by
      constructor
      · rw [Complex.ofReal_re]; exact hy.le
      · rw [Complex.ofReal_im, abs_zero]; norm_num
    have h := hDc.norm_image_sub_le_of_norm_deriv_le (f := Q) (C := K)
      (fun z hz => (hQ z hz.1 hz.2).1.differentiableAt) (fun z hz => (hQ z hz.1 hz.2).2.1)
      (hinD x hxX) (hinD x' hx'X)
    have hnorm : ‖(x' : ℂ) - x‖ = g := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgpos]
    rwa [hnorm] at h
  have hre := congrArg Complex.re hid
  have hgc : ((g : ℝ) : ℂ) ^ 2 = ((g ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hgc] at hre
  have hmul : (((g : ℝ) : ℂ) * (zeroVelocity t (x' : ℂ) - zeroVelocity t (x : ℂ))).re =
      g * ((zeroVelocity t (x' : ℂ)).re - (zeroVelocity t (x : ℂ)).re) := by
    rw [Complex.re_ofReal_mul, Complex.sub_re]
  have hmul2 : (2 * ((g ^ 2 : ℝ) : ℂ) * pairCompression t T x x').re =
      2 * g ^ 2 * (pairCompression t T x x').re := by
    rw [show (2 : ℂ) * ((g ^ 2 : ℝ) : ℂ) = ((2 * g ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  have hmul3 : (2 * ((g : ℝ) : ℂ) * (Q (x' : ℂ) - Q (x : ℂ))).re =
      2 * g * (Q (x' : ℂ) - Q (x : ℂ)).re := by
    rw [show (2 : ℂ) * ((g : ℝ) : ℂ) = ((2 * g : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.sub_re] at hre
  rw [hmul, hmul2, hmul3] at hre
  have h4 : ((4 : ℂ)).re = 4 := by norm_num
  rw [h4] at hre
  have hQre : (Q (x' : ℂ) - Q (x : ℂ)).re ≤ K * g :=
    (Complex.re_le_norm _).trans hincr
  have hg2 : 0 ≤ 2 * g ^ 2 := by positivity
  have h5 : 0 ≤ 2 * g ^ 2 * (pairCompression t T x x').re := mul_nonneg hg2 hC
  have h6 : 2 * g * (Q (x' : ℂ) - Q (x : ℂ)).re ≤ 2 * g * (K * g) :=
    mul_le_mul_of_nonneg_left hQre (by positivity)
  nlinarith only [hre, h5, h6]

/-! ## The integrated gap law -/

/-- **The gap law along paths.** Let `x < x'` be continuous paths of simple real zeros in the inner window at height `X`, with the
other zeros outside the Jensen disc of the pair. Then `g²(b) ≤ e^{κ(b−a)} (g²(a) + 8(b − a))`, with `κ = 4C log X`. -/
theorem exists_gap_sq_le_of_paths :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1 / 8 →
      b * Real.log X ≤ 1 → ∀ x x' : ℝ → ℝ, ContinuousOn x (Icc a b) → ContinuousOn x' (Icc a b) →
      (∀ s ∈ Icc a b, riemannHeat s (x s : ℂ) = 0 ∧ riemannHeat s (x' s : ℂ) = 0 ∧
        deriv (riemannHeat s) (x s : ℂ) ≠ 0 ∧ deriv (riemannHeat s) (x' s : ℂ) ≠ 0 ∧ x s < x' s ∧
        |x s - X| < 1 ∧ |x' s - X| < 1 ∧
        ∀ w, riemannHeat s w = 0 → |w.re - X| ≤ 2 → w ≠ (x s : ℂ) → w ≠ (x' s : ℂ) →
          ((x' s - x s) / 2) ^ 2 + w.im ^ 2 ≤ (w.re - (x s + x' s) / 2) ^ 2) →
      (x' b - x b) ^ 2 ≤ Real.exp (4 * (C * Real.log X) * (b - a)) * ((x' a - x a) ^ 2 + 8 * (b - a)) := by
  obtain ⟨C, hC, X₀, hX₀, hforce⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X hX a b ha hab hb hbX x x' hxc hx'c hprop
  have hL : 0 ≤ Real.log X := Real.log_nonneg (by linarith only [hX, hX₀])
  set κ := 4 * (C * Real.log X) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set f : ℝ → ℝ := fun s => (x' s - x s) ^ 2 * Real.exp (-κ * (s - a)) with hf
  have hfc : ContinuousOn f (Icc a b) :=
    ((hx'c.sub hxc).pow 2).mul (by fun_prop : Continuous fun s : ℝ => Real.exp (-κ * (s - a))).continuousOn
  have hderiv (s : ℝ) (hs : s ∈ Ioo a b) : ∃ D, HasDerivAt f D s ∧ D ≤ 8 := by
    have hsI : s ∈ Icc a b := Ioo_subset_Icc_self hs
    obtain ⟨h0, h0', hd, hd', hlt, hw, hw', hJ⟩ := hprop s hsI
    have hIcc : Icc a b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hs0 : 0 < s := ha.trans hs.1
    have hdx := hasDerivAt_real_zero_path hs0 (hxc.continuousAt hIcc)
      (Filter.eventually_of_mem hIcc fun u hu => (hprop u hu).1) hd
    have hdx' := hasDerivAt_real_zero_path hs0 (hx'c.continuousAt hIcc)
      (Filter.eventually_of_mem hIcc fun u hu => (hprop u hu).2.1) hd'
    have hsX : s * Real.log X ≤ 1 := (mul_le_mul_of_nonneg_right hs.2.le hL).trans hbX
    obtain ⟨S, Q, hpacket, -, -, hQ⟩ := hforce X hX s hs0.le (hs.2.le.trans hb) hsX
    have hrate := gap_rate_le (K := C * Real.log X) hs0 hpacket
      (fun z h1 h2 => ⟨(hQ z h1 h2).1, (hQ z h1 h2).2.2.1, (hQ z h1 h2).2.2.2.2⟩) h0 h0' hd hd' hlt hw hw' hJ
    set v := (zeroVelocity s (x s : ℂ)).re with hv
    set v' := (zeroVelocity s (x' s : ℂ)).re with hv'
    set g := x' s - x s with hg
    have hE : HasDerivAt (fun u : ℝ => Real.exp (-κ * (u - a))) (Real.exp (-κ * (s - a)) * (-κ)) s := by
      have h1 : HasDerivAt (fun u : ℝ => -κ * (u - a)) (-κ) s := by
        simpa using ((hasDerivAt_id s).sub_const a).const_mul (-κ)
      exact h1.exp
    have hfd := (((hdx'.sub hdx).pow 2)).mul hE
    refine ⟨_, hfd, ?_⟩
    have hexp1 : Real.exp (-κ * (s - a)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ s - a := by linarith only [hs.1]
      nlinarith only [mul_nonneg hκ0 this]
    have hexp0 : 0 < Real.exp (-κ * (s - a)) := Real.exp_pos _
    simp only [Pi.pow_apply, Pi.sub_apply]
    have hrate' : 2 * g * (v' - v) - κ * g ^ 2 ≤ 8 := by
      rw [hκ]
      linarith only [hrate]
    have hform : (2 : ℕ) * (x' s - x s) ^ (2 - 1) * (v' - v) * Real.exp (-κ * (s - a)) +
        (x' s - x s) ^ 2 * (Real.exp (-κ * (s - a)) * -κ) =
        (2 * g * (v' - v) - κ * g ^ 2) * Real.exp (-κ * (s - a)) := by
      rw [hg]
      push_cast
      ring
    rw [hform]
    calc _ ≤ 8 * Real.exp (-κ * (s - a)) := mul_le_mul_of_nonneg_right hrate' hexp0.le
      _ ≤ 8 * 1 := by gcongr
      _ = 8 := by ring
  have hmain : f b - f a ≤ 8 * (b - a) := by
    have hD := Convex.image_sub_le_mul_sub_of_deriv_le (D := Icc a b) (convex_Icc a b) hfc
      (by
        rw [interior_Icc]
        intro s hs
        obtain ⟨D, hD, -⟩ := hderiv s hs
        exact hD.differentiableAt.differentiableWithinAt)
      (C := 8) (by
        rw [interior_Icc]
        intro s hs
        obtain ⟨D, hD, hle⟩ := hderiv s hs
        rw [hD.deriv]
        exact hle) a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
    exact hD
  have hfa : f a = (x' a - x a) ^ 2 := by simp [hf]
  have hfb : f b = (x' b - x b) ^ 2 * Real.exp (-κ * (b - a)) := rfl
  rw [hfa, hfb] at hmain
  have hexpb : Real.exp (κ * (b - a)) * Real.exp (-κ * (b - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp : 0 < Real.exp (κ * (b - a)) := Real.exp_pos _
  have h2 := mul_le_mul_of_nonneg_left (show (x' b - x b) ^ 2 * Real.exp (-κ * (b - a)) ≤
    (x' a - x a) ^ 2 + 8 * (b - a) by linarith only [hmain]) hexp.le
  calc (x' b - x b) ^ 2 = Real.exp (κ * (b - a)) * ((x' b - x b) ^ 2 * Real.exp (-κ * (b - a))) := by
        rw [mul_left_comm, hexpb, mul_one]
    _ ≤ _ := h2

/-- **A pair born at a collision.** If the gap of two paths of zeros tends to `0` at time `a`, then
`g²(b) ≤ 8(b − a) e^{κ(b−a)}`: gaps open no faster than the model `x² − 2(t − t₀)`. -/
theorem exists_gap_sq_le_of_collision :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 / 8 →
      b * Real.log X ≤ 1 → ∀ x x' : ℝ → ℝ, ContinuousOn x (Ioc a b) → ContinuousOn x' (Ioc a b) →
      (∀ s ∈ Ioc a b, riemannHeat s (x s : ℂ) = 0 ∧ riemannHeat s (x' s : ℂ) = 0 ∧
        deriv (riemannHeat s) (x s : ℂ) ≠ 0 ∧ deriv (riemannHeat s) (x' s : ℂ) ≠ 0 ∧ x s < x' s ∧
        |x s - X| < 1 ∧ |x' s - X| < 1 ∧
        ∀ w, riemannHeat s w = 0 → |w.re - X| ≤ 2 → w ≠ (x s : ℂ) → w ≠ (x' s : ℂ) →
          ((x' s - x s) / 2) ^ 2 + w.im ^ 2 ≤ (w.re - (x s + x' s) / 2) ^ 2) →
      Tendsto (fun s => x' s - x s) (𝓝[>] a) (𝓝 0) →
      (x' b - x b) ^ 2 ≤ Real.exp (4 * (C * Real.log X) * (b - a)) * (8 * (b - a)) := by
  obtain ⟨C, hC, X₀, hX₀, hlaw⟩ := exists_gap_sq_le_of_paths
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X hX a b ha hab hb hbX x x' hxc hx'c hprop hlim
  have hupper : Tendsto (fun a' => Real.exp (4 * (C * Real.log X) * (b - a')) *
      ((x' a' - x a') ^ 2 + 8 * (b - a'))) (𝓝[>] a)
      (𝓝 (Real.exp (4 * (C * Real.log X) * (b - a)) * ((0 : ℝ) ^ 2 + 8 * (b - a)))) := by
    have h1 : Tendsto (fun a' : ℝ => Real.exp (4 * (C * Real.log X) * (b - a'))) (𝓝[>] a)
        (𝓝 (Real.exp (4 * (C * Real.log X) * (b - a)))) := by
      have hc : Continuous fun a' : ℝ => Real.exp (4 * (C * Real.log X) * (b - a')) := by fun_prop
      exact (hc.tendsto a).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun a' : ℝ => 8 * (b - a')) (𝓝[>] a) (𝓝 (8 * (b - a))) := by
      have hc : Continuous fun a' : ℝ => 8 * (b - a') := by fun_prop
      exact (hc.tendsto a).mono_left nhdsWithin_le_nhds
    exact h1.mul ((hlim.pow 2).add h2)
  have hle : ∀ᶠ a' in 𝓝[>] a, (x' b - x b) ^ 2 ≤ Real.exp (4 * (C * Real.log X) * (b - a')) *
      ((x' a' - x a') ^ 2 + 8 * (b - a')) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with a' ha'
    have hsub : Icc a' b ⊆ Ioc a b := fun s hs => ⟨ha'.1.trans_le hs.1, hs.2⟩
    exact hlaw X hX a' b (ha.trans_lt ha'.1) ha'.2.le hb hbX x x' (hxc.mono hsub) (hx'c.mono hsub)
      fun s hs => hprop s (hsub hs)
  have := le_of_tendsto_of_tendsto tendsto_const_nhds hupper hle
  simpa using this

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
