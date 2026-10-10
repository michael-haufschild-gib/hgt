import GaloisForLFunctions.RHTower.MertensFrontierMultiplicityOmega

/-!
# One-sided graded Ω± for the Mertens function at the zero frontier

Let `Θ = sup {Re ρ : ζ(ρ) = 0}` (`zetaZeroAbscissa`) and suppose a zero `ρ` of order `m` lies on
`Re s = Θ`. Then, with no hypothesis:

* **Order cap from one-sided bounds** (`natCast_order_le_of_mertens_oneSided`). For `½ ≤ θ < 1`,
  if `M(N) = O(N^{θ+ε})` for every `ε > 0` and `η M(x) ≤ c x^θ (1 + log x)^a + K` on `x ≥ 1` for
  one sign `η = ±1`, then every point of `Re s = θ` has `ζ`-order `≤ a + 1`; at order exactly
  `a + 1` the constant obeys `1 ≤ 2^{a+2} K_a c ‖ρ‖ ‖g(ρ)‖`, where `ζ(z) = (z - ρ)^{a+1} g(z)`.
* **Graded one-sided Ω at the frontier** (`not_eventually_mertens_oneSided_zetaZeroAbscissa`).
  For every sign `η` and every `c`, `η M(x) ≤ c x^Θ (1 + log x)^a` fails for arbitrarily large
  `x` whenever `a + 1 < m`.
* **Sharp Ω±** (`exists_mertens_omega_pm_zetaZeroAbscissa`). There is `c₀ > 0` such that for both
  signs and every `c < c₀`, `η M(x) ≤ c x^Θ (1 + log x)^{m-1}` fails for arbitrarily large `x`.
  At a simple frontier zero this is `M(x) = Ω±(x^Θ)`.

**Proof.** No Landau theorem is needed: unconditionally `M(N) = O(N^{Θ+ε})`, so
`G(s) = ∫_1^∞ M(x) x^{-s-1} dx` is holomorphic on `Re s > Θ` with `G(s)·s·(s - 1)ζ(s) = s - 1`.
Write `φ(x) = c x^θ (1 + log x)^a + K` and `h = φ - ηM ≥ 0`. For `σ = Re s`,
`‖G(s)‖ ≤ ‖∫ φ x^{-s-1}‖ + ‖∫ h x^{-s-1}‖ ≤ 2∫ φ x^{-σ-1} + |G(σ)|`, because `h` is nonnegative and
`∫ h x^{-σ-1} = ∫ φ x^{-σ-1} - η G(σ)`. The real values `G(σ) = 1/(σζ(σ))` stay bounded as
`σ ↓ θ`, and `∫ φ x^{-σ-1} ≤ c 2^{a+1} K_a (σ - θ)^{-(a+1)} + K/σ`. Along `s = ρ + r` this gives
`‖G(ρ + r)‖ ≤ 2^{a+2} K_a c r^{-(a+1)} + O(1)`, and the ray lemma below compares it with the
exact pole `(ρ - 1)/(r^m ρ (ρ - 1) g(ρ))`.
-/

open Complex Filter Topology MeasureTheory Set Asymptotics

namespace RHTower

noncomputable section

/-! ## The ray lemma with an exact exponent -/

/-- **Ray lemma, big-`O` form.** If `F·E = H` along `z = ρ + r`, `E z = (z - ρ)^n p z` near `ρ`
with `n ≠ 0`, and `‖F(ρ + r)‖ ≤ B r^{-n} + C`, then `‖H ρ‖ ≤ B ‖p ρ‖`. -/
theorem norm_le_of_ray_bigO {E F H p : ℂ → ℂ} {ρ : ℂ} {B C : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hp : ContinuousAt p ρ) (hfac : ∀ᶠ z in 𝓝 ρ, E z = (z - ρ) ^ n * p z)
    (hH : ContinuousAt H ρ)
    (hFE : ∀ᶠ r : ℝ in 𝓝[>] 0, F (ρ + r) * E (ρ + r) = H (ρ + r))
    (hF : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖F (ρ + r)‖ ≤ B * r ^ (-(n : ℝ)) + C) :
    ‖H ρ‖ ≤ B * ‖p ρ‖ := by
  have hray : Tendsto (fun r : ℝ => ρ + (r : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + (r : ℂ)) (𝓝 0) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    rw [Complex.ofReal_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim1 : Tendsto (fun r : ℝ => ‖H (ρ + r)‖) (𝓝[>] 0) (𝓝 ‖H ρ‖) :=
    (hH.tendsto.comp hray).norm
  have hpow : Tendsto (fun r : ℝ => r ^ n) (𝓝[>] 0) (𝓝 0) := by
    have h := ((continuous_pow n).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [zero_pow hn] at h
  have hlim2 : Tendsto (fun r : ℝ => (B + C * r ^ n) * ‖p (ρ + r)‖) (𝓝[>] 0)
      (𝓝 (B * ‖p ρ‖)) := by
    have h := ((tendsto_const_nhds (x := B)).add (hpow.const_mul C)).mul
      (hp.tendsto.comp hray).norm
    rwa [mul_zero, add_zero] at h
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [hFE, hF, hray.eventually hfac, self_mem_nhdsWithin] with r hr1 hr2 hr3 hr0
  have hr0' : (0 : ℝ) < r := hr0
  rw [← hr1, hr3, add_sub_cancel_left, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hr0'.le]
  have hrn : r ^ (-(n : ℝ)) * r ^ n = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0', neg_add_cancel, Real.rpow_zero]
  have hp0 := norm_nonneg (p (ρ + r))
  have hrn0 : 0 ≤ r ^ n := pow_nonneg hr0'.le n
  calc ‖F (ρ + r)‖ * (r ^ n * ‖p (ρ + r)‖)
      ≤ (B * r ^ (-(n : ℝ)) + C) * (r ^ n * ‖p (ρ + r)‖) :=
        mul_le_mul_of_nonneg_right hr2 (mul_nonneg hrn0 hp0)
    _ = (B * (r ^ (-(n : ℝ)) * r ^ n) + C * r ^ n) * ‖p (ρ + r)‖ := by ring
    _ = (B + C * r ^ n) * ‖p (ρ + r)‖ := by rw [hrn, mul_one]

/-- **Ray lemma, sub-critical exponent.** If `‖F(ρ + r)‖ ≤ B r^{-b} + C` with `b < n`, then
`H ρ = 0`. -/
theorem eq_zero_of_ray_bigO_lt {E F H p : ℂ → ℂ} {ρ : ℂ} {b B C : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hb : b < n) (hp : ContinuousAt p ρ) (hfac : ∀ᶠ z in 𝓝 ρ, E z = (z - ρ) ^ n * p z)
    (hH : ContinuousAt H ρ)
    (hFE : ∀ᶠ r : ℝ in 𝓝[>] 0, F (ρ + r) * E (ρ + r) = H (ρ + r))
    (hF : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖F (ρ + r)‖ ≤ B * r ^ (-b) + C) :
    H ρ = 0 := by
  have hsmall : ∀ ε : ℝ, 0 < ε → ‖H ρ‖ ≤ ε * ‖p ρ‖ := by
    intro ε hε
    have hd : 0 < (n : ℝ) - b := by linarith
    have hcont : Tendsto (fun r : ℝ => |B| * r ^ ((n : ℝ) - b)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const 0 ((n : ℝ) - b) (Or.inr hd.le)).tendsto).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      rw [Real.zero_rpow hd.ne'] at h
      simpa using h.const_mul |B|
    refine norm_le_of_ray_bigO (C := C) hn hp hfac hH hFE ?_
    filter_upwards [hF, hcont.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with r hr hrε hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hsplit : r ^ (-b) = r ^ ((n : ℝ) - b) * r ^ (-(n : ℝ)) := by
      rw [← Real.rpow_add hr0']; ring_nf
    have hneg : 0 ≤ r ^ (-(n : ℝ)) := Real.rpow_nonneg hr0'.le _
    calc ‖F (ρ + r)‖ ≤ B * r ^ (-b) + C := hr
      _ ≤ |B| * r ^ (-b) + C := by
          gcongr
          exact le_abs_self B
      _ = |B| * r ^ ((n : ℝ) - b) * r ^ (-(n : ℝ)) + C := by rw [hsplit]; ring
      _ ≤ ε * r ^ (-(n : ℝ)) + C := by
          gcongr
  by_contra hne
  have hpos : 0 < ‖H ρ‖ := norm_pos_iff.mpr hne
  have h := hsmall (‖H ρ‖ / (‖p ρ‖ + 1)) (by positivity)
  have hlt : ‖H ρ‖ / (‖p ρ‖ + 1) * ‖p ρ‖ < ‖H ρ‖ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (p ρ)]
  linarith

/-! ## Real values of the transform -/

/-- `G(σ)` is the real integral `∫_1^∞ M(x) x^{-σ-1} dx`. -/
theorem mertensMellin_ofReal (σ : ℝ) :
    mertensMellin (σ : ℂ) =
      ((∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * mertensFunctionReal x : ℝ) : ℂ) := by
  rw [mertensMellin_eq_integral_Ici, integral_Ici_eq_integral_Ioi, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans one_pos hx)
  rw [mertensC, Complex.ofReal_mul, Complex.ofReal_cpow hx0]
  push_cast
  ring_nf

/-- The real values `G(θ + r)` stay bounded as `r ↓ 0`. -/
theorem exists_norm_mertensMellin_ofReal_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (θ + ε)) :
    ∃ D : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0, ‖mertensMellin ((θ + r : ℝ) : ℂ)‖ ≤ D := by
  set q : ℂ → ℂ := fun s => (s - 1) / (s * zetaResidueUnit s) with hq
  have hθ0 : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ.ne'
  have hZ : zetaResidueUnit (θ : ℂ) ≠ 0 := zetaResidueUnit_ofReal_ne_zero hθ
  have hqc : ContinuousAt q (θ : ℂ) :=
    ((continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.mul (analyticAt_zetaResidueUnit _).continuousAt) (mul_ne_zero hθ0 hZ))
  have hray : Tendsto (fun r : ℝ => ((θ + r : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (θ : ℂ)) := by
    have h : Tendsto (fun r : ℝ => ((θ + r : ℝ) : ℂ)) (𝓝 0) (𝓝 (((θ + 0 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine ⟨‖q θ‖ + 1, ?_⟩
  have hlim := (hqc.tendsto.comp hray).norm
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one ‖q θ‖)), self_mem_nhdsWithin]
    with r hr hr0
  have hr0' : (0 : ℝ) < r := hr0
  have hre : θ < ((θ + r : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
  have hid := mertensMellin_mul_eq_of_subpower hθ.le hθ1 hM hre
  have hs0 : ((θ + r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show θ + r ≠ 0 by linarith)
  have hZs : zetaResidueUnit ((θ + r : ℝ) : ℂ) ≠ 0 := zetaResidueUnit_ofReal_ne_zero (by linarith)
  have heq : mertensMellin ((θ + r : ℝ) : ℂ) = q ((θ + r : ℝ) : ℂ) := by
    rw [hq]
    simp only
    rw [← hid]
    field_simp
  rw [heq]
  exact hr.le

/-! ## The one-sided transform bound -/

/-- **One-sided transform bound.** If `η M(x) ≤ c x^θ (1 + log x)^a + K` on `x ≥ 1` and
`M(N) = O(N^{θ+ε})` for every `ε`, then for `θ < Re s ≤ θ + 1`
`‖G(s)‖ ≤ 2^{a+2} K_a c (Re s - θ)^{-(a+1)} + 2K/Re s + |G(Re s)|`. -/
theorem norm_mertensMellin_le_of_oneSided {θ a c K η : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hη : |η| = 1)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (θ + ε))
    (hone : ∀ x : ℝ, 1 ≤ x →
      η * mertensFunctionReal x ≤ c * x ^ θ * (1 + Real.log x) ^ a + K)
    {s : ℂ} (hs : θ < s.re) (hs1 : s.re ≤ θ + 1) :
    ‖mertensMellin s‖ ≤
      2 * c * (polylogConst a * 2 ^ (a + 1)) * (s.re - θ) ^ (-(a + 1)) + 2 * K / s.re +
        ‖mertensMellin (s.re : ℂ)‖ := by
  set σ : ℝ := s.re with hσ
  set r : ℝ := σ - θ with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  have hσ0 : 0 < σ := by linarith
  set Ka : ℝ := polylogConst a with hKa
  have hKa0 : 0 < Ka := polylogConst_pos a
  set φ : ℝ → ℝ := fun x => c * x ^ θ * (1 + Real.log x) ^ a + K with hφ
  set h : ℝ → ℝ := fun x => φ x - η * mertensFunctionReal x with hh
  set Ψ : ℝ → ℝ := fun x => c * ((2 / r) ^ a * Ka) * x ^ (-1 - r / 2) + K * x ^ (-σ - 1)
    with hΨ
  have hη2 : η * η = 1 := by
    have := sq_abs η
    rw [hη] at this
    nlinarith
  -- integrability
  have hi1 : IntegrableOn (fun x : ℝ => x ^ (-1 - r / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hi2 : IntegrableOn (fun x : ℝ => x ^ (-σ - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hΨi : IntegrableOn Ψ (Ioi 1) := (hi1.const_mul _).add (hi2.const_mul _)
  have hφmeas : Measurable φ := by
    rw [hφ]
    exact ((measurable_const.mul (measurable_id.pow_const θ)).mul
      ((measurable_const.add Real.measurable_log).pow_const a)).add measurable_const
  have hφle : ∀ x ∈ Ioi (1 : ℝ), x ^ (-σ - 1) * φ x ≤ Ψ x := by
    intro x hx
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := by linarith
    have hl := one_add_log_rpow_le ha hr0 hr1 hx1.le
    have e1 : x ^ (-σ - 1) * x ^ θ = x ^ (-1 - r) := by
      rw [← Real.rpow_add hx0, hr]; ring_nf
    have e2 : x ^ (-1 - r) * x ^ (r / 2) = x ^ (-1 - r / 2) := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hxp : 0 ≤ x ^ (-1 - r) := Real.rpow_nonneg hx0.le _
    calc x ^ (-σ - 1) * φ x
        = c * (x ^ (-σ - 1) * x ^ θ) * (1 + Real.log x) ^ a + K * x ^ (-σ - 1) := by
          rw [hφ]; ring
      _ = c * x ^ (-1 - r) * (1 + Real.log x) ^ a + K * x ^ (-σ - 1) := by rw [e1]
      _ ≤ c * x ^ (-1 - r) * ((2 / r) ^ a * Ka * x ^ (r / 2)) + K * x ^ (-σ - 1) := by
          gcongr
      _ = Ψ x := by rw [hΨ]; simp only; rw [← e2]; ring
  have hφnn : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ x ^ (-σ - 1) * φ x := by
    intro x hx
    have hx0 : 0 < x := lt_trans one_pos hx
    have : 0 ≤ φ x := by
      rw [hφ]
      have : 0 ≤ (1 + Real.log x) ^ a :=
        Real.rpow_nonneg (by linarith [Real.log_nonneg (le_of_lt (show (1 : ℝ) < x from hx))]) _
      positivity
    exact mul_nonneg (Real.rpow_nonneg hx0.le _) this
  have hφi : IntegrableOn (fun x => x ^ (-σ - 1) * φ x) (Ioi 1) := by
    refine Integrable.mono' hΨi ?_ ?_
    · exact ((measurable_id.pow_const _).mul hφmeas).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_of_nonneg (hφnn x hx)]
      exact hφle x hx
  -- the Mertens integrals
  obtain ⟨C₀, hC₀, hMC⟩ := hM (r / 2) (by linarith)
  set A : ℝ := C₀ * 2 ^ (θ + r / 2) with hA
  have hMbound : ∀ x ∈ Ioi (1 : ℝ), |mertensFunctionReal x| ≤ A * x ^ (θ + r / 2) := by
    intro x hx
    rw [hA]
    exact abs_mertensFunctionReal_le_of_subpower (by linarith) hC₀ hMC (le_of_lt hx)
  have hMi : IntegrableOn (fun x => x ^ (-σ - 1) * mertensFunctionReal x) (Ioi 1) := by
    refine Integrable.mono' (hi1.const_mul A) ?_ ?_
    · exact ((measurable_id.pow_const _).mul measurable_mertensFunctionReal).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := lt_trans one_pos hx
      rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), Real.norm_eq_abs]
      have e : x ^ (-σ - 1) * x ^ (θ + r / 2) = x ^ (-1 - r / 2) := by
        rw [← Real.rpow_add hx0, hr]; ring_nf
      calc x ^ (-σ - 1) * |mertensFunctionReal x| ≤ x ^ (-σ - 1) * (A * x ^ (θ + r / 2)) :=
            mul_le_mul_of_nonneg_left (hMbound x hx) (Real.rpow_nonneg hx0.le _)
        _ = A * x ^ (-1 - r / 2) := by rw [← e]; ring
  have hhi : IntegrableOn (fun x => x ^ (-σ - 1) * h x) (Ioi 1) := by
    have := hφi.sub (hMi.const_mul η)
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hh]
    ring
  have hhnn : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ h x := by
    intro x hx
    rw [hh, hφ]; simp only
    linarith [hone x (le_of_lt hx)]
  -- the complex decomposition
  have hcpow : ∀ x ∈ Ioi (1 : ℝ), ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-σ - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_trans one_pos hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    congr 1
  have hcmeas : Measurable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) :=
    Complex.measurable_ofReal.pow_const _
  have hCφi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (φ x : ℂ)) (Ioi 1) := by
    refine Integrable.mono' hφi ?_ ?_
    · exact (hcmeas.mul (Complex.measurable_ofReal.comp hφmeas)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, hcpow x hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_mul_le_mul_left (by simpa using hφnn x hx)
          (Real.rpow_pos_of_pos (lt_trans one_pos hx) (-σ - 1)))]
  have hhmeas : Measurable h := by
    rw [hh]; exact hφmeas.sub (measurable_const.mul measurable_mertensFunctionReal)
  have hChi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (h x : ℂ)) (Ioi 1) := by
    refine Integrable.mono' hhi ?_ ?_
    · exact (hcmeas.mul (Complex.measurable_ofReal.comp hhmeas)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, hcpow x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hhnn x hx)]
  have hdecomp : mertensMellin s = (η : ℂ) * ((∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (φ x : ℂ))
      - ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (h x : ℂ)) := by
    rw [← integral_sub hCφi hChi, ← integral_const_mul, mertensMellin_eq_integral_Ici,
      integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [hh, mertensC]
    simp only
    push_cast
    have hη2c : (η : ℂ) * η = 1 := by exact_mod_cast hη2
    linear_combination (↑x ^ (-s - 1) * ↑(mertensFunctionReal x)) * hη2c.symm
  -- the two norm bounds
  have hnormφ : ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (φ x : ℂ)‖ ≤ ∫ x in Ioi (1 : ℝ), Ψ x := by
    refine norm_integral_le_of_norm_le hΨi ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, hcpow x hx, Complex.norm_real, Real.norm_eq_abs]
    have hx0 : 0 < x := lt_trans one_pos hx
    have hφx : 0 ≤ φ x := le_of_mul_le_mul_left (by simpa using hφnn x hx)
      (Real.rpow_pos_of_pos hx0 (-σ - 1))
    rw [abs_of_nonneg hφx]
    exact hφle x hx
  have hnormh : ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (h x : ℂ)‖ ≤
      ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * h x := by
    refine norm_integral_le_of_norm_le hhi ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, hcpow x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hhnn x hx)]
  have hhint : ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * h x =
      (∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * φ x) -
        η * ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * mertensFunctionReal x := by
    rw [← integral_const_mul, ← integral_sub hφi (hMi.const_mul η)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [hh]; simp only; ring
  have hφint : ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * φ x ≤ ∫ x in Ioi (1 : ℝ), Ψ x :=
    setIntegral_mono_on hφi hΨi measurableSet_Ioi hφle
  have hreal : -(η * ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * mertensFunctionReal x) ≤
      ‖mertensMellin (σ : ℂ)‖ := by
    rw [mertensMellin_ofReal, Complex.norm_real, Real.norm_eq_abs]
    calc -(η * ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * mertensFunctionReal x)
        ≤ |η * ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * mertensFunctionReal x| := neg_le_abs _
      _ = |∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * mertensFunctionReal x| := by
          rw [abs_mul, hη, one_mul]
  have hΨint : ∫ x in Ioi (1 : ℝ), Ψ x =
      c * Ka * 2 ^ (a + 1) * r ^ (-(a + 1)) + K / σ := by
    rw [hΨ, integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, Real.one_rpow,
      show (-1 - r / 2 + 1 : ℝ) = -(r / 2) by ring, show (-σ - 1 + 1 : ℝ) = -σ by ring,
      neg_div_neg_eq, neg_div_neg_eq, one_div_div]
    have h2 : (2 / r) ^ a * (2 / r) = 2 ^ (a + 1) * r ^ (-(a + 1)) := by
      rw [Real.div_rpow (by norm_num) hr0.le, Real.rpow_add_one (by norm_num),
        Real.rpow_neg hr0.le, Real.rpow_add_one hr0.ne']
      field_simp
    calc c * ((2 / r) ^ a * Ka) * (2 / r) + K * (1 / σ)
        = c * Ka * ((2 / r) ^ a * (2 / r)) + K / σ := by ring
      _ = c * Ka * 2 ^ (a + 1) * r ^ (-(a + 1)) + K / σ := by rw [h2]; ring
  rw [hdecomp, norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul]
  calc ‖(∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (φ x : ℂ)) -
        ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (h x : ℂ)‖
      ≤ ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (φ x : ℂ)‖ +
          ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (h x : ℂ)‖ := norm_sub_le _ _
    _ ≤ (∫ x in Ioi (1 : ℝ), Ψ x) + ((∫ x in Ioi (1 : ℝ), Ψ x) + ‖mertensMellin (σ : ℂ)‖) := by
        refine add_le_add hnormφ (hnormh.trans ?_)
        rw [hhint]
        linarith
    _ = 2 * c * (Ka * 2 ^ (a + 1)) * r ^ (-(a + 1)) + 2 * K / σ + ‖mertensMellin (σ : ℂ)‖ := by
        rw [hΨint]; ring

/-! ## Orders at a one-sided exponent -/

/-- **Order cap from a one-sided bound.** For `½ ≤ θ < 1`, a one-sided bound
`η M(x) ≤ c x^θ (1 + log x)^a + K` together with `M(N) = O(N^{θ+ε})` makes every point of
`Re s = θ` have `ζ`-order `≤ a + 1`. -/
theorem natCast_order_le_of_mertens_oneSided {θ a c K η : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hK : 0 ≤ K) (hη : |η| = 1)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (θ + ε))
    (hone : ∀ x : ℝ, 1 ≤ x →
      η * mertensFunctionReal x ≤ c * x ^ θ * (1 + Real.log x) ^ a + K)
    {ρ : ℂ} (hρ : ρ.re = θ) :
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ a + 1 ∧
      ∀ p : ℂ → ℂ, ContinuousAt p ρ →
        (∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) ^ (analyticOrderAt riemannZeta ρ).toNat • p z) →
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ) = a + 1 →
        1 ≤ 2 * c * (polylogConst a * 2 ^ (a + 1)) * (‖ρ‖ * ‖p ρ‖) := by
  have hθ0 : 0 < θ := by linarith
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hρ; linarith
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ; linarith
  set n : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hn
  have hray_re : ∀ r : ℝ, (ρ + (r : ℂ)).re = θ + r := fun r => by simp [hρ]
  -- the ray bound for `G`
  obtain ⟨D, hD⟩ := exists_norm_mertensMellin_ofReal_le hθ0 hθ1 hM
  set B : ℝ := 2 * c * (polylogConst a * 2 ^ (a + 1)) with hB
  have hF : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖mertensMellin (ρ + r)‖ ≤ B * r ^ (-(a + 1)) + (2 * K / θ + D) := by
    filter_upwards [hD, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr hrI
    have hr0 : 0 < r := hrI.1
    have h := norm_mertensMellin_le_of_oneSided hθ0 ha hc hK hη hM hone
      (s := ρ + r) (by rw [hray_re]; linarith) (by rw [hray_re]; linarith [hrI.2])
    rw [hray_re, show θ + r - θ = r by ring] at h
    have hKθ : 2 * K / (θ + r) ≤ 2 * K / θ :=
      div_le_div_of_nonneg_left (by linarith) hθ0 (by linarith)
    rw [hB]
    linarith
  -- the factorisation at `ρ`
  have hFE : ∀ᶠ r : ℝ in 𝓝[>] 0,
      mertensMellin (ρ + r) * ((ρ + r) * zetaResidueUnit (ρ + r)) = (ρ + r) - 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    exact mertensMellin_mul_eq_of_subpower hθ0.le hθ1 hM (by rw [hray_re]; linarith)
  have hHc : ContinuousAt (fun z : ℂ => z - 1) ρ := continuousAt_id.sub continuousAt_const
  have hfacP : ∀ p : ℂ → ℂ,
      (∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) ^ n • p z) →
      ∀ᶠ z in 𝓝 ρ, z * zetaResidueUnit z = (z - ρ) ^ n * (z * ((z - 1) * p z)) := by
    intro p hp
    filter_upwards [hp, isOpen_compl_singleton.mem_nhds hρ1] with z hz hne
    rw [zetaResidueUnit, Function.update_of_ne hne, hz, smul_eq_mul]
    ring
  have hPc : ∀ p : ℂ → ℂ, ContinuousAt p ρ →
      ContinuousAt (fun z : ℂ => z * ((z - 1) * p z)) ρ := fun p hp =>
    continuousAt_id.mul ((continuousAt_id.sub continuousAt_const).mul hp)
  have hρpos : 0 < ρ.re := by rw [hρ]; exact hθ0
  have hρlt : ρ.re < 1 := by rw [hρ]; exact hθ1
  have horderFinite : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρlt⟩]
    exact xi_orderAt_ne_top ρ
  have hncoe : (n : ℕ∞) = analyticOrderAt riemannZeta ρ := ENat.coe_toNat horderFinite
  have hH0 : (ρ - 1) ≠ 0 := sub_ne_zero.mpr hρ1
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have hlt' : a + 1 < (n : ℝ) := not_le.mp hlt
    have hn0 : n ≠ 0 := by
      intro h; rw [h, Nat.cast_zero] at hlt'; linarith
    obtain ⟨p, hp, _, hfactor⟩ :=
      ((analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_natCast).mp hncoe.symm
    exact hH0 (eq_zero_of_ray_bigO_lt (H := fun z => z - 1) hn0 hlt' (hPc p hp.continuousAt)
      (hfacP p hfactor) hHc hFE hF)
  · intro p hp hfactor heq
    have hn0 : n ≠ 0 := by
      intro h; rw [h, Nat.cast_zero] at heq; linarith
    have hF' : ∀ᶠ r : ℝ in 𝓝[>] 0,
        ‖mertensMellin (ρ + r)‖ ≤ B * r ^ (-(n : ℝ)) + (2 * K / θ + D) := by
      rw [heq]; exact hF
    have h := norm_le_of_ray_bigO (H := fun z => z - 1) hn0 (hPc p hp) (hfacP p hfactor) hHc
      hFE hF'
    rw [norm_mul, norm_mul] at h
    have hρ1n : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr hH0
    have h' : ‖ρ - 1‖ * 1 ≤ ‖ρ - 1‖ * (B * (‖ρ‖ * ‖p ρ‖)) := by
      calc ‖ρ - 1‖ * 1 = ‖ρ - 1‖ := mul_one _
        _ ≤ B * (‖ρ‖ * (‖ρ - 1‖ * ‖p ρ‖)) := h
        _ = ‖ρ - 1‖ * (B * (‖ρ‖ * ‖p ρ‖)) := by ring
    exact le_of_mul_le_mul_left h' hρ1n

/-! ## Graded one-sided Ω at the zero frontier -/

/-- An eventual one-sided bound with a nonnegative constant holds globally on `x ≥ 1` after adding
a constant. -/
theorem exists_mertens_oneSided_global {θ a c η : ℝ} (hc : 0 ≤ c) (hη : |η| = 1)
    (hev : ∀ᶠ x : ℝ in atTop, η * mertensFunctionReal x ≤ c * x ^ θ * (1 + Real.log x) ^ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      η * mertensFunctionReal x ≤ c * x ^ θ * (1 + Real.log x) ^ a + K := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  refine ⟨max T 0, le_max_right _ _, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hw : 0 ≤ c * x ^ θ * (1 + Real.log x) ^ a := by
    have : 0 ≤ (1 + Real.log x) ^ a := Real.rpow_nonneg (by linarith [Real.log_nonneg hx]) _
    positivity
  rcases le_or_gt T x with hTx | hxT
  · linarith [hT x hTx, le_max_right T 0]
  · have h1 : η * mertensFunctionReal x ≤ |mertensFunctionReal x| := by
      calc η * mertensFunctionReal x ≤ |η * mertensFunctionReal x| := le_abs_self _
        _ = |mertensFunctionReal x| := by rw [abs_mul, hη, one_mul]
    have h2 : |mertensFunctionReal x| ≤ x := by
      have := abs_mertensFunctionReal_le_abs x
      rwa [abs_of_pos hx0] at this
    linarith [le_max_left T 0]

/-- **Graded one-sided Ω at the frontier.** If a zero `ρ` of order `m` lies on `Re s = Θ`, then for
both signs `η = ±1`, every `c` and every `0 ≤ a` with `a + 1 < m`, the bound
`η M(x) ≤ c x^Θ (1 + log x)^a` fails for arbitrarily large `x`. -/
theorem not_eventually_mertens_oneSided_zetaZeroAbscissa {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ : ρ.re = zetaZeroAbscissa) {a c η : ℝ} (ha : 0 ≤ a) (hη : |η| = 1)
    (hm : a + 1 < ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) :
    ¬ ∀ᶠ x : ℝ in atTop,
      η * mertensFunctionReal x ≤ c * x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a := by
  intro hev
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hev' : ∀ᶠ x : ℝ in atTop,
      η * mertensFunctionReal x ≤ max c 0 * x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a := by
    filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hw : 0 ≤ x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (by linarith [Real.log_nonneg hx1]) _)
    calc η * mertensFunctionReal x ≤ c * x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a := hx
      _ = c * (x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a) := by ring
      _ ≤ max c 0 * (x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hw
      _ = max c 0 * x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a := by ring
  obtain ⟨K, hK, hone⟩ := exists_mertens_oneSided_global (le_max_right c 0) hη hev'
  have h := (natCast_order_le_of_mertens_oneSided half_le_zetaZeroAbscissa
    (by rw [← hρ]; exact hρ1) ha (le_max_right c 0) hK hη
    (fun ε hε => mobiusMertens_subpower_zetaZeroAbscissa ε hε) hone hρ).1
  linarith

/-- **Sharp one-sided Ω± at the frontier.** If a zero `ρ` of order `m` lies on `Re s = Θ`, there
is `c₀ > 0` such that for both signs `η = ±1` and every `c < c₀` the bound
`η M(x) ≤ c x^Θ (1 + log x)^{m-1}` fails for arbitrarily large `x`. At a simple frontier zero
this is `M(x) = Ω±(x^Θ)`. -/
theorem exists_mertens_omega_pm_zetaZeroAbscissa {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ : ρ.re = zetaZeroAbscissa) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ η c : ℝ, |η| = 1 → c < c₀ →
      ¬ ∀ᶠ x : ℝ in atTop, η * mertensFunctionReal x ≤
        c * x ^ zetaZeroAbscissa *
          (1 + Real.log x) ^ (((analyticOrderAt riemannZeta ρ).toNat : ℝ) - 1) := by
  have hρpos : 0 < ρ.re := by rw [hρ]; exact zetaZeroAbscissa_pos
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hρne1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρ1; exact lt_irrefl _ hρ1
  have hρ0 : ρ ≠ 0 := by intro h; rw [h, Complex.zero_re] at hρpos; exact lt_irrefl _ hρpos
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρ1⟩]
    exact xi_orderAt_ne_top ρ
  set m : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hm
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    rintro (h | h)
    exacts [h (analyticOn_riemannZeta ρ hρne1), h hz]
  have hm1 : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero]
    intro h
    exact hne ((ENat.toNat_eq_zero.mp h).resolve_right hfin)
  have hmcoe : (m : ℕ∞) = analyticOrderAt riemannZeta ρ := ENat.coe_toNat hfin
  obtain ⟨p, hp, hpρ, hfactor⟩ :=
    ((analyticOn_riemannZeta ρ hρne1).analyticOrderAt_eq_natCast).mp hmcoe.symm
  set a : ℝ := (m : ℝ) - 1 with ha
  have ha0 : 0 ≤ a := by rw [ha]; have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
                         linarith
  set L : ℝ := 2 * (polylogConst a * 2 ^ (a + 1)) * (‖ρ‖ * ‖p ρ‖) with hL
  have hL0 : 0 < L := by
    have := polylogConst_pos a
    have h1 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
    have h2 : 0 < ‖p ρ‖ := norm_pos_iff.mpr hpρ
    positivity
  refine ⟨1 / L, by positivity, fun η c hη hc hev => ?_⟩
  have hev' : ∀ᶠ x : ℝ in atTop,
      η * mertensFunctionReal x ≤ max c 0 * x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a := by
    filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hw : 0 ≤ x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (by linarith [Real.log_nonneg hx1]) _)
    calc η * mertensFunctionReal x ≤ c * x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a := hx
      _ = c * (x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a) := by ring
      _ ≤ max c 0 * (x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hw
      _ = max c 0 * x ^ zetaZeroAbscissa * (1 + Real.log x) ^ a := by ring
  obtain ⟨K, hK, hone⟩ := exists_mertens_oneSided_global (le_max_right c 0) hη hev'
  have h := (natCast_order_le_of_mertens_oneSided half_le_zetaZeroAbscissa
    (by rw [← hρ]; exact hρ1) ha0 (le_max_right c 0) hK hη
    (fun ε hε => mobiusMertens_subpower_zetaZeroAbscissa ε hε) hone hρ).2 p hp.continuousAt
    hfactor (by rw [ha]; ring)
  have hmax : max c 0 < 1 / L := max_lt hc (by positivity)
  have : 2 * max c 0 * (polylogConst a * 2 ^ (a + 1)) * (‖ρ‖ * ‖p ρ‖) = max c 0 * L := by
    rw [hL]; ring
  rw [this] at h
  have : max c 0 * L < 1 := by
    rw [lt_div_iff₀ hL0] at hmax
    linarith
  linarith

end

end RHTower
