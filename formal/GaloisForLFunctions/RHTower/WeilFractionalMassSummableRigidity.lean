import GaloisForLFunctions.RHTower.HamburgerTruncatedRadialIntegral

/-!
# Summable fractional spectral masses force `Λ` and RH: the tail plays no role

Let `Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`, and suppose that on `Re s > 1`

`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)
  + Σ_k c_k · 2(s−½)/((s−½)² + u_k²)`,

with integer masses `m_j` at ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`) and real masses `c_k ≥ 0` at
ordinates `u_k ≥ 1`, `u_k → ∞`, with `Σ_k c_k < ∞`.

**Theorem** (`fractional_mass_summable_rigidity`).  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the
Riemann hypothesis holds.

`FractionalMassTailRigidity.fractional_mass_tail_rigidity` needs `Σ c_k u_k^K < ∞` for every `K`,
and `FractionalMassPolynomialTailRigidity.fractional_mass_polynomial_tail_rigidity` needs it for one
`K > 0`.  Here no decay of the mass tail is assumed.

**The general theorem** (`phase_lock_rigidity_of_monotone_twist`).  Let `G` be continuous on
`Re s ≥ ½` with `G' = ΦG`, `Φ` the Herglotz form of Weil positivity for `lam`, and suppose that on
the lower critical line

`G(1 − s) = κ⁻¹ e^{−2πi h(Im s/2)} G(s)`,

where `h` is monotone with values in `[0, H]` and `h(τ) → 0` as `τ → −∞`.  Then `lam = Λ` and RH
holds.  Nothing is assumed about the rate at which `h` tends to zero.

**Proof.**
* The lock defect is `e = κ⁻¹ (e^{−2πih} − 1) F`, with `F = phiG G` the boundary value of the
  producer zeta function.  By `PhaseLockRigidity.phase_lock_rigidity_of_radial_defect` it suffices
  that `ε J_e(ε + i m) → 0` for every `m`.
* Layer cake: `e^{−2πih(t)} − 1 = ∫_0^H ψ(x) 1[x ≤ h(t)] dx` with `ψ(x) = −2πi e^{−2πix}`.  By
  Fubini, `ε J_e = (κ⁻¹/2π) ∫_0^H ψ(x) · ε ∫_{S_x} F k_ε dx` with `S_x = {t < 0 : x ≤ h(t)}`.
* Since `h` is monotone, `S_x` is an interval `(a_x, 0)` up to a point, and `a_x > −∞` for `x > 0`
  because `h → 0`.  The truncated radial integrals `ε ∫_a^0 F k_ε` are bounded uniformly in `a` and
  `ε` (`TruncatedRadial.exists_bound_truncated_radial`, a contour shift), and tend to zero for fixed
  `a`.  Dominated convergence in `x` gives `ε J_e → 0`.  The case `m = 0` is direct: the kernel
  decays like `e^{−2|t|}`.
* For the fractional masses, `h(τ) = Σ_k c_k − Σ_{u_k < −2τ} c_k`, and the lock is the reflection
  law of the fractional product from `FractionalMassTailRigidity`.

The absolute (Abel) form of the defect condition would need `δ ∫ (tail) |F| e^{−δ|t|} → 0`, i.e. a
mean-value bound for `|F|` matched to the tail decay.  The signed radial form needs none, because
`ε ∫_a^0 F k_ε` is bounded uniformly in `a` by cancellation.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace MonotoneTwistLock

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial

noncomputable section

/-! ### The layer-cake representation of the twist -/

/-- The layer density `ψ(x) = −2πi e^{−2πix}`. -/
def layerDensity (x : ℝ) : ℂ := -(2 * Real.pi * I) * Complex.exp (-(2 * Real.pi * I) * x)

theorem continuous_layerDensity : Continuous layerDensity := by
  unfold layerDensity; fun_prop

theorem norm_layerDensity (x : ℝ) : ‖layerDensity x‖ = 2 * Real.pi := by
  have hpi := Real.pi_pos
  unfold layerDensity
  rw [norm_mul, norm_neg, show -(2 * (Real.pi : ℂ) * I) * (x : ℂ) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * I
    by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  norm_num

theorem integral_layerDensity (y : ℝ) :
    ∫ x in (0 : ℝ)..y, layerDensity x = Complex.exp (-(2 * Real.pi * I) * y) - 1 := by
  set c : ℂ := -(2 * Real.pi * I) with hc
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) y,
      HasDerivAt (fun x : ℝ => Complex.exp (c * x)) (layerDensity x) x := by
    intro x _
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) (Complex.exp (c * x) * (c * 1)) x :=
      ((hasDerivAt_id (x : ℂ)).const_mul c).cexp
    have h2 := h1.comp_ofReal
    unfold layerDensity
    rw [← hc]
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (continuous_layerDensity.intervalIntegrable _ _)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- `e^{−2πih} − 1 = ∫_{(0,H]} ψ(x) 1[x ≤ h] dx` for `0 ≤ h ≤ H`. -/
theorem twist_eq_setIntegral {y H : ℝ} (hy0 : 0 ≤ y) (hyH : y ≤ H) :
    Complex.exp (-(2 * Real.pi * I) * y) - 1 =
      ∫ x in Ioc 0 H, (if x ≤ y then layerDensity x else 0) := by
  rw [← integral_layerDensity, intervalIntegral.integral_of_le hy0]
  have e : (fun x => if x ≤ y then layerDensity x else 0) = (Iic y).indicator layerDensity := by
    funext x; simp [Set.indicator_apply]
  have hset : Ioc 0 H ∩ Iic y = Ioc 0 y := by
    ext x; simp only [mem_Ioc, mem_inter_iff, mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hyH⟩, h2⟩
  rw [e, setIntegral_indicator measurableSet_Iic, hset]

/-! ### Superlevel sets of a monotone twist are intervals -/

/-- **Superlevel sets of a monotone function vanishing at `−∞`.**  For `x > 0` there is `a ≤ 0`
such that integration over `{t < 0 : x ≤ h(t)}` is integration over `(a, 0)`. -/
theorem exists_interval_superlevel {h : ℝ → ℝ} (hmono : Monotone h)
    (hlim : Tendsto h atBot (𝓝 0)) {x : ℝ} (hx : 0 < x) :
    ∃ a : ℝ, a ≤ 0 ∧ ∀ g : ℝ → ℂ,
      ∫ t in Iio (0 : ℝ), (if x ≤ h t then g t else 0) = ∫ t in a..0, g t := by
  set S : Set ℝ := {t | t < 0 ∧ x ≤ h t} with hS
  obtain ⟨T, hT⟩ := Filter.eventually_atBot.mp (hlim.eventually_lt_const hx)
  have hbdd : BddBelow S := ⟨T, fun t ht => by
    by_contra hlt
    push Not at hlt
    exact absurd ht.2 (not_le.mpr (hT t hlt.le))⟩
  by_cases hne : S.Nonempty
  · set a := sInf S with ha
    have ha0 : a ≤ 0 := by
      obtain ⟨s, hs⟩ := hne
      exact (csInf_le hbdd hs).trans hs.1.le
    refine ⟨a, ha0, fun g => ?_⟩
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Iio (0 : ℝ) →
        (if x ≤ h t then g t else 0) = (Ioo a 0).indicator g t := by
      have hne_a : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
        rw [ae_iff]; simp
      filter_upwards [hne_a] with t hta ht0
      by_cases hxt : x ≤ h t
      · have hmem : t ∈ S := ⟨ht0, hxt⟩
        have hat : a < t := lt_of_le_of_ne (csInf_le hbdd hmem) (Ne.symm hta)
        rw [if_pos hxt, Set.indicator_of_mem (show t ∈ Ioo a 0 from ⟨hat, ht0⟩)]
      · rw [if_neg hxt, Set.indicator_of_notMem]
        rintro ⟨hat, _⟩
        obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne hat
        exact hxt (hs.2.trans (hmono hst.le))
    rw [setIntegral_congr_ae measurableSet_Iio hae, setIntegral_indicator measurableSet_Ioo,
      intervalIntegral.integral_of_le ha0, integral_Ioc_eq_integral_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Iio_self]
  · refine ⟨0, le_rfl, fun g => ?_⟩
    rw [intervalIntegral.integral_same]
    have hz : ∀ t ∈ Iio (0 : ℝ), (if x ≤ h t then g t else 0) = 0 := by
      intro t ht
      rw [if_neg]
      intro hxt
      exact hne ⟨t, ht, hxt⟩
    rw [setIntegral_congr_fun measurableSet_Iio hz, integral_zero]

/-! ### Radial vanishing for a monotone twist -/

/-- The radial integrand is integrable on the line for `Re τ > 0`. -/
theorem integrable_phiG_mul_pairKernel {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {τ : ℂ} (hτ : 0 < τ.re) : Integrable fun t : ℝ => phiG G t * pairKernel (2 * t) τ := by
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  have hδ : 0 < 2 * (τ.re / ‖τ‖) := by positivity
  have hdom := (integrable_abelMass (continuous_phiG hGc).aestronglyMeasurable
    (fun t => (hpoly t).1) hδ).const_mul (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)))
  refine hdom.mono' ((continuous_phiG hGc).mul
    (continuous_pairKernel_two_mul hτ0)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖phiG G t‖ * ‖pairKernel (2 * t) τ‖
      ≤ ‖phiG G t‖ * (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))) :=
        mul_le_mul_of_nonneg_left (norm_pairKernel_two_mul_le t hτ) (norm_nonneg _)
    _ = 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * (‖phiG G t‖ * Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))) := by
        ring

/-- **Radial vanishing for a monotone twist, `m ≥ 1`.**  If `h` is monotone with values in
`[0, H]` and `h → 0` at `−∞`, then
`ε ∫_{t<0} (e^{−2πih(t)} − 1) F(½ + 2it) k(2t, ε + i m) dt → 0`. -/
theorem tendsto_radial_monotone_twist {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {h : ℝ → ℝ} (hmono : Monotone h) (hh0 : ∀ t, 0 ≤ h t) {H : ℝ} (hhH : ∀ t, h t ≤ H)
    (hlim : Tendsto h atBot (𝓝 0)) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
        (Complex.exp (-(2 * Real.pi * I) * h t) - 1) *
          (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  obtain ⟨B, hB⟩ := exists_bound_truncated_radial hsl hΦre hid hGc hGd hG2 hm
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  set f : ℝ → ℝ → ℂ := fun ε t => phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) with hf
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hτre : ∀ ε : ℝ, 0 < ε → 0 < ((ε : ℂ) + (m : ℂ) * I).re := fun ε hε => by simp [hε]
  have hτ0 : ∀ ε : ℝ, 0 < ε → ((ε : ℂ) + (m : ℂ) * I) ≠ 0 := fun ε hε h0 => by
    have := hτre ε hε; rw [h0] at this; simp at this
  have hfint : ∀ ε : ℝ, 0 < ε → Integrable (f ε) := fun ε hε =>
    integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 (hτre ε hε)
  have hfc : ∀ ε : ℝ, 0 < ε → Continuous (f ε) := fun ε hε =>
    (continuous_phiG hGc).mul (continuous_pairKernel_two_mul (hτ0 ε hε))
  -- the kernel is bounded by `3` for `m ≥ 1`
  have hk3 : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, ‖pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)‖ ≤ 3 := by
    intro ε hε t
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I
    have h1 : 1 ≤ ‖τ‖ := by
      have := Complex.abs_im_le_norm τ
      simp only [τ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.natCast_re,
        Complex.I_im, mul_one, Complex.natCast_im, Complex.I_re, mul_zero, add_zero,
        zero_add] at this
      rw [abs_of_nonneg (Nat.cast_nonneg m)] at this
      linarith
    calc ‖pairKernel (2 * t) τ‖ ≤ 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 * (τ.re / ‖τ‖) * |t|)) := norm_pairKernel_two_mul_le t (hτre ε hε)
      _ ≤ 3 * 1 * 1 := by
          gcongr
          · exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
          · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by
              have := hτre ε hε; positivity))
      _ = 3 := by norm_num
  -- Fubini: the layer-cake form
  set F : ℝ → ℝ → ℂ := fun ε x => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
    (if x ≤ h t then layerDensity x * f ε t else 0) with hF
  have hmeasS : MeasurableSet {p : ℝ × ℝ | p.2 ≤ h p.1} :=
    measurableSet_le measurable_snd (hmono.measurable.comp measurable_fst)
  have hprod : ∀ ε : ℝ, 0 < ε → Integrable
      (Function.uncurry fun t x => if x ≤ h t then layerDensity x * f ε t else 0)
      ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioc 0 H))) := by
    intro ε hε
    have hdom : Integrable (fun p : ℝ × ℝ => ‖f ε p.1‖ * (2 * Real.pi))
        ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioc 0 H))) :=
      Integrable.mul_prod (hfint ε hε).norm.integrableOn
        (integrableOn_const (C := 2 * Real.pi) (hs := measure_Ioc_lt_top.ne))
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous fun p : ℝ × ℝ => layerDensity p.2 * f ε p.1 :=
        (continuous_layerDensity.comp continuous_snd).mul ((hfc ε hε).comp continuous_fst)
      exact (Measurable.ite hmeasS hc.measurable measurable_const).aestronglyMeasurable
    · simp only [Function.uncurry]
      split_ifs
      · rw [norm_mul, norm_layerDensity, mul_comm]
      · rw [norm_zero]; positivity
  have hfub : ∀ ε : ℝ, 0 < ε → (ε : ℂ) * ∫ t in Iio (0 : ℝ),
      (Complex.exp (-(2 * Real.pi * I) * h t) - 1) * f ε t = ∫ x in Ioc 0 H, F ε x := by
    intro ε hε
    have e1 : ∀ t : ℝ, (Complex.exp (-(2 * Real.pi * I) * h t) - 1) * f ε t =
        ∫ x in Ioc 0 H, (if x ≤ h t then layerDensity x * f ε t else 0) := by
      intro t
      rw [twist_eq_setIntegral (hh0 t) (hhH t), ← integral_mul_const]
      congr 1; funext x; split_ifs <;> simp
    simp only [e1]
    rw [integral_integral_swap (hprod ε hε), ← integral_const_mul]
  -- dominated convergence in `x`
  have hFb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x ∈ Ioc 0 H, ‖F ε x‖ ≤ 2 * Real.pi * B := by
    intro ε hε hε1 x hx
    obtain ⟨a, ha0, hint⟩ := exists_interval_superlevel hmono hlim hx.1
    have e : F ε x = layerDensity x * ((ε : ℂ) * ∫ t in a..0, f ε t) := by
      simp only [hF]
      rw [← hint]
      have : ∀ t, (if x ≤ h t then layerDensity x * f ε t else 0) =
          layerDensity x * (if x ≤ h t then f ε t else 0) := fun t => by
        split_ifs <;> simp
      simp only [this, integral_const_mul]
      ring
    rw [e, norm_mul, norm_layerDensity]
    exact mul_le_mul_of_nonneg_left (hB ε hε hε1 a ha0) (by positivity)
  have hFlim : ∀ x ∈ Ioc 0 H, Tendsto (fun ε => F ε x) (𝓝[>] 0) (𝓝 0) := by
    intro x hx
    obtain ⟨a, ha0, hint⟩ := exists_interval_superlevel hmono hlim hx.1
    set C : ℝ := 3 * (CB * (1 + |a|) ^ N) * |0 - a| with hC
    have hbd : ∀ ε : ℝ, 0 < ε → ‖∫ t in a..0, f ε t‖ ≤ C := by
      intro ε hε
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [Set.uIoc_of_le ha0] at ht
      have hta : |t| ≤ |a| := by
        rw [abs_of_nonpos ht.2, abs_of_nonpos ha0]; linarith [ht.1]
      simp only [hf]
      rw [norm_mul]
      calc ‖phiG G t‖ * ‖pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)‖
          ≤ (CB * (1 + |a|) ^ N) * 3 := by
            refine mul_le_mul ((hpoly t).1.trans ?_) (hk3 ε hε t) (norm_nonneg _) (by positivity)
            gcongr
        _ = 3 * (CB * (1 + |a|) ^ N) := by ring
    have hC0 : 0 ≤ C := by positivity
    refine squeeze_zero_norm' (a := fun ε : ℝ => 2 * Real.pi * C * ε) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : 0 < ε := hε
      have e : F ε x = layerDensity x * ((ε : ℂ) * ∫ t in a..0, f ε t) := by
        simp only [hF]
        rw [← hint]
        have : ∀ t, (if x ≤ h t then layerDensity x * f ε t else 0) =
            layerDensity x * (if x ≤ h t then f ε t else 0) := fun t => by
          split_ifs <;> simp
        simp only [this, integral_const_mul]
        ring
      rw [e, norm_mul, norm_layerDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hε']
      calc 2 * Real.pi * (ε * ‖∫ t in a..0, f ε t‖) ≤ 2 * Real.pi * (ε * C) := by
            gcongr; exact hbd ε hε'
        _ = 2 * Real.pi * C * ε := by ring
    · have := (tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds
      simpa using this.const_mul (2 * Real.pi * C)
  have hDCT : Tendsto (fun ε => ∫ x in Ioc 0 H, F ε x) (𝓝[>] 0) (𝓝 (∫ x in Ioc 0 H, (0 : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * Real.pi * B) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have h1 := (hprod ε hε).integral_prod_right
      exact (h1.aestronglyMeasurable.const_mul (ε : ℂ))
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with
        ε hε hε1
      exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun x hx => hFb ε hε hε1.2.le x hx)
    · exact integrableOn_const (C := 2 * Real.pi * B) (hs := measure_Ioc_lt_top.ne)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hFlim)
  rw [integral_zero] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hfub ε hε).symm

/-- **Radial vanishing at `m = 0`.**  For a bounded twist the kernel decays like `e^{−2|t|}`. -/
theorem tendsto_radial_zero {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {w : ℝ → ℂ} (hw : ∀ t, ‖w t‖ ≤ 2) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
        w t * (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((0 : ℕ) : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  set A : ℝ := ∫ t : ℝ, ‖phiG G t‖ * Real.exp (-(2 * |t|)) with hA
  have hAint : Integrable fun t : ℝ => ‖phiG G t‖ * Real.exp (-(2 * |t|)) :=
    integrable_abelMass (continuous_phiG hGc).aestronglyMeasurable (fun t => (hpoly t).1)
      two_pos
  have hA0 : 0 ≤ A := integral_nonneg fun t => by positivity
  refine squeeze_zero_norm' (a := fun ε : ℝ => 6 * A * ε ^ (1 / 2 : ℝ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hre : 0 < ((ε : ℂ)).re := by simpa using hε'
    have hn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
    have hpt : ∀ t : ℝ, ‖w t * (phiG G t * pairKernel (2 * t) (ε : ℂ))‖ ≤
        6 * ε ^ (-(1 / 2 : ℝ)) * (‖phiG G t‖ * Real.exp (-(2 * |t|))) := by
      intro t
      have hk := norm_pairKernel_two_mul_le t hre
      rw [hn, Complex.ofReal_re, div_self hε'.ne', mul_one] at hk
      rw [norm_mul, norm_mul]
      calc ‖w t‖ * (‖phiG G t‖ * ‖pairKernel (2 * t) (ε : ℂ)‖)
          ≤ 2 * (‖phiG G t‖ * (3 * ε ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 * |t|)))) := by
            gcongr; exact hw t
        _ = 6 * ε ^ (-(1 / 2 : ℝ)) * (‖phiG G t‖ * Real.exp (-(2 * |t|))) := by ring
    have hle : ‖∫ t in Iio (0 : ℝ), w t * (phiG G t * pairKernel (2 * t) (ε : ℂ))‖ ≤
        6 * ε ^ (-(1 / 2 : ℝ)) * A := by
      refine (norm_integral_le_of_norm_le ((hAint.const_mul _).integrableOn)
        (Eventually.of_forall hpt)).trans ?_
      rw [integral_const_mul]
      gcongr
      exact setIntegral_le_integral hAint (Eventually.of_forall fun t => by positivity)
    rw [norm_mul, hn]
    have e : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hε'.le (by norm_num)]; norm_num
    calc ε * ‖∫ t in Iio (0 : ℝ), w t * (phiG G t * pairKernel (2 * t) (ε : ℂ))‖
        ≤ ε * (6 * ε ^ (-(1 / 2 : ℝ)) * A) := by gcongr
      _ = 6 * A * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
      _ = 6 * A * ε ^ (1 / 2 : ℝ) := by rw [e]
  · have h := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h
    simpa using (h.mono_left nhdsWithin_le_nhds).const_mul (6 * A)

/-! ### The phase lock with a monotone twist -/

/-- **Phase-lock rigidity with a monotone twist.**  If on the lower critical line
`G(1 − s) = κ⁻¹ e^{−2πi h(Im s/2)} G(s)` with `h` monotone, `0 ≤ h ≤ H`, and `h → 0` at `−∞`, then
`lam = Λ` and the Riemann hypothesis holds.  No rate of convergence of `h` is needed. -/
theorem phase_lock_rigidity_of_monotone_twist {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {κ : ℂ} (hκ : κ ≠ 0) {h : ℝ → ℝ} (hmono : Monotone h) (hh0 : ∀ t, 0 ≤ h t) {H : ℝ}
    (hhH : ∀ t, h t ≤ H) (hlim : Tendsto h atBot (𝓝 0))
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ⁻¹ * Complex.exp (-(2 * Real.pi * I) * h τ) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hidT hGc hGd hG2
  set w : ℝ → ℂ := fun τ => Complex.exp (-(2 * Real.pi * I) * h τ) - 1 with hw
  set e : ℝ → ℂ := fun τ => if τ < 0 then κ⁻¹ * w τ * phiG G τ else 0 with he
  have hlock' : ∀ τ : ℝ, τ < -0 → G (1 - lineS τ) =
      κ⁻¹ * G (lineS τ) + lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) * e τ := by
    intro τ hτ
    have hτ0 : τ < 0 := by linarith
    have hD : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
        (Gammaℝ_lineS_ne_zero τ)
    simp only [he, if_pos hτ0]
    unfold phiG
    set D := lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) with hDdef
    have hcancel : D * (κ⁻¹ * w τ * (G (lineS τ) / D)) = κ⁻¹ * w τ * G (lineS τ) := by
      field_simp
    rw [hlock τ hτ0, hcancel]
    simp only [hw]
    ring
  have hwb : ∀ τ, ‖w τ‖ ≤ 2 := by
    intro τ
    simp only [hw]
    have hu : ‖Complex.exp (-(2 * Real.pi * I) * h τ)‖ = 1 := by
      rw [show -(2 * (Real.pi : ℂ) * I) * (h τ : ℂ) = ((-(2 * Real.pi * h τ) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    calc ‖Complex.exp (-(2 * Real.pi * I) * h τ) - 1‖
        ≤ ‖Complex.exp (-(2 * Real.pi * I) * h τ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hu, norm_one]; norm_num
  have hwm : Measurable w :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp hmono.measurable))).sub_const _
  have hem : Measurable e := Measurable.ite measurableSet_Iio
    ((measurable_const.mul hwm).mul (continuous_phiG hGc).measurable) measurable_const
  have heb : ∀ τ, ‖e τ‖ ≤ (2 * ‖κ⁻¹‖ * CB) * (1 + |τ|) ^ N := by
    intro τ
    simp only [he]
    split_ifs
    · rw [norm_mul, norm_mul]
      calc ‖κ⁻¹‖ * ‖w τ‖ * ‖phiG G τ‖ ≤ ‖κ⁻¹‖ * 2 * (CB * (1 + |τ|) ^ N) := by
            gcongr
            · exact hwb τ
            · exact (hpoly τ).1
        _ = _ := by ring
    · rw [norm_zero]; positivity
  have heR : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * HamburgerStability.defectLaplace
      ((Iio (-0 : ℝ)).indicator e) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    intro m
    have hrepr : ∀ ε : ℝ, (ε : ℂ) * HamburgerStability.defectLaplace ((Iio (-0 : ℝ)).indicator e)
        ((ε : ℂ) + (m : ℂ) * I) = ((1 / (2 * Real.pi) : ℝ) : ℂ) * κ⁻¹ * ((ε : ℂ) *
          ∫ t in Iio (0 : ℝ), w t * (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) := by
      intro ε
      unfold HamburgerStability.defectLaplace
      rw [neg_zero]
      have hind : (fun t => (Iio (0 : ℝ)).indicator e t *
            pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) =
          (Iio (0 : ℝ)).indicator fun t => e t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) := by
        funext t
        by_cases ht : t ∈ Iio (0 : ℝ)
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
      rw [hind, integral_indicator measurableSet_Iio]
      have hcongr : ∫ t in Iio (0 : ℝ), e t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) =
          ∫ t in Iio (0 : ℝ),
            κ⁻¹ * (w t * (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) := by
        refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
        simp only [he, if_pos (show t < 0 from ht)]
        ring
      rw [hcongr, integral_const_mul]
      ring
    simp only [hrepr]
    have hlim0 : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
        w t * (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; exact tendsto_radial_zero hsl hΦre hidT hGc hGd hG2 hwb
      · exact tendsto_radial_monotone_twist hsl hΦre hidT hGc hGd hG2 hmono hh0 hhH hlim hm
    simpa using hlim0.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ) * κ⁻¹)
  exact phase_lock_rigidity_of_radial_defect hsl hΦd hΦre hid hGc hGd hG2 hem heb le_rfl heR hκ
    hlock'

/-! ### Summable fractional masses -/

open FractionalMassTailRigidity in
/-- **Summable fractional spectral masses force `Λ` and RH.**  The hypotheses of
`FractionalMassTailRigidity.fractional_mass_tail_rigidity` with the tail condition replaced by
`Σ_k c_k < ∞`. -/
theorem fractional_mass_summable_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {c u : ℕ → ℝ}
    (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop) (hcs : Summable c)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hcs2 := summable_div_sq_of_summable hc hu1 hcs
  set G := gInf lam m t c u with hGdef
  set Φ := phiInf m t c u with hΦdef
  have hid' : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s := fun s hs => (hid s hs).symm
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum hc hu1 hut hcs2
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs =>
    re_phiInf_nonneg hc hu1 hut hcs2 hs
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := fun s hs =>
    hasDerivAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum hc hu1 hut hcs2
  set Cinf : ℝ := ∑' k, c k with hCinf
  set κ : ℂ := Complex.exp (-((2 * Real.pi * Cinf : ℝ) : ℂ) * I) with hκ
  have hκ0 : κ ≠ 0 := Complex.exp_ne_zero _
  have hκinv : κ⁻¹ = Complex.exp (((2 * Real.pi * Cinf : ℝ) : ℂ) * I) := by
    rw [hκ, ← Complex.exp_neg]; congr 1; ring
  set hf : ℝ → ℝ := fun τ => Cinf - phaseSum c u (-(2 * τ)) with hhf
  have hps_le : ∀ y, phaseSum c u y ≤ Cinf := fun y =>
    (summable_phaseTerm hut y).tsum_le_tsum (fun k => by split_ifs; exacts [le_rfl, hc k]) hcs
  have hps_nonneg : ∀ y, 0 ≤ phaseSum c u y := fun y =>
    tsum_nonneg fun k => by split_ifs; exacts [hc k, le_rfl]
  have hmono : Monotone hf := fun a b hab => by
    have := phaseSum_mono hc hut (show -(2 * b) ≤ -(2 * a) by linarith)
    simp only [hhf]; linarith
  have hh0 : ∀ τ, 0 ≤ hf τ := fun τ => by simp only [hhf]; linarith [hps_le (-(2 * τ))]
  have hhH : ∀ τ, hf τ ≤ Cinf := fun τ => by simp only [hhf]; linarith [hps_nonneg (-(2 * τ))]
  have hlimps : Tendsto (fun τ : ℝ => phaseSum c u (-(2 * τ))) atBot (𝓝 Cinf) := by
    have hy : Tendsto (fun τ : ℝ => -(2 * τ)) atBot atTop := by
      refine tendsto_neg_atBot_atTop.comp ?_
      exact Filter.tendsto_id.const_mul_atBot two_pos
    refine tendsto_tsum_of_dominated_convergence (bound := c) hcs (fun k => ?_)
      (Eventually.of_forall fun τ k => ?_)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hy.eventually_gt_atTop (u k)] with τ hτ
      rw [if_pos hτ]
    · split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (hc k)]
      · rw [norm_zero]; exact hc k
  have hlim : Tendsto hf atBot (𝓝 0) := by
    have := hlimps.const_sub Cinf
    rwa [sub_self] at this
  have hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ⁻¹ * Complex.exp (-(2 * Real.pi * I) * hf τ) * G (lineS τ) := by
    intro τ hτ0
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have hrefl : G (1 - lineS τ) = Complex.exp (((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I) *
        G (lineS τ) := by
      simp only [hGdef, gInf]
      rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracInfProd_conj hc hu1 hut hcs2 hre,
        hline, conj_fracInfProd_lower hc hu1 hut hcs2 hy]
      ring
    rw [hrefl, hκinv, ← Complex.exp_add]
    congr 2
    simp only [hhf]
    push_cast
    ring
  exact phase_lock_rigidity_of_monotone_twist hsl hΦd hΦre hid' hGc hGd hG2 hκ0 hmono hh0 hhH hlim
    hlock

end

end MonotoneTwistLock

end RHTower
