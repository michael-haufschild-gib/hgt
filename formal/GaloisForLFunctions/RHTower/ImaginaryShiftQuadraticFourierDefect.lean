import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import Zeta23.WeilEF.VerticalLine

/-!
# The transform of an even real kernel off the real axis

Write `ĥ(z) = ∫ h(u) e^{izu} du` for the paper transform.

* **Decay at complex points** (`norm_paperFT_mul_one_add_pow_le`).  For `h ∈ Cⁿ` supported in
  `[−R, R]`, `n` integrations by parts give
  `‖ĥ(z)‖ (1 + |Re z|)ⁿ ≤ 2ⁿ e^{|Im z| R} (‖h‖₁ + ‖h⁽ⁿ⁾‖₁)`.
* **Real part off the axis** (`re_paperFT_sub_mul_I_eq`).  For a real even kernel `K`,
  `Re K̂(w − iδ) = ∫ K(u) cos(wu) cosh(δu) du`: the odd part `sinh(δu)` integrates to zero.
* **Quadratic defect** (`abs_re_paperFT_sub_mul_I_sub_le`).  With
  `cosh(δu) − 1 = ∫₀^δ (δ − s) u² cosh(su) ds` the defect becomes an average of
  `Re (u²K)^(w − is)` over `s ∈ [0, δ]`, so
  `|Re K̂(w − iδ) − Re K̂(w)| ≤ 8 δ² e^{|δ|R} (‖u²K‖₁ + ‖(u²K)⁗‖₁) / (1 + |w|)⁴`.

Read through the explicit formula, a zero at horizontal distance `δ` from the critical line shifts
the real part of its Weil summand by `O(δ²)`, decaying like the fourth power of the distance between
its ordinate and the window.
-/

open Complex MeasureTheory Real Set Filter Topology

noncomputable section

namespace RHTower

open Zeta23

/-! ### Decay of the transform at complex points -/

/-- `n` integrations by parts: `(h⁽ⁿ⁾)^(z) = (−iz)ⁿ ĥ(z)`. -/
theorem paperFT_iteratedDeriv {n : ℕ} {h : ℝ → ℂ} (hh : ContDiff ℝ n h)
    (hc : HasCompactSupport h) (z : ℂ) :
    paperFT (iteratedDeriv n h) z = (-(I * z)) ^ n * paperFT h z := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    have hd : ContDiff ℝ n (deriv h) := by simpa using hh.iterate_deriv' n 1
    rw [iteratedDeriv_succ', ih hd hc.deriv,
      paperFT_deriv (hh.of_le (by exact_mod_cast Nat.le_add_left 1 n)) hc]
    ring

/-- All derivatives vanish outside the support interval. -/
theorem iteratedDeriv_eq_zero_of_lt_abs {h : ℝ → ℂ} {R : ℝ} (hsupp : ∀ u, h u ≠ 0 → |u| ≤ R)
    (n : ℕ) {u : ℝ} (hu : R < |u|) : iteratedDeriv n h u = 0 := by
  have hev : h =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hu] with v hv
    by_contra hne
    exact absurd (hsupp v hne) (not_le.mpr hv)
  rw [hev.iteratedDeriv_eq n]
  simp

theorem one_add_pow_le_two_pow_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ 2 ^ n * (1 + x ^ n) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + x ^ n) := le_mul_of_one_le_right (by positivity)
          (by linarith [pow_nonneg hx n])
  · calc (1 + x) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * x ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + x ^ n) := by gcongr; linarith

/-- **Decay at complex points.** `‖ĥ(z)‖ (1 + |Re z|)ⁿ ≤ 2ⁿ e^{|Im z|R} (‖h‖₁ + ‖h⁽ⁿ⁾‖₁)`. -/
theorem norm_paperFT_mul_one_add_pow_le {n : ℕ} {h : ℝ → ℂ} {R : ℝ} (hh : ContDiff ℝ n h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ R) (z : ℂ) :
    ‖paperFT h z‖ * (1 + |z.re|) ^ n ≤
      2 ^ n * Real.exp (|z.im| * R) * ((∫ u, ‖h u‖) + ∫ u, ‖iteratedDeriv n h u‖) := by
  have hc : HasCompactSupport h := hasCompactSupport_of_support_subset_abs hsupp
  have hsn : ∀ u, iteratedDeriv n h u ≠ 0 → |u| ≤ R := fun u hu => by
    by_contra h'
    exact hu (iteratedDeriv_eq_zero_of_lt_abs hsupp n (not_le.mp h'))
  have hint : Integrable h := hh.continuous.integrable_of_hasCompactSupport hc
  have hintn : Integrable (iteratedDeriv n h) :=
    (hh.continuous_iteratedDeriv n le_rfl).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs hsn)
  have h0 := norm_paperFT_le hint hsupp z
  have h1 := norm_paperFT_le hintn hsn z
  rw [paperFT_iteratedDeriv hh hc, norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I,
    one_mul] at h1
  have hpow : (1 + |z.re|) ^ n ≤ 2 ^ n * (1 + ‖z‖ ^ n) :=
    (pow_le_pow_left₀ (by positivity) (by linarith [Complex.abs_re_le_norm z]) n).trans
      (one_add_pow_le_two_pow_mul (norm_nonneg z) n)
  have hF : 0 ≤ ‖paperFT h z‖ := norm_nonneg _
  calc ‖paperFT h z‖ * (1 + |z.re|) ^ n ≤ ‖paperFT h z‖ * (2 ^ n * (1 + ‖z‖ ^ n)) :=
        mul_le_mul_of_nonneg_left hpow hF
    _ = 2 ^ n * (‖paperFT h z‖ + ‖z‖ ^ n * ‖paperFT h z‖) := by ring
    _ ≤ 2 ^ n * (Real.exp (|z.im| * R) * (∫ u, ‖h u‖) +
          Real.exp (|z.im| * R) * ∫ u, ‖iteratedDeriv n h u‖) := by gcongr
    _ = _ := by ring

/-! ### The real part of the transform of an even real kernel -/

section EvenReal

variable {K : ℝ → ℂ}

theorem re_ofReal_mul_cexp (k : ℝ) (z : ℂ) :
    ((k : ℂ) * cexp z).re = k * (Real.exp z.re * Real.cos z.im) := by
  rw [Complex.re_ofReal_mul, Complex.exp_re]

/-- **Real part off the axis.**  For a continuous, compactly supported, real and even kernel,
`Re K̂(w − iδ) = ∫ K(u) cos(wu) cosh(δu) du`. -/
theorem re_paperFT_sub_mul_I_eq (hK : Continuous K) (hKc : HasCompactSupport K)
    (hreal : ∀ u, (K u).im = 0) (heven : ∀ u, K (-u) = K u) (w δ : ℝ) :
    (paperFT K ((w : ℂ) - δ * I)).re =
      ∫ u, (K u).re * Real.cos (w * u) * Real.cosh (δ * u) := by
  set k : ℝ → ℝ := fun u => (K u).re with hk
  have hKk : ∀ u, K u = (k u : ℂ) := fun u => Complex.ext (by simp [hk]) (by simp [hreal u])
  have hkc : Continuous k := Complex.continuous_re.comp hK
  have hkcs : HasCompactSupport k := hKc.comp_left (by simp)
  have hkev : ∀ u, k (-u) = k u := fun u => by simp [hk, heven u]
  -- the real part of the integrand
  have hpt : ∀ u : ℝ, (K u * cexp (I * ((w : ℂ) - δ * I) * u)).re =
      k u * Real.cos (w * u) * Real.exp (δ * u) := by
    intro u
    rw [hKk u, re_ofReal_mul_cexp]
    have hre : (I * ((w : ℂ) - δ * I) * u).re = δ * u := by simp
    have him : (I * ((w : ℂ) - δ * I) * u).im = w * u := by simp
    rw [hre, him]
    ring
  have hcont : Continuous fun u : ℝ => K u * cexp (I * ((w : ℂ) - δ * I) * u) := by fun_prop
  have hint : Integrable fun u : ℝ => K u * cexp (I * ((w : ℂ) - δ * I) * u) :=
    hcont.integrable_of_hasCompactSupport hKc.mul_right
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [paperFT_def, ← hre]
  simp_rw [hpt]
  -- symmetrize `u ↦ −u`
  have hJc : Continuous fun u => k u * Real.cos (w * u) * Real.exp (δ * u) := by fun_prop
  have hJ'c : Continuous fun u => k u * Real.cos (w * u) * Real.exp (-(δ * u)) := by fun_prop
  have hJi : Integrable fun u => k u * Real.cos (w * u) * Real.exp (δ * u) :=
    hJc.integrable_of_hasCompactSupport (hkcs.mul_right.mul_right)
  have hJ'i : Integrable fun u => k u * Real.cos (w * u) * Real.exp (-(δ * u)) :=
    hJ'c.integrable_of_hasCompactSupport (hkcs.mul_right.mul_right)
  have hsym : ∫ u, k u * Real.cos (w * u) * Real.exp (δ * u) =
      ∫ u, k u * Real.cos (w * u) * Real.exp (-(δ * u)) := by
    rw [← integral_neg_eq_self (fun u => k u * Real.cos (w * u) * Real.exp (-(δ * u)))]
    congr 1 with u
    simp only [hkev, mul_neg, neg_neg, Real.cos_neg]
  have hcosh : (fun u => k u * Real.cos (w * u) * Real.cosh (δ * u)) = fun u =>
      (k u * Real.cos (w * u) * Real.exp (δ * u) +
        k u * Real.cos (w * u) * Real.exp (-(δ * u))) / 2 := by
    funext u
    rw [Real.cosh_eq]
    ring
  rw [hcosh, integral_div, integral_add hJi hJ'i, ← hsym]
  ring

/-- `cosh(δu) − 1 = ∫₀^δ (δ − s) u² cosh(su) ds`. -/
theorem integral_sub_mul_sq_mul_cosh (δ u : ℝ) :
    ∫ s in (0 : ℝ)..δ, (δ - s) * (u ^ 2 * Real.cosh (s * u)) = Real.cosh (δ * u) - 1 := by
  have hF : ∀ s ∈ uIcc (0 : ℝ) δ, HasDerivAt
      (fun s : ℝ => (δ - s) * (u * Real.sinh (s * u)) + Real.cosh (s * u))
      ((δ - s) * (u ^ 2 * Real.cosh (s * u))) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => s * u) u s := by simpa using (hasDerivAt_id s).mul_const u
    have hs := (Real.hasDerivAt_sinh (s * u)).comp s h1
    have hc := (Real.hasDerivAt_cosh (s * u)).comp s h1
    have hlin : HasDerivAt (fun s : ℝ => δ - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub δ
    have := (hlin.mul (hs.const_mul u)).add hc
    refine this.congr_deriv ?_
    simp only [Function.comp_apply]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- `‖u²K‖₁ + ‖(u²K)⁗‖₁`, the norm controlling the quadratic defect. -/
def quadraticDefectNorm (K : ℝ → ℂ) : ℝ :=
  (∫ u : ℝ, ‖(u : ℂ) ^ 2 * K u‖) + ∫ u : ℝ, ‖iteratedDeriv 4 (fun u : ℝ => (u : ℂ) ^ 2 * K u) u‖

theorem quadraticDefectNorm_nonneg (K : ℝ → ℂ) : 0 ≤ quadraticDefectNorm K :=
  add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

theorem abs_cosh_mul_le {s u δ R : ℝ} (hs : |s| ≤ δ) (hu : |u| ≤ R) :
    |Real.cosh (s * u)| ≤ Real.cosh (δ * R) := by
  rw [abs_of_pos (Real.cosh_pos _), Real.cosh_le_cosh, abs_mul]
  have hδ : 0 ≤ δ := (abs_nonneg s).trans hs
  calc |s| * |u| ≤ δ * R := mul_le_mul hs hu (abs_nonneg u) hδ
    _ ≤ |δ * R| := le_abs_self _

/-- The real part off the axis depends on `δ` only through `|δ|`. -/
theorem re_paperFT_sub_mul_I_abs (hK : Continuous K) (hKc : HasCompactSupport K)
    (hreal : ∀ u, (K u).im = 0) (heven : ∀ u, K (-u) = K u) (w δ : ℝ) :
    (paperFT K ((w : ℂ) - δ * I)).re = (paperFT K ((w : ℂ) - |δ| * I)).re := by
  rw [re_paperFT_sub_mul_I_eq hK hKc hreal heven, re_paperFT_sub_mul_I_eq hK hKc hreal heven]
  congr 1 with u
  rcases abs_choice δ with h | h <;> rw [h]
  rw [neg_mul, Real.cosh_neg]

/-- **Quadratic defect.**  For a continuous, real, even kernel `K` supported in `[−R, R]` with
`u²K ∈ C⁴`: `|Re K̂(w − iδ) − Re K̂(w)| ≤ 8 δ² e^{|δ|R} (‖u²K‖₁ + ‖(u²K)⁗‖₁) / (1 + |w|)⁴`. -/
theorem abs_re_paperFT_sub_mul_I_sub_le {R : ℝ} (hR : 0 ≤ R) (hK : Continuous K)
    (hsupp : ∀ u, K u ≠ 0 → |u| ≤ R) (hreal : ∀ u, (K u).im = 0) (heven : ∀ u, K (-u) = K u)
    (h4 : ContDiff ℝ 4 (fun u : ℝ => (u : ℂ) ^ 2 * K u)) (w δ : ℝ) :
    |(paperFT K ((w : ℂ) - δ * I)).re - (paperFT K w).re| ≤
      8 * δ ^ 2 * Real.exp (|δ| * R) * quadraticDefectNorm K / (1 + |w|) ^ 4 := by
  have hKc : HasCompactSupport K := hasCompactSupport_of_support_subset_abs hsupp
  -- reduce to `δ ≥ 0`
  rw [re_paperFT_sub_mul_I_abs hK hKc hreal heven, ← sq_abs δ]
  set d := |δ| with hd
  have hd0 : 0 ≤ d := abs_nonneg δ
  -- the weighted kernel `u²K`
  set K₂ : ℝ → ℂ := fun u => (u : ℂ) ^ 2 * K u with hK₂
  have hK₂c : Continuous K₂ := by simp only [hK₂]; fun_prop
  have hK₂s : ∀ u, K₂ u ≠ 0 → |u| ≤ R := fun u hu =>
    hsupp u (fun h0 => hu (by simp [hK₂, h0]))
  have hK₂cs : HasCompactSupport K₂ := hasCompactSupport_of_support_subset_abs hK₂s
  have hK₂r : ∀ u, (K₂ u).im = 0 := fun u => by
    simp only [hK₂]; rw [← Complex.ofReal_pow, Complex.im_ofReal_mul, hreal u, mul_zero]
  have hK₂e : ∀ u, K₂ (-u) = K₂ u := fun u => by simp [hK₂, heven u]
  have hK₂re : ∀ u, (K₂ u).re = u ^ 2 * (K u).re := fun u => by
    simp only [hK₂]; rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  set k : ℝ → ℝ := fun u => (K u).re with hk
  have hkc : Continuous k := Complex.continuous_re.comp hK
  have hks : ∀ u, R < |u| → k u = 0 := fun u hu => by
    have : K u = 0 := by by_contra h; exact absurd (hsupp u h) (not_le.mpr hu)
    simp [hk, this]
  -- the defect as an integral of `cosh(du) − 1`
  have hw0 : (paperFT K (w : ℂ)).re = ∫ u, k u * Real.cos (w * u) * Real.cosh (0 * u) := by
    rw [← re_paperFT_sub_mul_I_eq hK hKc hreal heven w 0]; simp
  rw [re_paperFT_sub_mul_I_eq hK hKc hreal heven, hw0]
  have hint : ∀ c : ℝ, Integrable fun u => k u * Real.cos (w * u) * Real.cosh (c * u) := fun c =>
    (by fun_prop : Continuous fun u => k u * Real.cos (w * u) * Real.cosh (c * u)).integrable_of_hasCompactSupport
      ((hasCompactSupport_of_support_subset_abs (Λ := R) (fun u hu => by
        by_contra h; exact hu (hks u (not_le.mp h)))).mul_right.mul_right)
  rw [← integral_sub (hint d) (hint 0)]
  -- Taylor in `s`, then swap the integrals
  set F : ℝ → ℝ → ℝ := fun s u =>
    (d - s) * (u ^ 2 * k u * Real.cos (w * u) * Real.cosh (s * u)) with hF
  have hpt : ∀ u, k u * Real.cos (w * u) * Real.cosh (d * u) -
      k u * Real.cos (w * u) * Real.cosh (0 * u) = ∫ s in (0 : ℝ)..d, F s u := by
    intro u
    have h := integral_sub_mul_sq_mul_cosh d u
    simp only [hF]
    rw [zero_mul, Real.cosh_zero]
    calc k u * Real.cos (w * u) * Real.cosh (d * u) - k u * Real.cos (w * u) * 1
        = k u * Real.cos (w * u) * (Real.cosh (d * u) - 1) := by ring
      _ = k u * Real.cos (w * u) * ∫ s in (0 : ℝ)..d, (d - s) * (u ^ 2 * Real.cosh (s * u)) := by
          rw [h]
      _ = ∫ s in (0 : ℝ)..d, k u * Real.cos (w * u) * ((d - s) * (u ^ 2 * Real.cosh (s * u))) :=
          (intervalIntegral.integral_const_mul _ _).symm
      _ = _ := by congr 1 with s; ring
  simp_rw [hpt]
  -- integrability on `[0, d] × ℝ`
  have hfin : volume (uIoc (0 : ℝ) d) ≠ ⊤ := by
    rw [uIoc_of_le hd0]; exact measure_Ioc_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) d)) := isFiniteMeasure_restrict.mpr hfin
  set g : ℝ → ℝ := fun u => u ^ 2 * |k u| * Real.cosh (d * R) with hg
  have hgi : Integrable g :=
    (by fun_prop : Continuous g).integrable_of_hasCompactSupport
      ((hasCompactSupport_of_support_subset_abs (Λ := R) (fun u hu => by
        by_contra h; exact hu (by simp [hg, hks u (not_le.mp h)]))))
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (uIoc (0 : ℝ) d)).prod volume) := by
    refine Integrable.mono' ((integrable_const d).mul_prod hgi)
      ((by fun_prop : Continuous (Function.uncurry F)).aestronglyMeasurable) ?_
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict,
      ae_restrict_iff' (measurableSet_uIoc.prod MeasurableSet.univ)]
    refine Eventually.of_forall fun p hp => ?_
    obtain ⟨hp1, -⟩ := hp
    rw [uIoc_of_le hd0] at hp1
    obtain ⟨s, u⟩ := p
    simp only [Function.uncurry_apply_pair, hF, hg, Real.norm_eq_abs]
    rcases le_or_gt |u| R with hu | hu
    · have hc := abs_cosh_mul_le (s := s) (u := u) (δ := d)
        (by rw [abs_of_pos hp1.1]; exact hp1.2) hu
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith [hp1.2] : 0 ≤ d - s),
        abs_of_nonneg (sq_nonneg u)]
      have h1 : d - s ≤ d := by linarith [hp1.1]
      have h2 : |Real.cos (w * u)| ≤ 1 := Real.abs_cos_le_one _
      have h3 : 0 ≤ u ^ 2 * |k u| := by positivity
      calc (d - s) * (u ^ 2 * |k u| * |Real.cos (w * u)| * |Real.cosh (s * u)|)
          ≤ d * (u ^ 2 * |k u| * 1 * Real.cosh (d * R)) := by
            apply mul_le_mul h1 _ (by positivity) hd0
            exact mul_le_mul (mul_le_mul_of_nonneg_left h2 h3) hc (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · simp [hks u hu]
  rw [← intervalIntegral_integral_swap hFi]
  -- the inner integral is `Re (u²K)^(w − is)`
  have hinner : ∀ s, ∫ u, F s u = (d - s) * (paperFT K₂ ((w : ℂ) - s * I)).re := by
    intro s
    rw [re_paperFT_sub_mul_I_eq hK₂c hK₂cs hK₂r hK₂e, ← integral_const_mul]
    congr 1 with u
    simp only [hF, hK₂re, hk]
  simp_rw [hinner]
  -- bound the transform of `u²K` uniformly on `[0, d]`
  set B : ℝ := 16 * Real.exp (d * R) * quadraticDefectNorm K / (1 + |w|) ^ 4 with hB
  have hbound : ∀ s ∈ Icc (0 : ℝ) d, |(paperFT K₂ ((w : ℂ) - s * I)).re| ≤ B := by
    intro s hs
    have h := norm_paperFT_mul_one_add_pow_le h4 hK₂s ((w : ℂ) - s * I)
    have hre : ((w : ℂ) - s * I).re = w := by simp
    have him : |((w : ℂ) - s * I).im| = s := by simp [abs_of_nonneg hs.1]
    rw [hre, him] at h
    have hexp : Real.exp (s * R) ≤ Real.exp (d * R) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.2 hR)
    have hpos : 0 < (1 + |w|) ^ 4 := by positivity
    rw [hB, le_div_iff₀ hpos]
    calc |(paperFT K₂ ((w : ℂ) - s * I)).re| * (1 + |w|) ^ 4
        ≤ ‖paperFT K₂ ((w : ℂ) - s * I)‖ * (1 + |w|) ^ 4 :=
          mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) hpos.le
      _ ≤ 2 ^ 4 * Real.exp (s * R) * quadraticDefectNorm K := by
          simpa [quadraticDefectNorm, hK₂] using h
      _ ≤ 16 * Real.exp (d * R) * quadraticDefectNorm K := by
          have := quadraticDefectNorm_nonneg K
          nlinarith
  have hB0 : 0 ≤ B := by rw [hB]; have := quadraticDefectNorm_nonneg K; positivity
  have hcont : Continuous fun s : ℝ => (d - s) * (paperFT K₂ ((w : ℂ) - s * I)).re := by
    have : Continuous fun s : ℝ => paperFT K₂ ((w : ℂ) - s * I) :=
      (Zeta23.WeilEF.differentiable_paperFT hK₂c hK₂cs).continuous.comp (by fun_prop)
    fun_prop
  calc |∫ s in (0 : ℝ)..d, (d - s) * (paperFT K₂ ((w : ℂ) - s * I)).re|
      ≤ ∫ s in (0 : ℝ)..d, |(d - s) * (paperFT K₂ ((w : ℂ) - s * I)).re| :=
        intervalIntegral.abs_integral_le_integral_abs hd0
    _ ≤ ∫ s in (0 : ℝ)..d, (d - s) * B := by
        refine intervalIntegral.integral_mono_on hd0 (hcont.abs.intervalIntegrable 0 d)
          ((by fun_prop : Continuous fun s : ℝ => (d - s) * B).intervalIntegrable 0 d) ?_
        intro s hs
        rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : 0 ≤ d - s)]
        exact mul_le_mul_of_nonneg_left (hbound s hs) (by linarith [hs.2])
    _ = d ^ 2 / 2 * B := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub intervalIntegrable_const
          intervalIntegral.intervalIntegrable_id, integral_id, intervalIntegral.integral_const,
          smul_eq_mul]
        ring
    _ = 8 * d ^ 2 * Real.exp (d * R) * quadraticDefectNorm K / (1 + |w|) ^ 4 := by
        rw [hB]; ring

end EvenReal

end RHTower
