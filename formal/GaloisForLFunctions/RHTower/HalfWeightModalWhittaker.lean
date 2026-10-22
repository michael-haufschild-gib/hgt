import GaloisForLFunctions.RHTower.HalfWeightWhittaker
import GaloisForLFunctions.RHTower.SelbergModalEnergy
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMBesselOrderExteriorEnvelope

/-!
# Bounded modal solutions below `1/4` are Whittaker functions

For `y² a'' = (k² y² - s₀(1 - s₀)) a` with `1/2 < s₀ < 1`:

* `modal_zero_of_leading_zero`: a decaying solution with vanishing Frobenius leading coefficient is
  identically zero (the energy of `SelbergModalEnergy`);
* `leading_unique`: the leading coefficient of `α y^{1-s₀} + O(y^{s₀})` is unique;
* **`modal_proportional`**: two bounded decaying solutions with the same `k` are proportional.

For the Schläfli `K_τ` with real `|τ| ≤ 1/2`:

* `norm_Kb_le`: `‖K_τ(s)‖ ≤ √π √(2/s)` for every `s > 0` (`cosh u ≥ e^u/2`, `cosh(τu) ≤ e^{u/2}`, and
  the substitution `v = e^u` into a Gamma integral, `integral_exp_exp_le`);
* `norm_Wh_le`, `tendsto_Wh_atTop`, `Wh_ne_zero`: `W_τ(t) = √t K_τ(t)` is bounded by `√(2π)`, tends
  to `0`, and does not vanish;
* `whModal τ k y = W_τ(ky)` solves `y² b'' = (k²y² - (1/4 - τ²)) b` (`whModal_ode`).

**`modal_eq_whittaker`**: for `0 < τ < 1/2` every bounded decaying solution of the modal equation with
`λ = 1/4 - τ²` is `c · W_τ(ky)`.
-/

open Real Complex Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.RHTower.HalfWeight

open SelbergModalFrobenius SelbergModalEnergy

noncomputable section

/-! ### Rigidity of bounded modal solutions below `1/4` -/

section Rigidity

variable {k s₀ : ℝ} {a a' a'' : ℝ → ℂ}

/-- A modal solution whose Frobenius leading coefficient vanishes is identically zero. -/
theorem modal_zero_of_leading_zero (hs1 : 1 / 2 < s₀) (hs2 : s₀ < 1)
    (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y) (ha' : ∀ y, 0 < y → HasDerivAt a' (a'' y) y)
    (hode : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * a'' y = ((k ^ 2 * y ^ 2 - s₀ * (1 - s₀) : ℝ) : ℂ) * a y)
    (hinf : Tendsto a atTop (𝓝 0)) {C : ℝ}
    (hA : ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y‖ ≤ C * y ^ s₀)
    (hB : ∀ y ∈ Ioc (0 : ℝ) 1, ‖(y : ℂ) * a' y - s₀ * a y‖ ≤ C * y ^ s₀) :
    ∀ y, 0 < y → a y = 0 := by
  apply eq_zero_of_energy (lam := s₀ * (1 - s₀)) (k := k) (by nlinarith) ha ha'
  · intro y hy
    have hy2 : (y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hy 2).ne'
    have := hode y hy
    rw [mul_comm, ← eq_div_iff hy2] at this
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [this]; push_cast; field_simp
  · apply energy_tendsto_zero (C := C + s₀ * C) hs1
    · intro y hy
      have := hA y hy
      have hs : 0 ≤ s₀ * (C * y ^ s₀) := mul_nonneg (by linarith) ((norm_nonneg _).trans this)
      nlinarith
    · intro y hy
      have hA' := hA y hy
      have hB' := hB y hy
      calc ‖(y : ℂ) * a' y‖ = ‖((y : ℂ) * a' y - s₀ * a y) + s₀ * a y‖ := by ring_nf
        _ ≤ ‖(y : ℂ) * a' y - s₀ * a y‖ + ‖(s₀ : ℂ) * a y‖ := norm_add_le _ _
        _ ≤ C * y ^ s₀ + s₀ * (C * y ^ s₀) := by
            gcongr
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
            gcongr
        _ = (C + s₀ * C) * y ^ s₀ := by ring
  · exact hinf

/-- Frobenius data with explicit leading coefficient. -/
theorem modal_frobenius (hs1 : 1 / 2 < s₀) (hs2 : s₀ < 1)
    (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y) (ha' : ∀ y, 0 < y → HasDerivAt a' (a'' y) y)
    (hode : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * a'' y = ((k ^ 2 * y ^ 2 - s₀ * (1 - s₀) : ℝ) : ℂ) * a y)
    {B : ℝ} (hB : ∀ y, 0 < y → ‖a y‖ ≤ B) :
    ∃ α : ℂ, ∃ C : ℝ, ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀ ∧
      ‖((y : ℂ) * a' y - s₀ * a y) - (1 - 2 * s₀) * α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀ :=
  frobenius_asymptotics (k := k) hs1 hs2.le (fun y hy => ha y hy.1) (fun y hy => ha' y hy.1)
    (fun y hy => hode y hy.1) (fun y hy => hB y hy.1)

/-- The Frobenius leading coefficient is unique. -/
theorem leading_unique (hs1 : 1 / 2 < s₀) {α β : ℂ} {C D : ℝ} {f : ℝ → ℂ}
    (hα : ∀ y ∈ Ioc (0 : ℝ) 1, ‖f y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀)
    (hβ : ∀ y ∈ Ioc (0 : ℝ) 1, ‖f y - β * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ D * y ^ s₀) : α = β := by
  by_contra hne
  have hd : 0 < ‖α - β‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  -- `|α - β| y^{1-s₀} ≤ (C + D) y^{s₀}` for all small `y`
  have key : ∀ y ∈ Ioc (0 : ℝ) 1, ‖α - β‖ ≤ (C + D) * y ^ (2 * s₀ - 1) := by
    intro y hy
    have hy0 := hy.1
    have h1 := hα y hy
    have h2 := hβ y hy
    have e : (α - β) * ((y ^ (1 - s₀) : ℝ) : ℂ) =
        (f y - β * ((y ^ (1 - s₀) : ℝ) : ℂ)) - (f y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)) := by ring
    have hn : ‖α - β‖ * y ^ (1 - s₀) ≤ C * y ^ s₀ + D * y ^ s₀ := by
      have := norm_sub_le (f y - β * ((y ^ (1 - s₀) : ℝ) : ℂ)) (f y - α * ((y ^ (1 - s₀) : ℝ) : ℂ))
      rw [← e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hy0 _)] at this
      linarith
    have hp : 0 < y ^ (1 - s₀) := Real.rpow_pos_of_pos hy0 _
    have e2 : y ^ s₀ = y ^ (1 - s₀) * y ^ (2 * s₀ - 1) := by
      rw [← Real.rpow_add hy0]; congr 1; ring
    rw [e2] at hn
    have : ‖α - β‖ * y ^ (1 - s₀) ≤ (C + D) * y ^ (2 * s₀ - 1) * y ^ (1 - s₀) := by nlinarith
    exact le_of_mul_le_mul_right this hp
  have hlim : Tendsto (fun y : ℝ => (C + D) * y ^ (2 * s₀ - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 (2 * s₀ - 1) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at hc
    simpa using (hc.const_mul (C + D)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), ‖α - β‖ ≤ (C + D) * y ^ (2 * s₀ - 1) := by
    filter_upwards [Ioc_mem_nhdsGT one_pos] with y hy using key y hy
  have := ge_of_tendsto hlim hev
  linarith

variable {b b' b'' : ℝ → ℂ}

/-- **Rigidity**: two bounded decaying modal solutions with the same `k` and `λ = s₀(1 - s₀) < 1/4` are
proportional, provided the second is not identically zero. -/
theorem modal_proportional (hs1 : 1 / 2 < s₀) (hs2 : s₀ < 1)
    (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y) (ha' : ∀ y, 0 < y → HasDerivAt a' (a'' y) y)
    (hoa : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * a'' y = ((k ^ 2 * y ^ 2 - s₀ * (1 - s₀) : ℝ) : ℂ) * a y)
    {Ba : ℝ} (hBa : ∀ y, 0 < y → ‖a y‖ ≤ Ba) (hta : Tendsto a atTop (𝓝 0))
    (hb : ∀ y, 0 < y → HasDerivAt b (b' y) y) (hb' : ∀ y, 0 < y → HasDerivAt b' (b'' y) y)
    (hob : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * b'' y = ((k ^ 2 * y ^ 2 - s₀ * (1 - s₀) : ℝ) : ℂ) * b y)
    {Bb : ℝ} (hBb : ∀ y, 0 < y → ‖b y‖ ≤ Bb) (htb : Tendsto b atTop (𝓝 0))
    {y₁ : ℝ} (hy₁ : 0 < y₁) (hb0 : b y₁ ≠ 0) :
    ∃ c : ℂ, ∀ y, 0 < y → a y = c * b y := by
  obtain ⟨αa, Ca, hCa⟩ := modal_frobenius hs1 hs2 ha ha' hoa hBa
  obtain ⟨αb, Cb, hCb⟩ := modal_frobenius hs1 hs2 hb hb' hob hBb
  have hαb : αb ≠ 0 := by
    intro h0
    apply hb0
    refine modal_zero_of_leading_zero hs1 hs2 hb hb' hob htb (C := Cb) ?_ ?_ y₁ hy₁
    · intro y hy; have := (hCb y hy).1; rwa [h0, zero_mul, sub_zero] at this
    · intro y hy; have := (hCb y hy).2; rwa [h0, mul_zero, zero_mul, sub_zero] at this
  set c := αa / αb
  refine ⟨c, ?_⟩
  set h : ℝ → ℂ := fun y => a y - c * b y
  have hh : ∀ y, 0 < y → HasDerivAt h (a' y - c * b' y) y := fun y hy => (ha y hy).sub ((hb y hy).const_mul c)
  have hh' : ∀ y, 0 < y → HasDerivAt (fun y => a' y - c * b' y) (a'' y - c * b'' y) y :=
    fun y hy => (ha' y hy).sub ((hb' y hy).const_mul c)
  have hoh : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * (a'' y - c * b'' y) =
      ((k ^ 2 * y ^ 2 - s₀ * (1 - s₀) : ℝ) : ℂ) * h y := by
    intro y hy; simp only [h]; rw [mul_sub, hoa y hy, mul_left_comm, hob y hy]; ring
  have hBh : ∀ y, 0 < y → ‖h y‖ ≤ Ba + ‖c‖ * Bb := by
    intro y hy
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    exact add_le_add (hBa y hy) (mul_le_mul_of_nonneg_left (hBb y hy) (norm_nonneg _))
  have hth : Tendsto h atTop (𝓝 0) := by
    have := hta.sub (htb.const_mul c)
    simpa using this
  obtain ⟨αh, Ch, hCh⟩ := modal_frobenius hs1 hs2 hh hh' hoh hBh
  -- the leading coefficient of `h` is `αa - c αb = 0`
  have hαh : αh = 0 := by
    have h1 : ∀ y ∈ Ioc (0 : ℝ) 1, ‖h y - 0 * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ (Ca + ‖c‖ * Cb) * y ^ s₀ := by
      intro y hy
      have e : h y - 0 * ((y ^ (1 - s₀) : ℝ) : ℂ) = (a y - αa * ((y ^ (1 - s₀) : ℝ) : ℂ)) -
          c * (b y - αb * ((y ^ (1 - s₀) : ℝ) : ℂ)) := by
        simp only [h, c]; field_simp; ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      have := (hCa y hy).1
      have := (hCb y hy).1
      nlinarith [norm_nonneg c]
    exact leading_unique hs1 (fun y hy => (hCh y hy).1) h1
  have hzero := modal_zero_of_leading_zero hs1 hs2 hh hh' hoh hth (C := Ch)
    (fun y hy => by have := (hCh y hy).1; rwa [hαh, zero_mul, sub_zero] at this)
    (fun y hy => by have := (hCh y hy).2; rwa [hαh, mul_zero, zero_mul, sub_zero] at this)
  intro y hy
  have := hzero y hy
  simp only [h] at this
  exact sub_eq_zero.1 this

end Rigidity


/-! ### Size of `K_τ` for real order `|τ| ≤ 1/2` -/

open GaloisForLFunctions.HTGeometry in
/-- `∫_0^∞ e^{-s e^u/2} e^{u/2} du ≤ √π √(2/s)` (substitute `v = e^u`). -/
theorem integral_exp_exp_le {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => Real.exp (-(s * Real.exp u / 2)) * Real.exp (u / 2)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), Real.exp (-(s * Real.exp u / 2)) * Real.exp (u / 2) ≤
      Real.sqrt Real.pi * Real.sqrt (2 / s) := by
  set g₀ : ℝ → ℝ := fun v => v ^ (-(1 / 2 : ℝ)) * Real.exp (-(s / 2) * v)
  have hg₀ : IntegrableOn g₀ (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2)) (b := s / 2)
      (by norm_num) le_rfl (by positivity)
    simpa [g₀, Real.rpow_one] using this
  have hcomp : ∀ u : ℝ, (g₀ ∘ Real.exp) u * Real.exp u =
      Real.exp (-(s * Real.exp u / 2)) * Real.exp (u / 2) := by
    intro u
    simp only [Function.comp, g₀]
    rw [← Real.exp_mul, show u * -(1 / 2 : ℝ) = -(u / 2) by ring, Real.exp_neg]
    have h1 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (u / 2) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    rw [← h1]; ring_nf
  have hdom : ∀ u : ℝ, 0 ≤ u → Real.exp (-(s * Real.exp u / 2)) * Real.exp (u / 2) ≤
      2 / s * Real.exp (-(1 / 2) * u) := by
    intro u _
    have hx : 0 < s * Real.exp u / 2 := by positivity
    have h1 : Real.exp (-(s * Real.exp u / 2)) ≤ 1 / (s * Real.exp u / 2) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp (s * Real.exp u / 2)])
    have h2 : Real.exp (u / 2) * (1 / (s * Real.exp u / 2)) = 2 / s * Real.exp (-(1 / 2) * u) := by
      have h3 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
        rw [← Real.exp_add]; congr 1; ring
      rw [show -(1 / 2) * u = -(u / 2) by ring, Real.exp_neg, ← h3]
      field_simp
    calc Real.exp (-(s * Real.exp u / 2)) * Real.exp (u / 2)
        ≤ 1 / (s * Real.exp u / 2) * Real.exp (u / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = _ := by rw [mul_comm]; exact h2
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-(s * Real.exp u / 2)) * Real.exp (u / 2)) (Ici 0) := by
    have hI := ((exp_neg_integrableOn_Ioi 0 (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul (2 / s))
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine hI.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hdom u hu.le
  refine ⟨hint.mono_set Ioi_subset_Ici_self, ?_⟩
  have hcv := integral_comp_mul_deriv_Ioi (f := Real.exp) (f' := Real.exp) (g := g₀) (a := 0)
    Real.continuous_exp.continuousOn Real.tendsto_exp_atTop
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (by
      refine ContinuousOn.mul ?_ (by fun_prop)
      intro v hv
      obtain ⟨u, _, rfl⟩ := hv
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (Real.exp_pos u).ne')).continuousWithinAt)
    (by
      refine hg₀.mono_set ?_
      rintro v ⟨u, hu, rfl⟩
      exact Real.exp_pos u)
    (by simpa only [hcomp] using hint)
  simp only [hcomp, Real.exp_zero] at hcv
  rw [hcv]
  have hg0 : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ g₀ v := fun v hv => by
    simp only [g₀]; exact mul_nonneg (Real.rpow_nonneg (le_of_lt hv) _) (Real.exp_pos _).le
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi 0)] g₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hg0 v hv
  have hsub : Ioi (1 : ℝ) ≤ᵐ[volume] Ioi (0 : ℝ) := (Set.Ioi_subset_Ioi zero_le_one).eventuallyLE
  calc ∫ u in Ioi (1 : ℝ), g₀ u ≤ ∫ u in Ioi (0 : ℝ), g₀ u := setIntegral_mono_set hg₀ hnn hsub
    _ = Real.sqrt Real.pi * Real.sqrt (2 / s) := by
        have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := s / 2) (by norm_num)
          (by positivity)
        simp only [g₀]
        rw [show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by norm_num]
        simp_rw [show ∀ v : ℝ, -(s / 2) * v = -(s / 2 * v) by intro v; ring]
        rw [this, Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        rw [show 1 / (s / 2) = 2 / s by field_simp]
        ring

open GaloisForLFunctions.HTGeometry in
/-- **Small-argument bound**: `‖K_τ(s)‖ ≤ √π √(2/s)` for real `|τ| ≤ 1/2`, every `s > 0`. -/
theorem norm_Kb_le {τ : ℝ} (hτ : |τ| ≤ 1 / 2) {s : ℝ} (hs : 0 < s) :
    ‖Kb τ s‖ ≤ Real.sqrt Real.pi * Real.sqrt (2 / s) := by
  obtain ⟨hI, hle⟩ := integral_exp_exp_le hs
  refine le_trans ?_ hle
  unfold Kb modifiedBesselKOrder
  refine norm_integral_le_of_norm_le hI ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  unfold besselOrderKernel
  have hu0 : 0 < u := hu
  have hre : (-(s : ℂ) * Complex.cosh (u : ℂ)).re = -s * Real.cosh u := by
    rw [← Complex.ofReal_cosh]; simp
  rw [norm_mul, Complex.norm_exp, hre, show ((τ : ℂ) * (u : ℂ)) = ((τ * u : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  have hc1 : Real.exp u / 2 ≤ Real.cosh u := by
    rw [Real.cosh_eq]; have := (Real.exp_pos (-u)).le; linarith
  have hc2 : Real.cosh (τ * u) ≤ Real.exp (u / 2) := by
    rw [Real.cosh_eq]
    have h1 : τ * u ≤ u / 2 := by nlinarith [le_abs_self τ]
    have h2 : -(τ * u) ≤ u / 2 := by nlinarith [neg_abs_le τ]
    have := Real.exp_le_exp.2 h1
    have := Real.exp_le_exp.2 h2
    linarith
  have hc3 : Real.exp (-s * Real.cosh u) ≤ Real.exp (-(s * Real.exp u / 2)) :=
    Real.exp_le_exp.2 (by nlinarith)
  exact mul_le_mul hc3 hc2 (Real.cosh_pos _).le (Real.exp_pos _).le


/-! ### The Whittaker function as the bounded modal solution -/

section Whittaker

variable {τ : ℝ}

theorem norm_Wh_le (hτ : |τ| ≤ 1 / 2) {t : ℝ} (ht : 0 < t) :
    ‖Wh τ t‖ ≤ Real.sqrt Real.pi * Real.sqrt 2 := by
  rw [Wh, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := norm_Kb_le hτ ht
  calc Real.sqrt t * ‖Kb τ t‖ ≤ Real.sqrt t * (Real.sqrt Real.pi * Real.sqrt (2 / t)) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = Real.sqrt Real.pi * (Real.sqrt t * Real.sqrt (2 / t)) := by ring
    _ = Real.sqrt Real.pi * Real.sqrt 2 := by
        rw [← Real.sqrt_mul ht.le, mul_div_cancel₀ _ ht.ne']

theorem tendsto_Wh_atTop : Tendsto (Wh τ) atTop (𝓝 0) := by
  have hb : ∀ t : ℝ, 1 ≤ t → ‖Wh τ t‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (τ ^ 2 / 2) * Real.exp (-t) := by
    intro t ht
    have htp : 0 < t := by linarith
    have h := RHTower.d4BM_norm_modifiedBesselKOrder_le ⟨t, htp⟩ (τ : ℂ)
    simp only at h
    rw [Wh, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hν : ‖(τ : ℂ)‖ ^ 2 / (2 * t) ≤ τ ^ 2 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg τ]
    calc Real.sqrt t * ‖Kb τ t‖
        ≤ Real.sqrt t * (Real.exp (-t) * Real.exp (‖(τ : ℂ)‖ ^ 2 / (2 * t)) *
            Real.sqrt (2 * Real.pi / t)) := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt t * (Real.exp (-t) * Real.exp (τ ^ 2 / 2) * Real.sqrt (2 * Real.pi / t)) := by
          gcongr
      _ = Real.sqrt (2 * Real.pi) * Real.exp (τ ^ 2 / 2) * Real.exp (-t) := by
          rw [show Real.sqrt t * (Real.exp (-t) * Real.exp (τ ^ 2 / 2) * Real.sqrt (2 * Real.pi / t)) =
            Real.exp (-t) * Real.exp (τ ^ 2 / 2) * (Real.sqrt t * Real.sqrt (2 * Real.pi / t)) by ring,
            ← Real.sqrt_mul htp.le, mul_div_cancel₀ _ htp.ne']
          ring
  have hlim : Tendsto (fun t : ℝ => Real.sqrt (2 * Real.pi) * Real.exp (τ ^ 2 / 2) * Real.exp (-t)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Real.sqrt (2 * Real.pi) * Real.exp (τ ^ 2 / 2))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with t ht using hb t ht

theorem Wh_ne_zero {t : ℝ} (ht : 0 < t) : Wh τ t ≠ 0 := by
  rw [Wh]
  refine mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 ht).ne') ?_
  intro h
  have := HTGeometry.modifiedBesselKOrder_real_pos ht τ
  rw [show HTGeometry.modifiedBesselKOrder t (τ : ℂ) = Kb τ t from rfl, h] at this
  simp at this

variable (τ) in
/-- The modal Whittaker solution `b(y) = W_τ(k y)`. -/
def whModal (k : ℝ) (y : ℝ) : ℂ := Wh τ (k * y)

theorem whModal_hasDerivAt {k : ℝ} (hk : 0 < k) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (whModal τ k) ((k : ℂ) * dWh τ (k * y)) y := by
  have h := (hasDerivAt_Wh (mul_pos hk hy) (τ : ℂ)).scomp y ((hasDerivAt_id' y).const_mul k)
  refine h.congr_deriv ?_
  rw [mul_one, Complex.real_smul]

theorem whModal_hasDerivAt' {k : ℝ} (hk : 0 < k) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => (k : ℂ) * dWh τ (k * y))
      ((k : ℂ) ^ 2 * ((1 + ((τ : ℂ) ^ 2 - 1 / 4) / ((k * y : ℝ) : ℂ) ^ 2) * Wh τ (k * y))) y := by
  have h := ((hasDerivAt_dWh (mul_pos hk hy) (τ : ℂ)).scomp y ((hasDerivAt_id' y).const_mul k)).const_mul (k : ℂ)
  refine h.congr_deriv ?_
  rw [mul_one, Complex.real_smul]
  push_cast
  ring

/-- `y² b'' = (k² y² - (1/4 - τ²)) b`. -/
theorem whModal_ode {k : ℝ} (hk : 0 < k) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ 2 * ((k : ℂ) ^ 2 * ((1 + ((τ : ℂ) ^ 2 - 1 / 4) / ((k * y : ℝ) : ℂ) ^ 2) * Wh τ (k * y))) =
      ((k ^ 2 * y ^ 2 - (1 / 2 + τ) * (1 - (1 / 2 + τ)) : ℝ) : ℂ) * whModal τ k y := by
  unfold whModal
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp
  ring

/-- **Modal identification**: every bounded decaying solution of `y² a'' = (k²y² - λ) a`,
`λ = 1/4 - τ²`, `0 < τ < 1/2`, is a multiple of `W_τ(ky)`. -/
theorem modal_eq_whittaker (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {k : ℝ} (hk : 0 < k)
    {a a' a'' : ℝ → ℂ}
    (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y) (ha' : ∀ y, 0 < y → HasDerivAt a' (a'' y) y)
    (hode : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * a'' y =
      ((k ^ 2 * y ^ 2 - (1 / 2 + τ) * (1 - (1 / 2 + τ)) : ℝ) : ℂ) * a y)
    {B : ℝ} (hB : ∀ y, 0 < y → ‖a y‖ ≤ B) (hinf : Tendsto a atTop (𝓝 0)) :
    ∃ c : ℂ, ∀ y, 0 < y → a y = c * whModal τ k y := by
  have hτ : |τ| ≤ 1 / 2 := by rw [abs_of_pos hτ0]; linarith
  refine modal_proportional (s₀ := 1 / 2 + τ) (by linarith) (by linarith) ha ha' hode hB hinf
    (fun y hy => whModal_hasDerivAt hk hy) (fun y hy => whModal_hasDerivAt' hk hy)
    (fun y hy => whModal_ode hk hy) (Bb := Real.sqrt Real.pi * Real.sqrt 2)
    (fun y hy => norm_Wh_le hτ (mul_pos hk hy))
    (tendsto_Wh_atTop.comp (tendsto_id.const_mul_atTop hk)) one_pos
    (Wh_ne_zero (by simpa using hk))

end Whittaker
