import GaloisForLFunctions.RHTower.HodgeOffLineFlatnessLaw
import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.RHTower.ZetaConvexityBound

/-!
# The level-`a` Hodge index makes off-line zeros of `ζ` super-exponentially flat

`HodgeOffLineFlatnessLaw` bounds the node values of the detection kernel of an off-line pair by the
tail of Riemann's kernel. This module converts that bound into a statement about `ζ` itself.

* The leading coefficient of `Ξ(z) = ξ(1/2+iz)` at `γ = gammaOf ρ` is `i^k ξ_unit(ρ) v(ρ)`, where
  `ζ(s) = (s-ρ)^k v(s)` near `ρ` and `ξ_unit(s) = s(s-1)/2 · Γ_ℝ(s)`
  (`norm_leading_riemannXiHat`, from uniqueness of local factorisations, `local_factor_unique`).
* `|ξ_unit(β+it)| ≥ e^{-π|t|/4}` for `0 < β < 1`, `|t| ≥ 8` (`exp_le_norm_xiUnit`). This uses the
  reflection formula, `|Γ(1+iy)|² = πy/sinh(πy)` (`norm_Gamma_one_add_I_mul_sq`), and the vertical
  Gamma ratio.
* The polar symbol is at least `β(1-β)/128` at an off-line pair (`norm_polarSymbol_ge`).
* The tail of `Φ` beyond `X` is at most `80 Mθ e^π e^{(c+9/2)X - πe^{2X}}/κ`
  (`expTail_riemannPhiKernel_le`).

The result (`hodgeIndex_zeta_flatness_explicit`): if the Hodge index holds at level `a`, every
off-line zero `ρ₀ = β₀ + it₀` with `|t₀| ≥ 8`, together with its mirror `1 - conj ρ₀`, has

`|v(ρ₀)| |v'(ρ₀')| ≤ K 4^N (1 + 1/|β₀-½|)² (1+|γ₀|)² (β₀(1-β₀))⁻² e^{a/2} G_Φ(N)`
`  · exp((π/2)|t₀| + (λ+9/2)(a-3/8) - π e^{2a-3/4})`,

where `N` is the sum of the two orders and `λ = 1/2 + 3N/2`. Below the height `2e^{2a-3/4}` this is
super-exponentially small.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## Uniqueness of local factorisations -/

/-- Two local factorisations `(z-γ)^m u = (z-γ)^{m'} u'` with nonvanishing continuous factors have
the same order and the same leading value. -/
theorem local_factor_unique {f u u' : ℂ → ℂ} {γ : ℂ} {m m' : ℕ} (hu : ContinuousAt u γ)
    (hu' : ContinuousAt u' γ) (hu0 : u γ ≠ 0) (hu'0 : u' γ ≠ 0)
    (h : f =ᶠ[𝓝 γ] fun z => (z - γ) ^ m * u z) (h' : f =ᶠ[𝓝 γ] fun z => (z - γ) ^ m' * u' z) :
    m = m' ∧ u γ = u' γ := by
  have heq : ∀ᶠ z in 𝓝[≠] γ, (z - γ) ^ m * u z = (z - γ) ^ m' * u' z :=
    nhdsWithin_le_nhds (h.symm.trans h')
  -- compare orders by passing to the limit
  have key : ∀ {p q : ℕ} {a b : ℂ → ℂ}, ContinuousAt a γ → ContinuousAt b γ → a γ ≠ 0 →
      p < q → (∀ᶠ z in 𝓝[≠] γ, (z - γ) ^ p * a z = (z - γ) ^ q * b z) → False := by
    intro p q a b ha hb ha0 hpq hev
    have hev2 : ∀ᶠ z in 𝓝[≠] γ, a z = (z - γ) ^ (q - p) * b z := by
      filter_upwards [hev, self_mem_nhdsWithin] with z hz hne
      have hne' : (z - γ) ^ p ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
      have : (z - γ) ^ q = (z - γ) ^ p * (z - γ) ^ (q - p) := by
        rw [← pow_add]; congr 1; omega
      rw [this, mul_assoc] at hz
      exact mul_left_cancel₀ hne' hz
    have t1 : Tendsto a (𝓝[≠] γ) (𝓝 (a γ)) := ha.tendsto.mono_left nhdsWithin_le_nhds
    have hc : ContinuousAt (fun z => (z - γ) ^ (q - p) * b z) γ :=
      ((continuousAt_id.sub continuousAt_const).pow _).mul hb
    have t2 : Tendsto a (𝓝[≠] γ) (𝓝 ((γ - γ) ^ (q - p) * b γ)) :=
      (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev2.mono fun z hz => hz.symm)
    have := tendsto_nhds_unique t1 t2
    rw [sub_self, zero_pow (by omega), zero_mul] at this
    exact ha0 this
  rcases lt_trichotomy m m' with hlt | heqm | hgt
  · exact (key hu hu' hu0 hlt heq).elim
  · subst heqm
    refine ⟨rfl, ?_⟩
    have hev2 : ∀ᶠ z in 𝓝[≠] γ, u z = u' z := by
      filter_upwards [heq, self_mem_nhdsWithin] with z hz hne
      exact mul_left_cancel₀ (pow_ne_zero _ (sub_ne_zero.mpr hne)) hz
    exact tendsto_nhds_unique (hu.tendsto.mono_left nhdsWithin_le_nhds)
      ((hu'.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev2.mono fun z hz => hz.symm))
  · exact (key hu' hu hu'0 hgt (heq.mono fun z hz => hz.symm)).elim

/-! ## `Ξ` near a zero, in terms of `ζ` -/

theorem riemannXiHat_eq_xiUnit_mul_zeta {z : ℂ} (hre : 0 < (1 / 2 + I * z).re)
    (h0 : 1 / 2 + I * z ≠ 0) (h1 : 1 / 2 + I * z ≠ 1) :
    riemannXiHat z = xiUnit (1 / 2 + I * z) * riemannZeta (1 / 2 + I * z) := by
  rw [riemannXiHat_eq, riemannPhiTransform_eq h0 h1, ← xi_eq_half_mul h0 h1,
    xi_eq_xiUnit_mul_zeta h0 h1 hre]

/-- **Transfer of the leading coefficient.** If `ζ(s) = (s-ρ)^k v(s)` near a nontrivial zero `ρ`
and `Ξ(z) = (z-γ)^m u(z)` near `γ = gammaOf ρ`, then `m = k` and `|u(γ)| = |ξ-unit(ρ)| |v(ρ)|`. -/
theorem norm_leading_riemannXiHat {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) {k m : ℕ}
    {v u : ℂ → ℂ} (hv : AnalyticAt ℂ v ρ) (hv0 : v ρ ≠ 0)
    (hlocζ : ∀ᶠ s in 𝓝 ρ, riemannZeta s = (s - ρ) ^ k * v s)
    (hu : AnalyticAt ℂ u (gammaOf ρ)) (hu0 : u (gammaOf ρ) ≠ 0)
    (hlocΞ : riemannXiHat =ᶠ[𝓝 (gammaOf ρ)] fun z => (z - gammaOf ρ) ^ m * u z) :
    m = k ∧ ‖u (gammaOf ρ)‖ = ‖xiUnit ρ‖ * ‖v ρ‖ := by
  have hnt : IsNontrivialZero ρ := hρ
  set γ := gammaOf ρ with hγ
  have hsγ : 1 / 2 + I * γ = ρ := one_half_add_I_mul_gammaOf ρ
  have hmap : Tendsto (fun z : ℂ => 1 / 2 + I * z) (𝓝 γ) (𝓝 ρ) := by
    have : Continuous fun z : ℂ => 1 / 2 + I * z := by fun_prop
    have h := this.tendsto γ
    rwa [hsγ] at h
  have hρ0 : ρ ≠ 0 := fun h => by have := hnt.2.1; rw [h] at this; simp at this
  have hρ1 : ρ ≠ 1 := fun h => by have := hnt.2.2; rw [h] at this; simp at this
  have hre : ∀ᶠ s in 𝓝 ρ, 0 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hnt.2.1
  have hn0 : ∀ᶠ s in 𝓝 ρ, s ≠ 0 := eventually_ne_nhds hρ0
  have hn1 : ∀ᶠ s in 𝓝 ρ, s ≠ 1 := eventually_ne_nhds hρ1
  have hall := hmap.eventually (hlocζ.and (hre.and (hn0.and hn1)))
  set w : ℂ → ℂ := fun z => I ^ k * (xiUnit (1 / 2 + I * z) * v (1 / 2 + I * z)) with hw
  have hlocw : riemannXiHat =ᶠ[𝓝 γ] fun z => (z - γ) ^ k * w z := by
    filter_upwards [hall] with z hz
    obtain ⟨hζ, hre', hz0, hz1⟩ := hz
    rw [riemannXiHat_eq_xiUnit_mul_zeta hre' hz0 hz1, hζ]
    have e : 1 / 2 + I * z - ρ = I * (z - γ) := by rw [← hsγ]; ring
    rw [e, mul_pow]; simp only [hw]; ring
  have hxiU : AnalyticAt ℂ xiUnit ρ := analyticAt_xiUnit hnt.2.1
  have hcw : ContinuousAt w γ := by
    have h1 : ContinuousAt (fun z : ℂ => xiUnit (1 / 2 + I * z)) γ :=
      (hxiU.continuousAt.comp_of_eq (by fun_prop) hsγ)
    have h2 : ContinuousAt (fun z : ℂ => v (1 / 2 + I * z)) γ :=
      (hv.continuousAt.comp_of_eq (by fun_prop) hsγ)
    exact continuousAt_const.mul (h1.mul h2)
  have hw0 : w γ ≠ 0 := by
    simp only [hw, hsγ]
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
      (mul_ne_zero (xiUnit_ne_zero hρ0 hρ1 hnt.2.1) hv0)
  obtain ⟨hmk, huw⟩ := local_factor_unique hu.continuousAt hcw hu0 hw0 hlocΞ hlocw
  refine ⟨hmk, ?_⟩
  rw [huw]; simp only [hw, hsγ, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]

/-! ## Elementary lower bounds -/

theorem cosh_sub_cosh_ge {A B : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) :
    (A ^ 2 - B ^ 2) / 2 ≤ Real.cosh A - Real.cosh B := by
  have hftc : ∫ x in B..A, Real.sinh x = Real.cosh A - Real.cosh B :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_cosh x)
      (Real.continuous_sinh.intervalIntegrable _ _)
  rw [← hftc, ← integral_id]
  exact intervalIntegral.integral_mono_on hBA (continuous_id.intervalIntegrable _ _)
    (Real.continuous_sinh.intervalIntegrable _ _)
    (fun x hx => Real.self_le_sinh_iff.mpr (hB.trans hx.1))

/-- The polar symbol is bounded below on the strip: `|cos(sz) - cosh(s/2)| ≥ s²(1-4 Im z²)/8`. -/
theorem norm_polarSymbol_ge {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    s ^ 2 * (1 - 4 * z.im ^ 2) / 8 ≤ ‖polarSymbol s z‖ := by
  have hre : (polarSymbol s z).re = Real.cosh (s * z.im) * Real.cos (s * z.re) - Real.cosh (s / 2) := by
    unfold polarSymbol
    simp only [Complex.sub_re, Complex.div_re, Complex.add_re, Complex.exp_re, Complex.ofReal_re]
    have h1 : (I * z * (s : ℂ)).re = -(s * z.im) := by simp [Complex.mul_re]; ring
    have h2 : (I * z * (s : ℂ)).im = s * z.re := by simp [Complex.mul_im]; ring
    have h3 : (-(I * z * (s : ℂ))).re = s * z.im := by rw [Complex.neg_re, h1]; ring
    have h4 : (-(I * z * (s : ℂ))).im = -(s * z.re) := by rw [Complex.neg_im, h2]
    rw [h1, h2, h3, h4, Real.cos_neg]
    simp only [Real.cosh_eq]
    norm_num
    ring
  have hc : Real.cosh (s * z.im) * Real.cos (s * z.re) ≤ Real.cosh (s * z.im) :=
    mul_le_of_le_one_right (Real.cosh_pos _).le (Real.cos_le_one _)
  have hB : |s * z.im| ≤ s / 2 := by rw [abs_mul, abs_of_nonneg hs]; nlinarith [abs_nonneg z.im]
  have hlow := cosh_sub_cosh_ge (abs_nonneg (s * z.im)) hB
  rw [Real.cosh_abs] at hlow
  have hsq : |s * z.im| ^ 2 = s ^ 2 * z.im ^ 2 := by rw [sq_abs]; ring
  rw [hsq] at hlow
  calc s ^ 2 * (1 - 4 * z.im ^ 2) / 8 = ((s / 2) ^ 2 - s ^ 2 * z.im ^ 2) / 2 := by ring
    _ ≤ Real.cosh (s / 2) - Real.cosh (s * z.im) := hlow
    _ ≤ -(polarSymbol s z).re := by rw [hre]; linarith
    _ ≤ |(polarSymbol s z).re| := neg_le_abs _
    _ ≤ ‖polarSymbol s z‖ := Complex.abs_re_le_norm _

/-- `|Γ(1+iy)|² = πy / sinh(πy)`. -/
theorem norm_Gamma_one_add_I_mul_sq {y : ℝ} (hy : 0 < y) :
    ‖Complex.Gamma (1 + I * y)‖ ^ 2 = π * y / Real.sinh (π * y) := by
  have hIy : I * (y : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hy.ne')
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (I * y)
  have hadd : Complex.Gamma (1 + I * y) = I * y * Complex.Gamma (I * y) := by
    rw [add_comm]; exact Complex.Gamma_add_one _ hIy
  have hconj : Complex.Gamma (1 - I * y) = (starRingEnd ℂ) (Complex.Gamma (1 + I * y)) := by
    rw [← Complex.Gamma_conj]; congr 1; simp [map_add, map_mul, Complex.conj_ofReal]; ring
  have hsin : Complex.sin (π * (I * y)) = Real.sinh (π * y) * I := by
    rw [show (π : ℂ) * (I * y) = ((π * y : ℝ) : ℂ) * I by push_cast; ring, Complex.sin_mul_I,
      ← Complex.ofReal_sinh]
  have hsh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have key : Complex.Gamma (1 + I * y) * (starRingEnd ℂ) (Complex.Gamma (1 + I * y)) =
      ((π * y / Real.sinh (π * y) : ℝ) : ℂ) := by
    rw [← hconj, hadd, mul_assoc, hrefl, hsin]
    push_cast
    field_simp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at key
  exact_mod_cast key

theorem norm_Gamma_one_add_I_mul_sq_le {y : ℝ} (hy : 1 ≤ y) :
    ‖Complex.Gamma (1 + I * y)‖ ^ 2 ≤ 4 * π * y * Real.exp (-(π * y)) := by
  rw [norm_Gamma_one_add_I_mul_sq (by linarith)]
  have hx : 1 ≤ π * y := by nlinarith [Real.pi_gt_three]
  have hsinh : Real.exp (π * y) / 4 ≤ Real.sinh (π * y) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-(π * y)) ≤ Real.exp (π * y) / 2 := by
      have : Real.exp (-(π * y)) * Real.exp (π * y) = 1 := by rw [← Real.exp_add]; simp
      have h2 : 2 ≤ Real.exp (π * y) := by
        have := Real.add_one_le_exp (π * y); linarith
      nlinarith [Real.exp_pos (π * y), Real.exp_pos (-(π * y))]
    linarith
  have hpos : 0 < Real.exp (π * y) / 4 := by positivity
  rw [div_le_iff₀ (hpos.trans_le hsinh)]
  calc π * y ≤ 4 * π * y * Real.exp (-(π * y)) * (Real.exp (π * y) / 4) := by
        rw [show 4 * π * y * Real.exp (-(π * y)) * (Real.exp (π * y) / 4) =
          π * y * (Real.exp (-(π * y)) * Real.exp (π * y)) by ring, ← Real.exp_add]; simp
    _ ≤ 4 * π * y * Real.exp (-(π * y)) * Real.sinh (π * y) := by gcongr

theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp [le_abs_self]
  have h2 : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp [neg_le_abs]
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, show ‖(2 : ℂ)‖ = 2 by simp]
  calc ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2
      ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by gcongr
    _ = Real.exp |z.im| := by ring

/-- `|Γ(a + iy)|² ≤ e^{3/2} · 4π y e^{-πy}` for `1/2 ≤ a ≤ 1`, `y ≥ 4`. -/
theorem norm_Gamma_vertical_sq_le {a y : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) (hy : 4 ≤ y) :
    ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
      Real.exp (3 / 2) * (4 * π * y * Real.exp (-(π * y))) := by
  have hr := norm_Gamma_vertical_le_rpow_mul (a := a) (b := 1) (y := y) (by linarith) ha1 hy
  have hpow : y ^ (a - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hexp : Real.exp (6 * (1 - a) / y) ≤ Real.exp (3 / 4) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h1 : ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp (3 / 4) * ‖Complex.Gamma ((1 : ℝ) + (y : ℂ) * I)‖ := by
    refine hr.trans ?_
    calc y ^ (a - 1) * Real.exp (6 * (1 - a) / y) * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ 1 * Real.exp (3 / 4) * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
          gcongr
      _ = Real.exp (3 / 4) * ‖Complex.Gamma ((1 : ℝ) + (y : ℂ) * I)‖ := by ring
  have h2 := norm_Gamma_one_add_I_mul_sq_le (y := y) (by linarith)
  rw [show (1 : ℂ) + I * y = ((1 : ℝ) : ℂ) + (y : ℂ) * I by push_cast; ring] at h2
  have h3 : ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
      (Real.exp (3 / 4) * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (y : ℂ) * I)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow, ← Real.exp_nat_mul] at h3
  norm_num at h3
  calc ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ^ 2
      ≤ Real.exp (3 / 2) * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
        convert h3 using 2; norm_num
    _ ≤ Real.exp (3 / 2) * (4 * π * y * Real.exp (-(π * y))) := by gcongr

/-- **Lower bound for `Γ` in the critical strip.** For `0 < β < 1` and `|t| ≥ 8`,
`|Γ(β/2 + it/2)|² ≥ π e^{-π|t|/2} / (2 e^{3/2} |t|)`. -/
theorem norm_Gamma_half_sq_ge {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht : 8 ≤ |t|) :
    π * Real.exp (-(π * |t| / 2)) / (2 * Real.exp (3 / 2) * |t|) ≤
      ‖Complex.Gamma ((β : ℂ) / 2 + I * ((t : ℂ) / 2))‖ ^ 2 := by
  set w : ℂ := (β : ℂ) / 2 + I * ((t : ℂ) / 2) with hw
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  set y : ℝ := |t| / 2 with hy
  have hy4 : 4 ≤ y := by rw [hy]; linarith
  have hyt : |t| = 2 * y := by rw [hy]; ring
  -- the reflected factor
  have hone : ‖Complex.Gamma (1 - w)‖ = ‖Complex.Gamma (((1 - β / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
    have e : 1 - w = ((1 - β / 2 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * I := by
      rw [hw]; push_cast; ring
    rw [e]
    rcases le_or_gt 0 t with h0 | h0
    · have : ((1 - β / 2 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * I =
          (starRingEnd ℂ) (((1 - β / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
        rw [hy, abs_of_nonneg h0, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
          Complex.conj_I]
        push_cast; ring
      rw [this, Complex.Gamma_conj, Complex.norm_conj]
    · have : ((-(t / 2) : ℝ) : ℂ) = (y : ℂ) := by rw [hy, abs_of_neg h0]; push_cast; ring
      rw [this]
  have hG1 := norm_Gamma_vertical_sq_le (a := 1 - β / 2) (y := y) (by linarith) (by linarith) hy4
  rw [← hone] at hG1
  have hsin := norm_sin_le_exp_abs_im (π * w)
  have him : (↑π * w).im = π / 2 * t := by rw [hw]; simp [Complex.mul_im]; ring
  have hsim : |(↑π * w).im| = π * |t| / 2 := by
    rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < π / 2)]; ring
  rw [hsim] at hsin
  have hwint : ∀ m : ℕ, w ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp [hw] at this; linarith
  have hw1int : ∀ m : ℕ, 1 - w ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp [hw] at this; linarith
  have hGw : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwint
  have hG1w : Complex.Gamma (1 - w) ≠ 0 := Complex.Gamma_ne_zero hw1int
  have hsin0 : Complex.sin (π * w) ≠ 0 := by
    intro h; rw [h, div_zero] at hrefl; exact mul_ne_zero hGw hG1w hrefl
  have hnorm : ‖Complex.Gamma w‖ ^ 2 * ‖Complex.Gamma (1 - w)‖ ^ 2 =
      π ^ 2 / ‖Complex.sin (π * w)‖ ^ 2 := by
    have := congrArg (fun x => ‖x‖ ^ 2) hrefl
    simp only [norm_mul, norm_div, mul_pow, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos] at this
    exact this
  have hs2 : ‖Complex.sin (π * w)‖ ^ 2 ≤ Real.exp (π * |t|) := by
    calc ‖Complex.sin (π * w)‖ ^ 2 ≤ Real.exp (π * |t| / 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hsin 2
      _ = Real.exp (π * |t|) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsn : 0 < ‖Complex.sin (π * w)‖ ^ 2 := by positivity
  have hg1n : 0 < ‖Complex.Gamma (1 - w)‖ ^ 2 := by positivity
  have hmain : ‖Complex.Gamma w‖ ^ 2 = π ^ 2 / (‖Complex.sin (π * w)‖ ^ 2 *
      ‖Complex.Gamma (1 - w)‖ ^ 2) := by
    rw [eq_div_iff (by positivity)]
    have h := hnorm
    rw [eq_div_iff hsn.ne'] at h
    linear_combination h
  rw [hmain, le_div_iff₀ (by positivity)]
  have hB : ‖Complex.sin (π * w)‖ ^ 2 * ‖Complex.Gamma (1 - w)‖ ^ 2 ≤
      Real.exp (π * |t|) * (Real.exp (3 / 2) * (4 * π * y * Real.exp (-(π * y)))) :=
    mul_le_mul hs2 hG1 hg1n.le (Real.exp_pos _).le
  have hval : π * Real.exp (-(π * |t| / 2)) / (2 * Real.exp (3 / 2) * |t|) *
      (Real.exp (π * |t|) * (Real.exp (3 / 2) * (4 * π * y * Real.exp (-(π * y))))) = π ^ 2 := by
    rw [hyt]
    have e1 : Real.exp (-(π * (2 * y) / 2)) * Real.exp (π * (2 * y)) * Real.exp (-(π * y)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
    have hy0 : 0 < y := by linarith
    calc π * Real.exp (-(π * (2 * y) / 2)) / (2 * Real.exp (3 / 2) * (2 * y)) *
          (Real.exp (π * (2 * y)) * (Real.exp (3 / 2) * (4 * π * y * Real.exp (-(π * y)))))
        = π / (2 * Real.exp (3 / 2) * (2 * y)) * (Real.exp (3 / 2) * (4 * π * y)) *
          (Real.exp (-(π * (2 * y) / 2)) * Real.exp (π * (2 * y)) * Real.exp (-(π * y))) := by
          ring
      _ = π / (2 * Real.exp (3 / 2) * (2 * y)) * (Real.exp (3 / 2) * (4 * π * y)) := by
          rw [e1, mul_one]
      _ = π ^ 2 := by field_simp; ring
  calc π * Real.exp (-(π * |t| / 2)) / (2 * Real.exp (3 / 2) * |t|) *
        (‖Complex.sin (π * w)‖ ^ 2 * ‖Complex.Gamma (1 - w)‖ ^ 2)
      ≤ π * Real.exp (-(π * |t| / 2)) / (2 * Real.exp (3 / 2) * |t|) *
        (Real.exp (π * |t|) * (Real.exp (3 / 2) * (4 * π * y * Real.exp (-(π * y))))) := by
        gcongr
    _ = π ^ 2 := hval

/-- **The `ξ` unit is not smaller than `e^{-π|t|/4}` in the strip** (`|t| ≥ 8`). -/
theorem exp_le_norm_xiUnit {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (ht : 8 ≤ |ρ.im|) :
    Real.exp (-(π * |ρ.im| / 4)) ≤ ‖xiUnit ρ‖ := by
  set β := ρ.re
  set t := ρ.im
  have hρ : ρ / 2 = (β : ℂ) / 2 + I * ((t : ℂ) / 2) := by
    conv_lhs => rw [← Complex.re_add_im ρ]
    ring
  have hG := norm_Gamma_half_sq_ge hre0 hre1 ht
  rw [← hρ] at hG
  have hpoly : t ^ 2 / 2 ≤ ‖ρ * (ρ - 1) / 2‖ := by
    rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
    have h1 : |t| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    have h2 : |t| ≤ ‖ρ - 1‖ := by
      have := Complex.abs_im_le_norm (ρ - 1); simpa using this
    have : t ^ 2 = |t| * |t| := by rw [← sq_abs]; ring
    rw [this]
    gcongr
  have hpi : π ^ (-(1 : ℝ) / 2) ≤ ‖(π : ℂ) ^ (-ρ / 2)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
    simp; linarith
  have hunit : ‖xiUnit ρ‖ = ‖ρ * (ρ - 1) / 2‖ * ‖(π : ℂ) ^ (-ρ / 2)‖ * ‖Complex.Gamma (ρ / 2)‖ := by
    unfold xiUnit; rw [Complex.Gammaℝ_def, norm_mul, norm_mul, mul_assoc]
  have hpi2 : (π ^ (-(1 : ℝ) / 2)) ^ 2 = π⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num
    rw [Real.rpow_neg_one]
  have hsq : Real.exp (-(π * |t| / 2)) ≤ ‖xiUnit ρ‖ ^ 2 := by
    rw [hunit, mul_pow, mul_pow]
    have ht0 : 0 < |t| := by linarith
    have a1 : (t ^ 2 / 2) ^ 2 ≤ ‖ρ * (ρ - 1) / 2‖ ^ 2 := pow_le_pow_left₀ (by positivity) hpoly 2
    have a2 : π⁻¹ ≤ ‖(π : ℂ) ^ (-ρ / 2)‖ ^ 2 := by
      rw [← hpi2]; exact pow_le_pow_left₀ (by positivity) hpi 2
    have hcomb : (t ^ 2 / 2) ^ 2 * π⁻¹ *
        (π * Real.exp (-(π * |t| / 2)) / (2 * Real.exp (3 / 2) * |t|)) ≤
        ‖ρ * (ρ - 1) / 2‖ ^ 2 * ‖(π : ℂ) ^ (-ρ / 2)‖ ^ 2 * ‖Complex.Gamma (ρ / 2)‖ ^ 2 := by
      gcongr
    refine le_trans ?_ hcomb
    have ht4 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have he : Real.exp (3 / 2) ≤ 5 := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp (1 / 2) ≤ 17 / 10 := by
        have := Real.exp_bound' (x := 1 / 2) (by norm_num) (by norm_num) (n := 3) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
      have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
      rw [this]
      nlinarith [Real.exp_pos 1, Real.exp_pos (1 / 2)]
    have hval : (t ^ 2 / 2) ^ 2 * π⁻¹ *
        (π * Real.exp (-(π * |t| / 2)) / (2 * Real.exp (3 / 2) * |t|)) =
        |t| ^ 3 / (8 * Real.exp (3 / 2)) * Real.exp (-(π * |t| / 2)) := by
      rw [ht4]; field_simp; ring
    rw [hval]
    have hbig : 1 ≤ |t| ^ 3 / (8 * Real.exp (3 / 2)) := by
      rw [le_div_iff₀ (by positivity)]
      have : (8 : ℝ) ^ 3 ≤ |t| ^ 3 := pow_le_pow_left₀ (by norm_num) ht 3
      nlinarith
    nlinarith [Real.exp_pos (-(π * |t| / 2))]
  have hexp2 : Real.exp (-(π * |t| / 2)) = Real.exp (-(π * |t| / 4)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp2] at hsq
  exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) hsq

/-! ## The flatness law for `ζ` -/

theorem norm_kernel_at_γ₀_ge (D : OffLinePairData) :
    ‖D.u₀ D.γ₀‖ ≤ ‖paperFT D.kernel D.γ₀‖ := by
  rw [D.kernel_at_γ₀, norm_div, norm_pow]
  have hd : ‖D.γ₀ - D.γ₁‖ = 2 * |D.γ₀.im| := by
    have : D.γ₀ - D.γ₁ = ((2 * D.γ₀.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [OffLinePairData.γ₁]; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_two]
  have hle : ‖D.γ₀ - D.γ₁‖ ^ D.m₁ ≤ 1 := by
    rw [hd]; exact pow_le_one₀ (by positivity) (by linarith [D.him2])
  have hpos : 0 < ‖D.γ₀ - D.γ₁‖ ^ D.m₁ := by
    rw [hd]; have := abs_pos.mpr D.him; positivity
  rw [le_div_iff₀ hpos]
  exact mul_le_of_le_one_right (norm_nonneg _) hle

theorem norm_kernel_at_γ₁_ge (D : OffLinePairData) :
    ‖D.u₁ D.γ₁‖ ≤ ‖paperFT D.kernel D.γ₁‖ := by
  rw [D.kernel_at_γ₁, norm_div, norm_pow]
  have hd : ‖D.γ₁ - D.γ₀‖ = 2 * |D.γ₀.im| := by
    have : D.γ₁ - D.γ₀ = ((-(2 * D.γ₀.im) : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [OffLinePairData.γ₁]; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_mul, abs_two]
  have hle : ‖D.γ₁ - D.γ₀‖ ^ D.m₀ ≤ 1 := by
    rw [hd]; exact pow_le_one₀ (by positivity) (by linarith [D.him2])
  have hpos : 0 < ‖D.γ₁ - D.γ₀‖ ^ D.m₀ := by
    rw [hd]; have := abs_pos.mpr D.him; positivity
  rw [le_div_iff₀ hpos]
  exact mul_le_of_le_one_right (norm_nonneg _) hle

/-- **Flatness law for `ζ`.** There is an absolute constant `K` such that, if the level-`a` Hodge
index holds (`a ≥ 1`), then for every nontrivial zero `ρ₀ = β₀ + it₀` off the critical line with
`|t₀| ≥ 8`, and its mirror `ρ₀' = 1 - conj ρ₀`, the leading Taylor coefficients `v, v'` of `ζ`
(`ζ(s) = (s-ρ)^k v(s)`) satisfy

`|v(ρ₀)| |v'(ρ₀')| ≤ K 4^{k+k'} (1 + 1/|β₀ - 1/2|)² (1+|γ₀|)² (β₀(1-β₀))⁻² e^{a/2} e^{π|t₀|/2}`
`  · ε_Φ(a) · G_Φ`,

where `ε_Φ(a) = ∫_{|u| ≥ a-3/8} ‖Φ‖ e^{(1/2 + 3(k+k')/2)|u|}` is the tail of Riemann's kernel. -/
theorem hodgeIndex_zeta_flatness :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : ℝ}, 1 ≤ a → HodgeIndexAtLevel zetaZeroConfig a →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → ρ₀.re ≠ 1 / 2 → 8 ≤ |ρ₀.im| →
      ∀ {k k' : ℕ} {v v' : ℂ → ℂ}, AnalyticAt ℂ v ρ₀ → v ρ₀ ≠ 0 →
        (∀ᶠ s in 𝓝 ρ₀, riemannZeta s = (s - ρ₀) ^ k * v s) →
        AnalyticAt ℂ v' (Zeta23.reflect ρ₀) → v' (Zeta23.reflect ρ₀) ≠ 0 →
        (∀ᶠ s in 𝓝 (Zeta23.reflect ρ₀), riemannZeta s = (s - Zeta23.reflect ρ₀) ^ k' * v' s) →
        ‖v ρ₀‖ * ‖v' (Zeta23.reflect ρ₀)‖ ≤
          K * (2 ^ (k + k')) ^ 2 * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
            (1 / (ρ₀.re * (1 - ρ₀.re))) ^ 2 * Real.exp (a / 2) * Real.exp (π * |ρ₀.im| / 2) *
            expTail Φ (1 / 2 + 3 / 2 * ((k + k' : ℕ) : ℝ)) (a - 1 / 4 - OffLinePairData.sh) *
            expTail Φ (1 / 2 + 3 / 2 * ((k + k' : ℕ) : ℝ)) 0 := by
  obtain ⟨C, hC, hflat⟩ := OffLinePairData.flatness
  refine ⟨128 ^ 2 * C, by positivity, fun {a} ha hH {ρ₀} hρ₀ hoff ht {k k' v v'} hv hv0 hloc
    hv' hv'0 hloc' => ?_⟩
  obtain ⟨D, hD⟩ := OffLinePairData.exists_offLinePairData hρ₀ hoff
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  set ρ₁ := Zeta23.reflect ρ₀ with hρ₁
  have hρ₁m : ρ₁ ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem ρ₀ hρ₀
  have hγ₁ : gammaOf ρ₁ = D.γ₁ := by rw [hρ₁, gammaOf_reflect', ← hD]; rfl
  -- transfer the leading coefficients
  have hloc₀ : riemannXiHat =ᶠ[𝓝 (gammaOf ρ₀)] fun z => (z - gammaOf ρ₀) ^ D.m₀ * D.u₀ z := by
    rw [← hD]; exact D.hloc₀
  have hloc₁ : riemannXiHat =ᶠ[𝓝 (gammaOf ρ₁)] fun z => (z - gammaOf ρ₁) ^ D.m₁ * D.u₁ z := by
    rw [hγ₁]; exact D.hloc₁
  have hu₀ : AnalyticAt ℂ D.u₀ (gammaOf ρ₀) := by rw [← hD]; exact D.hu₀
  have hu₁ : AnalyticAt ℂ D.u₁ (gammaOf ρ₁) := by rw [hγ₁]; exact D.hu₁
  have hu₀0 : D.u₀ (gammaOf ρ₀) ≠ 0 := by rw [← hD]; exact D.hu₀0
  have hu₁0 : D.u₁ (gammaOf ρ₁) ≠ 0 := by rw [hγ₁]; exact D.hu₁0
  obtain ⟨hm₀, hn₀⟩ := norm_leading_riemannXiHat hρ₀ hv hv0 hloc hu₀ hu₀0 hloc₀
  obtain ⟨hm₁, hn₁⟩ := norm_leading_riemannXiHat hρ₁m hv' hv'0 hloc' hu₁ hu₁0 hloc₁
  rw [← hD] at hn₀
  rw [hγ₁] at hn₁
  -- the flatness law for the pair
  have hF := hflat D hρ₀ hD.symm ha hH
  have hn : D.n = k + k' := by unfold OffLinePairData.n; rw [hm₀, hm₁]
  rw [hn] at hF
  -- lower bounds for the node values
  have hβ : D.γ₀.im = 1 / 2 - ρ₀.re := by rw [hD, WeilEF.gammaOf_im]
  have hP : ∀ z : ℂ, z.im = D.γ₀.im ∨ z.im = -D.γ₀.im →
      ρ₀.re * (1 - ρ₀.re) / 128 ≤ ‖polarSymbol OffLinePairData.sh z‖ := by
    intro z hz
    have hzi : |z.im| ≤ 1 / 2 := by
      rcases hz with h | h
      · rw [h]; exact D.him2
      · rw [h, abs_neg]; exact D.him2
    have h := norm_polarSymbol_ge (s := OffLinePairData.sh) OffLinePairData.sh_pos.le hzi
    have hsq : z.im ^ 2 = D.γ₀.im ^ 2 := by rcases hz with h | h <;> rw [h]; ring
    rw [hsq, hβ] at h
    have e : OffLinePairData.sh ^ 2 * (1 - 4 * (1 / 2 - ρ₀.re) ^ 2) / 8 =
        ρ₀.re * (1 - ρ₀.re) / 128 := by rw [show OffLinePairData.sh = 1 / 8 from rfl]; ring
    linarith
  have hP₀ := hP D.γ₀ (Or.inl rfl)
  have hP₁ := hP D.γ₁ (Or.inr (by simp [OffLinePairData.γ₁]))
  have hxi₀ := exp_le_norm_xiUnit hnt.2.1 hnt.2.2 ht
  have hre₁ : ρ₁.re = 1 - ρ₀.re := by simp [hρ₁, Zeta23.reflect]
  have him₁ : ρ₁.im = ρ₀.im := by simp [hρ₁, Zeta23.reflect]
  have hxi₁ := exp_le_norm_xiUnit (ρ := ρ₁) (by rw [hre₁]; linarith [hnt.2.2])
    (by rw [hre₁]; linarith [hnt.2.1]) (by rw [him₁]; exact ht)
  rw [him₁] at hxi₁
  have hk₀ := norm_kernel_at_γ₀_ge D
  have hk₁ := norm_kernel_at_γ₁_ge D
  have hq0 : 0 < ρ₀.re * (1 - ρ₀.re) := mul_pos hnt.2.1 (by linarith [hnt.2.2])
  set E := Real.exp (-(π * |ρ₀.im| / 4)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- X₀ X₁ ≥ (q/128)² E² |v| |v'|
  have hX : (ρ₀.re * (1 - ρ₀.re) / 128) ^ 2 * (E * ‖v ρ₀‖) * (E * ‖v' ρ₁‖) ≤
      ‖polarSymbol OffLinePairData.sh D.γ₀ * paperFT D.kernel D.γ₀‖ *
        ‖polarSymbol OffLinePairData.sh D.γ₁ * paperFT D.kernel D.γ₁‖ := by
    rw [norm_mul, norm_mul]
    have a0 : E * ‖v ρ₀‖ ≤ ‖paperFT D.kernel D.γ₀‖ := by
      refine le_trans ?_ hk₀
      rw [hn₀]; exact mul_le_mul_of_nonneg_right hxi₀ (norm_nonneg _)
    have a1 : E * ‖v' ρ₁‖ ≤ ‖paperFT D.kernel D.γ₁‖ := by
      refine le_trans ?_ hk₁
      rw [hn₁]; exact mul_le_mul_of_nonneg_right hxi₁ (norm_nonneg _)
    have hq : 0 ≤ ρ₀.re * (1 - ρ₀.re) / 128 := by positivity
    calc (ρ₀.re * (1 - ρ₀.re) / 128) ^ 2 * (E * ‖v ρ₀‖) * (E * ‖v' ρ₁‖)
        = ((ρ₀.re * (1 - ρ₀.re) / 128) * (E * ‖v ρ₀‖)) *
          ((ρ₀.re * (1 - ρ₀.re) / 128) * (E * ‖v' ρ₁‖)) := by ring
      _ ≤ (‖polarSymbol OffLinePairData.sh D.γ₀‖ * ‖paperFT D.kernel D.γ₀‖) *
          (‖polarSymbol OffLinePairData.sh D.γ₁‖ * ‖paperFT D.kernel D.γ₁‖) := by
        gcongr
  have hall := hX.trans hF
  have himγ : |D.γ₀.im| = |ρ₀.re - 1 / 2| := by rw [hβ, abs_sub_comm]
  rw [himγ, hD] at hall
  -- divide out
  have hEE : E * E * Real.exp (π * |ρ₀.im| / 2) = 1 := by
    rw [hE, ← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  set R := C * (2 ^ (k + k')) ^ 2 * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
    Real.exp (a / 2) * expTail Φ (1 / 2 + 3 / 2 * ((k + k' : ℕ) : ℝ)) (a - 1 / 4 - OffLinePairData.sh) *
    expTail Φ (1 / 2 + 3 / 2 * ((k + k' : ℕ) : ℝ)) 0 with hR
  have hall' : (ρ₀.re * (1 - ρ₀.re) / 128) ^ 2 * (E * E) * (‖v ρ₀‖ * ‖v' ρ₁‖) ≤ R := by
    have : (ρ₀.re * (1 - ρ₀.re) / 128) ^ 2 * (E * E) * (‖v ρ₀‖ * ‖v' ρ₁‖) =
        (ρ₀.re * (1 - ρ₀.re) / 128) ^ 2 * (E * ‖v ρ₀‖) * (E * ‖v' ρ₁‖) := by ring
    rw [this]; exact hall
  have hfac : 0 < (ρ₀.re * (1 - ρ₀.re) / 128) ^ 2 * (E * E) := by positivity
  have hmain : ‖v ρ₀‖ * ‖v' ρ₁‖ ≤ R / ((ρ₀.re * (1 - ρ₀.re) / 128) ^ 2 * (E * E)) := by
    rw [le_div_iff₀ hfac]; linarith
  refine hmain.trans (le_of_eq ?_)
  have hE2 : E * E = (Real.exp (π * |ρ₀.im| / 2))⁻¹ := by
    rw [hE, ← Real.exp_add, ← Real.exp_neg]; ring_nf
  rw [hR, hE2]
  field_simp

/-! ## The tail of Riemann's kernel -/

local notation "Mθ" => jacobiThetaTailConstant

/-- Pointwise double-exponential bound: for `0 ≤ X ≤ v` with `e^{2X} ≥ 3`,
`‖Φ(v)‖ e^{cv} ≤ 20 Mθ e^π e^{(c+9/2)X - πe^{2X}} e^{-(2πe^{2X} - c - 9/2)(v - X)}`. -/
theorem norm_riemannPhiKernel_mul_exp_tail_le {c X v : ℝ} (hX : 3 ≤ Real.exp (2 * X))
    (hXv : X ≤ v) :
    ‖Φ v‖ * Real.exp (c * v) ≤ 20 * Mθ * Real.exp π *
      Real.exp ((c + 9 / 2) * X - π * Real.exp (2 * X)) *
      Real.exp (-(2 * π * Real.exp (2 * X) - c - 9 / 2) * (v - X)) := by
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  have hv3 : 3 ≤ Real.exp (2 * v) := hX.trans (Real.exp_le_exp.mpr (by linarith))
  have h1 := norm_riemannPhiKernel_le hv3
  set y := Real.exp (2 * v) with hy
  have hy1 : 1 ≤ y := by linarith
  have hpoly : 3 * y + 2 * y ^ 2 ≤ 5 * y ^ 2 := by nlinarith
  have hy2 : y ^ 2 = Real.exp (4 * v) := by rw [hy, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hgrow : Real.exp (2 * X) * (1 + 2 * (v - X)) ≤ y := by
    have h := Real.add_one_le_exp (2 * (v - X))
    have := mul_le_mul_of_nonneg_left h (Real.exp_pos (2 * X)).le
    rw [← Real.exp_add, show 2 * X + 2 * (v - X) = 2 * v by ring] at this
    linarith
  have hexp : v / 2 + 4 * v + c * v - π * y ≤ (c + 9 / 2) * X - π * Real.exp (2 * X) +
      (-(2 * π * Real.exp (2 * X) - c - 9 / 2) * (v - X)) := by
    nlinarith [Real.pi_pos, Real.exp_pos (2 * X)]
  calc ‖Φ v‖ * Real.exp (c * v)
      ≤ (4 * Mθ * Real.exp π * Real.exp (v / 2) * (3 * y + 2 * y ^ 2) * Real.exp (-π * y)) *
          Real.exp (c * v) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ (4 * Mθ * Real.exp π * Real.exp (v / 2) * (5 * y ^ 2) * Real.exp (-π * y)) *
          Real.exp (c * v) := by gcongr
    _ = 20 * Mθ * Real.exp π * Real.exp (v / 2 + 4 * v + c * v - π * y) := by
        rw [hy2]
        rw [show v / 2 + 4 * v + c * v - π * y = v / 2 + 4 * v + c * v + (-π * y) by ring,
          Real.exp_add, Real.exp_add, Real.exp_add]
        ring
    _ ≤ 20 * Mθ * Real.exp π * Real.exp ((c + 9 / 2) * X - π * Real.exp (2 * X) +
          (-(2 * π * Real.exp (2 * X) - c - 9 / 2) * (v - X))) := by
        gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem integrable_exp_neg_mul_abs {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun u : ℝ => Real.exp (-(κ * |u|))) := by
  have h := (integrable_exp_neg_abs).comp_mul_left' hκ.ne'
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [abs_mul, abs_of_pos hκ]

theorem integral_exp_neg_mul_abs {κ : ℝ} (hκ : 0 < κ) :
    ∫ u : ℝ, Real.exp (-(κ * |u|)) = 2 / κ := by
  have h := integral_comp_abs (f := fun v => Real.exp (-(κ * v)))
  rw [h]
  have := integral_exp_mul_Ioi (a := -κ) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at this
  rw [show (fun x : ℝ => Real.exp (-(κ * x))) = fun x => Real.exp (-κ * x) by
    funext x; ring_nf, this]
  field_simp

/-- **Tail of Riemann's kernel.** For `e^{2X} ≥ 3` and `κ = 2πe^{2X} - c - 9/2 > 0`,
`∫_{|u| ≥ X} ‖Φ(u)‖ e^{c|u|} du ≤ 80 Mθ e^π e^{(c+9/2)X - πe^{2X}} / κ`. -/
theorem expTail_riemannPhiKernel_le {c X : ℝ} (hX : 3 ≤ Real.exp (2 * X))
    (hκ : c + 9 / 2 < 2 * π * Real.exp (2 * X)) :
    expTail Φ c X ≤ 80 * Mθ * Real.exp π *
      Real.exp ((c + 9 / 2) * X - π * Real.exp (2 * X)) / (2 * π * Real.exp (2 * X) - c - 9 / 2) := by
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  set κ := 2 * π * Real.exp (2 * X) - c - 9 / 2 with hκdef
  have hκ0 : 0 < κ := by rw [hκdef]; linarith
  set B := 20 * Mθ * Real.exp π * Real.exp ((c + 9 / 2) * X - π * Real.exp (2 * X)) with hB
  have hB0 : 0 ≤ B := by positivity
  have i1 : Integrable (fun u : ℝ => Real.exp (-(κ * |u - X|))) :=
    (integrable_exp_neg_mul_abs hκ0).comp_sub_right X
  have i2 : Integrable (fun u : ℝ => Real.exp (-(κ * |u + X|))) :=
    (integrable_exp_neg_mul_abs hκ0).comp_add_right X
  have hpt : ∀ u : ℝ, {u : ℝ | X ≤ |u|}.indicator (fun u => ‖Φ u‖ * Real.exp (c * |u|)) u ≤
      B * (Real.exp (-(κ * |u - X|)) + Real.exp (-(κ * |u + X|))) := by
    intro u
    have hsum : 0 ≤ B * (Real.exp (-(κ * |u - X|)) + Real.exp (-(κ * |u + X|))) := by positivity
    simp only [indicator, mem_setOf_eq]
    split_ifs with h
    · rw [← norm_riemannPhiKernel_abs u]
      have hb := norm_riemannPhiKernel_mul_exp_tail_le (c := c) hX h
      have hκe : -(2 * π * Real.exp (2 * X) - c - 9 / 2) * (|u| - X) = -(κ * (|u| - X)) := by
        rw [hκdef]; ring
      have hb' : ‖Φ |u|‖ * Real.exp (c * |u|) ≤ B * Real.exp (-(κ * (|u| - X))) := by
        rw [hκe] at hb; rw [hB]; exact hb
      refine hb'.trans ?_
      have hd : |u| - X = |u - X| ∨ |u| - X = |u + X| := by
        rcases le_or_gt 0 u with h0 | h0
        · left; rw [abs_of_nonneg h0, abs_of_nonneg (by rw [abs_of_nonneg h0] at h; linarith)]
        · right; rw [abs_of_neg h0, abs_of_nonpos (by rw [abs_of_neg h0] at h; linarith)]; ring
      rcases hd with hd | hd <;> rw [hd] <;> gcongr <;> nlinarith [Real.exp_pos (-(κ * |u + X|)),
        Real.exp_pos (-(κ * |u - X|))]
    · exact hsum
  unfold expTail
  calc ∫ u, {u : ℝ | X ≤ |u|}.indicator (fun u => ‖Φ u‖ * Real.exp (c * |u|)) u
      ≤ ∫ u, B * (Real.exp (-(κ * |u - X|)) + Real.exp (-(κ * |u + X|))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => by
          simp only [indicator]; split_ifs <;> positivity) ((i1.add i2).const_mul B)
          (Eventually.of_forall hpt)
    _ = B * (2 / κ + 2 / κ) := by
        rw [integral_const_mul, integral_add i1 i2]
        have e1 : ∫ u : ℝ, Real.exp (-(κ * |u - X|)) = 2 / κ := by
          rw [integral_sub_right_eq_self (fun u => Real.exp (-(κ * |u|))) X]
          exact integral_exp_neg_mul_abs hκ0
        have e2 : ∫ u : ℝ, Real.exp (-(κ * |u + X|)) = 2 / κ := by
          rw [integral_add_right_eq_self (fun u => Real.exp (-(κ * |u|))) X]
          exact integral_exp_neg_mul_abs hκ0
        rw [e1, e2]
    _ = 80 * Mθ * Real.exp π * Real.exp ((c + 9 / 2) * X - π * Real.exp (2 * X)) / κ := by
        rw [hB]; field_simp; ring

/-- **Explicit flatness law for `ζ`.** There is an absolute constant `K` such that, if the
level-`a` Hodge index holds (`a ≥ 1`), then every nontrivial zero `ρ₀ = β₀ + it₀` off the critical
line with `|t₀| ≥ 8`, orders `k, k'` at `ρ₀` and its mirror, `N = k + k'`, `λ = 1/2 + 3N/2`,
`X = a - 3/8` and `λ + 11/2 ≤ 2πe^{2X}`, satisfies

`|v(ρ₀)| |v'(ρ₀')| ≤ K 4^N (1 + 1/|β₀-1/2|)² (1+|γ₀|)² (β₀(1-β₀))⁻² e^{a/2} G_Φ(N)`
`  · exp((π/2)|t₀| + (λ+9/2)X - π e^{2X})`,

with `G_Φ(N) = ∫ ‖Φ‖ e^{λ|u|}`. The exponent is negative as soon as `|t₀| < 2e^{2a-3/4} - O(Na)`:
below that height, the Hodge index at level `a` forces every off-line zero and its mirror to be
super-exponentially flat. -/
theorem hodgeIndex_zeta_flatness_explicit :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : ℝ}, 1 ≤ a → HodgeIndexAtLevel zetaZeroConfig a →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → ρ₀.re ≠ 1 / 2 → 8 ≤ |ρ₀.im| →
      ∀ {k k' : ℕ} {v v' : ℂ → ℂ}, AnalyticAt ℂ v ρ₀ → v ρ₀ ≠ 0 →
        (∀ᶠ s in 𝓝 ρ₀, riemannZeta s = (s - ρ₀) ^ k * v s) →
        AnalyticAt ℂ v' (Zeta23.reflect ρ₀) → v' (Zeta23.reflect ρ₀) ≠ 0 →
        (∀ᶠ s in 𝓝 (Zeta23.reflect ρ₀), riemannZeta s = (s - Zeta23.reflect ρ₀) ^ k' * v' s) →
        1 / 2 + 3 / 2 * ((k + k' : ℕ) : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) →
        ‖v ρ₀‖ * ‖v' (Zeta23.reflect ρ₀)‖ ≤
          K * 4 ^ (k + k') * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
            (1 / (ρ₀.re * (1 - ρ₀.re))) ^ 2 * Real.exp (a / 2) *
            expTail Φ (1 / 2 + 3 / 2 * ((k + k' : ℕ) : ℝ)) 0 *
            Real.exp (π * |ρ₀.im| / 2 + (1 / 2 + 3 / 2 * ((k + k' : ℕ) : ℝ) + 9 / 2) * (a - 3 / 8) -
              π * Real.exp (2 * (a - 3 / 8))) := by
  obtain ⟨K₀, hK₀, hflat⟩ := hodgeIndex_zeta_flatness
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  refine ⟨K₀ * (80 * Mθ * Real.exp π + 1), by positivity, fun {a} ha hH {ρ₀} hρ₀ hoff ht
    {k k' v v'} hv hv0 hloc hv' hv'0 hloc' hlam => ?_⟩
  have h := hflat ha hH hρ₀ hoff ht hv hv0 hloc hv' hv'0 hloc'
  set lam : ℝ := 1 / 2 + 3 / 2 * ((k + k' : ℕ) : ℝ) with hlamdef
  have hX : (a - 1 / 4 - OffLinePairData.sh) = a - 3 / 8 := by
    rw [show OffLinePairData.sh = 1 / 8 from rfl]; ring
  rw [hX] at h
  have hX3 : 3 ≤ Real.exp (2 * (a - 3 / 8)) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 2 * (a - 3 / 8)) (by linarith)
    nlinarith
  have hκ1 : 1 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) - lam - 9 / 2 := by linarith
  have htail := expTail_riemannPhiKernel_le (c := lam) hX3 (by linarith)
  have htail' : expTail Φ lam (a - 3 / 8) ≤ (80 * Mθ * Real.exp π + 1) *
      Real.exp ((lam + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))) := by
    refine htail.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ 80 * Mθ * Real.exp π *
        Real.exp ((lam + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))) := by positivity
    nlinarith [Real.exp_pos ((lam + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8)))]
  have hG0 : 0 ≤ expTail Φ lam 0 := expTail_nonneg _ _ _
  have hpow : ((2 : ℝ) ^ (k + k')) ^ 2 = 4 ^ (k + k') := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hpow] at h
  refine h.trans ?_
  set Pre := K₀ * 4 ^ (k + k') * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
    (1 / (ρ₀.re * (1 - ρ₀.re))) ^ 2 * Real.exp (a / 2) with hPre
  have hPre0 : 0 ≤ Pre := by positivity
  calc Pre * Real.exp (π * |ρ₀.im| / 2) * expTail Φ lam (a - 3 / 8) * expTail Φ lam 0
      ≤ Pre * Real.exp (π * |ρ₀.im| / 2) * ((80 * Mθ * Real.exp π + 1) *
          Real.exp ((lam + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8)))) *
          expTail Φ lam 0 := by gcongr
    _ = K₀ * (80 * Mθ * Real.exp π + 1) * 4 ^ (k + k') * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 *
          (1 + ‖gammaOf ρ₀‖) ^ 2 * (1 / (ρ₀.re * (1 - ρ₀.re))) ^ 2 * Real.exp (a / 2) *
          expTail Φ lam 0 * Real.exp (π * |ρ₀.im| / 2 + (lam + 9 / 2) * (a - 3 / 8) -
            π * Real.exp (2 * (a - 3 / 8))) := by
        rw [hPre, show π * |ρ₀.im| / 2 + (lam + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))
          = π * |ρ₀.im| / 2 + ((lam + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))) by ring,
          Real.exp_add]
        ring

end

end RHTower
