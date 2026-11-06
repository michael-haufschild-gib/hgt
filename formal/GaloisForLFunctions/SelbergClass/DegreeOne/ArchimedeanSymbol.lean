import GaloisForLFunctions.SelbergClass.DegreeOne.VerticalStirling
import GaloisForLFunctions.RHTower.SelbergClass.AsymmetricFunctionalEquation

/-!
# The archimedean symbol of a degree-one functional equation

Let `G` be a Gamma presentation of degree one, with conductor `q` and internal shift `θ`, and put
`s = σ + it`.  The functional equation writes `F(s)` as a Gamma quotient times the reflected series.
Multiplied by the Mellin factor `Γ(s)`, that quotient is

`Γ(s) Q^{1−2s} ∏ⱼ Γ(λⱼ(1−s)+μ̄ⱼ)/Γ(λⱼs+μⱼ) ~ c · e^{−πt/2} · (q/2π)^{−it} · t^{−iθ}`,   `t → +∞`,

with `c ≠ 0` (`exists_tendsto_symbol`).  All `t log t` phases and all powers of `t` cancel precisely
because `2Σλⱼ = 1`; this is what makes degree one the boundary case.
-/

set_option autoImplicit false

open Complex Filter Topology
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.SelbergClass.DegreeOne

noncomputable section

/-- The point `σ + it`. -/
abbrev linePoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

/-- With `x = λt`, the main term of `τ log τ − τ` at `τ = x + m` is `x log x − x + m log x`. -/
theorem tendsto_shiftedMainTerm_sub {lam : ℝ} (hlam : 0 < lam) (m : ℝ) :
    Tendsto (fun t : ℝ => ((lam * t + m) * Real.log (lam * t + m) - (lam * t + m)) -
      (lam * t * Real.log (lam * t) - lam * t + m * Real.log (lam * t))) atTop (𝓝 0) := by
  have hx : Tendsto (fun t : ℝ => lam * t) atTop atTop := tendsto_id.const_mul_atTop hlam
  have h1 : Tendsto (fun x : ℝ => x * Real.log (1 + m / x)) atTop (𝓝 m) := by
    refine Real.tendsto_mul_log_one_add_of_tendsto ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hdiv : Tendsto (fun x : ℝ => m / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun x : ℝ => Real.log (1 + m / x)) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 + 0 : ℝ) ≠ 0)).tendsto.comp
      (tendsto_const_nhds.add hdiv)
    simpa [Function.comp_def] using h
  have h3 := ((h1.add (h2.const_mul m)).sub_const m).comp hx
  simp only [mul_zero, add_zero, sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [hx.eventually_gt_atTop 0, hx.eventually_gt_atTop (-m)] with t ht ht'
  have hpos : 0 < lam * t + m := by linarith
  have hlog : Real.log (1 + m / (lam * t)) = Real.log (lam * t + m) - Real.log (lam * t) := by
    rw [← Real.log_div hpos.ne' ht.ne', add_div, div_self ht.ne']
  simp only [Function.comp_apply]
  rw [hlog]
  ring

/-- The conjugate shape against the shape: the modulus exponents subtract, the phases add. -/
theorem stirlingShape_div_conj (a a' : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    stirlingShape a τ / conj (stirlingShape a' τ) =
      cexp (I * ((π * (a + a' - 1) / 2 + 2 * (τ * Real.log τ - τ) : ℝ) : ℂ)) *
        ((τ ^ (a - a') : ℝ) : ℂ) := by
  have hE : conj (cexp (I * ((π * (a' - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ))) =
      cexp (-(I * ((π * (a' - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  unfold stirlingShape
  rw [map_mul, hE, Complex.conj_ofReal]
  have hp : τ ^ (a - a') = τ ^ (a - 1 / 2) / τ ^ (a' - 1 / 2) := by
    rw [← Real.rpow_sub hτ]
    congr 1
    ring
  have hexp : cexp (I * ((π * (a + a' - 1) / 2 + 2 * (τ * Real.log τ - τ) : ℝ) : ℂ)) =
      cexp (I * ((π * (a - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ)) /
        cexp (-(I * ((π * (a' - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ))) := by
    rw [← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [hexp, hp]
  have h1 : ((τ ^ (a' - 1 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ _).ne'
  have h2 : ((Real.exp (-(π * τ / 2)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have h3 := Complex.exp_ne_zero (-(I * ((π * (a' - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ)))
  push_cast
  field_simp

/-- The Gamma pair of one factor of the presentation, with its phase and power removed. -/
theorem tendsto_gamma_ratio (σ : ℝ) {lam : ℝ} (hlam : 0 < lam) (μ : ℂ) :
    Tendsto (fun t : ℝ =>
      (Complex.Gamma ((lam : ℂ) * (1 - linePoint σ t) + star μ) *
        (Complex.Gamma ((lam : ℂ) * linePoint σ t + μ))⁻¹) *
        cexp (I * ((2 * (lam * t * Real.log (lam * t) - lam * t +
          μ.im * Real.log (lam * t)) : ℝ) : ℂ)) *
        (((lam * t) ^ (-(lam * (1 - 2 * σ))) : ℝ) : ℂ)) atTop
      (𝓝 (cexp (I * ((-(π * (lam + 2 * μ.re - 1) / 2) : ℝ) : ℂ)))) := by
  set a : ℝ := lam * σ + μ.re with ha
  set a' : ℝ := lam * (1 - σ) + μ.re with ha'
  have hτ : Tendsto (fun t : ℝ => lam * t + μ.im) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hlam)
  have hg := (tendsto_Gamma_div_stirlingShape a).comp hτ
  have hg' := (tendsto_Gamma_div_stirlingShape a').comp hτ
  have hconj := (Complex.continuous_conj.tendsto _).comp hg'
  rw [Complex.conj_ofReal] at hconj
  have hsqrt : (Real.sqrt (2 * π) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hquot := hconj.mul (hg.inv₀ hsqrt)
  rw [mul_inv_cancel₀ hsqrt] at hquot
  -- the phase defect
  have hδ := tendsto_shiftedMainTerm_sub hlam μ.im
  have hδe : Tendsto (fun t : ℝ => cexp (I * ((-(2 * (((lam * t + μ.im) * Real.log (lam * t + μ.im) -
      (lam * t + μ.im)) - (lam * t * Real.log (lam * t) - lam * t + μ.im * Real.log (lam * t)))) :
      ℝ) : ℂ))) atTop (𝓝 1) := by
    have h := (Complex.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds (x := I)).mul ((Complex.continuous_ofReal.tendsto _).comp
        ((hδ.const_mul 2).neg)))
    simpa [Function.comp_def] using h
  -- the power defect
  have hratio : Tendsto (fun t : ℝ => (lam * t + μ.im) / (lam * t)) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun t : ℝ => μ.im / (lam * t)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hlam)
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hdiv
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  have hpow : Tendsto (fun t : ℝ => ((((lam * t + μ.im) / (lam * t)) ^ (lam * (1 - 2 * σ)) : ℝ) : ℂ))
      atTop (𝓝 1) := by
    have h := hratio.rpow_const (p := lam * (1 - 2 * σ)) (Or.inl one_ne_zero)
    rw [Real.one_rpow] at h
    have h' := (Complex.continuous_ofReal.tendsto _).comp h
    simpa [Function.comp_def] using h'
  have hall := ((hquot.mul_const (cexp (I * ((-(π * (lam + 2 * μ.re - 1) / 2) : ℝ) : ℂ)))).mul hδe).mul
    hpow
  simp only [one_mul, mul_one] at hall
  refine hall.congr' ?_
  filter_upwards [(tendsto_id.const_mul_atTop hlam).eventually_gt_atTop (0 : ℝ),
    hτ.eventually_gt_atTop (0 : ℝ)] with t ht hτt
  simp only [Function.comp_apply, id_eq] at ht ⊢
  set τ : ℝ := lam * t + μ.im with hτdef
  have hw : (lam : ℂ) * linePoint σ t + μ = (a : ℂ) + (τ : ℂ) * I := by
    apply Complex.ext <;> simp [linePoint, ha, hτdef]
  have hw' : (lam : ℂ) * (1 - linePoint σ t) + star μ = conj ((a' : ℂ) + (τ : ℂ) * I) := by
    apply Complex.ext <;> (simp [linePoint, ha', hτdef]; try ring)
  rw [hw, hw', Complex.Gamma_conj]
  have hS := stirlingShape_ne_zero a hτt
  have hS' : conj (stirlingShape a' τ) ≠ 0 :=
    (map_ne_zero _).mpr (stirlingShape_ne_zero a' hτt)
  have hshape := stirlingShape_div_conj a a' hτt
  have hee : a - a' = -(lam * (1 - 2 * σ)) := by
    rw [ha, ha']
    ring
  have haa : a + a' - 1 = lam + 2 * μ.re - 1 := by
    rw [ha, ha']
    ring
  rw [hee, haa] at hshape
  have hτpow : (((τ / (lam * t)) ^ (lam * (1 - 2 * σ)) : ℝ) : ℂ) *
      ((τ ^ (-(lam * (1 - 2 * σ))) : ℝ) : ℂ) = (((lam * t) ^ (-(lam * (1 - 2 * σ))) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.div_rpow hτt.le ht.le, Real.rpow_neg hτt.le, Real.rpow_neg ht.le]
    congr 1
    have h1 := Real.rpow_pos_of_pos hτt (lam * (1 - 2 * σ))
    have h2 := Real.rpow_pos_of_pos ht (lam * (1 - 2 * σ))
    field_simp
  have hphase : cexp (I * ((-(π * (lam + 2 * μ.re - 1) / 2) : ℝ) : ℂ)) *
      cexp (I * ((-(2 * ((τ * Real.log τ - τ) - (lam * t * Real.log (lam * t) - lam * t +
        μ.im * Real.log (lam * t)))) : ℝ) : ℂ)) *
      cexp (I * ((π * (lam + 2 * μ.re - 1) / 2 + 2 * (τ * Real.log τ - τ) : ℝ) : ℂ)) =
      cexp (I * ((2 * (lam * t * Real.log (lam * t) - lam * t +
        μ.im * Real.log (lam * t)) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [map_div₀, inv_div]
  rw [← hphase, ← hτpow]
  rw [div_eq_iff hS'] at hshape
  generalize cexp (I * ((π * (lam + 2 * μ.re - 1) / 2 + 2 * (τ * Real.log τ - τ) : ℝ) : ℂ)) = E₁ at *
  generalize cexp (I * ((-(π * (lam + 2 * μ.re - 1) / 2) : ℝ) : ℂ)) = E₂ at *
  generalize cexp (I * ((-(2 * ((τ * Real.log τ - τ) - (lam * t * Real.log (lam * t) - lam * t +
        μ.im * Real.log (lam * t)))) : ℝ) : ℂ)) = E₃ at *
  generalize ((τ ^ (-(lam * (1 - 2 * σ))) : ℝ) : ℂ) = P at *
  generalize (((τ / (lam * t)) ^ (lam * (1 - 2 * σ)) : ℝ) : ℂ) = P' at *
  generalize conj (Complex.Gamma ((a' : ℂ) + (τ : ℂ) * I)) = Γ₁ at *
  generalize Complex.Gamma ((a : ℂ) + (τ : ℂ) * I) = Γ₀ at *
  generalize conj (stirlingShape a' τ) = S₁ at *
  generalize stirlingShape a τ = S₀ at *
  subst hshape
  field_simp

/-- The product of `Γ(s)`, the positive exponential of `Q`, and all Gamma pairs. -/
def symbol (G : RHTower.SelbergGammaData) (σ t : ℝ) : ℂ :=
  Complex.Gamma (linePoint σ t) *
    (((G.Q : ℂ) ^ (1 - linePoint σ t) *
      ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - linePoint σ t) + star (G.mu j))) *
      (G.gammaFactor (linePoint σ t))⁻¹)

/-- `log (q/2π)` in terms of the presentation, at degree one. -/
theorem log_conductor_div (G : RHTower.SelbergGammaData) (hd : G.degree = 1) :
    Real.log (G.conductor / (2 * π)) =
      2 * Real.log G.Q + ∑ j, 2 * G.lambda j * Real.log (G.lambda j) := by
  have hprod : 0 < ∏ j, G.lambda j ^ (2 * G.lambda j) :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (G.lambda_pos j) _
  have hQ := G.Q_pos
  have hq : G.conductor / (2 * π) = G.Q ^ 2 * ∏ j, G.lambda j ^ (2 * G.lambda j) := by
    unfold RHTower.SelbergGammaData.conductor
    rw [hd, Real.rpow_one]
    field_simp
  rw [hq, Real.log_mul (by positivity) hprod.ne', Real.log_pow, Real.log_prod (fun j _ =>
    (Real.rpow_pos_of_pos (G.lambda_pos j) _).ne')]
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun j _ => Real.log_rpow (G.lambda_pos j) _

/-- The sum of the phases of all pairs is `t log t − t + tΛ + θ log t + M`, where
`Λ = Σ 2λⱼ log λⱼ` and `M = Σ 2 Im μⱼ log λⱼ`. -/
theorem sum_pair_phases (G : RHTower.SelbergGammaData) (hd : G.degree = 1) {t : ℝ} (ht : 0 < t) :
    ∑ j, (2 * (G.lambda j * t * Real.log (G.lambda j * t) - G.lambda j * t +
        (G.mu j).im * Real.log (G.lambda j * t))) =
      (t * Real.log t - t) + t * (∑ j, 2 * G.lambda j * Real.log (G.lambda j)) +
        G.internalShift * Real.log t + ∑ j, 2 * (G.mu j).im * Real.log (G.lambda j) := by
  have hdeg : 2 * ∑ j, G.lambda j = 1 := hd
  have hshift : G.internalShift = 2 * ∑ j, (G.mu j).im := by
    unfold RHTower.SelbergGammaData.internalShift
    rw [hd, Complex.im_sum]
    norm_num
  have hterm : ∀ j, 2 * (G.lambda j * t * Real.log (G.lambda j * t) - G.lambda j * t +
      (G.mu j).im * Real.log (G.lambda j * t)) =
      G.lambda j * (2 * (t * Real.log t - t)) + t * (2 * G.lambda j * Real.log (G.lambda j)) +
        (G.mu j).im * (2 * Real.log t) + 2 * (G.mu j).im * Real.log (G.lambda j) := fun j => by
    rw [Real.log_mul (G.lambda_pos j).ne' ht.ne']
    ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hshift]
  linear_combination (t * Real.log t - t) * hdeg

/-- The product of the powers of `λⱼ t`. -/
theorem prod_pair_powers (G : RHTower.SelbergGammaData) (hd : G.degree = 1) (σ : ℝ) {t : ℝ}
    (ht : 0 < t) :
    ∏ j, (G.lambda j * t) ^ (-(G.lambda j * (1 - 2 * σ))) =
      (∏ j, G.lambda j ^ (-(G.lambda j * (1 - 2 * σ)))) * t ^ (σ - 1 / 2) := by
  have hdeg : 2 * ∑ j, G.lambda j = 1 := hd
  have hexp : σ - 1 / 2 = ∑ j, -(G.lambda j * (1 - 2 * σ)) := by
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    linear_combination ((1 - 2 * σ) / 2) * hdeg
  rw [hexp, Real.rpow_sum_of_pos ht, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => Real.mul_rpow (G.lambda_pos j).le ht.le

/-- Field algebra of the symbol identity. -/
theorem symbol_algebra {A R QQ Eℓ Eθ Ex ET Ey q P p e₁ e₂ : ℂ} (hEx : Ex ≠ 0) (hP : P ≠ 0)
    (hp : p ≠ 0) (he₁ : e₁ ≠ 0) (he : e₁ * e₂ = 1) (h : QQ * Eℓ * Eθ * Ex = q * ET * Ey) :
    (A / (Ex * (p * e₁))) * (R * ET * (P * p)) * (q * P⁻¹ * Ey) = A * (QQ * R) * e₂ * Eℓ * Eθ := by
  have he₂ : e₂ = e₁⁻¹ := eq_inv_of_mul_eq_one_right he
  have hL : (A / (Ex * (p * e₁))) * (R * ET * (P * p)) * (q * P⁻¹ * Ey) =
      A * R * (q * ET * Ey) * (Ex⁻¹ * e₁⁻¹) := by
    field_simp
  rw [hL, ← h, he₂]
  field_simp

/-- **The symbol on a far line.**  At degree one, `symbol G σ t · e^{πt/2} (q/2π)^{it} t^{iθ}` converges
to a nonzero constant as `t → +∞`. -/
theorem exists_tendsto_symbol (G : RHTower.SelbergGammaData) (hd : G.degree = 1) (σ : ℝ) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun t : ℝ => symbol G σ t * ((Real.exp (π * t / 2) : ℝ) : ℂ) *
      cexp (I * ((t * Real.log (G.conductor / (2 * π)) : ℝ) : ℂ)) *
      cexp (I * ((G.internalShift * Real.log t : ℝ) : ℂ))) atTop (𝓝 c) := by
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∏ j, G.lambda j ^ (-(G.lambda j * (1 - 2 * σ))) := ⟨_, rfl⟩
  have hP0 : 0 < P := by
    rw [hPdef]
    exact Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (G.lambda_pos j) _
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ j, 2 * (G.mu j).im * Real.log (G.lambda j) := ⟨_, rfl⟩
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = ∑ j, 2 * G.lambda j * Real.log (G.lambda j) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℂ, K = ((G.Q ^ (1 - 2 * σ) : ℝ) : ℂ) * (P : ℂ)⁻¹ *
      cexp (I * ((π * (σ - 1 / 2) / 2 - M : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hPc : (P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hP0.ne'
  have hQc : ((G.Q ^ (1 - 2 * σ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos G.Q_pos _).ne'
  have hK0 : K ≠ 0 := by
    rw [hK]
    exact mul_ne_zero (mul_ne_zero hQc (inv_ne_zero hPc)) (Complex.exp_ne_zero _)
  have hprod := tendsto_finsetProd Finset.univ
    (fun j _ => tendsto_gamma_ratio σ (G.lambda_pos j) (G.mu j))
  have hall := ((tendsto_Gamma_div_stirlingShape σ).mul hprod).mul_const K
  refine ⟨_, ?_, hall.congr' ?_⟩
  · refine mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr ?_) ?_) hK0
    · exact (Real.sqrt_pos.mpr (by positivity)).ne'
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => Complex.exp_ne_zero _
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  -- the product of the pairs
  obtain ⟨R, hR⟩ : ∃ R : ℂ, R = ∏ j, (Complex.Gamma ((G.lambda j : ℂ) * (1 - linePoint σ t) +
      star (G.mu j)) * (Complex.Gamma ((G.lambda j : ℂ) * linePoint σ t + G.mu j))⁻¹) := ⟨_, rfl⟩
  have hprodR : (∏ j, ((Complex.Gamma ((G.lambda j : ℂ) * (1 - linePoint σ t) + star (G.mu j)) *
        (Complex.Gamma ((G.lambda j : ℂ) * linePoint σ t + G.mu j))⁻¹) *
        cexp (I * ((2 * (G.lambda j * t * Real.log (G.lambda j * t) - G.lambda j * t +
          (G.mu j).im * Real.log (G.lambda j * t)) : ℝ) : ℂ)) *
        (((G.lambda j * t) ^ (-(G.lambda j * (1 - 2 * σ))) : ℝ) : ℂ))) =
      R * cexp (I * (((t * Real.log t - t) + t * Λ + G.internalShift * Real.log t + M : ℝ) : ℂ)) *
        ((P : ℂ) * ((t ^ (σ - 1 / 2) : ℝ) : ℂ)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← hR, ← Complex.exp_sum, ← Finset.mul_sum,
      ← Complex.ofReal_sum, sum_pair_phases G hd ht, ← Complex.ofReal_prod,
      prod_pair_powers G hd σ ht, ← hPdef, ← hMdef, ← hΛdef, Complex.ofReal_mul]
  have hsym : symbol G σ t = Complex.Gamma (linePoint σ t) *
      (((G.Q : ℂ) ^ (1 - linePoint σ t) * (G.Q : ℂ) ^ (-linePoint σ t)) * R) := by
    unfold symbol
    rw [G.gammaFactor_inv_expansion, hR, Finset.prod_mul_distrib]
    ring
  have hshape : stirlingShape σ t =
      cexp (I * ((π * (σ - 1 / 2) / 2 + (t * Real.log t - t) : ℝ) : ℂ)) *
        (((t ^ (σ - 1 / 2) : ℝ) : ℂ) * ((Real.exp (-(π * t / 2)) : ℝ) : ℂ)) := by
    unfold stirlingShape
    rw [Complex.ofReal_mul]
  have hQlog : ((G.Q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr G.Q_pos.ne'
  have hexps : ((G.Q : ℂ) ^ (1 - linePoint σ t) * (G.Q : ℂ) ^ (-linePoint σ t)) *
      cexp (I * ((t * Real.log (G.conductor / (2 * π)) : ℝ) : ℂ)) *
      cexp (I * ((G.internalShift * Real.log t : ℝ) : ℂ)) *
      cexp (I * ((π * (σ - 1 / 2) / 2 + (t * Real.log t - t) : ℝ) : ℂ)) =
      ((G.Q ^ (1 - 2 * σ) : ℝ) : ℂ) *
        cexp (I * (((t * Real.log t - t) + t * Λ + G.internalShift * Real.log t + M : ℝ) : ℂ)) *
        cexp (I * ((π * (σ - 1 / 2) / 2 - M : ℝ) : ℂ)) := by
    rw [log_conductor_div G hd, ← hΛdef, Complex.cpow_def_of_ne_zero hQlog,
      Complex.cpow_def_of_ne_zero hQlog, ← Complex.ofReal_log G.Q_pos.le,
      Real.rpow_def_of_pos G.Q_pos, Complex.ofReal_exp]
    simp only [← Complex.exp_add]
    congr 1
    simp only [linePoint]
    push_cast
    ring
  have he : ((Real.exp (-(π * t / 2)) : ℝ) : ℂ) * ((Real.exp (π * t / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  rw [hprodR, hsym, hK, hshape]
  exact symbol_algebra (Complex.exp_ne_zero _) hPc
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne')
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') he hexps

end

end GaloisForLFunctions.SelbergClass.DegreeOne
