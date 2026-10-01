import GaloisForLFunctions.HTGeometry.MellinRegularStrip

/-!
# Linear structure and integrability for the Mellin-regular class

Regular functions on a strip form a vector space and `Mellin⁻¹_c` is linear on it. Also:
`|Mellin⁻¹_c Ψ (x)| ≤ (2π)⁻¹ x^{-c} ∫|Ψ(c+it)|dt`, and the weighted square
`|Mellin⁻¹_σ Ψ|² x^{2σ-1}` is integrable on `(0,∞)` whenever `Ψ(σ+i·)` is integrable and square
integrable (by the substitution `x = e^{-u}` and Plancherel).
-/

open Complex MeasureTheory Filter Set Topology
open scoped FourierTransform

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace MellinRegularStrip

variable {Ψ Ψ₁ Ψ₂ : ℂ → ℂ} {α β : ℝ}

theorem zero : MellinRegularStrip (fun _ => 0) α β :=
  ⟨fun _ _ _ => differentiableAt_const _, fun _ _ _ _ _ => ⟨0, fun _ _ _ => by simp⟩⟩

theorem add (h₁ : MellinRegularStrip Ψ₁ α β) (h₂ : MellinRegularStrip Ψ₂ α β) :
    MellinRegularStrip (fun s => Ψ₁ s + Ψ₂ s) α β := by
  refine ⟨fun s ha hb => (h₁.diff s ha hb).add (h₂.diff s ha hb), fun a b ha hb K => ?_⟩
  obtain ⟨C₁, hC₁⟩ := h₁.decay a b ha hb K
  obtain ⟨C₂, hC₂⟩ := h₂.decay a b ha hb K
  refine ⟨C₁ + C₂, fun s h1 h2 => ?_⟩
  calc ‖Ψ₁ s + Ψ₂ s‖ ≤ ‖Ψ₁ s‖ + ‖Ψ₂ s‖ := norm_add_le _ _
    _ ≤ C₁ / (1 + s.im ^ 2) ^ K + C₂ / (1 + s.im ^ 2) ^ K := add_le_add (hC₁ s h1 h2) (hC₂ s h1 h2)
    _ = (C₁ + C₂) / (1 + s.im ^ 2) ^ K := by ring

theorem const_mul (h : MellinRegularStrip Ψ α β) (c : ℂ) :
    MellinRegularStrip (fun s => c * Ψ s) α β := by
  refine ⟨fun s ha hb => (h.diff s ha hb).const_mul c, fun a b ha hb K => ?_⟩
  obtain ⟨C, hC⟩ := h.decay a b ha hb K
  refine ⟨‖c‖ * C, fun s h1 h2 => ?_⟩
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hC s h1 h2) (norm_nonneg c)

/-- The inverse Mellin integrand on a line inside the strip is integrable. -/
theorem integrable_mellinInv_integrand (h : MellinRegularStrip Ψ α β) {c : ℝ} (hc : α < c)
    (hc' : c < β) {x : ℝ} (hx : 0 < x) :
    Integrable fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + t * I)) • Ψ ((c : ℂ) + t * I) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ((h.integrable_line hc hc').norm.const_mul (x ^ (-c))).mono'
    ((Continuous.const_cpow (by fun_prop) (Or.inl hx0)).smul
      (h.continuous_line hc hc')).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

end MellinRegularStrip

theorem mellinInv_add {Ψ₁ Ψ₂ : ℂ → ℂ} {α β c : ℝ} (h₁ : MellinRegularStrip Ψ₁ α β)
    (h₂ : MellinRegularStrip Ψ₂ α β) (hc : α < c) (hc' : c < β) {x : ℝ} (hx : 0 < x) :
    mellinInv c (fun s => Ψ₁ s + Ψ₂ s) x = mellinInv c Ψ₁ x + mellinInv c Ψ₂ x := by
  simp only [mellinInv, smul_add]
  rw [integral_add (h₁.integrable_mellinInv_integrand hc hc' hx)
    (h₂.integrable_mellinInv_integrand hc hc' hx), smul_add]

theorem mellinInv_const_mul {Ψ : ℂ → ℂ} (c : ℝ) (a : ℂ) (x : ℝ) :
    mellinInv c (fun s => a * Ψ s) x = a * mellinInv c Ψ x := by
  simp only [mellinInv, smul_eq_mul]
  rw [show (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + t * I)) * (a * Ψ ((c : ℂ) + t * I)))
      = fun t : ℝ => a * ((x : ℂ) ^ (-((c : ℂ) + t * I)) * Ψ ((c : ℂ) + t * I)) by
    funext t; ring, integral_const_mul]
  rw [Complex.real_smul, Complex.real_smul]; ring

/-- `|Mellin⁻¹_c Ψ (x)| ≤ (2π)⁻¹ x^{-c} ∫ |Ψ(c+it)| dt`. -/
theorem norm_mellinInv_le {Ψ : ℂ → ℂ} (c : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖mellinInv c Ψ x‖ ≤ (1 / (2 * Real.pi)) * x ^ (-c) * ∫ t : ℝ, ‖Ψ ((c : ℂ) + t * I)‖ := by
  simp only [mellinInv]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_assoc]
  gcongr
  calc ‖∫ t : ℝ, (x : ℂ) ^ (-((c : ℂ) + t * I)) • Ψ ((c : ℂ) + t * I)‖
      ≤ ∫ t : ℝ, ‖(x : ℂ) ^ (-((c : ℂ) + t * I)) • Ψ ((c : ℂ) + t * I)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, x ^ (-c) * ‖Ψ ((c : ℂ) + t * I)‖ := by
        congr 1; funext t
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
    _ = x ^ (-c) * ∫ t : ℝ, ‖Ψ ((c : ℂ) + t * I)‖ := integral_const_mul _ _

/-- Substitution `x = e^{-u}` for integrability: `G ∈ L¹(ℝ)` gives `G(-log x)/x ∈ L¹(0,∞)`. -/
theorem integrableOn_Ioi_comp_neg_log_div {G : ℝ → ℝ} (hG : Integrable G) :
    IntegrableOn (fun x => G (-Real.log x) * x⁻¹) (Ioi 0) := by
  have hderiv : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-x)) univ x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    rw [mul_neg_one] at h1
    exact h1.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (-u)) univ := by
    intro a _ b _ h
    simpa using Real.exp_injective h
  have himage : (fun u : ℝ => Real.exp (-u)) '' univ = Ioi 0 := by
    rw [Set.image_univ]
    ext x
    constructor
    · rintro ⟨u, rfl⟩; exact Real.exp_pos _
    · intro hx; exact ⟨-Real.log x, by simp [Real.exp_log hx]⟩
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun x : ℝ => G (-Real.log x) * x⁻¹)
  rw [himage] at h
  refine h.mpr ?_
  rw [integrableOn_univ]
  refine hG.congr (Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul, Real.log_exp, neg_neg, abs_neg, abs_of_pos (Real.exp_pos _)]
  have := Real.exp_pos (-u)
  field_simp

/-- Integrability companion of Mellin–Plancherel: `|Mellin⁻¹_σ Ψ|² x^{2σ-1} ∈ L¹(0,∞)`. -/
theorem integrableOn_norm_sq_mellinInv {Ψ : ℂ → ℂ} {σ : ℝ}
    (hint : Integrable fun t : ℝ => Ψ ((σ : ℂ) + t * I))
    (hL2 : MemLp (fun t : ℝ => Ψ ((σ : ℂ) + t * I)) 2) :
    IntegrableOn (fun x => ‖mellinInv σ Ψ x‖ ^ 2 * x ^ (2 * σ - 1)) (Ioi 0) := by
  set φ : ℝ → ℂ := fun y => Ψ ((σ : ℂ) + 2 * Real.pi * y * I) with hφ
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hφeq : φ = fun y : ℝ => (fun t : ℝ => Ψ ((σ : ℂ) + t * I)) (2 * Real.pi * y) := by
    funext y; simp only [hφ]; push_cast; ring_nf
  have hφint : Integrable φ := by
    rw [hφeq]; exact hint.comp_mul_left' h2π.ne'
  have hφL2 : MemLp φ 2 := by
    rw [memLp_two_iff_integrable_sq_norm hφint.aestronglyMeasurable]
    have h := (memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable).mp hL2
    rw [hφeq]
    exact h.comp_mul_left' h2π.ne'
  -- `𝓕φ ∈ L²`
  set u : Lp ℂ 2 (volume : Measure ℝ) := hφL2.toLp φ with hu
  have hcoe : (u : ℝ → ℂ) =ᵐ[volume] φ := hφL2.coeFn_toLp
  have huint : Integrable (u : ℝ → ℂ) := hφint.congr hcoe.symm
  have hF : ((𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ := by
    refine (coeFn_fourierTransform_eq_fourierIntegral u huint).trans ?_
    filter_upwards with ξ
    exact Real.fourier_congr_ae hcoe ξ
  have hFsq : Integrable fun ξ : ℝ => ‖𝓕 φ ξ‖ ^ 2 := by
    have h1 := (Lp.memLp (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)))
    have h2 := (memLp_two_iff_integrable_sq_norm h1.1).mp h1
    refine h2.congr ?_
    filter_upwards [hF] with ξ h; rw [h]
  have hFinv : Integrable fun ξ : ℝ => ‖𝓕⁻ φ ξ‖ ^ 2 := by
    simp_rw [Real.fourierInv_eq_fourier_neg]
    exact hFsq.comp_neg
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ‖mellinInv σ Ψ x‖ ^ 2 * x ^ (2 * σ - 1)
      = ‖𝓕⁻ φ (-Real.log x)‖ ^ 2 * x⁻¹ := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    rw [mellinInv_eq_fourierInv σ Ψ hx', norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx']
    simp only [neg_re, ofReal_re]
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx'.le]
    have : x ^ ((-σ) * ((2 : ℕ) : ℝ)) * x ^ (2 * σ - 1) = x⁻¹ := by
      rw [← Real.rpow_add hx', ← Real.rpow_neg_one]
      congr 1; push_cast; ring
    calc x ^ (-σ * ((2 : ℕ) : ℝ)) * ‖𝓕⁻ φ (-Real.log x)‖ ^ 2 * x ^ (2 * σ - 1)
        = ‖𝓕⁻ φ (-Real.log x)‖ ^ 2 * (x ^ (-σ * ((2 : ℕ) : ℝ)) * x ^ (2 * σ - 1)) := by ring
      _ = _ := by rw [this]
  exact (integrableOn_Ioi_comp_neg_log_div hFinv).congr_fun (fun x hx => (hpt x hx).symm)
    measurableSet_Ioi

end GaloisForLFunctions.HTGeometry
