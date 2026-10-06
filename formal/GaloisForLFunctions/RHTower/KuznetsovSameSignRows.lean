import GaloisForLFunctions.RHTower.KuznetsovCuspFormPairing

/-!
# The same-sign rows of the Poincaré pairing

For the Selberg profile `h_{s,ν}(w) = (Im w)^s e(νw)` with a cusp vector `w` of frequency `ν`, a row
`(c, d)` with `c ≠ 0` of `M = (a b; c d)` and `x = yξ − d/c`,

`M(x+iy) = a/c − 1/(c² y (ξ + i))`,

and the term of the frequency-`μ` coefficient of `P(·| h_{s₂,ν}, w)`, weighted by the conjugate profile
of `U(·, s₁)` and the invariant measure, is

`y^{s̄₁−2} e^{−2πμy} · y · coeffTerm(yξ − d/c) = ⟨v, ρ(M)⁻¹w⟩ e((μd + νa)/c) (c²)^{−s₂}
  K⁺(s̄₁, s₂; μ, ν, c²)(y, ξ)`

with the same-sign kernel `K⁺(a₁, a₂)(y, ξ) = (1+ξ²)^{−a₂} y^{a₁−a₂−1} e^{−2πμ(1+iξ)y − 2πν/(c²(1−iξ)y)}`
(`kuzKernelPlus`).  Its modulus equals that of the opposite-sign kernel (`norm_kuzKernelPlus`), so it is
absolutely integrable under the same conditions.  The diagonal term is
`[μ = ν] y^{s₂} e^{−2πνy} ⟨v, w + ρ(−1)⁻¹w⟩` (`diagonal_poincProfile`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## The same-sign kernel -/

/-- The same-sign Kuznetsov kernel
`(1+ξ²)^{−a₂} y^{a₁−a₂−1} exp(−2πμ(1+iξ)y − 2πν/(q(1−iξ)y))`. -/
def kuzKernelPlus (a₁ a₂ : ℂ) (μ ν q : ℝ) (p : ℝ × ℝ) : ℂ :=
  (((1 + p.2 ^ 2 : ℝ)) : ℂ) ^ (-a₂) * ((p.1 : ℂ) ^ (a₁ - a₂ - 1) *
    cexp (-(Kuznetsov.kuzRate μ p.2 * p.1) -
      ((2 * Real.pi * ν : ℝ) : ℂ) / ((q : ℂ) * (1 - Complex.I * p.2) * p.1)))

theorem re_kuzParam_div {μ ν q : ℝ} (hμ : 0 < μ) (hq : 0 < q) {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    ((Kuznetsov.kuzParam μ ν q : ℂ) / (Kuznetsov.kuzRate μ ξ * y)).re =
      (((2 * Real.pi * ν : ℝ) : ℂ) / ((q : ℂ) * (1 - Complex.I * ξ) * y)).re := by
  have hc : (Kuznetsov.kuzParam μ ν q : ℂ) / (Kuznetsov.kuzRate μ ξ * y) =
      conj (((2 * Real.pi * ν : ℝ) : ℂ) / ((q : ℂ) * (1 - Complex.I * ξ) * y)) := by
    have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h1 := Kuznetsov.one_add_I_mul_ne_zero ξ
    simp only [map_div₀, map_mul, Complex.conj_ofReal, map_sub, map_one, Complex.conj_I,
      Kuznetsov.kuzParam, Kuznetsov.kuzRate]
    push_cast
    rw [show (1 : ℂ) - -Complex.I * ξ = 1 + Complex.I * ξ by ring]
    field_simp
    ring
  rw [hc, Complex.conj_re]

/-- **`|K⁺| = |K|`.** -/
theorem norm_kuzKernelPlus {a₁ a₂ : ℂ} {μ ν q : ℝ} (hμ : 0 < μ) (hq : 0 < q) {y : ℝ} (hy : 0 < y)
    (ξ : ℝ) : ‖kuzKernelPlus a₁ a₂ μ ν q (y, ξ)‖ = ‖Kuznetsov.kuzKernel a₁ a₂ μ ν q (y, ξ)‖ := by
  rw [kuzKernelPlus, Kuznetsov.kuzKernel, Kuznetsov.invGaussKernel, norm_mul, norm_mul, norm_mul,
    norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 3
  simp only [Complex.sub_re, Complex.neg_re]
  rw [re_kuzParam_div hμ hq hy ξ]

theorem measurable_kuzKernelPlus (a₁ a₂ : ℂ) (μ ν q : ℝ) :
    Measurable (kuzKernelPlus a₁ a₂ μ ν q) := by
  unfold kuzKernelPlus Kuznetsov.kuzRate
  fun_prop

/-- **Absolute convergence** of the same-sign double integral. -/
theorem integrable_kuzKernelPlus {a₁ a₂ : ℂ} {μ ν q δ : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q)
    (hδ : 0 < δ) (hδ₁ : a₂.re - a₁.re < δ) (hδ₂ : δ < a₂.re - 1 / 2) :
    Integrable (kuzKernelPlus a₁ a₂ μ ν q) ((volume.restrict (Ioi 0)).prod volume) := by
  refine (Kuznetsov.integrable_kuzKernel hμ hν hq hδ hδ₁ hδ₂).norm.mono'
    (measurable_kuzKernelPlus a₁ a₂ μ ν q).aestronglyMeasurable ?_
  filter_upwards [Kuznetsov.ae_prod_fst_mem_Ioi] with p hp
  obtain ⟨y, ξ⟩ := p
  rw [norm_kuzKernelPlus hμ hq hp ξ]

theorem integral_norm_kuzKernelPlus_le {a₁ a₂ : ℂ} {μ ν q δ : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hq : 0 < q) (hδ : 0 < δ) (hδ₁ : a₂.re - a₁.re < δ) (hδ₂ : δ < a₂.re - 1 / 2) :
    ∫ p, ‖kuzKernelPlus a₁ a₂ μ ν q p‖ ∂((volume.restrict (Ioi 0)).prod volume) ≤
      δ ^ δ * (2 * Real.pi * ν)⁻¹ ^ δ *
        ((∫ y in Ioi (0 : ℝ), y ^ ((a₁ - a₂).re + δ - 1) * Real.exp (-(2 * Real.pi * μ * y))) *
          ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - a₂.re)) * q ^ δ := by
  refine le_of_eq_of_le ?_ (Kuznetsov.integral_norm_kuzKernel_le hμ hν hq hδ hδ₁ hδ₂)
  refine integral_congr_ae ?_
  filter_upwards [Kuznetsov.ae_prod_fst_mem_Ioi] with p hp
  obtain ⟨y, ξ⟩ := p
  exact norm_kuzKernelPlus hμ hq hp ξ

/-- The value `∫_0^∞ ∫_ℝ K⁺(a₁, a₂; μ, ν, q)(y, ξ) dξ dy` of the same-sign double integral. -/
def kuzValuePlus (a₁ a₂ : ℂ) (μ ν q : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), ∫ ξ, kuzKernelPlus a₁ a₂ μ ν q (y, ξ)

/-! ## Rows in Kuznetsov's coordinates -/

theorem coe_gammaSetMatrix_smul_rowPoint {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) {y : ℝ}
    (hy : 0 < y) (ξ : ℝ) :
    ((gammaSetMatrix p • rowPoint p hy ξ : ℍ) : ℂ) =
      (gammaSetMatrix p 0 0 : ℂ) / (p.1 0 : ℂ) - 1 / ((p.1 0 : ℂ) ^ 2 * y * (ξ + Complex.I)) := by
  have hc' : (p.1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hξ : (ξ : ℂ) + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hdet := det_gammaSetMatrix p
  have hz : (rowPoint p hy ξ : ℂ) = y * (ξ + Complex.I) - (p.1 1 : ℂ) / (p.1 0 : ℂ) := by
    rw [rowPoint, coe_hLine]; push_cast; ring
  have hnum : (gammaSetMatrix p 0 0 : ℂ) * (rowPoint p hy ξ : ℂ) + (gammaSetMatrix p 0 1 : ℂ) =
      (gammaSetMatrix p 0 0 : ℂ) * y * (ξ + Complex.I) - 1 / (p.1 0 : ℂ) := by
    rw [hz]
    field_simp
    linear_combination -hdet
  rw [coe_gammaSetMatrix_smul, denom_rowPoint hc hy, hnum]
  field_simp

/-- The same-sign row weight `⟨v, ρ(M)⁻¹w⟩ e((μd + νa)/c)` of `M = (a b; c d)`. -/
def rowWeightPlus (μ ν : ℝ) (v w : DeckSpace N) (p : gammaSet 1 1 0) : ℂ :=
  ⟪v, (deckRho N (gammaSetMatrix p)).symm w⟫_ℂ *
    cexp (2 * Real.pi * Complex.I *
      ((μ * (p.1 1 : ℂ) + ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ)))

theorem norm_rowWeightPlus_le (μ ν : ℝ) (v w : DeckSpace N) (p : gammaSet 1 1 0) :
    ‖rowWeightPlus μ ν v w p‖ ≤ ‖v‖ * ‖w‖ := by
  rw [rowWeightPlus, norm_mul]
  have he : ‖cexp (2 * Real.pi * Complex.I *
      ((μ * (p.1 1 : ℂ) + ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ)))‖ = 1 := by
    rw [show (2 * Real.pi * Complex.I *
        ((μ * (p.1 1 : ℂ) + ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ))) =
        (((2 * Real.pi * ((μ * (p.1 1 : ℝ) + ν * (gammaSetMatrix p 0 0 : ℝ)) / (p.1 0 : ℝ)) : ℝ)
          : ℂ) * Complex.I) by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [he, mul_one]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]

/-- **The same-sign row term in Kuznetsov's coordinates.** -/
theorem coeffTerm_rowPoint_eq_kuzKernelPlus {μ ν : ℝ} (s₁ s₂ : ℂ) (v w : DeckSpace N)
    {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    ((y ^ 2)⁻¹ : ℝ) • ((y : ℂ) ^ (conj s₁) * (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) *
      ((y : ℂ) * coeffTerm μ v (poincProfile s₂ ν) w hy p
        (y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ)))) =
      rowWeightPlus μ ν v w p * (((p.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s₂) *
        kuzKernelPlus (conj s₁) s₂ μ ν ((p.1 0 : ℝ) ^ 2) (y, ξ) := by
  have hc' : (p.1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hξ1 : (1 : ℂ) - Complex.I * ξ ≠ 0 := Kuznetsov.one_sub_I_mul_ne_zero ξ
  have hξI : (ξ : ℂ) + Complex.I = Complex.I * (1 - Complex.I * ξ) := by
    ring_nf; rw [Complex.I_sq]; ring
  have hξ0 : 0 < 1 + ξ ^ 2 := by positivity
  have hc2 : 0 < (p.1 0 : ℝ) ^ 2 := by positivity
  -- the profile at the row point
  have hrow : coeffTerm μ v (poincProfile s₂ ν) w hy p (y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ)) =
      cexp (-(2 * Real.pi * Complex.I * μ * ((y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ) : ℝ) : ℂ))) *
        ((((p.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s₂) * (y : ℂ) ^ (-s₂) *
          (((1 + ξ ^ 2 : ℝ)) : ℂ) ^ (-s₂) *
          cexp (2 * Real.pi * Complex.I * ν * ((gammaSetMatrix p 0 0 : ℂ) / (p.1 0 : ℂ) -
            1 / ((p.1 0 : ℂ) ^ 2 * y * (ξ + Complex.I)))) *
          ⟪v, (deckRho N (gammaSetMatrix p)).symm w⟫_ℂ) := by
    rw [coeffTerm, cuspChar, poincTerm, inner_smul_right]
    change _ * (poincProfile s₂ ν (gammaSetMatrix p • rowPoint p hy ξ) * _) = _
    rw [poincProfile, im_gammaSetMatrix_smul_rowPoint hc hy,
      coe_gammaSetMatrix_smul_rowPoint hc hy, ofReal_inv_cpow (by positivity),
      Complex.ofReal_mul ((p.1 0 : ℝ) ^ 2 * y), Complex.mul_cpow_ofReal_nonneg (by positivity) hξ0.le,
      Complex.ofReal_mul ((p.1 0 : ℝ) ^ 2), Complex.mul_cpow_ofReal_nonneg hc2.le hy.le]
  -- the power of `y`
  have hpow : (y : ℂ) ^ (conj s₁ - s₂ - 1) =
      (y : ℂ) ^ (conj s₁) * (y : ℂ) ^ (-s₂) * (y : ℂ)⁻¹ := by
    rw [sub_eq_add_neg, sub_eq_add_neg, Complex.cpow_add _ _ hy', Complex.cpow_add _ _ hy',
      Complex.cpow_neg_one]
  -- the exponent
  have hexp : cexp (-(Kuznetsov.kuzRate μ ξ * y) -
      ((2 * Real.pi * ν : ℝ) : ℂ) / ((((p.1 0 : ℝ) ^ 2 : ℝ) : ℂ) * (1 - Complex.I * ξ) * y)) =
      cexp (-(2 * Real.pi * Complex.I * μ * ((y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ) : ℝ) : ℂ))) *
        cexp (2 * Real.pi * Complex.I * ν * ((gammaSetMatrix p 0 0 : ℂ) / (p.1 0 : ℂ) -
          1 / ((p.1 0 : ℂ) ^ 2 * y * (ξ + Complex.I)))) *
        cexp ((-(2 * Real.pi * μ * y) : ℝ) : ℂ) /
        cexp (2 * Real.pi * Complex.I *
          ((μ * (p.1 1 : ℂ) + ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ))) := by
    rw [eq_div_iff (Complex.exp_ne_zero _), ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    rw [hξI, Kuznetsov.kuzRate]
    push_cast
    field_simp
    ring_nf
  rw [kuzKernelPlus, hexp, hpow, hrow, rowWeightPlus, Complex.real_smul, ← Complex.ofReal_exp]
  push_cast
  field_simp

/-- **The same-sign row integral at height `y`** in Kuznetsov's coordinates. -/
theorem integral_coeffTerm_poincProfile {μ ν : ℝ} (s₁ s₂ : ℂ) (v w : DeckSpace N)
    {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) {y : ℝ} (hy : 0 < y) :
    ((y ^ 2)⁻¹ : ℝ) • ((y : ℂ) ^ (conj s₁) * (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) *
      ∫ x, coeffTerm μ v (poincProfile s₂ ν) w hy p x) =
      rowWeightPlus μ ν v w p * (((p.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s₂) *
        ∫ ξ, kuzKernelPlus (conj s₁) s₂ μ ν ((p.1 0 : ℝ) ^ 2) (y, ξ) := by
  set f := coeffTerm μ v (poincProfile s₂ ν) w hy p
  set e : ℝ := (p.1 1 : ℝ) / (p.1 0 : ℝ)
  have h1 : ∫ x, f x = (y : ℂ) * ∫ ξ, f (y * ξ - e) := by
    rw [← integral_sub_right_eq_self f e]
    have h := Measure.integral_comp_mul_left (fun x => f (x - e)) y
    rw [abs_inv, abs_of_pos hy] at h
    rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hy.ne',
      Complex.ofReal_one, one_mul]
  rw [h1, ← integral_const_mul, ← integral_const_mul, ← integral_smul, ← integral_const_mul]
  congr 1
  funext ξ
  exact coeffTerm_rowPoint_eq_kuzKernelPlus (μ := μ) (ν := ν) s₁ s₂ v w hc hy ξ

/-! ## The diagonal term -/

theorem inner_cuspEigen_sub_eq_zero {μ ν : ℝ} {v u : DeckSpace N} (hv : IsCuspEigen μ v)
    (hu : IsCuspEigen ν u) :
    (1 - cexp (2 * Real.pi * Complex.I * (ν - μ))) * ⟪v, u⟫_ℂ = 0 := by
  have h := (deckRho N ModularGroup.T).inner_map_map v u
  rw [hv, hu, inner_smul_left, inner_smul_right, ← Complex.exp_conj, ← mul_assoc,
    ← Complex.exp_add] at h
  have he : conj (2 * Real.pi * Complex.I * μ) + 2 * Real.pi * Complex.I * (ν : ℂ) =
      2 * Real.pi * Complex.I * (ν - μ) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [he] at h
  linear_combination -h

/-- **The diagonal term**: `[μ = ν] y^{s₂} e^{−2πνy} ⟨v, w + ρ(−1)⁻¹w⟩`. -/
theorem diagonal_poincProfile {μ ν : ℝ} (s : ℂ) {v w : DeckSpace N} (hv : IsCuspEigen μ v)
    (hw : IsCuspEigen ν w) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0 : ℝ) 1, cuspChar μ x * poincProfile s ν (hLine hy x)) *
        ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ =
      if μ = ν then (y : ℂ) ^ s * (Real.exp (-(2 * Real.pi * ν * y)) : ℂ) *
        ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ else 0 := by
  have hpt : ∀ x : ℝ, cuspChar μ x * poincProfile s ν (hLine hy x) =
      (y : ℂ) ^ s * (Real.exp (-(2 * Real.pi * ν * y)) : ℂ) *
        cexp ((2 * Real.pi * Complex.I * (ν - μ)) * x) := fun x => by
    rw [poincProfile_hLine, cuspChar, cuspChar, mul_comm, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  split_ifs with h
  · subst h
    simp
  · set c : ℂ := 2 * Real.pi * Complex.I * (ν - μ)
    have hc : c ≠ 0 := by
      have : (ν - μ : ℂ) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast (Ne.symm h)
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero) this
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_exp_mul_complex hc]
    have h0 := inner_cuspEigen_sub_eq_zero hv (isCuspEigen_add_neg_one hw)
    push_cast
    rw [mul_one, mul_zero, Complex.exp_zero]
    have : (cexp c - 1) * ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ = 0 := by
      linear_combination -h0
    rw [mul_div_assoc', div_mul_eq_mul_div, mul_assoc, this, mul_zero, zero_div]

end

end GaloisForLFunctions.RHTower.DeckPointPair
