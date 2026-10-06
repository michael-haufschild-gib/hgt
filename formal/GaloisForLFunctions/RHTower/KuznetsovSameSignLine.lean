import GaloisForLFunctions.RHTower.KuznetsovSameSignIdentity

/-!
# The same-sign Kuznetsov identity on a vertical line

On the line `s̄₁ = σ + it`, `s₂ = σ − it` (`σ > 1`), the substitution `y = λ eʷ` with
`λ = √(ν/(μq(1+ξ²)))` turns the exponent of the same-sign kernel into
`−2πμ(1+iξ)y − 2πν/(q(1−iξ)y) = −X ζ(ξ) cosh w`, `X = 4π√(μν/q)`, `ζ(ξ) = (1+iξ)/√(1+ξ²)`, so

`V⁺(σ+it, σ−it; μ, ν, q) = (ν/(μq))^{it} Ξ_σ(t, X)`,
`Ξ_σ(t, X) = ∫ (1+ξ²)^{−σ} ∫ e^{2itw} e^{−X ζ(ξ) cosh w} dw dξ`

(`kuzValuePlus_line`).  The factors `(ν/μ)^{it}` of the two sides cancel, leaving

`2[μ = ν](4πμ)^{1−2σ} Γ(2σ−1) ⟨v, w + ρ(−1)⁻¹w⟩ + 2 Σ_{(c,d)} ⟨v, ρ(M)⁻¹w⟩ e((μd+νa)/c) c^{−2σ}
   Ξ_σ(t, 4π√(μν)/|c|)
 = 4 (2πμ)^{½−σ} (2πν)^{½−σ} (Σ_j ρ_j(v) ρ̄_j(w) W(σ+it, ν_j) W(σ−it, ν_j) + (4π)⁻¹ ∫ …)`

(`kuznetsov_same_sign_line`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## The unit `ζ(ξ) = (1+iξ)/√(1+ξ²)` and the line kernel -/

/-- The unit `ζ(ξ) = (1+iξ)/√(1+ξ²) = e^{i arctan ξ}`. -/
def cayleyUnit (ξ : ℝ) : ℂ := ((Real.sqrt (1 + ξ ^ 2))⁻¹ : ℝ) * (1 + Complex.I * ξ)

theorem sqrt_one_add_sq_pos (ξ : ℝ) : 0 < Real.sqrt (1 + ξ ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

theorem re_cayleyUnit (ξ : ℝ) : (cayleyUnit ξ).re = (Real.sqrt (1 + ξ ^ 2))⁻¹ := by
  simp [cayleyUnit]

theorem norm_cayleyUnit (ξ : ℝ) : ‖cayleyUnit ξ‖ = 1 := by
  have hs := sqrt_one_add_sq_pos ξ
  have hn : ‖(1 : ℂ) + Complex.I * ξ‖ = Real.sqrt (1 + ξ ^ 2) := by
    rw [show (1 : ℂ) + Complex.I * ξ = ⟨1, ξ⟩ from Complex.ext (by simp) (by simp),
      Complex.norm_def, Complex.normSq_mk]
    congr 1; ring
  rw [cayleyUnit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hs, hn,
    inv_mul_cancel₀ hs.ne']

/-- The same-sign line kernel `Ξ_σ(t, X) = ∫ (1+ξ²)^{−σ} ∫ e^{2itw} e^{−X ζ(ξ) cosh w} dw dξ`. -/
def sameSignKernel (σ t X : ℝ) : ℂ :=
  ∫ ξ : ℝ, (((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) *
    ∫ w : ℝ, cexp (2 * t * w * Complex.I) * cexp (-(X * cayleyUnit ξ * Real.cosh w))

/-! ## The substitution `y = λ eʷ` -/

theorem ofReal_exp_cpow (u : ℝ) (z : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ z = cexp (u * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]

theorem ofReal_cpow_two_mul {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ (2 * z) = ((x ^ 2 : ℝ) : ℂ) ^ z := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hx 2).ne'),
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log (pow_pos hx 2).le, Real.log_pow]
  push_cast
  ring_nf

/-- **The inner `y`-integral of the same-sign kernel on the line.** -/
theorem integral_Ioi_cpow_mul_kuzExp {μ ν q : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q) (t ξ : ℝ) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (2 * t * Complex.I - 1) *
        cexp (-(Kuznetsov.kuzRate μ ξ * y) -
          ((2 * Real.pi * ν : ℝ) : ℂ) / ((q : ℂ) * (1 - Complex.I * ξ) * y)) =
      (((ν / (μ * q * (1 + ξ ^ 2)) : ℝ)) : ℂ) ^ (t * Complex.I) *
        ∫ w : ℝ, cexp (2 * t * w * Complex.I) *
          cexp (-((4 * Real.pi * Real.sqrt (μ * ν / q) : ℝ) * cayleyUnit ξ * Real.cosh w)) := by
  set a := Real.sqrt (μ * ν / q) with ha_def
  set s := Real.sqrt (1 + ξ ^ 2) with hs_def
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hs : 0 < s := sqrt_one_add_sq_pos ξ
  have ha2 : a ^ 2 = μ * ν / q := Real.sq_sqrt (by positivity)
  have hs2 : s ^ 2 = 1 + ξ ^ 2 := Real.sq_sqrt (by positivity)
  set l := a / (μ * s) with hl_def
  have hl : 0 < l := by positivity
  have hl2 : l ^ 2 = ν / (μ * q * (1 + ξ ^ 2)) := by
    rw [hl_def, div_pow, mul_pow, ha2, hs2]; field_simp
  have himg : (fun w : ℝ => l * Real.exp w) '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    ext y
    simp only [Set.image_univ, Set.mem_range, Set.mem_Ioi]
    constructor
    · rintro ⟨w, rfl⟩; positivity
    · intro hy
      exact ⟨Real.log (y / l), by rw [Real.exp_log (div_pos hy hl)]; field_simp⟩
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := (univ : Set ℝ)) (f := fun w : ℝ => l * Real.exp w) (f' := fun w => l * Real.exp w)
    MeasurableSet.univ (fun x _ => ((Real.hasDerivAt_exp x).const_mul l).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective (mul_left_cancel₀ hl.ne' h))
    (fun y : ℝ => (y : ℂ) ^ (2 * t * Complex.I - 1) *
        cexp (-(Kuznetsov.kuzRate μ ξ * y) -
          ((2 * Real.pi * ν : ℝ) : ℂ) / ((q : ℂ) * (1 - Complex.I * ξ) * y)))
  rw [himg, setIntegral_univ] at hchange
  rw [hchange, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hξ := Kuznetsov.one_sub_I_mul_ne_zero ξ
  have hew : cexp (w : ℂ) ≠ 0 := Complex.exp_ne_zero _
  -- the power
  have hpow : ((l * Real.exp w : ℝ) : ℂ) ^ (2 * t * Complex.I - 1) =
      (l : ℂ) ^ (2 * t * Complex.I) * (l : ℂ)⁻¹ * (cexp (2 * t * w * Complex.I) * cexp (-(w : ℂ))) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hl.le (Real.exp_pos w).le,
      ofReal_exp_cpow, Complex.cpow_sub _ _ hlc, Complex.cpow_one, ← Complex.exp_add]
    rw [div_eq_mul_inv]
    congr 2
    ring
  have hl2c : (l : ℂ) ^ (2 * t * Complex.I) =
      (((ν / (μ * q * (1 + ξ ^ 2)) : ℝ)) : ℂ) ^ (t * Complex.I) := by
    rw [show (2 * t * Complex.I : ℂ) = 2 * (t * Complex.I) by ring, ofReal_cpow_two_mul hl, hl2]
  -- the exponent
  have hexp : -(Kuznetsov.kuzRate μ ξ * ((l * Real.exp w : ℝ) : ℂ)) -
      ((2 * Real.pi * ν : ℝ) : ℂ) / ((q : ℂ) * (1 - Complex.I * ξ) * ((l * Real.exp w : ℝ) : ℂ)) =
      -(((4 * Real.pi * a : ℝ) : ℂ) * cayleyUnit ξ * (Real.cosh w : ℂ)) := by
    rw [Kuznetsov.kuzRate, cayleyUnit, show Real.sqrt (1 + ξ ^ 2) = s from rfl,
      Complex.ofReal_cosh, Complex.cosh, Complex.exp_neg]
    have ha2c : (a : ℂ) ^ 2 * q = μ * ν := by
      have : a ^ 2 * q = μ * ν := by rw [ha2]; field_simp
      exact_mod_cast this
    have hs2c : (s : ℂ) ^ 2 = 1 + ξ ^ 2 := by exact_mod_cast hs2
    rw [hl_def]
    push_cast
    field_simp
    linear_combination (4 * (1 - Complex.I ^ 2 * (ξ : ℂ) ^ 2)) * ha2c - 4 * (μ : ℂ) * ν * hs2c -
      4 * (μ : ℂ) * ν * (ξ : ℂ) ^ 2 * Complex.I_sq
  rw [hpow, hexp, hl2c, Complex.real_smul, abs_of_pos (by positivity : (0 : ℝ) < l * Real.exp w)]
  push_cast
  rw [Complex.exp_neg]
  field_simp

theorem ofReal_cpow_mul_ofReal_div_cpow {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (z : ℂ) :
    ((x : ℝ) : ℂ) ^ z * (((y / x : ℝ)) : ℂ) ^ z = ((y : ℝ) : ℂ) ^ z := by
  rw [← Complex.mul_cpow_ofReal_nonneg hx.le (div_nonneg hy hx.le), ← Complex.ofReal_mul,
    mul_div_cancel₀ _ hx.ne']

/-- **The same-sign double integral on the line**: `V⁺(σ+it, σ−it; μ, ν, q) = (ν/(μq))^{it} Ξ_σ(t, X)`. -/
theorem kuzValuePlus_line {μ ν q σ : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q) (hσ : 1 < σ)
    (t : ℝ) :
    kuzValuePlus ((σ : ℂ) + t * Complex.I) ((σ : ℂ) - t * Complex.I) μ ν q =
      (((ν / (μ * q)) : ℝ) : ℂ) ^ (t * Complex.I) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / q)) := by
  have hre1 : ((σ : ℂ) + t * Complex.I).re = σ := by simp
  have hre2 : ((σ : ℂ) - t * Complex.I).re = σ := by simp
  have hint := integrable_kuzKernelPlus (a₁ := (σ : ℂ) + t * Complex.I)
    (a₂ := (σ : ℂ) - t * Complex.I) hμ hν hq (δ := (σ - 1 / 2) / 2) (by linarith)
    (by rw [hre1, hre2]; linarith) (by rw [hre2]; linarith)
  rw [kuzValuePlus, integral_integral_swap (f := fun y ξ => kuzKernelPlus ((σ : ℂ) + t * Complex.I)
    ((σ : ℂ) - t * Complex.I) μ ν q (y, ξ)) hint, sameSignKernel, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [kuzKernelPlus]
  have hξ : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  rw [integral_const_mul, show (σ : ℂ) + t * Complex.I - ((σ : ℂ) - t * Complex.I) - 1 =
    2 * t * Complex.I - 1 by ring, integral_Ioi_cpow_mul_kuzExp hμ hν hq t ξ]
  have hsplit : (((1 + ξ ^ 2 : ℝ)) : ℂ) ^ (-((σ : ℂ) - t * Complex.I)) =
      (((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) * (((1 + ξ ^ 2 : ℝ)) : ℂ) ^ (t * Complex.I) := by
    rw [show -((σ : ℂ) - t * Complex.I) = ((-σ : ℝ) : ℂ) + t * Complex.I by push_cast; ring,
      Complex.cpow_add _ _ (by exact_mod_cast hξ.ne'), Complex.ofReal_cpow hξ.le]
  have hcomb : (((1 + ξ ^ 2 : ℝ)) : ℂ) ^ (t * Complex.I) *
      (((ν / (μ * q * (1 + ξ ^ 2)) : ℝ)) : ℂ) ^ (t * Complex.I) =
      (((ν / (μ * q)) : ℝ) : ℂ) ^ (t * Complex.I) := by
    rw [show ν / (μ * q * (1 + ξ ^ 2)) = (ν / (μ * q)) / (1 + ξ ^ 2) by field_simp,
      ofReal_cpow_mul_ofReal_div_cpow hξ (by positivity)]
  rw [hsplit]
  linear_combination (((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) *
    (∫ w : ℝ, cexp (2 * t * w * Complex.I) *
      cexp (-((4 * Real.pi * Real.sqrt (μ * ν / q) : ℝ) * cayleyUnit ξ * Real.cosh w))) * hcomb

/-! ## The identity on the line -/

theorem diagPlus_congr {a₁ a₂ b₁ b₂ : ℂ} (h : a₁ + a₂ = b₁ + b₂) (μ ν : ℝ) (v w : DeckSpace N) :
    diagPlus a₁ a₂ μ ν v w = diagPlus b₁ b₂ μ ν v w := by
  rw [diagPlus, diagPlus, h]

theorem ratio_cpow_mul_diagPlus (a₁ a₂ : ℂ) {μ ν : ℝ} (hμ : μ ≠ 0) (v w : DeckSpace N) (z : ℂ) :
    (((ν / μ : ℝ)) : ℂ) ^ z * diagPlus a₁ a₂ μ ν v w = diagPlus a₁ a₂ μ ν v w := by
  by_cases h : μ = ν
  · rw [← h, div_self hμ, Complex.ofReal_one, Complex.one_cpow, one_mul]
  · simp [diagPlus, h]

/-- **The same-sign Kuznetsov identity on the line `s̄₁ = σ + it`, `s₂ = σ − it`.** -/
theorem kuznetsov_same_sign_line (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {μ ν : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen ν w)
    {n m : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n) (hm : ν * ((N + 1 : ℕ) : ℝ) = m) :
    2 * diagPlus (σ : ℂ) σ μ ν v w +
      2 * ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 *
        (((((r.1.1 0 : ℝ)) ^ 2) ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / ((r.1.1 0 : ℝ)) ^ 2)) =
      4 * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2)) *
        ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2)) *
        ((∑' j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j ν w) *
            whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1) *
            whittMellin ((σ : ℂ) - t * Complex.I) (specParam j.1)) +
          (4 * Real.pi : ℂ)⁻¹ * ∫ r : ℝ, ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
            conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
            whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I) *
            whittMellin ((σ : ℂ) - t * Complex.I) (r * Complex.I)) := by
  set E : ℂ := (((ν / μ : ℝ)) : ℂ) ^ (t * Complex.I) with hE
  have hE0 : E ≠ 0 := by
    rw [hE, Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (div_pos hν hμ).ne' (by exact_mod_cast h.1)
  have hs : 1 < ((σ : ℂ) - t * Complex.I).re := by simp [hσ]
  have hconj : conj ((σ : ℂ) - t * Complex.I) = (σ : ℂ) + t * Complex.I := by
    simp [map_sub, Complex.conj_ofReal]
  have h := kuznetsov_same_sign_explicit hN hs hs hμ hν hv hw hn hm
  rw [hconj] at h
  refine mul_left_cancel₀ hE0 ?_
  -- the geometric side
  have hrow : ∀ r : ReducedRow, rowWeightPlus μ ν v w r.1 *
      (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I)) *
      kuzValuePlus ((σ : ℂ) + t * Complex.I) ((σ : ℂ) - t * Complex.I) μ ν ((r.1.1 0 : ℝ) ^ 2) =
      E * (rowWeightPlus μ ν v w r.1 * (((((r.1.1 0 : ℝ)) ^ 2) ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / ((r.1.1 0 : ℝ)) ^ 2))) := fun r => by
    have hq : 0 < ((r.1.1 0 : ℝ)) ^ 2 := by
      have : (r.1.1 0 : ℝ) ≠ 0 := by exact_mod_cast r.2.1
      positivity
    rw [kuzValuePlus_line hμ hν hq hσ t]
    have hsplit : (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I)) =
        (((((r.1.1 0 : ℝ)) ^ 2) ^ (-σ) : ℝ) : ℂ) *
          (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (t * Complex.I) := by
      rw [show -((σ : ℂ) - t * Complex.I) = ((-σ : ℝ) : ℂ) + t * Complex.I by push_cast; ring,
        Complex.cpow_add _ _ (by exact_mod_cast hq.ne'), Complex.ofReal_cpow hq.le]
    have hcomb : (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (t * Complex.I) *
        (((ν / (μ * (r.1.1 0 : ℝ) ^ 2)) : ℝ) : ℂ) ^ (t * Complex.I) = E := by
      rw [hE, show ν / (μ * (r.1.1 0 : ℝ) ^ 2) = (ν / μ) / (r.1.1 0 : ℝ) ^ 2 by field_simp,
        ofReal_cpow_mul_ofReal_div_cpow hq (div_pos hν hμ).le]
    rw [hsplit, ← hcomb]
    ring
  -- the spectral factors
  have hπμ : (0 : ℝ) < 2 * Real.pi * μ := by positivity
  have hπν : (0 : ℝ) < 2 * Real.pi * ν := by positivity
  have hfac : ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)) *
      ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I - 1 / 2)) =
      E * (((2 * Real.pi * μ : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2)) *
        ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2))) := by
    have hμc : ((2 * Real.pi * μ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπμ.ne'
    have hνc : ((2 * Real.pi * ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπν.ne'
    have hEμ : ((2 * Real.pi * μ : ℝ) : ℂ) ^ (t * Complex.I) * E =
        ((2 * Real.pi * ν : ℝ) : ℂ) ^ (t * Complex.I) := by
      rw [hE, show ν / μ = (2 * Real.pi * ν) / (2 * Real.pi * μ) by field_simp,
        ofReal_cpow_mul_ofReal_div_cpow hπμ hπν.le]
    rw [show -((σ : ℂ) + t * Complex.I - 1 / 2) = -((σ : ℂ) - 1 / 2) + -(t * Complex.I) by ring,
      show -((σ : ℂ) - t * Complex.I - 1 / 2) = -((σ : ℂ) - 1 / 2) + t * Complex.I by ring,
      Complex.cpow_add _ _ hμc, Complex.cpow_add _ _ hνc,
      Complex.cpow_neg ((2 * Real.pi * μ : ℝ) : ℂ) ((t : ℂ) * Complex.I), ← hEμ]
    have hne : ((2 * Real.pi * μ : ℝ) : ℂ) ^ (t * Complex.I) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hμc h.1
    field_simp
  rw [diagPlus_congr (b₁ := (σ : ℂ)) (b₂ := (σ : ℂ)) (by ring)] at h
  rw [tsum_congr hrow, mul_assoc 4, hfac, tsum_mul_left] at h
  rw [mul_add, mul_add, ← mul_assoc E 2, mul_comm E 2, mul_assoc 2 E,
    ratio_cpow_mul_diagPlus _ _ hμ.ne']
  linear_combination h

end

end GaloisForLFunctions.RHTower.DeckPointPair
