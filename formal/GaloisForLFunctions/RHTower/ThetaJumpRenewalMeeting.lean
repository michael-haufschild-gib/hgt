import GaloisForLFunctions.RHTower.ThetaReflectedJumpExponents

/-!
# The theta jump law meets the renewal phase; a positive-real renewal function

With `a = 1/4`, `c = Θ(1)`, the renewal transforms `C(r) = ∫₀^∞ Q cos(r·)`, `S(r) = ∫₀^∞ Q sin(r·)`
and the one-port formula `D(-ir) = c e^{-C(r) - iS(r)}`:

* `G'(2r) = 2cr e^{-C(r)} [a cos S(r) - r sin S(r)]` and
  `B(2r) = 2cr {r - e^{-C(r)} [r cos S(r) + a sin S(r)]} > 0`;
* the cumulative renewal inequality `∫₀^r s e^{-C(s)} [a cos S(s) - s sin S(s)] ds = G(2r)/(4c) > 0`.

With `N(λ) = ∫₀^∞ e^{-λt} ν_renewal`, the one-port formula reads `h(2iλ) = ac - (a + λ)N(λ)` for
all complex `λ`, and `H(λ) = λ[ac - (a + λ)N(λ)] = ½∫₀^∞ ω(x)(1 - e^{-2λx}) dx` is positive real:
`Re H > 0` on `Re λ > 0`, `conj H(λ) = H(conj λ)`, and its Pick kernel
`(H(λ) + conj H(μ))/(λ + μ̄)` is positive semidefinite (Cauchy-kernel Gram representation).
Nonzero Xi zeros are the solutions of `H(λ) = H(-λ)`, `H(λ) - H(-λ) = λ Ξ(2iλ)`.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta
open scoped ComplexConjugate ComplexOrder

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Meeting the renewal phase on the real axis -/

/-- `Ξ(2r) = 2c e^{-C(r)} (a cos S(r) - r sin S(r))`. -/
theorem Xi_two_mul_eq_renewal (r : ℝ) :
    Xi (2 * r) = 2 * Θ 1 * Real.exp (-thetaRenewalRealCos r) *
      (1 / 4 * Real.cos (thetaRenewalRealSin r) - r * Real.sin (thetaRenewalRealSin r)) := by
  have h := thetaOneSidedConnection_two_mul_eq_denominator (r : ℂ)
  rw [thetaRenewalDenominator_neg_I_mul, cexp_neg_add_mul_I] at h
  rw [Xi_eq_two_mul_re_thetaOneSidedConnection, show ((2 * r : ℝ) : ℂ) = 2 * (r : ℂ) by push_cast; ring,
    h]
  simp only [add_re, mul_re, sub_re, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    div_ofNat_re, div_ofNat_im, one_re, one_im]
  ring

/-- **(9).** `G'(2r) = 2cr e^{-C(r)} [a cos S(r) - r sin S(r)]`. -/
theorem hasDerivAt_thetaDispersionExponentReal_two_mul (r : ℝ) :
    HasDerivAt thetaDispersionExponentReal
      (2 * Θ 1 * r * Real.exp (-thetaRenewalRealCos r) *
        (1 / 4 * Real.cos (thetaRenewalRealSin r) - r * Real.sin (thetaRenewalRealSin r))) (2 * r) := by
  refine (hasDerivAt_thetaDispersionExponentReal (2 * r)).congr_deriv ?_
  rw [Xi_two_mul_eq_renewal]; ring

/-- **(10).** `B(2r) = 2cr {r - e^{-C(r)} [r cos S(r) + a sin S(r)]} > 0` for `r > 0`. -/
theorem thetaJumpCosineMass_two_mul_eq {r : ℝ} (hr : 0 < r) :
    thetaJumpCosineMass (2 * r) = 2 * Θ 1 * r * (r - Real.exp (-thetaRenewalRealCos r) *
        (r * Real.cos (thetaRenewalRealSin r) + 1 / 4 * Real.sin (thetaRenewalRealSin r))) ∧
      0 < thetaJumpCosineMass (2 * r) := by
  refine ⟨?_, thetaJumpCosineMass_pos (by positivity)⟩
  have h := (pi_mul_thetaPortDensity_sq_eq_renewal (u := 2 * r) (by positivity)).1
  rw [show 2 * r / 2 = r by ring] at h
  rw [thetaJumpCosineMass_eq_pi_mul_thetaPortDensity (by positivity),
    show Real.pi * (2 * r) * thetaPortDensity ((2 * r) ^ 2) =
      2 * r * (Real.pi * thetaPortDensity ((2 * r) ^ 2)) by ring, h]
  ring

/-- **(11).** The cumulative renewal inequality
`∫₀^r s e^{-C(s)} [a cos S(s) - s sin S(s)] ds = G(2r)/(4c) > 0` for `r > 0`. -/
theorem integral_renewal_phase_eq {r : ℝ} :
    ∫ s in (0 : ℝ)..r, s * Real.exp (-thetaRenewalRealCos s) *
      (1 / 4 * Real.cos (thetaRenewalRealSin s) - s * Real.sin (thetaRenewalRealSin s)) =
      thetaDispersionExponentReal (2 * r) / (4 * Θ 1) := by
  have hc := thetaSeam_pos
  have hpt : ∀ s : ℝ, s * Real.exp (-thetaRenewalRealCos s) *
      (1 / 4 * Real.cos (thetaRenewalRealSin s) - s * Real.sin (thetaRenewalRealSin s)) =
      1 / (4 * Θ 1) * ((2 * s) * Xi (2 * s)) := by
    intro s
    rw [Xi_two_mul_eq_renewal]
    field_simp
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun v => v * Xi v) (two_ne_zero), mul_zero,
    integral_mul_Xi_eq]
  field_simp
  ring

theorem integral_renewal_phase_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ s in (0 : ℝ)..r, s * Real.exp (-thetaRenewalRealCos s) *
      (1 / 4 * Real.cos (thetaRenewalRealSin s) - s * Real.sin (thetaRenewalRealSin s)) := by
  rw [integral_renewal_phase_eq]
  exact div_pos (thetaDispersionExponentReal_pos (by positivity)) (by positivity [thetaSeam_pos])

/-! ## The positive-real renewal function -/

/-- **The one-port formula.** `h(2iλ) = ac - (a + λ) N(λ)` for every complex `λ`. -/
theorem thetaOneSidedConnection_two_I_mul_eq_renewal (s : ℂ) :
    thetaOneSidedConnection (2 * I * s) =
      1 / 4 * (Θ 1 : ℂ) - (1 / 4 + s) * thetaRenewalLaplace s := by
  rw [thetaOneSidedConnection_two_I_mul, thetaRenewalLaplace_eq, jacobiThetaSum_one_eq]
  ring

/-- The positive-real function `H(λ) = λ [ac - (a + λ) N(λ)]`. -/
def thetaRenewalPositiveReal (s : ℂ) : ℂ :=
  s * (1 / 4 * (Θ 1 : ℂ) - (1 / 4 + s) * thetaRenewalLaplace s)

/-- **(12).** `H(λ) = ½ ∫₀^∞ ω(x) (1 - e^{-2λx}) dx` for every complex `λ`. -/
theorem thetaRenewalPositiveReal_eq (s : ℂ) :
    thetaRenewalPositiveReal s =
      1 / 2 * ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) * (1 - cexp (-(2 * s * x))) := by
  have h := thetaJumpExponent_eq (2 * I * s)
  rw [thetaOneSidedConnection_two_I_mul_eq_renewal] at h
  rw [thetaRenewalPositiveReal]
  have hK : thetaJumpExponent (2 * I * s) =
      ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) * (1 - cexp (-(2 * s * x))) := by
    rw [thetaJumpExponent]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [show I * (2 * I * s) * (x : ℂ) = -(2 * s * x) by linear_combination (2 * s * x) * I_sq]
  rw [← hK, h]
  linear_combination (s * (1 / 4 * (Θ 1 : ℂ) - (1 / 4 + s) * thetaRenewalLaplace s)) * I_sq

/-- **(12).** `Re H(λ) > 0` on the open right half-plane. -/
theorem re_thetaRenewalPositiveReal_pos {s : ℂ} (hs : 0 < s.re) : 0 < (thetaRenewalPositiveReal s).re := by
  rw [thetaRenewalPositiveReal_eq]
  have hint : IntegrableOn (fun x : ℝ => (thetaJumpDensity x : ℂ) * (1 - cexp (-(2 * s * x))))
      (Ioi 0) := by
    have := integrableOn_thetaJumpExponent (2 * I * s)
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only
    rw [show I * (2 * I * s) * (x : ℂ) = -(2 * s * x) by linear_combination (2 * s * x) * I_sq]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [Complex.mul_re, ← hre]
  simp only [div_ofNat_re, one_re, div_ofNat_im, one_im, zero_div, zero_mul, sub_zero]
  refine mul_pos (by norm_num) (setIntegral_Ioi_pos (hint.re) fun x hx => ?_)
  rw [Complex.re_ofReal_mul]
  refine mul_pos (thetaJumpDensity_pos hx) ?_
  rw [Complex.sub_re, Complex.one_re, sub_pos]
  have h1 : (cexp (-(2 * s * x))).re ≤ ‖cexp (-(2 * s * x))‖ := Complex.re_le_norm _
  rw [Complex.norm_exp] at h1
  have h2 : (-(2 * s * (x : ℂ))).re = -(2 * s.re * x) := by simp
  rw [h2] at h1
  have h3 : Real.exp (-(2 * s.re * x)) < 1 := by
    rw [← Real.exp_zero]; have : (0 : ℝ) < x := hx
    exact Real.exp_lt_exp.mpr (by nlinarith)
  linarith

/-- The nonzero zero equation `H(λ) = H(-λ)`: `H(λ) - H(-λ) = λ Ξ(2iλ)`. -/
theorem thetaRenewalPositiveReal_sub_neg (s : ℂ) :
    thetaRenewalPositiveReal s - thetaRenewalPositiveReal (-s) = s * XiC (2 * I * s) := by
  rw [XiC_eq_thetaOneSidedConnection_add, show -(2 * I * s) = 2 * I * (-s) by ring,
    thetaOneSidedConnection_two_I_mul_eq_renewal, thetaOneSidedConnection_two_I_mul_eq_renewal,
    thetaRenewalPositiveReal, thetaRenewalPositiveReal]
  ring

theorem XiC_two_I_mul_eq_zero_iff_positiveReal {s : ℂ} (hs : s ≠ 0) :
    XiC (2 * I * s) = 0 ↔ thetaRenewalPositiveReal s = thetaRenewalPositiveReal (-s) := by
  have h := thetaRenewalPositiveReal_sub_neg s
  constructor
  · intro hX; rw [hX, mul_zero] at h; exact sub_eq_zero.mp h
  · intro hH; rw [hH, sub_self] at h; exact (mul_eq_zero.mp h.symm).resolve_left hs

/-- At a zero with `Re λ > 0` the reflected value `H(-λ)` lies in the open right half-plane. -/
theorem re_thetaRenewalPositiveReal_neg_pos {s : ℂ} (hs : 0 < s.re) (hX : XiC (2 * I * s) = 0) :
    0 < (thetaRenewalPositiveReal (-s)).re := by
  have h := (XiC_two_I_mul_eq_zero_iff_positiveReal (fun h => by rw [h] at hs; simp at hs)).mp hX
  rw [← h]; exact re_thetaRenewalPositiveReal_pos hs

/-! ## The Pick kernel of `H` is positive semidefinite -/

theorem ofReal_norm_sq_sum_mul_cexp {n : ℕ} (a lam : Fin n → ℂ) (t : ℝ) :
    ((‖∑ j, a j * cexp (-lam j * t)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ k, a j * conj (a k) * cexp (-(lam j + conj (lam k)) * t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]
  rw [show -(lam j + conj (lam k)) * (t : ℂ) = -lam j * t + -conj (lam k) * t by ring,
    Complex.exp_add]
  ring

/-- **Cauchy kernel.** `Σ a_j ā_k/(λ_j + λ̄_k) = ∫₀^∞ |Σ a_j e^{-λ_j t}|² dt` for `Re λ_j > 0`. -/
theorem sum_div_add_conj_eq_integral {n : ℕ} (lam : Fin n → ℂ) (hlam : ∀ j, 0 < (lam j).re)
    (a : Fin n → ℂ) :
    ∑ j, ∑ k, a j * conj (a k) / (lam j + conj (lam k)) =
      ((∫ t in Ioi (0 : ℝ), ‖∑ j, a j * cexp (-lam j * t)‖ ^ 2 : ℝ) : ℂ) := by
  have hw : ∀ j k, (-(lam j + conj (lam k))).re < 0 := fun j k => by
    simp only [neg_re, add_re, conj_re]; linarith [hlam j, hlam k]
  have hint : ∀ j k, IntegrableOn (fun t : ℝ => a j * conj (a k) *
      cexp (-(lam j + conj (lam k)) * t)) (Ioi 0) := fun j k =>
    (integrableOn_exp_mul_complex_Ioi (hw j k) 0).const_mul _
  rw [← integral_complex_ofReal]
  simp_rw [ofReal_norm_sq_sum_mul_cexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hne : lam j + conj (lam k) ≠ 0 := fun h => by
    have := hw j k; rw [h] at this; simp at this
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (hw j k) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

/-- **Truncated Cauchy kernel.**
`Σ a_j ā_k (1 - e^{-2(λ_j + λ̄_k) y})/(λ_j + λ̄_k) = 2 ∫₀^y |Σ a_j e^{-2λ_j s}|² ds`. -/
theorem sum_one_sub_exp_div_eq_integral {n : ℕ} (lam : Fin n → ℂ) (hlam : ∀ j, 0 < (lam j).re)
    (a : Fin n → ℂ) (y : ℝ) :
    ∑ j, ∑ k, a j * conj (a k) * ((1 - cexp (-(2 * (lam j + conj (lam k))) * y)) /
        (lam j + conj (lam k))) =
      ((2 * ∫ s in (0 : ℝ)..y, ‖∑ j, a j * cexp (-(2 * lam j) * s)‖ ^ 2 : ℝ) : ℂ) := by
  have hne : ∀ j k, lam j + conj (lam k) ≠ 0 := fun j k h => by
    have := congrArg Complex.re h
    simp only [add_re, conj_re, zero_re] at this; linarith [hlam j, hlam k]
  rw [Complex.ofReal_mul, ← intervalIntegral.integral_ofReal]
  have hpt : ∀ s : ℝ, ((‖∑ j, a j * cexp (-(2 * lam j) * s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ k, a j * conj (a k) * cexp (-(2 * (lam j + conj (lam k))) * s) := by
    intro s
    rw [ofReal_norm_sq_sum_mul_cexp]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_ofNat]; ring_nf
  simp_rw [hpt]
  have hcont : ∀ j k, IntervalIntegrable (fun s : ℝ => a j * conj (a k) *
      cexp (-(2 * (lam j + conj (lam k))) * s)) volume 0 y := fun j k =>
    (by fun_prop : Continuous fun s : ℝ => a j * conj (a k) *
      cexp (-(2 * (lam j + conj (lam k))) * s)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (f := fun j (s : ℝ) => ∑ k, a j * conj (a k) *
      cexp (-(2 * (lam j + conj (lam k))) * s)) fun j _ =>
    (continuous_finsetSum _ fun k _ => by fun_prop).intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum (f := fun k (s : ℝ) => a j * conj (a k) *
      cexp (-(2 * (lam j + conj (lam k))) * s)) fun k _ => hcont j k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 : -(2 * (lam j + conj (lam k))) ≠ 0 := by
    simpa using hne j k
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex h2]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  push_cast
  ring

/-- The Pick kernel `(H(λ) + conj H(μ))/(λ + conj μ)` of the positive-real function `H`. -/
def thetaRenewalPickKernel (lam mu : ℂ) : ℂ :=
  (thetaRenewalPositiveReal lam + conj (thetaRenewalPositiveReal mu)) / (lam + conj mu)

theorem integrableOn_thetaJumpDensity_mul_one_sub_exp (l : ℂ) :
    IntegrableOn (fun x : ℝ => (thetaJumpDensity x : ℂ) * (1 - cexp (-(2 * l) * x))) (Ioi 0) := by
  have := integrableOn_thetaJumpExponent (2 * I * l)
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only
  rw [show I * (2 * I * l) * (x : ℂ) = -(2 * l) * x by linear_combination (2 * l * x) * I_sq]

theorem thetaRenewalPositiveReal_eq' (l : ℂ) :
    thetaRenewalPositiveReal l =
      1 / 2 * ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) * (1 - cexp (-(2 * l) * x)) := by
  rw [thetaRenewalPositiveReal_eq]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring_nf

/-- `H` has real coefficients: `conj H(λ) = H(conj λ)`. -/
theorem conj_thetaRenewalPositiveReal (l : ℂ) :
    conj (thetaRenewalPositiveReal l) = thetaRenewalPositiveReal (conj l) := by
  rw [thetaRenewalPositiveReal_eq', thetaRenewalPositiveReal_eq', map_mul, ← integral_conj]
  congr 1
  · rw [map_div₀, map_one, map_ofNat]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [map_mul, map_sub, map_one, Complex.conj_ofReal, ← Complex.exp_conj, map_neg,
      map_ofNat]

/-- The kernel as one integral: `(H(λ) + conj H(μ))/(λ + conj μ) = ½∫ ω T_{λ,μ}` with
`T_{λ,μ}(x) = (2 - e^{-2λx} - e^{-2μ̄x})/(λ + μ̄)`. -/
theorem thetaRenewalPickKernel_eq (lam mu : ℂ) :
    thetaRenewalPickKernel lam mu = 1 / 2 * ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) *
      ((2 - cexp (-(2 * lam) * x) - cexp (-(2 * conj mu) * x)) / (lam + conj mu)) := by
  rw [thetaRenewalPickKernel, conj_thetaRenewalPositiveReal, thetaRenewalPositiveReal_eq',
    thetaRenewalPositiveReal_eq', ← mul_add, ← integral_add
      (integrableOn_thetaJumpDensity_mul_one_sub_exp lam)
      (integrableOn_thetaJumpDensity_mul_one_sub_exp (conj mu))]
  rw [show (fun x : ℝ => (thetaJumpDensity x : ℂ) *
      ((2 - cexp (-(2 * lam) * x) - cexp (-(2 * conj mu) * x)) / (lam + conj mu))) =
      fun x => (lam + conj mu)⁻¹ * ((thetaJumpDensity x : ℂ) * (1 - cexp (-(2 * lam) * x)) +
        (thetaJumpDensity x : ℂ) * (1 - cexp (-(2 * conj mu) * x))) by
    funext x; rw [div_eq_inv_mul]; ring, integral_const_mul]
  rw [div_eq_inv_mul]; ring

/-- **The Pick kernel is positive semidefinite on the right half-plane.** For points `λ_j` with
`Re λ_j > 0` and coefficients `c_j`, `Σ c_j c̄_k (H(λ_j) + conj H(λ_k))/(λ_j + λ̄_k) ≥ 0`. -/
theorem thetaRenewalPickKernel_nonneg {n : ℕ} (lam : Fin n → ℂ) (hlam : ∀ j, 0 < (lam j).re)
    (c : Fin n → ℂ) :
    0 ≤ ∑ j, ∑ k, c j * conj (c k) * thetaRenewalPickKernel (lam j) (lam k) := by
  set T : Fin n → Fin n → ℝ → ℂ := fun j k x =>
    (2 - cexp (-(2 * lam j) * x) - cexp (-(2 * conj (lam k)) * x)) / (lam j + conj (lam k))
  have hTint : ∀ j k, IntegrableOn (fun x => c j * conj (c k) *
      ((thetaJumpDensity x : ℂ) * T j k x)) (Ioi 0) := by
    intro j k
    refine IntegrableOn.congr_fun (Integrable.const_mul
      ((integrableOn_thetaJumpDensity_mul_one_sub_exp (lam j)).add
      (integrableOn_thetaJumpDensity_mul_one_sub_exp (conj (lam k))))
      (c j * conj (c k) / (lam j + conj (lam k)))) (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, T]
    rw [div_eq_inv_mul, div_eq_inv_mul]; ring
  have hsum : ∑ j, ∑ k, c j * conj (c k) * thetaRenewalPickKernel (lam j) (lam k) =
      1 / 2 * ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) *
        ∑ j, ∑ k, c j * conj (c k) * T j k x := by
    simp_rw [thetaRenewalPickKernel_eq]
    rw [show (fun x : ℝ => (thetaJumpDensity x : ℂ) * ∑ j, ∑ k, c j * conj (c k) * T j k x) =
        fun x => ∑ j, ∑ k, c j * conj (c k) * ((thetaJumpDensity x : ℂ) * T j k x) by
      funext x; simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_; ring,
      integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hTint j k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hTint j k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]; ring
  set q : ℝ → ℝ := fun x => (∫ t in Ioi (0 : ℝ),
      ‖∑ j, c j * (1 - cexp (-(2 * lam j) * x)) * cexp (-lam j * t)‖ ^ 2) +
    2 * ∫ s in (0 : ℝ)..x, ‖∑ j, c j * cexp (-(2 * lam j) * s)‖ ^ 2
  have hq : ∀ x, 0 ≤ x → 0 ≤ q x := fun x hx =>
    add_nonneg (setIntegral_nonneg measurableSet_Ioi fun _ _ => by positivity)
      (mul_nonneg two_pos.le (intervalIntegral.integral_nonneg hx fun _ _ => by positivity))
  have hQ : ∀ x : ℝ, ∑ j, ∑ k, c j * conj (c k) * T j k x = (q x : ℂ) := by
    intro x
    have h1 := sum_div_add_conj_eq_integral lam hlam (fun j => c j * (1 - cexp (-(2 * lam j) * x)))
    have h2 := sum_one_sub_exp_div_eq_integral lam hlam c x
    simp only [q, Complex.ofReal_add]
    rw [← h1, ← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : conj (cexp (-(2 * lam k) * x)) = cexp (-(2 * conj (lam k)) * x) := by
      rw [← Complex.exp_conj]; simp [map_mul, map_neg, Complex.conj_ofReal, map_ofNat]
    have hprod : cexp (-(2 * lam j) * x) * cexp (-(2 * conj (lam k)) * x) =
        cexp (-(2 * (lam j + conj (lam k))) * x) := by
      rw [← Complex.exp_add]; ring_nf
    simp only [T]
    rw [map_mul, map_sub, map_one, hc, ← hprod]
    ring
  rw [hsum]
  have hreal : ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) * ∑ j, ∑ k, c j * conj (c k) * T j k x =
      ((∫ x in Ioi (0 : ℝ), thetaJumpDensity x * q x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [hQ]; push_cast; rfl
  rw [hreal]
  have hnn : 0 ≤ ∫ x in Ioi (0 : ℝ), thetaJumpDensity x * q x :=
    setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (thetaJumpDensity_pos hx).le (hq x (le_of_lt hx))
  have : (0 : ℂ) ≤ ((1 / 2 * ∫ x in Ioi (0 : ℝ), thetaJumpDensity x * q x : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by positivity)
  simpa using this

end

end RHTower
