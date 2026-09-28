import GaloisForLFunctions.RHTower.ThetaCausalGermPort
import GaloisForLFunctions.RHTower.ThetaDeletionInversionCommutator

/-!
# Prime-moment ports of the theta symmetrized transform

For a port `E` with `E + E# = X` (`X` the symmetrized theta transform, `F#(w) = conj F(-w̄)`),
`D_E = |E|² - |E#|² = 2Re(E X̄) - |X|² = 2|X|² Re[(E - X/2)/X]`; its normal derivative on the
imaginary axis is `4⟪E, E'⟫`, and `2⟪E, X'⟫` at a zero of `X`.

With the one-prime Euler multiplier `A_p(w) = 1 - p^{-1/2} cosh(w log p)` and a real clock gauge
`μ`, the ports `E_{p,μ} = X/2 + A_p X' + μ A_p' X/log p` (deletion-after-clock `μ = 0`,
clock-after-deletion `μ = log p`, i.e. `X/2 + (A_p X)'`) are anti-reflected channels.  At every
real Xi zero their normal derivative is `2[1 - p^{-1/2}cos(γ log p)]Ξ'(γ)² > 0`, for every gauge.

* Clock-after-deletion fails on the whole right half-plane (`D_p(α) < 0` for large real `α`), has
  the exact center curvature condition `X''(0)/X(0) ≥ rL²/(1 - r)` (satisfied for large `p`), and
  the wall values `A_p(1/2) = (1 - p⁻¹)/2`, `Y_p'(1/2) = (1 - p⁻¹)[X'(1/2) - log p X(1/2)]/2` force
  a negative defect inside the strip once `log p > X'(1/2)/X(1/2)`.
* Deletion-after-clock is positive on the real radius `(0, 1/2]`; `|1 - A_p| ≤ (1 + p⁻¹)/2 < 1` on
  the closed strip; the phase-aperture inequality `Re(X'/X) > r cosh(L Re w)|X'/X|` is sufficient;
  its critical-boundary normal derivative is
  `[1 - r cos(Lγ)](x'² - x x'') - rL sin(Lγ) x x'`.
* As `p → ∞` the clock-after-deletion port converges uniformly on compacts of `|Re w| < 1/2` to
  `X/2 + X'`; at the wall `A_p(1/2 + iβ) = 1 - [p^{iβ} + p^{-1}p^{-iβ}]/2`.
-/
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate

namespace RHTower

noncomputable section

/-! ## General anti-reflected ports -/

/-- The modulus imbalance `D_E = |E|² - |E#|²` of a port. -/
def portImbalance (E : ℂ → ℂ) (w : ℂ) : ℝ := ‖E w‖ ^ 2 - ‖halfPortReflect E w‖ ^ 2

/-- For a port with `E + E# = X`, `D_E = 2 Re(E X̄) - |X|²`. -/
theorem portImbalance_eq_of_add_reflect {E : ℂ → ℂ} (hE : ∀ w, E w + halfPortReflect E w =
    thetaSymmetrizedPort w) (w : ℂ) :
    portImbalance E w = 2 * (E w * conj (thetaSymmetrizedPort w)).re - ‖thetaSymmetrizedPort w‖ ^ 2 := by
  rw [portImbalance, show halfPortReflect E w = thetaSymmetrizedPort w - E w by rw [← hE w]; ring]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

/-- **(15).** Away from the zeros of `X`, `D_E = 2|X|² Re[(E - X/2)/X]`. -/
theorem portImbalance_eq_re_div {E : ℂ → ℂ} (hE : ∀ w, E w + halfPortReflect E w =
    thetaSymmetrizedPort w) {w : ℂ} (hX : thetaSymmetrizedPort w ≠ 0) :
    portImbalance E w = 2 * ‖thetaSymmetrizedPort w‖ ^ 2 *
      ((E w - thetaSymmetrizedPort w / 2) / thetaSymmetrizedPort w).re := by
  rw [portImbalance_eq_of_add_reflect hE]
  set X := thetaSymmetrizedPort w
  have h1 : (E w - X / 2) / X * ((‖X‖ ^ 2 : ℝ) : ℂ) = (E w - X / 2) * conj X := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']; field_simp
  have h2 := congrArg Complex.re h1
  rw [Complex.re_mul_ofReal] at h2
  have hXX : (X * conj X).re = ‖X‖ ^ 2 := by
    rw [Complex.mul_conj']; norm_cast
  have h3 : ((E w - X / 2) * conj X).re = (E w * conj X).re - ‖X‖ ^ 2 / 2 := by
    rw [sub_mul, Complex.sub_re, show X / 2 * conj X = (X * conj X) / 2 by ring,
      Complex.div_ofNat_re, hXX]
  rw [mul_assoc, mul_comm (‖X‖ ^ 2), h2, h3]
  ring

/-- The general normal derivative: `∂_α D_E(α + iγ)|₀ = 4⟪E(iγ), E'(iγ)⟫`. -/
theorem hasDerivAt_portImbalance {E : ℂ → ℂ} {γ : ℝ} {E' : ℂ} (hE : HasDerivAt E E' (γ * I)) :
    HasDerivAt (fun α : ℝ => portImbalance E (α + γ * I)) (4 * inner ℝ (E (γ * I)) E') 0 := by
  have hE0 : HasDerivAt E E' (((0 : ℝ) : ℂ) + γ * I) := by rw [Complex.ofReal_zero, zero_add]; exact hE
  have h1 : HasDerivAt (fun α : ℝ => E (α + γ * I)) E' 0 := by
    have h := (hE0.comp (((0 : ℝ) : ℂ)) ((hasDerivAt_id (((0 : ℝ) : ℂ))).add_const
      ((γ : ℂ) * I))).comp_ofReal
    simpa using h
  have hE0' : HasDerivAt E E' (-((0 : ℝ) : ℂ) + γ * I) := by
    rw [Complex.ofReal_zero, neg_zero, zero_add]; exact hE
  have h2 : HasDerivAt (fun α : ℝ => E (-α + γ * I)) (-E') 0 := by
    have h := (hE0'.comp (((0 : ℝ) : ℂ)) ((hasDerivAt_neg (((0 : ℝ) : ℂ))).add_const
      ((γ : ℂ) * I))).comp_ofReal
    simpa using h
  have hfun : (fun α : ℝ => portImbalance E (α + γ * I)) =
      fun α : ℝ => ‖E (α + γ * I)‖ ^ 2 - ‖E (-α + γ * I)‖ ^ 2 := by
    funext α
    rw [portImbalance, halfPortReflect, Complex.norm_conj]
    congr 3
    simp [map_add, map_mul]
    ring_nf
  rw [hfun]
  refine (h1.norm_sq.sub h2.norm_sq).congr_deriv ?_
  simp only [Complex.ofReal_zero, neg_zero, zero_add, inner_neg_right]
  ring

/-- At a zero of `X`, a port with `E + E# = X` has normal derivative `2⟪E(iγ), X'(iγ)⟫`. -/
theorem hasDerivAt_portImbalance_of_zero {E : ℂ → ℂ} {γ : ℝ} {E' : ℂ} (hE : HasDerivAt E E' (γ * I))
    (hsym : ∀ w, E w + halfPortReflect E w = thetaSymmetrizedPort w)
    (hX : thetaSymmetrizedPort (γ * I) = 0) :
    HasDerivAt (fun α : ℝ => portImbalance E (α + γ * I))
      (2 * inner ℝ (E (γ * I)) (deriv thetaSymmetrizedPort (γ * I))) 0 := by
  have hX0 := hasDerivAt_thetaSymmetrizedPort ((γ : ℂ) * I)
  have hEX : HasDerivAt (fun w => thetaSymmetrizedPort w - E w)
      (deriv thetaSymmetrizedPort (γ * I) - E') (γ * I) := hX0.sub hE
  have hline0 : ∀ {F : ℂ → ℂ} {F' : ℂ}, HasDerivAt F F' (γ * I) →
      HasDerivAt (fun α : ℝ => F (α + γ * I)) F' 0 := by
    intro F F' hF
    have hF0 : HasDerivAt F F' (((0 : ℝ) : ℂ) + γ * I) := by
      rw [Complex.ofReal_zero, zero_add]; exact hF
    have h := (hF0.comp (((0 : ℝ) : ℂ)) ((hasDerivAt_id (((0 : ℝ) : ℂ))).add_const
      ((γ : ℂ) * I))).comp_ofReal
    simpa using h
  have hfun : (fun α : ℝ => portImbalance E (α + γ * I)) = fun α : ℝ =>
      ‖E (α + γ * I)‖ ^ 2 - ‖thetaSymmetrizedPort (α + γ * I) - E (α + γ * I)‖ ^ 2 := by
    funext α
    rw [portImbalance, show halfPortReflect E (α + γ * I) =
      thetaSymmetrizedPort (α + γ * I) - E (α + γ * I) by rw [← hsym]; ring]
  rw [hfun]
  refine ((hline0 hE).norm_sq.sub (hline0 hEX).norm_sq).congr_deriv ?_
  simp only [Complex.ofReal_zero, zero_add, hX, zero_sub, inner_neg_left, inner_sub_right]
  ring

/-! ## The Euler multiplier of one prime -/

/-- The symmetric one-prime multiplier `A_p(w) = 1 - p^{-1/2} cosh(w log p)`. -/
def primeDeletionSymbol (p : ℝ) (w : ℂ) : ℂ :=
  1 - ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.cosh (Real.log p * w)

/-- Its derivative `A_p'(w) = -p^{-1/2} log p · sinh(w log p)`. -/
def primeDeletionSymbolDeriv (p : ℝ) (w : ℂ) : ℂ :=
  -(((p ^ (-(1 / 2 : ℝ)) * Real.log p : ℝ) : ℂ) * Complex.sinh (Real.log p * w))

theorem hasDerivAt_primeDeletionSymbol (p : ℝ) (w : ℂ) : HasDerivAt (primeDeletionSymbol p) (primeDeletionSymbolDeriv p w) w := by
  have h := (((hasDerivAt_id w).const_mul (Real.log p : ℂ)).ccosh).const_mul
    (((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
  refine (h.const_sub 1).congr_deriv ?_
  simp only [primeDeletionSymbolDeriv, id]; push_cast; ring

theorem hasDerivAt_primeDeletionSymbolDeriv (p : ℝ) (w : ℂ) :
    HasDerivAt (primeDeletionSymbolDeriv p)
      (-(((p ^ (-(1 / 2 : ℝ)) * Real.log p ^ 2 : ℝ) : ℂ) * Complex.cosh (Real.log p * w))) w := by
  have h := ((((hasDerivAt_id w).const_mul (Real.log p : ℂ)).csinh).const_mul
    (((p ^ (-(1 / 2 : ℝ)) * Real.log p : ℝ) : ℂ))).neg
  refine h.congr_deriv ?_
  simp only [id]; push_cast; ring

theorem halfPortReflect_primeDeletionSymbol (p : ℝ) (w : ℂ) : halfPortReflect (primeDeletionSymbol p) w = primeDeletionSymbol p w := by
  simp only [halfPortReflect, primeDeletionSymbol, map_sub, map_one, map_mul, Complex.conj_ofReal,
    ← Complex.cosh_conj, Complex.conj_conj, mul_neg, Complex.cosh_neg]

theorem halfPortReflect_primeDeletionSymbolDeriv (p : ℝ) (w : ℂ) :
    halfPortReflect (primeDeletionSymbolDeriv p) w = -primeDeletionSymbolDeriv p w := by
  simp only [halfPortReflect, primeDeletionSymbolDeriv, map_mul, Complex.conj_ofReal,
    ← Complex.sinh_conj, Complex.conj_conj, mul_neg, Complex.sinh_neg, neg_neg]

theorem primeDeletionSymbol_mul_I (p γ : ℝ) :
    primeDeletionSymbol p (γ * I) = ((1 - p ^ (-(1 / 2 : ℝ)) * Real.cos (Real.log p * γ) : ℝ) : ℂ) := by
  rw [primeDeletionSymbol, show (Real.log p : ℂ) * (γ * I) = ((Real.log p * γ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.cosh_mul_I, ← Complex.ofReal_cos]
  push_cast; ring

theorem primeDeletionSymbolDeriv_mul_I (p γ : ℝ) :
    primeDeletionSymbolDeriv p (γ * I) =
      -(((p ^ (-(1 / 2 : ℝ)) * Real.log p * Real.sin (Real.log p * γ) : ℝ) : ℂ) * I) := by
  rw [primeDeletionSymbolDeriv, show (Real.log p : ℂ) * (γ * I) = ((Real.log p * γ : ℝ) : ℂ) * I by
    push_cast; ring, Complex.sinh_mul_I, ← Complex.ofReal_sin]
  push_cast; ring

/-- **The exact wall symbol (20).** `A_p(1/2 + iβ) = 1 - [p^{iβ} + p^{-1} p^{-iβ}]/2`. -/
theorem primeDeletionSymbol_wall {p : ℝ} (hp : 0 < p) (β : ℝ) :
    primeDeletionSymbol p (1 / 2 + β * I) =
      1 - (cexp (Real.log p * β * I) + p⁻¹ * cexp (-(Real.log p * β * I))) / 2 := by
  have hr : p ^ (-(1 / 2 : ℝ)) = Real.exp (-(Real.log p / 2)) := by
    rw [Real.rpow_def_of_pos hp]; ring_nf
  have hr1 : ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (Real.log p * (1 / 2 : ℂ)) = 1 := by
    rw [show (Real.log p : ℂ) * (1 / 2 : ℂ) = ((Real.log p / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, hr, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, Complex.ofReal_one]
  have hr2 : ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(Real.log p * (1 / 2 : ℂ))) = (p⁻¹ : ℝ) := by
    rw [show -((Real.log p : ℂ) * (1 / 2 : ℂ)) = ((-(Real.log p / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, hr, ← Real.exp_add,
      show -(Real.log p / 2) + -(Real.log p / 2) = -Real.log p by ring, Real.exp_neg,
      Real.exp_log hp]
  rw [primeDeletionSymbol, Complex.cosh, show (Real.log p : ℂ) * (1 / 2 + β * I) =
    Real.log p * (1 / 2 : ℂ) + Real.log p * β * I by ring, Complex.exp_add, neg_add,
    Complex.exp_add]
  linear_combination (-(cexp (Real.log p * β * I)) / 2) * hr1 +
    (-(cexp (-(Real.log p * β * I))) / 2) * hr2

theorem primeDeletionSymbol_ofReal (p α : ℝ) :
    primeDeletionSymbol p α = ((1 - p ^ (-(1 / 2 : ℝ)) * Real.cosh (Real.log p * α) : ℝ) : ℂ) := by
  rw [primeDeletionSymbol, show (Real.log p : ℂ) * α = ((Real.log p * α : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cosh]
  push_cast; ring

theorem primeDeletionSymbolDeriv_ofReal (p α : ℝ) :
    primeDeletionSymbolDeriv p α =
      ((-(p ^ (-(1 / 2 : ℝ)) * Real.log p * Real.sinh (Real.log p * α)) : ℝ) : ℂ) := by
  rw [primeDeletionSymbolDeriv, show (Real.log p : ℂ) * α = ((Real.log p * α : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sinh]
  push_cast; ring

theorem norm_sinh_le_cosh_re (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  have hz : z = (z.re : ℂ) + z.im * I := (Complex.re_add_im z).symm
  have hsq : ‖Complex.sinh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.sin z.im ^ 2 := by
    rw [hz, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im, Complex.re_add_im]
    have h1 := Real.cosh_sq_sub_sinh_sq z.re
    nlinarith [Real.sin_sq_add_cos_sq z.im]
  have hc : 0 < Real.cosh z.re := Real.cosh_pos _
  have h1 := Real.cosh_sq_sub_sinh_sq z.re
  have h2 := Real.sin_sq_le_one z.im
  nlinarith [norm_nonneg (Complex.sinh z)]

/-- `|1 - A_p(α + iβ)| ≤ p^{-1/2} cosh(α log p)`. -/
theorem norm_one_sub_primeDeletionSymbol_le {p : ℝ} (hp : 0 ≤ p) (w : ℂ) :
    ‖1 - primeDeletionSymbol p w‖ ≤ p ^ (-(1 / 2 : ℝ)) * Real.cosh (Real.log p * w.re) := by
  rw [primeDeletionSymbol, sub_sub_cancel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hp _)]
  refine mul_le_mul_of_nonneg_left ((norm_cosh_le_cosh_re _).trans (le_of_eq ?_))
    (Real.rpow_nonneg hp _)
  simp

/-- `r cosh(α log p) ≤ (1 + p⁻¹)/2 < 1` on `|α| ≤ 1/2`, `p > 1`. -/
theorem rpow_mul_cosh_le {p : ℝ} (hp : 1 < p) {α : ℝ} (hα : |α| ≤ 1 / 2) :
    p ^ (-(1 / 2 : ℝ)) * Real.cosh (Real.log p * α) ≤ (1 + p⁻¹) / 2 := by
  have hp0 : 0 < p := by linarith
  have hL : 0 < Real.log p := Real.log_pos hp
  have hmono : Real.cosh (Real.log p * α) ≤ Real.cosh (Real.log p / 2) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : 0 < Real.log p / 2)]
    nlinarith
  have hval : p ^ (-(1 / 2 : ℝ)) * Real.cosh (Real.log p / 2) = (1 + p⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.rpow_def_of_pos hp0, show Real.log p * -(1 / 2) = -(Real.log p / 2) by ring]
    rw [mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add,
      show -(Real.log p / 2) + Real.log p / 2 = 0 by ring,
      show -(Real.log p / 2) + -(Real.log p / 2) = -Real.log p by ring, Real.exp_zero,
      Real.exp_neg, Real.exp_log hp0]
  calc p ^ (-(1 / 2 : ℝ)) * Real.cosh (Real.log p * α)
      ≤ p ^ (-(1 / 2 : ℝ)) * Real.cosh (Real.log p / 2) :=
        mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hp0.le _)
    _ = (1 + p⁻¹) / 2 := hval

theorem one_add_inv_div_two_lt_one {p : ℝ} (hp : 1 < p) : (1 + p⁻¹) / 2 < 1 := by
  have : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  linarith

/-! ## The gauge family of prime-moment ports -/

/-- The prime-moment port with real clock gauge `μ`:
`E_{p,μ} = X/2 + A_p X' + μ A_p' X / log p`. `μ = 0` is deletion-after-clock (13) and
`μ = log p` is clock-after-deletion `X/2 + (A_p X)'` (9). -/
def primeGaugePort (p μ : ℝ) (w : ℂ) : ℂ :=
  thetaSymmetrizedPort w / 2 + primeDeletionSymbol p w * deriv thetaSymmetrizedPort w +
    ((μ / Real.log p : ℝ) : ℂ) * primeDeletionSymbolDeriv p w * thetaSymmetrizedPort w

/-- The deletion-after-clock port `E_p^cov = X/2 + A_p X'` (13). -/
def primeCovariantPort (p : ℝ) : ℂ → ℂ := primeGaugePort p 0

/-- The clock-after-deletion port `E_p = X/2 + (A_p X)'` (9). -/
def primeMomentPort (p : ℝ) : ℂ → ℂ := primeGaugePort p (Real.log p)

theorem primeMomentPort_eq {p : ℝ} (hp : 1 < p) (w : ℂ) :
    primeMomentPort p w = thetaSymmetrizedPort w / 2 +
      deriv (fun z => primeDeletionSymbol p z * thetaSymmetrizedPort z) w := by
  have hL : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  have h := (hasDerivAt_primeDeletionSymbol p w).mul (hasDerivAt_thetaSymmetrizedPort w)
  rw [show (fun z => primeDeletionSymbol p z * thetaSymmetrizedPort z) = primeDeletionSymbol p * thetaSymmetrizedPort
    from rfl, h.deriv, primeMomentPort, primeGaugePort, div_self hL]
  push_cast; ring

theorem halfPortReflect_primeGaugePort (p μ : ℝ) (w : ℂ) :
    halfPortReflect (primeGaugePort p μ) w = thetaSymmetrizedPort w / 2 -
      primeDeletionSymbol p w * deriv thetaSymmetrizedPort w -
        ((μ / Real.log p : ℝ) : ℂ) * primeDeletionSymbolDeriv p w * thetaSymmetrizedPort w := by
  have h1 := halfPortReflect_thetaSymmetrizedPort w
  have h2 := halfPortReflect_deriv_thetaSymmetrizedPort w
  have h3 := halfPortReflect_primeDeletionSymbol p w
  have h4 := halfPortReflect_primeDeletionSymbolDeriv p w
  simp only [halfPortReflect, primeGaugePort] at h1 h2 h3 h4 ⊢
  rw [map_add, map_add, map_div₀, map_mul, map_mul, map_mul, h1, h2, h3, h4, Complex.conj_ofReal,
    map_ofNat]
  ring

/-- **The gauge ports are anti-reflected channels:** `E_{p,μ} + E_{p,μ}# = X`. -/
theorem primeGaugePort_add_reflect (p μ : ℝ) (w : ℂ) :
    primeGaugePort p μ w + halfPortReflect (primeGaugePort p μ) w = thetaSymmetrizedPort w := by
  rw [halfPortReflect_primeGaugePort, primeGaugePort]; ring

theorem hasDerivAt_primeGaugePort (p μ : ℝ) (w : ℂ) :
    HasDerivAt (primeGaugePort p μ) (deriv (primeGaugePort p μ) w) w := by
  have hX := differentiable_thetaSymmetrizedPort
  have hX' := differentiable_deriv_thetaSymmetrizedPort
  have hA : Differentiable ℂ (primeDeletionSymbol p) := fun z => (hasDerivAt_primeDeletionSymbol p z).differentiableAt
  have hA' : Differentiable ℂ (primeDeletionSymbolDeriv p) :=
    fun z => (hasDerivAt_primeDeletionSymbolDeriv p z).differentiableAt
  have hd : Differentiable ℂ (primeGaugePort p μ) := by
    unfold primeGaugePort
    exact ((hX.div_const 2).add (hA.mul hX')).add (((differentiable_const _).mul hA').mul hX)
  exact (hd w).hasDerivAt

/-- At a real Xi zero, `E_{p,μ}(iγ) = -i[1 - p^{-1/2} cos(γ log p)] Ξ'(γ)`, for every gauge. -/
theorem primeGaugePort_mul_I {p μ γ : ℝ} (hγ : Xi γ = 0) :
    primeGaugePort p μ (γ * I) =
      -I * ((1 - p ^ (-(1 / 2 : ℝ)) * Real.cos (Real.log p * γ) : ℝ) : ℂ) * deriv Xi γ := by
  rw [primeGaugePort, thetaSymmetrizedPort_mul_I, hγ, deriv_thetaSymmetrizedPort_mul_I,
    primeDeletionSymbol_mul_I]
  push_cast; ring

/-- **Local orientation (10).** At every real Xi zero, for every real gauge,
`∂_α D(α + iγ)|₀ = 2[1 - p^{-1/2} cos(γ log p)] Ξ'(γ)²`. -/
theorem hasDerivAt_primeGaugePort_imbalance {p μ γ : ℝ} (hγ : Xi γ = 0) :
    HasDerivAt (fun α : ℝ => portImbalance (primeGaugePort p μ) (α + γ * I))
      (2 * (1 - p ^ (-(1 / 2 : ℝ)) * Real.cos (Real.log p * γ)) * deriv Xi γ ^ 2) 0 := by
  have hX : thetaSymmetrizedPort (γ * I) = 0 := by
    rw [thetaSymmetrizedPort_mul_I, hγ, Complex.ofReal_zero]
  refine (hasDerivAt_portImbalance_of_zero (hasDerivAt_primeGaugePort p μ (γ * I))
    (primeGaugePort_add_reflect p μ) hX).congr_deriv ?_
  rw [primeGaugePort_mul_I hγ, deriv_thetaSymmetrizedPort_mul_I, Complex.inner]
  simp [Complex.mul_re, Complex.mul_im]
  rw [← Complex.ofReal_mul, Complex.cos_ofReal_re]
  ring

theorem one_sub_rpow_mul_cos_pos {p : ℝ} (hp : 1 < p) (t : ℝ) :
    0 < 1 - p ^ (-(1 / 2 : ℝ)) * Real.cos t := by
  have hr : p ^ (-(1 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  have hr0 : 0 ≤ p ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith [Real.cos_le_one t, Real.neg_one_le_cos t]

/-- The normal derivative (10) is strictly positive at every simple critical zero. -/
theorem primeGaugePort_normal_pos {p : ℝ} (hp : 1 < p) {γ : ℝ} (hd : deriv Xi γ ≠ 0) :
    0 < 2 * (1 - p ^ (-(1 / 2 : ℝ)) * Real.cos (Real.log p * γ)) * deriv Xi γ ^ 2 := by
  have := one_sub_rpow_mul_cos_pos hp (Real.log p * γ)
  positivity

/-- **(15) for the gauge ports.** Away from zeros of `X`,
`D = 2|X|² Re[A_p z + (μ/log p) A_p']`, `z = X'/X`. -/
theorem primeGaugePort_imbalance_eq {p μ : ℝ} {w : ℂ} (hX : thetaSymmetrizedPort w ≠ 0) :
    portImbalance (primeGaugePort p μ) w = 2 * ‖thetaSymmetrizedPort w‖ ^ 2 *
      (primeDeletionSymbol p w * (deriv thetaSymmetrizedPort w / thetaSymmetrizedPort w) +
        ((μ / Real.log p : ℝ) : ℂ) * primeDeletionSymbolDeriv p w).re := by
  rw [portImbalance_eq_re_div (primeGaugePort_add_reflect p μ) hX]
  congr 3
  rw [primeGaugePort]
  field_simp
  ring

/-- **The phase-aperture criterion (16).** If `Re(X'/X) > p^{-1/2} cosh(Re w log p)|X'/X|` then
the deletion-after-clock port has strict modulus order at `w`. -/
theorem primeCovariantPort_imbalance_pos {p : ℝ} (hp : 0 ≤ p) {w : ℂ}
    (hX : thetaSymmetrizedPort w ≠ 0)
    (hap : p ^ (-(1 / 2 : ℝ)) * Real.cosh (Real.log p * w.re) *
      ‖deriv thetaSymmetrizedPort w / thetaSymmetrizedPort w‖ <
        (deriv thetaSymmetrizedPort w / thetaSymmetrizedPort w).re) :
    0 < portImbalance (primeCovariantPort p) w := by
  rw [primeCovariantPort, primeGaugePort_imbalance_eq hX]
  set z := deriv thetaSymmetrizedPort w / thetaSymmetrizedPort w
  have hA : (primeDeletionSymbol p w * z).re ≥ z.re - ‖1 - primeDeletionSymbol p w‖ * ‖z‖ := by
    have h : primeDeletionSymbol p w * z = z - (1 - primeDeletionSymbol p w) * z := by ring
    rw [h, Complex.sub_re]
    have := Complex.re_le_norm ((1 - primeDeletionSymbol p w) * z)
    rw [norm_mul] at this
    linarith
  have hb := norm_one_sub_primeDeletionSymbol_le hp w
  have hpos : 0 < (primeDeletionSymbol p w * z).re := by
    nlinarith [norm_nonneg z]
  have hXn : 0 < ‖thetaSymmetrizedPort w‖ ^ 2 := by positivity
  simp only [zero_div, Complex.ofReal_zero, zero_mul, add_zero]
  positivity

/-- On the whole closed physical strip the multiplier stays in the right half-plane:
`|1 - A_p(α + iβ)| ≤ (1 + p⁻¹)/2 < 1` for `|α| ≤ 1/2`. -/
theorem norm_one_sub_primeDeletionSymbol_lt_one {p : ℝ} (hp : 1 < p) {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    ‖1 - primeDeletionSymbol p w‖ ≤ (1 + p⁻¹) / 2 ∧ (1 + p⁻¹) / 2 < 1 :=
  ⟨(norm_one_sub_primeDeletionSymbol_le (by linarith) w).trans (rpow_mul_cosh_le hp hw),
    one_add_inv_div_two_lt_one hp⟩

/-! ## The critical-boundary normal derivative (17) -/

theorem hasDerivAt_deriv_thetaSymmetrizedPort (w : ℂ) :
    HasDerivAt (deriv thetaSymmetrizedPort) (deriv (deriv thetaSymmetrizedPort) w) w :=
  (differentiable_deriv_thetaSymmetrizedPort w).hasDerivAt

/-- `Ξ'` is differentiable with `Ξ''(γ) = -X''(iγ)`, and `X''(iγ)` is real. -/
theorem hasDerivAt_deriv_Xi (γ : ℝ) :
    HasDerivAt (deriv Xi) (-(deriv (deriv thetaSymmetrizedPort) (γ * I))).re γ ∧
      (deriv (deriv thetaSymmetrizedPort) (γ * I)).im = 0 := by
  have h1 : ∀ t : ℝ, ((deriv Xi t : ℝ) : ℂ) = I * deriv thetaSymmetrizedPort (t * I) := fun t => by
    rw [deriv_thetaSymmetrizedPort_mul_I]; ring_nf; rw [Complex.I_sq]; ring
  have hC : HasDerivAt (fun t : ℝ => I * deriv thetaSymmetrizedPort (t * I))
      (I * (deriv (deriv thetaSymmetrizedPort) (γ * I) * I)) γ := by
    have h := ((hasDerivAt_deriv_thetaSymmetrizedPort ((γ : ℂ) * I)).comp (γ : ℂ)
      ((hasDerivAt_id (γ : ℂ)).mul_const I)).comp_ofReal
    simpa using h.const_mul I
  have hC' : HasDerivAt (fun t : ℝ => ((deriv Xi t : ℝ) : ℂ))
      (-(deriv (deriv thetaSymmetrizedPort) (γ * I))) γ := by
    rw [funext h1]
    refine hC.congr_deriv ?_
    ring_nf; rw [Complex.I_sq]; ring
  have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt γ hC')
  have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt γ hC')
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  refine ⟨hre, ?_⟩
  have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 γ := hasDerivAt_const _ _
  have := him.unique h0
  simpa using this

theorem deriv_deriv_thetaSymmetrizedPort_mul_I (γ : ℝ) :
    deriv (deriv thetaSymmetrizedPort) (γ * I) = -((deriv (deriv Xi) γ : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := hasDerivAt_deriv_Xi γ
  rw [h1.deriv]
  apply Complex.ext <;> simp [h2]

/-- **The critical-boundary normal derivative (17)** of the deletion-after-clock port:
`½ ∂_α D(α + iγ)|₀ = [1 - r cos(γL)](x'² - x x'') - rL sin(γL) x x'`, `x = Ξ|ℝ`. -/
theorem hasDerivAt_primeCovariantPort_imbalance (p γ : ℝ) :
    HasDerivAt (fun α : ℝ => portImbalance (primeCovariantPort p) (α + γ * I))
      (2 * ((1 - p ^ (-(1 / 2 : ℝ)) * Real.cos (Real.log p * γ)) *
          (deriv Xi γ ^ 2 - Xi γ * deriv (deriv Xi) γ) -
        p ^ (-(1 / 2 : ℝ)) * Real.log p * Real.sin (Real.log p * γ) * Xi γ * deriv Xi γ)) 0 := by
  have hE : HasDerivAt (primeCovariantPort p)
      (deriv thetaSymmetrizedPort (γ * I) / 2 +
        (primeDeletionSymbolDeriv p (γ * I) * deriv thetaSymmetrizedPort (γ * I) +
          primeDeletionSymbol p (γ * I) * deriv (deriv thetaSymmetrizedPort) (γ * I))) (γ * I) := by
    have h := ((hasDerivAt_thetaSymmetrizedPort ((γ : ℂ) * I)).div_const 2).add
      ((hasDerivAt_primeDeletionSymbol p ((γ : ℂ) * I)).mul (hasDerivAt_deriv_thetaSymmetrizedPort _))
    have e : primeCovariantPort p =
        (fun w => thetaSymmetrizedPort w / 2) + primeDeletionSymbol p * deriv thetaSymmetrizedPort := by
      funext w; simp [primeCovariantPort, primeGaugePort]
    rw [e]; exact h
  refine (hasDerivAt_portImbalance hE).congr_deriv ?_
  simp only [primeCovariantPort, primeGaugePort, Complex.ofReal_zero, zero_div, zero_mul, add_zero]
  rw [thetaSymmetrizedPort_mul_I, deriv_thetaSymmetrizedPort_mul_I,
    deriv_deriv_thetaSymmetrizedPort_mul_I, primeDeletionSymbol_mul_I, primeDeletionSymbolDeriv_mul_I, Complex.inner]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-! ## The symmetrized port on the real axis -/

/-- The moment transforms `T_j(β) = ∫₀^∞ e^{βu} u^j k(u) du`. -/
def thetaMomentTransform (j : ℕ) (β : ℂ) : ℂ :=
  halfLineExpTransform (fun u => (u : ℂ) ^ j * (thetaCuspFullSource u : ℂ)) β

theorem integrableOn_exp_mul_norm_pow_mul_thetaCuspFullSource (j : ℕ) (σ : ℝ) :
    IntegrableOn (fun u => Real.exp (σ * u) * ‖(u : ℂ) ^ j * (thetaCuspFullSource u : ℂ)‖) (Ioi 0) := by
  obtain ⟨C, hC, h⟩ := exists_abs_thetaCuspFullSource_le (|σ| + j + 2)
  refine ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul (j.factorial * C)).mono'
    ((by have := continuous_thetaCuspFullSource; fun_prop : Continuous fun u : ℝ =>
      Real.exp (σ * u) * ‖(u : ℂ) ^ j * (thetaCuspFullSource u : ℂ)‖).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_))
  have hu : (0 : ℝ) ≤ u := le_of_lt hu
  have hb := h u
  rw [abs_of_nonneg hu] at hb
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_norm, norm_mul, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu]
  have hpow : u ^ j ≤ j.factorial * Real.exp u := by
    have := Real.pow_div_factorial_le_exp u hu j
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have hσ : Real.exp (σ * u) ≤ Real.exp (|σ| * u) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self σ) hu)
  calc Real.exp (σ * u) * (u ^ j * |thetaCuspFullSource u|)
      ≤ Real.exp (|σ| * u) * ((j.factorial * Real.exp u) *
          (C * Real.exp (-((|σ| + j + 2) * u)))) := by gcongr
    _ = j.factorial * C * (Real.exp (|σ| * u) * Real.exp u * Real.exp (-((|σ| + j + 2) * u))) := by
        ring
    _ ≤ j.factorial * C * Real.exp (-1 * u) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have : (0 : ℝ) ≤ j * u := by positivity
        nlinarith

theorem hasDerivAt_thetaMomentTransform (j : ℕ) (β : ℂ) :
    HasDerivAt (thetaMomentTransform j) (thetaMomentTransform (j + 1) β) β := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ j * (thetaCuspFullSource u : ℂ))
      (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous fun u : ℝ => (u : ℂ) ^ j).mul
      (Complex.continuous_ofReal.comp continuous_thetaCuspFullSource)).aestronglyMeasurable
  have h := hasDerivAt_halfLineExpTransform hmeas
    (integrableOn_exp_mul_norm_pow_mul_thetaCuspFullSource j (β.re + 1)) (w := β) (by linarith)
  unfold thetaMomentTransform
  convert h using 2
  funext u; ring

theorem thetaMomentTransform_ofReal (j : ℕ) (β : ℝ) :
    thetaMomentTransform j β =
      ((∫ u in Ioi (0 : ℝ), Real.exp (β * u) * (u ^ j * thetaCuspFullSource u) : ℝ) : ℂ) := by
  rw [thetaMomentTransform, halfLineExpTransform, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  push_cast; ring_nf

theorem thetaMomentTransform_zero : thetaMomentTransform 0 = thetaHalfLaplace := by
  funext β; simp [thetaMomentTransform, halfLineExpTransform, thetaHalfLaplace, thetaHalfLaplaceTail]

theorem deriv_thetaSymmetrizedPort_eq_moment (w : ℂ) :
    deriv thetaSymmetrizedPort w = thetaMomentTransform 1 w - thetaMomentTransform 1 (-w) := by
  have h := (hasDerivAt_thetaMomentTransform 0 w).add
    ((hasDerivAt_thetaMomentTransform 0 (-w)).comp w (hasDerivAt_neg w))
  have e : thetaSymmetrizedPort = thetaMomentTransform 0 + thetaMomentTransform 0 ∘ Neg.neg := by
    funext z; simp [thetaSymmetrizedPort, thetaMomentTransform_zero]
  rw [e, h.deriv]; ring

theorem hasDerivAt_deriv_thetaSymmetrizedPort_eq (w : ℂ) :
    deriv (deriv thetaSymmetrizedPort) w = thetaMomentTransform 2 w + thetaMomentTransform 2 (-w) := by
  have h := (hasDerivAt_thetaMomentTransform 1 w).sub
    ((hasDerivAt_thetaMomentTransform 1 (-w)).comp w (hasDerivAt_neg w))
  have e : deriv thetaSymmetrizedPort = thetaMomentTransform 1 - thetaMomentTransform 1 ∘ Neg.neg := by
    funext z; simp [deriv_thetaSymmetrizedPort_eq_moment]
  rw [e, h.deriv]; ring

/-- `X(α)` on the real axis. -/
def thetaPortReal (α : ℝ) : ℝ :=
  (∫ u in Ioi (0 : ℝ), Real.exp (α * u) * (u ^ 0 * thetaCuspFullSource u)) +
    ∫ u in Ioi (0 : ℝ), Real.exp (-α * u) * (u ^ 0 * thetaCuspFullSource u)

/-- `X'(α)` on the real axis. -/
def thetaPortRealDeriv (α : ℝ) : ℝ :=
  (∫ u in Ioi (0 : ℝ), Real.exp (α * u) * (u ^ 1 * thetaCuspFullSource u)) -
    ∫ u in Ioi (0 : ℝ), Real.exp (-α * u) * (u ^ 1 * thetaCuspFullSource u)

/-- `X''(α)` on the real axis. -/
def thetaPortRealDeriv2 (α : ℝ) : ℝ :=
  (∫ u in Ioi (0 : ℝ), Real.exp (α * u) * (u ^ 2 * thetaCuspFullSource u)) +
    ∫ u in Ioi (0 : ℝ), Real.exp (-α * u) * (u ^ 2 * thetaCuspFullSource u)

theorem thetaSymmetrizedPort_ofReal (α : ℝ) : thetaSymmetrizedPort α = (thetaPortReal α : ℂ) := by
  rw [thetaSymmetrizedPort, ← thetaMomentTransform_zero, show -(α : ℂ) = ((-α : ℝ) : ℂ) by push_cast; ring,
    thetaMomentTransform_ofReal, thetaMomentTransform_ofReal, thetaPortReal]
  push_cast; ring_nf

theorem deriv_thetaSymmetrizedPort_ofReal (α : ℝ) :
    deriv thetaSymmetrizedPort α = (thetaPortRealDeriv α : ℂ) := by
  rw [deriv_thetaSymmetrizedPort_eq_moment, show -(α : ℂ) = ((-α : ℝ) : ℂ) by push_cast; ring,
    thetaMomentTransform_ofReal, thetaMomentTransform_ofReal, thetaPortRealDeriv]
  push_cast; ring_nf

theorem deriv_deriv_thetaSymmetrizedPort_ofReal (α : ℝ) :
    deriv (deriv thetaSymmetrizedPort) α = (thetaPortRealDeriv2 α : ℂ) := by
  rw [hasDerivAt_deriv_thetaSymmetrizedPort_eq, show -(α : ℂ) = ((-α : ℝ) : ℂ) by push_cast; ring,
    thetaMomentTransform_ofReal, thetaMomentTransform_ofReal, thetaPortRealDeriv2]
  push_cast; ring_nf

theorem hasDerivAt_thetaPortReal (α : ℝ) : HasDerivAt thetaPortReal (thetaPortRealDeriv α) α := by
  have h := (hasDerivAt_thetaSymmetrizedPort (α : ℂ)).real_of_complex
  rw [deriv_thetaSymmetrizedPort_ofReal, Complex.ofReal_re] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  simp [thetaSymmetrizedPort_ofReal]

theorem hasDerivAt_thetaPortRealDeriv (α : ℝ) :
    HasDerivAt thetaPortRealDeriv (thetaPortRealDeriv2 α) α := by
  have h := (hasDerivAt_deriv_thetaSymmetrizedPort (α : ℂ)).real_of_complex
  rw [deriv_deriv_thetaSymmetrizedPort_ofReal, Complex.ofReal_re] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  simp [deriv_thetaSymmetrizedPort_ofReal]

theorem integrableOn_exp_mul_pow_mul_thetaCuspFullSource (j : ℕ) (σ : ℝ) :
    IntegrableOn (fun u => Real.exp (σ * u) * (u ^ j * thetaCuspFullSource u)) (Ioi 0) := by
  refine (integrableOn_exp_mul_norm_pow_mul_thetaCuspFullSource j σ).mono'
    ((by have := continuous_thetaCuspFullSource; fun_prop : Continuous fun u : ℝ =>
      Real.exp (σ * u) * (u ^ j * thetaCuspFullSource u)).aestronglyMeasurable)
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), norm_mul, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow]

theorem thetaPortReal_pos (α : ℝ) : 0 < thetaPortReal α := by
  have h : ∀ σ : ℝ, 0 < ∫ u in Ioi (0 : ℝ), Real.exp (σ * u) * (u ^ 0 * thetaCuspFullSource u) :=
    fun σ => setIntegral_Ioi_pos (integrableOn_exp_mul_pow_mul_thetaCuspFullSource 0 σ)
      fun u _ => by have := thetaCuspFullSource_pos u; positivity
  exact add_pos (h α) (h (-α))

theorem thetaPortRealDeriv_pos {α : ℝ} (hα : 0 < α) : 0 < thetaPortRealDeriv α := by
  rw [thetaPortRealDeriv, ← integral_sub (integrableOn_exp_mul_pow_mul_thetaCuspFullSource 1 α)
    (integrableOn_exp_mul_pow_mul_thetaCuspFullSource 1 (-α))]
  refine setIntegral_Ioi_pos ((integrableOn_exp_mul_pow_mul_thetaCuspFullSource 1 α).sub
    (integrableOn_exp_mul_pow_mul_thetaCuspFullSource 1 (-α))) fun u hu => ?_
  have hk := thetaCuspFullSource_pos u
  have hu' : (0 : ℝ) < u := hu
  have he : Real.exp (-α * u) < Real.exp (α * u) := Real.exp_lt_exp.mpr (by nlinarith)
  rw [← sub_mul]
  exact mul_pos (by linarith) (by positivity)

theorem thetaPortRealDeriv_zero : thetaPortRealDeriv 0 = 0 := by
  simp [thetaPortRealDeriv]

theorem thetaPortRealDeriv2_pos (α : ℝ) : 0 < thetaPortRealDeriv2 α := by
  have h : ∀ σ : ℝ, 0 < ∫ u in Ioi (0 : ℝ), Real.exp (σ * u) * (u ^ 2 * thetaCuspFullSource u) :=
    fun σ => setIntegral_Ioi_pos (integrableOn_exp_mul_pow_mul_thetaCuspFullSource 2 σ)
      fun u hu => by have := thetaCuspFullSource_pos u; have : (0 : ℝ) < u := hu; positivity
  exact add_pos (h α) (h (-α))

/-! ## The gauge ports on the positive real radius -/

/-- The real multiplier `A_p(α) = 1 - p^{-1/2} cosh(α log p)`. -/
def primeDeletionSymbolReal (p α : ℝ) : ℝ := 1 - p ^ (-(1 / 2 : ℝ)) * Real.cosh (Real.log p * α)

/-- Its derivative `A_p'(α) = -p^{-1/2} log p sinh(α log p)`. -/
def primeDeletionSymbolRealDeriv (p α : ℝ) : ℝ := -(p ^ (-(1 / 2 : ℝ)) * Real.log p * Real.sinh (Real.log p * α))

theorem hasDerivAt_primeDeletionSymbolReal (p α : ℝ) :
    HasDerivAt (primeDeletionSymbolReal p) (primeDeletionSymbolRealDeriv p α) α := by
  have h := ((((hasDerivAt_id α).const_mul (Real.log p)).cosh).const_mul
    (p ^ (-(1 / 2 : ℝ)))).const_sub 1
  refine h.congr_deriv ?_
  simp only [primeDeletionSymbolRealDeriv, id]; ring

theorem hasDerivAt_primeDeletionSymbolRealDeriv (p α : ℝ) :
    HasDerivAt (primeDeletionSymbolRealDeriv p)
      (-(p ^ (-(1 / 2 : ℝ)) * Real.log p ^ 2 * Real.cosh (Real.log p * α))) α := by
  have h := ((((hasDerivAt_id α).const_mul (Real.log p)).sinh).const_mul
    (p ^ (-(1 / 2 : ℝ)) * Real.log p)).neg
  refine h.congr_deriv ?_
  simp only [id]; ring

/-- On the real axis `D_{p,μ}(α) = 2X(α)[A_p(α)X'(α) + (μ/log p)A_p'(α)X(α)]`. -/
theorem primeGaugePort_imbalance_ofReal (p μ α : ℝ) :
    portImbalance (primeGaugePort p μ) α = 2 * thetaPortReal α *
      (primeDeletionSymbolReal p α * thetaPortRealDeriv α +
        μ / Real.log p * primeDeletionSymbolRealDeriv p α * thetaPortReal α) := by
  rw [portImbalance_eq_of_add_reflect (primeGaugePort_add_reflect p μ), primeGaugePort,
    thetaSymmetrizedPort_ofReal, deriv_thetaSymmetrizedPort_ofReal, primeDeletionSymbol_ofReal,
    primeDeletionSymbolDeriv_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im]
  simp only [primeDeletionSymbolReal, primeDeletionSymbolRealDeriv]
  ring

/-- **The whole right half-plane fails.** For every `p > 1` the clock-after-deletion port has
`D_p(α) < 0` for all sufficiently large real `α`. -/
theorem eventually_primeMomentPort_imbalance_neg {p : ℝ} (hp : 1 < p) :
    ∀ᶠ α : ℝ in atTop, portImbalance (primeMomentPort p) (α : ℂ) < 0 := by
  have hL : 0 < Real.log p := Real.log_pos hp
  have hr : 0 < p ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have htend : Tendsto (fun α : ℝ => p ^ (-(1 / 2 : ℝ)) * (Real.exp (Real.log p * α) / 2)) atTop
      atTop :=
    ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hL)).atTop_div_const two_pos).const_mul_atTop hr
  filter_upwards [htend.eventually_gt_atTop 1, eventually_gt_atTop 0] with α hα hα0
  rw [primeMomentPort, primeGaugePort_imbalance_ofReal, div_self hL.ne', one_mul]
  have hcosh : Real.exp (Real.log p * α) / 2 ≤ Real.cosh (Real.log p * α) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.log p * α))]
  have hA : primeDeletionSymbolReal p α < 0 := by
    simp only [primeDeletionSymbolReal]; nlinarith
  have hA' : primeDeletionSymbolRealDeriv p α < 0 := by
    simp only [primeDeletionSymbolRealDeriv]
    have := Real.sinh_pos_iff.mpr (mul_pos hL hα0)
    have : 0 < p ^ (-(1 / 2 : ℝ)) * Real.log p * Real.sinh (Real.log p * α) := by positivity
    linarith
  have hX := thetaPortReal_pos α
  have hX1 := thetaPortRealDeriv_pos hα0
  have : primeDeletionSymbolReal p α * thetaPortRealDeriv α + primeDeletionSymbolRealDeriv p α * thetaPortReal α < 0 := by
    nlinarith
  nlinarith

/-- `Y_p'(α) = A_p(α)X'(α) + A_p'(α)X(α)`, the real-axis clock-after-deletion moment. -/
def primeMomentReal (p α : ℝ) : ℝ :=
  primeDeletionSymbolReal p α * thetaPortRealDeriv α + primeDeletionSymbolRealDeriv p α * thetaPortReal α

theorem primeMomentPort_imbalance_ofReal {p : ℝ} (hp : 1 < p) (α : ℝ) :
    portImbalance (primeMomentPort p) α = 2 * thetaPortReal α * primeMomentReal p α := by
  rw [primeMomentPort, primeGaugePort_imbalance_ofReal, div_self (Real.log_pos hp).ne', one_mul,
    primeMomentReal]

theorem hasDerivAt_primeMomentReal (p α : ℝ) :
    HasDerivAt (primeMomentReal p)
      (primeDeletionSymbolRealDeriv p α * thetaPortRealDeriv α + primeDeletionSymbolReal p α * thetaPortRealDeriv2 α +
        (-(p ^ (-(1 / 2 : ℝ)) * Real.log p ^ 2 * Real.cosh (Real.log p * α)) * thetaPortReal α +
          primeDeletionSymbolRealDeriv p α * thetaPortRealDeriv α)) α := by
  have h := ((hasDerivAt_primeDeletionSymbolReal p α).mul (hasDerivAt_thetaPortRealDeriv α)).add
    ((hasDerivAt_primeDeletionSymbolRealDeriv p α).mul (hasDerivAt_thetaPortReal α))
  exact h

/-- **The center curvature (11).** Strict order on a right neighbourhood of the center forces
`X''(0)/X(0) ≥ rL²/(1 - r)`. -/
theorem primeMomentPort_center_condition {p : ℝ} (hp : 1 < p)
    (hord : ∃ ε : ℝ, 0 < ε ∧ ∀ α : ℝ, 0 < α → α < ε → 0 < portImbalance (primeMomentPort p) (α : ℂ)) :
    p ^ (-(1 / 2 : ℝ)) * Real.log p ^ 2 * thetaPortReal 0 ≤
      (1 - p ^ (-(1 / 2 : ℝ))) * thetaPortRealDeriv2 0 := by
  obtain ⟨ε, hε, hpos⟩ := hord
  by_contra hcon
  push Not at hcon
  have hder := hasDerivAt_primeMomentReal p 0
  have h0 : primeMomentReal p 0 = 0 := by
    simp [primeMomentReal, primeDeletionSymbolRealDeriv, thetaPortRealDeriv_zero]
  have hval : primeDeletionSymbolRealDeriv p 0 * thetaPortRealDeriv 0 +
      primeDeletionSymbolReal p 0 * thetaPortRealDeriv2 0 +
      (-(p ^ (-(1 / 2 : ℝ)) * Real.log p ^ 2 * Real.cosh (Real.log p * 0)) * thetaPortReal 0 +
        primeDeletionSymbolRealDeriv p 0 * thetaPortRealDeriv 0) < 0 := by
    simp only [primeDeletionSymbolReal, primeDeletionSymbolRealDeriv, thetaPortRealDeriv_zero, mul_zero,
      Real.cosh_zero, Real.sinh_zero]
    linarith
  obtain ⟨α, hα0, hαε, hneg⟩ := exists_neg_of_hasDerivAt hder h0 hval hε
  have := hpos α hα0 hαε
  rw [primeMomentPort_imbalance_ofReal hp] at this
  have hX := thetaPortReal_pos α
  nlinarith

/-- The center condition holds for every sufficiently large prime. -/
theorem eventually_primeMomentPort_center :
    ∀ᶠ p in atTop, p ^ (-(1 / 2 : ℝ)) * Real.log p ^ 2 * thetaPortReal 0 <
      (1 - p ^ (-(1 / 2 : ℝ))) * thetaPortRealDeriv2 0 := by
  have hlog : Tendsto (fun p : ℝ => Real.log p / p ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hsq : Tendsto (fun p : ℝ => p ^ (-(1 / 2 : ℝ)) * Real.log p ^ 2) atTop (𝓝 0) := by
    have := hlog.pow 2
    rw [zero_pow two_ne_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hq : (p ^ (1 / 4 : ℝ)) ^ 2 = p ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
    rw [div_pow, hq, Real.rpow_neg hp.le, div_eq_inv_mul]
  have hr : Tendsto (fun p : ℝ => p ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hL := (hsq.mul_const (thetaPortReal 0))
  have hR := ((hr.const_sub 1).mul_const (thetaPortRealDeriv2 0))
  rw [zero_mul] at hL
  rw [sub_zero, one_mul] at hR
  exact hL.eventually_lt hR (thetaPortRealDeriv2_pos 0)

theorem primeDeletionSymbolReal_half {p : ℝ} (hp : 0 < p) : primeDeletionSymbolReal p (1 / 2) = (1 - p⁻¹) / 2 := by
  rw [primeDeletionSymbolReal, Real.cosh_eq, Real.rpow_def_of_pos hp]
  rw [mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add,
    show Real.log p * -(1 / 2) + Real.log p * (1 / 2) = 0 by ring,
    show Real.log p * -(1 / 2) + -(Real.log p * (1 / 2)) = -Real.log p by ring, Real.exp_zero,
    Real.exp_neg, Real.exp_log hp]
  ring

theorem primeDeletionSymbolRealDeriv_half {p : ℝ} (hp : 0 < p) :
    primeDeletionSymbolRealDeriv p (1 / 2) = -(Real.log p * (1 - p⁻¹) / 2) := by
  rw [primeDeletionSymbolRealDeriv, Real.sinh_eq, Real.rpow_def_of_pos hp]
  rw [show Real.exp (Real.log p * -(1 / 2)) * Real.log p *
      ((Real.exp (Real.log p * (1 / 2)) - Real.exp (-(Real.log p * (1 / 2)))) / 2) =
    Real.log p * ((Real.exp (Real.log p * -(1 / 2) + Real.log p * (1 / 2)) -
      Real.exp (Real.log p * -(1 / 2) + -(Real.log p * (1 / 2)))) / 2) by
      rw [Real.exp_add, Real.exp_add]; ring,
    show Real.log p * -(1 / 2) + Real.log p * (1 / 2) = 0 by ring,
    show Real.log p * -(1 / 2) + -(Real.log p * (1 / 2)) = -Real.log p by ring, Real.exp_zero,
    Real.exp_neg, Real.exp_log hp]
  ring

/-- **The wall values (11a).** `Y_p'(1/2) = (1 - p⁻¹)[X'(1/2) - log p · X(1/2)]/2`. -/
theorem primeMomentReal_half {p : ℝ} (hp : 0 < p) :
    primeMomentReal p (1 / 2) =
      (1 - p⁻¹) * (thetaPortRealDeriv (1 / 2) - Real.log p * thetaPortReal (1 / 2)) / 2 := by
  rw [primeMomentReal, primeDeletionSymbolReal_half hp, primeDeletionSymbolRealDeriv_half hp]; ring

/-- **The wall shear.** Once `log p > X'(1/2)/X(1/2)`, the clock-after-deletion port has a
negative modulus defect inside the physical strip. -/
theorem exists_primeMomentPort_imbalance_neg {p : ℝ} (hp : 1 < p)
    (hlog : thetaPortRealDeriv (1 / 2) / thetaPortReal (1 / 2) < Real.log p) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 2 ∧ portImbalance (primeMomentPort p) (α : ℂ) < 0 := by
  have hp0 : 0 < p := by linarith
  have hX := thetaPortReal_pos (1 / 2)
  have hY : primeMomentReal p (1 / 2) < 0 := by
    rw [primeMomentReal_half hp0]
    have h1 : 0 < 1 - p⁻¹ := by have := inv_lt_one_of_one_lt₀ hp; linarith
    have h2 : thetaPortRealDeriv (1 / 2) - Real.log p * thetaPortReal (1 / 2) < 0 := by
      rw [div_lt_iff₀ hX] at hlog; linarith
    have := mul_neg_of_pos_of_neg h1 h2
    linarith
  have hcont : ContinuousAt (primeMomentReal p) (1 / 2) :=
    (hasDerivAt_primeMomentReal p (1 / 2)).continuousAt
  have hev := (hcont.eventually (gt_mem_nhds hY)).and (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set α := 1 / 2 - min (δ / 2) (1 / 4)
  have hα1 : 0 < α := by simp only [α]; linarith [min_le_right (δ / 2) (1 / 4)]
  have hα2 : α < 1 / 2 := by
    have : 0 < min (δ / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
    simp only [α]; linarith
  have hm1 := min_le_left (δ / 2) (1 / 4)
  have hm2 : 0 < min (δ / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
  have hd : dist α (1 / 2) < δ := by
    rw [Real.dist_eq, abs_lt]; simp only [α]; constructor <;> linarith
  refine ⟨α, hα1, hα2, ?_⟩
  rw [primeMomentPort_imbalance_ofReal hp]
  have := (hball hd).1
  have := thetaPortReal_pos α
  nlinarith

theorem eventually_exists_primeMomentPort_imbalance_neg :
    ∀ᶠ p : ℝ in atTop, ∃ α : ℝ, 0 < α ∧ α < 1 / 2 ∧
      portImbalance (primeMomentPort p) (α : ℂ) < 0 := by
  filter_upwards [eventually_gt_atTop 1, (Real.tendsto_log_atTop.eventually_gt_atTop
    (thetaPortRealDeriv (1 / 2) / thetaPortReal (1 / 2)))] with p hp hlog
  exact exists_primeMomentPort_imbalance_neg hp hlog

/-- **The positive real radius (14).** The deletion-after-clock port satisfies `A_p(α) > 0` and
`D_p^cov(α) = 2X(α)A_p(α)X'(α) > 0` for `0 < α ≤ 1/2`. -/
theorem primeCovariantPort_imbalance_ofReal_pos {p : ℝ} (hp : 1 < p) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1 / 2) :
    0 < primeDeletionSymbolReal p α ∧ portImbalance (primeCovariantPort p) α =
      2 * thetaPortReal α * primeDeletionSymbolReal p α * thetaPortRealDeriv α ∧
      0 < portImbalance (primeCovariantPort p) α := by
  have hA : 0 < primeDeletionSymbolReal p α := by
    have h1 := rpow_mul_cosh_le hp (α := α) (by rw [abs_of_pos hα0]; exact hα1)
    have h2 := one_add_inv_div_two_lt_one hp
    simp only [primeDeletionSymbolReal]; linarith
  have hD : portImbalance (primeCovariantPort p) α =
      2 * thetaPortReal α * primeDeletionSymbolReal p α * thetaPortRealDeriv α := by
    rw [primeCovariantPort, primeGaugePort_imbalance_ofReal]; ring
  refine ⟨hA, hD, ?_⟩
  rw [hD]
  have := thetaPortReal_pos α
  have := thetaPortRealDeriv_pos hα0
  positivity

/-! ## A single prime sent to infinity (12) -/

/-- **(12).** On every compact subset of `|Re w| < 1/2` the clock-after-deletion port converges
uniformly to the derivative receiver `X/2 + X'` as `p → ∞`. -/
theorem tendstoUniformlyOn_primeMomentPort {K : Set ℂ} (hK : IsCompact K)
    (hKs : ∀ w ∈ K, |w.re| < 1 / 2) :
    TendstoUniformlyOn (fun (p : ℝ) w => primeMomentPort p w)
      (fun w => thetaSymmetrizedPort w / 2 + deriv thetaSymmetrizedPort w) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hne
    ((continuous_abs.comp Complex.continuous_re).continuousOn)
  set σ := |w₀.re|
  have hσ : σ < 1 / 2 := hKs w₀ hw₀
  have hσK : ∀ w ∈ K, |w.re| ≤ σ := fun w hw => hmax hw
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((differentiable_thetaSymmetrizedPort.continuous.norm.add
      differentiable_deriv_thetaSymmetrizedPort.continuous.norm).continuousOn)
  have hM0 : ∀ w ∈ K, ‖thetaSymmetrizedPort w‖ ≤ M ∧ ‖deriv thetaSymmetrizedPort w‖ ≤ M := by
    intro w hw
    have h := hM w hw
    simp only [Pi.add_apply, Real.norm_eq_abs] at h
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at h
    exact ⟨by linarith [norm_nonneg (deriv thetaSymmetrizedPort w)],
      by linarith [norm_nonneg (thetaSymmetrizedPort w)]⟩
  set δ := 1 / 2 - σ
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hb : Tendsto (fun p : ℝ => (1 + Real.log p) * p ^ (-δ) * (2 * |M|)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ => p ^ (-δ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hδ
    have h2 : Tendsto (fun p : ℝ => Real.log p * p ^ (-δ)) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with p hp
      rw [Real.rpow_neg hp.le, div_eq_mul_inv]
    have := (h1.add h2).mul_const (2 * |M|)
    rw [zero_add, zero_mul] at this
    refine this.congr fun p => ?_
    ring
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb.eventually (gt_mem_nhds hε), eventually_gt_atTop 1] with p hp hp1 w hw
  have hp0 : 0 < p := by linarith
  have hL : 0 < Real.log p := Real.log_pos hp1
  have hr : 0 ≤ p ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
  obtain ⟨hXM, hX'M⟩ := hM0 w hw
  have hcosh : Real.cosh (Real.log p * w.re) ≤ p ^ σ := by
    rw [Real.rpow_def_of_pos hp0, Real.cosh_eq]
    have h1 : Real.log p * w.re ≤ Real.log p * σ :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hσK w hw)) hL.le
    have h2 : -(Real.log p * w.re) ≤ Real.log p * σ := by
      have := mul_le_mul_of_nonneg_left ((neg_le_abs w.re).trans (hσK w hw)) hL.le
      linarith
    have := Real.exp_le_exp.mpr h1
    have := Real.exp_le_exp.mpr h2
    linarith
  have hrp : p ^ (-(1 / 2 : ℝ)) * p ^ σ = p ^ (-δ) := by
    rw [← Real.rpow_add hp0]; simp only [δ]; ring_nf
  have hA : ‖1 - primeDeletionSymbol p w‖ ≤ p ^ (-δ) := by
    refine (norm_one_sub_primeDeletionSymbol_le hp0.le w).trans ?_
    rw [← hrp]; exact mul_le_mul_of_nonneg_left hcosh hr
  have hA' : ‖primeDeletionSymbolDeriv p w‖ ≤ Real.log p * p ^ (-δ) := by
    rw [primeDeletionSymbolDeriv, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hs := norm_sinh_le_cosh_re ((Real.log p : ℂ) * w)
    have hre : ((Real.log p : ℂ) * w).re = Real.log p * w.re := by simp
    rw [hre] at hs
    calc p ^ (-(1 / 2 : ℝ)) * Real.log p * ‖Complex.sinh (↑(Real.log p) * w)‖
        ≤ p ^ (-(1 / 2 : ℝ)) * Real.log p * p ^ σ :=
          mul_le_mul_of_nonneg_left (hs.trans hcosh) (by positivity)
      _ = Real.log p * p ^ (-δ) := by rw [← hrp]; ring
  have hEp : primeMomentPort p w = thetaSymmetrizedPort w / 2 +
      primeDeletionSymbol p w * deriv thetaSymmetrizedPort w +
        primeDeletionSymbolDeriv p w * thetaSymmetrizedPort w := by
    rw [primeMomentPort, primeGaugePort, div_self hL.ne']; push_cast; ring
  rw [dist_eq_norm, hEp]
  have e : thetaSymmetrizedPort w / 2 + deriv thetaSymmetrizedPort w -
      (thetaSymmetrizedPort w / 2 + primeDeletionSymbol p w * deriv thetaSymmetrizedPort w +
        primeDeletionSymbolDeriv p w * thetaSymmetrizedPort w) =
      (1 - primeDeletionSymbol p w) * deriv thetaSymmetrizedPort w -
        primeDeletionSymbolDeriv p w * thetaSymmetrizedPort w := by ring
  rw [e]
  have hM : M ≤ |M| := le_abs_self M
  have hpd : 0 ≤ p ^ (-δ) := Real.rpow_nonneg hp0.le _
  calc ‖(1 - primeDeletionSymbol p w) * deriv thetaSymmetrizedPort w -
        primeDeletionSymbolDeriv p w * thetaSymmetrizedPort w‖
      ≤ ‖1 - primeDeletionSymbol p w‖ * ‖deriv thetaSymmetrizedPort w‖ +
          ‖primeDeletionSymbolDeriv p w‖ * ‖thetaSymmetrizedPort w‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ p ^ (-δ) * M + Real.log p * p ^ (-δ) * M := by
        gcongr
    _ ≤ (1 + Real.log p) * p ^ (-δ) * (2 * |M|) := by
        have h1 : 0 ≤ (1 + Real.log p) * p ^ (-δ) := by positivity
        have h2 : p ^ (-δ) * M + Real.log p * p ^ (-δ) * M = ((1 + Real.log p) * p ^ (-δ)) * M := by
          ring
        rw [h2]; exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg M]) h1
    _ < ε := hp

end

end RHTower
