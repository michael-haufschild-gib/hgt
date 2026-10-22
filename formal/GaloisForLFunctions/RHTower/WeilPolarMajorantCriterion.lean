import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity

/-!
# The majorant form of Weil's criterion on polar tests

A Weil test `f` (`C²`, compactly supported) is *polar* when `f̂(±i/2) = 0`; then the pole term of
its autocorrelation `k_f = f ⋆ f̃` vanishes.  The **polar nonnegative cone** `𝒞₊` consists of the
nonnegative combinations `Σ c_f k_f` of autocorrelations of polar tests whose normalized values
`ℓ_n = Re(k(log n) + k(−log n))/√n` are nonnegative at every `n ≥ 2`.  On `𝒞₊` the primes enter
`W_Λ` only through a nonnegative sum.

**Theorem** (`riemannHypothesis_iff_positiveOnPolarNonnegCone`).  RH holds iff `W_Λ ≥ 0` on `𝒞₊`.

**Majorants give no freedom** (`eq_vonMangoldt_of_ge_of_positiveOnPolarNonnegCone`).  A majorant
`lam ≥ Λ` with `W_lam ≥ 0` on `𝒞₊` is `Λ`.

**Proof.**  Positivity on `𝒞₊` is the hypothesis of the M. Riesz extension theorem
(`HTGeometry.exists_ge_of_nonneg_on_nonneg_cone`).  It produces weights `lam ≥ Λ` whose Weil
functional is nonnegative on every polar test, i.e. `lam` is Weil-positive in the polar cone
(`weilPositive_of_polar`); then `lam = Λ` and RH by polar majorant rigidity.  The extension needs,
for every `j ≥ 2`, a polar test whose `ℓ`-vector is a positive multiple of `e_j`
(`polarCoordinateTest`).  With `φ` a bump of radius `1/(4(j+1))`, the test
`h + φ(· − log j)`, `h = αφ' + βφ''`, `α = √j − 1/√j`, `β = −2(√j + 1/√j)`, is polar because
`∫ φ^{(k)} e^{cx} = (−c)^k ∫ φ e^{cx}`; its autocorrelation sees only `±log j`, with value
`∫ hφ = 2(√j + 1/√j) ∫ φ'² > 0`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff
open Zeta23

namespace RHTower.WeilPolarMajorant

noncomputable section

open WeilOneSided

/-! ## Polar positivity is the corpus's level-wise Weil positivity -/

/-- Nonnegativity of the full Weil functional on every polar test is the corpus's polar,
level-wise Weil positivity. -/
theorem weilPositive_of_polar {lam : ℕ → ℝ}
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → paperFT f (I / 2) = 0 →
      paperFT f (-(I / 2)) = 0 → 0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re) :
    WeilPositive lam :=
  _root_.RHTower.weilPositive_of_polar hW

/-! ## Integration by parts against compactly supported smooth functions -/

private theorem integral_mul_deriv {u ψ : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, u x * deriv ψ x = -∫ x, deriv u x * ψ x := by
  have hdu : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hcd : HasCompactSupport (deriv ψ) := hc.deriv
  refine integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hu.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hψ.differentiable (by norm_num) x).hasDerivAt) ?_ ?_ ?_
  · exact (hu.continuous.mul hdψ).integrable_of_hasCompactSupport hcd.mul_left
  · exact (hdu.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hu.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left

/-! ## Polar tests reaching one coordinate -/

/-- The real bump `φ_j` of radius `1/(4(j+1))`. -/
def bump (j : ℕ) (x : ℝ) : ℝ := narrowBump j x

theorem contDiff_bump (j : ℕ) : ContDiff ℝ ∞ (bump j) := (narrowBump j).contDiff

theorem hasCompactSupport_bump (j : ℕ) : HasCompactSupport (bump j) := (narrowBump j).hasCompactSupport

/-- The radius `r = 1/(4(j+1))`. -/
def radius (j : ℕ) : ℝ := 1 / (4 * ((j : ℝ) + 1))

theorem radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

theorem tsupport_bump (j : ℕ) : tsupport (bump j) ⊆ Icc (-radius j) (radius j) := by
  intro x hx
  have h : x ∈ Metric.closedBall (0 : ℝ) (narrowBump j).rOut := by
    rw [← (narrowBump j).tsupport_eq]; exact hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  exact abs_le.mp h

/-- The first and second derivatives of the bump. -/
def bump₁ (j : ℕ) : ℝ → ℝ := deriv (bump j)
def bump₂ (j : ℕ) : ℝ → ℝ := deriv (bump₁ j)

theorem contDiff_bump₁ (j : ℕ) : ContDiff ℝ ∞ (bump₁ j) :=
  (contDiff_infty_iff_deriv.mp (contDiff_bump j)).2

theorem contDiff_bump₂ (j : ℕ) : ContDiff ℝ ∞ (bump₂ j) :=
  (contDiff_infty_iff_deriv.mp (contDiff_bump₁ j)).2

theorem hasCompactSupport_bump₁ (j : ℕ) : HasCompactSupport (bump₁ j) :=
  (hasCompactSupport_bump j).deriv

theorem hasCompactSupport_bump₂ (j : ℕ) : HasCompactSupport (bump₂ j) :=
  (hasCompactSupport_bump₁ j).deriv

/-- The coefficients `α = √j − 1/√j`, `β = −2(√j + 1/√j)`. -/
def coefA (j : ℕ) : ℝ := Real.sqrt j - 1 / Real.sqrt j
def coefB (j : ℕ) : ℝ := -2 * (Real.sqrt j + 1 / Real.sqrt j)

/-- The local part `h = αφ' + βφ''`. -/
def localPart (j : ℕ) (x : ℝ) : ℝ := coefA j * bump₁ j x + coefB j * bump₂ j x

theorem localPart_eq_zero {j : ℕ} {x : ℝ} (hx : radius j < |x|) : localPart j x = 0 := by
  have h0 : x ∉ tsupport (bump j) := fun hm => by
    have := tsupport_bump j hm
    rw [mem_Icc] at this
    have := abs_le.mpr this
    linarith
  have h1 : bump₁ j x = 0 := by
    by_contra hne
    exact h0 (support_deriv_subset (Function.mem_support.mpr hne))
  have h2 : bump₂ j x = 0 := by
    by_contra hne
    have h3 : x ∈ tsupport (bump₂ j) := subset_tsupport _ (Function.mem_support.mpr hne)
    have h4 : x ∈ tsupport (bump₁ j) := tsupport_deriv_subset (f := bump₁ j) h3
    exact h0 (tsupport_deriv_subset (f := bump j) h4)
  simp [localPart, h1, h2]

theorem bump_eq_zero {j : ℕ} {x : ℝ} (hx : radius j < |x|) : bump j x = 0 := by
  by_contra hne
  have := tsupport_bump j (subset_tsupport _ (Function.mem_support.mpr hne))
  rw [mem_Icc] at this
  have := abs_le.mpr this
  linarith

/-- The real profile `g = h + φ(· − log j)`. -/
def profile (j : ℕ) (x : ℝ) : ℝ := localPart j x + bump j (x - Real.log j)


theorem contDiff_profile (j : ℕ) : ContDiff ℝ ∞ (profile j) :=
  ((contDiff_const.mul (contDiff_bump₁ j)).add (contDiff_const.mul (contDiff_bump₂ j))).add
    ((contDiff_bump j).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_profile (j : ℕ) : HasCompactSupport (profile j) :=
  (((hasCompactSupport_bump₁ j).mul_left).add (hasCompactSupport_bump₂ j).mul_left).add
    ((hasCompactSupport_bump j).comp_homeomorph (Homeomorph.subRight (Real.log j)))

theorem profile_ne_zero {j : ℕ} {t : ℝ} (ht : profile j t ≠ 0) :
    |t| ≤ radius j ∨ |t - Real.log j| ≤ radius j := by
  by_contra h
  push Not at h
  exact ht (by simp only [profile, localPart_eq_zero h.1, bump_eq_zero h.2, add_zero])

/-! ### Moments of the bump -/

private theorem continuous_bump (j : ℕ) : Continuous (bump j) := (contDiff_bump j).continuous

private theorem contDiff_one_of_infty {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 f :=
  hf.of_le (by norm_cast)

private theorem hasDerivAt_exp_mul (c x : ℝ) :
    HasDerivAt (fun x => Real.exp (c * x)) (c * Real.exp (c * x)) x := by
  have := ((hasDerivAt_id x).const_mul c).exp
  simpa [mul_comm] using this

private theorem deriv_exp_mul (c : ℝ) : deriv (fun x => Real.exp (c * x)) = fun x => c * Real.exp (c * x) :=
  funext fun x => (hasDerivAt_exp_mul c x).deriv

private theorem contDiff_exp_mul (c : ℝ) : ContDiff ℝ 1 fun x => Real.exp (c * x) := by fun_prop

/-- The exponential moment `M(c) = ∫ φ(x) e^{cx} dx`. -/
def moment (j : ℕ) (c : ℝ) : ℝ := ∫ x, bump j x * Real.exp (c * x)

theorem integral_bump₁_mul_exp (j : ℕ) (c : ℝ) :
    ∫ x, bump₁ j x * Real.exp (c * x) = -c * moment j c := by
  have h := integral_mul_deriv (contDiff_exp_mul c) (contDiff_one_of_infty (contDiff_bump j))
    (hasCompactSupport_bump j)
  rw [deriv_exp_mul] at h
  unfold moment bump₁
  simp_rw [mul_comm (deriv (bump j) _)]
  rw [h, ← integral_const_mul, ← integral_neg]
  congr 1
  funext x
  simp only
  ring

theorem integral_bump₂_mul_exp (j : ℕ) (c : ℝ) :
    ∫ x, bump₂ j x * Real.exp (c * x) = c ^ 2 * moment j c := by
  have h := integral_mul_deriv (contDiff_exp_mul c) (contDiff_one_of_infty (contDiff_bump₁ j))
    (hasCompactSupport_bump₁ j)
  rw [deriv_exp_mul] at h
  have h1 := integral_bump₁_mul_exp j c
  unfold bump₂
  simp_rw [mul_comm (deriv (bump₁ j) _)]
  rw [h]
  have e : ∫ x, c * Real.exp (c * x) * bump₁ j x = c * ∫ x, bump₁ j x * Real.exp (c * x) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e, h1]
  ring

theorem integral_bump_shift_mul_exp (j : ℕ) (c L : ℝ) :
    ∫ x, bump j (x - L) * Real.exp (c * x) = Real.exp (c * L) * moment j c := by
  rw [← integral_add_right_eq_self (fun x => bump j (x - L) * Real.exp (c * x)) L]
  unfold moment
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [add_sub_cancel_right, show c * (x + L) = c * x + c * L by ring, Real.exp_add]
  ring

private theorem integrable_mul_exp {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (c : ℝ) : Integrable fun x => g x * Real.exp (c * x) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right

theorem integral_profile_mul_exp (j : ℕ) (c : ℝ) :
    ∫ x, profile j x * Real.exp (c * x) =
      (-coefA j * c + coefB j * c ^ 2 + Real.exp (c * Real.log j)) * moment j c := by
  have h1 := integrable_mul_exp (contDiff_bump₁ j).continuous (hasCompactSupport_bump₁ j) c
  have h2 := integrable_mul_exp (contDiff_bump₂ j).continuous (hasCompactSupport_bump₂ j) c
  have h3 : Integrable fun x => bump j (x - Real.log j) * Real.exp (c * x) :=
    integrable_mul_exp (g := fun x => bump j (x - Real.log j))
      ((continuous_bump j).comp (continuous_id.sub continuous_const))
      ((hasCompactSupport_bump j).comp_homeomorph (Homeomorph.subRight (Real.log j))) c
  have ha : Integrable fun x => coefA j * (bump₁ j x * Real.exp (c * x)) := h1.const_mul _
  have hb : Integrable fun x => coefB j * (bump₂ j x * Real.exp (c * x)) := h2.const_mul _
  have hab : Integrable fun x => coefA j * (bump₁ j x * Real.exp (c * x)) +
      coefB j * (bump₂ j x * Real.exp (c * x)) := ha.add hb
  have e : (fun x => profile j x * Real.exp (c * x)) = fun x =>
      coefA j * (bump₁ j x * Real.exp (c * x)) + coefB j * (bump₂ j x * Real.exp (c * x)) +
        bump j (x - Real.log j) * Real.exp (c * x) := by
    funext x; simp only [profile, localPart]; ring
  rw [e, integral_add hab h3, integral_add ha hb, integral_const_mul, integral_const_mul,
    integral_bump₁_mul_exp, integral_bump₂_mul_exp, integral_bump_shift_mul_exp]
  ring

private theorem exp_half_log {j : ℕ} (hj : 2 ≤ j) :
    Real.exp (1 / 2 * Real.log j) = Real.sqrt j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hj0]
  ring_nf

private theorem exp_neg_half_log {j : ℕ} (hj : 2 ≤ j) :
    Real.exp (-1 / 2 * Real.log j) = 1 / Real.sqrt j := by
  rw [show -1 / 2 * Real.log j = -(1 / 2 * Real.log j) by ring, Real.exp_neg, exp_half_log hj,
    one_div]

/-- The profile is orthogonal to both pole profiles `e^{±x/2}`. -/
theorem integral_profile_mul_exp_half {j : ℕ} (hj : 2 ≤ j) :
    (∫ x, profile j x * Real.exp (1 / 2 * x)) = 0 ∧
      ∫ x, profile j x * Real.exp (-1 / 2 * x) = 0 := by
  have hs : 0 < Real.sqrt j := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < j by omega))
  rw [integral_profile_mul_exp, integral_profile_mul_exp, exp_half_log hj, exp_neg_half_log hj]
  unfold coefA coefB
  constructor
  · rw [show -(Real.sqrt j - 1 / Real.sqrt j) * (1 / 2) +
        -2 * (Real.sqrt j + 1 / Real.sqrt j) * (1 / 2) ^ 2 + Real.sqrt j = 0 by ring, zero_mul]
  · rw [show -(Real.sqrt j - 1 / Real.sqrt j) * (-1 / 2) +
        -2 * (Real.sqrt j + 1 / Real.sqrt j) * (-1 / 2) ^ 2 + 1 / Real.sqrt j = 0 by ring,
      zero_mul]

/-! ### The local energy -/

theorem integral_bump₁_mul_bump (j : ℕ) : ∫ x, bump₁ j x * bump j x = 0 := by
  have h := integral_mul_deriv (contDiff_one_of_infty (contDiff_bump j))
    (contDiff_one_of_infty (contDiff_bump j)) (hasCompactSupport_bump j)
  have e : ∫ x, bump j x * deriv (bump j) x = ∫ x, bump₁ j x * bump j x := by
    unfold bump₁; congr 1; funext x; ring
  rw [e] at h
  unfold bump₁ at h ⊢
  linarith

theorem integral_bump₂_mul_bump (j : ℕ) :
    ∫ x, bump₂ j x * bump j x = -∫ x, bump₁ j x ^ 2 := by
  have h := integral_mul_deriv (contDiff_one_of_infty (contDiff_bump j))
    (contDiff_one_of_infty (contDiff_bump₁ j)) (hasCompactSupport_bump₁ j)
  have e : ∫ x, bump j x * deriv (bump₁ j) x = ∫ x, bump₂ j x * bump j x := by
    unfold bump₂; congr 1; funext x; ring
  rw [e] at h
  rw [h]
  congr 1
  unfold bump₁
  congr 1
  funext x
  ring

theorem exists_bump₁_ne_zero (j : ℕ) : ∃ x, bump₁ j x ≠ 0 := by
  have hr := radius_pos j
  have h0 : bump j 0 = 1 :=
    (narrowBump j).one_of_mem_closedBall (Metric.mem_closedBall_self (narrowBump j).rIn_pos.le)
  have hR : bump j (radius j) = 0 := by
    refine (narrowBump j).zero_of_le_dist ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    rfl
  obtain ⟨x, -, hx⟩ := exists_deriv_eq_slope (bump j) hr
    (continuous_bump j).continuousOn
    (fun x _ => ((contDiff_bump j).differentiable (by simp) x).differentiableWithinAt)
  refine ⟨x, ?_⟩
  unfold bump₁
  rw [hx, hR, h0, sub_zero]
  exact div_ne_zero (by norm_num) hr.ne'

theorem integral_bump₁_sq_pos (j : ℕ) : 0 < ∫ x, bump₁ j x ^ 2 := by
  obtain ⟨x, hx⟩ := exists_bump₁_ne_zero j
  exact ((contDiff_bump₁ j).continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((hasCompactSupport_bump₁ j).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num))
    (fun _ => sq_nonneg _) (x := x) (pow_ne_zero 2 hx)

/-- The local energy `∫ hφ = 2(√j + 1/√j) ∫ φ'²`. -/
def localEnergy (j : ℕ) : ℝ := ∫ x, localPart j x * bump j x

theorem localEnergy_eq (j : ℕ) :
    localEnergy j = 2 * (Real.sqrt j + 1 / Real.sqrt j) * ∫ x, bump₁ j x ^ 2 := by
  have h1 : Integrable fun x => bump₁ j x * bump j x :=
    ((contDiff_bump₁ j).continuous.mul (continuous_bump j)).integrable_of_hasCompactSupport
      (hasCompactSupport_bump j).mul_left
  have h2 : Integrable fun x => bump₂ j x * bump j x :=
    ((contDiff_bump₂ j).continuous.mul (continuous_bump j)).integrable_of_hasCompactSupport
      (hasCompactSupport_bump j).mul_left
  have ha : Integrable fun x => coefA j * (bump₁ j x * bump j x) := h1.const_mul _
  have hb : Integrable fun x => coefB j * (bump₂ j x * bump j x) := h2.const_mul _
  have e : (fun x => localPart j x * bump j x) =
      fun x => coefA j * (bump₁ j x * bump j x) + coefB j * (bump₂ j x * bump j x) := by
    funext x; simp only [localPart]; ring
  unfold localEnergy
  rw [e, integral_add ha hb, integral_const_mul, integral_const_mul,
    integral_bump₁_mul_bump, integral_bump₂_mul_bump]
  unfold coefB
  ring

theorem localEnergy_pos {j : ℕ} (hj : 1 ≤ j) : 0 < localEnergy j := by
  rw [localEnergy_eq]
  have hs : 0 < Real.sqrt j := Real.sqrt_pos.mpr (by exact_mod_cast hj)
  exact mul_pos (mul_pos two_pos (add_pos_of_pos_of_nonneg hs (by positivity)))
    (integral_bump₁_sq_pos j)

/-! ### The autocorrelation of the coordinate test -/

/-- The polar coordinate test `x ↦ g(x)` as a complex function. -/
def coordTest (j : ℕ) (x : ℝ) : ℂ := (profile j x : ℂ)

theorem weilTest_coordTest (j : ℕ) (y : ℝ) :
    EF.weilTest (coordTest j) (coordTest j) y =
      ((∫ t, profile j t * profile j (t - y) : ℝ) : ℂ) := by
  unfold EF.weilTest convolution EF.tilde
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', coordTest, Complex.conj_ofReal]
  rw [show -(y - t) = t - y by ring]
  push_cast
  ring

private theorem two_radius_lt_log_two (j : ℕ) : 2 * radius j < Real.log 2 := by
  have h := Real.log_two_gt_d9
  unfold radius
  have : 2 * (1 / (4 * ((j : ℝ) + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  linarith

private theorem log_ge_log_two {n : ℕ} (hn : 2 ≤ n) : Real.log 2 ≤ Real.log n :=
  Real.log_le_log two_pos (by exact_mod_cast hn)

/-- Products vanish away from the three difference windows. -/
theorem profile_mul_shift_eq_zero {j : ℕ} {y : ℝ} (h1 : 2 * radius j < |y|)
    (h2 : 2 * radius j < |y - Real.log j|) (h3 : 2 * radius j < |y + Real.log j|) (t : ℝ) :
    profile j t * profile j (t - y) = 0 := by
  by_contra hne
  have ha := profile_ne_zero (left_ne_zero_of_mul hne)
  have hb := profile_ne_zero (right_ne_zero_of_mul hne)
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have : |y| ≤ 2 * radius j := by
      calc |y| = |t - (t - y)| := by ring_nf
        _ ≤ |t| + |t - y| := abs_sub _ _
        _ ≤ 2 * radius j := by linarith
    linarith
  · have : |y + Real.log j| ≤ 2 * radius j := by
      calc |y + Real.log j| = |t - (t - y - Real.log j)| := by ring_nf
        _ ≤ |t| + |t - y - Real.log j| := abs_sub _ _
        _ ≤ 2 * radius j := by linarith
    linarith
  · have : |y - Real.log j| ≤ 2 * radius j := by
      calc |y - Real.log j| = |(t - Real.log j) - (t - y)| := by ring_nf
        _ ≤ |t - Real.log j| + |t - y| := abs_sub _ _
        _ ≤ 2 * radius j := by linarith
    linarith
  · have : |y| ≤ 2 * radius j := by
      calc |y| = |(t - Real.log j) - (t - y - Real.log j)| := by ring_nf
        _ ≤ |t - Real.log j| + |t - y - Real.log j| := abs_sub _ _
        _ ≤ 2 * radius j := by linarith
    linarith

theorem profile_mul_shift_log {j : ℕ} (hj : 2 ≤ j) (t : ℝ) :
    profile j t * profile j (t - Real.log j) =
      bump j (t - Real.log j) * localPart j (t - Real.log j) := by
  have hL := log_ge_log_two hj
  have hr := two_radius_lt_log_two j
  have hr0 := radius_pos j
  by_cases ht : |t - Real.log j| ≤ radius j
  · have hta : radius j < |t| := by
      have := abs_sub_abs_le_abs_sub t (Real.log j)
      have : |Real.log j| = Real.log j := abs_of_pos (by linarith)
      have := abs_sub_abs_le_abs_sub (Real.log j) t
      rw [abs_sub_comm] at ht
      linarith [le_abs_self t, neg_abs_le t, abs_le.mp ht]
    have htb : radius j < |t - Real.log j - Real.log j| := by
      have := abs_le.mp ht
      rw [abs_of_neg (by linarith)]
      linarith
    simp only [profile, localPart_eq_zero hta, bump_eq_zero htb, zero_add, add_zero]
  · push Not at ht
    rw [bump_eq_zero ht, zero_mul]
    by_contra hne
    have ha := profile_ne_zero (left_ne_zero_of_mul hne)
    have hb := profile_ne_zero (right_ne_zero_of_mul hne)
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · have := abs_le.mp ha; have := abs_le.mp hb; linarith
      · have := abs_le.mp ha; have := abs_le.mp hb; linarith
    · linarith

theorem profile_mul_shift_neg_log {j : ℕ} (hj : 2 ≤ j) (t : ℝ) :
    profile j t * profile j (t - -Real.log j) = localPart j t * bump j t := by
  have h := profile_mul_shift_log hj (t + Real.log j)
  rw [add_sub_cancel_right] at h
  rw [sub_neg_eq_add, mul_comm, h, mul_comm]

theorem integral_profile_mul_shift_log {j : ℕ} (hj : 2 ≤ j) :
    ∫ t, profile j t * profile j (t - Real.log j) = localEnergy j := by
  simp_rw [profile_mul_shift_log hj]
  rw [integral_sub_right_eq_self (fun t => bump j t * localPart j t) (Real.log j)]
  unfold localEnergy
  congr 1; funext t; ring

theorem integral_profile_mul_shift_neg_log {j : ℕ} (hj : 2 ≤ j) :
    ∫ t, profile j t * profile j (t - -Real.log j) = localEnergy j := by
  simp_rw [profile_mul_shift_neg_log hj]
  rfl

/-- The normalized values of the coordinate test: `2 E_j/√j` at `n = j` and `0` elsewhere. -/
theorem logValue_coordTest {j : ℕ} (hj : 2 ≤ j) {n : ℕ} (hn : 2 ≤ n) :
    logValue (coordTest j) n = if n = j then 2 * localEnergy j / Real.sqrt j else 0 := by
  unfold logValue
  rw [weilTest_coordTest, weilTest_coordTest]
  split_ifs with hnj
  · subst hnj
    rw [integral_profile_mul_shift_log hj, integral_profile_mul_shift_neg_log hj,
      Complex.add_re, Complex.ofReal_re]
    ring
  · have hr := two_radius_lt_log_two j
    have hlog_n := log_ge_log_two hn
    have hlog_j := log_ge_log_two hj
    have hgap := WeilExcess.inv_succ_le_abs_log_sub (by omega) (by omega) hnj
    have hgap' : 2 * radius j < |Real.log n - Real.log j| := by
      refine lt_of_lt_of_le ?_ hgap
      unfold radius
      rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hpos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have e1 : (fun t => profile j t * profile j (t - Real.log n)) = fun _ => 0 := by
      funext t
      refine profile_mul_shift_eq_zero ?_ hgap' ?_ t
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have e2 : (fun t => profile j t * profile j (t - -Real.log n)) = fun _ => 0 := by
      funext t
      refine profile_mul_shift_eq_zero ?_ ?_ ?_ t
      · rw [abs_neg, abs_of_pos (by linarith)]; linarith
      · rw [show -Real.log n - Real.log j = -(Real.log n + Real.log j) by ring, abs_neg,
          abs_of_pos (by linarith)]; linarith
      · rw [show -Real.log n + Real.log j = -(Real.log n - Real.log j) by ring, abs_neg]
        exact hgap'
    rw [e1, e2]
    simp

theorem paperFT_coordTest {j : ℕ} (hj : 2 ≤ j) :
    paperFT (coordTest j) (I / 2) = 0 ∧ paperFT (coordTest j) (-(I / 2)) = 0 := by
  obtain ⟨hp, hm⟩ := integral_profile_mul_exp_half hj
  have key : ∀ c : ℝ, ∀ z : ℂ, (∀ x : ℝ, I * z * (x : ℂ) = ((c * x : ℝ) : ℂ)) →
      paperFT (coordTest j) z = ((∫ x, profile j x * Real.exp (c * x) : ℝ) : ℂ) := by
    intro c z hz
    unfold paperFT coordTest
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [hz x, ← Complex.ofReal_exp]
    push_cast
    ring
  constructor
  · rw [key (-1 / 2) (I / 2) (fun x => by push_cast; linear_combination ((x : ℂ) / 2) * Complex.I_sq),
      hm, Complex.ofReal_zero]
  · rw [key (1 / 2) (-(I / 2)) (fun x => by
        push_cast; linear_combination (-(x : ℂ) / 2) * Complex.I_sq), hp, Complex.ofReal_zero]

/-! ## The polar nonnegative cone -/

/-- Polar Weil tests: `f̂(±i/2) = 0`. -/
def PolarTestFn : Type := {f : WeilTestFn // paperFT f.1 (I / 2) = 0 ∧ paperFT f.1 (-(I / 2)) = 0}

/-- The coordinate test as a polar Weil test. -/
def coordTestFn (j : LogIndex) : PolarTestFn :=
  ⟨⟨coordTest j, ofRealCLM.contDiff.comp ((contDiff_profile j).of_le (by norm_cast)),
    (hasCompactSupport_profile j).comp_left Complex.ofReal_zero⟩, paperFT_coordTest j.2⟩

theorem logVector_coordTestFn (j : LogIndex) :
    logVector (coordTestFn j).1 =
      Finsupp.single j (2 * localEnergy j / Real.sqrt j) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (coordTest j) m = _
  rw [logValue_coordTest j.2 m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm]
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

theorem coordWeight_pos (j : LogIndex) : 0 < 2 * localEnergy j / Real.sqrt j := by
  have hj : (0 : ℝ) < (j : ℕ) := by exact_mod_cast (lt_of_lt_of_le two_pos j.2)
  exact div_pos (mul_pos two_pos (localEnergy_pos (by have := j.2; omega))) (Real.sqrt_pos.mpr hj)

/-- Weil positivity of `L` on the polar nonnegative cone `𝒞₊`: nonnegative combinations of
autocorrelations of polar tests whose normalized values at every `±log n` are nonnegative. -/
def PositiveOnPolarNonnegCone (L : ℕ → ℝ) : Prop :=
  ∀ c : PolarTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1.1 n) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional L (EF.weilTest f.1.1 f.1.1)).re

theorem linearCombination_polarLogVector_apply (c : PolarTestFn →₀ ℝ) (j : LogIndex) :
    linearCombination ℝ (fun f : PolarTestFn => logVector f.1) c j =
      c.sum fun f t => t * logValue f.1.1 j := by
  rw [linearCombination_apply, Finsupp.sum_apply]
  simp [logVector_apply]

theorem sum_re_weilFullFunctional_polar (U : ℕ → ℝ) (c : PolarTestFn →₀ ℝ) :
    (c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1.1 f.1.1)).re) =
      linearCombination ℝ (fun f : PolarTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) c -
        linearCombination ℝ (fun j : LogIndex => U j)
          (linearCombination ℝ (fun f : PolarTestFn => logVector f.1) c) := by
  simp_rw [re_weilFullFunctional_eq _ (Subtype.val _)]
  have e1 : linearCombination ℝ (fun f : PolarTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) c =
      c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1) := by
    rw [linearCombination_apply]; simp only [smul_eq_mul]
  have e2 : linearCombination ℝ (fun j : LogIndex => U j)
      (linearCombination ℝ (fun f : PolarTestFn => logVector f.1) c) =
      c.sum fun f t => t * linearCombination ℝ (fun j : LogIndex => U j) (logVector f.1) := by
    rw [linearCombination_apply ℝ (v := fun f : PolarTestFn => logVector f.1), map_finsuppSum]
    exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
  rw [e1, e2, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun f _ => by ring

/-- **Positivity on `𝒞₊` produces a polar Weil-positive majorant of `L`.** -/
theorem exists_weilPositive_ge_of_positiveOnPolarNonnegCone {L : ℕ → ℝ}
    (h : PositiveOnPolarNonnegCone L) :
    ∃ lam : ℕ → ℝ, WeilPositive lam ∧ ∀ n, 2 ≤ n → L n ≤ lam n := by
  obtain ⟨lam, hlamL, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_ge_of_nonneg_on_nonneg_cone
    (fun f : PolarTestFn => logVector f.1)
    (fun f : PolarTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) (fun j : LogIndex => L j)
    (fun j => ⟨coordTestFn j, _, coordWeight_pos j, logVector_coordTestFn j⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        rw [← linearCombination_polarLogVector_apply c ⟨n, hn⟩]; exact hcT ⟨n, hn⟩
      rw [sum_re_weilFullFunctional_polar] at h1
      linarith)
  refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0,
    weilPositive_of_polar fun f hf hc hp hm => ?_, fun n hn => ?_⟩
  · rw [re_weilFullFunctional_eq _ ⟨f, hf, hc⟩]
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
        lam := funext fun j => by simp [j.2]
    rw [e]
    linarith [hlamT ⟨⟨f, hf, hc⟩, hp, hm⟩]
  · simp only [dif_pos hn]; exact hlamL ⟨n, hn⟩

/-- **Majorant form of Weil's criterion on polar tests.**  RH holds iff `W_Λ ≥ 0` on the polar
nonnegative cone `𝒞₊`. -/
theorem riemannHypothesis_iff_positiveOnPolarNonnegCone :
    RiemannHypothesis ↔
      PositiveOnPolarNonnegCone fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH c hc _
    exact Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f)
      ((riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) f.1.1 f.1.2.1 f.1.2.2)
  · intro h
    obtain ⟨lam, hW, hge⟩ := exists_weilPositive_ge_of_positiveOnPolarNonnegCone h
    exact riemannHypothesis_iff_exists_weilPositive_ge.mpr ⟨lam, hW, hge⟩

/-- **Majorants give no freedom on `𝒞₊`.**  A majorant `lam ≥ Λ` whose Weil functional is
nonnegative on the polar nonnegative cone is `Λ`. -/
theorem eq_vonMangoldt_of_ge_of_positiveOnPolarNonnegCone {lam : ℕ → ℝ}
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n)
    (h : PositiveOnPolarNonnegCone lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨lam', hW', hle'⟩ := exists_weilPositive_ge_of_positiveOnPolarNonnegCone h
  have heq := eq_vonMangoldt_of_weilPositive_of_ge hW' fun n hn => (hge n hn).trans (hle' n hn)
  exact fun n hn => le_antisymm (by linarith [hle' n hn, heq n hn]) (hge n hn)

end

end RHTower.WeilPolarMajorant
