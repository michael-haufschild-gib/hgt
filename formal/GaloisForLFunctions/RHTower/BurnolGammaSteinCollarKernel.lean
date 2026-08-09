import Mathlib

/-!
# The Gamma-sewn prime-two collar kernel

In the logarithmic coordinate the archimedean factor of the Burnol source is the density

`γ(u) = 2 e^{-u/2} exp(-π e^{-2u})`,

and the prime-two completion multiplier `C₂(w) = w²(w-1)/(2(2^w-1))` becomes the Stein polynomial
`½ A²(A-1)` with `A = ∂ + 1/2` composed with the causal dyadic ladder.  Each dyadic depth
contributes one translated copy of the same three-chamber profile

`κ_n(u) = 4 e^{-u/2} e^{-z} z (2z² - 7z + 3)`,   `z = z_n(u) = π 4ⁿ e^{-2u}`.

The whole computation rests on one differentiation rule: on the profile family `h_n · P(z_n)` the
Stein operator acts by `P ↦ 2z (P - P')`.  Iterating it three times produces the cubic
`8z³ - 28z² + 12z`, whose sign is that of `2(z - 1/2)(z - 3)`.  Hence every depth carries exactly
one negative logarithmic collar, of depth-independent width `½ log 6`.

The first transverse deformation of the polar factor has kernel `2z(3z-4)γ`, with a single sign
change at `½ log (3π/4)`.
-/

open Real Filter Topology

noncomputable section

namespace RHTower

/-! ## The Stein operator and the collar profiles -/

/-- The logarithmic Stein operator `A = ∂ + 1/2`. -/
def burnolSteinA (f : ℝ → ℝ) : ℝ → ℝ := fun u => deriv f u + f u / 2

/-- The depth-`n` dyadic variable `z_n(u) = π 4ⁿ e^{-2u}`. -/
def burnolCollarZ (n : ℕ) (u : ℝ) : ℝ := π * 4 ^ n * Real.exp (-2 * u)

/-- The depth-`n` Gamma-sewn profile `h_n(u) = 2 e^{-u/2} exp(-z_n(u))`. -/
def burnolCollarH (n : ℕ) (u : ℝ) : ℝ :=
  2 * Real.exp (-u / 2) * Real.exp (-burnolCollarZ n u)

/-- The archimedean collar density `γ(u) = 2 e^{-u/2} exp(-π e^{-2u})`. -/
def burnolCollarGamma : ℝ → ℝ := burnolCollarH 0

theorem burnolCollarZ_pos (n : ℕ) (u : ℝ) : 0 < burnolCollarZ n u := by
  unfold burnolCollarZ
  positivity

theorem burnolCollarH_pos (n : ℕ) (u : ℝ) : 0 < burnolCollarH n u := by
  unfold burnolCollarH
  positivity

theorem burnolCollarZ_zero (u : ℝ) : burnolCollarZ 0 u = π * Real.exp (-2 * u) := by
  unfold burnolCollarZ
  norm_num

theorem burnolCollarGamma_apply (u : ℝ) :
    burnolCollarGamma u = 2 * Real.exp (-u / 2) * Real.exp (-(π * Real.exp (-2 * u))) := by
  rw [burnolCollarGamma, burnolCollarH, burnolCollarZ_zero]

theorem hasDerivAt_burnolCollarZ (n : ℕ) (u : ℝ) :
    HasDerivAt (burnolCollarZ n) (-2 * burnolCollarZ n u) u := by
  have hlin : HasDerivAt (fun v : ℝ => -2 * v) (-2 : ℝ) u := by
    simpa using (hasDerivAt_id u).const_mul (-2 : ℝ)
  have h : HasDerivAt (fun v : ℝ => Real.exp (-2 * v)) (Real.exp (-2 * u) * (-2)) u := hlin.exp
  refine (h.const_mul (π * 4 ^ n)).congr_deriv ?_
  unfold burnolCollarZ
  ring

theorem hasDerivAt_burnolCollarH (n : ℕ) (u : ℝ) :
    HasDerivAt (burnolCollarH n) (burnolCollarH n u * (2 * burnolCollarZ n u - 1 / 2)) u := by
  have h1 : HasDerivAt (fun v : ℝ => 2 * Real.exp (-v / 2))
      (2 * Real.exp (-u / 2) * (-(1 / 2))) u := by
    have hb : HasDerivAt (fun v : ℝ => -v / 2) (-(1 / 2)) u :=
      ((hasDerivAt_id u).neg.div_const 2).congr_deriv (by ring)
    refine (hb.exp.const_mul (2 : ℝ)).congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (-burnolCollarZ n v))
      (Real.exp (-burnolCollarZ n u) * (2 * burnolCollarZ n u)) u := by
    refine ((hasDerivAt_burnolCollarZ n u).neg.exp).congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have := h1.mul h2
  refine this.congr_deriv ?_
  unfold burnolCollarH
  ring

/-- **The Stein operator on the collar profile family.**  On `h_n · P(z_n)` it acts by
`P ↦ 2 z (P - P')`. -/
theorem burnolSteinA_collarProfile (n : ℕ) {P Q : ℝ → ℝ} (hP : ∀ x : ℝ, HasDerivAt P (Q x) x)
    (u : ℝ) :
    burnolSteinA (fun v => burnolCollarH n v * P (burnolCollarZ n v)) u =
      2 * burnolCollarZ n u * burnolCollarH n u *
        (P (burnolCollarZ n u) - Q (burnolCollarZ n u)) := by
  have hcomp : HasDerivAt (fun v => P (burnolCollarZ n v))
      (Q (burnolCollarZ n u) * (-2 * burnolCollarZ n u)) u :=
    (hP (burnolCollarZ n u)).comp u (hasDerivAt_burnolCollarZ n u)
  have hprod : HasDerivAt (fun v => burnolCollarH n v * P (burnolCollarZ n v))
      (burnolCollarH n u * (2 * burnolCollarZ n u - 1 / 2) * P (burnolCollarZ n u) +
        burnolCollarH n u * (Q (burnolCollarZ n u) * (-2 * burnolCollarZ n u))) u :=
    (hasDerivAt_burnolCollarH n u).mul hcomp
  rw [burnolSteinA, hprod.deriv]
  ring

/-- The Stein operator applied to the collar density itself. -/
theorem burnolSteinA_burnolCollarH (n : ℕ) (u : ℝ) :
    burnolSteinA (burnolCollarH n) u = 2 * burnolCollarZ n u * burnolCollarH n u := by
  have h := burnolSteinA_collarProfile n (P := fun _ : ℝ => (1 : ℝ)) (Q := fun _ : ℝ => (0 : ℝ))
    (fun x => hasDerivAt_const x 1) u
  simpa using h

/-- First polar step: `(A - 1) h_n = h_n (2 z_n - 1)`. -/
theorem burnolSteinA_sub_one_burnolCollarH (n : ℕ) (u : ℝ) :
    burnolSteinA (burnolCollarH n) u - burnolCollarH n u =
      burnolCollarH n u * (2 * burnolCollarZ n u - 1) := by
  rw [burnolSteinA_burnolCollarH]
  ring

/-- Second polar step. -/
theorem burnolSteinA_polarOne (n : ℕ) (u : ℝ) :
    burnolSteinA (fun v => burnolCollarH n v * (2 * burnolCollarZ n v - 1)) u =
      burnolCollarH n u * (4 * burnolCollarZ n u ^ 2 - 6 * burnolCollarZ n u) := by
  have h := burnolSteinA_collarProfile n (P := fun x : ℝ => 2 * x - 1)
    (Q := fun _ : ℝ => (2 : ℝ)) (fun x => by simpa using (hasDerivAt_id x).const_mul (2 : ℝ)) u
  rw [h]
  ring

/-- Third polar step: the cubic `8 z³ - 28 z² + 12 z`. -/
theorem burnolSteinA_polarTwo (n : ℕ) (u : ℝ) :
    burnolSteinA (fun v => burnolCollarH n v *
        (4 * burnolCollarZ n v ^ 2 - 6 * burnolCollarZ n v)) u =
      burnolCollarH n u * (8 * burnolCollarZ n u ^ 3 - 28 * burnolCollarZ n u ^ 2 +
        12 * burnolCollarZ n u) := by
  have hP : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 4 * x ^ 2 - 6 * x) (8 * x - 6) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => 4 * x ^ 2) (4 * (2 * x)) x :=
      ((hasDerivAt_pow 2 x).const_mul (4 : ℝ)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x : ℝ => 6 * x) (6 : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (6 : ℝ)
    exact (h1.sub h2).congr_deriv (by ring)
  have h := burnolSteinA_collarProfile n (P := fun x : ℝ => 4 * x ^ 2 - 6 * x)
    (Q := fun x : ℝ => 8 * x - 6) hP u
  rw [h]
  ring

/-! ## The depth kernels -/

/-- The depth-`n` Gamma-sewn collar kernel. -/
def burnolCollarKernel (n : ℕ) (u : ℝ) : ℝ :=
  4 * Real.exp (-u / 2) * Real.exp (-burnolCollarZ n u) * burnolCollarZ n u *
    (2 * burnolCollarZ n u ^ 2 - 7 * burnolCollarZ n u + 3)

/-- **The kernel is the halved third Stein iterate of the Gamma profile.** -/
theorem burnolCollarKernel_eq_steinIterate (n : ℕ) (u : ℝ) :
    burnolCollarKernel n u =
      1 / 2 * burnolSteinA (fun v => burnolCollarH n v *
        (4 * burnolCollarZ n v ^ 2 - 6 * burnolCollarZ n v)) u := by
  rw [burnolSteinA_polarTwo, burnolCollarKernel, burnolCollarH]
  ring

/-- **Every depth is one translated copy of the depth-zero profile.** -/
theorem burnolCollarKernel_eq_translate (n : ℕ) (u : ℝ) :
    burnolCollarKernel n u =
      (2 : ℝ) ^ (-(n : ℝ) / 2) * burnolCollarKernel 0 (u - n * Real.log 2) := by
  have hz : burnolCollarZ 0 (u - n * Real.log 2) = burnolCollarZ n u := by
    unfold burnolCollarZ
    rw [show (-2 : ℝ) * (u - n * Real.log 2) = -2 * u + n * (2 * Real.log 2) by ring,
      Real.exp_add]
    have h4 : Real.exp ((n : ℝ) * (2 * Real.log 2)) = 4 ^ n := by
      rw [show (n : ℝ) * (2 * Real.log 2) = Real.log 4 * (n : ℝ) by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring,
        ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_natCast]
    rw [h4]
    ring
  have hexp : Real.exp (-(u - n * Real.log 2) / 2) =
      (2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-u / 2) := by
    rw [show -((u : ℝ) - n * Real.log 2) / 2 = (n : ℝ) / 2 * Real.log 2 + -u / 2 by ring,
      Real.exp_add, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  rw [burnolCollarKernel, burnolCollarKernel, hz, hexp]
  have hpow : (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (-(n : ℝ) / 2 + (n : ℝ) / 2) = 0 by ring, Real.rpow_zero]
  linear_combination (-(4 * Real.exp (-u / 2) * Real.exp (-burnolCollarZ n u) *
    burnolCollarZ n u * (2 * burnolCollarZ n u ^ 2 - 7 * burnolCollarZ n u + 3))) * hpow

/-! ## The three-chamber sign law -/

theorem burnolCollarKernel_sign_factor (n : ℕ) (u : ℝ) :
    burnolCollarKernel n u < 0 ↔ 2 * burnolCollarZ n u ^ 2 - 7 * burnolCollarZ n u + 3 < 0 := by
  have hpos : 0 < 4 * Real.exp (-u / 2) * Real.exp (-burnolCollarZ n u) * burnolCollarZ n u := by
    have := burnolCollarZ_pos n u
    positivity
  rw [burnolCollarKernel]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem burnolCollarQuadratic_neg_iff (z : ℝ) :
    2 * z ^ 2 - 7 * z + 3 < 0 ↔ 1 / 2 < z ∧ z < 3 := by
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

/-- **One universal negative collar at every depth.** -/
theorem burnolCollarKernel_neg_iff (n : ℕ) (u : ℝ) :
    burnolCollarKernel n u < 0 ↔
      (n : ℝ) * Real.log 2 + 1 / 2 * Real.log (π / 3) < u ∧
        u < (n : ℝ) * Real.log 2 + 1 / 2 * Real.log (2 * π) := by
  rw [burnolCollarKernel_sign_factor, burnolCollarQuadratic_neg_iff]
  have hpi : 0 < π := Real.pi_pos
  have hz : burnolCollarZ n u = π * 4 ^ n * Real.exp (-2 * u) := rfl
  have hfour : (4 : ℝ) ^ n = Real.exp ((n : ℝ) * (2 * Real.log 2)) := by
    rw [show (n : ℝ) * (2 * Real.log 2) = Real.log 4 * (n : ℝ) by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring,
      ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_natCast]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · -- `z < 3` gives the left endpoint
      have hlt : Real.exp (-2 * u) < 3 / (π * 4 ^ n) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith [hz ▸ h2]
      have := Real.log_lt_log (Real.exp_pos _) hlt
      rw [Real.log_exp, Real.log_div (by norm_num) (by positivity), Real.log_mul
        (by positivity) (by positivity), hfour, Real.log_exp] at this
      have hlogpi : Real.log (π / 3) = Real.log π - Real.log 3 :=
        Real.log_div (ne_of_gt hpi) (by norm_num)
      rw [hlogpi]
      linarith
    · have hgt : 1 / (2 * (π * 4 ^ n)) < Real.exp (-2 * u) := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hz ▸ h1]
      have := Real.log_lt_log (by positivity) hgt
      rw [Real.log_exp, Real.log_div (by norm_num) (by positivity), Real.log_mul
        (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
        hfour, Real.log_exp, Real.log_one] at this
      have hlog2pi : Real.log (2 * π) = Real.log 2 + Real.log π :=
        Real.log_mul (by norm_num) (ne_of_gt hpi)
      rw [hlog2pi]
      linarith
  · rintro ⟨h1, h2⟩
    have hlogpi : Real.log (π / 3) = Real.log π - Real.log 3 :=
      Real.log_div (ne_of_gt hpi) (by norm_num)
    have hlog2pi : Real.log (2 * π) = Real.log 2 + Real.log π :=
      Real.log_mul (by norm_num) (ne_of_gt hpi)
    rw [hlogpi] at h1
    rw [hlog2pi] at h2
    have hlogfour : Real.log ((4 : ℝ) ^ n) = (n : ℝ) * (2 * Real.log 2) := by
      rw [hfour, Real.log_exp]
    constructor
    · -- `1/2 < z`
      have hexp : 1 / (2 * (π * 4 ^ n)) < Real.exp (-2 * u) := by
        rw [show (1 : ℝ) / (2 * (π * 4 ^ n)) = Real.exp (Real.log (1 / (2 * (π * 4 ^ n)))) from
          (Real.exp_log (by positivity)).symm]
        refine Real.exp_lt_exp.mpr ?_
        rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (by positivity) (by positivity), hlogfour, Real.log_one]
        linarith
      rw [hz]
      rw [div_lt_iff₀ (by positivity)] at hexp
      nlinarith [hexp]
    · have hexp : Real.exp (-2 * u) < 3 / (π * 4 ^ n) := by
        rw [show (3 : ℝ) / (π * 4 ^ n) = Real.exp (Real.log (3 / (π * 4 ^ n))) from
          (Real.exp_log (by positivity)).symm]
        refine Real.exp_lt_exp.mpr ?_
        rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by positivity)
          (by positivity), hlogfour]
        linarith
      rw [hz]
      rw [lt_div_iff₀ (by positivity)] at hexp
      nlinarith [hexp]

/-- **The negative collar has depth-independent width `½ log 6`.** -/
theorem burnolCollarWidth (n : ℕ) :
    ((n : ℝ) * Real.log 2 + 1 / 2 * Real.log (2 * π)) -
        ((n : ℝ) * Real.log 2 + 1 / 2 * Real.log (π / 3)) = 1 / 2 * Real.log 6 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul (by norm_num) (ne_of_gt hpi)
  have h2 : Real.log (π / 3) = Real.log π - Real.log 3 :=
    Real.log_div (ne_of_gt hpi) (by norm_num)
  have h3 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h1, h2, h3]
  ring

/-! ## The transverse Bockstein kernel -/

/-- The first transverse deformation of the polar factor, `κ̇ = ½(3A² - 2A)γ`. -/
def burnolBocksteinKernel (u : ℝ) : ℝ :=
  2 * burnolCollarZ 0 u * (3 * burnolCollarZ 0 u - 4) * burnolCollarGamma u

/-- **Explicit form of the Bockstein kernel.** -/
theorem burnolBocksteinKernel_apply (u : ℝ) :
    burnolBocksteinKernel u =
      2 * π * Real.exp (-2 * u) * (3 * π * Real.exp (-2 * u) - 4) * burnolCollarGamma u := by
  rw [burnolBocksteinKernel, burnolCollarZ_zero]
  ring

/-- **The Bockstein kernel is the halved combination `3A² - 2A` of the Gamma profile.** -/
theorem burnolBocksteinKernel_eq_steinCombination (u : ℝ) :
    burnolBocksteinKernel u =
      1 / 2 * (3 * burnolSteinA (fun v => burnolCollarH 0 v * (2 * burnolCollarZ 0 v)) u -
        2 * burnolSteinA (burnolCollarH 0) u) := by
  have hP : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 2 * x) (2 : ℝ) x := by
    intro x
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h2 := burnolSteinA_collarProfile 0 (P := fun x : ℝ => 2 * x) (Q := fun _ : ℝ => (2 : ℝ))
    hP u
  rw [h2, burnolSteinA_burnolCollarH, burnolBocksteinKernel, burnolCollarGamma]
  ring

/-- **The Bockstein kernel has exactly one sign change, at `½ log (3π/4)`.** -/
theorem burnolBocksteinKernel_pos_iff (u : ℝ) :
    0 < burnolBocksteinKernel u ↔ u < 1 / 2 * Real.log (3 * π / 4) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hz : 0 < burnolCollarZ 0 u := burnolCollarZ_pos 0 u
  have hg : 0 < burnolCollarGamma u := burnolCollarH_pos 0 u
  have hsign : 0 < burnolBocksteinKernel u ↔ 4 / 3 < burnolCollarZ 0 u := by
    rw [burnolBocksteinKernel]
    constructor
    · intro h
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * burnolCollarZ 0 u)
        (by linarith : (0 : ℝ) ≤ 4 - 3 * burnolCollarZ 0 u)) hg.le]
    · intro h
      have hfac : 0 < 3 * burnolCollarZ 0 u - 4 := by linarith
      positivity
  rw [hsign, burnolCollarZ_zero]
  constructor
  · intro h
    have hexp : 4 / (3 * π) < Real.exp (-2 * u) := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hlog := Real.log_lt_log (by positivity) hexp
    rw [Real.log_exp, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) (ne_of_gt hpi)] at hlog
    have hval : Real.log (3 * π / 4) = Real.log 3 + Real.log π - Real.log 4 := by
      rw [Real.log_div (by positivity) (by norm_num),
        Real.log_mul (by norm_num) (ne_of_gt hpi)]
    rw [hval]
    linarith
  · intro h
    have hval : Real.log (3 * π / 4) = Real.log 3 + Real.log π - Real.log 4 := by
      rw [Real.log_div (by positivity) (by norm_num),
        Real.log_mul (by norm_num) (ne_of_gt hpi)]
    rw [hval] at h
    have hexp : 4 / (3 * π) < Real.exp (-2 * u) := by
      rw [show (4 : ℝ) / (3 * π) = Real.exp (Real.log (4 / (3 * π))) from
        (Real.exp_log (by positivity)).symm]
      refine Real.exp_lt_exp.mpr ?_
      rw [Real.log_div (by norm_num) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt hpi)]
      linarith
    rw [div_lt_iff₀ (by positivity)] at hexp
    nlinarith

end RHTower
