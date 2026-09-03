import GaloisForLFunctions.RHTower.SoninSemilocalAllEvenJacobiResidue
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiPolynomials
import GaloisForLFunctions.HTGeometry.PRecursiveDFinite

/-!
# The Meixner–Pollaczek generating function of the archimedean semilocal Jacobi polynomials

The corpus's orthonormal archimedean Jacobi polynomials `p_n` (recursively defined through the radii
`r_n = √((n+½)(n+1))`) are Meixner–Pollaczek polynomials with `λ = 1/4`, `φ = π/2`, `x = s/2`, up to
the normalization `c_n = √((2n)!)/(2^n n!)`:

`Σ_n c_n p_n(s) w^n = (1 − iw)^{−1/4 + is/2} (1 + iw)^{−1/4 − is/2}`   for `|w| < 1`,

and for real `w ∈ (−1, 1)` the right-hand side is `(1 + w²)^{−1/4} exp(s · arctan w)`.

Proof: the right-hand side `G` is holomorphic on the unit disc and satisfies the first-order equation
`(1 + w²) G′ = (s − w/2) G`; differentiating it `n + 1` times at `0` (only the coordinate Leibniz
rule is needed) gives the three-term recurrence `D_{n+2} = s D_{n+1} − (n+1)(n+½) D_n` for the
derivatives `D_n = G^{(n)}(0)`, which is the recurrence of `n! c_n p_n(s)` by the corpus identities
`(n+1) c_{n+1} = r_n c_n` and `c_{n+1} r_n = (n+½) c_n`.  Cauchy's Taylor theorem on the disc then
gives the `HasSum`.
-/

open Complex Filter
open scoped Topology

namespace RHTower

namespace MeixnerPollaczek

open GaloisForLFunctions.HTGeometry

/-- Meixner–Pollaczek exponent `−1/4 + is/2`. -/
noncomputable def mpExponentPlus (s : ℝ) : ℂ := -(1 / 4 : ℂ) + (s : ℂ) * I / 2

/-- Meixner–Pollaczek exponent `−1/4 − is/2`. -/
noncomputable def mpExponentMinus (s : ℝ) : ℂ := -(1 / 4 : ℂ) - (s : ℂ) * I / 2

/-- The generating function `(1 − iw)^{−1/4 + is/2} (1 + iw)^{−1/4 − is/2}`. -/
noncomputable def mpGeneratingFunction (s : ℝ) (w : ℂ) : ℂ :=
  (1 - I * w) ^ mpExponentPlus s * (1 + I * w) ^ mpExponentMinus s

/-- The normalized coefficient sequence `c_n p_n(s)`. -/
noncomputable def mpCoefficient (s : ℝ) (n : ℕ) : ℝ :=
  semilocalArchimedeanJacobiNormalization n *
    (semilocalArchimedeanJacobiPolynomial n).eval s

/-! ## The bases avoid the branch cut on the unit disc -/

theorem mp_re_one_sub_I_mul (w : ℂ) : (1 - I * w).re = 1 + w.im := by
  simp [Complex.sub_re, Complex.mul_re]

theorem mp_re_one_add_I_mul (w : ℂ) : (1 + I * w).re = 1 - w.im := by
  simp [Complex.add_re, Complex.mul_re, sub_eq_add_neg]

theorem one_sub_I_mul_mem_slitPlane {w : ℂ} (hw : ‖w‖ < 1) : 1 - I * w ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  rw [mp_re_one_sub_I_mul]
  have h := abs_im_le_norm w
  have := (abs_lt.mp (h.trans_lt hw)).1
  linarith

theorem one_add_I_mul_mem_slitPlane {w : ℂ} (hw : ‖w‖ < 1) : 1 + I * w ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  rw [mp_re_one_add_I_mul]
  have h := abs_im_le_norm w
  have := (abs_lt.mp (h.trans_lt hw)).2
  linarith

theorem mp_one_add_sq_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) + w ^ 2 ≠ 0 := by
  have h1 := slitPlane_ne_zero (one_sub_I_mul_mem_slitPlane hw)
  have h2 := slitPlane_ne_zero (one_add_I_mul_mem_slitPlane hw)
  have : (1 : ℂ) + w ^ 2 = (1 - I * w) * (1 + I * w) := by
    linear_combination (w ^ 2) * I_sq
  rw [this]
  exact mul_ne_zero h1 h2

/-! ## The first-order differential equation -/

/-- The logarithmic derivative of the generating function. -/
theorem mpExponent_identity (s : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    -I * mpExponentPlus s / (1 - I * w) + I * mpExponentMinus s / (1 + I * w) =
      ((s : ℂ) - w / 2) / (1 + w ^ 2) := by
  have hA0 := slitPlane_ne_zero (one_sub_I_mul_mem_slitPlane hw)
  have hB0 := slitPlane_ne_zero (one_add_I_mul_mem_slitPlane hw)
  have hq := mp_one_add_sq_ne_zero hw
  rw [div_add_div _ _ hA0 hB0, div_eq_div_iff (mul_ne_zero hA0 hB0) hq]
  unfold mpExponentPlus mpExponentMinus
  linear_combination (-((s : ℂ) - w / 2)) * I_sq

theorem hasDerivAt_mpGeneratingFunction (s : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (mpGeneratingFunction s)
      (mpGeneratingFunction s w * ((s : ℂ) - w / 2) / (1 + w ^ 2)) w := by
  have hA : HasDerivAt (fun z : ℂ => 1 - I * z) (-I) w := by
    simpa using ((hasDerivAt_id w).const_mul I).const_sub 1
  have hB : HasDerivAt (fun z : ℂ => 1 + I * z) I w := by
    simpa using ((hasDerivAt_id w).const_mul I).const_add 1
  have hsA := one_sub_I_mul_mem_slitPlane hw
  have hsB := one_add_I_mul_mem_slitPlane hw
  have hA' := hA.cpow_const (c := mpExponentPlus s) hsA
  have hB' := hB.cpow_const (c := mpExponentMinus s) hsB
  have h := hA'.mul hB'
  refine h.congr_deriv ?_
  have hA0 := slitPlane_ne_zero hsA
  have hB0 := slitPlane_ne_zero hsB
  rw [cpow_sub _ _ hA0, cpow_sub _ _ hB0, cpow_one, cpow_one, mul_div_assoc,
    ← mpExponent_identity s hw]
  unfold mpGeneratingFunction
  field_simp

theorem differentiableOn_mpGeneratingFunction (s : ℝ) :
    DifferentiableOn ℂ (mpGeneratingFunction s) (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa using hw
  exact (hasDerivAt_mpGeneratingFunction s hw').differentiableAt.differentiableWithinAt

theorem deriv_mpGeneratingFunction (s : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    deriv (mpGeneratingFunction s) w =
      mpGeneratingFunction s w * ((s : ℂ) - w / 2) / (1 + w ^ 2) :=
  (hasDerivAt_mpGeneratingFunction s hw).deriv

/-- The differential equation `(1 + w²) G′ = (s − w/2) G` on the unit disc. -/
theorem mpGeneratingFunction_ode (s : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    (1 + w ^ 2) * deriv (mpGeneratingFunction s) w =
      ((s : ℂ) - w / 2) * mpGeneratingFunction s w := by
  rw [deriv_mpGeneratingFunction s hw]
  have hq := mp_one_add_sq_ne_zero hw
  field_simp

/-! ## Smoothness at the origin -/

theorem contDiffAt_mpGeneratingFunction (s : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (mpGeneratingFunction s) 0 :=
  ((differentiableOn_mpGeneratingFunction s).contDiffOn Metric.isOpen_ball).contDiffAt
    (Metric.ball_mem_nhds _ one_pos)

theorem contDiffAt_deriv_mpGeneratingFunction (s : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (deriv (mpGeneratingFunction s)) 0 :=
  (((differentiableOn_mpGeneratingFunction s).deriv Metric.isOpen_ball).contDiffOn
    Metric.isOpen_ball).contDiffAt (Metric.ball_mem_nhds _ one_pos)

/-- Two coordinate factors: `∂^{n+1}[w (w h)](0) = (n+1) n ∂^{n-1} h (0)`. -/
theorem iteratedDeriv_id_mul_id_mul_zero (h : ℂ → ℂ)
    (hh : ∀ m : WithTop ℕ∞, ContDiffAt ℂ m h 0) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z => z * (z * h z)) 0 =
      ((n : ℂ) + 1) * n * iteratedDeriv (n - 1) h 0 := by
  have hzh : ∀ m : WithTop ℕ∞, ContDiffAt ℂ m (fun z => z * h z) 0 := fun m =>
    contDiffAt_id.mul (hh m)
  rw [iteratedDeriv_id_mul_zero_succ_of_contDiffAt (fun z => z * h z) n (hzh _)]
  cases n with
  | zero => simp
  | succ m =>
      rw [iteratedDeriv_id_mul_zero_succ_of_contDiffAt h m (hh _)]
      try simp only [Nat.add_sub_cancel]
      try push_cast
      try ring

/-! ## The derivative recurrence at the origin -/

/-- `D_n = G^{(n)}(0)`. -/
noncomputable def mpDerivative (s : ℝ) (n : ℕ) : ℂ :=
  iteratedDeriv n (mpGeneratingFunction s) 0

theorem mpDerivative_zero (s : ℝ) : mpDerivative s 0 = 1 := by
  unfold mpDerivative
  rw [iteratedDeriv_zero]
  simp [mpGeneratingFunction]

theorem mpDerivative_one (s : ℝ) : mpDerivative s 1 = s := by
  unfold mpDerivative
  rw [iteratedDeriv_one, deriv_mpGeneratingFunction s (by simp)]
  simp [mpGeneratingFunction]

theorem iteratedDeriv_deriv_mpGeneratingFunction (s : ℝ) (n : ℕ) :
    iteratedDeriv n (deriv (mpGeneratingFunction s)) 0 = mpDerivative s (n + 1) := by
  unfold mpDerivative
  rw [iteratedDeriv_succ']

/-- **Three-term recurrence of the Taylor derivatives:**
`D_{n+2} = s D_{n+1} − (n+1)(n+½) D_n`. -/
theorem mpDerivative_recurrence (s : ℝ) (n : ℕ) :
    mpDerivative s (n + 2) =
      (s : ℂ) * mpDerivative s (n + 1) -
        ((n : ℂ) + 1) * ((n : ℂ) + 1 / 2) * mpDerivative s n := by
  set G := mpGeneratingFunction s with hG
  -- the two sides of the ODE as global functions
  set L : ℂ → ℂ := fun w => deriv G w + w * (w * deriv G w) with hL
  set R : ℂ → ℂ := fun w => (s : ℂ) * G w - (1 / 2 : ℂ) * (w * G w) with hR
  have hLR : L =ᶠ[𝓝 (0 : ℂ)] R := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    have := mpGeneratingFunction_ode s hw'
    simp only [hL, hR]
    linear_combination this
  have hcG : ∀ m : WithTop ℕ∞, ContDiffAt ℂ m G 0 := contDiffAt_mpGeneratingFunction s
  have hcG' : ∀ m : WithTop ℕ∞, ContDiffAt ℂ m (deriv G) 0 :=
    contDiffAt_deriv_mpGeneratingFunction s
  have hkey := hLR.iteratedDeriv_eq (n + 1)
  -- left side
  have hleft : iteratedDeriv (n + 1) L 0 =
      mpDerivative s (n + 2) + ((n : ℂ) + 1) * n * mpDerivative s n := by
    have hsplit : L = deriv G + fun w => w * (w * deriv G w) := by
      funext w; simp [hL]
    have hc2 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => w * (w * deriv G w)) 0 :=
      contDiffAt_id.mul (contDiffAt_id.mul (hcG' _))
    rw [hsplit, iteratedDeriv_add (hcG' _) hc2,
      iteratedDeriv_deriv_mpGeneratingFunction, iteratedDeriv_id_mul_id_mul_zero _ hcG']
    cases n with
    | zero => simp
    | succ m =>
        rw [iteratedDeriv_deriv_mpGeneratingFunction]
        try simp only [Nat.add_sub_cancel]
        try push_cast
        try ring
  -- right side
  have hright : iteratedDeriv (n + 1) R 0 =
      (s : ℂ) * mpDerivative s (n + 1) - (1 / 2 : ℂ) * (((n : ℂ) + 1) * mpDerivative s n) := by
    have hsplit : R = (fun w => (s : ℂ) * G w) + fun w => -(1 / 2 : ℂ) * (w * G w) := by
      funext w; simp [hR]; ring
    have hc1 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => (s : ℂ) * G w) 0 :=
      contDiffAt_const.mul (hcG _)
    have hc3 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => w * G w) 0 :=
      contDiffAt_id.mul (hcG _)
    have hc2 : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => -(1 / 2 : ℂ) * (w * G w)) 0 :=
      contDiffAt_const.mul hc3
    rw [hsplit, iteratedDeriv_add hc1 hc2, iteratedDeriv_const_mul _ (hcG _),
      iteratedDeriv_const_mul _ hc3, iteratedDeriv_id_mul_zero_succ_of_contDiffAt G n (hcG _)]
    unfold mpDerivative
    push_cast
    ring
  rw [hleft, hright] at hkey
  linear_combination hkey

/-! ## Identification with `n! c_n p_n(s)` -/

theorem mpCoefficient_zero (s : ℝ) : mpCoefficient s 0 = 1 := by
  simp [mpCoefficient, semilocalArchimedeanJacobiNormalization]

theorem mpCoefficient_one (s : ℝ) : mpCoefficient s 1 = s := by
  unfold mpCoefficient
  have h := semilocalArchimedeanJacobi_succ_mul_normalization 0
  have h0 : semilocalArchimedeanJacobiNormalization 0 = 1 := by
    simp [semilocalArchimedeanJacobiNormalization]
  rw [h0] at h
  have hr := (semilocalArchimedeanJacobiCoefficient_pos 0).ne'
  rw [semilocalArchimedeanJacobiPolynomial_eval_one]
  simp at h
  rw [h]
  field_simp

/-- **Three-term recurrence of `c_n p_n(s)`:** `(n+2) b_{n+2} = s b_{n+1} − (n+½) b_n`. -/
theorem mpCoefficient_recurrence (s : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * mpCoefficient s (n + 2) =
      s * mpCoefficient s (n + 1) - ((n : ℝ) + 1 / 2) * mpCoefficient s n := by
  unfold mpCoefficient
  have hrec := semilocalArchimedeanJacobiPolynomial_eval_recurrence n s
  have h1 := semilocalArchimedeanJacobi_succ_mul_normalization (n + 1)
  have h2 := semilocalArchimedeanJacobiNormalization_succ_mul_coefficient n
  push_cast at h1
  -- (n+2) c_{n+2} p_{n+2} = c_{n+1} r_{n+1} p_{n+2} = c_{n+1} (s p_{n+1} − r_n p_n)
  have hstep : ((n : ℝ) + 2) * (semilocalArchimedeanJacobiNormalization (n + 2) *
      (semilocalArchimedeanJacobiPolynomial (n + 2)).eval s) =
      semilocalArchimedeanJacobiNormalization (n + 1) *
        (semilocalArchimedeanJacobiCoefficient (n + 1) *
          (semilocalArchimedeanJacobiPolynomial (n + 2)).eval s) := by
    rw [← mul_assoc, show ((n : ℝ) + 2) = ((n : ℝ) + 1 + 1) by ring, h1]; ring
  rw [hstep]
  linear_combination (-(semilocalArchimedeanJacobiNormalization (n + 1))) * hrec +
    (-(semilocalArchimedeanJacobiPolynomial n).eval s) * h2

theorem mpDerivative_eq_factorial_mul_coefficient_pair (s : ℝ) (n : ℕ) :
    mpDerivative s n = (n.factorial : ℂ) * (mpCoefficient s n : ℂ) ∧
      mpDerivative s (n + 1) = ((n + 1).factorial : ℂ) * (mpCoefficient s (n + 1) : ℂ) := by
  induction n with
  | zero =>
      exact ⟨by simp [mpDerivative_zero, mpCoefficient_zero],
        by simp [mpDerivative_one, mpCoefficient_one]⟩
  | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hfac : ((n + 1 + 1).factorial : ℂ) =
          ((n : ℂ) + 2) * ((n : ℂ) + 1) * (n.factorial : ℂ) := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
      have hfac1 : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hrec := mpCoefficient_recurrence s n
      have hrecC : ((n : ℂ) + 2) * (mpCoefficient s (n + 2) : ℂ) =
          (s : ℂ) * (mpCoefficient s (n + 1) : ℂ) -
            ((n : ℂ) + 1 / 2) * (mpCoefficient s n : ℂ) := by
        have h := congrArg (fun x : ℝ => (x : ℂ)) hrec
        push_cast at h
        linear_combination h
      change mpDerivative s (n + 2) = ((n + 1 + 1).factorial : ℂ) * (mpCoefficient s (n + 2) : ℂ)
      rw [mpDerivative_recurrence, ih.2, ih.1, hfac, hfac1]
      linear_combination (-((n : ℂ) + 1) * (n.factorial : ℂ)) * hrecC

/-- `G^{(n)}(0) = n! c_n p_n(s)`. -/
theorem mpDerivative_eq_factorial_mul_coefficient (s : ℝ) (n : ℕ) :
    mpDerivative s n = (n.factorial : ℂ) * (mpCoefficient s n : ℂ) :=
  (mpDerivative_eq_factorial_mul_coefficient_pair s n).1

/-! ## The generating function -/

/-- **Meixner–Pollaczek generating function of the archimedean semilocal Jacobi polynomials.**
For `‖w‖ < 1`,
`Σ_n c_n p_n(s) w^n = (1 − iw)^{−1/4 + is/2} (1 + iw)^{−1/4 − is/2}`. -/
theorem hasSum_mpGeneratingFunction (s : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => (mpCoefficient s n : ℂ) * w ^ n) (mpGeneratingFunction s w) := by
  have hmem : w ∈ Metric.ball (0 : ℂ) 1 := by simpa using hw
  have h := Complex.hasSum_taylorSeries_on_ball (differentiableOn_mpGeneratingFunction s) hmem
  refine h.congr_fun fun n => ?_
  rw [sub_zero, smul_eq_mul, smul_eq_mul]
  change (mpCoefficient s n : ℂ) * w ^ n = _ * (w ^ n * mpDerivative s n)
  rw [mpDerivative_eq_factorial_mul_coefficient]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

theorem hasSum_normalization_mul_eval (s : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => ((semilocalArchimedeanJacobiNormalization n *
        (semilocalArchimedeanJacobiPolynomial n).eval s : ℝ) : ℂ) * w ^ n)
      (mpGeneratingFunction s w) :=
  hasSum_mpGeneratingFunction s hw

/-! ## The real form `(1 + w²)^{−1/4} exp(s arctan w)` -/

theorem arg_one_sub_I_mul_ofReal (w : ℝ) : (1 - I * (w : ℂ)).arg = -Real.arctan w := by
  have hre : (1 - I * (w : ℂ)).re = 1 := by simp
  have him : (1 - I * (w : ℂ)).im = -w := by simp
  have hlt : |(1 - I * (w : ℂ)).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact one_pos))
  have htan := Complex.tan_arg (1 - I * (w : ℂ))
  rw [hre, him, div_one] at htan
  rw [← Real.arctan_neg]
  conv_rhs => rw [← htan]
  exact (Real.arctan_tan (abs_lt.mp hlt).1 (abs_lt.mp hlt).2).symm

theorem arg_one_add_I_mul_ofReal (w : ℝ) : (1 + I * (w : ℂ)).arg = Real.arctan w := by
  have hre : (1 + I * (w : ℂ)).re = 1 := by simp
  have him : (1 + I * (w : ℂ)).im = w := by simp
  have hlt : |(1 + I * (w : ℂ)).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact one_pos))
  have htan := Complex.tan_arg (1 + I * (w : ℂ))
  rw [hre, him, div_one] at htan
  conv_rhs => rw [← htan]
  exact (Real.arctan_tan (abs_lt.mp hlt).1 (abs_lt.mp hlt).2).symm

theorem norm_one_sub_I_mul_ofReal (w : ℝ) : ‖(1 - I * (w : ℂ))‖ = Real.sqrt (1 + w ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp

theorem norm_one_add_I_mul_ofReal (w : ℝ) : ‖(1 + I * (w : ℂ))‖ = Real.sqrt (1 + w ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp

theorem log_one_sub_I_mul_ofReal (w : ℝ) :
    Complex.log (1 - I * (w : ℂ)) =
      ((Real.log (1 + w ^ 2) / 2 : ℝ) : ℂ) - ((Real.arctan w : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_one_sub_I_mul_ofReal, -Complex.ofReal_arctan,
      Real.log_sqrt (by positivity : (0:ℝ) ≤ 1 + w ^ 2)]
  · simp [Complex.log_im, arg_one_sub_I_mul_ofReal, -Complex.ofReal_arctan]

theorem log_one_add_I_mul_ofReal (w : ℝ) :
    Complex.log (1 + I * (w : ℂ)) =
      ((Real.log (1 + w ^ 2) / 2 : ℝ) : ℂ) + ((Real.arctan w : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_one_add_I_mul_ofReal, -Complex.ofReal_arctan,
      Real.log_sqrt (by positivity : (0:ℝ) ≤ 1 + w ^ 2)]
  · simp [Complex.log_im, arg_one_add_I_mul_ofReal, -Complex.ofReal_arctan]

/-- **Real form of the generating function:** for real `w`,
`(1 − iw)^{−1/4 + is/2} (1 + iw)^{−1/4 − is/2} = (1 + w²)^{−1/4} exp(s · arctan w)`. -/
theorem mpGeneratingFunction_ofReal (s w : ℝ) :
    mpGeneratingFunction s w =
      (((1 + w ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (s * Real.arctan w) : ℝ) : ℂ) := by
  have hA : (1 - I * (w : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hB : (1 + I * (w : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hexp : Complex.log (1 - I * (w : ℂ)) * mpExponentPlus s +
      Complex.log (1 + I * (w : ℂ)) * mpExponentMinus s =
      ((-(1 / 4 : ℝ) * Real.log (1 + w ^ 2) + s * Real.arctan w : ℝ) : ℂ) := by
    rw [log_one_sub_I_mul_ofReal, log_one_add_I_mul_ofReal]
    unfold mpExponentPlus mpExponentMinus
    push_cast
    try simp only [Complex.ofReal_arctan]
    linear_combination (-(s : ℂ) * Complex.arctan (w : ℂ)) * I_sq
  unfold mpGeneratingFunction
  rw [cpow_def_of_ne_zero hA, cpow_def_of_ne_zero hB, ← Complex.exp_add, hexp,
    ← Complex.ofReal_exp]
  congr 1
  rw [Real.exp_add, Real.rpow_def_of_pos (by positivity)]
  ring_nf

/-- The real generating function: for `|w| < 1`,
`Σ_n c_n p_n(s) w^n = (1 + w²)^{−1/4} exp(s · arctan w)`. -/
theorem hasSum_mpGeneratingFunction_real (s w : ℝ) (hw : |w| < 1) :
    HasSum (fun n : ℕ => mpCoefficient s n * w ^ n)
      ((1 + w ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (s * Real.arctan w)) := by
  have hw' : ‖(w : ℂ)‖ < 1 := by simpa using hw
  have h := hasSum_mpGeneratingFunction s hw'
  rw [mpGeneratingFunction_ofReal] at h
  have h' := Complex.hasSum_re h
  rw [Complex.ofReal_re] at h'
  refine h'.congr_fun fun n => ?_
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

end MeixnerPollaczek

end RHTower
