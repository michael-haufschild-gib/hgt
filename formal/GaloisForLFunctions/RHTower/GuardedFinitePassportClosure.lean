import GaloisForLFunctions.RHTower.CoshPolynomialGlobalCertificate
import GaloisForLFunctions.RHTower.ImaginaryAxisPositiveRepair

/-!
# Guarded finite-passport approximants converge to the all-order periodic face

The polynomial multiplier

`1 + exp(-(N+1)^2) Q(z)^(N+1)`

is flat to order `N+1` on one real-even quartet, strictly positive on the imaginary axis, and
nonconstant.  Multiplying the periodic cosh quartet envelope by it gives an aperiodic, exact-order-one
guarded realizer at every finite depth.  The superexponential scalar makes these realizers converge
pointwise to the periodic envelope as the contact depth tends to infinity.

This is the formal core of the compact-open closure theorem in
`guarded-finite-passport-compact-open-closure.md`.  It identifies the finite-to-infinite wall as a
closure phenomenon: all elementary global guards survive at every finite depth, while exact
all-order partner equality occurs on the periodic boundary.
-/

open Complex Polynomial Filter Topology

namespace RHTower

noncomputable section

/-- The upper member `a + πi/2` of the selected real-even quartet. -/
def closureQuartetCenter (a : ℝ) : ℂ :=
  (a : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I

/-- The scaled Hermite-flat polynomial multiplier at contact order `M`. -/
def guardedClosurePolynomial (a : ℝ) (M : ℕ) (ε : ℝ) : Polynomial ℂ :=
  1 + C (ε : ℂ) * quartetFlatPolynomial (closureQuartetCenter a) ^ M

@[simp] theorem guardedClosurePolynomial_eval (a : ℝ) (M : ℕ) (ε : ℝ) (z : ℂ) :
    (guardedClosurePolynomial a M ε).eval z =
      1 + (ε : ℂ) * quartetFlatAtom (closureQuartetCenter a) z ^ M := by
  simp [guardedClosurePolynomial]

/-- Every closure multiplier is even. -/
theorem guardedClosurePolynomial_even (a : ℝ) (M : ℕ) (ε : ℝ) (z : ℂ) :
    (guardedClosurePolynomial a M ε).eval (-z) =
      (guardedClosurePolynomial a M ε).eval z := by
  have hq : quartetFlatAtom (closureQuartetCenter a) (-z) =
      quartetFlatAtom (closureQuartetCenter a) z := by
    unfold quartetFlatAtom
    ring
  rw [guardedClosurePolynomial_eval, guardedClosurePolynomial_eval, hq]

/-- Every closure multiplier is Schwarz-real. -/
theorem guardedClosurePolynomial_conj (a : ℝ) (M : ℕ) (ε : ℝ) (z : ℂ) :
    (guardedClosurePolynomial a M ε).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((guardedClosurePolynomial a M ε).eval z) := by
  have hq : quartetFlatAtom (closureQuartetCenter a) ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (quartetFlatAtom (closureQuartetCenter a) z) := by
    unfold quartetFlatAtom
    simp only [map_mul, map_sub, map_pow, starRingEnd_self_apply]
    ring
  rw [guardedClosurePolynomial_eval, guardedClosurePolynomial_eval, hq]
  simp

/-- A nonzero real displacement keeps the selected quartet polynomial away from zero on the
imaginary axis. -/
theorem closureQuartetCenter_axis_nondegenerate {a y : ℝ} (ha : a ≠ 0) :
    ((y : ℂ) ^ 2) + (closureQuartetCenter a) ^ 2 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp [closureQuartetCenter, pow_two, Complex.mul_im] at him
  have hapi : a * Real.pi = 0 := by nlinarith [him]
  exact ha ((mul_eq_zero.mp hapi).resolve_right (ne_of_gt Real.pi_pos))

/-- Positive scale makes the closure multiplier strictly positive real on the entire imaginary
axis. -/
theorem guardedClosurePolynomial_pos_imaginaryAxis {a ε : ℝ} (M : ℕ)
    (ha : a ≠ 0) (hε : 0 < ε) (y : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      (guardedClosurePolynomial a M ε).eval ((y : ℂ) * I) = (r : ℂ) := by
  obtain ⟨r, hr, hq⟩ := quartetFlatAtom_mul_I_pos_real
    (closureQuartetCenter_axis_nondegenerate (a := a) (y := y) ha)
  refine ⟨1 + ε * r ^ M, by positivity, ?_⟩
  rw [guardedClosurePolynomial_eval, hq]
  norm_cast

/-- The scaled multiplier has exact degree `4M`. -/
theorem guardedClosurePolynomial_natDegree {a ε : ℝ} {M : ℕ}
    (hε : ε ≠ 0) (hM : 0 < M) :
    (guardedClosurePolynomial a M ε).natDegree = 4 * M := by
  rw [guardedClosurePolynomial]
  have hεc : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hε
  have hterm : (C (ε : ℂ) * quartetFlatPolynomial (closureQuartetCenter a) ^ M).natDegree =
      4 * M := by
    rw [natDegree_C_mul hεc, natDegree_pow, quartetFlatPolynomial_natDegree]
    omega
  rw [natDegree_add_eq_right_of_natDegree_lt]
  · exact hterm
  · rw [hterm]
    simp [hM]

theorem guardedClosurePolynomial_degree_pos {a ε : ℝ} {M : ℕ}
    (hε : ε ≠ 0) (hM : 0 < M) :
    0 < (guardedClosurePolynomial a M ε).degree := by
  rw [← natDegree_pos_iff_degree_pos, guardedClosurePolynomial_natDegree hε hM]
  omega

/-- A Gaussian depth scale beats every fixed geometric growth factor. -/
theorem exp_neg_nat_sq_mul_pow_tendsto_zero {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) ^ 2)) * R ^ n) atTop (𝓝 0) := by
  let P : Polynomial ℝ := X ^ 2 - C (Real.log R) * X
  have hnatlt : (C (Real.log R) * X : Polynomial ℝ).natDegree <
      (X ^ 2 : Polynomial ℝ).natDegree := by
    calc
      (C (Real.log R) * X : Polynomial ℝ).natDegree ≤ X.natDegree :=
        natDegree_C_mul_le _ _
      _ < (X ^ 2 : Polynomial ℝ).natDegree := by simp
  have hdeg : 0 < P.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    rw [show P = X ^ 2 - C (Real.log R) * X by rfl,
      natDegree_sub_eq_left_of_natDegree_lt hnatlt]
    simp
  have hlead : 0 ≤ P.leadingCoeff := by
    rw [show P = X ^ 2 - C (Real.log R) * X by rfl,
      leadingCoeff_sub_of_degree_lt (degree_lt_degree hnatlt)]
    simp
  have htopR : Tendsto (fun x : ℝ => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead
  have htopN : Tendsto (fun n : ℕ => P.eval (n : ℝ)) atTop atTop :=
    htopR.comp tendsto_natCast_atTop_atTop
  have hbot : Tendsto (fun n : ℕ => -(P.eval (n : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp htopN
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(P.eval (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hbot
  convert hexp using 1
  funext n
  rw [← Real.exp_log hR, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp [P]
  ring

theorem exp_neg_nat_sq_mul_pow_tendsto_zero_of_nonneg {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) ^ 2)) * R ^ n) atTop (𝓝 0) := by
  rcases hR.eq_or_lt with rfl | hpos
  · refine (tendsto_congr' (show ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n : ℝ) ^ 2)) * 0 ^ n = 0 by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simp [Nat.ne_of_gt hn])).mpr ?_
    exact tendsto_const_nhds
  · exact exp_neg_nat_sq_mul_pow_tendsto_zero hpos

/-- Superexponential scale used to pass from finite-depth realizers to the periodic boundary. -/
def guardedClosureScale (N : ℕ) : ℝ :=
  Real.exp (-(((N + 1 : ℕ) : ℝ) ^ 2))

/-- The guarded aperiodic realizer at contact depth `N`. -/
def guardedClosureApproximant (a : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  polynomialXiEnvelope a
    (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)) z

/-- At every fixed point, the guarded finite-depth realizers converge to the periodic all-order
envelope. -/
theorem guardedClosureApproximant_tendsto (a : ℝ) (z : ℂ) :
    Tendsto (fun N => guardedClosureApproximant a N z) atTop
      (𝓝 (coshQuartetEnvelope a z)) := by
  let q : ℂ := quartetFlatAtom (closureQuartetCenter a) z
  have hnorm : Tendsto
      (fun N : ℕ => ‖((guardedClosureScale N : ℝ) : ℂ) * q ^ (N + 1)‖) atTop (𝓝 0) := by
    rw [show (fun N : ℕ => ‖((guardedClosureScale N : ℝ) : ℂ) * q ^ (N + 1)‖) =
        fun N : ℕ => Real.exp (-((((N + 1 : ℕ) : ℝ)) ^ 2)) * ‖q‖ ^ (N + 1) by
      funext N
      rw [norm_mul, norm_pow]
      rw [Complex.norm_real, Real.norm_eq_abs, guardedClosureScale,
        abs_of_pos (Real.exp_pos _)]]
    exact (exp_neg_nat_sq_mul_pow_tendsto_zero_of_nonneg (norm_nonneg q)).comp
      (tendsto_add_atTop_nat 1)
  have hcorr : Tendsto
      (fun N : ℕ => ((guardedClosureScale N : ℝ) : ℂ) * q ^ (N + 1)) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hone : Tendsto
      (fun N : ℕ => 1 + ((guardedClosureScale N : ℝ) : ℂ) * q ^ (N + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hcorr
  have hmul : Tendsto
      (fun N : ℕ => coshQuartetEnvelope a z *
        (1 + ((guardedClosureScale N : ℝ) : ℂ) * q ^ (N + 1))) atTop
        (𝓝 (coshQuartetEnvelope a z * 1)) := tendsto_const_nhds.mul hone
  simpa [guardedClosureApproximant, polynomialXiEnvelope, guardedClosurePolynomial_eval, q] using hmul

/-- Every finite-depth approximant retains the complete elementary guard stack: entire, real-even,
Schwarz-real, positive on the imaginary axis, aperiodic, and of exact order one. -/
theorem guardedClosureApproximant_global_certificate (a : ℝ) (ha : a ≠ 0) (N : ℕ) :
    (∀ z, AnalyticAt ℂ (guardedClosureApproximant a N) z) ∧
    (∀ z, guardedClosureApproximant a N (-z) = guardedClosureApproximant a N z) ∧
    (∀ z, guardedClosureApproximant a N ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (guardedClosureApproximant a N z)) ∧
    (∀ y : ℝ, ∃ r : ℝ, 0 < r ∧
      guardedClosureApproximant a N ((y : ℂ) * I) = (r : ℂ)) ∧
    (∀ h, Function.Periodic (guardedClosureApproximant a N) h ↔ h = 0) ∧
    ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ z : ℂ, ‖guardedClosureApproximant a N z‖ ≤
        Kupper * (1 + ‖z‖) ^
          (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).natDegree *
            Real.exp (2 * ‖z‖)) ∧
      ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤
        ‖guardedClosureApproximant a N (x : ℂ)‖ := by
  have hscale : 0 < guardedClosureScale N := Real.exp_pos _
  simpa only [guardedClosureApproximant] using
    polynomialXiEnvelope_global_certificate a ha
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N))
      (guardedClosurePolynomial_degree_pos hscale.ne' (Nat.succ_pos N))
      (guardedClosurePolynomial_even a (N + 1) (guardedClosureScale N))
      (guardedClosurePolynomial_conj a (N + 1) (guardedClosureScale N))
      (guardedClosurePolynomial_pos_imaginaryAxis (N + 1) ha hscale)

end

end RHTower
