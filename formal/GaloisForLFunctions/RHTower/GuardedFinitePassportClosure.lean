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
  (a : ℂ) + (Real.pi : ℂ) / 2 * I

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

/-! ## Finite completed-flux contact at the two period-partner centers -/

/-- The lower member `-a - πi/2` of the selected quartet. -/
def closureLowerCenter (a : ℝ) : ℂ :=
  -closureQuartetCenter a

/-- Its vertical period partner `-a + πi/2`. -/
def closureUpperPartnerCenter (a : ℝ) : ℂ :=
  -(starRingEnd ℂ) (closureQuartetCenter a)

theorem closureUpperPartnerCenter_eq_shift (a : ℝ) :
    closureUpperPartnerCenter a = closureLowerCenter a + (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [closureUpperPartnerCenter, closureLowerCenter, closureQuartetCenter,
      map_div₀, map_ofNat, Complex.mul_re]
  · simp [closureUpperPartnerCenter, closureLowerCenter, closureQuartetCenter,
      map_div₀, map_ofNat, Complex.mul_im]
    ring

/-- Changing the quartet parameter by sign does not change its real-even atom. -/
theorem quartetFlatAtom_neg_parameter (α z : ℂ) :
    quartetFlatAtom (-α) z = quartetFlatAtom α z := by
  unfold quartetFlatAtom
  simp only [map_neg, neg_sq]

/-- Changing the quartet parameter by conjugation does not change its Schwarz-paired atom. -/
theorem quartetFlatAtom_conj_parameter (α z : ℂ) :
    quartetFlatAtom ((starRingEnd ℂ) α) z = quartetFlatAtom α z := by
  change (z ^ 2 - (star α) ^ 2) * (z ^ 2 - (star (star α)) ^ 2) =
    (z ^ 2 - α ^ 2) * (z ^ 2 - (star α) ^ 2)
  rw [star_star]
  ring

theorem quartetFlatAtom_closureLowerCenter (a : ℝ) (z : ℂ) :
    quartetFlatAtom (closureQuartetCenter a) z = quartetFlatAtom (closureLowerCenter a) z := by
  rw [closureLowerCenter, quartetFlatAtom_neg_parameter]

theorem quartetFlatAtom_closureUpperPartnerCenter (a : ℝ) (z : ℂ) :
    quartetFlatAtom (closureQuartetCenter a) z =
      quartetFlatAtom (closureUpperPartnerCenter a) z := by
  rw [closureUpperPartnerCenter, quartetFlatAtom_neg_parameter,
    quartetFlatAtom_conj_parameter]

/-- The analytic unit left after extracting the prescribed power at a selected quartet center. -/
def guardedClosureLocalUnit (ε : ℝ) (M : ℕ) (c x : ℂ) : ℂ :=
  (ε : ℂ) * quartetFlatAtomUnit c x ^ M

theorem guardedClosureLocalUnit_analyticAt_zero (ε : ℝ) (M : ℕ) (c : ℂ) :
    AnalyticAt ℂ (guardedClosureLocalUnit ε M c) 0 := by
  unfold guardedClosureLocalUnit quartetFlatAtomUnit
  fun_prop

/-- At the lower center, the polynomial multiplier is exactly a Hermite-flat factor. -/
theorem guardedClosurePolynomial_shift_lower (a ε : ℝ) (M : ℕ) (x : ℂ) :
    (guardedClosurePolynomial a M ε).eval (closureLowerCenter a + x) =
      hermiteFlatFactor M (guardedClosureLocalUnit ε M (closureLowerCenter a)) x := by
  rw [guardedClosurePolynomial_eval, quartetFlatAtom_closureLowerCenter,
    quartetFlatAtom_shift]
  simp only [hermiteFlatFactor, guardedClosureLocalUnit]
  ring

/-- At the vertical partner, the same polynomial multiplier is independently Hermite-flat to the
same order. -/
theorem guardedClosurePolynomial_shift_upperPartner (a ε : ℝ) (M : ℕ) (x : ℂ) :
    (guardedClosurePolynomial a M ε).eval (closureUpperPartnerCenter a + x) =
      hermiteFlatFactor M (guardedClosureLocalUnit ε M (closureUpperPartnerCenter a)) x := by
  rw [guardedClosurePolynomial_eval, quartetFlatAtom_closureUpperPartnerCenter,
    quartetFlatAtom_shift]
  simp only [hermiteFlatFactor, guardedClosureLocalUnit]
  ring

theorem closureQuartetCenter_self_factor_ne {a : ℝ} (ha : a ≠ 0) :
    (2 * closureQuartetCenter a) *
      ((closureQuartetCenter a) ^ 2 -
        ((starRingEnd ℂ) (closureQuartetCenter a)) ^ 2) ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have hre := congrArg Complex.re h
    simp [closureQuartetCenter] at hre
    exact ha hre
  · intro h
    have him := congrArg Complex.im h
    have hstar : (starRingEnd ℂ) (closureQuartetCenter a) =
        (a : ℂ) - (Real.pi : ℂ) / 2 * I := by
      apply Complex.ext <;>
        simp [closureQuartetCenter, map_div₀, map_ofNat, Complex.mul_re, Complex.mul_im]
    rw [hstar] at him
    simp [closureQuartetCenter, pow_two, Complex.mul_im] at him
    have hapi : a * Real.pi = 0 := by linarith
    exact ha ((mul_eq_zero.mp hapi).resolve_right (ne_of_gt Real.pi_pos))

theorem closureLowerCenter_self_factor_ne {a : ℝ} (ha : a ≠ 0) :
    (2 * closureLowerCenter a) *
      ((closureLowerCenter a) ^ 2 -
        ((starRingEnd ℂ) (closureLowerCenter a)) ^ 2) ≠ 0 := by
  simpa [closureLowerCenter] using closureQuartetCenter_self_factor_ne ha

theorem closureUpperPartnerCenter_self_factor_ne {a : ℝ} (ha : a ≠ 0) :
    (2 * closureUpperPartnerCenter a) *
      ((closureUpperPartnerCenter a) ^ 2 -
        ((starRingEnd ℂ) (closureUpperPartnerCenter a)) ^ 2) ≠ 0 := by
  have hbase := closureLowerCenter_self_factor_ne ha
  have hcenter : closureUpperPartnerCenter a =
      (starRingEnd ℂ) (closureLowerCenter a) := by
    simp [closureUpperPartnerCenter, closureLowerCenter]
  rw [hcenter]
  intro hzero
  apply hbase
  have hstar := congrArg (starRingEnd ℂ) hzero
  simpa only [map_mul, map_ofNat, map_sub, map_pow, map_zero,
    starRingEnd_self_apply] using hstar

theorem guardedClosureLocalUnit_zero_ne {ε : ℝ} {M : ℕ} {c : ℂ}
    (hε : ε ≠ 0)
    (hc : (2 * c) * (c ^ 2 - ((starRingEnd ℂ) c) ^ 2) ≠ 0) :
    guardedClosureLocalUnit ε M c 0 ≠ 0 := by
  rw [guardedClosureLocalUnit]
  apply mul_ne_zero (ofReal_ne_zero.mpr hε)
  simpa [quartetFlatAtomUnit] using pow_ne_zero M hc

/-- Every correction coefficient below the selected contact order vanishes at the lower center. -/
theorem guardedClosure_lower_fluxCorrection_iteratedDeriv_zero
    {a ε : ℝ} {M n : ℕ} (ha : a ≠ 0) (hε : ε ≠ 0) (hM : 0 < M) (hn : n < M) :
    iteratedDeriv n
      (hermiteFlatFluxCorrection M
        (guardedClosureLocalUnit ε M (closureLowerCenter a))) 0 = 0 := by
  exact hermiteFlatFluxCorrection_iteratedDeriv_zero hM
    (guardedClosureLocalUnit_analyticAt_zero ε M (closureLowerCenter a))
    (guardedClosureLocalUnit_zero_ne hε (closureLowerCenter_self_factor_ne ha)) hn

/-- Every correction coefficient below the selected contact order vanishes at the vertical
partner center. -/
theorem guardedClosure_upperPartner_fluxCorrection_iteratedDeriv_zero
    {a ε : ℝ} {M n : ℕ} (ha : a ≠ 0) (hε : ε ≠ 0) (hM : 0 < M) (hn : n < M) :
    iteratedDeriv n
      (hermiteFlatFluxCorrection M
        (guardedClosureLocalUnit ε M (closureUpperPartnerCenter a))) 0 = 0 := by
  exact hermiteFlatFluxCorrection_iteratedDeriv_zero hM
    (guardedClosureLocalUnit_analyticAt_zero ε M (closureUpperPartnerCenter a))
    (guardedClosureLocalUnit_zero_ne hε
      (closureUpperPartnerCenter_self_factor_ne ha)) hn

/-- The lower-center correction first escapes at the prescribed order. -/
theorem guardedClosure_lower_fluxCorrection_iteratedDeriv_escape_ne_zero
    {a ε : ℝ} {M : ℕ} (ha : a ≠ 0) (hε : ε ≠ 0) (hM : 0 < M) :
    iteratedDeriv M
      (hermiteFlatFluxCorrection M
        (guardedClosureLocalUnit ε M (closureLowerCenter a))) 0 ≠ 0 := by
  exact hermiteFlatFluxCorrection_iteratedDeriv_escape_ne_zero hM
    (guardedClosureLocalUnit_analyticAt_zero ε M (closureLowerCenter a))
    (guardedClosureLocalUnit_zero_ne hε (closureLowerCenter_self_factor_ne ha))

/-- The upper-partner correction first escapes at the same prescribed order. -/
theorem guardedClosure_upperPartner_fluxCorrection_iteratedDeriv_escape_ne_zero
    {a ε : ℝ} {M : ℕ} (ha : a ≠ 0) (hε : ε ≠ 0) (hM : 0 < M) :
    iteratedDeriv M
      (hermiteFlatFluxCorrection M
        (guardedClosureLocalUnit ε M (closureUpperPartnerCenter a))) 0 ≠ 0 := by
  exact hermiteFlatFluxCorrection_iteratedDeriv_escape_ne_zero hM
    (guardedClosureLocalUnit_analyticAt_zero ε M (closureUpperPartnerCenter a))
    (guardedClosureLocalUnit_zero_ne hε
      (closureUpperPartnerCenter_self_factor_ne ha))

/-- The two independent local multiplier-flux corrections have the same Taylor prefix at every
degree below `M`. -/
theorem guardedClosure_partner_fluxCorrection_same_prefix
    {a ε : ℝ} {M n : ℕ} (ha : a ≠ 0) (hε : ε ≠ 0) (hM : 0 < M) (hn : n < M) :
    iteratedDeriv n
      (hermiteFlatFluxCorrection M
        (guardedClosureLocalUnit ε M (closureLowerCenter a))) 0 =
    iteratedDeriv n
      (hermiteFlatFluxCorrection M
        (guardedClosureLocalUnit ε M (closureUpperPartnerCenter a))) 0 := by
  rw [guardedClosure_lower_fluxCorrection_iteratedDeriv_zero ha hε hM hn,
    guardedClosure_upperPartner_fluxCorrection_iteratedDeriv_zero ha hε hM hn]

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
