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

namespace RHTower

noncomputable section

/-! ## Compact-open convergence of the guarded realizers -/

theorem coshQuartetEnvelope_continuous (a : ℝ) :
    Continuous (coshQuartetEnvelope a) := by
  unfold coshQuartetEnvelope
  exact (Complex.continuous_cosh.comp (continuous_id.sub continuous_const)).mul
    (Complex.continuous_cosh.comp (continuous_id.add continuous_const))

theorem quartetFlatAtom_continuous (α : ℂ) :
    Continuous (quartetFlatAtom α) := by
  unfold quartetFlatAtom
  fun_prop

/-- **Compact-open closure.** The guarded aperiodic finite-depth realizers converge to the
periodic all-order envelope uniformly on every compact subset of the plane: the superexponential
contact scale beats the polynomial multiplier's geometric growth on each compact set. -/
theorem guardedClosureApproximant_tendstoLocallyUniformly (a : ℝ) :
    TendstoLocallyUniformly (fun N z => guardedClosureApproximant a N z)
      (coshQuartetEnvelope a) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨E, hE⟩ := hK.exists_bound_of_continuousOn
    (coshQuartetEnvelope_continuous a).continuousOn
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (quartetFlatAtom_continuous (closureQuartetCenter a)).continuousOn
  have hb : Tendsto
      (fun N : ℕ => max E 0 * (guardedClosureScale N * max R 0 ^ (N + 1)))
      atTop (𝓝 0) := by
    have htail := (exp_neg_nat_sq_mul_pow_tendsto_zero_of_nonneg
      (le_max_right R 0)).comp (tendsto_add_atTop_nat 1)
    have hmul := htail.const_mul (max E 0)
    simpa [guardedClosureScale, Function.comp, mul_zero] using hmul
  filter_upwards [hb.eventually_lt_const hε] with N hN z hz
  have hdiff : coshQuartetEnvelope a z - guardedClosureApproximant a N z =
      -(coshQuartetEnvelope a z * (((guardedClosureScale N : ℝ) : ℂ) *
        quartetFlatAtom (closureQuartetCenter a) z ^ (N + 1))) := by
    simp only [guardedClosureApproximant, polynomialXiEnvelope,
      guardedClosurePolynomial_eval]
    ring
  rw [dist_eq_norm, hdiff, norm_neg, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (show (0 : ℝ) < guardedClosureScale N from Real.exp_pos _)]
  have h1 : ‖coshQuartetEnvelope a z‖ ≤ max E 0 :=
    le_trans (hE z hz) (le_max_left E 0)
  have h2 : ‖quartetFlatAtom (closureQuartetCenter a) z‖ ≤ max R 0 :=
    le_trans (hR z hz) (le_max_left R 0)
  have h3 : (0 : ℝ) ≤ guardedClosureScale N := (Real.exp_pos _).le
  calc ‖coshQuartetEnvelope a z‖ *
      (guardedClosureScale N * ‖quartetFlatAtom (closureQuartetCenter a) z‖ ^ (N + 1))
      ≤ max E 0 * (guardedClosureScale N * max R 0 ^ (N + 1)) := by
        gcongr
    _ < ε := hN

/-! ## Formal germ separation of the two partner flux corrections

Equality of the partner germs would transport the aperiodic multiplier polynomial onto an exact
vertical period.  The chain is: eventual equality near the origin forces a polynomial identity,
the identity forces a Wronskian relation, value-one normalization at the origin upgrades the
Wronskian relation to equality of the two shifted polynomials, and equality of the shifts is a
nonzero period of a positive-degree polynomial. -/

/-- A neighbourhood of the origin supports infinitely many agreement points. -/
theorem infinite_setOf_eq_of_eventuallyEq_nhds_zero {f g : ℂ → ℂ}
    (h : f =ᶠ[𝓝 (0 : ℂ)] g) : {x : ℂ | f x = g x}.Infinite := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((δ / (n + 2) : ℝ) : ℂ))
  · intro m n hmn
    simp only [Complex.ofReal_inj] at hmn
    have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
    have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
    rw [div_eq_div_iff hm hn] at hmn
    have h2 := mul_left_cancel₀ (ne_of_gt hδ) hmn
    have h3 : (m : ℝ) = (n : ℝ) := by linarith
    exact_mod_cast h3
  · intro n
    apply hball
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < δ / ((n : ℝ) + 2))]
    apply div_lt_self hδ
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- Polynomials whose evaluations agree near the origin are equal. -/
theorem polynomial_eq_of_eval_eventuallyEq_nhds_zero {p q : Polynomial ℂ}
    (h : (fun x : ℂ => p.eval x) =ᶠ[𝓝 (0 : ℂ)] fun x : ℂ => q.eval x) : p = q :=
  Polynomial.eq_of_infinite_eval_eq p q (infinite_setOf_eq_of_eventuallyEq_nhds_zero h)

/-- A polynomial of positive degree admits no nonzero additive period. -/
theorem polynomial_no_nontrivial_period {P : Polynomial ℂ} {h : ℂ}
    (hdeg : 0 < P.natDegree) (hh : h ≠ 0)
    (hper : ∀ z : ℂ, P.eval (z + h) = P.eval z) : False := by
  have hiter : ∀ n : ℕ, P.eval ((n : ℂ) * h) = P.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        have hstep : ((m + 1 : ℕ) : ℂ) * h = (m : ℂ) * h + h := by
          push_cast
          ring
        rw [hstep, hper, ih]
  have hQne : P - Polynomial.C (P.eval 0) ≠ 0 := by
    intro h0
    rw [sub_eq_zero.mp h0, Polynomial.natDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  have hroots : {x : ℂ | (P - Polynomial.C (P.eval 0)).IsRoot x}.Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * h)
    · intro m n hmn
      have := mul_right_cancel₀ hh hmn
      exact_mod_cast this
    · intro n
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub,
        Polynomial.eval_C, hiter n, sub_self]
  exact hQne (Polynomial.eq_zero_of_infinite_isRoot _ hroots)

/-- Two polynomials with value one at the origin and equal logarithmic derivative coincide: the
difference would vanish at the origin to some exact finite order `k+1`, while the Wronskian
identity forces the order-`k` coefficient of its derivative to vanish as well. -/
theorem polynomial_eq_of_derivative_mul_eq {f g : Polynomial ℂ}
    (hf0 : f.eval 0 = 1) (hg0 : g.eval 0 = 1)
    (hw : Polynomial.derivative f * g = f * Polynomial.derivative g) : f = g := by
  by_contra hne
  have hne0 : f - g ≠ 0 := sub_ne_zero.mpr hne
  have hwron : f * Polynomial.derivative (f - g) =
      Polynomial.derivative f * (f - g) := by
    rw [Polynomial.derivative_sub]
    linear_combination hw
  have hkpos : 0 < (f - g).rootMultiplicity 0 := by
    rw [Polynomial.rootMultiplicity_pos hne0]
    simp [Polynomial.IsRoot, Polynomial.eval_sub, hf0, hg0]
  obtain ⟨q, hq, hnd⟩ := (f - g).exists_eq_pow_rootMultiplicity_mul_and_not_dvd hne0 0
  rw [Polynomial.C_0, sub_zero] at hq hnd
  obtain ⟨k, hk⟩ : ∃ k, (f - g).rootMultiplicity 0 = k + 1 :=
    ⟨(f - g).rootMultiplicity 0 - 1, by omega⟩
  rw [hk] at hq
  have hder : Polynomial.derivative (f - g) =
      X ^ k * (Polynomial.C ((k : ℂ) + 1) * q + X * Polynomial.derivative q) := by
    rw [hq, Polynomial.derivative_mul, Polynomial.derivative_X_pow, Nat.add_sub_cancel]
    push_cast
    ring
  have hXk : (X : Polynomial ℂ) ^ k ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hkey : f * (Polynomial.C ((k : ℂ) + 1) * q + X * Polynomial.derivative q) =
      Polynomial.derivative f * (X * q) := by
    apply mul_left_cancel₀ hXk
    calc
      X ^ k * (f * (Polynomial.C ((k : ℂ) + 1) * q + X * Polynomial.derivative q))
          = f * (X ^ k *
            (Polynomial.C ((k : ℂ) + 1) * q + X * Polynomial.derivative q)) := by
            ring
      _ = f * Polynomial.derivative (f - g) := by rw [hder]
      _ = Polynomial.derivative f * (f - g) := hwron
      _ = Polynomial.derivative f * (X ^ (k + 1) * q) := by rw [hq]
      _ = X ^ k * (Polynomial.derivative f * (X * q)) := by ring
  have heval := congrArg (Polynomial.eval (0 : ℂ)) hkey
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, hf0, one_mul, zero_mul, mul_zero, add_zero] at heval
  have hq0 : q.eval 0 = 0 := by
    rcases mul_eq_zero.mp heval with h | h
    · exfalso
      have hcast : ((k : ℂ) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      exact hcast h
    · exact h
  exact hnd (Polynomial.X_dvd_iff.mpr
    (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hq0))

/-- The completed flux correction is the negative coordinate-weighted logarithmic derivative of
its Hermite-flat factor. -/
theorem hermiteFlatFluxCorrection_eq_neg_logDeriv {M : ℕ} (hM : 0 < M)
    {u : ℂ → ℂ} (hu : Differentiable ℂ u) (x : ℂ) :
    hermiteFlatFluxCorrection M u x =
      -(x * deriv (hermiteFlatFactor M u) x) / hermiteFlatFactor M u x := by
  have h1 : HasDerivAt (hermiteFlatFactor M u)
      ((M : ℂ) * x ^ (M - 1) * u x + x ^ M * deriv u x) x := by
    have hpow : HasDerivAt (fun t : ℂ => t ^ M) ((M : ℂ) * x ^ (M - 1)) x :=
      hasDerivAt_pow M x
    have hmul : HasDerivAt (fun t : ℂ => t ^ M * u t)
        ((M : ℂ) * x ^ (M - 1) * u x + x ^ M * deriv u x) x :=
      hpow.mul (hu x).hasDerivAt
    exact hmul.const_add 1
  have hd := h1.deriv
  simp only [hermiteFlatFluxCorrection, hermiteFlatFluxUnit]
  rw [hd, ← mul_div_assoc]
  have hxpow : x * x ^ (M - 1) = x ^ M := by
    conv_rhs => rw [show M = M - 1 + 1 by omega]
    rw [pow_succ]
    ring
  congr 1
  linear_combination ((M : ℂ) * u x) * hxpow

theorem guardedClosureLocalUnit_differentiable (ε : ℝ) (M : ℕ) (c : ℂ) :
    Differentiable ℂ (guardedClosureLocalUnit ε M c) := by
  unfold guardedClosureLocalUnit quartetFlatAtomUnit
  fun_prop

/-- The multiplier takes the value one at the lower selected center. -/
theorem guardedClosurePolynomial_eval_lowerCenter (a : ℝ) (N : ℕ) :
    (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
      (closureLowerCenter a) = 1 := by
  have h := guardedClosurePolynomial_shift_lower a (guardedClosureScale N) (N + 1) 0
  rw [add_zero] at h
  rw [h]
  exact hermiteFlatFactor_zero (Nat.succ_pos N) _

/-- The multiplier takes the value one at the vertical partner center. -/
theorem guardedClosurePolynomial_eval_upperPartnerCenter (a : ℝ) (N : ℕ) :
    (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
      (closureUpperPartnerCenter a) = 1 := by
  have h := guardedClosurePolynomial_shift_upperPartner a (guardedClosureScale N) (N + 1) 0
  rw [add_zero] at h
  rw [h]
  exact hermiteFlatFactor_zero (Nat.succ_pos N) _

/-- **No vertical transport of the multiplier.** No scalar multiple identifies the multiplier
polynomial recentered at the two period-partner centers: evaluation at the centers forces the
scalar to be one, and exact equality would give the nonconstant polynomial the vertical period
`πi`. -/
theorem guardedClosurePolynomial_comp_partner_ne_C_mul (a : ℝ) (N : ℕ) (C : ℂ) :
    (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
        (X + Polynomial.C (closureLowerCenter a)) ≠
      Polynomial.C C *
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
          (X + Polynomial.C (closureUpperPartnerCenter a)) := by
  intro hcomp
  have hC : C = 1 := by
    have h0 := congrArg (Polynomial.eval (0 : ℂ)) hcomp
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, zero_add] at h0
    rw [guardedClosurePolynomial_eval_lowerCenter a N,
      guardedClosurePolynomial_eval_upperPartnerCenter a N, mul_one] at h0
    exact h0.symm
  rw [hC, map_one, one_mul] at hcomp
  have hper : ∀ w : ℂ,
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (w + (Real.pi : ℂ) * I) =
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval w := by
    intro w
    have h1 := congrArg (Polynomial.eval (w - closureLowerCenter a)) hcomp
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C] at h1
    rw [closureUpperPartnerCenter_eq_shift] at h1
    have e1 : w - closureLowerCenter a + closureLowerCenter a = w := by ring
    have e2 : w - closureLowerCenter a +
        (closureLowerCenter a + (Real.pi : ℂ) * I) = w + (Real.pi : ℂ) * I := by
      ring
    rw [e1, e2] at h1
    exact h1.symm
  have hπ : ((Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
  have hdeg :
      0 < (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).natDegree := by
    have hεne : guardedClosureScale N ≠ 0 := (Real.exp_pos _).ne'
    rw [guardedClosurePolynomial_natDegree hεne (Nat.succ_pos N)]
    omega
  exact polynomial_no_nontrivial_period hdeg hπ hper

/-- **Factor germ separation.** No scalar multiple identifies the two period-partner factor
germs near the origin. -/
theorem guardedClosure_partner_factor_germ_ne (a : ℝ) (N : ℕ) (C : ℂ) :
    ¬ ((fun x : ℂ => (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
          (closureLowerCenter a + x)) =ᶠ[𝓝 (0 : ℂ)]
        fun x : ℂ =>
          C * (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
            (closureUpperPartnerCenter a + x)) := by
  intro heq
  apply guardedClosurePolynomial_comp_partner_ne_C_mul a N C
  apply polynomial_eq_of_eval_eventuallyEq_nhds_zero
  filter_upwards [heq] with x hx
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [add_comm x (closureLowerCenter a), add_comm x (closureUpperPartnerCenter a)]
  exact hx

end

end RHTower

namespace RHTower

noncomputable section

/-- **Flux germ separation.** At every finite contact depth, the two period-partner completed
flux-correction germs are distinct near the origin.  Their equality would equate the coordinate-
weighted logarithmic derivatives of the two recentered multiplier factors, hence — after
polynomial rigidity at the origin — the recentered multipliers themselves, giving the nonconstant
multiplier the vertical period `πi`. -/
theorem guardedClosure_partner_fluxCorrection_germ_ne (a : ℝ) (N : ℕ) :
    ¬ (hermiteFlatFluxCorrection (N + 1)
        (guardedClosureLocalUnit (guardedClosureScale N) (N + 1) (closureLowerCenter a))
      =ᶠ[𝓝 (0 : ℂ)]
      hermiteFlatFluxCorrection (N + 1)
        (guardedClosureLocalUnit (guardedClosureScale N) (N + 1)
          (closureUpperPartnerCenter a))) := by
  intro heq
  have hFc : hermiteFlatFactor (N + 1)
      (guardedClosureLocalUnit (guardedClosureScale N) (N + 1) (closureLowerCenter a)) =
      fun x : ℂ => (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (closureLowerCenter a + x) :=
    funext fun x =>
      (guardedClosurePolynomial_shift_lower a (guardedClosureScale N) (N + 1) x).symm
  have hFd : hermiteFlatFactor (N + 1)
      (guardedClosureLocalUnit (guardedClosureScale N) (N + 1)
        (closureUpperPartnerCenter a)) =
      fun x : ℂ => (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (closureUpperPartnerCenter a + x) :=
    funext fun x =>
      (guardedClosurePolynomial_shift_upperPartner a (guardedClosureScale N) (N + 1) x).symm
  have hderiv_c : ∀ x : ℂ, deriv (fun t : ℂ =>
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (closureLowerCenter a + t)) x =
      (Polynomial.derivative
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N))).eval
        (closureLowerCenter a + x) := by
    intro x
    rw [deriv_comp_const_add (fun s : ℂ =>
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval s)
      (closureLowerCenter a) x]
    exact Polynomial.deriv _
  have hderiv_d : ∀ x : ℂ, deriv (fun t : ℂ =>
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (closureUpperPartnerCenter a + t)) x =
      (Polynomial.derivative
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N))).eval
        (closureUpperPartnerCenter a + x) := by
    intro x
    rw [deriv_comp_const_add (fun s : ℂ =>
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval s)
      (closureUpperPartnerCenter a) x]
    exact Polynomial.deriv _
  have hne_c : ∀ᶠ x in 𝓝 (0 : ℂ),
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (closureLowerCenter a + x) ≠ 0 := by
    have hcont : ContinuousAt (fun x : ℂ =>
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
          (closureLowerCenter a + x)) 0 :=
      (((guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).continuous).comp
        (continuous_const.add continuous_id)).continuousAt
    refine hcont.eventually_ne ?_
    show (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (closureLowerCenter a + 0) ≠ 0
    rw [add_zero, guardedClosurePolynomial_eval_lowerCenter a N]
    exact one_ne_zero
  have hne_d : ∀ᶠ x in 𝓝 (0 : ℂ),
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (closureUpperPartnerCenter a + x) ≠ 0 := by
    have hcont : ContinuousAt (fun x : ℂ =>
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
          (closureUpperPartnerCenter a + x)) 0 :=
      (((guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).continuous).comp
        (continuous_const.add continuous_id)).continuousAt
    refine hcont.eventually_ne ?_
    show (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
        (closureUpperPartnerCenter a + 0) ≠ 0
    rw [add_zero, guardedClosurePolynomial_eval_upperPartnerCenter a N]
    exact one_ne_zero
  have hpoly : X * ((Polynomial.derivative
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N))).comp
          (X + Polynomial.C (closureLowerCenter a)) *
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
          (X + Polynomial.C (closureUpperPartnerCenter a))) =
      X * ((Polynomial.derivative
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N))).comp
          (X + Polynomial.C (closureUpperPartnerCenter a)) *
        (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
          (X + Polynomial.C (closureLowerCenter a))) := by
    apply polynomial_eq_of_eval_eventuallyEq_nhds_zero
    filter_upwards [heq, hne_c, hne_d] with x hx hcx hdx
    have hbc : hermiteFlatFluxCorrection (N + 1)
        (guardedClosureLocalUnit (guardedClosureScale N) (N + 1) (closureLowerCenter a)) x =
        -(x * (Polynomial.derivative
            (guardedClosurePolynomial a (N + 1) (guardedClosureScale N))).eval
            (closureLowerCenter a + x)) /
          (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
            (closureLowerCenter a + x) := by
      rw [hermiteFlatFluxCorrection_eq_neg_logDeriv (Nat.succ_pos N)
        (guardedClosureLocalUnit_differentiable (guardedClosureScale N) (N + 1)
          (closureLowerCenter a)) x, hFc]
      simp only []
      rw [hderiv_c x]
    have hbd : hermiteFlatFluxCorrection (N + 1)
        (guardedClosureLocalUnit (guardedClosureScale N) (N + 1)
          (closureUpperPartnerCenter a)) x =
        -(x * (Polynomial.derivative
            (guardedClosurePolynomial a (N + 1) (guardedClosureScale N))).eval
            (closureUpperPartnerCenter a + x)) /
          (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).eval
            (closureUpperPartnerCenter a + x) := by
      rw [hermiteFlatFluxCorrection_eq_neg_logDeriv (Nat.succ_pos N)
        (guardedClosureLocalUnit_differentiable (guardedClosureScale N) (N + 1)
          (closureUpperPartnerCenter a)) x, hFd]
      simp only []
      rw [hderiv_d x]
    rw [hbc, hbd, div_eq_div_iff hcx hdx] at hx
    simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    simp only [add_comm x (closureLowerCenter a), add_comm x (closureUpperPartnerCenter a)]
    linear_combination -hx
  have hcancel := mul_left_cancel₀ (Polynomial.X_ne_zero (R := ℂ)) hpoly
  have hwr : Polynomial.derivative
      ((guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
        (X + Polynomial.C (closureLowerCenter a))) *
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
        (X + Polynomial.C (closureUpperPartnerCenter a)) =
      (guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
        (X + Polynomial.C (closureLowerCenter a)) *
      Polynomial.derivative
        ((guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
          (X + Polynomial.C (closureUpperPartnerCenter a))) := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_comp,
      Polynomial.derivative_X_add_C, Polynomial.derivative_X_add_C, one_mul, one_mul]
    linear_combination hcancel
  have hf0 : ((guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
      (X + Polynomial.C (closureLowerCenter a))).eval 0 = 1 := by
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      zero_add]
    exact guardedClosurePolynomial_eval_lowerCenter a N
  have hg0 : ((guardedClosurePolynomial a (N + 1) (guardedClosureScale N)).comp
      (X + Polynomial.C (closureUpperPartnerCenter a))).eval 0 = 1 := by
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      zero_add]
    exact guardedClosurePolynomial_eval_upperPartnerCenter a N
  have hfg := polynomial_eq_of_derivative_mul_eq hf0 hg0 hwr
  exact guardedClosurePolynomial_comp_partner_ne_C_mul a N 1
    (by rw [map_one, one_mul]; exact hfg)

end

end RHTower
