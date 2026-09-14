import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSignedFourierUniqueness
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinModularGeneratorInvariance
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBesselOrderExteriorEnvelope

/-!
# The completed Eisenstein series on the critical line as a modular-invariant function

The cusp Fourier model `d4BMCompletedEisensteinCuspLeg .scalar u x Y` of the completed weight-zero
Eisenstein series is defined for every parameter `u`; for `Re u > 1/2` it equals the absolutely
convergent completed Poincaré series, which is invariant under the generators `S`, `T` of
`SL(2, ℤ)`.  The model is holomorphic in `u` on the quarter-plane `Ω = {−1/2 < Re u, 0 < Im u}`:
its constant part is built from `Λ(2u)`, `Λ(1 + 2u)` and powers of `Y`, all holomorphic off the
real axis, and its Whittaker tail is a locally uniformly convergent series of holomorphic
functions of the Bessel order.  Translation invariance is exact in the Fourier phases, and
inversion invariance transfers from `Re u > 1/2` to all of `Ω` by the identity theorem.  Hence for
every `t > 0` the model `E*(·, ½ + it)` is an `SL(2, ℤ)`-invariant function on `ℍ`.
-/

open UpperHalfPlane Real Set Filter Topology
open scoped MatrixGroups

namespace RHTower

noncomputable section

/-! ## The parameter domain -/

/-- The quarter-plane `{−1/2 < Re u, 0 < Im u}` of Eisenstein parameters `u = s − 1/2`. -/
def eisensteinLineDomain : Set ℂ := {u : ℂ | -1 / 2 < u.re ∧ 0 < u.im}

theorem isOpen_eisensteinLineDomain : IsOpen eisensteinLineDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem convex_eisensteinLineDomain : Convex ℝ eisensteinLineDomain :=
  (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt 0)

theorem isPreconnected_eisensteinLineDomain : IsPreconnected eisensteinLineDomain :=
  convex_eisensteinLineDomain.isPreconnected

theorem mem_eisensteinLineDomain_of_re {u : ℂ} (hre : 1 / 2 < u.re) (him : 0 < u.im) :
    u ∈ eisensteinLineDomain :=
  ⟨by linarith, him⟩

theorem I_mul_mem_eisensteinLineDomain {t : ℝ} (ht : 0 < t) :
    (t : ℂ) * Complex.I ∈ eisensteinLineDomain := by
  refine ⟨?_, ?_⟩
  · simp; norm_num
  · simp [ht]

/-! ## Holomorphy of the constant part -/

/-- `Λ = Γ_ℝ · ζ` is holomorphic off the real axis. -/
theorem differentiableAt_reflectedCompletedLambda {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ reflectedCompletedLambda s := by
  have h1 : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have hG : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
      funext Complex.Gammaℝ_def
    rw [hG]
    apply DifferentiableAt.mul
    · exact (differentiableAt_id.neg.div_const 2).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · refine (Complex.differentiableAt_Gamma (s / 2) ?_).comp s (differentiableAt_id.div_const 2)
      intro m h
      apply hs
      have := congrArg Complex.im h
      simp at this
      linarith
  have h2 : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (fun h => hs (by rw [h]; simp))
  exact h1.mul h2

theorem differentiableAt_cuspConstantPart {Y : ℝ} (hY : 0 < Y) {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) :
    DifferentiableAt ℂ (fun u => d4BMCompletedEisensteinCuspConstantPart .scalar u Y) u := by
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have him : 0 < u.im := hu.2
  have hΛ2 : DifferentiableAt ℂ (fun u : ℂ => reflectedCompletedLambda (2 * u)) u := by
    refine (differentiableAt_reflectedCompletedLambda ?_).comp u (differentiableAt_id.const_mul 2)
    simp; linarith
  have hΛ1 : DifferentiableAt ℂ (fun u : ℂ => reflectedCompletedLambda (1 + 2 * u)) u := by
    refine (differentiableAt_reflectedCompletedLambda ?_).comp u
      ((differentiableAt_id.const_mul 2).const_add 1)
    simp; linarith
  have hpow : ∀ c : ℂ, DifferentiableAt ℂ (fun u : ℂ => (Y : ℂ) ^ (1 / 2 + c * u)) u := by
    intro c
    have h1 : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 + c * u) u := by fun_prop
    exact h1.const_cpow (Or.inl hYne)
  unfold d4BMCompletedEisensteinCuspConstantPart d4BMCompletedEisensteinCuspConstantTerm
    d4BMCompletedEisensteinCuspConstantCoefficient d4BMCompletedEisensteinCuspConstantMaassFactor
    d4BMCompletedEisensteinCuspWeylExponent d4BMCuspSign
  simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_one, mul_one]
  exact ((hΛ2.mul (hpow _))).add (hΛ1.mul (hpow _))

/-! ## Holomorphy of the Whittaker tail -/

/-- The Whittaker coefficient is entire in the parameter. -/
theorem differentiableAt_whittakerCoefficient (n : D4BMPositiveIndex) (u : ℂ) :
    DifferentiableAt ℂ (fun u => d4BMCompletedEisensteinWhittakerCoefficient u n) u := by
  unfold d4BMCompletedEisensteinWhittakerCoefficient
  have hn : ((n.1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.2.ne'
  have h1 : DifferentiableAt ℂ (fun u : ℂ => ((n.1 : ℕ) : ℂ) ^ u) u :=
    (differentiableAt_id (𝕜 := ℂ)).const_cpow (Or.inl hn)
  have h2 : DifferentiableAt ℂ (fun u : ℂ => ∑ d ∈ n.1.divisors, (d : ℂ) ^ (-2 * u)) u := by
    have hfun : (fun u : ℂ => ∑ d ∈ n.1.divisors, (d : ℂ) ^ (-2 * u)) =
        ∑ d ∈ n.1.divisors, (fun u : ℂ => (d : ℂ) ^ (-2 * u)) := by
      funext u; simp [Finset.sum_apply]
    rw [hfun]
    refine DifferentiableAt.sum fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have h3 : DifferentiableAt ℂ (fun u : ℂ => -2 * u) u := by fun_prop
    exact h3.const_cpow (Or.inl hd)
  exact h1.mul h2

/-- The `N`-th summand of the signed square-root Whittaker tail at zero degrees, with the Bessel
order equal to the parameter. -/
def eisensteinTailTerm (negative : Bool) (x Y : ℝ) (N : ℕ) (u : ℂ) : ℂ :=
  (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ (0 : ℕ) * d4BMCompletedEisensteinFourierPhase negative N x) *
    (Real.sqrt Y : ℂ) * (Y : ℂ) ^ (0 : ℕ) *
    GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) u

theorem signedSqrtWhittakerTail_eq_tsum_term (negative : Bool) (x Y : ℝ) (u : ℂ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative x 0 0 Y =
      ∑' N : ℕ, eisensteinTailTerm negative x Y N u := rfl

theorem differentiable_eisensteinTailTerm (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) (N : ℕ) :
    Differentiable ℂ (eisensteinTailTerm negative x Y N) := by
  intro u
  unfold eisensteinTailTerm
  have hs : (0 : ℝ) < 2 * Real.pi * ((N : ℝ) + 1) * Y := by positivity
  refine DifferentiableAt.mul ?_ (GaloisForLFunctions.HTGeometry.differentiable_modifiedBesselKOrder hs u)
  refine DifferentiableAt.mul ?_ (differentiableAt_const _)
  refine DifferentiableAt.mul ?_ (differentiableAt_const _)
  refine DifferentiableAt.mul ?_ (differentiableAt_const _)
  exact (differentiableAt_whittakerCoefficient _ u).mul (differentiableAt_const _)

/-- The majorant of the tail terms on a ball of radius one around `u₀`. -/
def eisensteinTailMajorant (Y : ℝ) (u₀ : ℂ) (N : ℕ) : ℝ :=
  (Real.sqrt Y * Real.exp ((‖u₀‖ + 1) ^ 2 / (4 * Real.pi * Y)) * Real.sqrt (1 / Y)) *
    (((N : ℝ) + 1) ^ (⌈3 * (‖u₀‖ + 1) + 1⌉₊) * Real.exp (-(2 * Real.pi * Y) * ((N : ℝ) + 1)))

theorem summable_eisensteinTailMajorant {Y : ℝ} (hY : 0 < Y) (u₀ : ℂ) :
    Summable (eisensteinTailMajorant Y u₀) := by
  unfold eisensteinTailMajorant
  refine Summable.mul_left _ ?_
  have h := Real.summable_pow_mul_exp_neg_nat_mul (⌈3 * (‖u₀‖ + 1) + 1⌉₊)
    (show 0 < 2 * Real.pi * Y by positivity)
  have h' := (summable_nat_add_iff 1).mpr h
  refine h'.congr fun N => ?_
  push_cast
  ring_nf

theorem norm_eisensteinTailTerm_le (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) (u₀ : ℂ)
    (N : ℕ) {u : ℂ} (hu : u ∈ Metric.ball u₀ 1) :
    ‖eisensteinTailTerm negative x Y N u‖ ≤ eisensteinTailMajorant Y u₀ N := by
  set R : ℝ := ‖u₀‖ + 1 with hR
  have huR : ‖u‖ ≤ R := by
    have := Metric.mem_ball.mp hu
    rw [dist_eq_norm] at this
    calc ‖u‖ = ‖(u - u₀) + u₀‖ := by ring_nf
      _ ≤ ‖u - u₀‖ + ‖u₀‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  have hRpos : 0 < R := by positivity
  set s : ℝ := 2 * Real.pi * ((N : ℝ) + 1) * Y with hsdef
  have hs : 0 < s := by positivity
  have hs2 : 2 * Real.pi * Y ≤ s := by
    rw [hsdef]
    have : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    nlinarith [Real.pi_pos, hY]
  -- the coefficient
  have hcoef : ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ ≤
      ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) := by
    refine (d4BM_norm_completedEisensteinWhittakerCoefficient_le u ⟨N + 1, by omega⟩).trans ?_
    have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    have hre : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
    calc ((N + 1 : ℕ) : ℝ) ^ (3 * |u.re| + 1) ≤ ((N + 1 : ℕ) : ℝ) ^ (⌈3 * R + 1⌉₊ : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
          have := Nat.le_ceil (3 * R + 1)
          linarith
      _ = ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) := by
          rw [Real.rpow_natCast]; push_cast; rfl
  -- the phase
  have hphase : ‖d4BMCompletedEisensteinFourierPhase negative N x‖ = 1 := by
    unfold d4BMCompletedEisensteinFourierPhase
    exact Complex.norm_exp_ofReal_mul_I _
  -- the Bessel factor
  have hK : ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder s u‖ ≤
      Real.exp (-s) * Real.exp (R ^ 2 / (4 * Real.pi * Y)) * Real.sqrt (1 / Y) := by
    have h := d4BM_norm_modifiedBesselKOrder_le ⟨s, hs⟩ u
    simp only at h
    refine h.trans ?_
    have h1 : Real.exp (‖u‖ ^ 2 / (2 * s)) ≤ Real.exp (R ^ 2 / (4 * Real.pi * Y)) := by
      rw [Real.exp_le_exp]
      have hu2 : ‖u‖ ^ 2 ≤ R ^ 2 := by
        have := norm_nonneg u
        nlinarith
      calc ‖u‖ ^ 2 / (2 * s) ≤ R ^ 2 / (2 * s) := by
            exact div_le_div_of_nonneg_right hu2 (by positivity)
        _ ≤ R ^ 2 / (4 * Real.pi * Y) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            linarith
    have h2 : Real.sqrt (2 * Real.pi / s) ≤ Real.sqrt (1 / Y) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_div_iff₀ hs hY]
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) h2 (Real.sqrt_nonneg _)
      (by positivity)
  -- assemble
  have hsq : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hterm : eisensteinTailTerm negative x Y N u =
      (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        d4BMCompletedEisensteinFourierPhase negative N x) * (Real.sqrt Y : ℂ) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder s u := by
    unfold eisensteinTailTerm
    rw [hsdef]
    simp only [pow_zero, mul_one]
  rw [hterm, norm_mul, norm_mul, norm_mul, hphase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hsq]
  unfold eisensteinTailMajorant
  have hexp : 0 ≤ Real.exp (-s) * Real.exp (R ^ 2 / (4 * Real.pi * Y)) * Real.sqrt (1 / Y) := by
    positivity
  calc ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ * Real.sqrt Y *
        ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder s u‖ ≤
        ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) * Real.sqrt Y *
          (Real.exp (-s) * Real.exp (R ^ 2 / (4 * Real.pi * Y)) * Real.sqrt (1 / Y)) := by
        gcongr
    _ = (Real.sqrt Y * Real.exp (R ^ 2 / (4 * Real.pi * Y)) * Real.sqrt (1 / Y)) *
          (((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) * Real.exp (-(2 * Real.pi * Y) * ((N : ℝ) + 1))) := by
        rw [hsdef]
        have : -(2 * Real.pi * ((N : ℝ) + 1) * Y) = -(2 * Real.pi * Y) * ((N : ℝ) + 1) := by ring
        rw [this]
        ring

theorem differentiableAt_signedSqrtWhittakerTail (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y)
    (u₀ : ℂ) :
    DifferentiableAt ℂ
      (fun u => d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative x 0 0 Y) u₀ := by
  have hU : IsOpen (Metric.ball u₀ (1 : ℝ)) := Metric.isOpen_ball
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm (summable_eisensteinTailMajorant hY u₀)
    (fun N => (differentiable_eisensteinTailTerm negative x hY N).differentiableOn) hU
    (fun N u hu => norm_eisensteinTailTerm_le negative x hY u₀ N hu)
  have h := hdiff.differentiableAt (hU.mem_nhds (Metric.mem_ball_self one_pos))
  simpa [signedSqrtWhittakerTail_eq_tsum_term] using h

theorem differentiableAt_cuspTailPart (x : ℝ) {Y : ℝ} (hY : 0 < Y) (u₀ : ℂ) :
    DifferentiableAt ℂ (fun u => d4BMCompletedEisensteinCuspTailPart .scalar u x Y) u₀ := by
  unfold d4BMCompletedEisensteinCuspTailPart d4BMCompletedEisensteinFullSignedZeroWord
  exact ((differentiableAt_signedSqrtWhittakerTail false x hY u₀).add
    (differentiableAt_signedSqrtWhittakerTail true x hY u₀)).const_mul 2

/-- **Holomorphy of the Fourier model in the parameter** on the quarter-plane. -/
theorem differentiableOn_cuspLeg (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    DifferentiableOn ℂ (fun u => d4BMCompletedEisensteinCuspLeg .scalar u x Y)
      eisensteinLineDomain := by
  intro u hu
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold d4BMCompletedEisensteinCuspLeg
  exact (differentiableAt_cuspConstantPart hY hu).add (differentiableAt_cuspTailPart x hY u)

/-! ## The model on the upper half-plane and its invariance -/

/-- The completed Eisenstein Fourier model at parameter `u`, as a function on `ℍ`. -/
def eisensteinLineModel (u : ℂ) (z : ℍ) : ℂ :=
  d4BMCompletedEisensteinCuspLeg .scalar u z.re z.im

theorem fourierPhase_add_one (negative : Bool) (N : ℕ) (x : ℝ) :
    d4BMCompletedEisensteinFourierPhase negative N (x + 1) =
      d4BMCompletedEisensteinFourierPhase negative N x := by
  unfold d4BMCompletedEisensteinFourierPhase d4BMFourierSign
  split_ifs
  · have h : (((-1 : ℝ) * (2 * Real.pi * ((N : ℝ) + 1) * (x + 1)) : ℝ) : ℂ) * Complex.I =
        (((-1 : ℝ) * (2 * Real.pi * ((N : ℝ) + 1) * x) : ℝ) : ℂ) * Complex.I +
          ((-((N : ℤ) + 1) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · have h : (((1 : ℝ) * (2 * Real.pi * ((N : ℝ) + 1) * (x + 1)) : ℝ) : ℂ) * Complex.I =
        (((1 : ℝ) * (2 * Real.pi * ((N : ℝ) + 1) * x) : ℝ) : ℂ) * Complex.I +
          ((((N : ℤ) + 1) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem cuspLeg_add_one (u : ℂ) (x Y : ℝ) :
    d4BMCompletedEisensteinCuspLeg .scalar u (x + 1) Y =
      d4BMCompletedEisensteinCuspLeg .scalar u x Y := by
  unfold d4BMCompletedEisensteinCuspLeg d4BMCompletedEisensteinCuspTailPart
    d4BMCompletedEisensteinFullSignedZeroWord d4BMCompletedEisensteinSignedSqrtWhittakerTail
  simp only [fourierPhase_add_one]

/-- Translation invariance of the model, for every parameter. -/
theorem eisensteinLineModel_T (u : ℂ) (z : ℍ) :
    eisensteinLineModel u (ModularGroup.T • z) = eisensteinLineModel u z := by
  unfold eisensteinLineModel
  rw [modular_T_smul]
  have hre : ((1 : ℝ) +ᵥ z : ℍ).re = z.re + 1 := by
    rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]; simp; ring
  have him : ((1 : ℝ) +ᵥ z : ℍ).im = z.im := by
    rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd]; simp
  rw [hre, him, cuspLeg_add_one]

/-- The coordinates of `S • z` are the inversion coordinates of the Poincaré modules. -/
theorem modular_S_smul_re (z : ℍ) :
    (ModularGroup.S • z).re = -z.re / (z.re ^ 2 + z.im ^ 2) := by
  rw [modular_S_smul, ← UpperHalfPlane.coe_re]
  show ((-(z : ℂ))⁻¹).re = _
  rw [Complex.inv_re, Complex.normSq_apply]
  simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem modular_S_smul_im (z : ℍ) :
    (ModularGroup.S • z).im = z.im / (z.re ^ 2 + z.im ^ 2) := by
  rw [modular_S_smul, ← UpperHalfPlane.coe_im]
  show ((-(z : ℂ))⁻¹).im = _
  rw [Complex.inv_im, Complex.normSq_apply]
  simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem horizontalCoordinate_self (w : D4BMUpperHalfPlaneCoordinate) :
    d4BMHorizontalCoordinate w w.x = w := by
  cases w; rfl

/-- Inversion invariance of the model for `Re u > 1/2`, from the Poincaré series. -/
theorem eisensteinLineModel_S_of_re {u : ℂ} (hu : 1 / 2 < u.re) (z : ℍ) :
    eisensteinLineModel u (ModularGroup.S • z) = eisensteinLineModel u z := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter :=
    ⟨u + 1 / 2, by simp; linarith⟩
  have hP : P.s - 1 / 2 = u := by simp [P]
  let w : D4BMUpperHalfPlaneCoordinate := ⟨z.re, z.im, z.im_pos⟩
  have h1 := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg w P w.x
  have h2 := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg (d4BMEisensteinInvertCoordinate w) P
    (d4BMEisensteinInvertCoordinate w).x
  have hinv := d4BM_completedEisensteinPoincareSeries_invert w P
  unfold d4BMCompletedEisensteinHorizontalFunction at h1 h2
  rw [horizontalCoordinate_self, hP] at h1 h2
  unfold eisensteinLineModel
  rw [modular_S_smul_re, modular_S_smul_im]
  have hx : (d4BMEisensteinInvertCoordinate w).x = -z.re / (z.re ^ 2 + z.im ^ 2) := rfl
  have hy : (d4BMEisensteinInvertCoordinate w).y = z.im / (z.re ^ 2 + z.im ^ 2) := rfl
  rw [← hx, ← hy, ← h2, hinv, h1]

/-- **Inversion invariance on the whole parameter domain**, by the identity theorem. -/
theorem eisensteinLineModel_S {u : ℂ} (hu : u ∈ eisensteinLineDomain) (z : ℍ) :
    eisensteinLineModel u (ModularGroup.S • z) = eisensteinLineModel u z := by
  let f : ℂ → ℂ := fun u =>
    eisensteinLineModel u (ModularGroup.S • z) - eisensteinLineModel u z
  have hf : AnalyticOnNhd ℂ f eisensteinLineDomain := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_eisensteinLineDomain
    exact (differentiableOn_cuspLeg _ (ModularGroup.S • z).im_pos).sub
      (differentiableOn_cuspLeg _ z.im_pos)
  have hz₀ : (1 + Complex.I) ∈ eisensteinLineDomain := by
    refine ⟨?_, ?_⟩
    · simp; norm_num
    · simp
  have hev : f =ᶠ[nhds (1 + Complex.I)] 0 := by
    have hopen : IsOpen {u : ℂ | 1 / 2 < u.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {u : ℂ | 1 / 2 < u.re} ∈ nhds (1 + Complex.I) :=
      hopen.mem_nhds (by simp; norm_num)
    filter_upwards [hmem] with u hu
    exact sub_eq_zero.mpr (eisensteinLineModel_S_of_re hu z)
  have h := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_eisensteinLineDomain
    hz₀ hev hu
  exact sub_eq_zero.mp h

/-- **Modular invariance of the completed Eisenstein model** for every parameter in the
quarter-plane, in particular on the critical line. -/
theorem eisensteinLineModel_smul {u : ℂ} (hu : u ∈ eisensteinLineDomain) (γ : SL(2, ℤ)) (z : ℍ) :
    eisensteinLineModel u (γ • z) = eisensteinLineModel u z := by
  have hγ : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  have key : ∀ g ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)),
      ∀ z : ℍ, eisensteinLineModel u (g • z) = eisensteinLineModel u z := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact fun z => eisensteinLineModel_S hu z
      · exact fun z => eisensteinLineModel_T u z
    | one => intro z; simp
    | mul g h _ _ hg hh => intro z; rw [mul_smul, hg, hh]
    | inv g _ hg =>
      intro z
      have := hg (g⁻¹ • z)
      rw [smul_inv_smul] at this
      exact this.symm
  exact key γ hγ z

/-- The completed Eisenstein series on the critical line, `E*(·, ½ + it)`, is `SL(2, ℤ)`-invariant. -/
theorem eisensteinLineModel_I_mul_smul {t : ℝ} (ht : 0 < t) (γ : SL(2, ℤ)) (z : ℍ) :
    eisensteinLineModel ((t : ℂ) * Complex.I) (γ • z) =
      eisensteinLineModel ((t : ℂ) * Complex.I) z :=
  eisensteinLineModel_smul (I_mul_mem_eisensteinLineDomain ht) γ z

end

end RHTower
