import GaloisForLFunctions.HTGeometry.SimplePoleWeightedFirstSubprincipal

/-!
# Second-subprincipal reflection for weighted simple-pole jet packets

After both principal and first directional boundaries vanish, a weighted polynomial packet is
controlled two pole grades below its nominal Bell weight by the second derivative of its analytic
normalized-coordinate curve.  For normalized simple-pole coordinates

`g_q(x) = C_q + x^(q+1) R_q(x)`,

the complete boundary has three terms: the `X₀` partial times `R₀'(0)`, the `X₁` partial times
`R₁(0)`, and half the `X₀,X₀` Hessian times `R₀(0)^2`.  The first term cannot be discarded when
first-boundary cancellation occurs only because `R₀(0)=0`.

The module first proves the general polynomial second-chain rule and twice-divided quotient limit,
then the weighted normalized-extension law, general simple-pole specialization, Gamma covariant
specialization, and native affine Gamma transfer.  Nonzero second boundary gives exact order
`-(W-2)` without genericity assumptions.
-/

open Complex Filter Topology Finset MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Second derivative of a multivariate polynomial evaluated on finitely many analytic curves. -/
theorem iteratedDeriv_two_mvPolynomial_eval_curve_complex {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ)
    (g : Fin n → ℂ → ℂ) (x : ℂ)
    (hg : ∀ i, AnalyticAt ℂ (g i) x) :
    iteratedDeriv 2 (fun s => MvPolynomial.eval (fun i => g i s) P) x =
      (∑ i, MvPolynomial.eval (fun q => g q x) (MvPolynomial.pderiv i P) *
        iteratedDeriv 2 (g i) x) +
      ∑ i, ∑ j,
        MvPolynomial.eval (fun q => g q x)
            (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) *
          deriv (g j) x * deriv (g i) x := by
  let F : ℂ → ℂ := fun s => MvPolynomial.eval (fun i => g i s) P
  let H : ℂ → ℂ := fun s =>
    ∑ i, MvPolynomial.eval (fun q => g q s) (MvPolynomial.pderiv i P) * deriv (g i) s
  have hgan : ∀ᶠ s in 𝓝 x, ∀ i, AnalyticAt ℂ (g i) s := by
    rw [Filter.eventually_all]
    exact fun i => (hg i).eventually_analyticAt
  have hderiv : deriv F =ᶠ[𝓝 x] H := by
    filter_upwards [hgan] with s hs
    have hd := hasDerivAt_mvPolynomial_eval_curve_complex P g
      (fun i => deriv (g i) s) s (fun i => (hs i).differentiableAt.hasDerivAt)
    exact hd.deriv
  have hH : HasDerivAt H
      ((∑ i, MvPolynomial.eval (fun q => g q x) (MvPolynomial.pderiv i P) *
        iteratedDeriv 2 (g i) x) +
      ∑ i, ∑ j,
        MvPolynomial.eval (fun q => g q x)
            (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) *
          deriv (g j) x * deriv (g i) x) x := by
    dsimp only [H]
    have hi : ∀ i, HasDerivAt
        (fun s => MvPolynomial.eval (fun q => g q s) (MvPolynomial.pderiv i P) *
          deriv (g i) s)
        ((∑ j, MvPolynomial.eval (fun q => g q x)
              (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) * deriv (g j) x) *
            deriv (g i) x +
          MvPolynomial.eval (fun q => g q x) (MvPolynomial.pderiv i P) *
            iteratedDeriv 2 (g i) x) x := by
      intro i
      have hp := hasDerivAt_mvPolynomial_eval_curve_complex
        (MvPolynomial.pderiv i P) g (fun j => deriv (g j) x) x
          (fun j => (hg j).differentiableAt.hasDerivAt)
      have hgi : HasDerivAt (deriv (g i)) (iteratedDeriv 2 (g i) x) x := by
        simpa [iteratedDeriv_succ, iteratedDeriv_one] using!
          (hg i).deriv.differentiableAt.hasDerivAt
      exact hp.mul hgi
    have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hi i)
    convert! hsum using 1
    · funext s
      simp only [Finset.sum_apply]
    · rw [Finset.sum_add_distrib, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
  rw [show iteratedDeriv 2 F x = deriv (deriv F) x by
    simp [iteratedDeriv_succ]]
  rw [hderiv.deriv_eq]
  exact hH.deriv

/-- If both the value and first directional derivative vanish, the second punctured quotient of a
polynomial curve tends to half its full second chain-rule derivative. -/
theorem tendsto_inv_sq_mul_mvPolynomial_eval_curve
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (g : Fin n → ℂ → ℂ)
    (hg : ∀ i, AnalyticAt ℂ (g i) 0)
    (hzero : MvPolynomial.eval (fun i => g i 0) P = 0)
    (hfirst : (∑ i,
      MvPolynomial.eval (fun q => g q 0) (MvPolynomial.pderiv i P) *
        deriv (g i) 0) = 0) :
    Tendsto
      (fun z : ℂ => z⁻¹ ^ 2 * MvPolynomial.eval (fun i => g i z) P)
      (𝓝[≠] 0)
      (𝓝 (((∑ i,
          MvPolynomial.eval (fun q => g q 0) (MvPolynomial.pderiv i P) *
            iteratedDeriv 2 (g i) 0) +
        ∑ i, ∑ j,
          MvPolynomial.eval (fun q => g q 0)
              (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) *
            deriv (g j) 0 * deriv (g i) 0) / 2)) := by
  let F : ℂ → ℂ := fun z => MvPolynomial.eval (fun i => g i z) P
  have hF : AnalyticAt ℂ F 0 := by
    simpa only [F, MvPolynomial.aeval_def] using!
      (AnalyticAt.aeval_mvPolynomial (fun i => hg i) P)
  have hFderiv : deriv F 0 = 0 := by
    have hd := hasDerivAt_mvPolynomial_eval_curve_complex P g
      (fun i => deriv (g i) 0) 0 (fun i => (hg i).differentiableAt.hasDerivAt)
    rw [hd.deriv]
    exact hfirst
  have hds0 : dslope F 0 0 = 0 := by
    rw [dslope_same, hFderiv]
  have hds : AnalyticAt ℂ (dslope F 0) 0 :=
    GaloisForLFunctions.analyticAt_dslope_zero_of_analyticAt hF
  have ht := hds.differentiableAt.hasDerivAt.tendsto_slope_zero
  have hdsderiv : deriv (dslope F 0) 0 = iteratedDeriv 2 F 0 / 2 := by
    rw [hds.differentiableAt.hasDerivAt.deriv]
    simpa using GaloisForLFunctions.iteratedDeriv_dslope_zero_eq hF 1
  rw [hdsderiv] at ht
  have hev :
      (fun z : ℂ => z⁻¹ ^ 2 * MvPolynomial.eval (fun i => g i z) P) =ᶠ[𝓝[≠] 0]
        fun z => z⁻¹ * (dslope F 0 z - dslope F 0 0) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    rw [hds0, sub_zero, dslope_of_ne F hz0]
    simp only [F, slope_def_field, sub_zero, hzero]
    field_simp [hz0]
  have hsecond :=
    iteratedDeriv_two_mvPolynomial_eval_curve_complex P g 0 hg
  change Tendsto
    (fun z : ℂ => z⁻¹ • (dslope F 0 (0 + z) - dslope F 0 0))
    (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 (fun s =>
      MvPolynomial.eval (fun i => g i s) P) 0 / 2)) at ht
  rw [hsecond] at ht
  have ht' : Tendsto (fun z : ℂ => z⁻¹ * (dslope F 0 z - dslope F 0 0))
      (𝓝[≠] 0)
      (𝓝 (((∑ i,
          MvPolynomial.eval (fun q => g q 0) (MvPolynomial.pderiv i P) *
            iteratedDeriv 2 (g i) 0) +
        ∑ i, ∑ j,
          MvPolynomial.eval (fun q => g q 0)
              (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) *
            deriv (g j) 0 * deriv (g i) 0) / 2)) := by
    simpa [smul_eq_mul] using ht
  exact ht'.congr' (hev.mono fun _ hz => hz.symm)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions

noncomputable section

/-- Only normalized coordinates `0` and `1` can have nonzero second derivative at the pole center. -/
theorem iteratedDeriv_two_simplePoleJetNormalizedExtension
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (q : ℕ) :
    iteratedDeriv 2 (simplePoleJetNormalizedExtension U q) 0 =
      if q = 0 then 2 * deriv (simplePoleJetRegularRemainder U 0) 0
      else if q = 1 then 2 * simplePoleJetRegularRemainder U 1 0 else 0 := by
  change iteratedDeriv 2 (fun x : ℂ =>
    simplePoleJetPrincipalCoefficient U q +
      x ^ (q + 1) * simplePoleJetRegularRemainder U q x) 0 = _
  rw [iteratedDeriv_const_add (by norm_num)]
  have hpow : ContDiffAt ℂ 2 (fun x : ℂ => x ^ (q + 1)) 0 := by fun_prop
  have hR : ContDiffAt ℂ 2 (simplePoleJetRegularRemainder U q) 0 :=
    (analyticAt_simplePoleJetRegularRemainder hU q).contDiffAt.of_le le_top
  change iteratedDeriv 2
    ((fun x : ℂ => x ^ (q + 1)) * simplePoleJetRegularRemainder U q) 0 = _
  rw [iteratedDeriv_mul hpow hR]
  rcases q with _ | q
  · simp [Finset.sum_range_succ, iteratedDeriv_succ]
  · rcases q with _ | q
    · simp [Finset.sum_range_succ, iteratedDeriv_succ]
    · simp [Finset.sum_range_succ, iteratedDeriv_succ]

/-- Algebraic reduction of the full second chain-rule sum when the tangent is supported at
coordinate `0` and the second jet is supported at coordinates `0` and `1`. -/
theorem mvPolynomial_secondBoundary_of_sparseJets
    {n : ℕ} (P : MvPolynomial (Fin (n + 2)) ℂ)
    (C : Fin (n + 2) → ℂ) (a b c : ℂ) :
    (((∑ i,
        MvPolynomial.eval C (MvPolynomial.pderiv i P) *
          (if i = (0 : Fin (n + 2)) then 2 * b
            else if i = (1 : Fin (n + 2)) then 2 * c else 0)) +
      ∑ i, ∑ j,
        MvPolynomial.eval C
            (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) *
          (if j = (0 : Fin (n + 2)) then a else 0) *
          (if i = (0 : Fin (n + 2)) then a else 0)) / 2) =
      MvPolynomial.eval C (MvPolynomial.pderiv (0 : Fin (n + 2)) P) * b +
      MvPolynomial.eval C (MvPolynomial.pderiv (1 : Fin (n + 2)) P) * c +
      (2 : ℂ)⁻¹ * MvPolynomial.eval C
        (MvPolynomial.pderiv (0 : Fin (n + 2))
          (MvPolynomial.pderiv (0 : Fin (n + 2)) P)) * a ^ 2 := by
  have hsum_two (A B : Fin (n + 2) → ℂ) :
      (∑ q, if q = (0 : Fin (n + 2)) then A q
        else if q = (1 : Fin (n + 2)) then B q else 0) = A 0 + B 1 := by
    calc
      (∑ q, if q = (0 : Fin (n + 2)) then A q
          else if q = (1 : Fin (n + 2)) then B q else 0) =
          ∑ q, ((if q = (0 : Fin (n + 2)) then A q else 0) +
            if q = (1 : Fin (n + 2)) then B q else 0) := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hq0 : q = 0 <;> by_cases hq1 : q = 1 <;> simp [hq0, hq1]
      _ = A 0 + B 1 := by
        rw [Finset.sum_add_distrib]
        simp
  simp only [mul_ite, mul_zero]
  rw [hsum_two]
  simp
  ring

/-- Abstract second-boundary law for weighted meromorphic coordinates with analytic normalized
extensions. -/
theorem tendsto_pow_sub_two_mul_weightedJetEval_of_normalizedExtension
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight n) W)
    (hW : 2 ≤ W)
    (a g : Fin n → ℂ → ℂ)
    (hg : ∀ q, AnalyticAt ℂ (g q) 0)
    (hcoord : ∀ q : Fin n,
      (fun x : ℂ => x ^ bellJetWeight n q * a q x) =ᶠ[𝓝[≠] 0] g q)
    (hcancel : MvPolynomial.eval (fun q => g q 0) P = 0)
    (hfirst : (∑ q,
      MvPolynomial.eval (fun i => g i 0) (MvPolynomial.pderiv q P) *
        deriv (g q) 0) = 0) :
    Tendsto
      (fun x : ℂ => x ^ (W - 2) * MvPolynomial.eval (fun q => a q x) P)
      (𝓝[≠] 0)
      (𝓝 (((∑ i,
          MvPolynomial.eval (fun q => g q 0) (MvPolynomial.pderiv i P) *
            iteratedDeriv 2 (g i) 0) +
        ∑ i, ∑ j,
          MvPolynomial.eval (fun q => g q 0)
              (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) *
            deriv (g j) 0 * deriv (g i) 0) / 2)) := by
  have hcurve := HTGeometry.tendsto_inv_sq_mul_mvPolynomial_eval_curve
    P g hg hcancel hfirst
  have hev :
      (fun x : ℂ => x ^ (W - 2) * MvPolynomial.eval (fun q => a q x) P) =ᶠ[𝓝[≠] 0]
      (fun x => x⁻¹ ^ 2 * MvPolynomial.eval (fun q => g q x) P) := by
    filter_upwards [Filter.eventually_all.2 hcoord, self_mem_nhdsWithin]
      with x hx hxp
    have hx0 : x ≠ 0 := by simpa using hxp
    have hframe : (fun q : Fin n => x ^ bellJetWeight n q * a q x) =
        fun q => g q x := by
      funext q
      exact hx q
    have hscale := isWeightedHomogeneous_eval₂_scale hP (RingHom.id ℂ)
      (fun q : Fin n => a q x) x
    have hxpow : x⁻¹ ^ 2 * x ^ W = x ^ (W - 2) := by
      rw [show W = (W - 2) + 2 by omega, pow_add]
      calc
        x⁻¹ ^ 2 * (x ^ (W - 2) * x ^ 2) =
            x ^ (W - 2) * (x⁻¹ * x) ^ 2 := by ring
        _ = x ^ (W - 2) := by rw [inv_mul_cancel₀ hx0, one_pow, mul_one]
    rw [← hxpow]
    calc
      x⁻¹ ^ 2 * x ^ W * MvPolynomial.eval (fun q => a q x) P =
          x⁻¹ ^ 2 * (x ^ W * MvPolynomial.eval (fun q => a q x) P) := by ring
      _ = x⁻¹ ^ 2 * MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun q : Fin n => x ^ bellJetWeight n q * a q x) P :=
        congrArg (fun y => x⁻¹ ^ 2 * y) hscale.symm
      _ = x⁻¹ ^ 2 * MvPolynomial.eval (fun q => g q x) P := by
        rw [hframe, MvPolynomial.eval₂_id]
  exact hcurve.congr' (hev.mono fun _ hx => hx.symm)

/-- Complete second-subprincipal boundary for a general analytic simple-pole packet. -/
def simplePoleSecondSubprincipalBoundary
    (U : ℂ → ℂ) (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) : ℂ :=
  MvPolynomial.eval
      (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      deriv (simplePoleJetRegularRemainder U 0) 0 +
    MvPolynomial.eval
      (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ))
      (MvPolynomial.pderiv (1 : Fin (n + 2)) P) *
      simplePoleJetRegularRemainder U 1 0 +
    (2 : ℂ)⁻¹ * MvPolynomial.eval
      (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 2))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P)) *
      simplePoleJetRegularRemainder U 0 0 ^ 2

/-- Twice-normalized polynomial evaluation on the analytic simple-pole coordinate extensions tends
to the complete second-subprincipal boundary. -/
theorem tendsto_inv_sq_mul_simplePoleNormalizedEval
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ)) P = 0)
    (hfirst : MvPolynomial.eval
        (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      simplePoleJetRegularRemainder U 0 0 = 0) :
    Tendsto
      (fun x : ℂ => x⁻¹ ^ 2 * MvPolynomial.eval
        (fun q : Fin (n + 2) => simplePoleJetNormalizedExtension U (q : ℕ) x) P)
      (𝓝[≠] 0)
      (𝓝 (simplePoleSecondSubprincipalBoundary U n P)) := by
  let g : Fin (n + 2) → ℂ → ℂ := fun q =>
    simplePoleJetNormalizedExtension U (q : ℕ)
  have hg : ∀ q, AnalyticAt ℂ (g q) 0 := fun q =>
    analyticAt_simplePoleJetNormalizedExtension hU (q : ℕ)
  have hg0 : (fun q : Fin (n + 2) => g q 0) =
      (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ)) := by
    funext q
    exact simplePoleJetNormalizedExtension_zero U (q : ℕ)
  have hg1 : ∀ q, deriv (g q) 0 =
      if (q : ℕ) = 0 then simplePoleJetRegularRemainder U 0 0 else 0 := by
    intro q
    exact (hasDerivAt_simplePoleJetNormalizedExtension hU (q : ℕ)).deriv
  have hg2 : ∀ q, iteratedDeriv 2 (g q) 0 =
      if (q : ℕ) = 0 then 2 * deriv (simplePoleJetRegularRemainder U 0) 0
      else if (q : ℕ) = 1 then 2 * simplePoleJetRegularRemainder U 1 0 else 0 := by
    intro q
    exact iteratedDeriv_two_simplePoleJetNormalizedExtension hU (q : ℕ)
  have hfirst' : (∑ q,
      MvPolynomial.eval (fun i => g i 0) (MvPolynomial.pderiv q P) *
        deriv (g q) 0) = 0 := by
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    · rw [hg0, hg1]
      simpa using hfirst
    · intro q _ hq
      rw [hg1]
      simp [hq]
    · simp
  have hcurve := HTGeometry.tendsto_inv_sq_mul_mvPolynomial_eval_curve
    P g hg (by rw [hg0]; exact hcancel) hfirst'
  have hboundary :
      (((∑ i,
          MvPolynomial.eval (fun q => g q 0) (MvPolynomial.pderiv i P) *
            iteratedDeriv 2 (g i) 0) +
        ∑ i, ∑ j,
          MvPolynomial.eval (fun q => g q 0)
              (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) *
            deriv (g j) 0 * deriv (g i) 0) / 2) =
        simplePoleSecondSubprincipalBoundary U n P := by
    rw [hg0]
    simp_rw [hg1, hg2]
    have hval_zero (q : Fin (n + 2)) : (q : ℕ) = 0 ↔ q = (0 : Fin (n + 2)) := by
      constructor
      · intro hq
        apply Fin.ext
        simpa using hq
      · intro hq
        subst q
        simp
    have hval_one (q : Fin (n + 2)) : (q : ℕ) = 1 ↔ q = (1 : Fin (n + 2)) := by
      constructor
      · intro hq
        apply Fin.ext
        simpa using hq
      · intro hq
        subst q
        simp
    simp_rw [hval_zero, hval_one]
    simpa [simplePoleSecondSubprincipalBoundary] using
      mvPolynomial_secondBoundary_of_sparseJets P
        (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ))
        (simplePoleJetRegularRemainder U 0 0)
        (deriv (simplePoleJetRegularRemainder U 0) 0)
        (simplePoleJetRegularRemainder U 1 0)
  rw [hboundary] at hcurve
  exact hcurve

/-- Bell-weight scaling transfers the analytic second quotient to the corresponding simple-pole
jet packet two grades below its nominal weight. -/
theorem tendsto_pow_sub_two_mul_simplePoleWeightedJetEval
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ)) P = 0)
    (hfirst : MvPolynomial.eval
        (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      simplePoleJetRegularRemainder U 0 0 = 0) :
    Tendsto
      (fun x : ℂ => x ^ (W - 2) * MvPolynomial.eval
        (fun q : Fin (n + 2) => simplePoleCovariantJetValue U (q : ℕ) x) P)
      (𝓝[≠] 0)
      (𝓝 (simplePoleSecondSubprincipalBoundary U n P)) := by
  let g : Fin (n + 2) → ℂ → ℂ := fun q =>
    simplePoleJetNormalizedExtension U (q : ℕ)
  have hcurve := tendsto_inv_sq_mul_simplePoleNormalizedEval
    hU n P hcancel hfirst
  have hev :
      (fun x : ℂ => x ^ (W - 2) * MvPolynomial.eval
        (fun q : Fin (n + 2) => simplePoleCovariantJetValue U (q : ℕ) x) P) =ᶠ[𝓝[≠] 0]
      (fun x => x⁻¹ ^ 2 * MvPolynomial.eval (fun q => g q x) P) := by
    have hcoord : ∀ q : Fin (n + 2),
        (fun x : ℂ => x ^ bellJetWeight (n + 2) q *
          simplePoleCovariantJetValue U (q : ℕ) x) =ᶠ[𝓝[≠] 0] g q := by
      intro q
      simpa [bellJetWeight, g] using
        pow_mul_simplePoleCovariantJetValue_eventuallyEq_normalizedExtension
          hU (q : ℕ)
    filter_upwards [Filter.eventually_all.2 hcoord, self_mem_nhdsWithin]
      with x hx hxp
    have hx0 : x ≠ 0 := by simpa using hxp
    have hframe :
        (fun q : Fin (n + 2) =>
          x ^ bellJetWeight (n + 2) q *
            simplePoleCovariantJetValue U (q : ℕ) x) =
        fun q => g q x := by
      funext q
      exact hx q
    have hscale := isWeightedHomogeneous_eval₂_scale hP (RingHom.id ℂ)
      (fun q : Fin (n + 2) => simplePoleCovariantJetValue U (q : ℕ) x) x
    have hxpow : x⁻¹ ^ 2 * x ^ W = x ^ (W - 2) := by
      rw [show W = (W - 2) + 2 by omega, pow_add]
      calc
        x⁻¹ ^ 2 * (x ^ (W - 2) * x ^ 2) =
            x ^ (W - 2) * (x⁻¹ * x) ^ 2 := by ring
        _ = x ^ (W - 2) := by rw [inv_mul_cancel₀ hx0, one_pow, mul_one]
    rw [← hxpow]
    calc
      x⁻¹ ^ 2 * x ^ W * MvPolynomial.eval
          (fun q : Fin (n + 2) => simplePoleCovariantJetValue U (q : ℕ) x) P =
          x⁻¹ ^ 2 * (x ^ W * MvPolynomial.eval
            (fun q : Fin (n + 2) => simplePoleCovariantJetValue U (q : ℕ) x) P) := by ring
      _ = x⁻¹ ^ 2 * MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun q : Fin (n + 2) => x ^ bellJetWeight (n + 2) q *
            simplePoleCovariantJetValue U (q : ℕ) x) P :=
        congrArg (fun y => x⁻¹ ^ 2 * y) hscale.symm
      _ = x⁻¹ ^ 2 * MvPolynomial.eval (fun q => g q x) P := by
        rw [hframe, MvPolynomial.eval₂_id]
  exact hcurve.congr' (hev.mono fun _ hx => hx.symm)

/-- A nonzero complete second boundary fixes exact simple-pole packet order `-(W-2)`. -/
theorem meromorphicOrderAt_simplePoleWeightedJetEval_of_secondSubprincipal
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ)) P = 0)
    (hfirst : MvPolynomial.eval
        (fun q : Fin (n + 2) => simplePoleJetPrincipalCoefficient U (q : ℕ))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      simplePoleJetRegularRemainder U 0 0 = 0)
    (hboundary : simplePoleSecondSubprincipalBoundary U n P ≠ 0) :
    meromorphicOrderAt (simplePoleWeightedJetEval U (n + 1) P) 0 =
      ((-((W - 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  refine meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul (W - 2)
    (meromorphicAt_simplePoleWeightedJetEval hU (n + 1) P)
    hboundary ?_
  simpa only [sub_zero, simplePoleWeightedJetEval] using
    tendsto_pow_sub_two_mul_simplePoleWeightedJetEval
      hU n P hP hW hcancel hfirst

/-- Sparse second derivative law for Gamma normalized jet coordinates. -/
theorem iteratedDeriv_two_gammaPoleJetNormalizedExtension
    (branch q : ℕ) :
    iteratedDeriv 2 (gammaPoleJetNormalizedExtension branch q) 0 =
      if q = 0 then 2 * deriv (gammaPoleJetRegularRemainder branch 0) 0
      else if q = 1 then 2 * gammaPoleJetRegularRemainder branch 1 0 else 0 := by
  change iteratedDeriv 2 (fun x : ℂ =>
    gammaPoleJetPrincipalCoefficient branch q +
      x ^ (q + 1) * gammaPoleJetRegularRemainder branch q x) 0 = _
  rw [iteratedDeriv_const_add (by norm_num)]
  have hpow : ContDiffAt ℂ 2 (fun x : ℂ => x ^ (q + 1)) 0 := by fun_prop
  have hR : ContDiffAt ℂ 2 (gammaPoleJetRegularRemainder branch q) 0 :=
    (analyticAt_gammaPoleJetRegularRemainder branch q).contDiffAt.of_le le_top
  change iteratedDeriv 2
    ((fun x : ℂ => x ^ (q + 1)) * gammaPoleJetRegularRemainder branch q) 0 = _
  rw [iteratedDeriv_mul hpow hR]
  rcases q with _ | q
  · simp [Finset.sum_range_succ, iteratedDeriv_succ]
  · rcases q with _ | q
    · simp [Finset.sum_range_succ, iteratedDeriv_succ]
    · simp [Finset.sum_range_succ, iteratedDeriv_succ]

/-- Complete second-subprincipal boundary for a Gamma covariant packet on one pole branch. -/
def gammaPoleSecondSubprincipalBoundary
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) : ℂ :=
  MvPolynomial.eval
      (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      deriv (gammaPoleJetRegularRemainder branch 0) 0 +
    MvPolynomial.eval
      (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
      (MvPolynomial.pderiv (1 : Fin (n + 2)) P) *
      gammaPoleJetRegularRemainder branch 1 0 +
    (2 : ℂ)⁻¹ * MvPolynomial.eval
      (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 2))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P)) *
      gammaPoleJetRegularRemainder branch 0 0 ^ 2

/-- Exact second-subprincipal reflection for a weighted Gamma covariant packet. -/
theorem tendsto_pow_sub_two_mul_gammaPoleWeightedJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) P = 0)
    (hfirst : MvPolynomial.eval
        (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      gammaPoleJetRegularRemainder branch 0 0 = 0) :
    Tendsto
      (fun x : ℂ => x ^ (W - 2) * gammaPoleWeightedJetEval branch (n + 1) P x)
      (𝓝[≠] 0)
      (𝓝 (gammaPoleSecondSubprincipalBoundary branch n P)) := by
  let g : Fin (n + 2) → ℂ → ℂ := fun q =>
    gammaPoleJetNormalizedExtension branch (q : ℕ)
  have hg : ∀ q, AnalyticAt ℂ (g q) 0 := fun q =>
    analyticAt_gammaPoleJetNormalizedExtension branch (q : ℕ)
  have hg0 : (fun q : Fin (n + 2) => g q 0) =
      (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) := by
    funext q
    exact gammaPoleJetNormalizedExtension_zero branch (q : ℕ)
  have hg1 : ∀ q, deriv (g q) 0 =
      if (q : ℕ) = 0 then gammaPoleJetRegularRemainder branch 0 0 else 0 := by
    intro q
    exact (hasDerivAt_gammaPoleJetNormalizedExtension branch (q : ℕ)).deriv
  have hg2 : ∀ q, iteratedDeriv 2 (g q) 0 =
      if (q : ℕ) = 0 then 2 * deriv (gammaPoleJetRegularRemainder branch 0) 0
      else if (q : ℕ) = 1 then 2 * gammaPoleJetRegularRemainder branch 1 0 else 0 := by
    intro q
    exact iteratedDeriv_two_gammaPoleJetNormalizedExtension branch (q : ℕ)
  have hfirst' : (∑ q,
      MvPolynomial.eval (fun i => g i 0) (MvPolynomial.pderiv q P) *
        deriv (g q) 0) = 0 := by
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    · rw [hg0, hg1]
      simpa using hfirst
    · intro q _ hq
      rw [hg1]
      simp [hq]
    · simp
  have hcoord : ∀ q : Fin (n + 2),
      (fun x : ℂ => x ^ bellJetWeight (n + 2) q *
        gammaPoleCovariantJetValue branch (q : ℕ) x) =ᶠ[𝓝[≠] 0] g q := by
    intro q
    simpa [bellJetWeight, g] using
      pow_mul_gammaPoleCovariantJetValue_eventuallyEq_normalizedExtension
        branch (q : ℕ)
  have hlim := tendsto_pow_sub_two_mul_weightedJetEval_of_normalizedExtension
    P hP hW
      (fun q x => gammaPoleCovariantJetValue branch (q : ℕ) x) g hg hcoord
      (by rw [hg0]; exact hcancel) hfirst'
  have hboundary :
      (((∑ i,
          MvPolynomial.eval (fun q => g q 0) (MvPolynomial.pderiv i P) *
            iteratedDeriv 2 (g i) 0) +
        ∑ i, ∑ j,
          MvPolynomial.eval (fun q => g q 0)
              (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) *
            deriv (g j) 0 * deriv (g i) 0) / 2) =
        gammaPoleSecondSubprincipalBoundary branch n P := by
    rw [hg0]
    simp_rw [hg1, hg2]
    have hval_zero (q : Fin (n + 2)) : (q : ℕ) = 0 ↔ q = (0 : Fin (n + 2)) := by
      constructor
      · intro hq
        apply Fin.ext
        simpa using hq
      · intro hq
        subst q
        simp
    have hval_one (q : Fin (n + 2)) : (q : ℕ) = 1 ↔ q = (1 : Fin (n + 2)) := by
      constructor
      · intro hq
        apply Fin.ext
        simpa using hq
      · intro hq
        subst q
        simp
    simp_rw [hval_zero, hval_one]
    simpa [gammaPoleSecondSubprincipalBoundary] using
      mvPolynomial_secondBoundary_of_sparseJets P
        (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
        (gammaPoleJetRegularRemainder branch 0 0)
        (deriv (gammaPoleJetRegularRemainder branch 0) 0)
        (gammaPoleJetRegularRemainder branch 1 0)
  rwa [hboundary] at hlim

/-- A nonzero Gamma second boundary fixes exact covariant packet order `-(W-2)`. -/
theorem meromorphicOrderAt_gammaPoleWeightedJetEval_of_secondSubprincipal
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) P = 0)
    (hfirst : MvPolynomial.eval
        (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      gammaPoleJetRegularRemainder branch 0 0 = 0)
    (hboundary : gammaPoleSecondSubprincipalBoundary branch n P ≠ 0) :
    meromorphicOrderAt (gammaPoleWeightedJetEval branch (n + 1) P) 0 =
      ((-((W - 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  refine meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul (W - 2)
    (meromorphicAt_gammaPoleWeightedJetEval branch (n + 1) P)
    hboundary ?_
  simpa only [sub_zero] using
    tendsto_pow_sub_two_mul_gammaPoleWeightedJetEval
      branch n P hP hW hcancel hfirst

/-- The Gamma second-subprincipal limit transfers to native affine Gamma derivatives. -/
theorem tendsto_pow_sub_two_mul_gammaAffineWeightedJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) P = 0)
    (hfirst : MvPolynomial.eval
        (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      gammaPoleJetRegularRemainder branch 0 0 = 0) :
    Tendsto
      (fun x : ℂ => x ^ (W - 2) * gammaAffineWeightedJetEval branch (n + 1) P x)
      (𝓝[≠] 0)
      (𝓝 (gammaPoleSecondSubprincipalBoundary branch n P)) := by
  have hev :
      (fun x : ℂ => x ^ (W - 2) * gammaAffineWeightedJetEval branch (n + 1) P x) =ᶠ[𝓝[≠] 0]
      (fun x => x ^ (W - 2) * gammaPoleWeightedJetEval branch (n + 1) P x) :=
    (gammaAffineWeightedJetEval_eventuallyEq_covariant branch (n + 1) P).mono fun x hx =>
      congrArg (fun y => x ^ (W - 2) * y) hx
  exact (tendsto_pow_sub_two_mul_gammaPoleWeightedJetEval
    branch n P hP hW hcancel hfirst).congr' (hev.mono fun _ hx => hx.symm)

/-- The native affine Gamma packet has the same exact second-subprincipal order. -/
theorem meromorphicOrderAt_gammaAffineWeightedJetEval_of_secondSubprincipal
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) P = 0)
    (hfirst : MvPolynomial.eval
        (fun q : Fin (n + 2) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
        (MvPolynomial.pderiv (0 : Fin (n + 2)) P) *
      gammaPoleJetRegularRemainder branch 0 0 = 0)
    (hboundary : gammaPoleSecondSubprincipalBoundary branch n P ≠ 0) :
    meromorphicOrderAt (gammaAffineWeightedJetEval branch (n + 1) P) 0 =
      ((-((W - 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr
    (gammaAffineWeightedJetEval_eventuallyEq_covariant branch (n + 1) P)]
  exact meromorphicOrderAt_gammaPoleWeightedJetEval_of_secondSubprincipal
    branch n P hP hW hcancel hfirst hboundary

end

end GaloisForLFunctions
