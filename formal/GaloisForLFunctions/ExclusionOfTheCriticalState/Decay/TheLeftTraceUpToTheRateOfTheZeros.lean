import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.LogarithmicMomentsOnTheReflectedLines
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasSquaredLogarithmicEnergyOnTheLinesOfItsDecay
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroCauchyTransformIsSquareIntegrableUpToALogarithm
import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheHeatedProfileBeyondTheWallHasAMeanSquareAtTheExactRate
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheProfileBeyondTheWallInPrimeForm

/-!
# The left trace up to the rate of the zeros

On the reflected zero-free strip the continued state is the sum of the reflected
Euler multiplier, the two wall terms, and the truncated prime tail. Each term
has finite square mass with respect to unweighted Lebesgue measure. Poisson
majorization and Laplace injectivity identify the Hardy datum with the unheated
profile. Thus both the profile and the prime sum after polar subtraction lie
in weighted square mean for every exponent above the centred zero abscissa.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The squared absolute value of the Cauchy kernel on an off-centre line is a
constant multiple of the Poisson kernel. -/
private theorem memLp_div_line {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ t, ‖f t‖ ≤ C) {b : ℝ} (hb : b ≠ 0) :
    MemLp (fun t : ℝ => f t / ((b:ℂ)+(t:ℂ)*I)) 2 volume := by
  have hn (t : ℝ) : (b:ℂ)+(t:ℂ)*I ≠ 0 := by
    intro e
    exact hb (by simpa using congrArg Complex.re e)
  have hm : Continuous fun t : ℝ => f t / ((b:ℂ)+(t:ℂ)*I) := hf.div (by fun_prop) hn
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hb' := abs_pos.mpr hb
  apply (((integrable_halfPlanePoisson hb').const_mul (Real.pi/|b|)).const_mul (C^2)).mono'
    (hm.norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  change ‖‖f t / ((b:ℂ)+(t:ℂ)*I)‖^2‖ ≤ C^2 * (Real.pi/|b| * halfPlanePoisson |b| t)
  have hnorm : ‖(b:ℂ)+(t:ℂ)*I‖^2 = b^2+t^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_div, div_pow, pi_div_mul_halfPlanePoisson hb',
    sq_abs, hnorm, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC t) 2) (by positivity)

/-- On `Θ - 1/2 < c < 1/2`, the continuation at `-8-c+it` has an ordinary
square-integrable trace. No heat factor or reciprocal logarithm is needed. -/
theorem integrable_norm_sq_stateMeromorphic_reflected_line {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : zetaZeroAbscissa - 1/2 < c) (hc2 : c < 1/2) :
    Integrable fun t : ℝ =>
      ‖stateMeromorphic W₀ F (((-c:ℝ):ℂ)+(t:ℂ)*I-8)‖^2 := by
  let κ := zetaZeroAbscissa - 1/2
  have hκ : 0 ≤ κ := sub_nonneg.mpr half_le_zetaZeroAbscissa
  have hc0 : 0 < c := lt_of_le_of_lt hκ hc
  have hz (q : XiZeroCopy) : (centredZero q).re ≤ κ := by
    simpa [centredZero, κ] using sub_le_sub_right
      (re_le_zetaZeroAbscissa (riemannZeta_xiZeroCopy_eq_zero q)) (1/2)
  let p := fun t : ℝ => ((-c:ℝ):ℂ)+(t:ℂ)*I
  let r := fun t : ℝ => (c:ℂ)-(t:ℂ)*I
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hpR (t) : (p t).re = -c := by simp [p]
  have hrR (t) : (r t).re = c := by simp [r]
  have hpr (t) : -p t = r t := by dsimp [p, r]; push_cast; ring
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let L := negativeHalfLineLaplace (cx F)
  have hL : Continuous fun t => L (p t) := continuous_iff_continuousAt.mpr fun t =>
    (differentiableAt_laplace hd (by rw [hpR]; linarith)).continuousAt.comp hp.continuousAt
  have hN : Continuous fun t => zetaRegularLogDeriv (1/2+r t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (differentiableAt_zetaRegularLogDeriv_half_add hκ hz (by rwa [hrR] : κ < (r t).re)
        ).continuousAt.comp hr.continuousAt
  have euler := (memLp_two_iff_integrable_sq_norm (hN.mul hL).aestronglyMeasurable).mpr
    (integrable_norm_sq_reflected_euler_mul_laplace hW ht hF hc (by linarith))
  have hJ : Continuous fun t => levyHeadTerm F (p t) :=
    (differentiableOn_levyHeadTerm hd).continuousOn.comp_continuous hp fun t =>
      (by change (p t).re < _; rw [hpR]; linarith)
  have hT : Continuous fun t => stateTail F (p t) :=
    (differentiableOn_stateTail_strip hd).continuousOn.comp_continuous hp fun t =>
      (by change -4 < (p t).re; rw [hpR]; linarith)
  have head := (memLp_two_iff_integrable_sq_norm hJ.aestronglyMeasurable).mpr
    (integrable_norm_sq_levyHeadTerm_line hd (neg_lt_zero.mpr hc0))
  have tail := (memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).mpr
    (integrable_norm_sq_stateTail_line_of_neg_four_lt hd (by linarith : -4 < -c))
  have slope := memLp_div_line (hL.sub (continuous_const (y := L (-(1/2)))))
    (C := transformMass F (-c) + ‖L (-(1/2))‖)
    (fun t => (norm_sub_le _ _).trans (add_le_add
      (norm_laplace_le_transformMass hd (by linarith : -4 < -c) (hpR t).ge) le_rfl))
    (b := -c+1/2) (by linarith)
  have pole := memLp_div_line (continuous_const (y := L (1/2))) (fun _ => le_rfl)
    (b := -c-1/2) (by linarith)
  have hsum := (((euler.neg.sub slope).add head).sub tail).add pole
  have heq (t : ℝ) : stateMeromorphic W₀ F (p t - 8) =
      (-((-(zetaRegularLogDeriv (1/2+r t)*L (p t)) -
        (L (p t)-L (-(1/2)))/(((-c+1/2:ℝ):ℂ)+(t:ℂ)*I) + levyHeadTerm F (p t) -
        stateTail F (p t)) + L (1/2)/(((-c-1/2:ℝ):ℂ)+(t:ℂ)*I))) /
        criticalAliasCoefficient W₀ := by
    have hs : (p t) ≠ -(1/2) := by
      intro e
      have h := congrArg Complex.re e
      rw [hpR] at h
      norm_num at h
      linarith
    have e : 1/2 - p t = 1/2+r t := by rw [sub_eq_add_neg, hpr]
    have hxi : xi (1/2 + p t) ≠ 0 := by
      rw [← xi_half_sub_eq, e]
      intro h
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
      have he : centredZero q = r t := by unfold centredZero; rw [hq]; ring
      have hu := hz q
      rw [he, hrR] at hu
      exact hc.not_ge hu
    unfold stateMeromorphic
    rw [sub_add_cancel, globalRemainder_eq_stripRemainder hd
      (by rw [hpR]; linarith) (by rw [hpR]; linarith) hxi]
    unfold stripRemainder
    rw [e, logDeriv_zetaEntire_half_add_eq hκ hz (by rwa [hrR]) (by rwa [hrR]),
      dslope_of_ne _ hs, slope_def_field]
    dsimp [L, p]
    push_cast
    ring_nf
  have htrace := hsum.neg.const_mul ((criticalAliasCoefficient W₀ : ℂ))⁻¹
  refine ((memLp_two_iff_integrable_sq_norm htrace.aestronglyMeasurable).mp htrace).congr
    (Eventually.of_forall fun t => ?_)
  change ‖_ * (-_)‖^2 = ‖stateMeromorphic W₀ F (p t-8)‖^2
  simp only [heq, div_eq_mul_inv, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  rw [mul_comm ((criticalAliasCoefficient W₀ : ℂ))⁻¹]

#print axioms integrable_norm_sq_stateMeromorphic_reflected_line

/-- The square of a resolvent absorbs quadratic growth on the closed right half-plane. -/
private theorem regulated_norm_le {g : ℂ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ B*(1+‖z‖)^2)
    {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖g z / (1+(ε:ℂ)*z)^2‖ ≤ B*(1+2/ε)^2 := by
  let q := 1+(ε:ℂ)*z
  have h1 : 1 ≤ ‖q‖ := by
    have h := Complex.re_le_norm q
    have he : q.re = 1+ε*z.re := by simp [q]
    linarith only [h, he, mul_nonneg hε.le hz]
  have h2 : ε*‖z‖ ≤ ‖q‖+1 := by
    have h := norm_sub_le q 1
    simpa [q, norm_mul, Real.norm_of_nonneg hε.le] using h
  have h3 : 1+‖z‖ ≤ (1+2/ε)*‖q‖ := by
    have h4 : ‖z‖ ≤ (2/ε)*‖q‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]
      linarith only [h2, h1]
    linarith only [h1, h4]
  change ‖g z / q^2‖ ≤ _
  rw [norm_div, norm_pow, div_le_iff₀ (sq_pos_of_pos (zero_lt_one.trans_le h1))]
  calc ‖g z‖ ≤ B*(1+‖z‖)^2 := hg z hz
    _ ≤ B*((1+2/ε)*‖q‖)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) h3 2) hB
    _ = _ := by ring

/-- An ordinary square-integrable boundary trace bounds every interior line.
Regularize the quadratic growth before applying the Poisson inequality. -/
private theorem hardy_of_quadratic_bound {g : ℂ → ℂ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ g z)
    {B : ℝ} (hB : 0 ≤ B) (hg : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ B*(1+‖z‖)^2)
    (ht : Integrable fun t : ℝ => ‖g ((t:ℂ)*I)‖^2) :
    IsHalfPlaneHardy g ((2*Real.pi)⁻¹ * ∫ t : ℝ, ‖g ((t:ℂ)*I)‖^2) := by
  have hmaj (d : ℝ) (hd : 0 < d) (y : ℝ) :
      ‖g ((d:ℂ)+(y:ℂ)*I)‖^2 ≤ ∫ t : ℝ, halfPlanePoisson d (t-y)*‖g ((t:ℂ)*I)‖^2 := by
    let z := (d:ℂ)+(y:ℂ)*I
    have hreg (ε : ℝ) (hε : 0 < ε) :
        ‖g z / (1+(ε:ℂ)*z)^2‖^2 ≤
          ∫ t : ℝ, halfPlanePoisson d (t-y)*‖g ((t:ℂ)*I)‖^2 := by
      have hden (v : ℂ) (hv : 0 ≤ v.re) : 1+(ε:ℂ)*v ≠ 0 := by
        intro e
        have h := congrArg Complex.re e
        simp at h
        linarith only [h, mul_nonneg hε.le hv]
      have h' (v : ℂ) (hv : 0 ≤ v.re) : DifferentiableAt ℂ
          (fun w : ℂ => g w / (1+(ε:ℂ)*w)^2) v :=
        (hdiff v hv).div (by fun_prop) (pow_ne_zero 2 (hden v hv))
      have hJ := norm_sq_apply_le_integral_halfPlanePoisson h'
        (fun v hv => regulated_norm_le hB hg hε hv) hd y
      simp only [Complex.ofReal_zero, zero_add] at hJ
      refine hJ.trans (integral_mono_of_nonneg (Eventually.of_forall fun t =>
        mul_nonneg (halfPlanePoisson_pos hd _).le (sq_nonneg _))
        (integrable_halfPlanePoisson_sub_mul ht hd y) (Eventually.of_forall fun t => ?_))
      apply mul_le_mul_of_nonneg_left _ (halfPlanePoisson_pos hd _).le
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_div, norm_pow]
      apply div_le_self (norm_nonneg _)
      apply one_le_pow₀
      calc (1:ℝ) = (1+(ε:ℂ)*((t:ℂ)*I)).re := by simp
        _ ≤ _ := Complex.re_le_norm _
    have hm : ContinuousAt (fun ε : ℝ => ‖g z / (1+(ε:ℂ)*z)^2‖^2) 0 := by
      apply ContinuousAt.pow
      apply ContinuousAt.norm
      exact continuousAt_const.div (by fun_prop) (by simp)
    have hlim := hm.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, one_pow, div_one] using
      le_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun ε hε => hreg ε hε)
  have hc (d : ℝ) (hd : 0 < d) : Continuous fun ξ => g (rayLine d ξ) :=
    continuous_iff_continuousAt.mpr fun ξ => (hdiff _ (by simp [hd.le])).continuousAt.comp
      (by unfold rayLine; fun_prop : ContinuousAt (rayLine d) ξ)
  have hline (d : ℝ) (hd : 0 < d) :
      Integrable (fun ξ => ‖g (rayLine d ξ)‖^2) ∧
      (∫ ξ, ‖g (rayLine d ξ)‖^2) ≤ (2*Real.pi)⁻¹ * ∫ t : ℝ, ‖g ((t:ℂ)*I)‖^2 := by
    let J := fun y : ℝ => ∫ t : ℝ, halfPlanePoisson d (t-y)*‖g ((t:ℂ)*I)‖^2
    obtain ⟨hJi, hJe⟩ := integrable_integral_halfPlanePoisson_mul ht hd
    have hJ : Integrable fun ξ => J (2*Real.pi*ξ) :=
      hJi.comp_mul_left' (by positivity : 2*Real.pi ≠ 0)
    have hpt (ξ : ℝ) : ‖g (rayLine d ξ)‖^2 ≤ J (2*Real.pi*ξ) := hmaj d hd _
    have hi := hJ.mono' ((hc d hd).norm.pow 2).aestronglyMeasurable (Eventually.of_forall
      fun ξ => by simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using hpt ξ)
    refine ⟨hi, (integral_mono hi hJ hpt).trans_eq ?_⟩
    rw [Measure.integral_comp_mul_left J (2*Real.pi), abs_of_pos (by positivity), smul_eq_mul]
    exact congrArg ((2*Real.pi)⁻¹ * ·) hJe
  exact ⟨fun z hz => (hdiff z (le_of_lt hz)).differentiableWithinAt,
    fun d hd => (memLp_two_iff_integrable_sq_norm (hc d hd).aestronglyMeasurable).mpr (hline d hd).1,
    fun d hd => (hline d hd).2⟩

/-- The continued state is Hardy on the half-plane beyond a reflected zero-free line. -/
private theorem hardy_reflected_state {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : zetaZeroAbscissa - 1/2 < c) (hc2 : c < 1/2) :
    ∃ M, IsHalfPlaneHardy (fun w : ℂ => stateMeromorphic W₀ F (-(w+(c:ℂ))-8)) M := by
  let κ := zetaZeroAbscissa - 1/2
  let δ := c-κ
  have hδ : 0 < δ := sub_pos.mpr hc
  let P := fun w : ℂ => -(w+(c:ℂ))
  have hdist (w : ℂ) (hw : 0 ≤ w.re) (q : XiZeroCopy) : δ ≤ ‖P w-centredZero q‖ := by
    have h := Complex.abs_re_le_norm (P w - centredZero q)
    have h' := neg_le_abs (P w - centredZero q).re
    have hq := neg_abscissa_le_re_centredZero q
    have he : (P w-centredZero q).re = -w.re-c-(centredZero q).re := by simp [P]; ring
    rw [he] at h h'
    dsimp [δ, κ]
    linarith only [h, h', hw, hq]
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let A := ‖globalRemainder F 1‖
  let H := 3 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹^2)
  let C := 1+|c|
  have hA : 0 ≤ A := norm_nonneg _
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg (by norm_num) (halfPoleMass_nonneg F))
    (tsum_nonneg fun _ => sq_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha := criticalAliasCoefficient_positive hW
  refine ⟨_, hardy_of_quadratic_bound (B := (A+H*(1+1/δ)*C^2)/criticalAliasCoefficient W₀)
    (fun w hw => ?_) (by positivity) (fun w hw => ?_) ?_⟩
  · have he (w : ℂ) : stateMeromorphic W₀ F (-(w+(c:ℂ))-8) =
        -globalRemainder F (P w)/criticalAliasCoefficient W₀ := by
      unfold stateMeromorphic; rw [sub_add_cancel]
    simp_rw [he]
    have hP : DifferentiableAt ℂ P w := by dsimp [P]; fun_prop
    have hR := differentiableAt_globalRemainder_of_xi_ne_zero hd (xi_ne_zero_of_dist hδ (hdist w hw))
    exact ((hR.comp w hP).neg).div_const _
  · let x := 1+‖w‖
    have hx : 1 ≤ x := by dsimp [x]; linarith only [norm_nonneg w]
    have hp : 1+‖P w‖ ≤ C*x := by
      have h := norm_add_le w (c:ℂ)
      simp only [Complex.norm_real, Real.norm_eq_abs] at h
      simp only [P, norm_neg, C, x]
      nlinarith only [h, mul_nonneg (abs_nonneg c) (norm_nonneg w)]
    have hd' : 1+‖P w‖/δ ≤ (1+1/δ)*(1+‖P w‖) := by
      rw [div_eq_mul_inv, one_div]
      have hi : 0 ≤ δ⁻¹ := by positivity
      nlinarith only [hi, norm_nonneg (P w)]
    have hq : (1+‖P w‖)*(1+‖P w‖/δ) ≤ (1+1/δ)*(C*x)^2 := by
      calc _ ≤ (C*x)*((1+1/δ)*(C*x)) :=
          mul_le_mul hp (hd'.trans (mul_le_mul_of_nonneg_left hp (by positivity)))
            (by positivity) (mul_nonneg hC (zero_le_one.trans hx))
        _ = _ := by ring
    have hbound := norm_globalRemainder_le_of_dist hd hδ (hdist w hw)
    change ‖globalRemainder F (P w)‖ ≤ A + H*((1+‖P w‖)*(1+‖P w‖/δ)) at hbound
    unfold stateMeromorphic
    rw [sub_add_cancel, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha.le]
    change ‖globalRemainder F (P w)‖ / criticalAliasCoefficient W₀ ≤ _ * x^2
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith only [hbound, mul_le_mul_of_nonneg_left hq hH,
      mul_le_mul_of_nonneg_left (one_le_pow₀ hx (n := 2)) hA]
  · have hi := (integrable_norm_sq_stateMeromorphic_reflected_line hW ht hF hc hc2).comp_neg
    refine hi.congr (Eventually.of_forall fun t => ?_)
    change ‖stateMeromorphic W₀ F (((-c:ℝ):ℂ)+((-t:ℝ):ℂ)*I-8)‖^2 = _
    have e : ((-c:ℝ):ℂ)+((-t:ℝ):ℂ)*I = -((t:ℂ)*I+(c:ℂ)) := by push_cast; ring
    rw [e]

/-- In the reflected zero-free strip the actual profile has finite damped square
mass. The Hardy datum agrees with the prime and archimedean profile by injectivity
of the Laplace transform on a common half-plane. -/
theorem memLp_damped_beyondWallProfile_of_lt_half {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : zetaZeroAbscissa-1/2 < c) (hc2 : c < 1/2) :
    MemLp (fun x : ℝ => expRay (c:ℂ) x *
      beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x)
      2 (volume.restrict (Ioi (0:ℝ))) := by
  obtain ⟨M, hhard⟩ := hardy_reflected_state hW ht hF hc hc2
  let G := fun w : ℂ => stateMeromorphic W₀ F (-(w+(c:ℂ))-8)
  let f := hardyDatum G hhard
  have hf : MemLp f 2 (volume.restrict (Ioi (0:ℝ))) := memLp_two_hardyDatum hhard
  let hd := criticalHalfLineEnergyDomain_of_groundState hF
  let U : ℝ → ℂ := unitLeftDatum W₀ hd
  let b := 1-c
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hU : MemLp U 2 (volume.restrict (Ioi (0:ℝ))) := Lp.memLp (unitLeftDatum W₀ hd)
  have hf' := (memLp_two_rayDamp hf hb).restrict (s := Ioi (0:ℝ))
  have heq : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), rayDamp f b x - U x = 0 := by
    apply ae_eq_zero_of_laplaceRay_eq_zero (hf'.sub hU)
    intro w hw
    have hwb : 0 < (w+(b:ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
    have hs : laplaceRay (rayDamp f b) w = laplaceRay f (w+(b:ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [rayDamp, indicator_of_mem hx, expRay]
      rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
    have he : laplaceRay f (w+(b:ℂ)) = laplaceRay U w := by
      rw [← isHalfPlaneHardy_eq_laplaceRay hhard hwb]
      have ea : (w+(b:ℂ))+(c:ℂ) = w+1 := by dsimp [b]; push_cast; ring
      rw [ea]
      exact stateMeromorphic_eq_laplaceRay_left hd (c := 1) (by norm_num) (by norm_num) hw
    change (∫ x in Ioi (0:ℝ), (rayDamp f b x - U x)*expRay w x) = 0
    simp_rw [sub_mul]
    rw [integral_sub (integrableOn_laplaceRay hf' hw) (integrableOn_laplaceRay hU hw)]
    exact sub_eq_zero.mpr (hs.trans he)
  apply MemLp.ae_eq _ hf
  filter_upwards [heq, ae_restrict_mem measurableSet_Ioi] with x hx hx0
  simp only [rayDamp, indicator_of_mem hx0] at hx
  change f x = expRay (c:ℂ) x * (Complex.exp (x:ℂ)*U x)
  rw [← sub_eq_zero.mp hx]
  unfold expRay
  have hh : Complex.exp (-((c:ℂ)*(x:ℂ))) * Complex.exp (x:ℂ) *
      Complex.exp (-((b:ℂ)*(x:ℂ))) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    dsimp [b]; push_cast
    rw [show -((c:ℂ)*(x:ℂ)) + x + -((1-c)*(x:ℂ)) = 0 by ring, Complex.exp_zero]
  linear_combination -(f x)*hh

#print axioms memLp_damped_beyondWallProfile_of_lt_half

/-- The unheated profile beyond the wall is in weighted square mean at every
exponent strictly greater than the centred zero abscissa. -/
theorem memLp_damped_beyondWallProfile_of_abscissa {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {d : ℝ}
    (hd : zetaZeroAbscissa-1/2 < d) :
    MemLp (fun x : ℝ => expRay (d:ℂ) x *
      beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x)
      2 (volume.restrict (Ioi (0:ℝ))) := by
  have hκ : zetaZeroAbscissa-1/2 < 1/2 := by
    by_contra! hh
    obtain ⟨ρ, hρ, hgt⟩ := exists_zetaZero_lt_re (b := 20999/24000) (by linarith)
    exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hgt hρ
  obtain ⟨c, hc, hc'⟩ := exists_between (lt_min hd hκ)
  have hcd := (lt_min_iff.mp hc').1.le
  refine (memLp_damped_beyondWallProfile_of_lt_half hW ht hF hc (lt_min_iff.mp hc').2).mono ?_ ?_
  · exact (continuous_expRay _).aestronglyMeasurable.mul (aestronglyMeasurable_beyondWallProfile _ _)
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with x hx
    rw [norm_mul, norm_mul, norm_expRay, norm_expRay, Complex.ofReal_re, Complex.ofReal_re]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hcd (le_of_lt hx)))

#print axioms memLp_damped_beyondWallProfile_of_abscissa

/-- The prime sum with its polar main term removed has finite damped square mass
at every exponent above the centred zero abscissa. -/
theorem memLp_damped_prime_sum_sub_pole_of_abscissa {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {d : ℝ}
    (hd : zetaZeroAbscissa-1/2 < d) :
    MemLp (fun x : ℝ => expRay (d:ℂ) x *
      ((∑' n : ℕ, (primeAtom n : ℂ) * (F (x-Real.log n) : ℂ)) -
        negativeHalfLineLaplace (cx F) (-(1/2)) * (Real.exp (x/2):ℂ)))
      2 (volume.restrict (Ioi (0:ℝ))) := by
  have hdom := criticalHalfLineEnergyDomain_of_groundState hF
  have hd0 : 0 < d := (sub_nonneg.mpr half_le_zetaZeroAbscissa).trans_lt hd
  have hp := (memLp_damped_beyondWallProfile_of_abscissa hW ht hF hd).const_mul
    (-(criticalAliasCoefficient W₀ : ℂ))
  have hJ := memLp_dampedLevyHeadProfile hdom hd0.le
  have hE := (memLp_two_expRay_restrict (w := (d:ℂ)+1/2) (by simp; linarith) 0).const_mul
    (negativeHalfLineLaplace (cx F) (1/2))
  refine MemLp.ae_eq ?_ ((hp.sub hJ).add hE)
  filter_upwards [beyondWallProfile_primeForm hW hdom] with x hx
  have he : expRay ((d:ℂ)+1/2) x = expRay (d:ℂ) x * (Real.exp (-(x/2)):ℂ) := by
    unfold expRay
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  change -(criticalAliasCoefficient W₀ : ℂ)*(expRay (d:ℂ) x*beyondWallProfile W₀ hdom x)
    - levyHeadProfile F x * expRay (d:ℂ) x +
      negativeHalfLineLaplace (cx F) (1/2)*expRay ((d:ℂ)+1/2) x = _
  rw [he]
  linear_combination (expRay (d:ℂ) x)*hx.2

#print axioms memLp_damped_prime_sum_sub_pole_of_abscissa

end GaloisForLFunctions.ExclusionOfTheCriticalState
