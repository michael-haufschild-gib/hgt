import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleDiagonalBounds
import GaloisForLFunctions.RHTower.CCMUnitRieszResolventRHCriterion

/-!
# The literal two-exponential pole criterion for RH

The actual pole matrix bounds the admitted logarithmic Chebyshev deficit at
square-root scale. Absolutely continuous integration by parts transports this
bound to the corpus's unit-Riesz resolvent, retaining the exact past-tail
normalization. Its existing analytic continuation theorem then gives RH.
Conversely, RH gives positivity on the smooth actual source core and density
extends it to the complete Weil form. Thus two literal parity poles at every
aperture are an exact RH test, equivalent to one explicit prime–Gamma matrix
inequality. That inequality is not proved here.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.RHTower
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- The ordinary primitive of the full Chebyshev deficit in logarithmic radius. -/
def ccmLogChebyshevDeficitPrimitive (T : ℝ) : ℝ :=
  ∫ t in 0..T, Real.exp t-Chebyshev.psi (Real.exp t)

private theorem deficit_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp t-Chebyshev.psi (Real.exp t)) volume a b := by
  exact (Real.continuous_exp.intervalIntegrable a b).sub
    ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)

/-- The physical pole deficit is exactly the logarithmic primitive at twice the aperture. -/
theorem ccmPoleIntegratedChebyshevDeficit_eq_logPrimitive (a : SuzukiPositiveAperture) :
    ccmPoleIntegratedChebyshevDeficit a=ccmLogChebyshevDeficitPrimitive (2*a.1) := by
  rw [ccmPoleIntegratedChebyshevDeficit,ccmLogChebyshevDeficitPrimitive,centralInterval,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -a.1≤a.1 by linarith [a.property]),
    intervalIntegral.integral_comp_sub_left (fun t => Real.exp t-Chebyshev.psi (Real.exp t))]
  rw [sub_self,show a.1-(-a.1)=2*a.1 by ring]

/-- Positivity of all literal pole matrices gives one uniform bound for the
logarithmic Chebyshev primitive on the full nonnegative ray. -/
theorem ccmLogChebyshevDeficitPrimitive_bound_of_poleCompression
    (h : ∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a|≤ccmWeilPoleDiagonal a)
    {T : ℝ} (hT : 0≤T) :
    |ccmLogChebyshevDeficitPrimitive T| ≤ ccmWeilPoleUniformDeficitBound*Real.exp (T/2) := by
  rcases eq_or_lt_of_le hT with hzero | hpos
  · rw [← hzero,ccmLogChebyshevDeficitPrimitive,intervalIntegral.integral_same,abs_zero]
    exact mul_nonneg ccmWeilPoleUniformDeficitBound_pos.le (Real.exp_pos _).le
  · let a : SuzukiPositiveAperture := ⟨T/2,by linarith⟩
    have hb := abs_ccmPoleIntegratedChebyshevDeficit_le_of_compression_nonneg a (h a)
    rw [ccmPoleIntegratedChebyshevDeficit_eq_logPrimitive] at hb
    change |ccmLogChebyshevDeficitPrimitive (2*(T/2))|≤ccmWeilPoleUniformDeficitBound*Real.exp (T/2) at hb
    rwa [show 2*(T/2)=T by ring] at hb

/-- Exact integration-by-parts transfer from the admitted unweighted deficit
primitive to the corpus unit-Riesz Chebyshev ray integral. -/
theorem unitRieszChebyshevRayIntegral_eq_deficitPrimitive {T : ℝ} (hT : 0≤T) :
    unitRieszChebyshevRayIntegral T =
      -Real.exp (T/2)*ccmLogChebyshevDeficitPrimitive T+
        (1/2)*(∫ t in 0..T, Real.exp (t/2)*ccmLogChebyshevDeficitPrimitive t) := by
  let E : ℝ → ℝ := fun t => Real.exp (t/2)
  let P : ℝ → ℝ := ccmLogChebyshevDeficitPrimitive
  let f : ℝ → ℝ := fun t => Real.exp t-Chebyshev.psi (Real.exp t)
  have hi : IntervalIntegrable f volume 0 T := deficit_intervalIntegrable 0 T
  have hPac : AbsolutelyContinuousOnInterval P 0 T :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (show (0:ℝ)∈uIcc 0 T by simp [hT])
  have hEcd : ContDiff ℝ 1 E := by dsimp [E];fun_prop
  have hEac : AbsolutelyContinuousOnInterval E 0 T :=
    hEcd.contDiffOn.absolutelyContinuousOnInterval
  have hparts := hEac.integral_mul_deriv_eq_deriv_mul hPac
  have hleft : (∫ t in 0..T, E t*deriv P t) = ∫ t in 0..T, E t*f t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    have hd : HasDerivAt P (f t) t := ht (uIoc_subset_uIcc hmem) 0 (by simp [hT])
    rw [hd.deriv]
  have hright : (∫ t in 0..T, deriv E t*P t) = (1/2)*(∫ t in 0..T, E t*P t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    have hd : HasDerivAt E ((1/2)*E t) t := by
      dsimp only [E]
      convert! ((hasDerivAt_id t).div_const 2).exp using 1; simp only [id_eq]; ring
    change deriv E t*P t=(1/2)*(E t*P t)
    rw [hd.deriv]
    ring
  have hP0 : P 0=0 := by simp [P,ccmLogChebyshevDeficitPrimitive]
  rw [hleft,hright,hP0,mul_zero,sub_zero] at hparts
  have hraw : unitRieszChebyshevRayIntegral T=-(∫ t in 0..T, E t*f t) := by
    rw [unitRieszChebyshevRayIntegral,← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    change Real.exp t*criticalMellinNormalizedChebyshevError t=-(E t*f t)
    rw [criticalMellinNormalizedChebyshevError_eq_apertureError,criticalMellinChebyshevError_eq_exp]
    dsimp [E,f]
    have he : Real.exp t*Real.exp (-t/2)=Real.exp (t/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp t*Real.exp (-t/2))*(Chebyshev.psi (Real.exp t)-Real.exp t) := by ring
      _ = _ := by rw [he];ring
  rw [hraw]
  dsimp only [E,P] at hparts
  linarith

private theorem weighted_deficit_integral_bound {B T : ℝ}
    (hB : ∀ t : ℝ, 0≤t → |ccmLogChebyshevDeficitPrimitive t|≤B*Real.exp (t/2)) (hT : 0≤T) :
    |∫ t in 0..T, Real.exp (t/2)*ccmLogChebyshevDeficitPrimitive t| ≤ B*(Real.exp T-1) := by
  have hmajor : IntervalIntegrable (fun t : ℝ => B*Real.exp t) volume 0 T :=
    (Real.continuous_exp.const_mul B).intervalIntegrable 0 T
  have hb := intervalIntegral.norm_integral_le_of_norm_le (f:=fun t =>
    Real.exp (t/2)*ccmLogChebyshevDeficitPrimitive t) hT (show ∀ᵐ t ∂volume,
      t∈Ioc 0 T → ‖Real.exp (t/2)*ccmLogChebyshevDeficitPrimitive t‖≤B*Real.exp t from by
    filter_upwards [] with t ht
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (t/2)*(B*Real.exp (t/2)) :=
        mul_le_mul_of_nonneg_left (hB t ht.1.le) (Real.exp_pos _).le
      _ = _ := by rw [show Real.exp (t/2)*(B*Real.exp (t/2))=
        B*(Real.exp (t/2)*Real.exp (t/2)) by ring,← Real.exp_add];congr 2;ring) hmajor
  rw [Real.norm_eq_abs,intervalIntegral.integral_const_mul,integral_exp,Real.exp_zero] at hb
  exact hb

/-- A square-root-scale logarithmic primitive bounds the complete unit-Riesz ray integral. -/
theorem abs_unitRieszChebyshevRayIntegral_le_of_deficitPrimitive_bound {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ t : ℝ, 0≤t → |ccmLogChebyshevDeficitPrimitive t|≤B*Real.exp (t/2))
    {T : ℝ} (hT : 0≤T) :
    |unitRieszChebyshevRayIntegral T| ≤ (3/2)*B*Real.exp T := by
  have hi := abs_le.mp (weighted_deficit_integral_bound hB hT)
  have hp : |Real.exp (T/2)*ccmLogChebyshevDeficitPrimitive T|≤B*Real.exp T := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (T/2)*(B*Real.exp (T/2)) :=
        mul_le_mul_of_nonneg_left (hB T hT) (Real.exp_pos _).le
      _ = _ := by rw [show Real.exp (T/2)*(B*Real.exp (T/2))=
        B*(Real.exp (T/2)*Real.exp (T/2)) by ring,← Real.exp_add];congr 2;ring
  obtain ⟨hpL,hpR⟩ := abs_le.mp hp
  rw [unitRieszChebyshevRayIntegral_eq_deficitPrimitive hT]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The exact past-tail normalization is retained when the primitive bound is
transported to the actual unit-Riesz Chebyshev resolvent. -/
theorem abs_criticalMellinChebyshevResolventSource_le_of_deficitPrimitive_bound
    {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ t : ℝ, 0≤t → |ccmLogChebyshevDeficitPrimitive t|≤B*Real.exp (t/2))
    {T : ℝ} (hT : 0≤T) :
    |criticalMellinChebyshevResolventSource T| ≤ (3/2)*B+2/3 := by
  have hray := abs_le.mp (abs_unitRieszChebyshevRayIntegral_le_of_deficitPrimitive_bound hB0 hB hT)
  have hid := unitRieszChebyshevRayIntegral_eq_fullResolvent hT
  have he := Real.exp_pos T
  have he1 : 1≤Real.exp T := Real.one_le_exp hT
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- The admitted square-root-scale logarithmic prime-error bound closes RH
through the corpus's actual unit-Riesz analytic continuation criterion. -/
theorem riemannHypothesis_of_logChebyshevDeficitPrimitive_bound {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ t : ℝ, 0≤t → |ccmLogChebyshevDeficitPrimitive t|≤B*Real.exp (t/2)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_criticalMellinChebyshevResolventSource
    (B:=(3/2)*B+2/3) (by positivity)
  exact fun t ht => abs_criticalMellinChebyshevResolventSource_le_of_deficitPrimitive_bound hB0 hB ht

/-- Positivity of the literal real-exponential two-pole compression at every
aperture is sufficient for RH. The source sign is the sole remaining antecedent. -/
theorem riemannHypothesis_of_weilPoleCompression_nonneg
    (h : ∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a|≤ccmWeilPoleDiagonal a) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_logChebyshevDeficitPrimitive_bound
    ccmWeilPoleUniformDeficitBound_pos.le
    (fun t ht => ccmLogChebyshevDeficitPrimitive_bound_of_poleCompression h ht)

/-- False RH forces failure of the explicit actual pole-matrix comparison. -/
theorem not_riemannHypothesis_implies_exists_negative_weilPoleCompression
    (hRH : ¬RiemannHypothesis) :
    ∃ a : SuzukiPositiveAperture, ccmWeilPoleDiagonal a < |ccmWeilPoleCross a| := by
  by_contra h
  push Not at h
  exact hRH (riemannHypothesis_of_weilPoleCompression_nonneg h)

/-- Under false RH, one literal even or odd exponential pole test has negative
full Weil energy. This is an actual source witness, not an abstract model. -/
theorem not_riemannHypothesis_implies_exists_negative_parityPole
    (hRH : ¬RiemannHypothesis) :
    ∃ (a : SuzukiPositiveAperture) (r : ℝ), (r=1 ∨ r=-1) ∧
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r)<0 := by
  obtain ⟨a,ha⟩ := not_riemannHypothesis_implies_exists_negative_weilPoleCompression hRH
  by_cases hC : 0≤ccmWeilPoleCross a
  · refine ⟨a,-1,Or.inr rfl,?_⟩
    rw [ccmWeilPoleCompression_parity_energy a (Or.inr rfl)]
    rw [abs_of_nonneg hC] at ha
    linarith
  · refine ⟨a,1,Or.inl rfl,?_⟩
    rw [ccmWeilPoleCompression_parity_energy a (Or.inl rfl)]
    rw [abs_of_neg (lt_of_not_ge hC)] at ha
    linarith

/-- RH makes the complete actual restricted Weil quadratic nonnegative: the
corpus's exact smooth-source identity extends through its dense form core. -/
theorem ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    0≤ccmRestrictedWeilSourceQuadratic a u := by
  have hc : IsClosed {v : CCMArchimedeanFormDomain a | 0≤ccmRestrictedWeilSourceQuadratic a v} :=
    isClosed_le continuous_const (continuous_ccmRestrictedWeilSourceQuadratic a)
  have hs : Set.range (fun v : CCMComplexSmoothInteriorSource a => v.toCCMFormVector) ⊆
      {v : CCMArchimedeanFormDomain a | 0≤ccmRestrictedWeilSourceQuadratic a v} := by
    rintro _ ⟨v,rfl⟩
    change 0≤ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector
    rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm]
    exact suzukiSmoothTestFormNonnegative_of_riemannHypothesis hRH a.1 a.2 _
  have hh := closure_minimal hs hc
  rw [closure_range_ccmComplexSmoothInteriorSource_toCCMFormVector] at hh
  exact hh (Set.mem_univ u)

/-- RH is exactly positivity of the literal two real-exponential poles at every
aperture. No moving complex parameters or general source tests remain in this criterion. -/
theorem riemannHypothesis_iff_weilPoleCompression_nonneg :
    RiemannHypothesis ↔
      ∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a|≤ccmWeilPoleDiagonal a := by
  constructor
  · intro hRH a
    apply (ccmWeilPoleCompression_nonneg_iff a).mp
    intro c d
    exact ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a _
  · exact riemannHypothesis_of_weilPoleCompression_nonneg

/-- Equivalent two-test form of the exact fixed-exponential RH criterion. -/
theorem riemannHypothesis_iff_parityPole_nonneg :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture,
      0≤ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ∧
      0≤ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) := by
  simp only [riemannHypothesis_iff_weilPoleCompression_nonneg,
    ccmWeilPoleCompression_nonneg_iff_parity]

/-- RH is exactly a square-root-scale bound on the ordinary logarithmic
primitive of the actual Chebyshev error, with no logarithmic loss. -/
theorem riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound :
    RiemannHypothesis ↔ ∃ B : ℝ, 0≤B ∧ ∀ t : ℝ, 0≤t →
      |ccmLogChebyshevDeficitPrimitive t|≤B*Real.exp (t/2) := by
  constructor
  · intro hRH
    exact ⟨ccmWeilPoleUniformDeficitBound,ccmWeilPoleUniformDeficitBound_pos.le,
      fun t ht => ccmLogChebyshevDeficitPrimitive_bound_of_poleCompression
        (riemannHypothesis_iff_weilPoleCompression_nonneg.mp hRH) ht⟩
  · rintro ⟨B,hB0,hB⟩
    exact riemannHypothesis_of_logChebyshevDeficitPrimitive_bound hB0 hB

/-- The complete fixed-pole RH criterion expressed in its literal prime–Gamma
arithmetic entries, with every visible prime power and boundary mass retained. -/
theorem riemannHypothesis_iff_primeGammaPoleInequality :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture,
      |(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*a.1)+2*a.1^2+
        (2*Real.sinh a.1)^2+ccmGammaPoleCrossBoundaryMass a-ccmPolarPrimeTent a| ≤
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*Real.sinh a.1)-
        Real.exp a.1+(1-2*a.1)*Real.exp (-a.1)+ccmGammaPoleSelfBoundaryMass a-
        2*Real.exp a.1*ccmReciprocalMangoldtError (2*a.1)+
        2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1)) := by
  rw [riemannHypothesis_iff_weilPoleCompression_nonneg]
  simp only [ccmWeilPoleCross_eq,ccmWeilPoleDiagonal_eq_error]

end RHTower
