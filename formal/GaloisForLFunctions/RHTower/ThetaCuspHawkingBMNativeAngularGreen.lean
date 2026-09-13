import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeModularTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularCuspCutoff
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoreTestData
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullNativeWave
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Joint angular regularity and compact Green identity for the literal native time primitive.

Compact continuous integration parameters retain smoothness in the angular variables.
Signed unit-cube rescaling applies this to the full causal response, preserving the
characteristic radius, odd source, and three principal cutoff amplitudes. Uniform modular
germs construct the actual smooth primitive extension. Nested cusp cutoffs then give
angular integration by parts with integrable pairings before global energy admission.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

namespace RHTower.D4BMNativeResponse
variable {E P K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [T2Space K] {μ : Measure K} [IsLocallyFiniteMeasure μ]
  {S : Set K} (hS : IsCompact S) (gamma : K → P) (hgamma : Continuous gamma)

private def partialMap {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E × P → G) (p : E × P) : E →L[ℝ] G :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E P)

omit [FiniteDimensional ℝ E] in
private theorem partialMap_smooth {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × P → G} {n : ℕ} (hf : ContDiff ℝ (n+1) f) :
    ContDiff ℝ n (partialMap f) := by
  have hh : ContDiff ℝ ((n : WithTop ℕ∞)+1) f := by exact_mod_cast hf
  exact (hh.fderiv_right le_rfl).clm_comp contDiff_const

omit [FiniteDimensional ℝ E] in
private theorem partialMap_derivative {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × P → G} (hf : ContDiff ℝ 1 f) (x : E) (p : P) :
    HasFDerivAt (fun y => f (y,p)) (partialMap f (x,p)) x := by
  exact ((hf.differentiable (by norm_num) (x,p)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const p x))

include hS hgamma in
private theorem compact_integral_first {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ 1 f) (x : E) :
    HasFDerivAt (fun y => ∫ k in S, f (y,gamma k) ∂μ)
      (∫ k in S, partialMap f (x,gamma k) ∂μ) x := by
  have hc : Continuous (fun q : E × K => f (q.1,gamma q.2)) :=
    hf.continuous.comp (continuous_fst.prodMk (hgamma.comp continuous_snd))
  have hd : Continuous (fun q : E × K => partialMap f (q.1,gamma q.2)) :=
    (partialMap_smooth (n := 0) hf).continuous.comp
      (continuous_fst.prodMk (hgamma.comp continuous_snd))
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hS).exists_bound_of_continuousOn hd.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y =>
      ((hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).restrict)
  · exact ((hc.comp (continuous_const.prodMk continuous_id)).continuousOn).integrableOn_compact hS
  · exact ((hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with k hk
    intro y hy
    exact hC (y,k) ⟨hy,hk⟩
  · exact integrableOn_const hS.measure_ne_top
  · exact Eventually.of_forall (fun k y _ => partialMap_derivative hf y (gamma k))

include hS hgamma in
private theorem compact_integral_smooth (n : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {f : E × P → G}, ContDiff ℝ n f →
      ContDiff ℝ n (fun y => ∫ k in S, f (y,gamma k) ∂μ) := by
  induction n with
  | zero =>
    intro G _ _ _ f hf
    apply contDiff_zero.mpr
    apply continuous_parametric_integral_of_continuous _ hS
    exact hf.continuous.comp (continuous_fst.prodMk (hgamma.comp continuous_snd))
  | succ n ih =>
    intro G _ _ _ f hf
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨(fun x => ∫ k in S, partialMap f (x,gamma k) ∂μ),?_,?_⟩
    · exact ih (partialMap_smooth hf)
    · intro x
      exact compact_integral_first hS gamma hgamma hf1 x

include hS hgamma in
private theorem compact_integral_infty {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => ∫ k in S, f (y,gamma k) ∂μ) :=
  contDiff_infty.mpr (fun n => compact_integral_smooth hS gamma hgamma n (contDiff_infty.mp hf n))

private theorem interval_integral_infty {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ ∞ f)
    (γ : ℝ → P) (hγ : Continuous γ) (a b : ℝ) :
    ContDiff ℝ ∞ (fun y => ∫ k in a..b, f (y,γ k)) := by
  have h := compact_integral_infty (μ := volume) (S := uIcc a b) isCompact_uIcc γ hγ hf
  have he (y : E) : (∫ k in a..b, f (y,γ k)) =
      (if a ≤ b then (1 : ℝ) else -1) • ∫ k in uIcc a b, f (y,γ k) := by
    by_cases hab : a ≤ b
    · simp [hab, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    · have hba : b ≤ a := le_of_not_ge hab
      simp [hab, uIcc_of_ge hba, intervalIntegral.integral_of_ge hba, integral_Icc_eq_integral_Ioc]
  simpa only [he] using h.const_smul (if a ≤ b then (1 : ℝ) else -1)

private theorem double_integral_infty {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ ∞ f)
    (γ : ℝ × ℝ → P) (hγ : Continuous γ) :
    ContDiff ℝ ∞ (fun y => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, f (y,γ (a,b))) := by
  have h := compact_integral_infty (μ := volume.prod volume)
    (S := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (isCompact_Icc.prod isCompact_Icc) γ hγ hf
  convert! h using 1
  funext y
  have hi : Integrable (fun k : ℝ × ℝ => f (y,γ k))
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuous.comp (continuous_const.prodMk hγ)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [← Measure.prod_restrict, integral_prod _ hi]
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

private theorem triple_integral_infty {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ ∞ f)
    (γ : ℝ × ℝ × ℝ → P) (hγ : Continuous γ) :
    ContDiff ℝ ∞ (fun y => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1, f (y,γ (a,b,c))) := by
  have h := compact_integral_infty (μ := volume.prod (volume.prod volume))
    (S := Icc (0:ℝ) 1 ×ˢ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1))
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) γ hγ hf
  convert! h using 1
  funext y
  have hi : Integrable (fun k : ℝ × ℝ × ℝ => f (y,γ k))
      ((volume.restrict (Icc (0:ℝ) 1)).prod
        ((volume.prod volume).restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuous.comp (continuous_const.prodMk hγ)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  rw [← Measure.prod_restrict, integral_prod _ hi]
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards with a
  have hj : Integrable (fun k : ℝ × ℝ => f (y,γ (a,k)))
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuous.comp
      (continuous_const.prodMk (hγ.comp (continuous_const.prodMk continuous_id)))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [← Measure.prod_restrict, integral_prod _ hj]
  simp only [integral_Icc_eq_integral_Ioc]


/-- A globally smooth integrand remains smooth after substitution of continuous
parameters and integration over the fixed unit cube. -/
theorem unitCube_integral_smooth {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ ∞ f)
    (γ : ℝ × ℝ × ℝ → P) (hγ : Continuous γ) :
    ContDiff ℝ ∞ (fun y => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1,
      ∫ c in (0:ℝ)..1, f (y,γ (a,b,c))) :=
  triple_integral_infty hf γ hγ

open GaloisForLFunctions.HTGeometry
open RHTower
open RHTower.D4BMNativeResponse RHTower.D4BMNativeCircle RHTower.D4BMCausalKernel
open RHTower.D4BMJointSource RHTower.D4BMModularCore

private def angularCircle (q : XiZeroCopy) (d X k : ℝ) : ℂ :=
  (1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..(2*Real.pi), source q d theta X k

private theorem angularCircle_smooth (q : XiZeroCopy) :
    ContDiff ℝ ∞ (fun v : ℝ × ℝ × ℝ => angularCircle q v.1 v.2.1 v.2.2) := by
  have hf : ContDiff ℝ ∞ (fun v : (ℝ × ℝ × ℝ) × ℝ =>
      source q v.1.1 v.2 v.1.2.1 v.1.2.2) :=
    by
      have h := (source_smooth q).comp
        (show ContDiff ℝ ∞ (fun v : (ℝ × ℝ × ℝ) × ℝ =>
          (![v.1.1,v.2,v.1.2.1,v.1.2.2] : Fin 4 → ℝ)) by
          apply contDiff_pi.mpr
          intro i
          fin_cases i
          · change ContDiff ℝ ∞ (fun v : (ℝ × ℝ × ℝ) × ℝ => v.1.1)
            fun_prop
          · change ContDiff ℝ ∞ (fun v : (ℝ × ℝ × ℝ) × ℝ => v.2)
            fun_prop
          · change ContDiff ℝ ∞ (fun v : (ℝ × ℝ × ℝ) × ℝ => v.1.2.1)
            fun_prop
          · change ContDiff ℝ ∞ (fun v : (ℝ × ℝ × ℝ) × ℝ => v.1.2.2)
            fun_prop)
      convert! h using 1
  exact contDiff_const.mul (interval_integral_infty hf id continuous_id 0 (2*Real.pi))

private def angularRadius (p r a b : ℝ) : ℝ :=
  Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)))

private theorem angularRadius_continuous :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => angularRadius z.1.1 z.1.2 z.2.1 z.2.2) := by
  apply Real.continuousOn_arcosh.comp_continuous
  · unfold invariant
    apply Continuous.max continuous_const
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  · intro z
    exact le_max_left (1:ℝ) _

private theorem oddSource_joint_continuous (s amplitude : ℂ) :
    Continuous (fun z : ℝ × ℝ => oddSource s amplitude z.1 z.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  exact h₁.sub h₂

private theorem fullNullResponse_angular_formula (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) : fullNullResponse q s amplitude p r X k =
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        angularCircle q (angularRadius p r a b) X k*
          oddSource s amplitude ((a+b)/2) ((a-b)/2) := by rfl

private theorem angularCircle_weighted_smooth (q : XiZeroCopy) :
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (ℝ × ℂ) =>
      angularCircle q z.2.1 z.1.1 z.1.2*z.2.2) :=
  by
    have h := (angularCircle_smooth q).comp
      (show ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (ℝ × ℂ) => (z.2.1,z.1.1,z.1.2)) by fun_prop)
    exact h.mul (by fun_prop)

private theorem unit_rescale (f : ℝ → ℂ) (b : ℝ) :
    (∫ u in (0:ℝ)..b, f u) = ∫ u in (0:ℝ)..1, (b:ℂ)*f (b*u) := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [mul_zero,mul_one,Complex.real_smul] using
    (intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1) f b).symm

private theorem fullNullResponse_unit_formula (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) : fullNullResponse q s amplitude p r X k =
      (1/4:ℂ)*∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1,
        angularCircle q (angularRadius p r (p*a) (r*b)) X k*
          ((p:ℂ)*(r:ℂ)*oddSource s amplitude ((p*a+r*b)/2) ((p*a-r*b)/2)) := by
  rw [fullNullResponse_angular_formula,unit_rescale]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  dsimp only
  rw [unit_rescale,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro b hb
  ring

/-- The literal causal response is jointly smooth in both angular coordinates,
including when its source rectangle crosses a characteristic edge. -/
theorem fullNullResponse_angular_smooth (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => fullNullResponse q s amplitude p r z.1 z.2) := by
  have hr : Continuous (fun z : ℝ × ℝ => angularRadius p r (p*z.1) (r*z.2)) :=
    by
      have h := angularRadius_continuous.comp
        (show Continuous (fun z : ℝ × ℝ => ((p,r),(p*z.1,r*z.2))) by fun_prop)
      convert! h using 1
  have hc : Continuous (fun z : ℝ × ℝ =>
      (p:ℂ)*(r:ℂ)*oddSource s amplitude ((p*z.1+r*z.2)/2) ((p*z.1-r*z.2)/2)) :=
    by
      have hs := (oddSource_joint_continuous s amplitude).comp
        (show Continuous (fun z : ℝ × ℝ => ((p*z.1+r*z.2)/2,(p*z.1-r*z.2)/2)) by fun_prop)
      have cc : Continuous (fun _ : ℝ × ℝ => (p:ℂ)*(r:ℂ)) := continuous_const
      convert! cc.mul hs using 1
  have h := double_integral_infty (angularCircle_weighted_smooth q) _ (hr.prodMk hc)
  have hcst : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1/4:ℂ)) := contDiff_const
  convert! hcst.mul h using 1
  funext z
  exact fullNullResponse_unit_formula q s amplitude p r z.1 z.2

private theorem full_time_unit_formula (q : XiZeroCopy) (s amplitude : ℂ)
    (t x X k : ℝ) :
    (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ)*fullNullResponse q s amplitude (u+x) (u-x) X k) =
    (1/4:ℂ)*∫ u in (0:ℝ)..1, ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1,
      angularCircle q (angularRadius (t*u+x) (t*u-x) ((t*u+x)*a) ((t*u-x)*b)) X k*
      ((t:ℂ)*((t-t*u:ℝ):ℂ)*((t*u+x:ℝ):ℂ)*((t*u-x:ℝ):ℂ)*
        oddSource s amplitude (((t*u+x)*a+(t*u-x)*b)/2) (((t*u+x)*a-(t*u-x)*b)/2)) := by
  rw [unit_rescale,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [fullNullResponse_unit_formula]
  simp_rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro a ha
  dsimp only
  apply intervalIntegral.integral_congr
  intro b hb
  dsimp only
  ring

private theorem full_time_angular_smooth (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => ∫ u in (0:ℝ)..t,
      ((t-u:ℝ):ℂ)*fullNullResponse q s amplitude (u+x) (u-x) z.1 z.2) := by
  have hr : Continuous (fun z : ℝ × ℝ × ℝ =>
      angularRadius (t*z.1+x) (t*z.1-x) ((t*z.1+x)*z.2.1) ((t*z.1-x)*z.2.2)) :=
    by
      have h := angularRadius_continuous.comp
        (show Continuous (fun z : ℝ × ℝ × ℝ =>
          ((t*z.1+x,t*z.1-x),((t*z.1+x)*z.2.1,(t*z.1-x)*z.2.2))) by fun_prop)
      convert! h using 1
  have hc : Continuous (fun z : ℝ × ℝ × ℝ =>
      (t:ℂ)*((t-t*z.1:ℝ):ℂ)*((t*z.1+x:ℝ):ℂ)*((t*z.1-x:ℝ):ℂ)*
        oddSource s amplitude (((t*z.1+x)*z.2.1+(t*z.1-x)*z.2.2)/2)
          (((t*z.1+x)*z.2.1-(t*z.1-x)*z.2.2)/2)) :=
    by
      have hs := (oddSource_joint_continuous s amplitude).comp
        (show Continuous (fun z : ℝ × ℝ × ℝ =>
          (((t*z.1+x)*z.2.1+(t*z.1-x)*z.2.2)/2,
           ((t*z.1+x)*z.2.1-(t*z.1-x)*z.2.2)/2)) by fun_prop)
      have cc : Continuous (fun z : ℝ × ℝ × ℝ =>
        (t:ℂ)*((t-t*z.1:ℝ):ℂ)*((t*z.1+x:ℝ):ℂ)*((t*z.1-x:ℝ):ℂ)) := by fun_prop
      convert! cc.mul hs using 1
  have h := triple_integral_infty (angularCircle_weighted_smooth q) _ (hr.prodMk hc)
  have hcst : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1/4:ℂ)) := contDiff_const
  convert! hcst.mul h using 1
  funext z
  exact full_time_unit_formula q s amplitude t x z.1 z.2

private theorem angularRadius_comp {Q : Type*} [TopologicalSpace Q]
    (p r a b : Q → ℝ) (hp : Continuous p) (hr : Continuous r)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun z => angularRadius (p z) (r z) (a z) (b z)) := by
  have h := angularRadius_continuous.comp ((hp.prodMk hr).prodMk (ha.prodMk hb))
  convert! h using 1
attribute [fun_prop] angularRadius_comp

private theorem angularCircle_comp {Q : Type*} [TopologicalSpace Q]
    (q : XiZeroCopy) (d X k : Q → ℝ) (hd : Continuous d)
    (hX : Continuous X) (hk : Continuous k) :
    Continuous (fun z => angularCircle q (d z) (X z) (k z)) := by
  have h := (angularCircle_smooth q).continuous.comp (hd.prodMk (hX.prodMk hk))
  convert! h using 1
attribute [fun_prop] angularCircle_comp

private theorem oddSource_comp {Q : Type*} [TopologicalSpace Q]
    (s amplitude : ℂ) (u x : Q → ℝ) (hu : Continuous u) (hx : Continuous x) :
    Continuous (fun z => oddSource s amplitude (u z) (x z)) := by
  have h := (oddSource_joint_continuous s amplitude).comp (hu.prodMk hx)
  convert! h using 1
attribute [fun_prop] oddSource_comp

private theorem full_time_continuous (q : XiZeroCopy) (s amplitude : ℂ) (x X k : ℝ) :
    Continuous (fun u : ℝ => fullNullResponse q s amplitude (u+x) (u-x) X k) := by
  simp only [fullNullResponse_unit_formula]
  fun_prop

private theorem principal_time_continuous (q : XiZeroCopy) (s amplitude : ℂ) (x : ℝ) (i : Fin 3) :
    Continuous (fun u : ℝ => principalNullResponse q s amplitude i (u+x) (u-x)) := by
  have h := (radialResponse_continuous (-principalExponent q i) s amplitude).comp
    (show Continuous (fun u : ℝ => (((u+x)+(u-x))/2,((u+x)-(u-x))/2)) by fun_prop)
  exact continuous_const.mul h

private theorem principal_correction_smooth (q : XiZeroCopy) :
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (Fin 3 → ℂ) =>
      ∑ i : Fin 3, z.2 i*cutoffPower (principalExponent q i) ![z.1.1,Real.exp z.1.2]) := by
  apply ContDiff.sum
  intro i hi
  change ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (Fin 3 → ℂ) =>
    z.2 i*powerCutoffHeight (principalExponent q i) (Real.exp z.1.2))
  exact (by fun_prop : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (Fin 3 → ℂ) => z.2 i)).mul
    ((powerCutoffHeight_smooth _).comp (by fun_prop))

/-- Joint angular smoothness of the literal cutoff residual keeps all three
principal amplitudes and the complete mixed angular derivatives. -/
theorem fullNullResidual_angular_smooth (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => fullNullResidual q s amplitude p r z.1 z.2) :=
  (fullNullResponse_angular_smooth q s amplitude p r).sub
    ((principal_correction_smooth q).comp (contDiff_id.prodMk contDiff_const))

/-- The actual double time primitive is jointly smooth in both angular variables.
No regularity of the characteristic radius beyond continuity is assumed. -/
theorem nativeResidualTimePrimitive_angular_smooth (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => nativeResidualTimePrimitive q s amplitude t x z.1 z.2) := by
  have hc : Continuous (fun u : ℝ => (fun i : Fin 3 =>
      ((t-u:ℝ):ℂ)*principalNullResponse q s amplitude i (u+x) (u-x))) := by
    apply continuous_pi
    intro i
    exact (by fun_prop : Continuous (fun u : ℝ => ((t-u:ℝ):ℂ))).mul
      (principal_time_continuous q s amplitude x i)
  have h := interval_integral_infty (principal_correction_smooth q) _ hc 0 t
  convert! (full_time_angular_smooth q s amplitude t x).sub h using 1
  funext z
  unfold nativeResidualTimePrimitive fullNullResidual
  simp only [mul_sub,Finset.mul_sum,← mul_assoc]
  rw [intervalIntegral.integral_sub]
  · exact ((by fun_prop : Continuous (fun u : ℝ => ((t-u:ℝ):ℂ))).mul
      (full_time_continuous q s amplitude x z.1 z.2)).intervalIntegrable 0 t
  · apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro i hi
    exact ((by fun_prop : Continuous (fun u : ℝ => ((t-u:ℝ):ℂ))).mul
      (principal_time_continuous q s amplitude x i)).mul continuous_const

open UpperHalfPlane ModularGroup
open scoped MatrixGroups

private theorem nativePrimitive_low (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ)
    (z : UpperHalfPlane) (hz : z.im < 2) :
    nativeResidualTimePrimitive q s amplitude t x z.re (Real.log z.im) =
      ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ)*fullNullResponse q s amplitude (u+x) (u-x) z.re (Real.log z.im) := by
  unfold nativeResidualTimePrimitive fullNullResidual
  simp only [Real.exp_log z.im_pos]
  have hh (i : Fin 3) : cutoffPower (principalExponent q i) ![z.re,z.im]=0 :=
    cutoffPower_low _ _ hz.le
  simp only [hh,mul_zero,Finset.sum_const_zero,sub_zero]

private theorem nativePrimitive_translate (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ)
    (n : ℤ) (z : UpperHalfPlane) :
    nativeResidualTimePrimitive q s amplitude t x (T^n • z).re (Real.log (T^n • z).im) =
      nativeResidualTimePrimitive q s amplitude t x z.re (Real.log z.im) := by
  unfold nativeResidualTimePrimitive fullNullResidual
  simp_rw [fullNullResponse_modular]
  simp only [cutoffPower,RHTower.D4BMGlobalAngularResponse.cutoff,Matrix.cons_val_one,ModularGroup.im_T_zpow_smul]

/-- The primitive retains full modular germs uniformly through the time integral. -/
theorem nativeResidualTimePrimitive_cell_compatible (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ) :
    CellGermCompatible (fun z => nativeResidualTimePrimitive q s amplitude t x z.re (Real.log z.im)) := by
  intro gamma z hz hgamma
  induction gamma using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hgamma ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      dsimp only
      rw [hn]
      exact nativePrimitive_translate q s amplitude t x n w
    · obtain ⟨hl,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hgamma
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp
          (show Continuous (fun w : UpperHalfPlane => A • w) by
            simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      rw [nativePrimitive_low q s amplitude t x _ hAw,nativePrimitive_low q s amplitude t x _ hw]
      simp only [fullNullResponse_modular]

private theorem nativePrimitive_chart_smooth (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ) :
    ChartSmooth (fun z => nativeResidualTimePrimitive q s amplitude t x z.re (Real.log z.im)) := by
  intro z
  have hp : ContDiffAt ℝ ∞ (fun w : ℂ => (w.re,Real.log w.im)) (z:ℂ) := by
    exact Complex.reCLM.contDiff.contDiffAt.prodMk
      ((Real.contDiffAt_log.mpr z.im_pos.ne').comp (z:ℂ) Complex.imCLM.contDiff.contDiffAt)
  have h := (nativeResidualTimePrimitive_angular_smooth q s amplitude t x).contDiffAt.comp (z:ℂ) hp
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,ofComplex_apply_of_im_pos hw]
  rfl

/-- The native double time primitive extended using its actual closed-cell germs. -/
def globalNativeTimePrimitive (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => nativeResidualTimePrimitive q s amplitude t x z.re (Real.log z.im))

/-- This is a globally smooth modular representative of the literal primitive. -/
theorem globalNativeTimePrimitive_smooth (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ) :
    ChartSmooth (globalNativeTimePrimitive q s amplitude t x) :=
  cellGermExtension_smooth _ (nativeResidualTimePrimitive_cell_compatible q s amplitude t x)
    (nativePrimitive_chart_smooth q s amplitude t x)

/-- The original function and all angular derivatives agree near every closed-cell point. -/
theorem globalNativeTimePrimitive_germ (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    globalNativeTimePrimitive q s amplitude t x =ᶠ[𝓝 z]
      (fun w => nativeResidualTimePrimitive q s amplitude t x w.re (Real.log w.im)) :=
  cellGermExtension_germ _ (nativeResidualTimePrimitive_cell_compatible q s amplitude t x) z hz

/-- All modular transformations preserve the actual primitive extension. -/
theorem globalNativeTimePrimitive_invariant (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ)
    (gamma : PSL2Z) (z : UpperHalfPlane) :
    globalNativeTimePrimitive q s amplitude t x (gamma • z) = globalNativeTimePrimitive q s amplitude t x z :=
  cellGermExtension_invariant _ (nativeResidualTimePrimitive_cell_compatible q s amplitude t x) gamma z

open RHTower.D4BMJointWave
open scoped ComplexConjugate
attribute [instance] RCLike.innerProductSpace

private theorem cutoffScale_ge_one (n : ℕ) : (1:ℝ) ≤ (n:ℝ)+1 := by
  have hn : (0:ℝ) ≤ n := by positivity
  linarith

/-- Every finite cusp cutoff of the literal primitive is in the original angular core. -/
def nativeTimePrimitiveCutoff (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ) (n j : ℕ) : CoreField where
  field z := modularCuspCutoff ((n:ℝ)+1) z^(j+1)*globalNativeTimePrimitive q s amplitude t x z
  smooth z := ((modularCuspCutoff_smooth _ (cutoffScale_ge_one n) z).pow (j+1)).mul
    (globalNativeTimePrimitive_smooth q s amplitude t x z)
  invariant gamma z := by
    rw [modularCuspCutoff_invariant _ (cutoffScale_ge_one n),globalNativeTimePrimitive_invariant]
  compact := by
    obtain ⟨K,hK,hz⟩ := modularCuspCutoff_compact ((n:ℝ)+1) (cutoffScale_ge_one n)
    refine ⟨K,hK,?_⟩
    intro z hfd hn
    simp only [hz z hfd hn,zero_pow (Nat.succ_ne_zero _),zero_mul]

private theorem frameDeriv_congr {f g : UpperHalfPlane → ℂ} {z : UpperHalfPlane}
    (he : f =ᶠ[𝓝 z] g) (v : ℂ) : weightedDeriv v f z = weightedDeriv v g z := by
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hp : f ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] g ∘ ofComplex := by
    apply hc.eventually (p := fun w => f w = g w)
    rw [ofComplex_apply]
    filter_upwards [he] with w hw
    exact hw
  unfold weightedDeriv
  rw [hp.fderiv_eq]

private theorem primitiveOuter_germ (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ)
    (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) (hy : z.im ≤ 3*((n:ℝ)+1)) :
    (nativeTimePrimitiveCutoff q s amplitude t x (3*n+2) 0).field =ᶠ[𝓝 z]
      globalNativeTimePrimitive q s amplitude t x := by
  have hN : (1:ℝ) ≤ ((3*n+2:ℕ):ℝ)+1 := cutoffScale_ge_one _
  have hn : (0:ℝ) ≤ n := by positivity
  have hlo : z.im < 2*(((3*n+2:ℕ):ℝ)+1) := by push_cast; linarith
  filter_upwards [modularCuspCutoff_germ _ hN z hz,
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hlo] with w hw hwy
  change modularCuspCutoff _ w^(0+1)*_ = _
  rw [hw,scaledCuspCutoff_low _ _ (by positivity) hwy.le]
  simp

private theorem primitiveInner_zero_germ (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ)
    (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) (hy : 3*((n:ℝ)+1) < z.im) :
    (nativeTimePrimitiveCutoff q s amplitude t x n 1).field =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [modularCuspCutoff_germ _ (cutoffScale_ge_one n) z hz,
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds hy] with w hw hwy
  change modularCuspCutoff _ w^(1+1)*_ = _
  rw [hw,scaledCuspCutoff_high _ _ (by positivity) hwy.le]
  simp

private theorem core_green_integral (f g : CoreField) :
    Integrable (frameEnergy f.field g.field) D4BMModularCore.measure ∧
    Integrable (fun z => conj (chartLaplacian f.field z)*g.field z) D4BMModularCore.measure ∧
    (∫ z : UpperHalfPlane, frameEnergy f.field g.field z ∂D4BMModularCore.measure) =
      -∫ z : UpperHalfPlane, conj (chartLaplacian f.field z)*g.field z ∂D4BMModularCore.measure := by
  have he := f.completed_green ⟨frameGraph g,frameGraph_mem g⟩
  change inner ℂ (derivativeVector f 1) (derivativeVector g 1)+
    inner ℂ (derivativeVector f Complex.I) (derivativeVector g Complex.I) =
    -inner ℂ (fieldVector f.laplacian) (fieldVector g) at he
  have hd (v : ℂ) : inner ℂ (derivativeVector f v) (derivativeVector g v) =
      ∫ z : UpperHalfPlane, conj (weightedDeriv v f.field z)*weightedDeriv v g.field z ∂D4BMModularCore.measure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(weightedDeriv_memLp v f.field f.smooth f.compact).coeFn_toLp,
      (weightedDeriv_memLp v g.field g.smooth g.compact).coeFn_toLp] with z hf hg
    change (derivativeVector f v) z = _ at hf
    change (derivativeVector g v) z = _ at hg
    rw [hf,hg]
    simp only [RCLike.inner_apply,mul_comm]
  have hi (v : ℂ) : Integrable (fun z : UpperHalfPlane =>
      conj (weightedDeriv v f.field z)*weightedDeriv v g.field z) D4BMModularCore.measure := by
    apply (L2.integrable_inner (𝕜 := ℂ) (derivativeVector f v) (derivativeVector g v)).congr
    filter_upwards [(weightedDeriv_memLp v f.field f.smooth f.compact).coeFn_toLp,
      (weightedDeriv_memLp v g.field g.smooth g.compact).coeFn_toLp] with z hf hg
    change (derivativeVector f v) z = _ at hf
    change (derivativeVector g v) z = _ at hg
    rw [hf,hg]
    simp only [RCLike.inner_apply,mul_comm]
  have hl : inner ℂ (fieldVector f.laplacian) (fieldVector g) =
      ∫ z : UpperHalfPlane, conj (chartLaplacian f.field z)*g.field z ∂D4BMModularCore.measure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(core_field_memLp f.laplacian.field f.laplacian.smooth f.laplacian.compact).coeFn_toLp,
      (core_field_memLp g.field g.smooth g.compact).coeFn_toLp] with z hf hg
    change (fieldVector f.laplacian) z = _ at hf
    change (fieldVector g) z = _ at hg
    rw [hf,hg]
    simp only [CoreField.laplacian_field,RCLike.inner_apply,mul_comm]
  have hli : Integrable (fun z => conj (chartLaplacian f.field z)*g.field z) D4BMModularCore.measure := by
    apply (L2.integrable_inner (𝕜 := ℂ) (fieldVector f.laplacian) (fieldVector g)).congr
    filter_upwards [(core_field_memLp f.laplacian.field f.laplacian.smooth f.laplacian.compact).coeFn_toLp,
      (core_field_memLp g.field g.smooth g.compact).coeFn_toLp] with z hf hg
    change (fieldVector f.laplacian) z = _ at hf
    change (fieldVector g) z = _ at hg
    rw [hf,hg]
    simp only [CoreField.laplacian_field,RCLike.inner_apply,mul_comm]
  refine ⟨?_,hli,?_⟩
  · convert! (hi 1).add (hi Complex.I) using 1
    funext z
    simp only [frameEnergy,Fin.sum_univ_two,direction,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.add_apply]
  rw [hd 1,hd Complex.I,hl,← integral_add (hi 1) (hi Complex.I)] at he
  simpa only [frameEnergy,Fin.sum_univ_two,direction,Matrix.cons_val_zero,Matrix.cons_val_one] using he

/-- Compact angular integration by parts for the literal native primitive. The outer
cutoff disappears by equality of actual germs; no global finite-energy premise is used. -/
theorem nativeTimePrimitive_compact_angular_green (q : XiZeroCopy) (s amplitude : ℂ)
    (t x : ℝ) (n : ℕ) :
    Integrable (frameEnergy (globalNativeTimePrimitive q s amplitude t x)
      (nativeTimePrimitiveCutoff q s amplitude t x n 1).field) D4BMModularCore.measure ∧
    Integrable (fun z => conj (chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z)*
      (nativeTimePrimitiveCutoff q s amplitude t x n 1).field z) D4BMModularCore.measure ∧
    (∫ z : UpperHalfPlane, frameEnergy (globalNativeTimePrimitive q s amplitude t x)
        (nativeTimePrimitiveCutoff q s amplitude t x n 1).field z ∂D4BMModularCore.measure) =
      -∫ z : UpperHalfPlane, conj (chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z)*
        (nativeTimePrimitiveCutoff q s amplitude t x n 1).field z ∂D4BMModularCore.measure := by
  let f := nativeTimePrimitiveCutoff q s amplitude t x (3*n+2) 0
  let g := nativeTimePrimitiveCutoff q s amplitude t x n 1
  have hleft : (fun z => frameEnergy f.field g.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => frameEnergy (globalNativeTimePrimitive q s amplitude t x) g.field z) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ 3*((n:ℝ)+1)
    · have he := primitiveOuter_germ q s amplitude t x n z hz hy
      unfold frameEnergy
      apply Finset.sum_congr rfl
      intro i hi
      rw [frameDeriv_congr he]
    · have he := primitiveInner_zero_germ q s amplitude t x n z hz (lt_of_not_ge hy)
      have hd (v : ℂ) : weightedDeriv v g.field z = 0 := by
        rw [frameDeriv_congr he]
        simp [weightedDeriv,Function.comp_def]
      simp only [frameEnergy,hd,mul_zero,Finset.sum_const_zero]
  have hright : (fun z => conj (chartLaplacian f.field z)*g.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => conj (chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z)*g.field z) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ 3*((n:ℝ)+1)
    · rw [chartLaplacian_congr (primitiveOuter_germ q s amplitude t x n z hz hy)]
    · have hg : g.field z = 0 :=
        (primitiveInner_zero_germ q s amplitude t x n z hz (lt_of_not_ge hy)).eq_of_nhds
      rw [hg,mul_zero,mul_zero]
  obtain ⟨hfl,hfr,hfg⟩ := core_green_integral f g
  refine ⟨hfl.congr hleft,hfr.congr hright,?_⟩
  exact (integral_congr_ae hleft).symm.trans
    (hfg.trans (congrArg Neg.neg (integral_congr_ae hright)))


/-- Joint smoothness of the literal full-source circle mean in radius and both
base coordinates. This exposes the existing compact-integral proof for source
operator transposition; no angular or radial regularity premise is supplied. -/
theorem nativeMean_joint_smooth (q : XiZeroCopy) :
    ContDiff ℝ ∞ (fun v : ℝ × ℝ × ℝ => mean q v.1 v.2.1 v.2.2) := by
  have he : angularCircle q = mean q := by
    funext d X k
    unfold angularCircle mean D4BMNativeCircle.average
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  simpa only [he] using angularCircle_smooth q

end RHTower.D4BMNativeResponse
