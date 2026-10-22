import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalBoundaryRestoration

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceTailCollar
open D4BMJointSource D4BMModularCore D4BMOriginalReaderCuspBounds D4BMOriginalAngularReaderBounds
open D4BMOriginalCausalPotential D4BMOriginalCausalPeriod D4BMOriginalCausalRestoration
open D4BMOriginalScalarRestoration D4BMGlobalAngularResponse D4BMOriginalBaseCircleJets
noncomputable section
set_option autoImplicit false

/-- Literal high-cusp domain in the original modular measure. -/
def tailSet (k : ℝ) : Set UpperHalfPlane := {z | Real.exp k<z.im}

/-- Original scalar-period tail, including the unchanged radial and time reader. -/
def tailDensity (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p L : ℝ) (z : UpperHalfPlane) : ℂ :=
  Complex.exp (-w*(p:ℂ))*reader q w L*sourceJet q br amp 0 p L z.re (Real.log z.im)*
    angularJet q false z.re (Real.log z.im)

/-- Its actual source-derived horizon trace, before angular integration. -/
def horizonTailDensity (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p : ℝ) (z : UpperHalfPlane) : ℂ :=
  Complex.exp (-w*(p:ℂ))*horizonReader q w*horizonJet q br amp 0 p z.re (Real.log z.im)*
    angularJet q false z.re (Real.log z.im)

private theorem tail_log (k : ℝ) (z : UpperHalfPlane) (hz : z∈tailSet k) : k≤Real.log z.im := by
  have h := Real.log_le_log (Real.exp_pos k) hz.le
  simpa only [Real.log_exp] using h

/-- The actual scalar-period cusp tail has a mixed horizon error with an
integrable time majorant, uniformly over its entire unbounded angular domain. -/
theorem source_tail_density_error (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ C : ℝ,0≤C ∧ ∀ᶠ L : ℝ in atTop,∀ p k : ℝ,0<p → 0≤k →
        ∀ z∈tailSet k,‖tailDensity q br amp w p L z-horizonTailDensity q br amp w p z‖≤
          C*Real.exp (-L)*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := original_reader_source_jet_error q br amp 0 (N+1)
  obtain ⟨A,hA,ha⟩ := angularJet_bound q false
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨B,hB,hb⟩ := hg w hwi hw
  refine ⟨2*B*A,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with L hL hL0 p k hp hk z hz
  let t := Real.log z.im
  have ht : k≤t := tail_log k z hz
  have ht0 : 0≤t := hk.trans ht
  have he : ‖tailDensity q br amp w p L z-horizonTailDensity q br amp w p z‖=
      ‖Complex.exp (-w*(p:ℂ))*(reader q w L*sourceJet q br amp 0 p L z.re t-
        horizonReader q w*horizonJet q br amp 0 p z.re t)‖*‖angularJet q false z.re t‖ := by
    rw [← norm_mul]
    congr 1
    unfold tailDensity horizonTailDensity
    dsimp only [t]
    ring
  rw [he]
  have hsum : Real.exp (-L)+Real.exp (-w.re*L)≤2*Real.exp (-L) := by
    have h1 : 1≤w.re := by linarith
    have h2 : -w.re*L≤-L := by nlinarith
    linarith [Real.exp_le_exp.mpr h2]
  calc
    _ ≤ (B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-((N+1:ℕ):ℝ)*t)*Real.exp (-p))*(A*Real.exp t) :=
      mul_le_mul (hL p z.re t hp ht0) (ha z.re t ht0) (norm_nonneg _) (by positivity)
    _ ≤ (B*(2*Real.exp (-L))*Real.exp (-((N+1:ℕ):ℝ)*t)*Real.exp (-p))*(A*Real.exp t) := by gcongr
    _ = (2*B*A)*Real.exp (-L)*Real.exp (-(N:ℝ)*t)*Real.exp (-p) := by
      rw [show (B*(2*Real.exp (-L))*Real.exp (-((N+1:ℕ):ℝ)*t)*Real.exp (-p))*(A*Real.exp t)=
        (2*B*A)*Real.exp (-L)*(Real.exp (-((N+1:ℕ):ℝ)*t)*Real.exp t)*Real.exp (-p) by ring,
        ← Real.exp_add]
      congr 3
      push_cast
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N)]

/-- Finite modular mass turns the pointwise mixed error into a uniform bound
for the literal cusp-tail integral. No cusp coordinate reparameterization is used. -/
theorem source_tail_integral_error (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ C : ℝ,0≤C ∧ ∀ᶠ L : ℝ in atTop,∀ p k : ℝ,0<p → 0≤k →
        ‖∫ z in tailSet k,tailDensity q br amp w p L z-horizonTailDensity q br amp w p z ∂measure‖≤
          C*Real.exp (-L)*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := source_tail_density_error q br amp N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := hg w hwi hw
  refine ⟨C*measure.real univ,by positivity,?_⟩
  filter_upwards [hc] with L hL p k hp hk
  let B := C*Real.exp (-L)*Real.exp (-(N:ℝ)*k)*Real.exp (-p)
  have hB : 0≤B := by dsimp [B];positivity
  have hm : MeasurableSet (tailSet k) := measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  have hi : Integrable (fun _ : UpperHalfPlane => B) (measure.restrict (tailSet k)) := integrable_const B
  have h := norm_integral_le_of_norm_le hi (by
    filter_upwards [ae_restrict_mem hm] with z hz
    exact hL p k hp hk z hz)
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at h
  have hmass : measure.real (tailSet k) ≤ measure.real univ := measureReal_mono (μ:=measure) (subset_univ _)
  calc
    _ ≤ measure.real (tailSet k)*B := h
    _ ≤ measure.real univ*B := mul_le_mul_of_nonneg_right hmass hB
    _ = _ := by dsimp [B];ring

private theorem source_jet_cutoff (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p L : ℝ) (z : UpperHalfPlane) (hy : 3≤z.im) :
    sourceJet q br amp 0 p L z.re (Real.log z.im)=originalCutoffResidual q br amp p (p+L) z := by
  have he (i : Fin 3) : cutoffPower (principalExponent q i) (coordinates z)=
      Complex.exp (principalExponent q i*(Real.log z.im:ℂ)) := by
    change (Real.smoothTransition (z.im-2):ℂ)*(z.im:ℂ)^principalExponent q i=_
    rw [Real.smoothTransition.one_of_one_le (by linarith),Complex.ofReal_one,one_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr z.im_pos.ne'),
      ← Complex.ofReal_log z.im_pos.le]
    congr 1
    ring
  simp only [sourceJet,baseOperator,originalCutoffResidual,D4BMOriginalCuspJets.remainder,
    D4BMOriginalCuspJets.principal,Matrix.cons_val,he]

private theorem tail_density_cutoff (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (p L : ℝ) (z : UpperHalfPlane) (hy : 3≤z.im) :
    tailDensity q br amp w p L z=
      (Complex.exp (-w*(p:ℂ))*reader q w L)*
        (D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
          originalCutoffResidual q br amp p (p+L) z) := by
  rw [tailDensity,source_jet_cutoff q br amp p L z hy]
  simp only [angularJet,Bool.false_eq_true,if_false,Real.exp_log z.im_pos,coordinates]
  ring

theorem tail_density_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (p L k : ℝ) (hp : 0<p) (hL : 0<L) (hk : 4≤Real.exp k) :
    IntegrableOn (tailDensity q br amp w p L) (tailSet k) measure := by
  have h := ((originalCutoffResidual_scalar_integrable q br amp ⟨p,hp.le⟩
    ⟨p+L,show 0≤p+L by linarith⟩).const_mul (Complex.exp (-w*(p:ℂ))*reader q w L)).integrableOn (s:=tailSet k)
  have hm : MeasurableSet (tailSet k) := measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  apply h.congr
  filter_upwards [ae_restrict_mem hm] with z hz
  exact (tail_density_cutoff q br amp w p L z (by change Real.exp k<z.im at hz;linarith)).symm

/-- The horizon trace is admitted in the original cusp measure: it is the
almost-everywhere limit of the actual measurable physical tails. -/
theorem horizon_tail_measurable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ p k : ℝ,0<p → 0≤k → 4≤Real.exp k →
      AEStronglyMeasurable (horizonTailDensity q br amp w p) (measure.restrict (tailSet k)) := by
  obtain ⟨G,hG,hg⟩ := source_tail_density_error q br amp 0
  refine ⟨G,hG,?_⟩
  intro w hwi hw p k hp hk hk4
  obtain ⟨C,hC,hc⟩ := hg w hwi hw
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℝ)
    (fun L => (tail_density_integrable q br amp w p (Real.exp L) k hp (Real.exp_pos L) hk4).aestronglyMeasurable)
  have hm : MeasurableSet (tailSet k) := measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  filter_upwards [ae_restrict_mem hm] with z hz
  apply Filter.Tendsto.comp (g:=fun L : ℝ => tailDensity q br amp w p L z) _ Real.tendsto_exp_atTop
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun L : ℝ => C*Real.exp (-L)*Real.exp (-p)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).mul_const (Real.exp (-p))
  apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg _)) _ ht
  filter_upwards [hc] with L hL
  simpa only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using hL p k hp hk z hz

/-- The leading original scalar tail itself has arbitrary cusp decay and an
integrable time envelope; it is retained as a genuine horizon counterterm. -/
theorem horizon_tail_density_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧
      ∀ p k : ℝ,0<p → 0≤k → ∀ z∈tailSet k,
        ‖horizonTailDensity q br amp w p z‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨B,G,hB,hG,hg⟩ := D4BMOriginalHorizonForcingBound.original_action_base_jet_horizon_estimate
    (D4BMGlobalAngularResponse.center q) (physicalRate q br) amp 0 (N+1)
  obtain ⟨A,hA,ha⟩ := angularJet_bound q false
  refine ⟨G,hG,?_⟩
  intro w hw
  refine ⟨‖horizonReader q w‖*B*A,by positivity,?_⟩
  intro p k hp hk z hz
  let t := Real.log z.im
  have ht : k≤t := tail_log k z hz
  have ht0 : 0≤t := hk.trans ht
  have hH : ‖horizonJet q br amp 0 p z.re t‖≤B*Real.exp (G*p-((N+1:ℕ):ℝ)*t) :=
    (hg p 0 z.re t hp.le (by norm_num) (by norm_num) ht0).1
  unfold horizonTailDensity
  change ‖Complex.exp (-w*(p:ℂ))*horizonReader q w*horizonJet q br amp 0 p z.re t*
    angularJet q false z.re t‖≤_
  simp only [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ Real.exp (-w.re*p)*‖horizonReader q w‖*(B*Real.exp (G*p-((N+1:ℕ):ℝ)*t))*(A*Real.exp t) := by
      gcongr
      exact ha z.re t ht0
    _ = (‖horizonReader q w‖*B*A)*Real.exp ((G-w.re)*p-(N:ℝ)*t) := by
      rw [show Real.exp (-w.re*p)*‖horizonReader q w‖*(B*Real.exp (G*p-((N+1:ℕ):ℝ)*t))*(A*Real.exp t)=
        (‖horizonReader q w‖*B*A)*(Real.exp (-w.re*p)*Real.exp (G*p-((N+1:ℕ):ℝ)*t)*Real.exp t) by ring]
      rw [← Real.exp_add,← Real.exp_add]
      congr 2
      push_cast
      ring
    _ ≤ (‖horizonReader q w‖*B*A)*Real.exp (-p-(N:ℝ)*k) := by
      gcongr
      have hn : 0≤(N:ℝ) := Nat.cast_nonneg N
      nlinarith
    _ = _ := by rw [show -p-(N:ℝ)*k=-(N:ℝ)*k+(-p) by ring,Real.exp_add];ring

/-- Actual angular integral admission of the retained leading horizon tail. -/
theorem horizon_tail_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ p k : ℝ,0<p → 0≤k → 4≤Real.exp k →
      IntegrableOn (horizonTailDensity q br amp w p) (tailSet k) measure := by
  obtain ⟨G1,hG1,h1⟩ := horizon_tail_measurable q br amp
  obtain ⟨G2,_,h2⟩ := horizon_tail_density_bound q br amp 0
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw p k hp hk hk4
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨C,hC,hc⟩ := h2 w hw2
  have hi : Integrable (fun _ : UpperHalfPlane => C*Real.exp (-p)) (measure.restrict (tailSet k)) :=
    integrable_const _
  apply hi.mono' (h1 w hwi hw1 p k hp hk hk4)
  have hm : MeasurableSet (tailSet k) := measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  filter_upwards [ae_restrict_mem hm] with z hz
  simpa only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using hc p k hp hk z hz

/-- Exactly the source-period discrepancy occurring in the full physical
metric identity after its radius factors cancel. -/
def originalPeriodError (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p L k : ℝ) : ℂ :=
  Complex.exp (-w*(p:ℂ))*reader q w L*
    (originalFiniteHeightPeriod q br amp p (p+L) (Real.exp k)-originalRadialPeriod q br amp p (p+L))

def horizonPeriodError (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p k : ℝ) : ℂ :=
  -(∫ z in tailSet k,horizonTailDensity q br amp w p z ∂measure)

/-- The actual finite scalar-period discrepancy is precisely its admitted
original cusp tail, with the unchanged radial reader and time damping. -/
theorem original_period_error_tail (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (p L k : ℝ) (hp : 0<p) (hL : 0<L) (hk : 4≤Real.exp k) :
    originalPeriodError q br amp w p L k=
      -(∫ z in tailSet k,tailDensity q br amp w p L z ∂measure) := by
  have h := original_finiteHeight_sub_radial q br amp ⟨p,hp.le⟩ ⟨p+L,show 0≤p+L by linarith⟩ (Real.exp k) hk
  unfold originalPeriodError
  rw [h,mul_neg,← integral_const_mul]
  congr 1
  apply setIntegral_congr_fun (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)
  intro z hz
  exact (tail_density_cutoff q br amp w p L z (by change Real.exp k<z.im at hz;linarith)).symm

/-- The complete original scalar-period error, after its genuine leading
horizon trace is retained, has independent cusp/horizon decay and an integrable
time envelope. Both tail integrals are separately admitted. -/
theorem original_period_mixed_error (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ C : ℝ,0≤C ∧ ∀ᶠ L : ℝ in atTop,∀ p k : ℝ,0<p → 0≤k → 4≤Real.exp k →
        ‖originalPeriodError q br amp w p L k-horizonPeriodError q br amp w p k‖≤
          C*Real.exp (-L)*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G1,hG1,h1⟩ := source_tail_integral_error q br amp N
  obtain ⟨G2,_,h2⟩ := horizon_tail_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨C,hC,hc⟩ := h1 w hwi hw1
  refine ⟨C,hC,?_⟩
  filter_upwards [hc,eventually_gt_atTop (0:ℝ)] with L hL hLp p k hp hk hk4
  rw [original_period_error_tail q br amp w p L k hp hLp hk4,horizonPeriodError]
  have he : -(∫ z in tailSet k,tailDensity q br amp w p L z ∂measure)-
      -(∫ z in tailSet k,horizonTailDensity q br amp w p z ∂measure)=
      -(∫ z in tailSet k,tailDensity q br amp w p L z-horizonTailDensity q br amp w p z ∂measure) := by
    rw [integral_sub (tail_density_integrable q br amp w p L k hp hLp hk4) (h2 w hwi hw2 p k hp hk hk4)]
    ring
  rw [he,norm_neg]
  exact hL p k hp hk

end
end RHTower.D4BMOriginalSourceTailCollar
