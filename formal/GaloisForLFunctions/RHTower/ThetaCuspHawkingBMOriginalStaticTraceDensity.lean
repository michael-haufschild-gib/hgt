import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricTraceDecay

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalStaticTraceDensity
open D4BMJointSource D4BMModularCore D4BMOriginalMetricTraceDecay
open D4BMOriginalBoundaryCollarBounds D4BMOriginalBoundaryRestoration
open D4BMOriginalSourceRadialAdmission D4BMOriginalSourceRadialRestoration
open D4BMOriginalSourceTailCollar D4BMOriginalFullMetricCollar
noncomputable section
set_option autoImplicit false
private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q

/-- The horizontal period of the actual retained horizon transfer. -/
def transferPeriod (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 4) (k p : ℝ) : ℂ :=
  ∫ x in (-1/2:ℝ)..1/2,horizonTransfer q br amp w j p x k

/-- Complete source-minus-boundary endpoint density, with original coefficients. -/
def endpointDensity (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k p : ℝ) : ℂ :=
  (mu q-2)*(mu q*horizonPeriodError q br amp w p k-transferPeriod q br amp w 0 k p)

/-- The complete horizon bulk density paired with that endpoint density. -/
def bulkDensity (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k p : ℝ) : ℂ :=
  2*w*endpointDensity q br amp w k p+w*(mu q*transferPeriod q br amp w 1 k p-
    transferPeriod q br amp w 2 k p-transferPeriod q br amp w 3 k p)

private theorem period_integrable (F : ℝ×ℝ→ℂ)
    (hF : ContinuousOn F {z : ℝ×ℝ | 0<z.1}) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun p => ∫ x in (-1/2:ℝ)..1/2,F (p,x)) volume a b := by
  have hc : ContinuousOn F (Icc a b ×ˢ Icc (-1/2:ℝ) (1/2:ℝ)) :=
    hF.mono (fun z hz => ha.trans_le hz.1.1)
  have hi : Integrable F ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2),IntegrableOn]
    using hi.integral_prod_left

/-- Separate compact admission of the actual source and all four transfer
periods, before forming the original endpoint and bulk densities. -/
theorem component_time_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a b k : ℝ,
      0<a → a≤b → 0≤k → 4≤Real.exp k →
      IntervalIntegrable (fun p => horizonPeriodError q br amp w p k) volume a b ∧
      ∀ j : Fin 4,IntervalIntegrable (transferPeriod q br amp w j k) volume a b := by
  obtain ⟨G1,hG1,h1⟩ := horizon_period_time_integrable q br amp
  obtain ⟨G2,_,h2⟩ := horizon_transfer_continuous q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw a b k ha hab hk hk4
  refine ⟨h1 w hwi (by linarith [le_max_left G1 G2]) a b k ha hab hk hk4,?_⟩
  intro j
  exact period_integrable _ (h2 w hwi (by linarith [le_max_right G1 G2]) j k hk) a b ha hab

/-- The actual complete horizon endpoint and bulk terms have independent
compact time admission. -/
theorem trace_density_time_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a b k : ℝ,
      0<a → a≤b → 0≤k → 4≤Real.exp k →
      IntervalIntegrable (endpointDensity q br amp w k) volume a b ∧
      IntervalIntegrable (bulkDensity q br amp w k) volume a b := by
  obtain ⟨G,hG,hg⟩ := component_time_integrable q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw a b k ha hab hk hk4
  obtain ⟨hE,hP⟩ := hg w hwi hw a b k ha hab hk hk4
  have hU : IntervalIntegrable (endpointDensity q br amp w k) volume a b :=
    ((hE.const_mul (mu q)).sub (hP 0)).const_mul (mu q-2)
  exact ⟨hU,(hU.const_mul (2*w)).add ((((hP 1).const_mul (mu q)).sub (hP 2) |>.sub (hP 3)).const_mul w)⟩

/-- Exact attachment of the full original trace to its endpoint and bulk
terms. Every interval split uses the actual admitted components. -/
theorem trace_density_decomposition (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a b k : ℝ,
      0<a → a≤b → 0≤k → 4≤Real.exp k →
      metricTrace q br amp w a b k=endpointDensity q br amp w k b-endpointDensity q br amp w k a+
        ∫ p in a..b,bulkDensity q br amp w k p := by
  obtain ⟨G,hG,hg⟩ := component_time_integrable q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw a b k ha hab hk hk4
  obtain ⟨hE,hP⟩ := hg w hwi hw a b k ha hab hk hk4
  have hU : IntervalIntegrable (endpointDensity q br amp w k) volume a b :=
    ((hE.const_mul (mu q)).sub (hP 0)).const_mul (mu q-2)
  have hV : (∫ p in a..b,bulkDensity q br amp w k p)=
      2*w*((mu q-2)*(mu q*(∫ p in a..b,horizonPeriodError q br amp w p k)-
        ∫ p in a..b,transferPeriod q br amp w 0 k p))+
      w*(mu q*(∫ p in a..b,transferPeriod q br amp w 1 k p)-
        (∫ p in a..b,transferPeriod q br amp w 2 k p)-(∫ p in a..b,transferPeriod q br amp w 3 k p)) := by
    unfold bulkDensity
    rw [intervalIntegral.integral_add (hU.const_mul _) (((((hP 1).const_mul _).sub (hP 2)).sub (hP 3)).const_mul _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (((hP 1).const_mul _).sub (hP 2)) (hP 3),
      intervalIntegral.integral_sub ((hP 1).const_mul _) (hP 2),intervalIntegral.integral_const_mul]
    unfold endpointDensity
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (hE.const_mul _) (hP 0),
      intervalIntegral.integral_const_mul]
  rw [hV]
  unfold metricTrace horizonSourceFunctional horizonBoundary endpointDensity transferPeriod
  dsimp only
  ring

/-- Both complete densities have arbitrary cusp decay and one integrable
exponential time envelope. No trace or corner cancellation is assumed. -/
theorem trace_density_decay (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧ ∀ p k : ℝ,0<p → 0≤k →
      ‖endpointDensity q br amp w k p‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) ∧
      ‖bulkDensity q br amp w k p‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G1,hG1,h1⟩ := horizon_period_bound q br amp N
  obtain ⟨G2,_,h2⟩ := horizon_transfer_decay q br amp N
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := h1 w (by linarith [le_max_left G1 G2])
  obtain ⟨D,hD,hd⟩ := h2 w (by linarith [le_max_right G1 G2])
  let M := C+D
  have hM : 0≤M := add_nonneg hC hD
  let B := ‖mu q-2‖*(‖mu q‖+1)*M
  let J := ‖2*w‖*B+‖w‖*(‖mu q‖+2)*M
  have hB : 0≤B := by dsimp [B];positivity
  have hJ : 0≤J := by dsimp [J];positivity
  refine ⟨B+J,by positivity,?_⟩
  intro p k hp hk
  let Z := Real.exp (-(N:ℝ)*k)*Real.exp (-p)
  have hZ : 0≤Z := by dsimp [Z];positivity
  have hP (j : Fin 4) : ‖transferPeriod q br amp w j k p‖≤M*Z := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun x _ => hd p x k hp hk j)
    have h' : ‖transferPeriod q br amp w j k p‖≤D*Z := by
      simpa only [transferPeriod,Z,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one,neg_div,mul_assoc] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) hZ)
  have hE : ‖horizonPeriodError q br amp w p k‖≤M*Z := by
    have h : ‖horizonPeriodError q br amp w p k‖≤C*Z := by
      simpa only [Z,mul_assoc] using hc p k hp hk
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hZ)
  have hU : ‖endpointDensity q br amp w k p‖≤B*Z := by
    unfold endpointDensity
    rw [norm_mul]
    calc
      _ ≤ ‖mu q-2‖*(‖mu q‖*(M*Z)+M*Z) := by
        gcongr
        exact (norm_sub_le _ _).trans (by rw [norm_mul];gcongr;exact hP 0)
      _ = _ := by dsimp [B];ring
  have hV : ‖bulkDensity q br amp w k p‖≤J*Z := by
    unfold bulkDensity
    calc
      _ ≤ ‖2*w‖*(B*Z)+‖w‖*(‖mu q‖*(M*Z)+M*Z+M*Z) := by
        apply (norm_add_le _ _).trans
        simp only [norm_mul]
        gcongr
        exact (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans (by
          rw [norm_mul];gcongr <;> exact hP _))
      _ = _ := by dsimp [J];ring
  constructor
  · exact hU.trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hJ) hZ).trans_eq (by dsimp [Z];ring))
  · exact hV.trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) hZ).trans_eq (by dsimp [Z];ring))

end
end RHTower.D4BMOriginalStaticTraceDensity
