import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceRadialRestoration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalFullMetricDifference
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalBoundaryRadialAdmission

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalFullMetricCollar
open D4BMJointSource D4BMModularCore D4BMOriginalCompleteTransfer
open D4BMOriginalSourceRadialRestoration D4BMOriginalFullMetricDifference
open D4BMOriginalBoundaryRestoration D4BMOriginalBoundaryCollarBounds
open D4BMOriginalMetricTimePeriod D4BMOriginalReaderCuspBounds
noncomputable section
set_option autoImplicit false
private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q

/-- The unchanged finite metric density in its actual collar radial measure. -/
def metricDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  ((D4BMJointWave.tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*
    (metricTimeCut q br true amp w a b (D4BMJointWave.tortoiseRadius (-L/2)) (Real.exp k)-
      restoredMetricTime q br true amp w a b (D4BMJointWave.tortoiseRadius (-L/2)))

/-- The complete source/boundary leading trace; neither temporal endpoint nor
any of the four boundary transfers is discarded. -/
def metricTrace (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b k : ℝ) : ℂ :=
  horizonSourceFunctional q br amp w a b k+horizonBoundary q br amp w a b k

def forcingMoment (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  mu q*w*(∫ p in a..b,forcingPeriodError q br amp w p L k)

/-- The finite physical metric remainder after retaining its literal forcing
moment and its complete source/boundary horizon trace. -/
def metricError (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  metricDifference q br amp w a b L k-forcingMoment q br amp w a b L k-
    metricTrace q br amp w a b k

/-- Exact attachment of the complete finite metric remainder to the controlled
source and boundary errors. No matching or counterterm equality is assumed. -/
theorem metric_error_decomposition (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a b L k : ℝ,
      0<a → a≤b → 0<L → 0≤k → 4≤Real.exp k →
      metricError q br amp w a b L k=
        sourceError q br amp w a b L k+boundaryError q br amp w a b L k := by
  obtain ⟨G1,hG1,h1⟩ := source_difference q br amp
  obtain ⟨G2,_,h2⟩ := physical_boundary_restoration q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw a b L k ha hab hL hk hk4
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  have hs := h1 w hwi hw1 a b L k ha hab hL hk hk4
  have hb := h2 w hwi hw2 a b L k ha hab hL hk
  unfold physicalRestoredBoundary at hb
  dsimp only at hb
  rw [complete_metric_boundary_products q br amp w hwi a b L k ha hab hL,
    complete_boundary_radial_density q br amp w a b L k hL] at hb
  have hm := original_full_metric_difference q br amp w hwi a b L k ha hab hL hk4
  change metricDifference q br amp w a b L k=sourceFunctional q br amp w a b L k+
    forcingMoment q br amp w a b L k+radialBoundary q br amp w a b L k at hm
  unfold metricError metricTrace
  rw [hm,← hs,← hb]
  ring

/-- The actual complete metric remainder has a mixed error bound, uniformly
over arbitrary positive temporal intervals. -/
theorem metric_error_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ C : ℝ,0≤C ∧
      ∀ᶠ L : ℝ in atTop,∀ a b k : ℝ,0<a → a≤b → 0≤k → 4≤Real.exp k →
        ‖metricError q br amp w a b L k‖≤C*Real.exp (-L)*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G1,hG1,h1⟩ := metric_error_decomposition q br amp
  obtain ⟨G2,_,h2⟩ := source_error_bound q br amp N
  obtain ⟨G3,_,h3⟩ := complete_boundary_error_bound q br amp N
  refine ⟨max G1 (max G2 G3),le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 (max G2 G3)]
  have hw2 : G2+1≤w.re := by linarith [(le_max_left G2 G3).trans (le_max_right G1 (max G2 G3))]
  have hw3 : G3+1≤w.re := by linarith [(le_max_right G2 G3).trans (le_max_right G1 (max G2 G3))]
  obtain ⟨C,hC,hc⟩ := h2 w hwi hw2
  obtain ⟨D,hD,hd⟩ := h3 w hwi hw3
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  filter_upwards [hc,hd,eventually_gt_atTop (0:ℝ)] with L hs hb hL a b k ha hab hk hk4
  rw [h1 w hwi hw1 a b L k ha hab hL hk hk4]
  calc
    _ ≤ ‖sourceError q br amp w a b L k‖+‖boundaryError q br amp w a b L k‖ := norm_add_le _ _
    _ ≤ C*Real.exp (-L)*Real.exp (-(N:ℝ)*k)+D*Real.exp (-L)*Real.exp (-(N:ℝ)*k) :=
      add_le_add (hs a b k ha hab hk hk4) (hb a b k ha hab hk)
    _ = _ := by ring

/-- Separate radial admission of the original metric density after the literal
forcing moment is removed. Admission is derived from the actual source and all
four boundary transfers, not inferred from a bound on a possibly nonintegrable difference. -/
theorem metric_source_boundary_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ a b k A B : ℝ,
      0<a → a≤b → 0≤k → 4≤Real.exp k → L0≤A → A≤B →
      IntervalIntegrable (fun L => metricDifference q br amp w a b L k-forcingMoment q br amp w a b L k) volume A B := by
  obtain ⟨G,hG,hg⟩ := source_radial_integrable q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨L0,hL0,h⟩ := hg w hwi hw
  refine ⟨L0,hL0,?_⟩
  intro a b k A B ha hab hk hk4 hA hAB
  have hAp := hL0.trans_le hA
  have hi := (h a b k A B ha hab hk hk4 hA hAB).add
    (D4BMOriginalBoundaryRadialAdmission.boundary_radial_integrable q br amp w hwi k A B a b hAp hAB ha hab)
  apply hi.congr
  intro L hL
  have hLI : L∈Ioc A B := by simpa only [uIoc_of_le hAB] using hL
  have hm := original_full_metric_difference q br amp w hwi a b L k ha hab (hAp.trans hLI.1) hk4
  change metricDifference q br amp w a b L k=sourceFunctional q br amp w a b L k+
    forcingMoment q br amp w a b L k+radialBoundary q br amp w a b L k at hm
  dsimp only
  rw [hm]
  ring


/-- The complete source/boundary part of the original metric pairing restores
jointly at every sufficiently deep interface. Both temporal endpoints and the
upper radial cutoff can move arbitrarily; the physical collar factor is one-half. -/
theorem metric_source_boundary_joint_limit (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧
      ∀ A : ℝ,L0≤A →
      ∀ {ι : Type*} (l : Filter ι) (K : ι→ℝ),Tendsto K l atTop →
      ∀ (T : ι→{v : ℝ×ℝ // 0<v.1 ∧ v.1≤v.2}) (M : ι→Ici A),
        Tendsto (fun z : ι =>
          ((∫ L in A..(M z:ℝ),metricDifference q br amp w (T z).val.1 (T z).val.2 L (K z)-
              forcingMoment q br amp w (T z).val.1 (T z).val.2 L (K z))-
            ((M z:ℝ)-A)•metricTrace q br amp w (T z).val.1 (T z).val.2 (K z))/2)
          l (𝓝 0) := by
  obtain ⟨G1,hG1,h1⟩ := metric_error_bound q br amp 1
  obtain ⟨G2,_,h2⟩ := metric_source_boundary_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨C,hC,hc⟩ := h1 w hwi hw1
  obtain ⟨D,hD⟩ := eventually_atTop.mp hc
  obtain ⟨L2,hL2,hadmit⟩ := h2 w hwi hw2
  let L0 := max D L2
  have hL0 : 0<L0 := lt_of_lt_of_le hL2 (le_max_right _ _)
  refine ⟨L0,hL0,?_⟩
  intro A hA ι l K hK T M
  have hAp : 0<A := hL0.trans_le hA
  have hcut : ∀ᶠ z : ι in l,0≤K z ∧ 4≤Real.exp (K z) :=
    hK.eventually ((eventually_ge_atTop (0:ℝ)).and (Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (4:ℝ))))
  have he : Tendsto (fun z : ι => ∫ L in A..(M z:ℝ),metricError q br amp w (T z).val.1 (T z).val.2 L (K z))
      l (𝓝 0) := by
    have hlim : Tendsto (fun z : ι => C*Real.exp (-K z))
        l (𝓝 0) := by
      simpa only [Function.comp_def,mul_zero] using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).comp hK
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hcut] with z hz
    have hi := exponential_interval_bound (fun L => metricError q br amp w (T z).val.1 (T z).val.2 L (K z))
      (C*Real.exp (-K z)) A (M z:ℝ) (by positivity) (M z).property (fun L hL => by
        have h := hD L ((le_max_left D L2).trans (hA.trans hL.1))
          (T z).val.1 (T z).val.2 (K z) (T z).property.1 (T z).property.2 hz.1 hz.2
        simpa only [Nat.cast_one,neg_one_mul,mul_neg_one,mul_comm,mul_left_comm,mul_assoc] using h)
    exact hi.trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith : -A≤0)) (by positivity)).trans_eq (mul_one _))
  have hd := he.div_const (2:ℂ)
  simp only [zero_div] at hd
  apply hd.congr'
  filter_upwards [hcut] with z hz
  have hi := hadmit (T z).val.1 (T z).val.2 (K z) A (M z)
    (T z).property.1 (T z).property.2 hz.1 hz.2 ((le_max_right D L2).trans hA) (M z).property
  unfold metricError
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,intervalIntegral.integral_const]

end
end RHTower.D4BMOriginalFullMetricCollar
