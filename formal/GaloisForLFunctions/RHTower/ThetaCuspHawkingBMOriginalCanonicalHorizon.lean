import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricHorizon

open Set Filter Topology Metric
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The value selected by the actual positive-radius endpoint limit. -/
def endpointJetValue (F : ℂ→ℝ→ℂ) (w : ℂ) : ℂ :=
  limUnder (𝓝[>] (0:ℝ)) (F w)

/-- The slope selected by the actual positive-radius difference quotient. -/
def endpointJetSlope (F : ℂ→ℝ→ℂ) (w : ℂ) : ℂ :=
  limUnder (𝓝[>] (0:ℝ)) (fun z => (F w z-endpointJetValue F w)/(z:ℂ))

/-- A quadratic endpoint estimate uniquely fixes both coefficients through
actual one-sided limits; no choice of local coefficient functions remains. -/
theorem HasUniformJet2.canonical_coefficients {S : Set ℂ} {b C : ℝ}
    {F : ℂ→ℝ→ℂ} {c₀ c₁ : ℂ→ℂ} (h : HasUniformJet2 S b F c₀ c₁ C)
    (hb : 0<b) {w : ℂ} (hw : w∈S) :
    endpointJetValue F w=c₀ w ∧ endpointJetSlope F w=c₁ w := by
  have hz : Tendsto (fun z : ℝ => z) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hv : Tendsto (F w) (𝓝[>] (0:ℝ)) (𝓝 (c₀ w)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have ht : Tendsto (fun z : ℝ => C*z^2+‖c₁ w‖*z) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [zero_pow (by norm_num : 2≠0),mul_zero,add_zero] using
        ((hz.pow 2).const_mul C).add (hz.const_mul ‖c₁ w‖)
    apply squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg _)) _ ht
    filter_upwards [Ioc_mem_nhdsGT hb] with z hzi
    have hzn : ‖(z:ℂ)‖=z := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hzi.1]
    calc
      ‖F w z-c₀ w‖=‖(F w z-c₀ w-c₁ w*z)+c₁ w*z‖ := by congr 1;ring
      _ ≤ ‖F w z-c₀ w-c₁ w*z‖+‖c₁ w*z‖ := norm_add_le _ _
      _ ≤ C*z^2+‖c₁ w‖*z := by rw [norm_mul,hzn];exact add_le_add (h w hw z hzi) le_rfl
  have h0 : endpointJetValue F w=c₀ w := hv.limUnder_eq
  refine ⟨h0,?_⟩
  unfold endpointJetSlope
  rw [h0]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun z : ℝ => C*z) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hz.const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg _)) _ ht
  filter_upwards [Ioc_mem_nhdsGT hb] with z hzi
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hzi.1.ne'
  have hzn : ‖(z:ℂ)‖=z := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hzi.1]
  have he : (F w z-c₀ w)/(z:ℂ)-c₁ w=(F w z-c₀ w-c₁ w*z)/(z:ℂ) := by field_simp
  rw [he,norm_div,hzn]
  calc
    _ ≤ C*z^2/z := div_le_div_of_nonneg_right (h w hw z hzi) hzi.1.le
    _ = C*z := by field_simp

/-- Local analytic endpoint jets agree with one canonical coefficient family
on their whole parameter ball. -/
theorem AnalyticJet2At.canonical {w : ℂ} {F : ℂ→ℝ→ℂ} (h : AnalyticJet2At w F) :
    AnalyticAt ℂ (endpointJetValue F) w ∧ AnalyticAt ℂ (endpointJetSlope F) w ∧
      ∃ R b C : ℝ,0<R ∧ 0<b ∧ b≤1/2 ∧ 0≤C ∧
        HasUniformJet2 (closedBall w R) b F (endpointJetValue F) (endpointJetSlope F) C := by
  obtain ⟨R,b,hR,hb,hbh,c₀,c₁,C,hC,ha₀,ha₁,hj⟩ := h
  have he (u : ℂ) (hu : u∈closedBall w R) := hj.canonical_coefficients hb hu
  have h0 : c₀ =ᶠ[𝓝 w] endpointJetValue F := by
    filter_upwards [closedBall_mem_nhds w hR] with u hu
    exact (he u hu).1.symm
  have h1 : c₁ =ᶠ[𝓝 w] endpointJetSlope F := by
    filter_upwards [closedBall_mem_nhds w hR] with u hu
    exact (he u hu).2.symm
  refine ⟨ha₀.congr h0,ha₁.congr h1,R,b,C,hR,hb,hbh,hC,?_⟩
  intro u hu z hz
  rw [(he u hu).1,(he u hu).2]
  exact hj u hu z hz

/-- Two independently constructed local jets of the same original profile
agree on every parameter overlap, including both the finite value and slope. -/
theorem HasUniformJet2.coefficients_unique {S T : Set ℂ} {b d C D : ℝ}
    {F : ℂ→ℝ→ℂ} {c₀ c₁ e₀ e₁ : ℂ→ℂ}
    (h : HasUniformJet2 S b F c₀ c₁ C) (g : HasUniformJet2 T d F e₀ e₁ D)
    (hb : 0<b) (hd : 0<d) {w : ℂ} (hw : w∈S) (hw' : w∈T) :
    c₀ w=e₀ w ∧ c₁ w=e₁ w := by
  have hc := h.canonical_coefficients hb hw
  have he := g.canonical_coefficients hd hw'
  exact ⟨hc.1.symm.trans he.1,hc.2.symm.trans he.2⟩

end
end GaloisForLFunctions.HTGeometry


namespace RHTower.D4BMOriginalCanonicalHorizon
open Set Filter Topology Metric Complex GaloisForLFunctions.HTGeometry
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMOriginalMetricHorizon
noncomputable section
set_option autoImplicit false

/-- The actual Gauss profile has a quadratic horizon germ at every nonreal
frequency, not only at the two fundamental frequencies. -/
theorem gauss_germ (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) :
    AnalyticJet2At w (gaussProfile q) := by
  obtain ⟨R,C,L,hR,_,_,hg⟩ := horizonGauss_uniform_second_bound
    w (physicalRadialFrequency q) hw (b:=1/2) (by norm_num) (by norm_num)
  have hj : HasUniformJet2 (closedBall w (R/2)) (1/2) (gaussProfile q)
      (fun _ => 1) (fun u => horizonGaussFirstCoefficient u (physicalRadialFrequency q)) C := by
    intro u hu z hz
    have hu' : u∈ball w R := by
      have := mem_closedBall.mp hu
      exact mem_ball.mpr (by linarith)
    exact (hg u hu').2 z ⟨hz.1.le,hz.2⟩
  exact AnalyticJet2At.of_jet (half_pos hR) (by norm_num) le_rfl analyticAt_const
    (horizonGaussFirstCoefficient_analyticAt w (physicalRadialFrequency q) hw) hj

theorem negative_gauss_germ (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) :
    AnalyticJet2At w (fun u z => gaussProfile q (-u) z) := by
  have hn : (-w).im≠0 := by simpa only [Complex.neg_im,neg_ne_zero] using hw
  obtain ⟨R,C,L,hR,_,_,hg⟩ := horizonGauss_uniform_second_bound
    (-w) (physicalRadialFrequency q) hn (b:=1/2) (by norm_num) (by norm_num)
  have hj : HasUniformJet2 (closedBall w (R/2)) (1/2) (fun u z => gaussProfile q (-u) z)
      (fun _ => 1) (fun u => horizonGaussFirstCoefficient (-u) (physicalRadialFrequency q)) C := by
    intro u hu z hz
    have hu' : -u∈ball (-w) R := by
      have hd := mem_closedBall.mp hu
      rw [mem_ball,dist_neg_neg]
      linarith
    exact (hg (-u) hu').2 z ⟨hz.1.le,hz.2⟩
  exact AnalyticJet2At.of_jet (half_pos hR) (by norm_num) le_rfl analyticAt_const
    ((horizonGaussFirstCoefficient_analyticAt (-w) (physicalRadialFrequency q) hn).comp analyticAt_id.neg) hj

/-- Both branches are the profiles of the unchanged normalizable reader and
original source; their germs exist throughout the nonreal frequency domain. -/
theorem original_profiles_germ (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (hw : w.im≠0) :
    AnalyticJet2At w (incomingProfile q br amp K) ∧
      AnalyticJet2At w (oppositeProfile q br amp K) := by
  have hI : AnalyticAt ℂ (incomingCoefficient q) w :=
    normalizable_horizonRegularCoefficient_analyticAt w (physicalRadialFrequency q) hw
  have hw0 : w≠0 := by intro h;apply hw;simp [h]
  have hO : AnalyticAt ℂ (oppositeCoefficient q) w :=
    (connection_frequency_analyticAt w (physicalRadialFrequency q) hw).div
      (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hw0)
  have hS := remainderProfile_germ q br amp K w
  exact ⟨((gauss_germ q w hw).mul hS).const_mul hI,
    ((negative_gauss_germ q w hw).mul hS).const_mul hO⟩

/-- The three subtraction coefficients are defined by the actual profiles'
positive-radius limits, independently of a selected frequency neighborhood. -/
def incomingValue (q : XiZeroCopy) (br : Bool) (amp K : ℂ) : ℂ→ℂ :=
  endpointJetValue (incomingProfile q br amp K)
def incomingSlope (q : XiZeroCopy) (br : Bool) (amp K : ℂ) : ℂ→ℂ :=
  endpointJetSlope (incomingProfile q br amp K)
def oppositeValue (q : XiZeroCopy) (br : Bool) (amp K : ℂ) : ℂ→ℂ :=
  endpointJetValue (oppositeProfile q br amp K)

/-- One source-determined analytic coefficient family spans the convergence
half-plane and the QNM neighborhoods; the local jet coefficients must equal it. -/
theorem original_coefficients_analytic (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (hw : w.im≠0) :
    AnalyticAt ℂ (incomingValue q br amp K) w ∧
      AnalyticAt ℂ (incomingSlope q br amp K) w ∧
      AnalyticAt ℂ (oppositeValue q br amp K) w := by
  obtain ⟨hI,hO⟩ := original_profiles_germ q br amp K w hw
  obtain ⟨h0,h1,_⟩ := hI.canonical
  exact ⟨h0,h1,hO.canonical.1⟩

/-- Any admitted original incoming jet has exactly the same value and slope
as the source-defined family, on its entire parameter set. -/
theorem original_incoming_coefficients_unique (q : XiZeroCopy) (br : Bool) (amp K : ℂ)
    {S : Set ℂ} {b C : ℝ} {c₀ c₁ : ℂ→ℂ}
    (h : HasUniformJet2 S b (incomingProfile q br amp K) c₀ c₁ C) (hb : 0<b)
    {w : ℂ} (hw : w∈S) :
    incomingValue q br amp K w=c₀ w ∧ incomingSlope q br amp K w=c₁ w :=
  h.canonical_coefficients hb hw

theorem original_opposite_coefficient_unique (q : XiZeroCopy) (br : Bool) (amp K : ℂ)
    {S : Set ℂ} {b C : ℝ} {d₀ d₁ : ℂ→ℂ}
    (h : HasUniformJet2 S b (oppositeProfile q br amp K) d₀ d₁ C) (hb : 0<b)
    {w : ℂ} (hw : w∈S) : oppositeValue q br amp K w=d₀ w :=
  (h.canonical_coefficients hb hw).1

end
end RHTower.D4BMOriginalCanonicalHorizon
