import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceRadialAdmission

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceRadialRestoration
open D4BMJointSource D4BMModularCore D4BMOriginalSourceTailCollar D4BMOriginalSourceRadialAdmission
noncomputable section
set_option autoImplicit false
private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q

def sourceFunctional (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  mu q*(mu q-2)*(originalPeriodError q br amp w b L k-originalPeriodError q br amp w a L k+
    2*w*(∫ p in a..b,originalPeriodError q br amp w p L k))

def horizonSourceFunctional (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b k : ℝ) : ℂ :=
  mu q*(mu q-2)*(horizonPeriodError q br amp w b k-horizonPeriodError q br amp w a k+
    2*w*(∫ p in a..b,horizonPeriodError q br amp w p k))

def sourceError (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  let d := fun p => originalPeriodError q br amp w p L k-horizonPeriodError q br amp w p k
  mu q*(mu q-2)*(d b-d a+2*w*(∫ p in a..b,d p))

/-- The complete original source functional, including both temporal endpoints,
is separately radially admitted before any leading-trace subtraction. -/
theorem source_radial_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ a b k A B : ℝ,
      0<a → a≤b → 0≤k → 4≤Real.exp k → L0≤A → A≤B →
      IntervalIntegrable (fun L => sourceFunctional q br amp w a b L k) volume A B := by
  obtain ⟨G1,hG1,h1⟩ := endpoint_radial_integrable q br amp
  obtain ⟨G2,_,h2⟩ := moment_radial_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨L1,hL1,hl1⟩ := h1 w hwi hw1
  obtain ⟨L2,hL2,hl2⟩ := h2 w hwi hw2
  refine ⟨max L1 L2,lt_of_lt_of_le hL1 (le_max_left _ _),?_⟩
  intro a b k A B ha hab hk hk4 hA hAB
  have hA1 := (le_max_left L1 L2).trans hA
  have hA2 := (le_max_right L1 L2).trans hA
  exact (((hl1 b k A B (ha.trans_le hab) hk hk4 hA1 hAB).sub
    (hl1 a k A B ha hk hk4 hA1 hAB)).add ((hl2 a b k A B ha hab hk hk4 hA2 hAB).const_mul (2*w))).const_mul _

/-- The source endpoint/moment error is exactly the difference of the two
separately time-admitted physical source functionals. -/
theorem source_difference (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a b L k : ℝ,
      0<a → a≤b → 0<L → 0≤k → 4≤Real.exp k →
      sourceFunctional q br amp w a b L k-horizonSourceFunctional q br amp w a b k=
        sourceError q br amp w a b L k := by
  obtain ⟨G,hG,hg⟩ := horizon_period_time_integrable q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw a b L k ha hab hL hk hk4
  unfold sourceFunctional horizonSourceFunctional sourceError
  dsimp only
  rw [intervalIntegral.integral_sub (period_time_integrable q br amp w a b L k ha.le hab hL hk4)
    (hg w hwi hw a b k ha hab hk hk4)]
  ring

theorem exponential_interval_bound (f : ℝ→ℂ) (C a b : ℝ) (hC : 0≤C) (hab : a≤b)
    (h : ∀ p∈Icc a b,‖f p‖≤C*Real.exp (-p)) :
    ‖∫ p in a..b,f p‖≤C*Real.exp (-a) := by
  have hi : IntervalIntegrable (fun p : ℝ => C*Real.exp (-p)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall (fun p hp => h p (Ioc_subset_Icc_self hp))) hi
  calc
    _ ≤ ∫ p in a..b,C*Real.exp (-p) := hb
    _ = C*(Real.exp (-a)-Real.exp (-b)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp]
    _ ≤ C*Real.exp (-a) := by nlinarith [Real.exp_nonneg (-b)]

/-- The complete source endpoint/moment functional inherits the actual mixed
cusp/horizon error uniformly over every positive temporal interval. -/
theorem source_error_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ C : ℝ,0≤C ∧
      ∀ᶠ L : ℝ in atTop,∀ a b k : ℝ,0<a → a≤b → 0≤k → 4≤Real.exp k →
        ‖sourceError q br amp w a b L k‖≤C*Real.exp (-L)*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := original_period_mixed_error q br amp N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := hg w hwi hw
  refine ⟨‖mu q*(mu q-2)‖*(2+‖2*w‖)*C,by positivity,?_⟩
  filter_upwards [hc] with L hL a b k ha hab hk hk4
  let d := fun p => originalPeriodError q br amp w p L k-horizonPeriodError q br amp w p k
  let A := C*Real.exp (-L)*Real.exp (-(N:ℝ)*k)
  have hA : 0≤A := by dsimp [A];positivity
  have hd (p : ℝ) (hp : 0<p) : ‖d p‖≤A*Real.exp (-p) := hL p k hp hk hk4
  have hsmall (p : ℝ) (hp : 0<p) : ‖d p‖≤A :=
    (hd p hp).trans ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith : -p≤0)) hA).trans_eq (mul_one A))
  have hi : ‖∫ p in a..b,d p‖≤A :=
    (exponential_interval_bound d A a b hA hab (fun p hp => hd p (ha.trans_le hp.1))).trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith : -a≤0)) hA).trans_eq (mul_one A))
  change ‖mu q*(mu q-2)*(d b-d a+2*w*(∫ p in a..b,d p))‖≤_
  rw [norm_mul]
  calc
    _ ≤ ‖mu q*(mu q-2)‖*(‖d b‖+‖d a‖+‖2*w‖*‖∫ p in a..b,d p‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_of_eq (norm_mul _ _)))
    _ ≤ ‖mu q*(mu q-2)‖*(A+A+‖2*w‖*A) := by
      gcongr
      · exact hsmall b (ha.trans_le hab)
      · exact hsmall a ha
    _ = _ := by dsimp [A];ring

/-- The actual source error has a radial bound uniform in both temporal
endpoints and every finite horizon cutoff, at any sufficiently deep interface. -/
theorem source_error_collar_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ C L0 : ℝ,0≤C ∧ 0<L0 ∧
      ∀ a b k A B : ℝ,0<a → a≤b → 0≤k → 4≤Real.exp k → L0≤A → A≤B →
        ‖∫ L in A..B,sourceError q br amp w a b L k‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := source_error_bound q br amp N
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := hg w hwi hw
  obtain ⟨D,hD⟩ := eventually_atTop.mp hc
  let L0 := max D 1
  have hL0 : 0<L0 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  refine ⟨C,L0,hC,hL0,?_⟩
  intro a b k A B ha hab hk hk4 hA hAB
  have hCa : 0≤C*Real.exp (-(N:ℝ)*k) := by positivity
  have hi := exponential_interval_bound (fun L => sourceError q br amp w a b L k)
    (C*Real.exp (-(N:ℝ)*k)) A B hCa hAB (fun L hL => by
      have h := hD L ((le_max_left D 1).trans (hA.trans hL.1)) a b k ha hab hk hk4
      simpa only [mul_assoc,mul_comm,mul_left_comm] using h)
  exact hi.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
    (by linarith [hL0.trans_le hA] : -A≤0)) hCa).trans_eq (mul_one _))

/-- Independent-cutoff restoration of the separately admitted complete physical
source functional and its actual leading horizon trace, with both endpoints and
the original one-half collar Jacobian. -/
theorem source_radial_joint_limit (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧
      ∀ (T : ℝ×ℝ→{v : ℝ×ℝ // 0<v.1 ∧ v.1≤v.2}) (M : ℝ×ℝ→Ici L0),
        Tendsto (fun z : ℝ×ℝ =>
          ((∫ L in L0..(M z:ℝ),sourceFunctional q br amp w (T z).val.1 (T z).val.2 L z.2)-
            ((M z:ℝ)-L0)•horizonSourceFunctional q br amp w (T z).val.1 (T z).val.2 z.2)/2)
          ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨G1,hG1,h1⟩ := source_difference q br amp
  obtain ⟨G2,_,h2⟩ := source_error_collar_bound q br amp 1
  obtain ⟨G3,_,h3⟩ := source_radial_integrable q br amp
  refine ⟨max G1 (max G2 G3),le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 (max G2 G3)]
  have hw2 : G2+1≤w.re := by linarith [(le_max_left G2 G3).trans (le_max_right G1 (max G2 G3))]
  have hw3 : G3+1≤w.re := by linarith [(le_max_right G2 G3).trans (le_max_right G1 (max G2 G3))]
  obtain ⟨C,L2,hC,hL2,hbound⟩ := h2 w hwi hw2
  obtain ⟨L3,hL3,hadmit⟩ := h3 w hwi hw3
  let L0 := max L2 L3
  have hL0 : 0<L0 := lt_of_lt_of_le hL2 (le_max_left _ _)
  refine ⟨L0,hL0,?_⟩
  intro T M
  have hcut : ∀ᶠ z : ℝ×ℝ in ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)),0≤z.2 ∧ 4≤Real.exp z.2 :=
    tendsto_snd.eventually ((eventually_ge_atTop (0:ℝ)).and (Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (4:ℝ))))
  have he : Tendsto (fun z : ℝ×ℝ => ∫ L in L0..(M z:ℝ),sourceError q br amp w (T z).val.1 (T z).val.2 L z.2)
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    have hlim : Tendsto (fun z : ℝ×ℝ => C*Real.exp (-z.2))
        ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
      simpa only [Function.comp_def,mul_zero] using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).comp tendsto_snd
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hcut] with z hz
    simpa only [Nat.cast_one,neg_one_mul] using hbound (T z).val.1 (T z).val.2 z.2 L0 (M z)
      (T z).property.1 (T z).property.2 hz.1 hz.2 (le_max_left _ _) (M z).property
  have hd := he.div_const (2:ℂ)
  simp only [zero_div] at hd
  apply hd.congr'
  filter_upwards [hcut] with z hz
  have hM : L0≤(M z:ℝ) := (M z).property
  have hi := hadmit (T z).val.1 (T z).val.2 z.2 L0 (M z) (T z).property.1 (T z).property.2
    hz.1 hz.2 (le_max_right _ _) hM
  have heq : (∫ L in L0..(M z:ℝ),sourceError q br amp w (T z).val.1 (T z).val.2 L z.2)=
      (∫ L in L0..(M z:ℝ),sourceFunctional q br amp w (T z).val.1 (T z).val.2 L z.2)-
        ((M z:ℝ)-L0)•horizonSourceFunctional q br amp w (T z).val.1 (T z).val.2 z.2 := by
    calc
      _ = ∫ L in L0..(M z:ℝ),sourceFunctional q br amp w (T z).val.1 (T z).val.2 L z.2-
          horizonSourceFunctional q br amp w (T z).val.1 (T z).val.2 z.2 := by
        apply intervalIntegral.integral_congr
        intro L hL
        have hLI : L∈Icc L0 (M z:ℝ) := by simpa only [uIcc_of_le hM] using hL
        exact (h1 w hwi hw1 (T z).val.1 (T z).val.2 L z.2 (T z).property.1 (T z).property.2
          (hL0.trans_le hLI.1) hz.1 hz.2).symm
      _ = _ := by rw [intervalIntegral.integral_sub hi intervalIntegrable_const,intervalIntegral.integral_const]
  rw [heq]

end
end RHTower.D4BMOriginalSourceRadialRestoration
