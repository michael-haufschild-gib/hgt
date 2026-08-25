import GaloisForLFunctions.HTGeometry.DiskMultiplierPrivalov

/-!
# Boundary logarithm from Jensen-controlled approximants

Fatou's lemma applied to the nonnegative deficits
`log B - log ‖F n‖` turns a uniform Jensen lower bound into genuine integrability of the
nonzero boundary logarithm.  This is the measure-theoretic core of the Hardy canonical
factorization; it is independent of any particular analytic model.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Uniformly bounded measurable approximants with a common Jensen lower bound cannot converge
almost everywhere to a nonzero function with a nonintegrable negative logarithm. -/
theorem integrable_log_norm_of_jensen_approx
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [IsProbabilityMeasure mu]
    (F : ℕ → X → ℂ) (f : X → ℂ) (B L : ℝ)
    (hB : 1 ≤ B)
    (hFmeas : ∀ n, Measurable (F n)) (hfmeas : Measurable f)
    (hFbound : ∀ n x, ‖F n x‖ ≤ B)
    (hfbound : ∀ x, ‖f x‖ ≤ B) (hfne : ∀ x, f x ≠ 0)
    (hFlogInt : ∀ n, Integrable (fun x => Real.log ‖F n x‖) mu)
    (hlower : ∀ n, L ≤ ∫ x, Real.log ‖F n x‖ ∂mu)
    (htend : ∀ᵐ x ∂mu, Tendsto (fun n => F n x) atTop (nhds (f x))) :
    Integrable (fun x => Real.log ‖f x‖) mu := by
  let g : ℕ → X → ℝ := fun n x => Real.log B - Real.log ‖F n x‖
  let gLim : X → ℝ := fun x => Real.log B - Real.log ‖f x‖
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hg_nonneg (n : ℕ) (x : X) : 0 ≤ g n x := by
    dsimp [g]
    by_cases hx : F n x = 0
    · rw [hx, norm_zero, Real.log_zero]
      simpa using hlogB
    · exact sub_nonneg.mpr
        (Real.log_le_log (norm_pos_iff.mpr hx) (hFbound n x))
  have hgLim_nonneg (x : X) : 0 ≤ gLim x := by
    dsimp [gLim]
    exact sub_nonneg.mpr
      (Real.log_le_log (norm_pos_iff.mpr (hfne x)) (hfbound x))
  have hg_meas (n : ℕ) : Measurable (g n) :=
    measurable_const.sub (Real.measurable_log.comp (hFmeas n).norm)
  have hgLim_meas : Measurable gLim :=
    measurable_const.sub (Real.measurable_log.comp hfmeas.norm)
  have hg_int (n : ℕ) : Integrable (g n) mu :=
    (integrable_const (Real.log B)).sub (hFlogInt n)
  have hg_integral_le (n : ℕ) :
      ∫ x, g n x ∂mu ≤ Real.log B - L := by
    dsimp [g]
    rw [integral_sub (integrable_const (Real.log B)) (hFlogInt n)]
    simp only [integral_const, probReal_univ, one_smul]
    linarith [hlower n]
  let C : ENNReal := ENNReal.ofReal (Real.log B - L)
  have hlin_le (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (g n x) ∂mu) ≤ C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hg_int n)
      (Filter.Eventually.of_forall (hg_nonneg n))]
    exact ENNReal.ofReal_le_ofReal (hg_integral_le n)
  have hliminf_le :
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂mu) atTop ≤ C := by
    apply liminf_le_of_le (hf := by isBoundedDefault)
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hlin_le n)
  have hpoint : ∀ᵐ x ∂mu,
      liminf (fun n => ENNReal.ofReal (g n x)) atTop =
        ENNReal.ofReal (gLim x) := by
    filter_upwards [htend] with x hx
    have hlog : Tendsto (fun n => Real.log ‖F n x‖) atTop
        (nhds (Real.log ‖f x‖)) :=
      hx.norm.log (norm_pos_iff.mpr (hfne x)).ne'
    have hg : Tendsto (fun n => g n x) atTop (nhds (gLim x)) := by
      simpa [g, gLim] using tendsto_const_nhds.sub hlog
    exact (ENNReal.continuous_ofReal.tendsto (gLim x) |>.comp hg).liminf_eq
  have hfatou := lintegral_liminf_le
    (μ := mu) (u := atTop)
    (fun n => ENNReal.measurable_ofReal.comp (hg_meas n))
  have hlinLim : ∫⁻ x, ENNReal.ofReal (gLim x) ∂mu ≤ C := by
    calc
      ∫⁻ x, ENNReal.ofReal (gLim x) ∂mu =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂mu := by
            exact lintegral_congr_ae (Filter.EventuallyEq.symm hpoint)
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂mu) atTop := hfatou
      _ ≤ C := hliminf_le
  have hgLim_int : Integrable gLim mu := by
    refine ⟨hgLim_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hgLim_nonneg)]
    exact hlinLim.trans_lt ENNReal.ofReal_lt_top
  have heq : (fun _x : X => Real.log B) - gLim =
      fun x => Real.log ‖f x‖ := by
    funext x
    dsimp [gLim]
    ring
  rw [← heq]
  exact (integrable_const (Real.log B)).sub hgLim_int

theorem integrable_log_norm_diskMultiplierBoundaryFun
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Integrable (fun z => Real.log ‖diskMultiplierBoundaryFun phi z‖)
      circleLebesgue := by
  let f : HardyDisk := hardyOf phi
  have hfne : f ≠ 0 := by
    intro hf0
    obtain ⟨z, hz, hphiz⟩ := hphi
    have hval := hardyFun_hardyOf phi
      (by simpa [Metric.mem_ball, dist_zero_right] using hz)
    have hzero : hardyFun (0 : HardyDisk) z = 0 := by
      rw [hardyFun]
      simp
    apply hphiz
    calc
      phi.fn z = hardyFun (hardyOf phi) z := hval.symm
      _ = hardyFun f z := rfl
      _ = hardyFun (0 : HardyDisk) z := by rw [hf0]
      _ = 0 := hzero
  have hfcoord : ∃ n, f n ≠ 0 := by
    by_contra h
    push Not at h
    apply hfne
    apply lp.ext
    funext n
    simpa using h n
  let n : ℕ := Nat.find hfcoord
  have hfn : f n ≠ 0 := Nat.find_spec hfcoord
  have hfbefore : ∀ k < n, f k = 0 := by
    intro k hk
    by_contra hfk
    have := Nat.find_min' hfcoord hfk
    omega
  let g : HardyDisk := hardyBack n f
  have hg0 : g 0 ≠ 0 := by
    simpa [g, n, Nat.zero_add] using hfn
  let sf : HardyDisk := ⟨shiftFun n g, memℓp_shiftFun (lp.memℓp g) n⟩
  have hfshift : f = sf := by
    apply lp.ext
    funext k
    change f k = shiftFun n g k
    by_cases hk : k < n
    · rw [shiftFun_of_lt hk, hfbefore k hk]
    · rw [shiftFun_of_le (Nat.le_of_not_gt hk)]
      simp only [g, hardyBack_apply]
      rw [Nat.sub_add_cancel (Nat.le_of_not_gt hk)]
  have hfactor {z : ℂ} (hz : ‖z‖ < 1) :
      phi.fn z = z ^ n * hardyFun g z := by
    rw [← hardyFun_hardyOf phi hz, show hardyOf phi = f from rfl, hfshift]
    exact hardyFun_shiftFun n g hz
  obtain ⟨ns, hns, hradial⟩ := exists_diskMultiplierRadialBoundary_subseq_ae phi
  have hradii : Tendsto (fun i => hardyDiskAbelRadius (ns i)) atTop (nhds 1) :=
    (tendsto_hardyDiskAbelRadius.mono_right inf_le_left).comp hns.tendsto_atTop
  have hrhalf : ∀ᶠ i in atTop, (1 / 2 : ℝ) ≤ hardyDiskAbelRadius (ns i) :=
    hradii.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hrhalf
  let idx : ℕ → ℕ := fun i => ns (i + N)
  let r : ℕ → ℝ := fun i => hardyDiskAbelRadius (idx i)
  have hr1 (i : ℕ) : r i < 1 := hardyDiskAbelRadius_lt_one _
  have hrhalf' (i : ℕ) : (1 / 2 : ℝ) ≤ r i := by
    exact hN (i + N) (by omega)
  have hr0 (i : ℕ) : 0 < r i := lt_of_lt_of_le (by norm_num) (hrhalf' i)
  let F : ℕ → Circle → ℂ := fun i z =>
    hardyFun g ((r i : ℂ) * (z : ℂ))
  let B : ℝ := max 1 (phi.bd / (1 / 2 : ℝ) ^ n)
  have hB : 1 ≤ B := le_max_left _ _
  have hFbound : ∀ i z, ‖F i z‖ ≤ B := by
    intro i z
    have hzarg : ‖(r i : ℂ) * (z : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 i),
        Circle.norm_coe, mul_one]
      exact hr1 i
    have hfac := congrArg norm (hfactor hzarg)
    have hpowpos : 0 < (r i) ^ n := pow_pos (hr0 i) _
    have hphibd := phi.bd_le ((r i : ℂ) * (z : ℂ))
      (by simpa [Metric.mem_ball, dist_zero_right] using hzarg)
    have hnormarg : ‖(r i : ℂ) * (z : ℂ)‖ = r i := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 i),
        Circle.norm_coe, mul_one]
    rw [norm_mul, norm_pow, hnormarg] at hfac
    have hgBound : ‖F i z‖ ≤ phi.bd / (r i) ^ n := by
      dsimp [F]
      apply (le_div_iff₀ hpowpos).2
      rw [mul_comm, ← hfac]
      exact hphibd
    have hden : (1 / 2 : ℝ) ^ n ≤ (r i) ^ n :=
      pow_le_pow_left₀ (by norm_num) (hrhalf' i) _
    have hdiv : phi.bd / (r i) ^ n ≤ phi.bd / (1 / 2 : ℝ) ^ n :=
      div_le_div_of_nonneg_left phi.bd_nonneg
        (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _) hden
    exact hgBound.trans (hdiv.trans (le_max_right _ _))
  let R : ℕ → ℝ := fun i => (1 + (r i)⁻¹) / 2
  have hR1 (i : ℕ) : 1 < R i := by
    have hmul : r i * (r i)⁻¹ = 1 := mul_inv_cancel₀ (hr0 i).ne'
    have hgap := mul_pos (sub_pos.mpr (hr1 i)) (inv_pos.mpr (hr0 i))
    have hinv : 1 < (r i)⁻¹ := by nlinarith
    dsimp [R]
    linarith
  have hRinv (i : ℕ) : R i < (r i)⁻¹ := by
    have hmul : r i * (r i)⁻¹ = 1 := mul_inv_cancel₀ (hr0 i).ne'
    have hgap := mul_pos (sub_pos.mpr (hr1 i)) (inv_pos.mpr (hr0 i))
    have hinv : 1 < (r i)⁻¹ := by nlinarith
    dsimp [R]
    linarith
  have hrR (i : ℕ) : r i * R i < 1 := by
    calc
      r i * R i < r i * (r i)⁻¹ := mul_lt_mul_of_pos_left (hRinv i) (hr0 i)
      _ = 1 := mul_inv_cancel₀ (hr0 i).ne'
  let Fi : ℕ → ℂ → ℂ := fun i z => hardyFun g ((r i : ℂ) * z)
  have hFi (i : ℕ) : AnalyticOnNhd ℂ (Fi i) (Metric.ball 0 (R i)) := by
    intro z hz
    have hznorm : ‖z‖ < R i := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have harg : ‖(r i : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 i)]
      exact (mul_lt_mul_of_pos_left hznorm (hr0 i)).trans (hrR i)
    have hgAn : AnalyticAt ℂ (hardyFun g) ((r i : ℂ) * z) :=
      (hasFPowerSeriesOnBall_hardyFun g).analyticAt_of_mem (by
        rw [eball_one_eq, Metric.mem_ball, dist_zero_right]
        exact harg)
    exact hgAn.comp (analyticAt_const.mul analyticAt_id)
  have hFi0 (i : ℕ) : Fi i 0 ≠ 0 := by
    simpa [Fi, hardyFun_zero] using hg0
  have hFmeas : ∀ i, Measurable (F i) := by
    intro i
    have hcont : Continuous (F i) := by
      change Continuous (fun z : Circle => Fi i (z : ℂ))
      exact (hFi i).continuousOn.comp_continuous (by fun_prop) fun z => by
        rw [Metric.mem_ball, dist_zero_right, Circle.norm_coe]
        exact hR1 i
    exact hcont.measurable
  have hFiClosed (i : ℕ) :
      AnalyticOnNhd ℂ (Fi i) (Metric.closedBall 0 (1 : ℝ)) :=
    (hFi i).mono fun z hz => by
      rw [Metric.mem_ball, dist_zero_right]
      have hzle : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      exact hzle.trans_lt (hR1 i)
  have hFiMeas (i : ℕ) : Measurable (Fi i) := by
    dsimp [Fi, hardyFun]
    apply Measurable.tsum
    intro k
    fun_prop
  have hFlogInt : ∀ i, Integrable (fun z => Real.log ‖F i z‖)
      circleLebesgue := by
    intro i
    refine integrable_circleLebesgue_of_intervalIntegrable
      (fun w => Real.log ‖Fi i w‖)
      (Real.measurable_log.comp (hFiMeas i).norm) ?_
    have ha : AnalyticOnNhd ℂ (Fi i) (Metric.closedBall 0 |(1 : ℝ)|) := by
      simpa using hFiClosed i
    exact (ha.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hlower : ∀ i, Real.log ‖g 0‖ ≤
      ∫ z, Real.log ‖F i z‖ ∂circleLebesgue := by
    intro i
    have ha : AnalyticOnNhd ℂ (Fi i) (Metric.closedBall 0 |(1 : ℝ)|) := by
      simpa using hFiClosed i
    have hj := log_norm_center_le_circleAverage_log_norm (Fi i) ha (hFi0 i)
    have hmeas : AEStronglyMeasurable
        (fun z : Circle => Real.log ‖Fi i (z : ℂ)‖) circleLebesgue :=
      (hFlogInt i).aestronglyMeasurable
    rw [← integral_circleLebesgue_eq_circleAverage
      (fun w => Real.log ‖Fi i w‖) hmeas] at hj
    simpa [F, Fi, hardyFun_zero] using hj
  let raw : Circle → ℂ := fun z =>
    diskMultiplierBoundaryMeasurableRep phi z / (z : ℂ) ^ n
  have hrawMeas : Measurable raw := by
    dsimp [raw]
    exact (measurable_diskMultiplierBoundaryMeasurableRep phi).div (by fun_prop)
  let boundary : Circle → ℂ := fun z =>
    if raw z ≠ 0 ∧ ‖raw z‖ ≤ B then raw z else 1
  have hset : MeasurableSet {z | raw z ≠ 0 ∧ ‖raw z‖ ≤ B} := by
    exact ((hrawMeas (measurableSet_singleton 0)).compl).inter
      (hrawMeas.norm measurableSet_Iic)
  have hboundaryMeas : Measurable boundary :=
    Measurable.ite hset hrawMeas measurable_const
  have hboundaryBound (z : Circle) : ‖boundary z‖ ≤ B := by
    dsimp [boundary]
    split_ifs with hz
    · exact hz.2
    · simpa using hB
  have hboundaryNe (z : Circle) : boundary z ≠ 0 := by
    dsimp [boundary]
    split_ifs with hz
    · exact hz.1
    · exact one_ne_zero
  have hphiBdB : phi.bd ≤ B := by
    have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
    have hpOne : (1 / 2 : ℝ) ^ n ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hdiv : phi.bd ≤ phi.bd / (1 / 2 : ℝ) ^ n := by
      rw [le_div_iff₀ hp]
      nlinarith [phi.bd_nonneg]
    exact hdiv.trans (le_max_right _ _)
  have hrawGood : ∀ᵐ z ∂circleLebesgue, raw z ≠ 0 ∧ ‖raw z‖ ≤ B := by
    filter_upwards [diskMultiplierBoundary_ne_zero_ae phi hphi,
      diskMultiplierBoundaryMeasurableRep_ae phi,
      ae_norm_diskMultiplierBoundaryFun_le phi] with z hne hrep hbd
    have hzpow : (z : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by
      rw [← norm_pos_iff, Circle.norm_coe]
      norm_num)
    constructor
    · dsimp [raw]
      rw [hrep]
      exact div_ne_zero hne hzpow
    · dsimp [raw]
      rw [hrep, norm_div, norm_pow, Circle.norm_coe, one_pow, div_one]
      exact hbd.trans hphiBdB
  have hboundaryRaw : boundary =ᵐ[circleLebesgue] raw := by
    filter_upwards [hrawGood] with z hz
    simp [boundary, hz]
  have hrtend : Tendsto r atTop (nhds 1) := by
    have hadd : StrictMono (fun i : ℕ => i + N) := by
      intro a b hab
      exact Nat.add_lt_add_right hab N
    exact hradii.comp hadd.tendsto_atTop
  have htend : ∀ᵐ z ∂circleLebesgue,
      Tendsto (fun i => F i z) atTop (nhds (boundary z)) := by
    filter_upwards [hradial, diskMultiplierBoundaryMeasurableRep_ae phi,
      hboundaryRaw] with z hzrad hzrep hzboundary
    have hadd : StrictMono (fun i : ℕ => i + N) := by
      intro a b hab
      exact Nat.add_lt_add_right hab N
    have hnum : Tendsto
        (fun i => diskMultiplierRadialBoundaryFun (idx i) phi z) atTop
        (nhds (diskMultiplierBoundaryMeasurableRep phi z)) := by
      have hc := hzrad.comp hadd.tendsto_atTop
      simpa [Function.comp_def, idx, hzrep] using hc
    have hden : Tendsto
        (fun i => (((r i : ℝ) : ℂ) * (z : ℂ)) ^ n) atTop
        (nhds ((z : ℂ) ^ n)) := by
      have hrC : Tendsto (fun i => ((r i : ℝ) : ℂ)) atTop (nhds (1 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp hrtend
      simpa using (hrC.mul_const (z : ℂ)).pow n
    have hzpow : (z : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by
      rw [← norm_pos_iff, Circle.norm_coe]
      norm_num)
    have hquot := hnum.div hden hzpow
    rw [hzboundary]
    change Tendsto (fun i => F i z) atTop (nhds (raw z))
    apply hquot.congr'
    filter_upwards with i
    have harg : ‖((r i : ℝ) : ℂ) * (z : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 i),
        Circle.norm_coe, mul_one]
      exact hr1 i
    have hfac := hfactor harg
    have hdenne : ((((r i : ℝ) : ℂ) * (z : ℂ)) ^ n) ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero (by exact_mod_cast (hr0 i).ne') (by
        rw [← norm_pos_iff, Circle.norm_coe]
        norm_num))
    change diskMultiplierRadialBoundaryFun (idx i) phi z /
      ((((r i : ℝ) : ℂ) * (z : ℂ)) ^ n) = F i z
    apply (div_eq_iff hdenne).2
    rw [diskMultiplierRadialBoundaryFun]
    simpa [F, mul_comm] using hfac
  have hboundaryLog := integrable_log_norm_of_jensen_approx
    F boundary B (Real.log ‖g 0‖) hB hFmeas hboundaryMeas hFbound
      hboundaryBound hboundaryNe hFlogInt hlower htend
  have hrawLog : Integrable (fun z => Real.log ‖raw z‖) circleLebesgue :=
    hboundaryLog.congr (hboundaryRaw.mono fun z hz => by
      exact congrArg (fun w : ℂ => Real.log ‖w‖) hz)
  have hrepLog : Integrable
      (fun z => Real.log ‖diskMultiplierBoundaryMeasurableRep phi z‖)
      circleLebesgue := by
    apply hrawLog.congr
    filter_upwards with z
    dsimp [raw]
    rw [norm_div, norm_pow, Circle.norm_coe, one_pow, div_one]
  exact hrepLog.congr ((diskMultiplierBoundaryMeasurableRep_ae phi).mono
    fun z hz => congrArg (fun w : ℂ => Real.log ‖w‖) hz)


end

end GaloisForLFunctions.HTGeometry
