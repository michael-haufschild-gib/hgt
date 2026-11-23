import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Traces
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.GermRecovery

/-! # Covariance of the relative partition on the right half-plane -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- The relative partition of the actual squared heat with one direction omitted. -/
def omissionPartition (v : MissingWave) := relativePartition (missingSpectrum v)

theorem omissionPartition_analytic (v : MissingWave) :
    AnalyticOnNhd ℂ (omissionPartition v) {z : ℂ | 0 < z.re} :=
  fun _ hz => analyticAt_relativePartition _ hz

theorem insertion_heat_analytic (a : ℕ+) (z : ℂ) : AnalyticAt ℂ (fun w => heat w a) z :=
  (analyticAt_id.neg.mul analyticAt_const).cexp

private theorem partition_real (v : MissingWave) (q : GibbsExponent) :
    omissionPartition v (q.val:ℂ) = (momentLoss q (missingSpectrum v):ℂ) := relativePartition_real _ q

private theorem inserted_at_real (a : ℕ+) (v : MissingWave) (q : TraceTemperature) :
    omissionPartition (insertMissing a v) (q.val:ℂ) = heat (q.val:ℂ) a*omissionPartition v (q.val:ℂ) := by
  have h := congrArg Complex.ofReal (inserted_real_moment a v q)
  rw [Complex.ofReal_mul,sectorWeight_power_heat,← partition_real,← partition_real] at h
  exact h

/-- Inserting any factor multiplies the entire relative thermal reading by its complex heat amplitude. -/
theorem omissionPartition_insert (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    omissionPartition (insertMissing a v) z = heat z a*omissionPartition v z := by
  let f := omissionPartition (insertMissing a v)
  let g (w : ℂ) := heat w a*omissionPartition v w
  have hg : AnalyticOnNhd ℂ g {w : ℂ | 0 < w.re} :=
    fun w hw => (insertion_heat_analytic a w).mul (omissionPartition_analytic v w hw)
  let u (n : ℕ) := 2+occupationWeight n
  have hu : Tendsto u atTop (𝓝 (2:ℝ)) := by
    simpa only [add_zero] using occupationWeight_tendsto.const_add 2
  have hacc : (2:ℂ) ∈ closure ({w | f w = g w} \ {(2:ℂ)}) := by
    apply mem_closure_of_tendsto ((Complex.continuous_ofReal.tendsto 2).comp hu)
    apply Eventually.of_forall
    intro n
    have hpos : (2:ℝ) < u n := lt_add_of_pos_right _ (occupationWeight_pos n)
    refine ⟨inserted_at_real a v ⟨u n,(by norm_num : (1:ℝ)<2).trans hpos⟩,?_⟩
    change (u n:ℂ) ≠ 2
    exact_mod_cast hpos.ne'
  exact (omissionPartition_analytic (insertMissing a v)).eqOn_of_preconnected_of_mem_closure hg
    (convex_halfSpace_re_gt 0).isPreconnected (by change 0 < (2:ℂ).re; norm_num) hacc hz

/-- The same scaling holds for relative real moments even when separate ordinary traces diverge. -/
theorem all_real_moments_insert (a : ℕ+) (v : MissingWave) (q : GibbsExponent) :
    momentLoss q (missingSpectrum (insertMissing a v)) = sectorWeight a^q.val*momentLoss q (missingSpectrum v) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,sectorWeight_power_heat,← partition_real,← partition_real]
  exact omissionPartition_insert a v (z := (q.val:ℂ)) q.property

/-- The fourth-trace loss is strictly positive, giving a nonvanishing reference in the connected domain. -/
theorem omissionPartition_two_ne (v : MissingWave) : omissionPartition v 2 ≠ 0 := by
  let q : GibbsExponent := ⟨2,by norm_num⟩
  have hr := partition_real v q
  change omissionPartition v 2 = (momentLoss ⟨2,by norm_num⟩ (missingSpectrum v):ℂ) at hr
  rw [hr,missingSpectrum,momentLoss_two,traceLoss_omitLine]
  exact Complex.ofReal_ne_zero.mpr (line_loss_bounds v).1.ne'

#print axioms omissionPartition_analytic
#print axioms insertion_heat_analytic
#print axioms omissionPartition_insert
#print axioms all_real_moments_insert
#print axioms omissionPartition_two_ne

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
