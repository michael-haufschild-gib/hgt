import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.ThermalReflection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Spectators.ExactComplement
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateIsMeromorphicInThePlane

/-! # The complete meromorphic divisor of the remaining gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology ZeroForcingCalculus InverseSpectrum.ShellMixing

variable {ι κ : Type*} [Fintype ι]

private theorem analytic_trace (a : ι → ℕ+) (s : ℂ) : AnalyticAt ℂ (finiteHeatTrace a) s :=
  Finset.analyticAt_fun_sum _ (fun _ _ => (analyticAt_id.neg.mul analyticAt_const).cexp)

private theorem trace_eq_finite (a : ι → ℕ+) : subsystemTrace a = finiteHeatTrace a :=
  funext fun _ => tsum_fintype _

/-- Off the imaginary axis every zeta zero or pole survives. On the axis precisely the finite-factor zeros become poles. -/
theorem entire_complement_divisor {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) (s : ℂ) :
    meromorphicOrderAt (complementPartition a) s =
      if s.re = 0 then -meromorphicOrderAt (finiteHeatTrace a) s else meromorphicOrderAt riemannZeta s := by
  rw [complementPartition,trace_eq_finite,meromorphicOrderAt_div (meromorphicAt_riemannZeta s) (analytic_trace a s).meromorphicAt]
  split
  · rename_i hs
    have h1 : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
    have han : AnalyticAt ℂ riemannZeta s := ZeroForcingCalculus.analyticAt_riemannZeta h1
    rw [meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero han (ExclusionOfTheCriticalState.riemannZeta_ne_zero_of_re_eq_zero hs),
      zero_sub]
  · rename_i hs
    rw [meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (analytic_trace a s) (fun hz => hs (finite_partition_zeros_on_axis h hz)),
      sub_zero]

/-- The actual Gibbs trace uniquely fixes the meromorphic complement at every point of the plane. -/
theorem entire_complement_unique {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) {F : ℂ → ℂ}
    (hF : Meromorphic F) (hG : ∀ z : ℂ, 1 < z.re → F z = subsystemTrace b z) (s : ℂ) :
    F =ᶠ[𝓝[≠] s] complementPartition a := by
  have hm : MeromorphicOn (F-complementPartition a) Set.univ :=
    fun z _ => (hF z).sub (finiteStateComplement_meromorphic a z)
  have ht : meromorphicOrderAt (F-complementPartition a) (2:ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hnb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by change (1:ℝ)<2; norm_num)
    filter_upwards [nhdsWithin_le_nhds hnb] with z hz
    exact sub_eq_zero.mpr ((hG z hz).trans (complementPartition_trace h hz).symm)
  have hs : meromorphicOrderAt (F-complementPartition a) s = ⊤ := by
    by_contra hn
    exact (hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ s)
      (Set.mem_univ (2:ℂ)) hn) ht
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hs] with z hz
  exact sub_eq_zero.mp hz

#print axioms entire_complement_divisor
#print axioms entire_complement_unique

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
