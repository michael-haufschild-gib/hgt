import GaloisForLFunctions.RHTower.PrimeZetaOneLineConvergence

/-!
# Uniform compact-frequency PNT tail for the prime phase

The PNT error contribution to the prime phase is uniformly small on every fixed compact frequency
band.  The proof uses one `λ`-independent integrable majorant.  Consequently the factor
`(|λ| log U)⁻¹` in the explicit oscillatory main term, not the PNT error, is the sole nonuniform
mechanism as the frequency approaches zero with the cutoff.

This does not control the completed prime--polar source in that shrinking boundary layer; it
separates the established outer analytic regime from the RH-bearing cancellation problem.
-/

namespace RHTower

open Filter MeasureTheory Set
open scoped Topology

/-- On every compact frequency band, the PNT-error part of Abel summation has a uniform tail.

No zero-location or RH assumption enters: the only input is the unconditional de la Vallée
Poussin error already formalized for `Chebyshev.theta`. -/
theorem exists_uniform_compact_oscLogKernelDeriv_thetaError_tail
    (R eps : ℝ) (hR : 0 ≤ R) (heps : 0 < eps) :
    ∃ U : ℝ, 2 ≤ U ∧ ∀ x : ℝ, U ≤ x → ∀ lam : ℝ, |lam| ≤ R →
      ‖∫ t in Ioi x,
        oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ) : ℂ))‖ < eps := by
  obtain ⟨c, hc, hthetaO⟩ := RHTower.Sieve.chebyshevTheta_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hthetaO
  obtain ⟨C, hC⟩ := hthetaO
  rcases (eventually_atTop.1 hC) with ⟨T, hT⟩
  set K : ℝ := (1 + R) * (Real.log 2)⁻¹ + ((Real.log 2)⁻¹) ^ 2
  set A : ℝ := K * |C|
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have htail : Tendsto (fun x : ℝ => ∫ t in Ioi x,
      A * (Real.exp (-c * Real.sqrt (Real.log t)) / t)) atTop (nhds 0) :=
    MeasureTheory.tendsto_integral_Ioi_zero Filter.tendsto_id
  have hsmall : ∀ᶠ x : ℝ in atTop, ∫ t in Ioi x,
      A * (Real.exp (-c * Real.sqrt (Real.log t)) / t) < eps :=
    htail.eventually (eventually_lt_nhds heps)
  have hready := hsmall.and (eventually_ge_atTop (max 2 T))
  rcases (eventually_atTop.1 hready) with ⟨U, hU⟩
  refine ⟨U, ?_, ?_⟩
  · exact (le_max_left 2 T).trans (hU U (le_refl U)).2
  · intro x hx lam hlam
    have hxReady := hU x hx
    have hx2 : 2 ≤ x := (le_max_left 2 T).trans hxReady.2
    have hmajor : IntegrableOn
        (fun t : ℝ => A * (Real.exp (-c * Real.sqrt (Real.log t)) / t)) (Ioi x) :=
      ((integrableOn_pntErrorWeight hc).mono_set (Ioi_subset_Ioi hx2)).const_mul A
    have hbound := norm_integral_le_of_norm_le
      (f := fun t : ℝ =>
        oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ) : ℂ))) hmajor (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht2 : 2 ≤ t := le_trans hx2 ht.le
      have htT : T ≤ t := le_trans (le_max_right 2 T) (le_trans hxReady.2 ht.le)
      have htheta := hT t htT
      have ht0 : 0 < t := by linarith
      have hthetaNorm : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖ =
          t * Real.exp (-c * Real.sqrt (Real.log t)) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hthetaBound : |Chebyshev.theta t - t| ≤
          |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) := by
        rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hthetaNorm] at htheta
        refine htheta.trans ?_
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      have hcoef : (1 + |lam|) * (Real.log 2)⁻¹ + ((Real.log 2)⁻¹) ^ 2 ≤ K := by
        dsimp [K]
        have hlog2 : 0 ≤ (Real.log 2)⁻¹ := by positivity
        nlinarith
      have hderiv := norm_oscLogKernelDeriv_le lam ht2
      have hfactor : 0 ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) := by
        positivity
      have htinvsq : 0 ≤ (t ^ 2)⁻¹ := by positivity
      have hpoint : ‖oscLogKernelDeriv lam t‖ * |Chebyshev.theta t - t| ≤
          A * (Real.exp (-c * Real.sqrt (Real.log t)) / t) := by
        calc
          ‖oscLogKernelDeriv lam t‖ * |Chebyshev.theta t - t|
              ≤ (((1 + |lam|) * (Real.log 2)⁻¹ + ((Real.log 2)⁻¹) ^ 2) *
                  (t ^ 2)⁻¹) *
                  (|C| * (t * Real.exp (-c * Real.sqrt (Real.log t)))) := by
                refine mul_le_mul hderiv hthetaBound (abs_nonneg _) ?_
                positivity
          _ ≤ (K * (t ^ 2)⁻¹) *
                  (|C| * (t * Real.exp (-c * Real.sqrt (Real.log t)))) := by
                apply mul_le_mul_of_nonneg_right
                exact mul_le_mul_of_nonneg_right hcoef htinvsq
                exact hfactor
          _ = A * (Real.exp (-c * Real.sqrt (Real.log t)) / t) := by
                dsimp [A]
                field_simp
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using hpoint)
    exact lt_of_le_of_lt hbound hxReady.1

end RHTower
