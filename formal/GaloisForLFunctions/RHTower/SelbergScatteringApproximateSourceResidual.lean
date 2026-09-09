import GaloisForLFunctions.RHTower.SelbergScatteringSourceNonvanishing

/-!
# Exact positive residual limit of the original cutoff family

Every complete original compact modular source approximant is nonzero and
produces an actual unit vector in the entire operator domain. Both normalized
values and actual operator images converge to the fixed corrected source.
Their full-Xi residuals therefore converge to its strictly positive residual.
This rules out approximate occurrence from this particular cutoff family,
while retaining its exact unit-domain construction and complete graph limit.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergScatteringApproximateSourceResidual
open D4BMModularCore SelbergScatteringSourceApproximation SelbergScatteringSourceNonvanishing
open SelbergScatteringSourceVector SelbergScatteringEntireOperator SelbergScatteringEntireXiPackets
noncomputable section

/-- Every actual compact source approximant is nonzero, as the complete source
is unchanged at a nonzero closed-cell point below the transition. -/
theorem sourceApproxDomain_ne_zero (q : XiZeroCopy) (n : ℕ) :
    (sourceApproxDomain q n : Space)≠0 := by
  intro h
  have hc : ((sourceApproxDomain q n : Space) : UpperHalfPlane → ℂ) =ᵐ[measure]
      (sourceCore q n).field :=
    (core_field_memLp (sourceCore q n).field (sourceCore q n).smooth (sourceCore q n).compact).coeFn_toLp
  have hz : ((sourceApproxDomain q n : Space) : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun _ => (0:ℂ)) := by
    rw [h]
    exact Lp.coeFn_zero ℂ 2 measure
  have hg := hc.symm.trans hz
  change (sourceCore q n).field =ᵐ[volume.restrict fd] (fun _ => (0:ℂ)) at hg
  have hclosure : fd ⊆ closure (interior fd) := by rw [← fdo_eq_interior_fd,← fd_eq_closure_fdo]
  have he := Measure.eqOn_of_ae_eq hg (sourceCore q n).smooth.continuous.continuousOn
    continuousOn_const hclosure
  obtain ⟨z,hz,hy,hn⟩ := globalResidual_nonzero_below_transition q
  have ha : z.im ≤ cutoffHeight n := by
    unfold cutoffHeight
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hh := he hz
  rw [sourceCore_field_on_fd q n z hz,heightWeight_one n z.im ha] at hh
  exact hn (by simpa only [Complex.ofReal_one,one_mul] using hh)

theorem sourceApproxCovariance_norm_pos (q : XiZeroCopy) (n : ℕ) :
    0 < ‖entireCovariance (sourceApproxDomain q n : Space)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  exact sourceApproxDomain_ne_zero q n (entireCovariance_injective (by simpa only [map_zero] using hz))

/-- The complete compact approximants produce actual entire-domain vectors. -/
def sourceApproxEntireDomain (q : XiZeroCopy) (n : ℕ) : entireOperator.domain :=
  ⟨entireCovariance (sourceApproxDomain q n : Space),entireCovariance_mem_domain _⟩

/-- The actual unit domain sequence from the full original modular cutoffs. -/
def sourceApproxEntireUnit (q : XiZeroCopy) (n : ℕ) : entireOperator.domain :=
  ((‖entireCovariance (sourceApproxDomain q n : Space)‖⁻¹:ℝ):ℂ) • sourceApproxEntireDomain q n

theorem sourceApproxEntireUnit_norm (q : XiZeroCopy) (n : ℕ) :
    ‖(sourceApproxEntireUnit q n : Space)‖=1 := by
  rw [sourceApproxEntireUnit,Submodule.coe_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sourceApproxCovariance_norm_pos q n))]
  exact inv_mul_cancel₀ (sourceApproxCovariance_norm_pos q n).ne'

/-- Exact full-Xi equation of each complete approximant in the entire domain. -/
theorem sourceApproxEntireDomain_equation (q : XiZeroCopy) (n : ℕ) :
    entireOperator (sourceApproxEntireDomain q n) -
      xiEntireTarget q • (sourceApproxEntireDomain q n : Space) =
      (sourceApproxDomain q n : Space) -
        (2+xiEntireTarget q) • entireCovariance (sourceApproxDomain q n : Space) := by
  rw [sourceApproxEntireDomain,entireOperator_apply_covariance]
  change (sourceApproxDomain q n : Space) - (2:ℂ) • entireCovariance (sourceApproxDomain q n : Space) -
    xiEntireTarget q • entireCovariance (sourceApproxDomain q n : Space) = _
  rw [add_smul]
  module

/-- Exact normalized residual of the actual cutoff sequence, with its nonzero
normalization denominator and entire complex target retained. -/
theorem sourceApproxEntireUnit_residual_norm (q : XiZeroCopy) (n : ℕ) :
    ‖entireOperator (sourceApproxEntireUnit q n) - xiEntireTarget q • (sourceApproxEntireUnit q n : Space)‖ =
      ‖entireCovariance (sourceApproxDomain q n : Space)‖⁻¹ *
        ‖(sourceApproxDomain q n : Space) - (2+xiEntireTarget q) • entireCovariance (sourceApproxDomain q n : Space)‖ := by
  rw [sourceApproxEntireUnit,entireOperator.map_smul,Submodule.coe_smul,
    smul_comm (xiEntireTarget q),← smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sourceApproxCovariance_norm_pos q n)),sourceApproxEntireDomain_equation]

/-- The actual normalized entire-domain values converge to the fixed complete
source unit vector in the original Hilbert norm. -/
theorem sourceApproxEntireUnit_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => (sourceApproxEntireUnit q n : Space)) atTop (𝓝 (sourceUnitVector q : Space)) := by
  have hc := (entireCovariance.continuous.tendsto (sourceVector q)).comp (sourceApproxDomain_tendsto q)
  have hn := hc.norm.inv₀ (sourceCovariance_norm_pos q).ne'
  have hs := (Complex.continuous_ofReal.tendsto _).comp hn
  exact hs.smul hc

/-- Their actual entire-operator images also converge in native Hilbert norm:
the constructed sequence has the fixed source as its genuine graph limit. -/
theorem sourceApproxEntireUnit_operator_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => entireOperator (sourceApproxEntireUnit q n)) atTop
      (𝓝 (entireOperator (sourceUnitVector q))) := by
  have hv := sourceApproxDomain_tendsto q
  have hc := (entireCovariance.continuous.tendsto (sourceVector q)).comp hv
  have hn := hc.norm.inv₀ (sourceCovariance_norm_pos q).ne'
  have hs := (Complex.continuous_ofReal.tendsto _).comp hn
  have h := hs.smul (hv.sub (hc.const_smul (2:ℂ)))
  simpa only [sourceApproxEntireUnit,sourceApproxEntireDomain,sourceUnitVector,sourceDomainVector,
    entireOperator.map_smul,entireOperator_apply_covariance,Function.comp_apply] using h

/-- The full normalized cutoff-family residual has exactly the fixed source's
strictly positive limiting residual, for every actual Xi copy. -/
theorem sourceApproxEntireUnit_residual_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => ‖entireOperator (sourceApproxEntireUnit q n) -
      xiEntireTarget q • (sourceApproxEntireUnit q n : Space)‖) atTop
      (𝓝 ‖entireOperator (sourceUnitVector q) - xiEntireTarget q • (sourceUnitVector q : Space)‖) :=
  ((sourceApproxEntireUnit_operator_tendsto q).sub
    ((sourceApproxEntireUnit_tendsto q).const_smul (xiEntireTarget q))).norm

/-- Increasing these original modular cutoffs cannot yield approximate
occurrence: their actual unit residual sequence does not tend to zero. -/
theorem sourceApproxEntireUnit_not_approximate (q : XiZeroCopy) :
    ¬ Tendsto (fun n => ‖entireOperator (sourceApproxEntireUnit q n) -
      xiEntireTarget q • (sourceApproxEntireUnit q n : Space)‖) atTop (𝓝 0) := by
  intro h
  exact (sourceUnitVector_residual_pos q).ne' (tendsto_nhds_unique (sourceApproxEntireUnit_residual_tendsto q) h)

end
end RHTower.SelbergScatteringApproximateSourceResidual
