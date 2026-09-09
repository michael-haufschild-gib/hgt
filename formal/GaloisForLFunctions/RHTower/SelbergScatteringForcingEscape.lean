import GaloisForLFunctions.RHTower.SelbergScatteringSpectralConcentration

/-!
# Unit native forcings whose complete resolvent responses disappear

The original cusp packets supply one unit native-domain family with increasing
frequency and covariance norm at most 2/(n+1). Exact resolvent factorization
through that covariance proves disappearance of the full response at every Xi
copy. Both the entire residual numerator at every complex target and its
positive normalization denominator tend to zero. The normalized domain
responses retain residual at least one at the target i. Thus unscaled forcing
smallness cannot substitute for normalized spectral occurrence. The positive
survivor includes the actual unit family, covariance bound, factorization,
full response limits, and exact normalized residual quotient.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergScatteringForcingEscape
open D4BMModularCore SelbergScatteringEntireOperator SelbergScatteringEntireCusp
open SelbergScatteringEntireEigenvectors SelbergScatteringForcingTransport
open SelbergScatteringNativeResidual SelbergScatteringEntireXiPackets
noncomputable section

private theorem exists_highEnergyIndex (n : ℕ) :
    ∃ m : ℕ, ‖nativeCovariance (cuspApproximateVector (n:ℝ) m:Space)-
      (((cuspEnergy (n:ℝ))⁻¹:ℝ):ℂ) • (cuspApproximateVector (n:ℝ) m:Space)‖ <
        ((n:ℝ)+1)⁻¹ :=
  ((nativeCovariance_cusp_residual_tendsto (n:ℝ)).eventually
    (gt_mem_nhds (by positivity : 0 < ((n:ℝ)+1)⁻¹))).exists

private def highEnergyIndex (n : ℕ) : ℕ := Classical.choose (exists_highEnergyIndex n)

/-- Actual unit native-domain cusp vectors whose frequencies increase before
any Xi source is selected. Cutoffs are chosen from proved analytic limits. -/
def highEnergyForcing (n : ℕ) : energyOperator.domain :=
  cuspApproximateVector (n:ℝ) (highEnergyIndex n)

theorem highEnergyForcing_norm (n : ℕ) : ‖(highEnergyForcing n:Space)‖=1 :=
  cuspApproximateVector_norm _ _

/-- A quantitative bound for the complete native covariance response. -/
theorem highEnergyForcing_covariance_norm_le (n : ℕ) :
    ‖nativeCovariance (highEnergyForcing n:Space)‖ ≤ 2*((n:ℝ)+1)⁻¹ := by
  have he := Classical.choose_spec (exists_highEnergyIndex n)
  change ‖nativeCovariance (highEnergyForcing n:Space)-
    (((cuspEnergy (n:ℝ))⁻¹:ℝ):ℂ) • (highEnergyForcing n:Space)‖ < ((n:ℝ)+1)⁻¹ at he
  have ha : (n:ℝ)+1 ≤ cuspEnergy (n:ℝ) := by
    unfold cuspEnergy
    nlinarith [sq_nonneg ((n:ℝ)-1/2)]
  have hb : (cuspEnergy (n:ℝ))⁻¹ ≤ ((n:ℝ)+1)⁻¹ := inv_anti₀ (by positivity) ha
  have hs : ‖(((cuspEnergy (n:ℝ))⁻¹:ℝ):ℂ) • (highEnergyForcing n:Space)‖ =
      (cuspEnergy (n:ℝ))⁻¹ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (cuspEnergy_pos _)),highEnergyForcing_norm,mul_one]
  have hn := norm_le_norm_sub_add (nativeCovariance (highEnergyForcing n:Space))
    ((((cuspEnergy (n:ℝ))⁻¹:ℝ):ℂ) • (highEnergyForcing n:Space))
  rw [hs] at hn
  linarith

/-- The same unconditional unit family has native covariance norm tending to zero. -/
theorem highEnergyForcing_covariance_tendsto :
    Tendsto (fun n => ‖nativeCovariance (highEnergyForcing n:Space)‖) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  exact squeeze_zero (fun _ => norm_nonneg _) highEnergyForcing_covariance_norm_le
    (by simpa using hi.const_mul 2)

/-- Exact native resolvent factorization through the original covariance. -/
theorem sourceResolvent_covariance_factor (q : XiZeroCopy) (f : Space) :
    sourceResolvent q f = nativeCovariance f+
      scatteringEnergy (q.1:ℂ) • sourceResolvent q (nativeCovariance f) := by
  have h := congrArg nativeCovariance (sourceResolvent_equation q f)
  have hi : nativeCovariance (energyOperator
      ⟨sourceResolvent q f,sourceResolvent_mem_domain q f⟩)=sourceResolvent q f :=
    closedDenseInverse_C_apply nativeCovariance nativeCovariance_injective _
  rw [map_sub,map_smul,hi,← sourceResolvent_nativeCovariance_commute] at h
  linear_combination (norm := module) h

/-- Covariance disappearance forces native resolvent disappearance, without
assuming boundedness or convergence of the original forcing family. -/
theorem sourceResolvent_tendsto_of_covariance {ι : Type*} {l : Filter ι}
    (q : XiZeroCopy) (f : ι → Space)
    (ht : Tendsto (fun i => ‖nativeCovariance (f i)‖) l (𝓝 0)) :
    Tendsto (fun i => ‖sourceResolvent q (f i)‖) l (𝓝 0) := by
  let D : Space →L[ℂ] Space := 1+scatteringEnergy (q.1:ℂ) • sourceResolvent q
  have he (i : ι) : sourceResolvent q (f i)=D (nativeCovariance (f i)) :=
    sourceResolvent_covariance_factor q (f i)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    (by simpa using ht.const_mul ‖D‖)
  rw [he]
  exact D.le_opNorm _

/-- Every original Xi resolvent loses the complete response of this unit forcing family. -/
theorem highEnergyForcing_resolvent_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => ‖sourceResolvent q (highEnergyForcing n:Space)‖) atTop (𝓝 0) :=
  sourceResolvent_tendsto_of_covariance q _ highEnergyForcing_covariance_tendsto

/-- The complete response-normalization denominator also tends to zero. -/
theorem highEnergyForcing_response_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => ‖entireCovariance (sourceResolvent q (highEnergyForcing n:Space))‖)
      atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (fun _ => entireCovariance.le_opNorm _)
    (by simpa using (highEnergyForcing_resolvent_tendsto q).const_mul ‖entireCovariance‖)

/-- Unscaled entire residuals tend to zero at every complex target on the same
unit forcing family. This includes targets excluded by self-adjointness. -/
theorem highEnergyForcing_numerator_tendsto (q : XiZeroCopy) (mu : ℂ) :
    Tendsto (fun n => ‖sourceResolvent q (highEnergyForcing n:Space)-
      (2+mu) • entireCovariance (sourceResolvent q (highEnergyForcing n:Space))‖)
      atTop (𝓝 0) := by
  have hh := (highEnergyForcing_resolvent_tendsto q).add
    ((highEnergyForcing_response_tendsto q).const_mul ‖2+mu‖)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hh)
  simpa only [norm_smul] using norm_sub_le
    (sourceResolvent q (highEnergyForcing n:Space))
    ((2+mu) • entireCovariance (sourceResolvent q (highEnergyForcing n:Space)))

/-- In particular the full Xi forcing numerator vanishes along this actual
unit family, for every Xi copy, without locating any zero. -/
theorem highEnergyForcing_transport_tendsto (q : XiZeroCopy) :
    Tendsto (fun n => ‖entireForcingTransport q (highEnergyForcing n:Space)‖)
      atTop (𝓝 0) := highEnergyForcing_numerator_tendsto q (xiEntireTarget q)

theorem highEnergyForcing_response_pos (q : XiZeroCopy) (n : ℕ) :
    0 < ‖entireCovariance (sourceResolvent q (highEnergyForcing n:Space))‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hr : sourceResolvent q (highEnergyForcing n:Space)=0 :=
    entireCovariance_injective (by simpa only [map_zero] using h)
  have hinj : Function.Injective (sourceResolvent q) :=
    resolventCLM_injective energyOperator_selfAdjoint (scatteringEnergy_nonreal q)
  have hf : (highEnergyForcing n:Space)=0 := hinj (by simpa only [map_zero] using hr)
  have hn := highEnergyForcing_norm n
  rw [hf,norm_zero] at hn
  exact zero_ne_one hn

/-- The actual entire-domain response to the unit forcing family. -/
def highEnergyEntireDomain (q : XiZeroCopy) (n : ℕ) : entireOperator.domain :=
  ⟨entireCovariance (sourceResolvent q (highEnergyForcing n:Space)),entireCovariance_mem_domain _⟩

/-- The corresponding actual unit response; its denominator is proved positive. -/
def highEnergyEntireUnit (q : XiZeroCopy) (n : ℕ) : entireOperator.domain :=
  ((‖entireCovariance (sourceResolvent q (highEnergyForcing n:Space))‖⁻¹:ℝ):ℂ) • highEnergyEntireDomain q n

theorem highEnergyEntireUnit_norm (q : XiZeroCopy) (n : ℕ) :
    ‖(highEnergyEntireUnit q n:Space)‖=1 := by
  rw [highEnergyEntireUnit,Submodule.coe_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (highEnergyForcing_response_pos q n))]
  exact inv_mul_cancel₀ (highEnergyForcing_response_pos q n).ne'

/-- Normalized residuals retain the full quotient of disappearing numerator and
denominator; the numerator's limit alone cannot replace this expression. -/
theorem highEnergyEntireUnit_residual_norm (q : XiZeroCopy) (n : ℕ) (mu : ℂ) :
    ‖entireOperator (highEnergyEntireUnit q n)-mu • (highEnergyEntireUnit q n:Space)‖ =
      ‖entireCovariance (sourceResolvent q (highEnergyForcing n:Space))‖⁻¹*
        ‖sourceResolvent q (highEnergyForcing n:Space)-
          (2+mu) • entireCovariance (sourceResolvent q (highEnergyForcing n:Space))‖ := by
  rw [highEnergyEntireUnit,entireOperator.map_smul,Submodule.coe_smul,smul_comm mu,
    ← smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (highEnergyForcing_response_pos q n))]
  congr 2
  rw [highEnergyEntireDomain,entireOperator_apply_covariance]
  change sourceResolvent q (highEnergyForcing n:Space)-
    (2:ℂ) • entireCovariance (sourceResolvent q (highEnergyForcing n:Space))-
    mu • entireCovariance (sourceResolvent q (highEnergyForcing n:Space))= _
  rw [add_smul]
  module

/-- A concrete nonreal target retains a unit lower residual despite its
unnormalized numerator tending to zero on the same actual forcing family. -/
theorem highEnergyEntireUnit_nonreal_residual_lower (q : XiZeroCopy) (n : ℕ) :
    1 ≤ ‖entireOperator (highEnergyEntireUnit q n)-Complex.I • (highEnergyEntireUnit q n:Space)‖ := by
  simpa only [Complex.I_im,abs_one,highEnergyEntireUnit_norm,mul_one] using
    norm_sub_smul_lower_bound entireOperator_selfAdjoint Complex.I (highEnergyEntireUnit q n)

end
end RHTower.SelbergScatteringForcingEscape
