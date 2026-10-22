import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSquarefreeFirstTraceExponentialContinuation
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesSubcriticalPassiveResponse

/-!
# Hedenmalm--Stokes first-trace moment duality wall

The Gamma-sewn Stokes response is unconditionally passive in the open physical strip, but its
thermodynamic limit controls the inverse-gap moment `b/g`.  The valuation-one first-trace current
is the opposite positive moment `b*g`.

This module proves the separation coefficient-exactly.  On every prime-power label, `b*g` is the
literal von Mangoldt coefficient.  It is also the high-frequency coefficient

`z * (R(z) - b) -> b*g`,

where `R(z)=b*z/(z-g)` is the one-subtracted passive atom.  For every `0 < s <= 1`, the positive
moment is nonsummable already on the valuation-zero prime slice, whereas for `0 < s < 1` the
inverse moment is summable.  Thus ordinary passive limiting cannot produce the continued
valuation-one current isolated by the squarefree first-trace continuation.

No Xi zero, RH premise, numerical computation, or added axiom enters.
-/

open Complex Filter Function Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive Stokes moment seen by the valuation-one current at infinity. -/
def gammaSewnMobiusApertureStokesFirstTracePositiveMoment
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
    gammaSewnMobiusApertureStokesGap s pk

/-- Passive thermodynamic limit instead sees the opposite, inverse-gap moment. -/
def gammaSewnMobiusApertureStokesPassiveInverseMoment
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
    gammaSewnMobiusApertureStokesGap s pk

theorem gammaSewnMobiusApertureStokesFirstTracePositiveMoment_pos
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesFirstTracePositiveMoment s pk := by
  apply mul_pos
  · rw [gammaSewnMobiusApertureStokesDualFeatureCoefficient]
    exact div_pos
      (gammaSewnMobiusContinuousApertureFeature_pos hs pk.1 pk.2) (by positivity)
  · exact gammaSewnMobiusApertureStokesGap_pos hs pk

/-- The positive Stokes moment is exactly one valuation-labelled first-trace coefficient. -/
theorem ofReal_gammaSewnMobiusApertureStokesFirstTracePositiveMoment_eq_flux
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    (gammaSewnMobiusApertureStokesFirstTracePositiveMoment s pk : ℂ) =
      primePowerFluxTerm (s : ℂ) pk := by
  exact gammaSewnMobiusApertureStokesDualFeatureCoefficient_mul_gap_eq_flux hs pk

/-- The valuation-zero slice retains its literal prime label and log-prime clock. -/
theorem gammaSewnMobiusApertureStokesFirstTracePositiveMoment_primeSlice_eq
    {s : ℝ} (hs : 0 < s) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesFirstTracePositiveMoment s (p, 0) =
      Real.log (p : ℝ) * xiMobiusContinuousApertureDiskNode s p := by
  rw [gammaSewnMobiusApertureStokesFirstTracePositiveMoment,
    gammaSewnMobiusApertureStokesDualFeatureCoefficient,
    gammaSewnMobiusApertureStokesGap]
  norm_num
  simpa [gammaSewnMobiusContinuousApertureFeature_zero, mul_comm] using
    gammaSewnMobiusApertureStokesInverseTilt_mul_edge hs p 0

/-- Below the first-trace wall the physical prime node dominates the prime harmonic node. -/
theorem one_div_prime_le_xiMobiusContinuousApertureDiskNode
    {s : ℝ} (hs1 : s ≤ 1) (p : Nat.Primes) :
    1 / (p : ℝ) ≤ xiMobiusContinuousApertureDiskNode s p := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  rw [xiMobiusContinuousApertureDiskNode]
  rw [show 1 / (p : ℝ) = Real.exp (-Real.log (p : ℝ)) by
    rw [Real.exp_neg, Real.exp_log hp]
    simp [div_eq_mul_inv]]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Quantitative prime-harmonic lower bound for the coefficient-faithful positive moment. -/
theorem log_two_div_prime_le_firstTracePositiveMoment_primeSlice
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (p : Nat.Primes) :
    Real.log 2 / (p : ℝ) ≤
      gammaSewnMobiusApertureStokesFirstTracePositiveMoment s (p, 0) := by
  rw [gammaSewnMobiusApertureStokesFirstTracePositiveMoment_primeSlice_eq hs]
  have hlogp : Real.log 2 ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast p.2.two_le
  have hnode := one_div_prime_le_xiMobiusContinuousApertureDiskNode hs1 p
  calc
    Real.log 2 / (p : ℝ) = Real.log 2 * (1 / (p : ℝ)) := by ring
    _ ≤ Real.log (p : ℝ) * xiMobiusContinuousApertureDiskNode s p := by gcongr

/-- **Positive-moment wall.**  Literal first-trace mass is nonsummable throughout `0 < s <= 1`.
The valuation-zero prime slice already contains a positive multiple of the prime harmonic series. -/
theorem not_summable_gammaSewnMobiusApertureStokesFirstTracePositiveMoment
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ¬ Summable (gammaSewnMobiusApertureStokesFirstTracePositiveMoment s) := by
  intro hsum
  have hslice : Summable (fun p : Nat.Primes =>
      gammaSewnMobiusApertureStokesFirstTracePositiveMoment s (p, 0)) :=
    hsum.comp_injective (by
      intro p q h
      exact congrArg Prod.fst h)
  have hscaled := hslice.mul_left (Real.log 2)⁻¹
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hscaled
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlower := log_two_div_prime_le_firstTracePositiveMoment_primeSlice hs hs1 p
  calc
    1 / (p : ℝ) = (Real.log 2)⁻¹ * (Real.log 2 / (p : ℝ)) := by
      field_simp [hlog2.ne']
    _ ≤ (Real.log 2)⁻¹ *
        gammaSewnMobiusApertureStokesFirstTracePositiveMoment s (p, 0) := by
      exact mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr hlog2.le)

/-- Equivalent wall stated directly for the complex valuation-one von Mangoldt family. -/
theorem not_summable_primePowerFluxTerm_of_real_le_one
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ¬ Summable (primePowerFluxTerm (s : ℂ)) := by
  intro hsum
  apply not_summable_gammaSewnMobiusApertureStokesFirstTracePositiveMoment hs hs1
  have hnorm : Summable (fun pk : Nat.Primes × ℕ =>
      ‖primePowerFluxTerm (s : ℂ) pk‖) := summable_norm_iff.mpr hsum
  apply hnorm.congr
  intro pk
  rw [← ofReal_gammaSewnMobiusApertureStokesFirstTracePositiveMoment_eq_flux hs]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gammaSewnMobiusApertureStokesFirstTracePositiveMoment_pos hs pk)]

/-- The opposite inverse-gap moment has the unconditional passive landing. -/
theorem summable_gammaSewnMobiusApertureStokesPassiveInverseMoment
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (gammaSewnMobiusApertureStokesPassiveInverseMoment s) := by
  exact summable_gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap hs hs1

/-- Algebraic extraction of the positive moment from one passive atom. -/
theorem gammaSewnMobiusApertureStokes_firstTrace_extraction_identity
    {s : ℝ} {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    z * (gammaSewnMobiusApertureStokesOneSubtractedAtom s z pk -
        (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ)) =
      (gammaSewnMobiusApertureStokesFirstTracePositiveMoment s pk : ℂ) * z /
        (z - (gammaSewnMobiusApertureStokesGap s pk : ℂ)) := by
  have hden : z - (gammaSewnMobiusApertureStokesGap s pk : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [gammaSewnMobiusApertureStokesOneSubtractedAtom]
  rw [gammaSewnMobiusApertureStokesFirstTracePositiveMoment]
  push_cast
  field_simp [hden]
  ring

/-- The literal positive moment is the high-imaginary-frequency coefficient of one passive atom. -/
theorem tendsto_gammaSewnMobiusApertureStokes_firstTrace_extraction
    (s : ℝ) (pk : Nat.Primes × ℕ) :
    Tendsto (fun y : ℝ =>
      (I * (y : ℂ)) *
        (gammaSewnMobiusApertureStokesOneSubtractedAtom s (I * (y : ℂ)) pk -
          (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ)))
      atTop
      (nhds (gammaSewnMobiusApertureStokesFirstTracePositiveMoment s pk : ℂ)) := by
  let g : ℝ := gammaSewnMobiusApertureStokesGap s pk
  let m : ℝ := gammaSewnMobiusApertureStokesFirstTracePositiveMoment s pk
  have hyinvR : Tendsto (fun y : ℝ => y⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hyinvC : Tendsto (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hyinvR
  have hginv : Tendsto (fun y : ℝ =>
      (g : ℂ) * ((y⁻¹ : ℝ) : ℂ)) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hyinvC
  have hden : Tendsto (fun y : ℝ =>
      I - (g : ℂ) * ((y⁻¹ : ℝ) : ℂ)) atTop (nhds I) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hginv
  have hratio : Tendsto (fun y : ℝ =>
      I / (I - (g : ℂ) * ((y⁻¹ : ℝ) : ℂ))) atTop (nhds 1) := by
    have hinv := hden.inv₀ I_ne_zero
    have hmul :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => I) atTop (nhds I)).mul hinv
    convert hmul using 1 <;> simp [div_eq_mul_inv]
  have heq : (fun y : ℝ =>
      (I * (y : ℂ)) *
        (gammaSewnMobiusApertureStokesOneSubtractedAtom s (I * (y : ℂ)) pk -
          (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ))) =ᶠ[atTop]
      (fun y : ℝ => (m : ℂ) *
        (I / (I - (g : ℂ) * ((y⁻¹ : ℝ) : ℂ)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [gammaSewnMobiusApertureStokes_firstTrace_extraction_identity
      (by simp [hy])]
    change (m : ℂ) * (I * (y : ℂ)) /
        (I * (y : ℂ) - (g : ℂ)) =
      (m : ℂ) * (I / (I - (g : ℂ) * ((y⁻¹ : ℝ) : ℂ)))
    have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    have hdenA : I * (y : ℂ) - (g : ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hyinv : ((y⁻¹ : ℝ) : ℂ) = (y : ℂ)⁻¹ := by norm_cast
    rw [show I - (g : ℂ) * ((y⁻¹ : ℝ) : ℂ) =
        (I * (y : ℂ) - (g : ℂ)) / (y : ℂ) by
      rw [hyinv]
      field_simp [hyC]]
    field_simp [hyC, hdenA]
  rw [Filter.tendsto_congr' heq]
  simpa only [mul_one] using tendsto_const_nhds.mul hratio

/-- **Moment duality wall.**  Passive response exists while coefficient-faithful first trace does
not land by ordinary all-prime summation anywhere in the open physical strip. -/
theorem gammaSewnMobiusApertureStokes_moment_duality_wall
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (gammaSewnMobiusApertureStokesPassiveInverseMoment s) ∧
      ¬ Summable (gammaSewnMobiusApertureStokesFirstTracePositiveMoment s) :=
  ⟨summable_gammaSewnMobiusApertureStokesPassiveInverseMoment hs hs1,
    not_summable_gammaSewnMobiusApertureStokesFirstTracePositiveMoment hs hs1.le⟩

end

end RHTower
