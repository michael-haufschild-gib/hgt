import GaloisForLFunctions.RHTower.ChiCubicMovingMellinCancellation
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMovingMellin

/-!
# Signed cancellation of the literal selected positive rational cone action

The actual original physical amplitude uses the controlled cutoff of width
N^(1/4). The complete rational cone at prime cutoff N has an admitted sum,
and its complex norm is o(N/log²N). Exact moving-line Mellin inversion,
scalar linearity and the actual L³/N physical normalization transfer the
proved moving-profile cancellation without an analytic premise.

This is the entire positive exact-cone action. The full sharp cubic uses
all transverse lattice defects and its covered physical-band source cutoff;
those source and geometric identifications remain separate obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology
namespace RHTower.BAGTrace
private abbrev E := HTGeometry.QuadrantLogSpace
private abbrev RationalPair (N : ℕ) :=
  DenominatorRational (Sieve.primeSubtypeLE N) × DenominatorRational (Sieve.primeSubtypeLE N)
private def oneParameter : {r : ℝ // 0<r} := ⟨1,zero_lt_one⟩
private def selectedLine (N : {n : ℕ // 2≤n}) :=
  bagGrowingMellinLines (fun _ => oneParameter) N

/-- The original physical Schwartz amplitude at the literal quarter-power
edge width, with zero outside the admissible range. -/
def bagCubicSelectedPhysicalSchwartz (N : ℕ) : SchwartzMap BAGPhysicalSpace ℂ :=
  if h : 1<(N : ℝ) ∧ (N : ℝ)^(1/4 : ℝ)<(N : ℝ)/2 then
    bagCubicControlledPhysicalSchwartz ⟨N,h.1⟩
      ⟨(N : ℝ)^(1/4 : ℝ),Real.rpow_pos_of_pos (zero_lt_one.trans h.1) _,h.2⟩
  else 0

/-- Entire positive rational cone action of the actual selected amplitude.
Both cofactors and all labelled mass sectors remain in the sum. -/
def bagCubicSelectedRationalConeAction (N : ℕ) : ℂ :=
  ∑' w : RationalPair N, criticalRationalMass (Sieve.primeSubtypeLE N) w*
    (𝓕 (bagCubicSelectedPhysicalSchwartz N))
      (bagCubicConeNode (criticalRationalPoint (Sieve.primeSubtypeLE N) w))

private theorem selected_admissible :
    ∀ᶠ N : ℕ in atTop, 1<(N : ℝ) ∧ (N : ℝ)^(1/4 : ℝ)<(N : ℝ)/2 := by
  have hd := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<3/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2,
    hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with N hN hdN
  have hN1 : 1<(N : ℝ) := by exact_mod_cast (show 1<N by omega)
  have hN0 := zero_lt_one.trans hN1
  have he : (N : ℝ)^(1/4 : ℝ)/(N : ℝ)=(N : ℝ)^(-(3/4 : ℝ)) := by
    rw [div_eq_mul_inv,←Real.rpow_neg_one,←Real.rpow_add hN0]
    congr 1
    norm_num
  refine ⟨hN1,?_⟩
  have hh := (div_lt_iff₀ hN0).mp (he.trans_lt hdN)
  linarith

/-- Eventual identification with the literal original physical amplitude. -/
theorem bagCubicSelectedPhysicalSchwartz_eventually_apply :
    ∀ᶠ N : ℕ in atTop, ∀v : BAGPhysicalSpace,
      bagCubicSelectedPhysicalSchwartz N v=
        bagCubicPhysicalAmplitude N
          (bagCubicControlledBandCutoff N ((N : ℝ)^(1/4 : ℝ))) v := by
  filter_upwards [selected_admissible] with N hN v
  rw [bagCubicSelectedPhysicalSchwartz,dif_pos hN]
  rfl

private theorem selected_normalization :
    ∀ᶠ N : ℕ in atTop,
      bagCubicSelectedNormalizedCone N=
        (((Real.log N)^3/(N : ℝ) : ℝ) : ℂ) •
          bagCubicConeSchwartz (bagCubicSelectedPhysicalSchwartz N) := by
  filter_upwards [selected_admissible] with N hN
  rw [bagCubicSelectedNormalizedCone,dif_pos hN,
    bagCubicSelectedPhysicalSchwartz,dif_pos hN]
  rfl

private theorem selected_source_identity (N : {n : ℕ // 2≤n}) (ξ : E) :
    bagMellinNormalizedArithmeticSource oneParameter oneParameter N.1 ξ=
      criticalCompletedConeEuler (Sieve.primeSubtypeLE N.1)
        (HTGeometry.PositiveLine.quadrantMellinLine (selectedLine N 0) (ξ 0))
        (HTGeometry.PositiveLine.quadrantMellinLine (selectedLine N 1) (ξ 1))/
          (Real.log N.1 : ℂ) := by
  simp only [bagMellinNormalizedArithmeticSource,selectedLine,bagGrowingMellinLines,
    HTGeometry.PositiveLine.quadrantMellinLine,Complex.ofReal_add,Complex.ofReal_one]

private theorem selected_profile_identity :
    ∀ᶠ N : ℕ in atTop,∀hN : 2≤N,
      𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter oneParameter oneParameter N) N)=
        (((Real.log N)^3/(N : ℝ) : ℝ) : ℂ) •
          bagCubicConeLineProfile (selectedLine ⟨N,hN⟩) (bagCubicSelectedPhysicalSchwartz N) := by
  filter_upwards [selected_normalization,
    bagCriticalMellinParameter_eventually_eq oneParameter oneParameter] with N hNorm hq hN
  have hqi (i : Fin 2) :
      (bagCriticalMellinParameter oneParameter oneParameter N).1 i=
        (selectedLine ⟨N,hN⟩ i : ℝ) := by
    rw [hq]
    fin_cases i <;> rfl
  have he : bagCubicSelectedMellin (bagCriticalMellinParameter oneParameter oneParameter N) N=
      (((Real.log N)^3/(N : ℝ) : ℝ) : ℂ) •
        HTGeometry.PositiveLine.quadrantLogSchwartz (bagConePositiveLines (selectedLine ⟨N,hN⟩))
          (bagCubicConeSchwartz (bagCubicSelectedPhysicalSchwartz N)) := by
    ext u
    change Real.exp (-((bagCriticalMellinParameter oneParameter oneParameter N).1 0)*u 0-
      ((bagCriticalMellinParameter oneParameter oneParameter N).1 1)*u 1) •
        bagCubicSelectedNormalizedCone N (HTGeometry.quadrantLogNode u)=_
    rw [hNorm,hqi 0,hqi 1]
    simp only [HTGeometry.PositiveLine.quadrantLogSchwartz_apply,smul_apply,
      bagConePositiveLines,Complex.real_smul,smul_eq_mul]
    ring
  rw [he,FourierTransform.fourier_smul]
  rfl

private theorem selected_action_hasSum (N : {n : ℕ // 2≤n}) :
    HasSum (fun w : RationalPair N.1 => criticalRationalMass (Sieve.primeSubtypeLE N.1) w*
      (𝓕 (bagCubicSelectedPhysicalSchwartz N.1))
        (bagCubicConeNode (criticalRationalPoint (Sieve.primeSubtypeLE N.1) w)))
      (∫ξ : E,criticalCompletedConeEuler (Sieve.primeSubtypeLE N.1)
        (HTGeometry.PositiveLine.quadrantMellinLine (selectedLine N 0) (ξ 0))
        (HTGeometry.PositiveLine.quadrantMellinLine (selectedLine N 1) (ξ 1))*
          bagCubicConeLineProfile (selectedLine N) (bagCubicSelectedPhysicalSchwartz N.1) ξ) :=
  criticalRationalCone_physical_line_hasSum (selectedLine N)
    (Sieve.primeSubtypeLE N.1) (bagCubicSelectedPhysicalSchwartz N.1)

/-- Absolute admission of the entire selected rational cone action. -/
theorem bagCubicSelectedRationalConeAction_summable :
    ∀ᶠ N : ℕ in atTop,Summable (fun w : RationalPair N =>
      criticalRationalMass (Sieve.primeSubtypeLE N) w*
        (𝓕 (bagCubicSelectedPhysicalSchwartz N))
          (bagCubicConeNode (criticalRationalPoint (Sieve.primeSubtypeLE N) w))) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (selected_action_hasSum ⟨N,hN⟩).summable

private theorem selected_pairing_identity :
    ∀ᶠ N : ℕ in atTop,
      (∫ξ : E,bagMellinNormalizedArithmeticSource oneParameter oneParameter N ξ*
        (𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter oneParameter oneParameter N) N)) ξ)=
        (((Real.log N)^2/(N : ℝ) : ℝ) : ℂ)*bagCubicSelectedRationalConeAction N := by
  filter_upwards [selected_profile_identity,eventually_ge_atTop 2] with N hprof hN
  have hL : (Real.log N : ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1<N by omega))).ne'
  rw [hprof hN]
  calc
    _ = ∫ξ : E,(((Real.log N)^2/(N : ℝ) : ℝ) : ℂ)*
        (criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
          (HTGeometry.PositiveLine.quadrantMellinLine (selectedLine ⟨N,hN⟩ 0) (ξ 0))
          (HTGeometry.PositiveLine.quadrantMellinLine (selectedLine ⟨N,hN⟩ 1) (ξ 1))*
            bagCubicConeLineProfile (selectedLine ⟨N,hN⟩) (bagCubicSelectedPhysicalSchwartz N) ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [selected_source_identity ⟨N,hN⟩]
      simp only [smul_apply,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_pow]
      field_simp [hL]
    _ = _ := by
      rw [integral_const_mul,←(selected_action_hasSum ⟨N,hN⟩).tsum_eq]
      rfl

/-- The literal selected full positive rational cone action is o(N/log²N)
in complex norm. This includes every growing cofactor and labelled sector. -/
theorem bagCubicSelectedRationalConeAction_norm_tendsto :
    Tendsto (fun N : ℕ => (Real.log N)^2/(N : ℝ)*
      ‖bagCubicSelectedRationalConeAction N‖) atTop (𝓝 (0 : ℝ)) := by
  have ht := (bagCubicSelectedMellin_arithmetic_pairing_tendsto oneParameter oneParameter).2.norm
  simp only [norm_zero] at ht
  apply ht.congr'
  filter_upwards [selected_pairing_identity] with N hN
  rw [hN,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg N))]

end RHTower.BAGTrace
