import GaloisForLFunctions.RHTower.ChiCubicSelectedRationalConeCancellation

/-!
# Covered-source cancellation for the selected physical rational cone

The complete arithmetic source at prime cutoff 2N cancels against the
literal selected Mellin profile at physical scale N. Uniform local Cauchy
control and actual exterior decay couple the two scales. Exact physical
Mellin inversion then proves that the entire positive rational cone action
at the covered cutoff has complex norm o(N/log²N).

No analytic cancellation or uniformity premise is assumed. The complete
global defect action, including nonzero transverse defects, remains a
separate obligation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ENNReal
namespace RHTower.BAGTrace
private abbrev E := HTGeometry.QuadrantLogSpace
private abbrev Q := {q : E // ∀i, q i∈Icc (1 : ℝ) 2}
private theorem twice_atTop : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
  tendsto_atTop_mono (fun N => by change N≤2*N; omega) tendsto_id

private theorem real_energy_bound (p : ℝ) (f : SchwartzMap E ℂ)
    (B : {r : ℝ // 0<r})
    (hb : (∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^p*‖(𝓕 f) ξ‖^2))≤ENNReal.ofReal B.1) :
    (∫ξ : E,(1+|ξ 0|+|ξ 1|)^p*‖(𝓕 f) ξ‖^2)≤B.1 := by
  have hf := (𝓕 f).continuous.measurable
  have hm : Measurable (fun ξ : E => (1+|ξ 0|+|ξ 1|)^p*‖(𝓕 f) ξ‖^2) := by fun_prop
  have hpos : ∀ᵐξ : E ∂volume,0≤(1+|ξ 0|+|ξ 1|)^p*‖(𝓕 f) ξ‖^2 :=
    Eventually.of_forall (fun ξ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  have hi : Integrable (fun ξ : E => (1+|ξ 0|+|ξ 1|)^p*‖(𝓕 f) ξ‖^2) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hpos).1
      (ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top))
  apply (ENNReal.ofReal_le_ofReal_iff B.2.le).1
  rw [ofReal_integral_eq_lintegral_ofReal hi hpos]
  exact hb

private theorem covered_exterior_bound (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,∀q : Q,
      Integrable (fun ξ : E => bagMellinNormalizedArithmeticSource ρ₁ ρ₂ (2*N) ξ*
        (𝓕 (bagCubicSelectedExteriorMellin q N)) ξ) ∧
      ‖∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ (2*N) ξ*
        (𝓕 (bagCubicSelectedExteriorMellin q N)) ξ‖≤C/(N : ℝ) := by
  obtain ⟨A,hA,hAb⟩ := bagMellinNormalizedArithmeticSource_H2_pairing_bound ρ₁ ρ₂
  obtain ⟨B,hB,hBb⟩ := bagCubicSelectedExteriorMellin_energy_decay 2
  refine ⟨2*A*Real.sqrt B,by positivity,?_⟩
  filter_upwards [twice_atTop.eventually hAb,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hBb,eventually_ge_atTop 1] with N hArow hBrow hN
  intro q
  have hn : (1 : ℝ)≤N := by exact_mod_cast hN
  have hnpos : (0 : ℝ)<N := by linarith
  let G := 𝓕 (bagCubicSelectedExteriorMellin q N)
  have henergy : (∫ξ : E,(1+|ξ 0|+|ξ 1|)^(4 : ℝ)*‖G ξ‖^2)≤B/(N : ℝ)^4 := by
    apply real_energy_bound 4 (bagCubicSelectedExteriorMellin q N) ⟨B/(N : ℝ)^4,by positivity⟩
    simpa only [Nat.reduceMul] using hBrow q
  have hs : Real.sqrt (∫ξ : E,(1+|ξ 0|+|ξ 1|)^(4 : ℝ)*‖G ξ‖^2)≤Real.sqrt B/(N : ℝ)^2 := by
    apply (Real.sqrt_le_sqrt henergy).trans_eq
    rw [Real.sqrt_div hB.le,show (N : ℝ)^4=((N : ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have hlog : Real.sqrt (1+Real.log ((2*N : ℕ) : ℝ))≤2*(N : ℝ) := by
    apply Real.sqrt_le_iff.2
    push_cast
    exact ⟨by positivity,by nlinarith [Real.log_le_sub_one_of_pos (by positivity : 0<2*(N : ℝ))]⟩
  refine ⟨(hArow G).1,((hArow G).2).trans ?_⟩
  calc
    _ ≤ (A*(2*(N : ℝ)))*(Real.sqrt B/(N : ℝ)^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog hA.le) hs
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp

private theorem localized_sub (q : Q) (f g : SchwartzMap E ℂ) :
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q (f-g)=
      GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f-
        GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q g := by
  ext u
  simp only [GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz_apply,
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinProfile,sub_apply,mul_sub]

private def localDifference (q : Q) (N : ℕ) : SchwartzMap E ℂ :=
  GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q (bagCubicSelectedNormalizedCone N)-
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q (bagCubicSelectedNormalizedCone (2*N : ℕ))

private theorem local_difference_pairing_tendsto (ρ₁ ρ₂ : {r : ℝ // 0<r}) (q : ℕ→Q) :
    Tendsto (fun N : ℕ => ∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ (2*N) ξ*
      (𝓕 (localDifference (q N) N)) ξ) atTop (𝓝 0) := by
  obtain ⟨C,hC,hCb⟩ := bagLocalizedMellin_difference_arithmetic_pairing_bound ρ₁ ρ₂
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ : {r : ℝ // 0<r} := ⟨(ε/(2*C))^2,sq_pos_of_pos (div_pos hε (by positivity))⟩
  obtain ⟨R,hR⟩ := bagCubicSelectedNormalizedCone_uniform_local_mellin_cauchy
    ⟨1/4,by norm_num⟩ δ
  filter_upwards [twice_atTop.eventually hCb,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop R] with N hN hNr
  have h2Nr : R≤((2*N : ℕ) : ℝ) :=
    hNr.trans (by exact_mod_cast (show N≤2*N by omega))
  have he := hR ⟨N,hNr⟩ ⟨(2*N : ℕ),h2Nr⟩ (q N)
  rw [localized_sub] at he
  have he' : (∫⁻ξ : E,ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*
      ‖(𝓕 (localDifference (q N) N)) ξ‖^2))≤ENNReal.ofReal δ.1 := by
    simpa only [localDifference,show (2 : ℝ)+2*(1/4 : ℝ)=5/2 by ring] using he
  have hE := real_energy_bound (5/2) (localDifference (q N) N) δ he'
  have hb := (hN (q N) (q N) (bagCubicSelectedNormalizedCone N)
    (bagCubicSelectedNormalizedCone (2*N : ℕ))).2
  rw [dist_zero_right]
  calc
    _ ≤ C*Real.sqrt (∫ξ : E,(1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*
        ‖(𝓕 (localDifference (q N) N)) ξ‖^2) := hb
    _ ≤ C*Real.sqrt δ.1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) hC.le
    _ = ε/2 := by
      dsimp only [δ]
      rw [Real.sqrt_sq (div_nonneg hε.le (by positivity))]
      field_simp [hC.ne']
    _ < ε := by linarith

/-- The covered-band source through2N cancels against the literal moving
Mellin profile at physical scaleN. Every source sector and the complete
physical exterior remain; the two cutoffs are matched explicitly. -/
theorem bagCubicSelectedMellin_covered_pairing_tendsto
    (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    (∀ᶠ N : ℕ in atTop,Integrable (fun ξ : E =>
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ (2*N) ξ*
        (𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter ρ₁ ρ₂ (2*N)) N)) ξ)) ∧
    Tendsto (fun N : ℕ => ∫ξ : E,
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ (2*N) ξ*
        (𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter ρ₁ ρ₂ (2*N)) N)) ξ)
      atTop (𝓝 0) := by
  let q := fun N : ℕ => bagCriticalMellinParameter ρ₁ ρ₂ (2*N)
  have hnative := (bagCubicSelectedMellin_arithmetic_pairing_tendsto ρ₁ ρ₂).2.comp twice_atTop
  have hdiff := local_difference_pairing_tendsto ρ₁ ρ₂ q
  obtain ⟨C,_hC,hExt⟩ := covered_exterior_bound ρ₁ ρ₂
  have hext : Tendsto (fun N : ℕ => ∫ξ : E,
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ (2*N) ξ*
        (𝓕 (bagCubicSelectedExteriorMellin (q N) N)) ξ) atTop (𝓝 0) :=
    squeeze_zero_norm' (hExt.mono (fun N hN => (hN (q N)).2))
      (tendsto_const_div_atTop_nhds_zero_nat C)
  have hextNative := (bagCubicSelectedExteriorMellin_arithmetic_pairing_tendsto ρ₁ ρ₂
    (bagCriticalMellinParameter ρ₁ ρ₂)).comp twice_atTop
  obtain ⟨_A,_hA,hAdmit⟩ := bagMellinNormalizedArithmeticSource_H2_pairing_bound ρ₁ ρ₂
  have hsplit (N : ℕ) :
      bagCubicSelectedMellin (q N) N=
      bagCubicSelectedMellin (q N) (2*N : ℕ)+localDifference (q N) N+
        bagCubicSelectedExteriorMellin (q N) N-bagCubicSelectedExteriorMellin (q N) (2*N : ℕ) := by
    rw [bagCubicSelectedMellin_decomposition,bagCubicSelectedMellin_decomposition]
    dsimp only [localDifference]
    abel
  constructor
  · filter_upwards [twice_atTop.eventually hAdmit] with N hN
    exact (hN (𝓕 (bagCubicSelectedMellin (q N) N))).1
  · have hh := ((hnative.add hdiff).add hext).sub hextNative
    simp only [add_zero,sub_self] at hh
    apply hh.congr'
    filter_upwards [twice_atTop.eventually hAdmit] with N hN
    have hF (f : SchwartzMap E ℂ) : Integrable (fun ξ : E =>
        bagMellinNormalizedArithmeticSource ρ₁ ρ₂ (2*N) ξ*(𝓕 f) ξ) := (hN (𝓕 f)).1
    symm
    rw [hsplit N]
    have hsub (f g : SchwartzMap E ℂ) : 𝓕 (f-g)=𝓕 f-𝓕 g :=
      map_sub (FourierTransform.fourierEquiv ℂ (SchwartzMap E ℂ)) f g
    simp only [hsub,FourierTransform.fourier_add,add_apply,sub_apply,mul_add,mul_sub]
    have hA := hF (bagCubicSelectedMellin (q N) (2*N : ℕ))
    have hB := hF (localDifference (q N) N)
    have hC := hF (bagCubicSelectedExteriorMellin (q N) N)
    have hD := hF (bagCubicSelectedExteriorMellin (q N) (2*N : ℕ))
    have hs := integral_sub ((hA.add hB).add hC) hD
    simp only [Pi.add_apply] at hs
    have hABC := integral_add (hA.add hB) hC
    have hAB := integral_add hA hB
    simp only [Pi.add_apply] at hABC hAB
    erw [hABC,hAB] at hs
    simpa only [Pi.add_apply,Function.comp_apply] using! hs

private abbrev CoveredPair (N : ℕ) :=
  DenominatorRational (Sieve.primeSubtypeLE (2*N)) × DenominatorRational (Sieve.primeSubtypeLE (2*N))
private def oneParameter : {r : ℝ // 0<r} := ⟨1,zero_lt_one⟩
private def coveredLine (N : {n : ℕ // 1≤n}) :=
  bagGrowingMellinLines (fun _ => oneParameter) ⟨2*N.1,by omega⟩

/-- Entire positive rational cone action with the covered physical-band
prime cutoff2N and the original selected physical amplitude atN. -/
def bagCubicCoveredRationalConeAction (N : ℕ) : ℂ :=
  ∑' w : CoveredPair N, criticalRationalMass (Sieve.primeSubtypeLE (2*N)) w*
    (𝓕 (bagCubicSelectedPhysicalSchwartz N))
      (bagCubicConeNode (criticalRationalPoint (Sieve.primeSubtypeLE (2*N)) w))

private theorem selected_normalization (N : ℕ) :
    bagCubicSelectedNormalizedCone N=
      (((Real.log N)^3/(N : ℝ) : ℝ) : ℂ) •
        bagCubicConeSchwartz (bagCubicSelectedPhysicalSchwartz N) := by
  by_cases h : 1<(N : ℝ) ∧ (N : ℝ)^(1/4 : ℝ)<(N : ℝ)/2
  · rw [bagCubicSelectedNormalizedCone,dif_pos h,
      bagCubicSelectedPhysicalSchwartz,dif_pos h]
    rfl
  · rw [bagCubicSelectedNormalizedCone,dif_neg h,
      bagCubicSelectedPhysicalSchwartz,dif_neg h]
    simp only [bagCubicConeSchwartz,FourierTransform.fourier_zero,map_zero,smul_zero]

private theorem covered_source_identity (N : {n : ℕ // 1≤n}) (ξ : E) :
    bagMellinNormalizedArithmeticSource oneParameter oneParameter (2*N.1) ξ=
      criticalCompletedConeEuler (Sieve.primeSubtypeLE (2*N.1))
        (HTGeometry.PositiveLine.quadrantMellinLine (coveredLine N 0) (ξ 0))
        (HTGeometry.PositiveLine.quadrantMellinLine (coveredLine N 1) (ξ 1))/
          (Real.log (2*N.1 : ℕ) : ℂ) := by
  simp only [bagMellinNormalizedArithmeticSource,coveredLine,bagGrowingMellinLines,
    HTGeometry.PositiveLine.quadrantMellinLine,Complex.ofReal_add,Complex.ofReal_one]

private theorem covered_profile_identity :
    ∀ᶠ N : ℕ in atTop,∀hN : 1≤N,
      𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter oneParameter oneParameter (2*N)) N)=
        (((Real.log N)^3/(N : ℝ) : ℝ) : ℂ) •
          bagCubicConeLineProfile (coveredLine ⟨N,hN⟩) (bagCubicSelectedPhysicalSchwartz N) := by
  filter_upwards [twice_atTop.eventually
    (bagCriticalMellinParameter_eventually_eq oneParameter oneParameter)] with N hq hN
  have hqi (i : Fin 2) :
      (bagCriticalMellinParameter oneParameter oneParameter (2*N)).1 i=
        (coveredLine ⟨N,hN⟩ i : ℝ) := by
    rw [hq]
    fin_cases i <;> rfl
  have he : bagCubicSelectedMellin (bagCriticalMellinParameter oneParameter oneParameter (2*N)) N=
      (((Real.log N)^3/(N : ℝ) : ℝ) : ℂ) •
        HTGeometry.PositiveLine.quadrantLogSchwartz (bagConePositiveLines (coveredLine ⟨N,hN⟩))
          (bagCubicConeSchwartz (bagCubicSelectedPhysicalSchwartz N)) := by
    ext u
    change Real.exp (-((bagCriticalMellinParameter oneParameter oneParameter (2*N)).1 0)*u 0-
      ((bagCriticalMellinParameter oneParameter oneParameter (2*N)).1 1)*u 1) •
        bagCubicSelectedNormalizedCone N (HTGeometry.quadrantLogNode u)=_
    rw [selected_normalization,hqi 0,hqi 1]
    simp only [HTGeometry.PositiveLine.quadrantLogSchwartz_apply,smul_apply,
      bagConePositiveLines,Complex.real_smul,smul_eq_mul]
    ring
  rw [he,FourierTransform.fourier_smul]
  rfl

private theorem covered_action_hasSum (N : {n : ℕ // 1≤n}) :
    HasSum (fun w : CoveredPair N.1 => criticalRationalMass (Sieve.primeSubtypeLE (2*N.1)) w*
      (𝓕 (bagCubicSelectedPhysicalSchwartz N.1))
        (bagCubicConeNode (criticalRationalPoint (Sieve.primeSubtypeLE (2*N.1)) w)))
      (∫ξ : E,criticalCompletedConeEuler (Sieve.primeSubtypeLE (2*N.1))
        (HTGeometry.PositiveLine.quadrantMellinLine (coveredLine N 0) (ξ 0))
        (HTGeometry.PositiveLine.quadrantMellinLine (coveredLine N 1) (ξ 1))*
          bagCubicConeLineProfile (coveredLine N) (bagCubicSelectedPhysicalSchwartz N.1) ξ) :=
  criticalRationalCone_physical_line_hasSum (coveredLine N)
    (Sieve.primeSubtypeLE (2*N.1)) (bagCubicSelectedPhysicalSchwartz N.1)

/-- Admission of the complete positive rational cone at the covered cutoff. -/
theorem bagCubicCoveredRationalConeAction_summable :
    ∀ᶠ N : ℕ in atTop,Summable (fun w : CoveredPair N =>
      criticalRationalMass (Sieve.primeSubtypeLE (2*N)) w*
        (𝓕 (bagCubicSelectedPhysicalSchwartz N))
          (bagCubicConeNode (criticalRationalPoint (Sieve.primeSubtypeLE (2*N)) w))) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (covered_action_hasSum ⟨N,hN⟩).summable

private theorem covered_pairing_identity :
    ∀ᶠ N : ℕ in atTop,
      (∫ξ : E,bagMellinNormalizedArithmeticSource oneParameter oneParameter (2*N) ξ*
        (𝓕 (bagCubicSelectedMellin (bagCriticalMellinParameter oneParameter oneParameter (2*N)) N)) ξ)=
        (((Real.log N)^3/((N : ℝ)*Real.log (2*N : ℕ)) : ℝ) : ℂ)*bagCubicCoveredRationalConeAction N := by
  filter_upwards [covered_profile_identity,eventually_ge_atTop 1] with N hprof hN
  rw [hprof hN]
  calc
    _ = ∫ξ : E,(((Real.log N)^3/((N : ℝ)*Real.log (2*N : ℕ)) : ℝ) : ℂ)*
        (criticalCompletedConeEuler (Sieve.primeSubtypeLE (2*N))
          (HTGeometry.PositiveLine.quadrantMellinLine (coveredLine ⟨N,hN⟩ 0) (ξ 0))
          (HTGeometry.PositiveLine.quadrantMellinLine (coveredLine ⟨N,hN⟩ 1) (ξ 1))*
            bagCubicConeLineProfile (coveredLine ⟨N,hN⟩) (bagCubicSelectedPhysicalSchwartz N) ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [covered_source_identity ⟨N,hN⟩]
      simp only [smul_apply,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [integral_const_mul,←(covered_action_hasSum ⟨N,hN⟩).tsum_eq]
      rfl

private theorem log_ratio_tendsto :
    Tendsto (fun N : ℕ => Real.log (2*N : ℕ)/Real.log N) atTop (𝓝 (1 : ℝ)) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_drift_zero (Real.log 2))
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL : Real.log (N : ℝ)≠0 :=
    (Real.log_pos (by exact_mod_cast (show 1<N by omega))).ne'
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2 : ℝ)≠0) hn.ne',add_div,div_self hL]
  ring

/-- The covered-band complete positive rational cone action has complex
norm o(N/log²N), with prime cutoff2N and physical scaleN both literal. -/
theorem bagCubicCoveredRationalConeAction_norm_tendsto :
    Tendsto (fun N : ℕ => (Real.log N)^2/(N : ℝ)*
      ‖bagCubicCoveredRationalConeAction N‖) atTop (𝓝 (0 : ℝ)) := by
  have ht := (bagCubicSelectedMellin_covered_pairing_tendsto oneParameter oneParameter).2.norm
  simp only [norm_zero] at ht
  have hh := log_ratio_tendsto.mul ht
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [covered_pairing_identity,eventually_ge_atTop 2] with N hpair hN
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hL2 : 0<Real.log ((2*N : ℕ) : ℝ) := Real.log_pos
    (by exact_mod_cast (show 1<2*N by omega))
  rw [hpair,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  field_simp [hL.ne',hL2.ne']

end RHTower.BAGTrace
