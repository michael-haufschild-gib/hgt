import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffPhaseLimit

/-!
# The cutoff approximation has a maximal operator-norm gap

At every nonzero time, every cutoff width leaves an exact norm gap of two
from the raw singular unitary. Arbitrarily small nonzero spectral points
realize an odd half-turn of the raw phase inside the frozen interval.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem exists_small_phase_half_turn (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε) :
    ∃ z : ℝ, z ≠ 0 ∧ |z| < ε ∧ phase t z = -1 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (|t|/(2*Real.pi*ε))
  let k : ℝ := 2*(n:ℝ)+1
  have hk : 0 < k := by dsimp [k]; positivity
  have hp : 0 < 2*Real.pi*ε := by positivity
  have hd : 0 < 2*Real.pi*k := by positivity
  let z := t/(2*Real.pi*k)
  have hz : z ≠ 0 := div_ne_zero ht hd.ne'
  have hs : |z| < ε := by
    dsimp [z]
    rw [abs_div,abs_of_pos hd]
    apply (div_lt_iff₀ hd).2
    calc
      |t| < (2*Real.pi*ε)*(n:ℝ) := by
        have h := (div_lt_iff₀ hp).mp hn
        nlinarith
      _ ≤ (2*Real.pi*ε)*k := mul_le_mul_of_nonneg_left (by
        dsimp [k]
        have h0 : 0 ≤ (n:ℝ) := by positivity
        linarith) hp.le
      _ = _ := by ring
  refine ⟨z,hz,hs,?_⟩
  have he : t/(2*z) = Real.pi*k := by
    dsimp [z]
    field_simp
  rw [phase,he]
  have hc : -((Real.pi*k : ℝ) : ℂ)*Complex.I =
      ((2*n+1 : ℕ) : ℂ) * (-((Real.pi:ℂ)*Complex.I)) := by
    dsimp [k]
    push_cast
    ring
  rw [show -(((Real.pi*k : ℝ) : ℂ)*Complex.I) =
      ((2*n+1 : ℕ) : ℂ) * (-((Real.pi:ℂ)*Complex.I)) by simpa only [neg_mul] using hc,
    Complex.exp_nat_mul,Complex.exp_neg,Complex.exp_pi_mul_I]
  norm_num [pow_add,pow_mul]

private theorem local_symbol_le_linfty (g : Lp ℂ ∞ (volume : Measure ℝ))
    (φ : ℝ → ℂ) (z : ℝ) (hg : (g : ℝ → ℂ) =ᵐ[volume] φ)
    (hc : ContinuousAt φ z) : ‖φ z‖ ≤ ‖g‖ := by
  have hbound : ∀ᵐ y ∂volume, ‖φ y‖ ≤ ‖g‖ := by
    have h := ae_le_lpNorm_exponent_top (Lp.memLp g)
    rw [← toReal_eLpNorm (Lp.memLp g).1,← Lp.norm_def] at h
    filter_upwards [h,hg] with y hy he
    rwa [he] at hy
  by_contra hn
  have hnhood : {y : ℝ | ‖g‖ < ‖φ y‖} ∈ 𝓝 z :=
    hc.norm.eventually (isOpen_Ioi.mem_nhds (lt_of_not_ge hn))
  have hp := Measure.measure_pos_of_mem_nhds volume hnhood
  have hz : volume {y : ℝ | ‖g‖ < ‖φ y‖} = 0 := by
    have h := hbound.mono fun y hy => not_lt.mpr hy
    simpa only [ae_iff,not_not] using h
  exact hp.ne' hz

private theorem cutoffPhase_eq_one_inside (a t z : ℝ) (hz : |z| < Real.exp a) :
    cutoffPhase a t z = 1 := by
  have hm : z ∉ cutoffPhaseSet a := not_le.mpr hz
  simp [cutoffPhase,cutoffPhaseFrequency,indicator_of_notMem hm]

private theorem cutoffPhase_continuous_inside (a t z : ℝ) (hz : |z| < Real.exp a) :
    ContinuousAt (cutoffPhase a t) z := by
  have he : cutoffPhase a t =ᶠ[𝓝 z] (fun _ => (1:ℂ)) := by
    filter_upwards [continuous_abs.continuousAt.eventually (isOpen_Iio.mem_nhds hz)] with y hy
    exact cutoffPhase_eq_one_inside a t y hy
  exact he.continuousAt

/-- At every nonzero time the cutoff phase stays exactly two away from the raw phase in L-infinity. -/
theorem norm_cutoffPhaseLinfty_sub_raw (a t : ℝ) :
    ‖cutoffPhaseLinfty a t - phaseLinfty t‖ = if t = 0 then 0 else 2 := by
  have hae : (cutoffPhaseLinfty a t - phaseLinfty t : Lp ℂ ∞ (volume : Measure ℝ)) =ᵐ[volume]
      fun z => cutoffPhase a t z - phase t z := by
    filter_upwards [Lp.coeFn_sub (cutoffPhaseLinfty a t) (phaseLinfty t),
      cutoffPhaseLinfty_ae a t,phaseLinfty_ae t] with z h0 h1 h2
    simpa only [Pi.sub_apply,h1,h2] using h0
  by_cases ht : t = 0
  · subst t
    rw [if_pos rfl]
    apply norm_eq_zero.mpr
    apply Lp.ext
    filter_upwards [hae,Lp.coeFn_zero ℂ ∞ (volume : Measure ℝ)] with z h0 h1
    change (cutoffPhaseLinfty a 0 - phaseLinfty 0 : Lp ℂ ∞ (volume : Measure ℝ)) z =
      (0 : Lp ℂ ∞ (volume : Measure ℝ)) z
    rw [h0,h1]
    simp [cutoffPhase,phase]
  rw [if_neg ht]
  apply le_antisymm
  · rw [Lp.norm_def,eLpNorm_exponent_top]
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [hae] with z hz
    rw [hz]
    exact (norm_sub_le _ _).trans (by rw [norm_cutoffPhase,norm_phase]; norm_num)
  · obtain ⟨z,hz,hsmall,hphase⟩ := exists_small_phase_half_turn t (Real.exp a) ht (Real.exp_pos a)
    have hp : ContinuousAt (phase t) z := by
      unfold phase
      fun_prop (disch := positivity)
    have hb := local_symbol_le_linfty _ _ z hae ((cutoffPhase_continuous_inside a t z hsmall).sub hp)
    rw [cutoffPhase_eq_one_inside a t z hsmall,hphase] at hb
    norm_num at hb ⊢
    exact hb

/-- Every cutoff width leaves a maximal operator-norm gap from the raw evolution at nonzero times. -/
theorem norm_cutoffEvolution_sub_raw (a t : ℝ) :
    ‖cutoffEvolution a t - (evolution t).toContinuousLinearEquiv.toContinuousLinearMap‖ =
      if t = 0 then 0 else 2 := by
  rw [cutoffEvolution_eq_lineLinftyMultiplier,evolution_eq_lineLinftyMultiplier,
    ← map_sub,norm_lineLinftyMultiplier,norm_cutoffPhaseLinfty_sub_raw]

/-- Operator-norm convergence to the raw evolution occurs precisely at time zero. -/
theorem cutoffEvolution_operator_tendsto_iff (t : ℝ) :
    Tendsto (fun a => cutoffEvolution a t) atBot
      (𝓝 (evolution t).toContinuousLinearEquiv.toContinuousLinearMap) ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
    simp only [norm_cutoffEvolution_sub_raw,if_neg ht] at hn
    have he : (2:ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
    norm_num at he
  · intro ht
    have he (a : ℝ) : cutoffEvolution a t =
        (evolution t).toContinuousLinearEquiv.toContinuousLinearMap := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      rw [norm_cutoffEvolution_sub_raw,if_pos ht]
    simpa only [he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
        (evolution t).toContinuousLinearEquiv.toContinuousLinearMap) atBot
        (𝓝 (evolution t).toContinuousLinearEquiv.toContinuousLinearMap))

/-- No alternative bounded operator can be the norm limit at a nonzero time. -/
theorem cutoffEvolution_exists_operator_limit_iff (t : ℝ) :
    (∃ A : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun a => cutoffEvolution a t) atBot (𝓝 A)) ↔ t = 0 := by
  constructor
  · rintro ⟨A,hA⟩
    have he : A = (evolution t).toContinuousLinearEquiv.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro u
      have h := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (volume : Measure ℝ)) u).continuous.continuousAt.tendsto.comp hA
      exact tendsto_nhds_unique h (cutoffEvolution_tendsto_atBot t u)
    rw [he] at hA
    exact (cutoffEvolution_operator_tendsto_iff t).1 hA
  · intro ht
    exact ⟨_,(cutoffEvolution_operator_tendsto_iff t).2 ht⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells
