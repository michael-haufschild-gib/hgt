import GaloisForLFunctions.RHTower.SoninGammaClockPhaseJets
import GaloisForLFunctions.RHTower.PolynomialJetMultiplierLimit

/-!
# Original Gamma clock exponentials converge on Schwartz tests

The exact discarded phase jets converge with polynomial height weights.
The original scattering exponential solves its literal scalar ODE, whose
coefficient error is the derivative of that discarded phase. Weighted-limit
algebra and the full Leibniz recurrence propagate convergence to every
exponential derivative. Each fixed Schwartz test absorbs the resulting weights.

The result retains the original finite clock endpoints, compensation, and
Gamma scattering orientation. It holds for every countably generated cofinal
endpoint family. The tested nuclear/cubic operator limit is a further theorem;
this does not close joint prime–polar completion or the TG sub-unit law.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped SchwartzMap
namespace RHTower

private def cutoffCoefficient (ε R t : ℝ) : ℂ :=
  2*Complex.I*((deriv (fun x => gammaClockHardyPhaseCutoff x ε R) t : ℝ):ℂ)

private def fullCoefficient (t : ℝ) : ℂ := 2*Complex.I*(gammaHardyPhaseRate t:ℂ)

private theorem fullCoefficient_temperate : Function.HasTemperateGrowth fullCoefficient :=
  (Function.HasTemperateGrowth.const (2*Complex.I)).mul
    gammaHardyPhaseRate_complex_hasTemperateGrowth

private theorem error_deriv {ε : ℝ} (hε : 0 < ε) (R t : ℝ) :
    deriv (fun x => gammaClockHardyPhaseLift x-gammaClockHardyPhaseCutoff x ε R) t =
      gammaHardyPhaseRate t-deriv (fun x => gammaClockHardyPhaseCutoff x ε R) t := by
  rw [deriv_fun_sub (hasDerivAt_gammaClockHardyPhaseLift t).differentiableAt
    ((contDiff_gammaClockHardyPhaseCutoff hε R).differentiable (by simp) t),
    (hasDerivAt_gammaClockHardyPhaseLift t).deriv]

private theorem error_deriv_temperate {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Function.HasTemperateGrowth
      (deriv (fun x => gammaClockHardyPhaseLift x-gammaClockHardyPhaseCutoff x ε R)) := by
  have hs := (gammaClockHardyPhase_error_hasTemperateGrowth hε R).1
  refine ⟨(contDiff_infty_iff_deriv.mp hs).2, fun n =>
    ⟨2, gammaClockPhaseErrorMajorant (n+1) ε R, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ']
  exact gammaClockHardyPhase_error_weighted_bound (n+1) hε R t

private theorem cutoffCoefficient_temperate {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Function.HasTemperateGrowth (cutoffCoefficient ε R) := by
  have heq : cutoffCoefficient ε R = fun t =>
      2*Complex.I*((gammaHardyPhaseRate t:ℂ)-
        ((deriv (fun x => gammaClockHardyPhaseLift x-gammaClockHardyPhaseCutoff x ε R) t:ℝ):ℂ)) := by
    funext t
    rw [error_deriv hε R t]
    simp only [cutoffCoefficient, Complex.ofReal_sub, sub_sub_cancel]
  rw [heq]
  exact (Function.HasTemperateGrowth.const (2*Complex.I)).mul
    (gammaHardyPhaseRate_complex_hasTemperateGrowth.sub
      (Complex.ofRealCLM.hasTemperateGrowth.comp (error_deriv_temperate hε R)))

private theorem cutoff_ode {ε : ℝ} (hε : 0 < ε) (R t : ℝ) :
    HasDerivAt (gammaClockScatteringCutoffSymbol ε R)
      (cutoffCoefficient ε R t*gammaClockScatteringCutoffSymbol ε R t) t := by
  have hd := (((((contDiff_gammaClockHardyPhaseCutoff hε R).differentiable
    (by simp) t).hasDerivAt).ofReal_comp).const_mul (2*Complex.I)).cexp
  change HasDerivAt (fun x => Complex.exp (2*Complex.I*(gammaClockHardyPhaseCutoff x ε R:ℂ)))
    ((2*Complex.I*((deriv (fun x => gammaClockHardyPhaseCutoff x ε R) t:ℝ):ℂ))*
      Complex.exp (2*Complex.I*(gammaClockHardyPhaseCutoff t ε R:ℂ))) t
  exact hd.congr_deriv (mul_comm _ _)

private theorem cutoff_norm (ε R t : ℝ) : ‖gammaClockScatteringCutoffSymbol ε R t‖=1 := by
  simp [gammaClockScatteringCutoffSymbol, Complex.norm_exp]

/-- The original finite clock phase acts on every Schwartz test. -/
theorem gammaClockScatteringCutoffSymbol_hasTemperateGrowth {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Function.HasTemperateGrowth (gammaClockScatteringCutoffSymbol ε R) :=
  hasTemperateGrowth_of_unitary_ode (fun t => (cutoff_ode hε R t).differentiableAt)
    (cutoffCoefficient_temperate hε R) (fun t => (cutoff_ode hε R t).deriv) (cutoff_norm ε R)

private theorem phase_exp_sub_bound (x y : ℝ) :
    ‖Complex.exp (2*Complex.I*(x:ℂ))-Complex.exp (2*Complex.I*(y:ℂ))‖ ≤ 2*‖x-y‖ := by
  have he : Complex.exp (2*Complex.I*(x:ℂ))-Complex.exp (2*Complex.I*(y:ℂ)) =
      Complex.exp (2*Complex.I*(y:ℂ))*(Complex.exp (Complex.I*((2*(x-y):ℝ):ℂ))-1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul]
  have hu : ‖Complex.exp (2*Complex.I*(y:ℂ))‖=1 := by simp [Complex.norm_exp]
  rw [hu, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*(x-y))
  simpa only [norm_mul, Real.norm_ofNat] using h

private theorem cutoff_weighted_zero {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) :
    PolynomiallyWeightedLimit l (fun i => gammaClockScatteringCutoffSymbol (ε i) (R i))
      ccmArchimedeanScatteringPhase := by
  refine ⟨2, 1, fun i => 2*gammaClockPhaseErrorMajorant 0 (ε i) (R i),
    zero_le_one, fun i => mul_nonneg (by norm_num) (gammaClockPhaseErrorMajorant_nonneg _ _ _),
    ?_, ?_, ?_⟩
  · simpa only [mul_zero] using (gammaClockPhaseErrorMajorant_tendsto 0 hε hR).const_mul 2
  · intro t
    rw [norm_ccmArchimedeanScatteringPhase, one_mul]
    exact one_le_pow₀ (by linarith [norm_nonneg t])
  · filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
    intro t
    rw [gammaClockScatteringCutoffSymbol, ccmArchimedeanScatteringPhase_eq_exp_gammaClock]
    calc
      _ ≤ 2*‖gammaClockHardyPhaseCutoff t (ε i) (R i)-gammaClockHardyPhaseLift t‖ :=
        phase_exp_sub_bound _ _
      _ = 2*‖gammaClockHardyPhaseLift t-gammaClockHardyPhaseCutoff t (ε i) (R i)‖ := by rw [norm_sub_rev]
      _ ≤ 2*(gammaClockPhaseErrorMajorant 0 (ε i) (R i)*(1+‖t‖)^2) :=
        mul_le_mul_of_nonneg_left (gammaClockHardyPhase_error_weighted_bound 0 hi (R i) t) (by norm_num)
      _ = _ := by ring

private theorem coefficient_jet_error {ε : ℝ} (hε : 0 < ε) (R : ℝ) (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n (cutoffCoefficient ε R) t-iteratedDeriv n fullCoefficient t‖ ≤
      (2*gammaClockPhaseErrorMajorant (n+1) ε R)*(1+‖t‖)^2 := by
  have hs := (error_deriv_temperate hε R).1
  have heq : (fun x => fullCoefficient x-cutoffCoefficient ε R x) = fun x =>
      2*Complex.I*((deriv (fun y => gammaClockHardyPhaseLift y-gammaClockHardyPhaseCutoff y ε R) x:ℝ):ℂ) := by
    funext x
    rw [error_deriv hε R x]
    simp only [fullCoefficient, cutoffCoefficient, Complex.ofReal_sub]
    ring
  rw [norm_sub_rev, ← iteratedDeriv_fun_sub
    (fullCoefficient_temperate.1.contDiffAt.of_le (by exact_mod_cast le_top))
    ((cutoffCoefficient_temperate hε R).1.contDiffAt.of_le (by exact_mod_cast le_top)), heq,
    iteratedDeriv_const_mul_field, SchwartzMap.iteratedDeriv_ofReal _ hs,
    ← iteratedDeriv_succ', norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ 2*(gammaClockPhaseErrorMajorant (n+1) ε R*(1+‖t‖)^2) :=
      mul_le_mul_of_nonneg_left (gammaClockHardyPhase_error_weighted_bound (n+1) hε R t) (by norm_num)
    _ = _ := by ring

private theorem cutoff_weighted_coefficient {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (n : ℕ) :
    PolynomiallyWeightedLimit l (fun i => iteratedDeriv n (cutoffCoefficient (ε i) (R i)))
      (iteratedDeriv n fullCoefficient) := by
  obtain ⟨k, C, hb⟩ := fullCoefficient_temperate.2 n
  simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
  have hC : 0 ≤ C := by
    have h := (norm_nonneg (iteratedDeriv n fullCoefficient 0)).trans (hb 0)
    simpa only [norm_zero, add_zero, one_pow, mul_one] using h
  refine ⟨k+2, C, fun i => 2*gammaClockPhaseErrorMajorant (n+1) (ε i) (R i), hC,
    fun i => mul_nonneg (by norm_num) (gammaClockPhaseErrorMajorant_nonneg _ _ _), ?_, ?_, ?_⟩
  · simpa only [mul_zero] using (gammaClockPhaseErrorMajorant_tendsto (n+1) hε hR).const_mul 2
  · intro t
    exact (hb t).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_right k 2)) hC)
  · filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
    intro t
    exact (coefficient_jet_error hi (R i) n t).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_left 2 k))
      (mul_nonneg (by norm_num) (gammaClockPhaseErrorMajorant_nonneg _ _ _)))

/-- Every derivative of the original clock scattering phase converges with a polynomial weight. -/
theorem gammaClockScatteringCutoffSymbol_weighted_jet_limit
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (n : ℕ) :
    PolynomiallyWeightedLimit l
      (fun i => iteratedDeriv n (gammaClockScatteringCutoffSymbol (ε i) (R i)))
      (iteratedDeriv n ccmArchimedeanScatteringPhase) :=
  polynomiallyWeightedLimit_iteratedDeriv_of_ode
    (fun i => (gammaClockScatteringCutoffSymbol_hasTemperateGrowth (hpos i) (R i)).1)
    ccmArchimedeanScatteringPhase_hasTemperateGrowth.1
    (fun i => (cutoffCoefficient_temperate (hpos i) (R i)).1) fullCoefficient_temperate.1
    (fun i t => (cutoff_ode (hpos i) (R i) t).deriv) deriv_ccmArchimedeanScatteringPhase
    (cutoff_weighted_zero hε hR) (cutoff_weighted_coefficient hε hR) n

/-- The literal finite clock phase acting on a Schwartz test. -/
def gammaClockScatteringCutoffSchwartz (ε R : ℝ) (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (gammaClockScatteringCutoffSymbol ε R) g

/-- The Schwartz realization retains pointwise multiplication by the original cutoff symbol. -/
theorem gammaClockScatteringCutoffSchwartz_apply {ε : ℝ} (hε : 0 < ε)
    (R : ℝ) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    gammaClockScatteringCutoffSchwartz ε R g t = gammaClockScatteringCutoffSymbol ε R t*g t := by
  rw [gammaClockScatteringCutoffSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (gammaClockScatteringCutoffSymbol_hasTemperateGrowth hε R)]
  exact smul_eq_mul _ _

/-- Positive original clock cutoffs converge on every fixed Schwartz test in the full topology. -/
theorem gammaClockScatteringCutoffSchwartz_tendsto_of_pos
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun i => gammaClockScatteringCutoffSchwartz (ε i) (R i) g) l
      (𝓝 (ccmArchimedeanScatteringPhaseMul g)) := by
  apply tendsto_schwartz_of_polynomiallyWeightedLimit
    (fun i => (gammaClockScatteringCutoffSymbol_hasTemperateGrowth (hpos i) (R i)).1)
    ccmArchimedeanScatteringPhase_hasTemperateGrowth.1
    (gammaClockScatteringCutoffSymbol_weighted_jet_limit hpos hε hR) g
  · intro i t
    exact gammaClockScatteringCutoffSchwartz_apply (hpos i) (R i) g t
  · intro t
    exact ccmArchimedeanScatteringPhaseMul_apply g t

/-- Every cofinal removal of the original clock endpoints converges in the full Schwartz topology. -/
theorem gammaClockScatteringCutoffSchwartz_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun i => gammaClockScatteringCutoffSchwartz (ε i) (R i) g) l
      (𝓝 (ccmArchimedeanScatteringPhaseMul g)) := by
  let ε' : ι → ℝ := fun i => if 0 < ε i then ε i else 1
  have hpos (i : ι) : 0 < ε' i := by
    dsimp [ε']
    split_ifs with hi
    · exact hi
    · norm_num
  have heq : ε' =ᶠ[l] ε := by
    filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
    exact if_pos hi
  have ht := gammaClockScatteringCutoffSchwartz_tendsto_of_pos hpos (hε.congr' heq.symm) hR g
  apply ht.congr'
  filter_upwards [heq] with i hi
  rw [hi]

end RHTower
