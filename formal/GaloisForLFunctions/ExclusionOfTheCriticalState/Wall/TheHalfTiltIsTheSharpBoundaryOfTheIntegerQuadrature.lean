import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheEndpointFourierMomentOfTheIntegerError
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.FractionalFourierEnergyOfTheTiltedState
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateAndThePrimeSideHaveExactLogarithmicLawsAtTheWall
import GaloisForLFunctions.RHTower.TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa
import GaloisForLFunctions.RHTower.DQPTPartialSumRate
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness

/-!
# The half tilt is the sharp boundary of the integer quadrature

For the critical state let `D(t) = N(t) − A e^{t/2}` be the integer quadrature
error. Below the half tilt `e^{λt} D ∈ L²(ℝ)`; at every `λ ≥ 1/2` the positive-ray
integral of `(e^{λt} D)²` diverges.

Mechanism. Put `ψ(u) = e^{u/2} Φ(u)` and `H = 𝓕ψ`. A finite half-tilted mass would
make `ζ(iτ) H` square integrable (Fatou on the subcritical Parseval identities).
The functional equation gives `|τ| |ζ(1 − iτ)|² ≤ 4π |ζ(iτ)|²` for `|τ| ≥ 1`, hence
`|τ| |η(1 − iτ) H|²` is integrable, `η(s) = (1 − 2^{1−s}) ζ(s)`. The alternating
dilation row `Σ (−1)^n (n+1)^{−1−ε} ψ(u + log(n+1))` has transform `η(1+ε−iτ) H` and
equals `ψ` on the last `log 2` before the wall, so Plancherel and two dominated
limits give
`∫_{−h}^0 |ψ|² ≤ ∫ |1 − e^{ihτ}|² |η(1 − iτ) H|²` for `0 < h < log 2`.
Dyadic `h = 2^{−j}` telescope against `y/(1+y)`, so the sum over `j` of
`h^{−1} ∫_{−h}^0 |ψ|²` would be finite, while the terminal mass law of the wall
makes each term at least `c/j`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open Complex (I)
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- The unit phase `e^{2πix}`. -/
private def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*I)

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem continuous_phase : Continuous phase := by unfold phase; fun_prop

private theorem phase_add (x y : ℝ) : phase (x+y) = phase x*phase y := by
  unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `‖1 − e^{iθ}‖² = 2 − 2 cos θ ≤ min(4, θ²)`. -/
private theorem norm_sq_one_sub_exp_le (θ : ℝ) :
    ‖1-Complex.exp ((θ:ℂ)*I)‖^2 ≤ 4 ∧ ‖1-Complex.exp ((θ:ℂ)*I)‖^2 ≤ θ^2 := by
  have hn : ‖1-Complex.exp ((θ:ℂ)*I)‖^2 = 2-2*Real.cos θ := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.one_re,Complex.exp_ofReal_mul_I_re,Complex.sub_im,
      Complex.one_im,Complex.exp_ofReal_mul_I_im]
    linear_combination Real.sin_sq_add_cos_sq θ
  rw [hn]
  exact ⟨by linarith only [Real.neg_one_le_cos θ],by linarith only [Real.one_sub_sq_div_two_le_cos (x := θ)]⟩

private theorem norm_sq_one_sub_phase_le (x : ℝ) : ‖1-phase x‖^2 ≤ 4 :=
  (norm_sq_one_sub_exp_le (2*Real.pi*x)).1

/-- Fourier transform of a translate. -/
private theorem fourier_comp_add (f : ℝ → ℂ) (a ξ : ℝ) :
    𝓕 (fun u => f (u+a)) ξ = phase (a*ξ)*𝓕 f ξ := by
  calc 𝓕 (fun u => f (u+a)) ξ = ∫ v, Complex.exp (((-2*Real.pi*v*ξ:ℝ):ℂ)*I)*f (v+a) := by
          simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
    _ = ∫ v, Complex.exp (((-2*Real.pi*(v-a)*ξ:ℝ):ℂ)*I)*f v := by
          have h := integral_sub_right_eq_self (μ := volume)
            (fun v : ℝ => Complex.exp (((-2*Real.pi*v*ξ:ℝ):ℂ)*I)*f (v+a)) a
          simp only [sub_add_cancel] at h
          exact h.symm
    _ = ∫ v, phase (a*ξ)*(Complex.exp (((-2*Real.pi*v*ξ:ℝ):ℂ)*I)*f v) := by
          congr 1; funext v
          rw [← mul_assoc]; unfold phase; rw [← Complex.exp_add]; congr 2; push_cast; ring
    _ = phase (a*ξ)*𝓕 f ξ := by
          rw [integral_const_mul]; simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]

private theorem integrable_phase_mul {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun v => Complex.exp (((-2*Real.pi*v*ξ:ℝ):ℂ)*I)*f v) := by
  refine hf.norm.mono' ((by fun_prop : Continuous fun v : ℝ =>
    Complex.exp (((-2*Real.pi*v*ξ:ℝ):ℂ)*I)).aestronglyMeasurable.mul hf.1) (Eventually.of_forall fun v => ?_)
  rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]

private theorem fourier_sub_translates {f : ℝ → ℂ} (hf : Integrable f) (a b ξ : ℝ) :
    𝓕 (fun u => f (u+a)-f (u+b)) ξ = (phase (a*ξ)-phase (b*ξ))*𝓕 f ξ := by
  rw [sub_mul,← fourier_comp_add f a ξ,← fourier_comp_add f b ξ]
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul,mul_sub]
  exact integral_sub (integrable_phase_mul (hf.comp_add_right a) ξ) (integrable_phase_mul (hf.comp_add_right b) ξ)

private theorem fourier_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℝ → ℂ)
    (hg : ∀ i ∈ s, Integrable (g i)) (ξ : ℝ) :
    𝓕 (fun u => ∑ i ∈ s, c i*g i u) ξ = ∑ i ∈ s, c i*𝓕 (g i) ξ := by
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul,Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]; congr 1; funext v; ring
  · intro i hi
    exact ((integrable_phase_mul (hg i hi) ξ).const_mul (c i)).congr (Eventually.of_forall fun v => by ring)

/-! ### The alternating dilation row -/

/-- Coefficients `(−1)^n (n+1)^{−(1+ε)}`. -/
private def altCoeff (ε : ℝ) (n : ℕ) : ℂ := (-1:ℂ)^n*((((n:ℝ)+1:ℝ):ℂ))^(-((1+ε:ℝ):ℂ))

/-- The partial alternating Dirichlet series on the line `Re s = 1 + ε`, as a
function of the frequency. -/
private def altPhaseSum (ε : ℝ) (N : ℕ) (ξ : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, altCoeff ε n*phase (Real.log ((n:ℝ)+1)*ξ)

/-- The point `1 + ε − 2πiξ`. -/
private def lineArg (ε ξ : ℝ) : ℂ := ((1+ε:ℝ):ℂ)-((2*Real.pi*ξ:ℝ):ℂ)*I

/-- The entire function `(1 − 2^{1−s}) ζ(s)`. -/
private def etaFn (s : ℂ) : ℂ := _root_.RHTower.etaSlope s*_root_.RHTower.zetaResidueUnit s

private theorem continuous_etaFn : Continuous etaFn :=
  _root_.RHTower.differentiable_etaSlope_mul_zetaResidueUnit.continuous

private theorem etaFn_eq {s : ℂ} (hs : s ≠ 1) : etaFn s = (1-(2:ℂ)^(1-s))*riemannZeta s :=
  _root_.RHTower.etaSlope_mul_zetaResidueUnit hs

private theorem cpow_neg_lineArg {x : ℝ} (hx : 0 < x) (ε ξ : ℝ) :
    ((x:ℂ))^(-lineArg ε ξ) = ((x:ℂ))^(-((1+ε:ℝ):ℂ))*phase (Real.log x*ξ) := by
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  unfold lineArg
  rw [show -(((1+ε:ℝ):ℂ)-((2*Real.pi*ξ:ℝ):ℂ)*I) = -((1+ε:ℝ):ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I by ring,
    Complex.cpow_add _ _ hx0]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hx0,← Complex.ofReal_log hx.le]
  unfold phase; congr 1; push_cast; ring

private theorem altPhaseSum_eq (ε : ℝ) (N : ℕ) (ξ : ℝ) :
    altPhaseSum ε N ξ = _root_.RHTower.DQPT.dqptAltPartialSum (lineArg ε ξ) N := by
  unfold altPhaseSum _root_.RHTower.DQPT.dqptAltPartialSum
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold _root_.RHTower.DQPT.dqptRp altCoeff
  rw [cpow_neg_lineArg (by positivity : (0:ℝ) < (n:ℝ)+1)]
  ring

private theorem norm_altCoeff (ε : ℝ) (n : ℕ) : ‖altCoeff ε n‖ = ((n:ℝ)+1)^(-(1+ε)) := by
  unfold altCoeff
  rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1)]
  simp

private theorem summable_rpow_shift {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^(-(1+ε))) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : -(1+ε) < -1))
  simpa only [Nat.cast_add,Nat.cast_one] using h

private theorem norm_altPhaseSum_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) (ξ : ℝ) :
    ‖altPhaseSum ε N ξ‖ ≤ ∑' n : ℕ, ((n:ℝ)+1)^(-(1+ε)) := by
  unfold altPhaseSum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Finset.range N, ‖altCoeff ε n*phase (Real.log ((n:ℝ)+1)*ξ)‖
        = ∑ n ∈ Finset.range N, ((n:ℝ)+1)^(-(1+ε)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_mul,norm_phase,mul_one,norm_altCoeff]
    _ ≤ _ := (summable_rpow_shift hε).sum_le_tsum _ fun n _ => by positivity

private theorem continuous_altPhaseSum (ε : ℝ) (N : ℕ) : Continuous (altPhaseSum ε N) := by
  unfold altPhaseSum
  exact continuous_finset_sum _ fun n _ => continuous_const.mul
    (continuous_phase.comp (continuous_const.mul continuous_id))

private theorem altCoeff_zero (ε : ℝ) : altCoeff ε 0 = 1 := by simp [altCoeff]

/-! ### The window identity and Plancherel -/

/-- The alternating dilation row minus its translate by `h`. -/
private def dilationIncrement (ψ : ℝ → ℂ) (ε h : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, altCoeff ε n*(ψ (u+Real.log ((n:ℝ)+1))-ψ (u+(h+Real.log ((n:ℝ)+1))))

/-- On the last `h < log 2` before the wall only the first term survives, and
its translate has already crossed the wall. -/
private theorem dilationIncrement_eq {ψ : ℝ → ℂ} (hψ0 : ∀ u, 0 ≤ u → ψ u = 0) {h : ℝ}
    (hh2 : h < Real.log 2) (ε : ℝ) (N : ℕ) {u : ℝ} (hu : u ∈ Ioo (-h) 0) :
    dilationIncrement ψ ε h (N+1) u = ψ u := by
  unfold dilationIncrement
  rw [Finset.sum_range_succ']
  have hrest : ∀ n ∈ Finset.range N, altCoeff ε (n+1)*(ψ (u+Real.log (((n+1:ℕ):ℝ)+1))-
      ψ (u+(h+Real.log (((n+1:ℕ):ℝ)+1)))) = 0 := by
    intro n _
    have hl : Real.log 2 ≤ Real.log (((n+1:ℕ):ℝ)+1) :=
      Real.log_le_log (by norm_num) (by push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
    rw [hψ0 (u+Real.log (((n+1:ℕ):ℝ)+1)) (by linarith [hu.1,hu.2]),
      hψ0 (u+(h+Real.log (((n+1:ℕ):ℝ)+1))) (by linarith [hu.1,hu.2]),sub_zero,mul_zero]
  rw [Finset.sum_eq_zero hrest,zero_add,altCoeff_zero,one_mul]
  simp only [Nat.cast_zero,zero_add,Real.log_one,add_zero]
  rw [hψ0 (u+h) (by linarith [hu.1]),sub_zero]

private theorem integrable_dilationIncrement {ψ : ℝ → ℂ} (hψ1 : Integrable ψ) (ε h : ℝ) (N : ℕ) :
    Integrable (dilationIncrement ψ ε h N) := by
  unfold dilationIncrement
  exact integrable_finsetSum _ fun n _ =>
    ((hψ1.comp_add_right _).sub (hψ1.comp_add_right _)).const_mul _

private theorem memLp_dilationIncrement {ψ : ℝ → ℂ} (hψ2 : MemLp ψ 2) (ε h : ℝ) (N : ℕ) :
    MemLp (dilationIncrement ψ ε h N) 2 := by
  unfold dilationIncrement
  refine memLp_finsetSum _ fun n _ => ?_
  exact ((hψ2.comp_measurePreserving (measurePreserving_add_right volume _)).sub
    (hψ2.comp_measurePreserving (measurePreserving_add_right volume _))).const_mul _

private theorem fourier_dilationIncrement {ψ : ℝ → ℂ} (hψ1 : Integrable ψ) (ε h : ℝ) (N : ℕ) (ξ : ℝ) :
    𝓕 (dilationIncrement ψ ε h N) ξ = (1-phase (h*ξ))*altPhaseSum ε N ξ*𝓕 ψ ξ := by
  have key := fourier_finset_sum (Finset.range N) (altCoeff ε)
    (fun n (u : ℝ) => ψ (u+Real.log ((n:ℝ)+1))-ψ (u+(h+Real.log ((n:ℝ)+1))))
    (fun n _ => (hψ1.comp_add_right _).sub (hψ1.comp_add_right _)) ξ
  calc 𝓕 (dilationIncrement ψ ε h N) ξ = ∑ n ∈ Finset.range N, altCoeff ε n*
        𝓕 (fun u => ψ (u+Real.log ((n:ℝ)+1))-ψ (u+(h+Real.log ((n:ℝ)+1)))) ξ := key
    _ = ∑ n ∈ Finset.range N, altCoeff ε n*((phase (Real.log ((n:ℝ)+1)*ξ)-
          phase ((h+Real.log ((n:ℝ)+1))*ξ))*𝓕 ψ ξ) :=
        Finset.sum_congr rfl fun n _ => by rw [fourier_sub_translates hψ1]
    _ = (1-phase (h*ξ))*altPhaseSum ε N ξ*𝓕 ψ ξ := by
        unfold altPhaseSum
        rw [Finset.mul_sum,Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [add_mul,phase_add]; ring

/-- Plancherel for the finite row: the window mass is bounded by the
frequency-side energy of the partial alternating series. -/
private theorem window_mass_le_partial {ψ : ℝ → ℂ} (hψ1 : Integrable ψ) (hψ2 : MemLp ψ 2)
    (hψ0 : ∀ u, 0 ≤ u → ψ u = 0) {h : ℝ} (hh2 : h < Real.log 2) (ε : ℝ) (N : ℕ) :
    (∫ u in Ioo (-h) 0, ‖ψ u‖^2) ≤
      ∫ ξ, ‖1-phase (h*ξ)‖^2*‖altPhaseSum ε (N+1) ξ‖^2*‖𝓕 ψ ξ‖^2 := by
  let V := dilationIncrement ψ ε h (N+1)
  have hVi := integrable_dilationIncrement hψ1 ε h (N+1)
  have hV2 := memLp_dilationIncrement hψ2 ε h (N+1)
  have hsq : Integrable (fun u => ‖V u‖^2) := (memLp_two_iff_integrable_sq_norm hVi.1).1 hV2
  calc (∫ u in Ioo (-h) 0, ‖ψ u‖^2) = ∫ u in Ioo (-h) 0, ‖V u‖^2 :=
        setIntegral_congr_fun measurableSet_Ioo fun u hu => by
          dsimp only [V]; rw [dilationIncrement_eq hψ0 hh2 ε N hu]
    _ ≤ ∫ u, ‖V u‖^2 := setIntegral_le_integral hsq (Eventually.of_forall fun _ => sq_nonneg _)
    _ = ∫ ξ, ‖𝓕 V ξ‖^2 := (RHTower.integral_norm_sq_fourier_eq hVi hV2).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        dsimp only [V]
        rw [fourier_dilationIncrement hψ1,norm_mul,norm_mul,mul_pow,mul_pow]

private theorem le_integral_of_tendsto {f : ℕ → ℝ → ℝ} {F g : ℝ → ℝ} {L : ℝ}
    (hm : ∀ n, AEStronglyMeasurable (f n)) (hb : ∀ n ξ, ‖f n ξ‖ ≤ g ξ) (hg : Integrable g)
    (hlim : ∀ ξ, Tendsto (fun n => f n ξ) atTop (𝓝 (F ξ))) (hL : ∀ n, L ≤ ∫ ξ, f n ξ) :
    L ≤ ∫ ξ, F ξ :=
  ge_of_tendsto' (tendsto_integral_of_dominated_convergence g hm hg
    (fun n => ae_of_all _ (hb n)) (ae_of_all _ hlim)) hL

private theorem continuous_fourier {ψ : ℝ → ℂ} (hψ1 : Integrable ψ) : Continuous (𝓕 ψ) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hψ1

/-- The full alternating series on the line `Re s = 1 + ε`. -/
private theorem window_mass_le_eta {ψ : ℝ → ℂ} (hψ1 : Integrable ψ) (hψ2 : MemLp ψ 2)
    (hψ0 : ∀ u, 0 ≤ u → ψ u = 0) {h : ℝ} (hh2 : h < Real.log 2) {ε : ℝ} (hε : 0 < ε) :
    (∫ u in Ioo (-h) 0, ‖ψ u‖^2) ≤
      ∫ ξ, ‖1-phase (h*ξ)‖^2*‖etaFn (lineArg ε ξ)‖^2*‖𝓕 ψ ξ‖^2 := by
  let Z := ∑' n : ℕ, ((n:ℝ)+1)^(-(1+ε))
  have hH := continuous_fourier hψ1
  have hH2 : Integrable (fun ξ => ‖𝓕 ψ ξ‖^2) := RHTower.integrable_norm_sq_fourier hψ1 hψ2
  have hph : Continuous fun ξ : ℝ => ‖1-phase (h*ξ)‖^2 :=
    (continuous_const.sub (continuous_phase.comp (continuous_const.mul continuous_id))).norm.pow 2
  refine le_integral_of_tendsto (g := fun ξ => 4*Z^2*‖𝓕 ψ ξ‖^2) (fun N => ?_) (fun N ξ => ?_)
    (hH2.const_mul _) (fun ξ => ?_) (fun N => window_mass_le_partial hψ1 hψ2 hψ0 hh2 ε N)
  · exact ((hph.mul ((continuous_altPhaseSum ε (N+1)).norm.pow 2)).mul (hH.norm.pow 2)).aestronglyMeasurable
  · have hP := norm_altPhaseSum_le hε (N+1) ξ
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (norm_sq_one_sub_phase_le _) (pow_le_pow_left₀ (norm_nonneg _) hP 2)
      (sq_nonneg _) (by norm_num)
  · have hre' : (lineArg ε ξ).re = 1+ε := by
      simp only [lineArg,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
        Complex.ofReal_im,mul_zero,mul_one,sub_zero]
    have hs1 : lineArg ε ξ ≠ 1 := by
      intro e
      have := congrArg Complex.re e
      rw [hre',Complex.one_re] at this
      linarith
    have hre : 0 < (lineArg ε ξ).re := by rw [hre']; linarith
    have hlim := (_root_.RHTower.DQPT.dqpt_altPartialSum_tendsto hre hs1).comp (tendsto_add_atTop_nat 1)
    rw [← etaFn_eq hs1] at hlim
    have hlim' : Tendsto (fun N => altPhaseSum ε (N+1) ξ) atTop (𝓝 (etaFn (lineArg ε ξ))) := by
      simpa only [Function.comp_def,altPhaseSum_eq] using hlim
    exact ((tendsto_const_nhds.mul (hlim'.norm.pow 2)).mul tendsto_const_nhds)

private theorem one_add_rpow_le {x : ℝ} (hx : 0 ≤ x) :
    (1+x)^(5/8:ℝ) ≤ 1+x^(5/8:ℝ) := by
  have h := NNReal.rpow_add_le_add_rpow (1:NNReal) ⟨x,hx⟩ (p := 5/8) (by norm_num) (by norm_num)
  have h' := NNReal.coe_le_coe.2 h
  simpa [NNReal.coe_rpow] using h'

/-- The line `Re s = 1`: the uniform bound `|η(s)| ≪ (1 + |Im s|)^{5/16}` on
`Re s ≥ 1/2` and the fractional energy of the half-tilted state dominate the
limit `ε → 0`. -/
private theorem window_mass_le_line {ψ : ℝ → ℂ} (hψ1 : Integrable ψ) (hψ2 : MemLp ψ 2)
    (hψ0 : ∀ u, 0 ≤ u → ψ u = 0)
    (hfrac : Integrable fun ξ : ℝ => |ξ|^(5/8:ℝ)*‖𝓕 ψ ξ‖^2) {h : ℝ} (hh2 : h < Real.log 2) :
    (∫ u in Ioo (-h) 0, ‖ψ u‖^2) ≤
      ∫ ξ, ‖1-phase (h*ξ)‖^2*‖etaFn (lineArg 0 ξ)‖^2*‖𝓕 ψ ξ‖^2 := by
  obtain ⟨A,hA,hηb⟩ := _root_.RHTower.exists_norm_etaSlope_mul_zetaResidueUnit_le
  have hH := continuous_fourier hψ1
  have hH2 : Integrable (fun ξ => ‖𝓕 ψ ξ‖^2) := RHTower.integrable_norm_sq_fourier hψ1 hψ2
  have hph : Continuous fun ξ : ℝ => ‖1-phase (h*ξ)‖^2 :=
    (continuous_const.sub (continuous_phase.comp (continuous_const.mul continuous_id))).norm.pow 2
  have hline (ε : ℝ) : Continuous fun ξ : ℝ => lineArg ε ξ := by unfold lineArg; fun_prop
  let εs := fun k : ℕ => 1/((k:ℝ)+1)
  have hεs (k : ℕ) : 0 < εs k := one_div_pos.2 (by positivity)
  let g := fun ξ : ℝ => 4*A^2*(‖𝓕 ψ ξ‖^2+(2*Real.pi)^(5/8:ℝ)*(|ξ|^(5/8:ℝ)*‖𝓕 ψ ξ‖^2))
  have hg : Integrable g := (hH2.add (hfrac.const_mul _)).const_mul _
  refine le_integral_of_tendsto (g := g) (fun k => ?_) (fun k ξ => ?_) hg (fun ξ => ?_)
    (fun k => window_mass_le_eta hψ1 hψ2 hψ0 hh2 (hεs k))
  · exact ((hph.mul ((continuous_etaFn.comp (hline _)).norm.pow 2)).mul (hH.norm.pow 2)).aestronglyMeasurable
  · have hre : 1/2 ≤ (lineArg (εs k) ξ).re := by
      simp only [lineArg,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
        Complex.ofReal_im,mul_zero,mul_one,sub_zero]
      linarith [hεs k]
    have him : |(lineArg (εs k) ξ).im| = 2*Real.pi*|ξ| := by
      simp only [lineArg,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,mul_zero,mul_one,zero_sub,zero_add,add_zero,abs_neg]
      rw [abs_mul,abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    have hb := hηb _ hre
    rw [him] at hb
    have hx : 0 ≤ 2*Real.pi*|ξ| := by positivity
    have hsq : ‖etaFn (lineArg (εs k) ξ)‖^2 ≤ A^2*(1+(2*Real.pi)^(5/8:ℝ)*|ξ|^(5/8:ℝ)) := by
      calc ‖etaFn (lineArg (εs k) ξ)‖^2 ≤ (A*(1+2*Real.pi*|ξ|)^(5/16:ℝ))^2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = A^2*(1+2*Real.pi*|ξ|)^(5/8:ℝ) := by
            rw [mul_pow,← Real.rpow_natCast ((1+2*Real.pi*|ξ|)^(5/16:ℝ)),← Real.rpow_mul (by positivity)]
            norm_num
        _ ≤ A^2*(1+(2*Real.pi*|ξ|)^(5/8:ℝ)) := mul_le_mul_of_nonneg_left (one_add_rpow_le hx) (sq_nonneg _)
        _ = A^2*(1+(2*Real.pi)^(5/8:ℝ)*|ξ|^(5/8:ℝ)) := by
            rw [Real.mul_rpow (by positivity) (abs_nonneg _)]
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖1-phase (h*ξ)‖^2*‖etaFn (lineArg (εs k) ξ)‖^2*‖𝓕 ψ ξ‖^2
        ≤ 4*(A^2*(1+(2*Real.pi)^(5/8:ℝ)*|ξ|^(5/8:ℝ)))*‖𝓕 ψ ξ‖^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul (norm_sq_one_sub_phase_le _) hsq (sq_nonneg _)
            (by norm_num)) (sq_nonneg _)
      _ = g ξ := by dsimp only [g]; ring
  · have hε : Tendsto εs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hl : Tendsto (fun k => lineArg (εs k) ξ) atTop (𝓝 (lineArg 0 ξ)) := by
      have hc : Continuous fun ε : ℝ => lineArg ε ξ := by unfold lineArg; fun_prop
      exact (hc.tendsto 0).comp hε
    exact (tendsto_const_nhds.mul (((continuous_etaFn.tendsto _).comp hl).norm.pow 2)).mul tendsto_const_nhds

/-! ### Reflection at the boundary line -/

private theorem cosh_le_two_mul_sinh {X : ℝ} (hX : 1 ≤ X) : Real.cosh X ≤ 2*Real.sinh X := by
  rw [Real.cosh_eq,Real.sinh_eq,Real.exp_neg]
  have ha : 2 ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
  have hinv : (Real.exp X)⁻¹ ≤ 2⁻¹ := (inv_le_inv₀ (Real.exp_pos X) (by norm_num)).2 ha
  linarith

/-- The functional equation at `s = iτ`: `|τ| |ζ(1 − iτ)|² ≤ 4π |ζ(iτ)|²` for `|τ| ≥ 1`,
from `|Γ(iτ)|² τ sinh(πτ) = π` and `|cos(πiτ/2)| = cosh(πτ/2)`. -/
private theorem abs_mul_norm_sq_zeta_one_sub_le {τ : ℝ} (hτ : 1 ≤ |τ|) :
    |τ|*‖riemannZeta (1-(τ:ℂ)*I)‖^2 ≤ 4*Real.pi*‖riemannZeta ((τ:ℂ)*I)‖^2 := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h,abs_zero] at hτ; linarith
  have hw0 : (τ:ℂ)*I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hτ0) Complex.I_ne_zero
  have hwn : ∀ n : ℕ, (τ:ℂ)*I ≠ -n := by
    intro n h
    have := congrArg Complex.im h
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_one,zero_mul,add_zero,Complex.neg_im,Complex.natCast_im,neg_zero] at this
    exact hτ0 this
  have hw1 : (τ:ℂ)*I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,zero_mul,sub_zero,Complex.one_re] at this
    exact zero_ne_one this
  rw [riemannZeta_one_sub hwn hw1]
  have h2pi : ‖(2*(Real.pi:ℂ))^(-((τ:ℂ)*I))‖ = 1 := by
    rw [show (2*(Real.pi:ℂ)) = ((2*Real.pi:ℝ):ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp
  have hcos : ‖Complex.cos (Real.pi*((τ:ℂ)*I)/2)‖ = Real.cosh (Real.pi*τ/2) := by
    rw [show (Real.pi:ℂ)*((τ:ℂ)*I)/2 = ((Real.pi*τ/2:ℝ):ℂ)*I by push_cast; ring,
      Complex.cos_mul_I,← Complex.ofReal_cosh,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
  have hnw : ‖(τ:ℂ)*I‖ = |τ| := by
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hs : Real.sinh (Real.pi*τ) ≠ 0 := by
    rw [Ne,Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero hτ0
  have hgam : ‖Complex.Gamma ((τ:ℂ)*I)‖^2*(τ*Real.sinh (Real.pi*τ)) = Real.pi := by
    have h1 := _root_.RHTower.norm_Gamma_one_add_mul_I_sq hτ0
    rw [show (1:ℂ)+(τ:ℂ)*I = (τ:ℂ)*I+1 by ring,Complex.Gamma_add_one _ hw0,norm_mul,mul_pow,
      hnw,sq_abs] at h1
    have h2 : τ^2*‖Complex.Gamma ((τ:ℂ)*I)‖^2*Real.sinh (Real.pi*τ) = Real.pi*τ := by
      rw [h1,div_mul_cancel₀ _ hs]
    apply mul_left_cancel₀ hτ0
    linear_combination h2
  -- the even quantities in `t = |τ|`
  have hts : τ*Real.sinh (Real.pi*τ) = |τ|*Real.sinh (Real.pi*|τ|) := by
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h,mul_neg,Real.sinh_neg]; ring
  have htc : Real.cosh (Real.pi*τ/2) = Real.cosh (Real.pi*|τ|/2) := by
    rw [← Real.cosh_abs (Real.pi*τ/2),abs_div,abs_mul,abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hX : 1 ≤ Real.pi*|τ|/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hτ Real.pi_pos.le,Real.pi_gt_three]
  have hsx : Real.sinh (Real.pi*|τ|) = 2*Real.sinh (Real.pi*|τ|/2)*Real.cosh (Real.pi*|τ|/2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  rw [hts,hsx] at hgam
  rw [htc] at hcos
  have hc := cosh_le_two_mul_sinh hX
  rw [norm_mul,norm_mul,norm_mul,norm_mul,h2pi,hcos]
  have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [h2n]
  have hG0 : 0 ≤ ‖Complex.Gamma ((τ:ℂ)*I)‖ := norm_nonneg _
  have hZ0 : 0 ≤ ‖riemannZeta ((τ:ℂ)*I)‖ := norm_nonneg _
  have ht0 : 0 ≤ |τ| := abs_nonneg τ
  have hcp := Real.cosh_pos (Real.pi*|τ|/2)
  have hkey := mul_le_mul_of_nonneg_left hc (mul_nonneg (mul_nonneg (mul_nonneg ht0
    (sq_nonneg ‖Complex.Gamma ((τ:ℂ)*I)‖)) hcp.le) (sq_nonneg ‖riemannZeta ((τ:ℂ)*I)‖))
  have hπZ : 4*Real.pi*‖riemannZeta ((τ:ℂ)*I)‖^2 = 4*(‖Complex.Gamma ((τ:ℂ)*I)‖^2*(|τ|*(2*Real.sinh
      (Real.pi*|τ|/2)*Real.cosh (Real.pi*|τ|/2))))*‖riemannZeta ((τ:ℂ)*I)‖^2 := by rw [hgam]
  rw [hπZ]
  nlinarith [hkey]

/-- `|τ| |η(1 − iτ)|² ≤ 16π |ζ(iτ)|²` for `|τ| ≥ 1`, since `|1 − 2^{iτ}| ≤ 2`. -/
private theorem abs_mul_norm_sq_eta_le {τ : ℝ} (hτ : 1 ≤ |τ|) :
    |τ|*‖etaFn (1-(τ:ℂ)*I)‖^2 ≤ 16*Real.pi*‖riemannZeta ((τ:ℂ)*I)‖^2 := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h,abs_zero] at hτ; linarith
  have hne : 1-(τ:ℂ)*I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hτ0 this
  rw [etaFn_eq hne,sub_sub_cancel]
  have h2 : ‖1-(2:ℂ)^((τ:ℂ)*I)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one,show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]
    simp; norm_num
  have hz := abs_mul_norm_sq_zeta_one_sub_le hτ
  rw [norm_mul,mul_pow]
  have h4 : ‖1-(2:ℂ)^((τ:ℂ)*I)‖^2 ≤ 4 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2; norm_num at this; exact this
  calc |τ|*(‖1-(2:ℂ)^((τ:ℂ)*I)‖^2*‖riemannZeta (1-(τ:ℂ)*I)‖^2)
      ≤ |τ|*(4*‖riemannZeta (1-(τ:ℂ)*I)‖^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (sq_nonneg _)) (abs_nonneg _)
    _ = 4*(|τ|*‖riemannZeta (1-(τ:ℂ)*I)‖^2) := by ring
    _ ≤ 4*(4*Real.pi*‖riemannZeta ((τ:ℂ)*I)‖^2) := mul_le_mul_of_nonneg_left hz (by norm_num)
    _ = 16*Real.pi*‖riemannZeta ((τ:ℂ)*I)‖^2 := by ring

/-! ### Dyadic telescoping -/

private def wq (y : ℝ) : ℝ := y/(1+y)

private theorem wq_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ wq y := div_nonneg hy (by linarith)

private theorem wq_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : wq x ≤ wq y := by
  unfold wq
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `‖1 − e^{2πihξ}‖² ≤ h · 24 a (q(ha) − q(ha/2))` with `a = 2π|ξ|`, `q(y) = y/(1+y)`. -/
private theorem norm_sq_one_sub_phase_le_wq {h : ℝ} (hh : 0 < h) (ξ : ℝ) :
    ‖1-phase (h*ξ)‖^2 ≤ h*(24*(2*Real.pi*|ξ|)*(wq (h*(2*Real.pi*|ξ|))-wq (h*(2*Real.pi*|ξ|)/2))) := by
  set a := 2*Real.pi*|ξ| with hadef
  have ha : 0 ≤ a := by positivity
  set y := h*a with hydef
  have hy : 0 ≤ y := mul_nonneg hh.le ha
  obtain ⟨h4,hθ⟩ := norm_sq_one_sub_exp_le (2*Real.pi*(h*ξ))
  have hθy : (2*Real.pi*(h*ξ))^2 = y^2 := by
    rw [hydef,hadef]
    have : (2*Real.pi*(h*ξ))^2 = (h*(2*Real.pi))^2*ξ^2 := by ring
    rw [this,← sq_abs ξ]; ring
  rw [hθy] at hθ
  change ‖1-Complex.exp (((2*Real.pi*(h*ξ):ℝ):ℂ)*I)‖^2 ≤ _
  have hdiff : wq y-wq (y/2) = y/((1+y)*(2+y)) := by
    unfold wq; field_simp; ring
  rw [hdiff]
  have hden : 0 < (1+y)*(2+y) := by positivity
  have hrhs : h*(24*a*(y/((1+y)*(2+y)))) = 24*y^2/((1+y)*(2+y)) := by
    rw [hydef]; field_simp; ring
  rw [hrhs,le_div_iff₀ hden]
  set N := ‖1-Complex.exp (((2*Real.pi*(h*ξ):ℝ):ℂ)*I)‖^2
  have hN : 0 ≤ N := sq_nonneg _
  rcases le_or_gt y 1 with hy1 | hy1
  · have hp : (1+y)*(2+y) ≤ 6 := by nlinarith
    calc N*((1+y)*(2+y)) ≤ y^2*6 := mul_le_mul hθ hp hden.le (sq_nonneg _)
      _ ≤ 24*y^2 := by nlinarith [sq_nonneg y]
  · have hp : (1+y)*(2+y) ≤ 6*y^2 := by nlinarith
    calc N*((1+y)*(2+y)) ≤ 4*(6*y^2) := mul_le_mul h4 hp hden.le (by norm_num)
      _ = 24*y^2 := by ring

/-! ### The theorem -/

/-- At the half tilt the positive-ray square integral of the integer quadrature
error of the critical state diverges. -/
theorem criticalState_not_integrable_half_tilt_integer_error {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) :
    ¬ IntegrableOn (fun t => (tiltedIntegerError Φ (1/2) t)^2) (Ioi 0) := by
  intro hend
  have hZ := criticalState_endpoint_integer_fourier_moment hW ht hF hc he hC hb hend
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,_,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  -- the half-tilted state and its transform
  let ψ := fun u : ℝ => ((Real.exp (1/2*u)*Φ u:ℝ):ℂ)
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let f := fun u : ℝ => Real.exp (1/2*u)*F u
  have hclip : f = (fun u : ℝ => Real.exp (1/2*min u 0)*F u) := by
    funext u
    rcases le_total u 0 with hu | hu
    · simp [f,min_eq_left hu]
    · simp [f,hd.support u hu]
  have hfd : CriticalHalfLineEnergyDomain f := by
    rw [hclip]; exact criticalHalfLineEnergyDomain_exp_min_mul hd (by norm_num)
  have hrep : (fun u => (f u:ℂ)) =ᵐ[volume] ψ := he.mono fun u hu => by simp [f,ψ,hu]
  have hψ1 : Integrable ψ := hfd.integrable.ofReal.congr hrep
  have hψ2 : MemLp ψ 2 := ((memLp_two_iff_integrable_sq_norm hfd.integrable.ofReal.aestronglyMeasurable).2
    (by simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hfd.sq)).ae_eq hrep
  have hψ0 : ∀ u, 0 ≤ u → ψ u = 0 := fun u hu => by simp [ψ,hs u hu]
  have hfrac : Integrable fun ξ : ℝ => |ξ|^(5/8:ℝ)*‖𝓕 ψ ξ‖^2 :=
    criticalState_tilted_fractional_fourier_energy hW ht hF he (by norm_num) (by norm_num) (by norm_num)
  have hH : Continuous (𝓕 ψ) := continuous_fourier hψ1
  have hH2 : Integrable (fun ξ => ‖𝓕 ψ ξ‖^2) := RHTower.integrable_norm_sq_fourier hψ1 hψ2
  have hHL (ξ : ℝ) : 𝓕 ψ ξ = negativeHalfLineLaplace (cx F) (1/2-((2*Real.pi*ξ:ℝ):ℂ)*I) :=
    (fourier_tilted_state_rep he (1/2) ξ).trans (by congr 1; norm_num)
  -- frequency-side quantities
  obtain ⟨A,hA,hηb⟩ := _root_.RHTower.exists_norm_etaSlope_mul_zetaResidueUnit_le
  let a := fun ξ : ℝ => 2*Real.pi*|ξ|
  have ha0 (ξ : ℝ) : 0 ≤ a ξ := by simp only [a]; positivity
  have hac : Continuous a := by simp only [a]; fun_prop
  let B := fun ξ : ℝ => ‖etaFn (lineArg 0 ξ)‖^2*‖𝓕 ψ ξ‖^2
  have hBn (ξ : ℝ) : 0 ≤ B ξ := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hline0 (ξ : ℝ) : lineArg 0 ξ = 1-((2*Real.pi*ξ:ℝ):ℂ)*I := by
    simp only [lineArg,add_zero,Complex.ofReal_one]
  have hlc : Continuous fun ξ : ℝ => lineArg 0 ξ := by unfold lineArg; fun_prop
  have hBc : Continuous B := ((continuous_etaFn.comp hlc).norm.pow 2).mul (hH.norm.pow 2)
  have hηline (ξ : ℝ) : ‖etaFn (lineArg 0 ξ)‖ ≤ A*(1+a ξ)^(5/16:ℝ) := by
    have hre : 1/2 ≤ (lineArg 0 ξ).re := by
      rw [hline0]
      simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero]
      norm_num
    have h := hηb _ hre
    have him : |(lineArg 0 ξ).im| = a ξ := by
      rw [hline0]
      simp only [a,Complex.sub_im,Complex.one_im,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero,zero_sub,abs_neg]
      rw [abs_mul,abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    rw [him] at h
    exact h
  -- the dyadic majorant
  let M := fun ξ : ℝ => 24*(a ξ*wq (a ξ/2))*B ξ
  let Maj := fun ξ : ℝ => 384*Real.pi*‖riemannZeta (((2*Real.pi*ξ:ℝ):ℂ)*I)*
      negativeHalfLineLaplace (cx F) (1/2-((2*Real.pi*ξ:ℝ):ℂ)*I)‖^2+48*A^2*‖𝓕 ψ ξ‖^2
  have hMaj : Integrable Maj := (hZ.const_mul _).add (hH2.const_mul _)
  have hM_le (ξ : ℝ) : M ξ ≤ Maj ξ := by
    have hq : a ξ*wq (a ξ/2) = a ξ^2/(2+a ξ) := by
      have h1 : (1:ℝ)+a ξ/2 ≠ 0 := (by linarith [ha0 ξ] : (0:ℝ) < 1+a ξ/2).ne'
      have h2 : (2:ℝ)+a ξ ≠ 0 := (by linarith [ha0 ξ] : (0:ℝ) < 2+a ξ).ne'
      unfold wq; field_simp; ring
    have hZn : 0 ≤ 384*Real.pi*‖riemannZeta (((2*Real.pi*ξ:ℝ):ℂ)*I)*
        negativeHalfLineLaplace (cx F) (1/2-((2*Real.pi*ξ:ℝ):ℂ)*I)‖^2 := by positivity
    have hHn : 0 ≤ 48*A^2*‖𝓕 ψ ξ‖^2 := by positivity
    rcases le_or_gt 1 (a ξ) with h1 | h1
    · have hτ : 1 ≤ |2*Real.pi*ξ| := by
        rw [abs_mul,abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]; exact h1
      have hη := abs_mul_norm_sq_eta_le hτ
      rw [abs_mul,abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)] at hη
      have hqa : a ξ*wq (a ξ/2) ≤ a ξ := by
        rw [hq,div_le_iff₀ (by linarith [ha0 ξ])]; nlinarith [ha0 ξ]
      calc M ξ = 24*(a ξ*wq (a ξ/2))*B ξ := rfl
        _ ≤ 24*a ξ*B ξ := by
            have := mul_le_mul_of_nonneg_right hqa (hBn ξ); nlinarith
        _ = 24*((2*Real.pi*|ξ|)*‖etaFn (1-((2*Real.pi*ξ:ℝ):ℂ)*I)‖^2)*‖𝓕 ψ ξ‖^2 := by
            simp only [B,a]; rw [hline0]; ring
        _ ≤ 24*(16*Real.pi*‖riemannZeta (((2*Real.pi*ξ:ℝ):ℂ)*I)‖^2)*‖𝓕 ψ ξ‖^2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hη (by norm_num)
        _ = 384*Real.pi*‖riemannZeta (((2*Real.pi*ξ:ℝ):ℂ)*I)*
              negativeHalfLineLaplace (cx F) (1/2-((2*Real.pi*ξ:ℝ):ℂ)*I)‖^2 := by
            rw [norm_mul,mul_pow,← hHL]; ring
        _ ≤ Maj ξ := by simp only [Maj]; exact le_add_of_nonneg_right hHn
    · have hqa : a ξ*wq (a ξ/2) ≤ 1/2 := by
        rw [hq,div_le_iff₀ (by linarith [ha0 ξ])]; nlinarith [ha0 ξ]
      have hηs : ‖etaFn (lineArg 0 ξ)‖^2 ≤ 4*A^2 := by
        have hp : (1+a ξ)^(5/16:ℝ) ≤ 2 := by
          calc (1+a ξ)^(5/16:ℝ) ≤ (1+a ξ)^(1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [ha0 ξ]) (by norm_num)
            _ ≤ 2 := by rw [Real.rpow_one]; linarith
        have h2 := (hηline ξ).trans (mul_le_mul_of_nonneg_left hp hA)
        calc ‖etaFn (lineArg 0 ξ)‖^2 ≤ (A*2)^2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
          _ = 4*A^2 := by ring
      calc M ξ = 24*(a ξ*wq (a ξ/2))*B ξ := rfl
        _ ≤ 24*(1/2)*(4*A^2*‖𝓕 ψ ξ‖^2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqa (by norm_num))
              (mul_le_mul_of_nonneg_right hηs (sq_nonneg _)) (hBn ξ) (by norm_num)
        _ = 48*A^2*‖𝓕 ψ ξ‖^2 := by ring
        _ ≤ Maj ξ := by simp only [Maj]; exact le_add_of_nonneg_left hZn
  have hwqc (c : ℝ) (hc0 : 0 ≤ c) : Continuous fun ξ => wq (c*a ξ) := by
    unfold wq
    exact (continuous_const.mul hac).div (continuous_const.add (continuous_const.mul hac))
      fun ξ => (add_pos_of_pos_of_nonneg one_pos (mul_nonneg hc0 (ha0 ξ))).ne'
  have hM_nonneg (ξ : ℝ) : 0 ≤ M ξ :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (ha0 ξ) (wq_nonneg (by linarith [ha0 ξ])))) (hBn ξ)
  have hM : Integrable M := by
    refine hMaj.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · have hw2 : Continuous fun ξ => wq (a ξ/2) := by
        have := hwqc (1/2) (by norm_num)
        refine this.congr fun ξ => ?_
        congr 1; ring
      exact ((continuous_const.mul (hac.mul hw2)).mul hBc).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (hM_nonneg ξ)]; exact hM_le ξ
  -- dyadic scales
  let hs' := fun j : ℕ => (1/2:ℝ)^(j+1)
  have hs'pos (j : ℕ) : 0 < hs' j := pow_pos (by norm_num) _
  have hs'le (j : ℕ) : hs' j ≤ 1/2 := by
    simp only [hs']; rw [pow_succ]
    have : (1/2:ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hs'succ (j : ℕ) : hs' (j+1) = hs' j/2 := by simp only [hs']; rw [pow_succ (1/2:ℝ) (j+1)]; ring
  have hlog2 : (1/2:ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  let wm := fun h : ℝ => ∫ u in Ioo (-h) 0, ‖ψ u‖^2
  let tm := fun (j : ℕ) (ξ : ℝ) => 24*a ξ*(wq (hs' j*a ξ)-wq (hs' (j+1)*a ξ))*B ξ
  have hmono (j : ℕ) (ξ : ℝ) : wq (hs' (j+1)*a ξ) ≤ wq (hs' j*a ξ) := by
    apply wq_mono (mul_nonneg (hs'pos (j+1)).le (ha0 ξ))
    rw [hs'succ]
    nlinarith [hs'pos j,ha0 ξ]
  have htm_nonneg (j : ℕ) (ξ : ℝ) : 0 ≤ tm j ξ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (ha0 ξ)) (sub_nonneg.2 (hmono j ξ))) (hBn ξ)
  have htm_le (j : ℕ) (ξ : ℝ) : tm j ξ ≤ M ξ := by
    have h0 := wq_nonneg (mul_nonneg (hs'pos (j+1)).le (ha0 ξ))
    have h1 := wq_mono (mul_nonneg (hs'pos j).le (ha0 ξ))
      (show hs' j*a ξ ≤ a ξ/2 by nlinarith [hs'le j,ha0 ξ])
    have h2 : wq (hs' j*a ξ)-wq (hs' (j+1)*a ξ) ≤ wq (a ξ/2) := by linarith
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 24) (ha0 ξ))
    simp only [tm,M]
    nlinarith [hBn ξ]
  have htm_int (j : ℕ) : Integrable (tm j) := by
    refine hM.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (((continuous_const.mul hac).mul ((hwqc _ (hs'pos j).le).sub
        (hwqc _ (hs'pos (j+1)).le))).mul hBc).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (htm_nonneg j ξ)]; exact htm_le j ξ
  have hpt (j : ℕ) (ξ : ℝ) :
      ‖1-phase (hs' j*ξ)‖^2*‖etaFn (lineArg 0 ξ)‖^2*‖𝓕 ψ ξ‖^2 ≤ tm j ξ*hs' j := by
    have hp := norm_sq_one_sub_phase_le_wq (hs'pos j) ξ
    have hhalf : hs' j*(2*Real.pi*|ξ|)/2 = hs' (j+1)*a ξ := by rw [hs'succ]; simp only [a]; ring
    rw [hhalf] at hp
    calc ‖1-phase (hs' j*ξ)‖^2*‖etaFn (lineArg 0 ξ)‖^2*‖𝓕 ψ ξ‖^2
        = ‖1-phase (hs' j*ξ)‖^2*B ξ := by simp only [B]; ring
      _ ≤ hs' j*(24*(2*Real.pi*|ξ|)*(wq (hs' j*(2*Real.pi*|ξ|))-wq (hs' (j+1)*a ξ)))*B ξ :=
        mul_le_mul_of_nonneg_right hp (hBn ξ)
      _ = tm j ξ*hs' j := by simp only [tm,a]; ring
  have hscale (j : ℕ) : wm (hs' j)/hs' j ≤ ∫ ξ, tm j ξ := by
    have hw := window_mass_le_line hψ1 hψ2 hψ0 hfrac ((hs'le j).trans_lt hlog2)
    rw [div_le_iff₀ (hs'pos j)]
    refine hw.trans ?_
    rw [← integral_mul_const]
    have hph : Continuous fun ξ : ℝ => ‖1-phase (hs' j*ξ)‖^2 :=
      (continuous_const.sub (continuous_phase.comp (continuous_const.mul continuous_id))).norm.pow 2
    have hleft : Integrable fun ξ => ‖1-phase (hs' j*ξ)‖^2*‖etaFn (lineArg 0 ξ)‖^2*‖𝓕 ψ ξ‖^2 := by
      refine ((htm_int j).mul_const (hs' j)).mono' ?_ (Eventually.of_forall fun ξ => ?_)
      · exact ((hph.mul ((continuous_etaFn.comp hlc).norm.pow 2)).mul (hH.norm.pow 2)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (by positivity)]; exact hpt j ξ
    exact integral_mono hleft ((htm_int j).mul_const _) (hpt j)
  -- the dyadic window masses have bounded partial sums
  have htel0 (ξ : ℝ) (J : ℕ) : ∑ j ∈ Finset.range J, (wq (hs' j*a ξ)-wq (hs' (j+1)*a ξ)) =
      wq (hs' 0*a ξ)-wq (hs' J*a ξ) := by
    induction J with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih]; ring
  have hpartial (J : ℕ) : ∑ j ∈ Finset.range J, wm (hs' j)/hs' j ≤ ∫ ξ, M ξ := by
    calc ∑ j ∈ Finset.range J, wm (hs' j)/hs' j ≤ ∑ j ∈ Finset.range J, ∫ ξ, tm j ξ :=
          Finset.sum_le_sum fun j _ => hscale j
      _ = ∫ ξ, ∑ j ∈ Finset.range J, tm j ξ := (integral_finsetSum _ fun j _ => htm_int j).symm
      _ ≤ ∫ ξ, M ξ := by
          refine integral_mono (integrable_finsetSum _ fun j _ => htm_int j) hM fun ξ => ?_
          have htel : ∑ j ∈ Finset.range J, tm j ξ =
              24*a ξ*(wq (hs' 0*a ξ)-wq (hs' J*a ξ))*B ξ := by
            simp only [tm]
            rw [← Finset.sum_mul,← Finset.mul_sum,htel0]
          rw [htel]
          have h0 : hs' 0*a ξ = a ξ/2 := by simp only [hs']; ring
          have hJ := wq_nonneg (mul_nonneg (hs'pos J).le (ha0 ξ))
          rw [h0]
          simp only [M]
          nlinarith [mul_nonneg (mul_nonneg (ha0 ξ) hJ) (hBn ξ)]
  have hnn (j : ℕ) : 0 ≤ wm (hs' j)/hs' j :=
    div_nonneg (setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _) (hs'pos j).le
  have hsum : Summable fun j => wm (hs' j)/hs' j := summable_of_sum_range_le hnn hpartial
  -- the terminal mass law of the wall gives a harmonic lower bound
  obtain ⟨c,hc0,hlow⟩ := criticalState_eventually_le_log_mul_terminal_square_mass hW ht hF
  have hto : Tendsto hs' atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_,Eventually.of_forall hs'pos⟩
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨J0,hJ0⟩ := eventually_atTop.1 (hto.eventually hlow)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hψc : Continuous ψ := by simp only [ψ]; fun_prop
  have hlowj (j : ℕ) (hj : J0 ≤ j) :
      Real.exp (-1)*c/(((j:ℝ)+2)*Real.log 2) ≤ wm (hs' j)/hs' j := by
    have hk := hJ0 j hj
    have hlog : Real.log (2/hs' j) = ((j:ℝ)+2)*Real.log 2 := by
      have h2 : (2:ℝ)/hs' j = 2^(j+2) := by
        simp only [hs']; rw [one_div_pow,div_div_eq_mul_div,div_one]; ring
      rw [h2,Real.log_pow]; push_cast; ring
    rw [hlog] at hk
    have hden : 0 < ((j:ℝ)+2)*Real.log 2 := by positivity
    have hmass : Real.exp (-1)*(∫ u in Ioo (-hs' j) 0, F u^2) ≤ wm (hs' j) := by
      have hFΦ : (∫ u in Ioo (-hs' j) 0, F u^2) = ∫ u in Ioo (-hs' j) 0, Φ u^2 :=
        integral_congr_ae (by filter_upwards [ae_restrict_of_ae he] with u hu; rw [hu])
      rw [hFΦ,← integral_const_mul]
      refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo fun u hu => ?_
      · exact ((hc.pow 2).const_mul _).integrableOn_Icc.mono_set Ioo_subset_Icc_self
      · exact (hψc.norm.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
      · have he1 : Real.exp (-1) ≤ Real.exp u := Real.exp_le_exp.2 (by linarith [hu.1,hs'le j])
        have hn : ‖ψ u‖^2 = Real.exp u*Φ u^2 := by
          simp only [ψ,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow]
          rw [← Real.exp_nat_mul]; congr 2; push_cast; ring
        rw [hn]
        exact mul_le_mul_of_nonneg_right he1 (sq_nonneg _)
    rw [le_div_iff₀ (hs'pos j),div_mul_eq_mul_div,div_le_iff₀ hden]
    have h3 := mul_le_mul_of_nonneg_left hk (Real.exp_pos (-1)).le
    have h4 := mul_le_mul_of_nonneg_right hmass hden.le
    nlinarith [h3,h4]
  -- harmonic divergence
  let κ := Real.exp (-1)*c/Real.log 2
  have hκ : 0 < κ := div_pos (mul_pos (Real.exp_pos _) hc0) hl2
  have hharm : Summable fun j : ℕ => κ/(((j+(J0+2):ℕ):ℝ)) := by
    refine Summable.of_nonneg_of_le (fun j => div_nonneg hκ.le (Nat.cast_nonneg _)) (fun j => ?_)
      ((summable_nat_add_iff J0).2 hsum)
    have := hlowj (j+J0) (Nat.le_add_left _ _)
    calc κ/(((j+(J0+2):ℕ):ℝ)) = Real.exp (-1)*c/((((j+J0:ℕ):ℝ)+2)*Real.log 2) := by
          simp only [κ]; rw [div_div]; congr 1; push_cast; ring
      _ ≤ _ := this
  have hinv : Summable fun n : ℕ => 1/(n:ℝ) := by
    have h1 : Summable fun j : ℕ => 1/(((j+(J0+2):ℕ):ℝ)) := by
      refine (hharm.mul_left κ⁻¹).congr fun j => ?_
      rw [mul_div_assoc',inv_mul_cancel₀ hκ.ne']
    exact (summable_nat_add_iff (J0+2)).1 h1
  exact Real.not_summable_one_div_natCast hinv

/-- For every `λ ≥ 1/2` the tilted integer quadrature error of the critical state
is not square integrable on the positive ray. -/
theorem criticalState_not_memLp_supercritical_integer_error {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {β : ℝ} (hβ : 1/2 ≤ β) :
    ¬ MemLp (tiltedIntegerError Φ β) 2 (volume.restrict (Ioi 0)) := by
  intro hm
  apply criticalState_not_integrable_half_tilt_integer_error hW ht hF hc he hC hb
  have hsq : IntegrableOn (fun t => (tiltedIntegerError Φ β t)^2) (Ioi 0) := by
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm hm.1).1 hm
  have hN := continuous_integerReferenceWave hc hC hb
  have hcont : Continuous (tiltedIntegerError Φ (1/2)) := by unfold tiltedIntegerError; fun_prop
  refine hsq.mono' (hcont.pow 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with t ht0
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  unfold tiltedIntegerError
  rw [mul_pow,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_right hβ (le_of_lt ht0))) 2

/-- The sharp exponential mean-square boundary of the integer quadrature: on the
critical state forced by failure of RH, `e^{λt}D ∈ L²(ℝ)` for `0 ≤ λ < 1/2` and
`e^{λt}D ∉ L²(0, ∞)` for `λ ≥ 1/2`. -/
theorem riemannHypothesis_or_sharp_integer_quadrature_boundary : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      (∀ β : ℝ, 0 ≤ β → β < 1/2 → MemLp (tiltedIntegerError Φ β) 2) ∧
      ∀ β : ℝ, 1/2 ≤ β → ¬ MemLp (tiltedIntegerError Φ β) 2 (volume.restrict (Ioi 0)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,
    fun _ hβ hβ' => criticalState_subcritical_integer_error hW ht hF hc he hC hb hβ hβ',
    fun _ hβ => criticalState_not_memLp_supercritical_integer_error hW ht hF hc he hC hb hβ⟩

#print axioms riemannHypothesis_or_sharp_integer_quadrature_boundary
end GaloisForLFunctions.ExclusionOfTheCriticalState
