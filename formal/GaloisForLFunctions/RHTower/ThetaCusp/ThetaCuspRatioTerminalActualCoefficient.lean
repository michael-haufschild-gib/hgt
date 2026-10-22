import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalUniversalSurplus
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalCoefficientSlice
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalFlatTransfer

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioInfinity Filter Topology
open RHTower.ThetaCuspModularRatio

def sixthSourceCoefficient : Poly := universalSurplusCoefficient ThetaRatioSquare.reducedSlope 6

def actualSourceSurplus (x : ℝ) : Polynomial ℂ :=
  let N := sourceSurplusNormal ((u x:ℂ)^2) (k x:ℂ)
    (kineticSourcePolynomial ThetaRatioSquare.reducedSlope ((u x:ℂ)^2) (k x:ℂ))
  N.re+Polynomial.C ((J x:ℂ)/(u x:ℂ))*N.im

theorem sixthSourceCoefficient_actual (x : ℝ) :
    eval (actualSquarePoint x) sixthSourceCoefficient=(actualSourceSurplus x).coeff 6 := by
  have hp : actualSquarePoint x=basePoint ((u x:ℂ)^2) (k x:ℂ) ((J x:ℂ)/(u x:ℂ)) := by
    funext i
    cases i <;> rfl
  rw [hp]
  exact universalSurplusCoefficient_eval ThetaRatioSquare.reducedSlope _ _ _ 6

theorem sixthSourceCoefficient_flat (k : ℂ) :
    eval (basePoint 9 k (1/3)) sixthSourceCoefficient=(flatSourceSurplus k (1/3)).coeff 6 :=
  universalSurplusCoefficient_flat ThetaRatioSquare.reducedSlope _ _ _

def terminalClock (x : ℝ) : ℝ := (3*k x+1)⁻¹

theorem terminalClock_tendsto : Tendsto terminalClock atTop (𝓝 0) := by
  have ht : Tendsto (fun x => 3*k x+1) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [(tendsto_atTop.1 k_tendsto_atTop) ((B-1)/3)] with x hx
    linarith
  exact tendsto_inv_atTop_zero.comp ht

theorem terminalClock_pos {x : ℝ} (hx : 0≤x) : 0<terminalClock x := by
  unfold terminalClock
  exact inv_pos.mpr (by linarith [k_gt hx])

theorem inverseClockK_terminalClock (x : ℝ) : inverseClockK (terminalClock x:ℂ)=(k x:ℂ) := by
  unfold inverseClockK terminalClock
  push_cast
  simp only [one_div,inv_inv]
  ring

theorem terminalClock_complex_tendsto :
    Tendsto (fun x => (terminalClock x:ℂ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def,Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto 0).comp terminalClock_tendsto

theorem sixthSourceCoefficient_flat_normalized_tendsto :
    Tendsto (fun x => (terminalClock x:ℂ)^10*eval (terminalBase x) sixthSourceCoefficient)
      atTop (𝓝 (-(8192/3)*189994*(12:ℂ)^18)) := by
  have hp := ((gradedSurplusSlice (1/3) 6).continuous.tendsto 0).comp terminalClock_complex_tendsto
  rw [gradedSurplusSlice_six_zero] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  have hh : (terminalClock x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (terminalClock_pos hx).ne'
  dsimp only [Function.comp_apply]
  rw [gradedSurplusSlice_six_source _ _ hh,inverseClockK_terminalClock]
  rw [terminalBase,sixthSourceCoefficient_flat]

theorem sixthSourceCoefficient_actual_normalized_tendsto :
    Tendsto (fun x => (terminalClock x:ℂ)^10*eval (actualSquarePoint x) sixthSourceCoefficient)
      atTop (𝓝 (-(8192/3)*189994*(12:ℂ)^18)) := by
  have hd : Tendsto (fun x => eval (actualSquarePoint x) sixthSourceCoefficient-
      eval (terminalBase x) sixthSourceCoefficient) atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul] using actual_terminal_polynomial_flat sixthSourceCoefficient 0
  have hh : Tendsto (fun x => (terminalClock x:ℂ)^10) atTop (𝓝 0) := by
    simpa using terminalClock_complex_tendsto.pow 10
  have ha := (hh.mul hd).add sixthSourceCoefficient_flat_normalized_tendsto
  convert ha using 1
  · funext x
    ring
  · simp

theorem actualSourceSurplus_six_eventually_neg :
    ∀ᶠ x in atTop, ((actualSourceSurplus x).coeff 6).re<0 := by
  have hl := (Complex.continuous_re.tendsto (-(8192/3)*189994*(12:ℂ)^18)).comp
    sixthSourceCoefficient_actual_normalized_tendsto
  have hz : (-(8192/3)*189994*(12:ℂ)^18).re<(0:ℝ) := by norm_num
  have hn := hl.eventually_lt_const hz
  filter_upwards [hn,eventually_ge_atTop (0:ℝ)] with x hn hx
  dsimp only [Function.comp_apply] at hn
  rw [sixthSourceCoefficient_actual] at hn
  have hs : terminalClock x^10*((actualSourceSurplus x).coeff 6).re<0 := by
    simpa only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] using hn
  have hp : 0<terminalClock x^10 := pow_pos (terminalClock_pos hx) _
  by_contra hq
  exact (not_lt_of_ge (mul_nonneg hp.le (le_of_not_gt hq))) hs

theorem actualSourceSurplus_no_nonnegative_representation :
    ∀ᶠ x in atTop, ¬∃ Q : Polynomial ℝ, (∀ n, 0≤Q.coeff n) ∧
      Q.map Complex.ofRealHom=actualSourceSurplus x := by
  filter_upwards [actualSourceSurplus_six_eventually_neg] with x hx
  rintro ⟨Q,hQ,he⟩
  rw [←he,Polynomial.coeff_map,Complex.ofRealHom_eq_coe,Complex.ofReal_re] at hx
  exact (not_lt_of_ge (hQ 6)) hx

-- The eighth-to-seventh absorption used by the ordinary-coefficient proposal
-- leaves the obstructing sixth coefficient unchanged, for every chosen mass.
def absorbEighth {R : Type*} [CommRing R] (P : Polynomial R) (M : R) : Polynomial R :=
  P-Polynomial.C (P.coeff 8)*Polynomial.X^8+
    Polynomial.C (P.coeff 8*M)*Polynomial.X^7

theorem absorbEighth_coeff_six {R : Type*} [CommRing R] (P : Polynomial R) (M : R) :
    (absorbEighth P M).coeff 6=P.coeff 6 := by
  simp only [absorbEighth,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_C_mul_X_pow]
  norm_num

theorem actualAbsorbedSurplus_six_eventually_neg :
    ∀ᶠ x in atTop, ∀ M : ℂ, ((absorbEighth (actualSourceSurplus x) M).coeff 6).re<0 := by
  filter_upwards [actualSourceSurplus_six_eventually_neg] with x hx
  intro M
  simpa only [absorbEighth_coeff_six] using hx

theorem actualAbsorbedSurplus_no_nonnegative_representation :
    ∀ᶠ x in atTop, ∀ M : ℂ, ¬∃ Q : Polynomial ℝ, (∀ n, 0≤Q.coeff n) ∧
      Q.map Complex.ofRealHom=absorbEighth (actualSourceSurplus x) M := by
  filter_upwards [actualAbsorbedSurplus_six_eventually_neg] with x hx
  intro M
  rintro ⟨Q,hQ,he⟩
  have hn := hx M
  rw [←he,Polynomial.coeff_map,Complex.ofRealHom_eq_coe,Complex.ofReal_re] at hn
  exact (not_lt_of_ge (hQ 6)) hn


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
