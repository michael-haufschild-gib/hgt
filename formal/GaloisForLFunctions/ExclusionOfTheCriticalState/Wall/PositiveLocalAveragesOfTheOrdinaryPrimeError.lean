import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.GammaAveragesOfTheOrdinaryPrimeError
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.SincWindowsOnTheLogarithmicAxis
import GaloisForLFunctions.RHTower.XiSliceSaddleQuantitativeBounds

/-!
# Positive localized averages of the ordinary-prime error

The Fourier representation of a sinc fourth power transfers uniform modulated
gamma bounds to positive windows with a bounded centred second moment.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private def phase (ξ t : ℝ) : ℂ := cexp ((ξ:ℂ)*I*(t:ℂ))

private theorem norm_phase (ξ t : ℝ) : ‖phase ξ t‖ = 1 := by
  rw [phase,Complex.norm_exp]
  simp [Complex.mul_re]

private theorem phase_sub (ξ t T : ℝ) : phase ξ (t-T) = phase ξ (-T)*phase ξ t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Fourier averaging over four bounded frequencies inserts the nonnegative window. -/
private theorem sincFourth_integral_bound {μ : Measure ℝ} [SFinite μ] {g : ℝ → ℂ}
    (hg : Integrable g μ) {δ A : ℝ} (hδ : 0 < δ)
    (hband : ∀ ξ : ℝ, |ξ| ≤ 4*δ → ‖∫ t, g t * phase ξ t ∂μ‖ ≤ A) (T : ℝ) :
    ‖∫ t, (Real.sinc (δ*(t-T)):ℂ)^4 * g t ∂μ‖ ≤ A := by
  let ν := sincFourthFrequency δ
  let f := fun ξ t : ℝ => phase ξ (t-T) * g t
  have hc : Continuous (fun p : ℝ × ℝ => phase p.1 (p.2-T)) := by unfold phase; fun_prop
  have hm : AEStronglyMeasurable (Function.uncurry f) (ν.prod μ) :=
    hc.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd
  have hi (ξ : ℝ) : Integrable (f ξ) μ := by
    have hcξ : Continuous (fun t : ℝ => phase ξ (t-T)) := by unfold phase; fun_prop
    apply hg.norm.mono' (hcξ.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    exact Eventually.of_forall fun t => by
      change ‖phase ξ (t-T) * g t‖ ≤ ‖g t‖
      rw [norm_mul,norm_phase,one_mul]
  have hn (ξ : ℝ) : (∫ t, ‖f ξ t‖ ∂μ) = ∫ t, ‖g t‖ ∂μ := by simp only [f,norm_mul,norm_phase,one_mul]
  have hprod : Integrable (Function.uncurry f) (ν.prod μ) :=
    (integrable_prod_iff hm).mpr ⟨Eventually.of_forall hi,by
      change Integrable (fun ξ => ∫ t, ‖f ξ t‖ ∂μ) ν
      simp only [hn]; exact integrable_const _⟩
  have hchar (u : ℝ) : (∫ ξ, phase ξ u ∂ν) = (Real.sinc (δ*u):ℂ)^4 := by
    rw [← charFun_sincFourthFrequency,charFun_apply_real]
    exact integral_congr_ae (Eventually.of_forall fun ξ => by
      simp only [phase,Complex.ofReal_mul,mul_comm,mul_left_comm,mul_assoc])
  have he : (∫ t, (Real.sinc (δ*(t-T)):ℂ)^4 * g t ∂μ) =
      ∫ ξ, phase ξ (-T)*(∫ t, g t*phase ξ t ∂μ) ∂ν := by
    calc _ = ∫ t, (∫ ξ, f ξ t ∂ν) ∂μ := by
           apply integral_congr_ae (Eventually.of_forall fun t => ?_)
           rw [← hchar,← integral_mul_const]
      _ = ∫ ξ, (∫ t, f ξ t ∂μ) ∂ν := (integral_integral_swap hprod).symm
      _ = _ := by
           apply integral_congr_ae (Eventually.of_forall fun ξ => ?_)
           rw [← integral_const_mul]
           apply integral_congr_ae (Eventually.of_forall fun t => ?_)
           rw [show f ξ t = phase ξ (t-T)*g t from rfl,phase_sub]
           ring
  rw [he]
  have bound : ∀ᵐ ξ ∂ν, ‖phase ξ (-T) * (∫ t, g t * phase ξ t ∂μ)‖ ≤ A := by
    filter_upwards [sincFourthFrequency_support hδ] with ξ hξ
    simpa only [norm_mul,norm_phase,one_mul] using hband ξ hξ
  simpa using norm_integral_le_of_norm_le_const bound

/-- Twice-centred physical prime error. The constants are the growing pole and
the signed contribution from the first proper prime power. -/
def centredOrdinaryPrimeError (F : ℝ → ℝ) (t : ℝ) : ℂ :=
  ordinaryPrimeWave F t - negativeHalfLineLaplace (cx F) (-(1/2))*cexp ((t:ℂ)/2) +
    negativeHalfLineLaplace (cx F) 0 / 2

/-- At every sufficiently late centre, a positive prime-error window of bounded
second moment has geometric signed cancellation. Its total mass is bounded below. -/
theorem ordinaryPrimeError_positive_local_windows {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ δ m M C R : ℝ, 0 < δ ∧ 0 < m ∧ 1 < R ∧ ∀ n : ℕ, 0 < n → ∀ T : ℝ,
      (n:ℝ) ≤ T → T ≤ n+1 →
      m ≤ (∫ t in Ioi (0:ℝ), localizedPrimeWindow δ n T t) ∧
      (∫ t in Ioi (0:ℝ), (t-T)^2 * localizedPrimeWindow δ n T t) ≤ M ∧
      ‖∫ t in Ioi (0:ℝ), (localizedPrimeWindow δ n T t:ℂ) * centredOrdinaryPrimeError F t‖ ≤
        C * Real.sqrt n / R^n := by
  obtain ⟨D,G,hd,hG,htrans⟩ := exists_regular_ordinaryPrimeError_datum hF
  obtain ⟨η,R,C,hη,hR,hband⟩ := gammaMoment_decay_on_band_of_regular_laplace (Lp.memLp D) hG htrans
  let δ := η/4
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  obtain ⟨m,M,hm,hwidth⟩ := localizedPrimeWindow_mass_and_width hδ
  refine ⟨δ,m,M,Real.exp 1 * max C 0,R,hδ,hm,hR,?_⟩
  intro n hn T hT hT'
  obtain ⟨hl,hu⟩ := hwidth n hn T hT hT'
  refine ⟨hl,hu,?_⟩
  let g := fun t : ℝ => ((t:ℂ)^n * cexp (-(t:ℂ)/4) * D t) / (n.factorial:ℂ)
  have hg : IntegrableOn g (Ioi (0:ℝ)) := (integrableOn_damped_gammaMoment (Lp.memLp D) n).div_const _
  have hmod (ξ : ℝ) (hξ : |ξ| ≤ 4*δ) : ‖∫ t in Ioi (0:ℝ), g t * phase ξ t‖ ≤ C/R^n := by
    have hξ' : |ξ| ≤ η := by dsimp only [δ] at hξ; linarith
    have hb := hband ξ hξ' n
    rw [← integral_div] at hb
    refine le_of_eq_of_le ?_ hb
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    unfold g phase
    ring
  have hb := sincFourth_integral_bound hg hδ hmod T
  let L : ℝ := (n.factorial:ℝ)*Real.exp n/(n:ℝ)^n
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hLle : L ≤ Real.exp 1 * Real.sqrt n := by
    have h := factorial_le_exp_one_mul_sqrt_mul_pow hn
    change (n.factorial:ℝ)*Real.exp n/(n:ℝ)^n ≤ _
    rw [div_le_iff₀ (pow_pos hn' n)]
    calc (n.factorial:ℝ)*Real.exp n ≤ (Real.exp 1 * Real.sqrt n * ((n:ℝ)/Real.exp 1)^n)*Real.exp n :=
           mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by rw [div_pow,← Real.exp_nat_mul]; simp only [mul_one]; field_simp
  have he : (∫ t in Ioi (0:ℝ), (localizedPrimeWindow δ n T t:ℂ) * centredOrdinaryPrimeError F t) =
      (L:ℂ) * (∫ t in Ioi (0:ℝ), (Real.sinc (δ*(t-T)):ℂ)^4*g t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hd] with t ht
    change D t = cexp (-(3/4)*(t:ℂ))*centredOrdinaryPrimeError F t at ht
    rw [localizedPrimeWindow_eq hn]
    simp only [g,L,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_exp,
      Complex.ofReal_sub,Complex.ofReal_natCast,ht]
    have hphase : cexp ((n:ℂ)-(t:ℂ)) = cexp (n:ℂ)*cexp (-(t:ℂ)/4)*cexp (-(3/4)*(t:ℂ)) := by
      rw [← Complex.exp_add,← Complex.exp_add]; congr 1; ring
    rw [hphase,div_pow]
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hfC : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp [hnC,hfC]
  rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hL]
  have hr : 0 < R^n := pow_pos (zero_lt_one.trans hR) _
  calc L * _ ≤ L * (max C 0/R^n) :=
         mul_le_mul_of_nonneg_left (hb.trans (div_le_div_of_nonneg_right (le_max_left _ _) hr.le)) hL
    _ ≤ (Real.exp 1 * Real.sqrt n) * (max C 0/R^n) :=
         mul_le_mul_of_nonneg_right hLle (div_nonneg (le_max_right _ _) hr.le)
    _ = _ := by ring

#print axioms ordinaryPrimeError_positive_local_windows

end GaloisForLFunctions.ExclusionOfTheCriticalState
