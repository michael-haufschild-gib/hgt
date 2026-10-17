import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarContinuousFactorialLift

/-! A compact continuous factorial producer for the actual signed prime–polar measure.
The right collars preserve all integer-grid values and contribute an explicit harmonic correction. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

def factorialCollar (N : ℕ) : ℝ := 1/(4*(N : ℝ))

def smoothFactorialBiNull (N : ℕ) (x : ℝ) : ℝ :=
  (smoothFactorialLift (factorialCollar N) (4*N) x -
    4*smoothFactorialLift (factorialCollar N) (2*N) x +
    4*smoothFactorialLift (factorialCollar N) N x)/Real.sqrt N

theorem factorialCollar_pos {N : ℕ} (hN : 1 ≤ N) : 0 < factorialCollar N := by
  unfold factorialCollar
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

theorem factorialCollar_mul_le_one {N K : ℕ} (hN : 1 ≤ N) (hK : K ≤ 4*N) :
    factorialCollar N*(K : ℝ) ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (K : ℝ) ≤ 4*(N : ℝ) := by exact_mod_cast hK
  unfold factorialCollar
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 4*(N : ℝ))).2
  simpa using hk

theorem continuous_smoothFactorialBiNull (N : ℕ) : Continuous (smoothFactorialBiNull N) :=
  (((continuous_smoothFactorialLift _ _).sub
    (continuous_const.mul (continuous_smoothFactorialLift _ _))).add
    (continuous_const.mul (continuous_smoothFactorialLift _ _))).div_const _

theorem smoothFactorialBiNull_at_log {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    smoothFactorialBiNull N (Real.log n) = factorialBiNull N (Real.log n) := by
  unfold smoothFactorialBiNull factorialBiNull
  rw [smoothFactorialLift_at_log (factorialCollar_pos hN)
      (factorialCollar_mul_le_one hN (by omega : 4*N ≤ 4*N)) hn,
    smoothFactorialLift_at_log (factorialCollar_pos hN)
      (factorialCollar_mul_le_one hN (by omega : 2*N ≤ 4*N)) hn,
    smoothFactorialLift_at_log (factorialCollar_pos hN)
      (factorialCollar_mul_le_one hN (by omega : N ≤ 4*N)) hn]

theorem smoothFactorialBiNull_of_nonpos {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : x ≤ 0) :
    smoothFactorialBiNull N x = 0 := by
  unfold smoothFactorialBiNull
  rw [smoothFactorialLift_of_nonpos (factorialCollar_pos hN) hx,
    smoothFactorialLift_of_nonpos (factorialCollar_pos hN) hx,
    smoothFactorialLift_of_nonpos (factorialCollar_pos hN) hx]
  push_cast
  ring

theorem smoothFactorialBiNull_tail {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : Real.log (4*(N : ℝ)+1) ≤ x) : smoothFactorialBiNull N x = 0 := by
  have he := Real.exp_le_exp.mpr hx
  rw [Real.exp_log (by positivity : 0 < 4*(N : ℝ)+1)] at he
  have hz (K : ℕ) (hk0 : 1 ≤ K) (hk : K ≤ 4*N) :
      smoothFactorialLift (factorialCollar N) K x = 0 := by
    apply smoothFactorialLift_eq_zero (factorialCollar_pos hN) hk0
    have hb := factorialCollar_mul_le_one hN hk
    have hk' : (K : ℝ) ≤ 4*(N : ℝ) := by exact_mod_cast hk
    nlinarith
  simp [smoothFactorialBiNull, hz (4*N) (by omega) (by omega),
    hz (2*N) (by omega) (by omega), hz N hN (by omega)]

theorem hasCompactSupport_smoothFactorialBiNull {N : ℕ} (hN : 1 ≤ N) :
    HasCompactSupport (smoothFactorialBiNull N) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc 0 (Real.log (4*(N : ℝ)+1))) isCompact_Icc
  intro x hx
  constructor
  · by_contra! hn
    exact hx (smoothFactorialBiNull_of_nonpos hN hn.le)
  · by_contra! hn
    exact hx (smoothFactorialBiNull_tail hN hn.le)

/-- A literal compact continuous test, indexed only by a natural number. -/
def continuousFactorialProducer (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨smoothFactorialBiNull (n+1), continuous_smoothFactorialBiNull (n+1)⟩,
    hasCompactSupport_smoothFactorialBiNull (by omega)⟩

theorem primeTerm_smoothFactorialBiNull {N : ℕ} (hN : 1 ≤ N) :
    primeTerm (smoothFactorialBiNull N) = primeTerm (factorialBiNull N) := by
  funext n
  unfold primeTerm
  split_ifs with hn
  · rw [smoothFactorialBiNull_at_log hN (by omega)]
  · rfl

theorem integrable_polar_smoothFactorialBiNull {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x => polarDensity x*smoothFactorialBiNull N x) :=
  (continuous_polarDensity.mul (continuous_smoothFactorialBiNull N)).integrable_of_hasCompactSupport
    ((hasCompactSupport_smoothFactorialBiNull hN).mul_left (f := polarDensity))

theorem smoothFactorialBiNull_admissible {N : ℕ} (hN : 1 ≤ N) :
    (Function.support (primeTerm (smoothFactorialBiNull N))).Finite ∧
      Summable (fun n => |primeTerm (smoothFactorialBiNull N) n|) ∧
      IntegrableOn (fun x => polarDensity x*smoothFactorialBiNull N x) (Ici 0) := by
  rw [primeTerm_smoothFactorialBiNull hN]
  exact ⟨(factorialBiNull_admissible N).1, (factorialBiNull_admissible N).2.1,
    (integrable_polar_smoothFactorialBiNull hN).integrableOn⟩

private theorem integral_polar_stencil (F : ℕ → ℝ → ℝ) (N : ℕ)
    (hi : ∀ K, IntegrableOn (fun x => polarDensity x*F K x) (Ici 0)) :
    (∫ x in Ici (0 : ℝ), polarDensity x*((F (4*N) x-4*F (2*N) x+4*F N x)/Real.sqrt N)) =
      ((∫ x in Ici (0 : ℝ), polarDensity x*F (4*N) x)-
        4*(∫ x in Ici (0 : ℝ), polarDensity x*F (2*N) x)+
        4*(∫ x in Ici (0 : ℝ), polarDensity x*F N x))/Real.sqrt N := by
  have hi2 : IntegrableOn (fun x => 4*(polarDensity x*F (2*N) x)) (Ici 0) :=
    (hi (2*N)).const_mul 4
  have hi1 : IntegrableOn (fun x => 4*(polarDensity x*F N x)) (Ici 0) :=
    (hi N).const_mul 4
  have hsub : IntegrableOn (fun x => polarDensity x*F (4*N) x-
      4*(polarDensity x*F (2*N) x)) (Ici 0) := (hi (4*N)).sub hi2
  have he : (fun x => polarDensity x*((F (4*N) x-4*F (2*N) x+4*F N x)/Real.sqrt N)) =
      fun x => (polarDensity x*F (4*N) x-4*(polarDensity x*F (2*N) x)+
        4*(polarDensity x*F N x))/Real.sqrt N := by funext x; ring
  rw [he, integral_div, integral_add hsub hi1, integral_sub (hi (4*N)) hi2,
    integral_const_mul, integral_const_mul]

theorem fullPairing_smoothFactorialBiNull_correction {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (smoothFactorialBiNull N) = fullPairing (factorialBiNull N)-
      (factorialCollar N/2*harmonicCorrection N)/Real.sqrt N := by
  unfold fullPairing
  rw [primeTerm_smoothFactorialBiNull hN]
  unfold smoothFactorialBiNull factorialBiNull
  rw [integral_polar_stencil _ N (integrableOn_polar_smoothFactorialLift (factorialCollar_pos hN)),
    integral_polar_stencil _ N (fun K => (factorialLift_admissible K).2.2)]
  rw [integral_polar_smoothFactorialLift (factorialCollar_pos hN),
    integral_polar_smoothFactorialLift (factorialCollar_pos hN),
    integral_polar_smoothFactorialLift (factorialCollar_pos hN)]
  unfold harmonicCorrection
  push_cast
  ring

theorem fullPairing_smoothFactorialBiNull_eq {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (smoothFactorialBiNull N) =
      (2*chebyshevBiNullProducer N-(1+1/(8*(N : ℝ)))*harmonicCorrection N)/Real.sqrt N := by
  rw [fullPairing_smoothFactorialBiNull_correction hN, fullPairing_factorialBiNull_eq hN]
  unfold factorialCollar
  ring

theorem abs_fullPairing_smoothFactorialBiNull_le {N : ℕ} (hN : 1 ≤ N) :
    |fullPairing (smoothFactorialBiNull N)| ≤
      (10*Real.log (4*(N : ℝ)+1)+3+1/(8*(N : ℝ)))/Real.sqrt N := by
  rw [fullPairing_smoothFactorialBiNull_eq hN, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := abs_chebyshevBiNullProducer_le hN
  obtain ⟨hc0,hc1⟩ := harmonicCorrection_bounds hN
  have hq : 0 ≤ 1+1/(8*(N : ℝ)) := by positivity
  calc
    _ ≤ |2*chebyshevBiNullProducer N|+|(1+1/(8*(N : ℝ)))*harmonicCorrection N| := abs_sub _ _
    _ = 2*|chebyshevBiNullProducer N|+(1+1/(8*(N : ℝ)))*harmonicCorrection N := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (mul_nonneg hq hc0)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc1 hq]


theorem continuousFactorialProducer_zero (n : ℕ) : continuousFactorialProducer n 0 = 0 :=
  smoothFactorialBiNull_of_nonpos (by omega) le_rfl

theorem continuousFactorialProducer_top (n : ℕ) :
    continuousFactorialProducer n (Real.log (4*((n+1 : ℕ) : ℝ))) = 2 := by
  have hg := smoothFactorialBiNull_at_log (N := n+1) (n := 4*(n+1)) (by omega) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hg
  change smoothFactorialBiNull (n+1) _ = _
  rw [hg, factorialBiNull_top (by omega)]

theorem continuousFactorialProducer_ne_autocorr (n : ℕ) (f : C_c(ℝ, ℝ)) :
    (continuousFactorialProducer n : ℝ → ℝ) ≠ RHTower.ArchimedeanAnomaly.autocorr f := by
  intro heq
  have hz := congrFun heq 0
  rw [continuousFactorialProducer_zero] at hz
  have ht := congrFun heq (Real.log (4*((n+1 : ℕ) : ℝ)))
  rw [continuousFactorialProducer_top] at ht
  have hc := autocorr_eq_zero_of_zero_eq_zero f.hasCompactSupport f.continuous hz.symm
    (Real.log (4*((n+1 : ℕ) : ℝ)))
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
