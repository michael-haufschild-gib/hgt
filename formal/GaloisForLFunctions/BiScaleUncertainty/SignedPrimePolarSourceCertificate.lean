import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceEnergy
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalEnergy
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalPairing

open MeasureTheory Set
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

theorem continuous_factorialSourceContrast (n : ℕ) : Continuous (factorialSourceContrast n) := by
  have he : factorialSourceContrast n = fun x => sourceFactorialCausal (n+1) x+sourceFactorialCausal (n+1) (-x) :=
    funext (factorialSourceContrast_eq n)
  rw [he]
  exact (continuous_sourceFactorialCausal _).add ((continuous_sourceFactorialCausal _).comp continuous_neg)

theorem hasCompactSupport_factorialSourceContrast (n : ℕ) : HasCompactSupport (factorialSourceContrast n) := by
  have he : factorialSourceContrast n = fun x => sourceFactorialCausal (n+1) x+sourceFactorialCausal (n+1) (-x) :=
    funext (factorialSourceContrast_eq n)
  rw [he]
  exact (hasCompactSupport_sourceFactorialCausal (by omega : 1 ≤ n+1)).add
    ((hasCompactSupport_sourceFactorialCausal (by omega : 1 ≤ n+1)).comp_homeomorph (Homeomorph.neg ℝ))

def factorialSourceProducer (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨factorialSourceContrast n, continuous_factorialSourceContrast n⟩,
    hasCompactSupport_factorialSourceContrast n⟩

theorem factorialSourceContrast_at_log (n : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    factorialSourceContrast n (Real.log m) = factorialBiNull (n+1) (Real.log m) := by
  rw [factorialSourceContrast_eq_of_nonneg n (Real.log_nonneg (by exact_mod_cast hm)),
    sourceFactorialCausal_at_log (by omega) hm]

theorem primeTerm_factorialSourceContrast (n : ℕ) :
    primeTerm (factorialSourceContrast n) = primeTerm (sourceFactorialCausal (n+1)) := by
  funext m
  unfold primeTerm
  split_ifs with hm
  · rw [factorialSourceContrast_eq_of_nonneg n (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega)))]
  · rfl

theorem fullPairing_factorialSourceContrast (n : ℕ) :
    fullPairing (factorialSourceContrast n) = fullPairing (sourceFactorialCausal (n+1)) := by
  unfold fullPairing
  rw [primeTerm_factorialSourceContrast]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [factorialSourceContrast_eq_of_nonneg n hx]

theorem factorialSourceContrast_admissible (n : ℕ) :
    (Function.support (primeTerm (factorialSourceContrast n))).Finite ∧
      Summable (fun m => |primeTerm (factorialSourceContrast n) m|) ∧
      IntegrableOn (fun x => polarDensity x*factorialSourceContrast n x) (Ici 0) := by
  rw [primeTerm_factorialSourceContrast]
  refine ⟨(sourceFactorialCausal_admissible (by omega : 1 ≤ n+1)).1,
    (sourceFactorialCausal_admissible (by omega : 1 ≤ n+1)).2.1, ?_⟩
  exact ((continuous_polarDensity.mul (continuous_factorialSourceContrast n)).integrable_of_hasCompactSupport
    ((hasCompactSupport_factorialSourceContrast n).mul_left (f := polarDensity))).integrableOn

theorem integral_factorialSourceContrast_sq (n : ℕ) :
    (∫ x : ℝ, (factorialSourceContrast n x)^2) =
      2*(∫ x : ℝ, (sourceFactorialCausal (n+1) x)^2) := by
  have hp (x : ℝ) : (factorialSourceContrast n x)^2 =
      (sourceFactorialCausal (n+1) x)^2+(sourceFactorialCausal (n+1) (-x))^2 := by
    rw [factorialSourceContrast_eq]
    by_cases hx : x ≤ 0
    · rw [sourceFactorialCausal_zero_of_nonpos (by omega : 1 ≤ n+1) hx]
      ring
    · rw [sourceFactorialCausal_zero_of_nonpos (by omega : 1 ≤ n+1) (show -x ≤ 0 by linarith)]
      ring
  have hir : Integrable (fun x => (sourceFactorialCausal (n+1) (-x))^2) := by
    have hcont : Continuous (fun x : ℝ => sourceFactorialCausal (n+1) (-x)) :=
      (continuous_sourceFactorialCausal (n+1)).comp continuous_neg
    apply (hcont.pow 2).integrable_of_hasCompactSupport
    have hc : HasCompactSupport (fun x : ℝ => sourceFactorialCausal (n+1) (-x)) :=
      (hasCompactSupport_sourceFactorialCausal (by omega : 1 ≤ n+1)).comp_homeomorph (Homeomorph.neg ℝ)
    simpa only [pow_two] using hc.mul_left (f := fun x => sourceFactorialCausal (n+1) (-x))
  simp_rw [hp]
  rw [integral_add (integrable_sourceFactorialCausal_sq (by omega : 1 ≤ n+1)) hir,
    integral_neg_eq_self (fun x => (sourceFactorialCausal (n+1) x)^2)]
  ring

theorem factorialSourceContrast_energy_bounds (n : ℕ) :
    2 ≤ (∫ x : ℝ, (factorialSourceContrast n x)^2) ∧
      (∫ x : ℝ, (factorialSourceContrast n x)^2) ≤ 32 := by
  rw [integral_factorialSourceContrast_sq]
  have hl := one_le_integral_sourceFactorialCausal_sq (by omega : 1 ≤ n+1)
  have hu := integral_sourceFactorialCausal_sq_le (by omega : 1 ≤ n+1)
  constructor <;> linarith

/-- Explicit genuine sources realize the factorial grid producer with an unconditional
prime–polar pairing bound, nonvanishing contrast size, and a quantified square-root source cost. -/
theorem factorialSourceProducer_certificate (n : ℕ) :
    (∀ x : ℝ, factorialSourceProducer n x =
      (autocorr (factorialSourcePlus n) x-autocorr (factorialSourceMinus n) x)/2) ∧
    autocorr (factorialSourcePlus n) 0 = autocorr (factorialSourceMinus n) 0 ∧
    6*Real.sqrt (n+1 : ℕ) ≤ autocorr (factorialSourcePlus n) 0 ∧
    autocorr (factorialSourcePlus n) 0 ≤ 46*Real.sqrt (n+1 : ℕ) ∧
    (∀ m : ℕ, 1 ≤ m → factorialSourceProducer n (Real.log m) = factorialBiNull (n+1) (Real.log m)) ∧
    fullPairing (factorialSourceProducer n) =
      (2*chebyshevBiNullProducer (n+1)-sourceFactorialCoefficient (n+1)*harmonicCorrection (n+1))/Real.sqrt (n+1 : ℕ) ∧
    |fullPairing (factorialSourceProducer n)| ≤
      (10*Real.log (4*((n+1 : ℕ) : ℝ)+1)+3+1/(4*((n+1 : ℕ) : ℝ)))/Real.sqrt (n+1 : ℕ) ∧
    (Function.support (primeTerm (factorialSourceProducer n))).Finite ∧
    Summable (fun m => |primeTerm (factorialSourceProducer n) m|) ∧
    IntegrableOn (fun x => polarDensity x*factorialSourceProducer n x) (Ici 0) ∧
    2 ≤ (∫ x : ℝ, (factorialSourceProducer n x)^2) ∧
    (∫ x : ℝ, (factorialSourceProducer n x)^2) ≤ 32 := by
  obtain ⟨he,hl,hu⟩ := factorialSource_energy_certificate n
  obtain ⟨hd1,hd2,hd3⟩ := factorialSourceContrast_admissible n
  obtain ⟨hn1,hn2⟩ := factorialSourceContrast_energy_bounds n
  refine ⟨fun _ => rfl, he, hl, hu, fun m hm => factorialSourceContrast_at_log n hm, ?_, ?_, hd1, hd2, hd3, hn1, hn2⟩
  · change fullPairing (factorialSourceContrast n) = _
    rw [fullPairing_factorialSourceContrast]
    exact fullPairing_sourceFactorialCausal_eq (by omega)
  · change |fullPairing (factorialSourceContrast n)| ≤ _
    rw [fullPairing_factorialSourceContrast]
    exact abs_fullPairing_sourceFactorialCausal_le (by omega)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
