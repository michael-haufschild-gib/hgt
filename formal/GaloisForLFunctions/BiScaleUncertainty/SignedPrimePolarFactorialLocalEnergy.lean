import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialPolarPacket
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialPacketEnvelope
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarReflectedTentPacket
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarScaledCollar
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceEnergy

/-! Explicit localized energy of the reflected balanced factorial sources. -/

open MeasureTheory Set
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
noncomputable section
set_option autoImplicit false

def factorialPacketWindow (n : ℕ) : Set ℝ :=
  Icc (-3*sourceFactorialWidth (n+1)) (Real.log (4*((n+1 : ℕ) : ℝ)+1))

theorem abs_signedSource_factorialRamp_le (n : ℕ) {u : ℝ}
    (hu : u ∈ factorialPacketWindow n) :
    |signedSource (factorialRampSource n) (10*(n+1)) u| ≤ 24*factorialPacketEnvelope (n+1) u := by
  have ha := abs_atomicSource_factorialRamp_le n hu.1 hu.2
  have hp := abs_polarSource_factorialRamp_le n hu.1 hu.2
  have ht := abs_sub_le (atomicSource (factorialRampSource n) (10*(n+1)) u) 0
    (polarSource (factorialRampSource n) (10*(n+1)) u)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  change |atomicSource (factorialRampSource n) (10*(n+1)) u-
    polarSource (factorialRampSource n) (10*(n+1)) u| ≤ _
  calc
    _ ≤ 19*Real.exp (u/2)/Real.sqrt (n+1 : ℕ)*(1+Real.log (13*((n+1 : ℕ) : ℝ))-u)+
        5*Real.exp (u/2)/Real.sqrt (n+1 : ℕ)*(1+Real.log (13*((n+1 : ℕ) : ℝ))-u) :=
      ht.trans (add_le_add ha hp)
    _ = _ := by unfold factorialPacketEnvelope; ring

theorem integral_signedSource_factorialRamp_sq_le (n : ℕ) :
    (∫ u in factorialPacketWindow n, signedSource (factorialRampSource n) (10*(n+1)) u ^ 2) ≤
      100000 := by
  have hc := (signedSource (factorialRampSource n) (10*(n+1))).continuous.pow 2
  have he := (continuous_factorialPacketEnvelope (n+1)).pow 2
  calc
    _ ≤ ∫ u in factorialPacketWindow n, 576*factorialPacketEnvelope (n+1) u^2 := by
      apply setIntegral_mono_on hc.integrableOn_Icc
        ((continuous_const.mul he).integrableOn_Icc) measurableSet_Icc
      intro u hu
      change signedSource (factorialRampSource n) (10*(n+1)) u^2 ≤
        576*factorialPacketEnvelope (n+1) u^2
      have h := abs_le.mp (abs_signedSource_factorialRamp_le n hu)
      have henv := factorialPacketEnvelope_nonneg (by omega : 1 ≤ n+1) hu.2
      nlinarith
    _ = 576*(∫ u in factorialPacketWindow n, factorialPacketEnvelope (n+1) u^2) :=
      integral_const_mul _ _
    _ ≤ 100000 := by
      have h := integral_factorialPacketEnvelope_sq_le (by omega : 1 ≤ n+1)
      change (∫ u in factorialPacketWindow n, factorialPacketEnvelope (n+1) u^2) ≤ 130 at h
      linarith

/-- False selects the reflected plus source; true selects the reflected minus source. -/
def factorialPacketSource (n : ℕ) (b : Bool) : C_c(ℝ, ℝ) :=
  factorialSourceScale n • factorialRampSource n -
    ((if b then 1 else -1)*(factorialSourceScale n)⁻¹) • factorialReflectedTent n

theorem factorialPacketSource_apply (n : ℕ) (b : Bool) (u : ℝ) :
    factorialPacketSource n b u =
      (if b then factorialSourceMinus n else factorialSourcePlus n) (-u) := by
  cases b <;>
    simp [factorialPacketSource, factorialSourceMinus, factorialSourcePlus,
      factorialSourceLeft, factorialSourceRight, factorialRampSource, factorialReflectedTent,
      smul_eq_mul]

theorem factorialPacketSource_autocorr (n : ℕ) (b : Bool) (x : ℝ) :
    autocorr (factorialPacketSource n b) x =
      autocorr (if b then factorialSourceMinus n else factorialSourcePlus n) x := by
  let f := if b then factorialSourceMinus n else factorialSourcePlus n
  calc
    _ = ∫ u, f (-u)*f (-u+(-x)) := by
      unfold autocorr
      apply integral_congr_ae
      filter_upwards [] with u
      rw [factorialPacketSource_apply, factorialPacketSource_apply]
      congr 1
      congr 1
      ring
    _ = ∫ u, f u*f (u+(-x)) := integral_neg_eq_self (fun u => f u*f (u+(-x))) volume
    _ = autocorr f x := autocorr_neg f x
    _ = _ := by cases b <;> rfl

theorem factorialPacketSource_energy_bounds (n : ℕ) (b : Bool) :
    6*Real.sqrt (n+1 : ℕ) ≤ autocorr (factorialPacketSource n b) 0 ∧
      autocorr (factorialPacketSource n b) 0 ≤ 46*Real.sqrt (n+1 : ℕ) := by
  rw [factorialPacketSource_autocorr]
  have h := factorialSource_energy_certificate n
  cases b
  · exact h.2
  · change 6*Real.sqrt (n+1 : ℕ) ≤ autocorr (factorialSourceMinus n) 0 ∧
      autocorr (factorialSourceMinus n) 0 ≤ 46*Real.sqrt (n+1 : ℕ)
    rw [← h.1]
    exact h.2

/-- The complete actual-source budget is independent of any discrepancy hypothesis. -/
theorem factorialPacketSource_local_energy_le (n : ℕ) (b : Bool) :
    (∫ u in factorialPacketWindow n,
      signedSource (factorialPacketSource n b) (10*(n+1)) u ^ 2) ≤
        300000*Real.sqrt (n+1 : ℕ) := by
  let r := Real.sqrt (n+1 : ℕ)
  let s := factorialSourceScale n
  let c : ℝ := (if b then 1 else -1)*(factorialSourceScale n)⁻¹
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hs := factorialSourceScale_sq n
  have hc : c^2 = 1/r := by
    dsimp [c, r]
    cases b <;> simp [inv_pow, factorialSourceScale_sq, one_div]
  have he (u : ℝ) : signedSource (factorialPacketSource n b) (10*(n+1)) u =
      s*signedSource (factorialRampSource n) (10*(n+1)) u-
        c*signedSource (factorialReflectedTent n) (10*(n+1)) u := by
    unfold factorialPacketSource
    rw [signedSource_sub_apply, signedSource_smul_apply, signedSource_smul_apply]
  have hiR : Continuous (fun u => signedSource (factorialRampSource n) (10*(n+1)) u^2) :=
    (signedSource (factorialRampSource n) (10*(n+1))).continuous.pow 2
  have hiH : Continuous (fun u => signedSource (factorialReflectedTent n) (10*(n+1)) u^2) :=
    (signedSource (factorialReflectedTent n) (10*(n+1))).continuous.pow 2
  have hiV : Continuous (fun u => signedSource (factorialPacketSource n b) (10*(n+1)) u^2) :=
    (signedSource (factorialPacketSource n b) (10*(n+1))).continuous.pow 2
  have hi1 : IntegrableOn (fun u => 2*s^2*signedSource (factorialRampSource n) (10*(n+1)) u^2)
      (factorialPacketWindow n) := (continuous_const.mul hiR).integrableOn_Icc
  have hi2 : IntegrableOn (fun u => 2*c^2*signedSource (factorialReflectedTent n) (10*(n+1)) u^2)
      (factorialPacketWindow n) := (continuous_const.mul hiH).integrableOn_Icc
  have h1 := integral_signedSource_factorialRamp_sq_le n
  have h2 := integral_signedSource_factorialReflectedTent_sq_le n (10*(n+1))
  have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hr1 : 1 ≤ r := by
    have hsq : r^2 = ((n+1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith
  have hrem : 2*(1/r)*(9/((n+1 : ℕ) : ℝ)) ≤ 18*r := by
    calc
      _ = 18/(r*((n+1 : ℕ) : ℝ)) := by ring
      _ ≤ 18 := (div_le_iff₀ (by positivity : 0 < r*((n+1 : ℕ) : ℝ))).2 (by nlinarith)
      _ ≤ _ := by linarith
  calc
    _ ≤ ∫ u in factorialPacketWindow n,
        2*s^2*signedSource (factorialRampSource n) (10*(n+1)) u^2+
        2*c^2*signedSource (factorialReflectedTent n) (10*(n+1)) u^2 := by
      apply setIntegral_mono_on hiV.integrableOn_Icc (hi1.add hi2) measurableSet_Icc
      intro u _
      change signedSource (factorialPacketSource n b) (10*(n+1)) u^2 ≤
        2*s^2*signedSource (factorialRampSource n) (10*(n+1)) u^2+
        2*c^2*signedSource (factorialReflectedTent n) (10*(n+1)) u^2
      rw [he]
      nlinarith [sq_nonneg (s*signedSource (factorialRampSource n) (10*(n+1)) u+
        c*signedSource (factorialReflectedTent n) (10*(n+1)) u)]
    _ = 2*r*(∫ u in factorialPacketWindow n,
          signedSource (factorialRampSource n) (10*(n+1)) u^2)+
        2*(1/r)*(∫ u in factorialPacketWindow n,
          signedSource (factorialReflectedTent n) (10*(n+1)) u^2) := by
      rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, hc]
      change 2*s^2*_+_ = _
      rw [show s^2 = r from hs]
    _ ≤ 2*r*100000+2*(1/r)*(9/((n+1 : ℕ) : ℝ)) := add_le_add
      (mul_le_mul_of_nonneg_left h1 (by positivity))
      (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ ≤ _ := by change _ ≤ 300000*r; nlinarith

theorem factorialPacketSource_local_energy_ratio_le (n : ℕ) (b : Bool) :
    (∫ u in factorialPacketWindow n,
      signedSource (factorialPacketSource n b) (10*(n+1)) u^2) /
        autocorr (factorialPacketSource n b) 0 ≤ 50000 := by
  have hr : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have h0 := (factorialPacketSource_energy_bounds n b).1
  have hpos : 0 < autocorr (factorialPacketSource n b) 0 := by linarith
  apply (div_le_iff₀ hpos).2
  nlinarith [factorialPacketSource_local_energy_le n b]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
