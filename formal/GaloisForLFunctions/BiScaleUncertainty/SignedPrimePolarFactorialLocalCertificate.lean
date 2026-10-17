import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialLocalEnergy
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarLocalizedPacket

/-! Numeric-index-only local transport certificate for the actual factorial sources. -/

open MeasureTheory Set
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

theorem factorialPacketSource_zero_left (n : ℕ) (b : Bool) {u : ℝ}
    (hu : u ≤ -2*sourceFactorialWidth (n+1)) : factorialPacketSource n b u = 0 := by
  have hd := sourceFactorialWidth_pos (by omega : 1 ≤ n+1)
  change factorialSourceScale n*factorialRampSource n u-
    ((if b then 1 else -1)*(factorialSourceScale n)⁻¹)*factorialReflectedTent n u = 0
  rw [factorialRampSource_zero_of_nonpos n (by linarith), factorialReflectedTent_zero_left n hu]
  ring

theorem factorialPacketSource_zero_right (n : ℕ) (b : Bool) {u : ℝ}
    (hu : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ u) : factorialPacketSource n b u = 0 := by
  have hL : 0 ≤ Real.log (4*((n+1 : ℕ) : ℝ)+1) := Real.log_nonneg (by
    have hn : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _
    linarith)
  change factorialSourceScale n*factorialRampSource n u-
    ((if b then 1 else -1)*(factorialSourceScale n)⁻¹)*factorialReflectedTent n u = 0
  rw [factorialRampSource_tail n hu, factorialReflectedTent_zero_right n (hL.trans hu)]
  ring

theorem factorialPacketSource_zero_of_not_mem (n : ℕ) (b : Bool) {u : ℝ}
    (hu : u ∉ factorialPacketWindow n) : factorialPacketSource n b u = 0 := by
  have hd := sourceFactorialWidth_pos (by omega : 1 ≤ n+1)
  by_cases hlo : u ≤ -2*sourceFactorialWidth (n+1)
  · exact factorialPacketSource_zero_left n b hlo
  · apply factorialPacketSource_zero_right n b
    by_contra! h
    exact hu ⟨by linarith, h.le⟩

theorem factorialPacketSource_packet_stable (n : ℕ) (b : Bool) (k : ℕ) {u : ℝ}
    (hu : u ∈ factorialPacketWindow n) :
    signedSource (factorialPacketSource n b) (10*(n+1)+k) u =
      signedSource (factorialPacketSource n b) (10*(n+1)) u := by
  apply signedSource_stable_of_right_support (factorialPacketSource n b)
    (fun x hx => factorialPacketSource_zero_right n b hx) (by omega)
  have h := factorial_packet_cutoff (by omega : 1 ≤ n+1) (by omega : 10*(n+1) ≤ 10*(n+1))
  linarith [hu.1]

theorem factorialPacketSource_local_energy_le_all_cutoffs (n : ℕ) (b : Bool) (k : ℕ) :
    (∫ u in factorialPacketWindow n,
      signedSource (factorialPacketSource n b) (10*(n+1)+k) u^2) ≤
        300000*Real.sqrt (n+1 : ℕ) := by
  have he : (∫ u in factorialPacketWindow n,
      signedSource (factorialPacketSource n b) (10*(n+1)+k) u^2) =
      ∫ u in factorialPacketWindow n,
        signedSource (factorialPacketSource n b) (10*(n+1)) u^2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    change signedSource (factorialPacketSource n b) (10*(n+1)+k) u^2 =
      signedSource (factorialPacketSource n b) (10*(n+1)) u^2
    rw [factorialPacketSource_packet_stable n b k hu]
  rw [he]
  exact factorialPacketSource_local_energy_le n b

theorem factorialPacketSource_pairing_sq_le (n : ℕ) (b : Bool) (k : ℕ) :
    pairing (10*(n+1)+k) (autocorr (factorialPacketSource n b)) ^ 2 ≤
      50000*autocorr (factorialPacketSource n b) 0 ^ 2 := by
  have h := pairing_sq_le_local_packet (factorialPacketSource n b) (factorialPacketSource n b)
    (10*(n+1)+k) (-3*sourceFactorialWidth (n+1)) (Real.log (4*((n+1 : ℕ) : ℝ)+1))
    (fun u hu => by rw [factorialPacketSource_zero_of_not_mem n b hu, zero_mul])
  rw [integral_sq_eq_autocorr_zero] at h
  change pairing (10*(n+1)+k) (autocorr (factorialPacketSource n b)) ^ 2 ≤
    autocorr (factorialPacketSource n b) 0 *
      (∫ u in factorialPacketWindow n, signedSource (factorialPacketSource n b) (10*(n+1)+k) u^2) at h
  have h0 := (factorialPacketSource_energy_bounds n b).1
  have h0n : 0 ≤ autocorr (factorialPacketSource n b) 0 := autocorr_zero_nonneg _
  have hbudget := mul_le_mul_of_nonneg_left (factorialPacketSource_local_energy_le_all_cutoffs n b k) h0n
  have hscale := mul_le_mul_of_nonneg_right h0 h0n
  nlinarith

def factorialPacketChord (n : ℕ) (b : Bool) (y : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => factorialPacketSource n b (u+(-y))-factorialPacketSource n b u,
    ((factorialPacketSource n b).continuous.comp (continuous_add_const (-y))).sub
      (factorialPacketSource n b).continuous⟩,
    (hasCompactSupport_comp_add (factorialPacketSource n b).hasCompactSupport (-y)).sub
      (factorialPacketSource n b).hasCompactSupport⟩

theorem factorialPacketChord_energy (n : ℕ) (b : Bool) (y : ℝ) :
    (∫ u, factorialPacketChord n b y u^2) =
      2*(autocorr (factorialPacketSource n b) 0-autocorr (factorialPacketSource n b) y) := by
  change (∫ u, (factorialPacketSource n b (u+(-y))-factorialPacketSource n b u)^2) = _
  simpa only [add_zero, sub_zero, autocorr_neg] using
    integral_shift_sub_shift_sq (factorialPacketSource n b).hasCompactSupport
      (factorialPacketSource n b).continuous (-y) 0

theorem factorialPacketChord_mixed (n : ℕ) (b : Bool) (y t : ℝ) :
    (∫ u, factorialPacketChord n b y u*factorialPacketSource n b (u+t)) =
      autocorr (factorialPacketSource n b) (t+y)-autocorr (factorialPacketSource n b) t := by
  let f := factorialPacketSource n b
  have hi1 : Integrable (fun u => f (u+(-y))*f (u+t)) :=
    ((f.continuous.comp (continuous_add_const (-y))).mul
      (f.continuous.comp (continuous_add_const t))).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_add f.hasCompactSupport (-y)).mul_right
  have hi2 : Integrable (fun u => f u*f (u+t)) :=
    integrable_mul_shift (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport t
  change (∫ u, (f (u+(-y))-f u)*f (u+t)) = _
  simp_rw [sub_mul]
  rw [integral_sub hi1 hi2]
  congr 1
  change (∫ u, f (u+(-y))*f (u+t)) = ∫ u, f u*f (u+(t+y))
  calc
    _ = ∫ u, f (u+(-y))*f (u+(-y)+(t+y)) := by
      congr 1 with u
      rw [show u+(-y)+(t+y) = u+t by ring]
    _ = _ := integral_add_right_eq_self (μ := volume) (fun u => f u*f (u+(t+y))) (-y)

theorem factorialPacketSource_increment_sq_le (n : ℕ) (b : Bool) (k : ℕ) {y : ℝ}
    (hy : y ∈ Icc (-sourceFactorialWidth (n+1)) (sourceFactorialWidth (n+1))) :
    pairing (10*(n+1)+k) (fun t => autocorr (factorialPacketSource n b) (t+y)-
      autocorr (factorialPacketSource n b) t) ^ 2 ≤
        600000*Real.sqrt (n+1 : ℕ) *
          (autocorr (factorialPacketSource n b) 0-autocorr (factorialPacketSource n b) y) := by
  have hd := sourceFactorialWidth_pos (by omega : 1 ≤ n+1)
  have hout (u : ℝ) (hu : u ∉ factorialPacketWindow n) :
      factorialPacketChord n b y u*signedSource (factorialPacketSource n b) (10*(n+1)+k) u = 0 := by
    by_cases hright : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ u
    · rw [signedSource_zero_of_right_support (factorialPacketSource n b) (10*(n+1)+k)
        (fun x hx => factorialPacketSource_zero_right n b hx) hright, mul_zero]
    · have hleft : u < -3*sourceFactorialWidth (n+1) := by
        by_contra! h
        exact hu ⟨h, by linarith⟩
      have hq : factorialPacketChord n b y u = 0 := by
        change factorialPacketSource n b (u+(-y))-factorialPacketSource n b u = 0
        rw [factorialPacketSource_zero_left n b (by linarith [hy.1]),
          factorialPacketSource_zero_left n b (by linarith), sub_self]
      rw [hq, zero_mul]
  have h := pairing_sq_le_local_packet (factorialPacketChord n b y) (factorialPacketSource n b)
    (10*(n+1)+k) (-3*sourceFactorialWidth (n+1)) (Real.log (4*((n+1 : ℕ) : ℝ)+1)) hout
  simp_rw [factorialPacketChord_mixed] at h
  have hq0 : 0 ≤ ∫ u, factorialPacketChord n b y u^2 := integral_nonneg fun u => sq_nonneg _
  have hb := mul_le_mul_of_nonneg_left (factorialPacketSource_local_energy_le_all_cutoffs n b k) hq0
  rw [factorialPacketChord_energy] at h hb
  exact h.trans (hb.trans_eq (by ring))

/-- An explicit local packet budget and transport law for both reflected source signs. -/
theorem factorialLocalPacket_certificate (n : ℕ) :
    ∀ b : Bool,
      (6*Real.sqrt (n+1 : ℕ) ≤ autocorr (factorialPacketSource n b) 0 ∧
        autocorr (factorialPacketSource n b) 0 ≤ 46*Real.sqrt (n+1 : ℕ)) ∧
      ∀ k : ℕ,
        (∫ u in factorialPacketWindow n,
          signedSource (factorialPacketSource n b) (10*(n+1)+k) u^2) ≤ 300000*Real.sqrt (n+1 : ℕ) ∧
        pairing (10*(n+1)+k) (autocorr (factorialPacketSource n b))^2 ≤
          50000*autocorr (factorialPacketSource n b) 0^2 ∧
        ∀ y ∈ Icc (-sourceFactorialWidth (n+1)) (sourceFactorialWidth (n+1)),
          pairing (10*(n+1)+k) (fun t => autocorr (factorialPacketSource n b) (t+y)-
            autocorr (factorialPacketSource n b) t)^2 ≤ 600000*Real.sqrt (n+1 : ℕ)*
              (autocorr (factorialPacketSource n b) 0-autocorr (factorialPacketSource n b) y) := by
  intro b
  refine ⟨factorialPacketSource_energy_bounds n b, fun k => ?_⟩
  exact ⟨factorialPacketSource_local_energy_le_all_cutoffs n b k,
    factorialPacketSource_pairing_sq_le n b k,
    fun _ hy => factorialPacketSource_increment_sq_le n b k hy⟩

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
