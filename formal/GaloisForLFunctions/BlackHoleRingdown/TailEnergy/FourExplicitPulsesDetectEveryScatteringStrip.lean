import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.TheMomentPulsesOfAFlatWindow
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.ASingleCompactPulseDetectsEveryStrip
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Four explicit compact pulses detect every scattering strip

The weighted derivative of tⁿ(1−t²)²h(t), for the flat window h, gives
a four-step recurrence for its Fourier moments at each complex frequency.
Four consecutive initial zeros would force every moment to vanish.
Consequently the derivatives of the first four moment pulses form a
fixed detector for every zero-free strip, including the RH endpoint.
-/

noncomputable section
open Complex Filter Set RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

private abbrev moment (n : ℕ) := momentPulse flatPulse n

private def threeMoments (j k l : ℕ) (a b c : ℂ) : CompactPulse :=
  ((CompactPulse.smul a (moment j)).add (CompactPulse.smul b (moment k))).add
    (CompactPulse.smul c (moment l))

private theorem triple_amplitude (j k l : ℕ) (a b c w : ℂ) :
    pulseAmplitude (threeMoments j k l a b c) w =
      a*pulseAmplitude (moment j) w+b*pulseAmplitude (moment k) w+
      c*pulseAmplitude (moment l) w := by
  simp only [threeMoments,pulseAmplitude_add,pulseAmplitude_smul]

private abbrev weighted (n : ℕ) := threeMoments n (n+2) (n+4) 1 (-2) 1
private abbrev row (n : ℕ) := threeMoments (n-1) (n+1) (n+3)
  n (-(2*(n:ℂ)+6)) ((n:ℂ)+4)

private theorem weighted_eq (n : ℕ) : (weighted n).toFun =
    fun t : ℝ => ((t^n*(1-t^2)^2*flatWindow t:ℝ):ℂ) := by
  funext t
  change 1*((t:ℂ)^n*(flatWindow t:ℂ))+(-2)*((t:ℂ)^(n+2)*(flatWindow t:ℂ))+
    1*((t:ℂ)^(n+4)*(flatWindow t:ℂ))=_
  push_cast
  rw [pow_add,pow_add]
  ring

private theorem weighted_hasDeriv (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => t^n*(1-t^2)^2*flatWindow t)
      ((n:ℝ)*t^(n-1)*flatWindow t-(2*(n:ℝ)+6)*t^(n+1)*flatWindow t+
        ((n:ℝ)+4)*t^(n+3)*flatWindow t) t := by
  have hwin := (flat_window_smooth.differentiable (by simp) t).hasDerivAt
  have h := ((((hasDerivAt_id t).pow n).mul
    (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 2)).mul hwin)
  apply h.congr_deriv
  dsimp only [id_eq]
  cases n with
  | zero =>
    norm_num only [Nat.cast_zero,zero_mul,zero_add,zero_pow,zero_ne_one,Nat.zero_sub,
      Nat.reduceAdd,Nat.reduceSub,pow_zero,pow_one,mul_one,one_mul,sub_zero]
    linear_combination flat_window_differential t
  | succ k =>
    simp only [Nat.cast_succ,Nat.succ_sub_one,Nat.reduceSub,pow_succ,pow_one,mul_one]
    linear_combination (t^k*t)*flat_window_differential t

private theorem weighted_D (n : ℕ) : (weighted n).D.toFun=(row n).toFun := by
  funext t
  change deriv (weighted n).toFun t=_
  rw [weighted_eq,(weighted_hasDeriv n t).ofReal_comp.deriv]
  change _=(n:ℂ)*((t:ℂ)^(n-1)*(flatWindow t:ℂ))+
    (-(2*(n:ℂ)+6))*((t:ℂ)^(n+1)*(flatWindow t:ℂ))+
    ((n:ℂ)+4)*((t:ℂ)^(n+3)*(flatWindow t:ℂ))
  push_cast
  ring

/-- Exact recurrence of all moment amplitudes at every complex frequency,
including zero. It follows from one integration by parts. -/
theorem flat_pulse_moment_recurrence (n : ℕ) (w : ℂ) :
    let A := fun j => pulseAmplitude (momentPulse flatPulse j) w
    I*w*(A n-2*A (n+2)+A (n+4)) =
      (n:ℂ)*A (n-1)-(2*(n:ℂ)+6)*A (n+1)+((n:ℂ)+4)*A (n+3) := by
  dsimp only
  have h := (weighted n).amplitude_D w
  change pulseAmplitude (weighted n).D.toFun w=I*w*pulseAmplitude (weighted n) w at h
  rw [weighted_D] at h
  change pulseAmplitude (row n) w=I*w*pulseAmplitude (weighted n) w at h
  simp only [row,weighted,triple_amplitude,one_mul,neg_mul] at h
  linear_combination -h

/-- One of the first four moment amplitudes is nonzero at each complex
frequency. The pulse list is independent of the frequency. -/
theorem four_flat_moments_have_no_common_zero (w : ℂ) :
    ∃ j : ℕ, j<4 ∧ pulseAmplitude (momentPulse flatPulse j) w≠0 := by
  by_contra! hblind
  let A (n : ℕ) := pulseAmplitude (momentPulse flatPulse n) w
  have hz (n : ℕ) : A n=0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n<4
      · exact hblind n hn
      obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+4 := ⟨n-4,by omega⟩
      by_cases hw : w=0
      · have h := flat_pulse_moment_recurrence (k+1) w
        change I*w*(A (k+1)-2*A (k+1+2)+A (k+1+4)) = _ at h
        change I*w*(A (k+1)-2*A (k+1+2)+A (k+1+4)) =
          ((k+1:ℕ):ℂ)*A (k+1-1)-(2*((k+1:ℕ):ℂ)+6)*A (k+1+1)+
          (((k+1:ℕ):ℂ)+4)*A (k+4) at h
        rw [hw,mul_zero,zero_mul,ih _ (by omega : k+1-1<k+4),mul_zero,
          ih _ (by omega : k+1+1<k+4),mul_zero,sub_zero,zero_add] at h
        exact (mul_eq_zero.mp h.symm).resolve_left (by
          exact_mod_cast (show k+1+4≠0 by omega))
      · have h := flat_pulse_moment_recurrence k w
        change I*w*(A k-2*A (k+2)+A (k+4)) =
          (k:ℂ)*A (k-1)-(2*(k:ℂ)+6)*A (k+1)+((k:ℂ)+4)*A (k+3) at h
        rw [ih k (by omega),ih (k+2) (by omega),ih (k-1) (by omega),
          ih (k+1) (by omega),ih (k+3) (by omega)] at h
        simp only [mul_zero,sub_zero,zero_add,add_zero] at h
        exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero I_ne_zero hw)
  obtain ⟨j,hj⟩ := moment_pulses_separate_frequencies flatPulse ⟨0,flat_pulse_zero_time⟩ w
  exact hj (hz j)

/-- The four specified derivative pulses test every strip with no
choice of a carrier frequency. -/
theorem four_flat_pulses_strip_iff {δ : ℝ} (hδ : 0<δ) (hq : δ≤1/4) :
    (∀ n : ℕ, n<4 → pulseDecayThrough (momentPulse flatPulse n).D δ) ↔
      ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ := by
  constructor
  · intro h ρ hz hρ
    by_contra! hb
    obtain ⟨j,hj,hn⟩ := four_flat_moments_have_no_common_zero (-I*((ρ-1)/2))
    exact hn (fast_derivative_hides_zeta_zero _ (h j hj) hz hρ hb)
  · intro h n _ σ hσ hσδ
    obtain ⟨C,hC⟩ := (zeroFreeStrip_tailEnergy_equivalences hδ hq).2.2.1.mp h
      (δ-σ) (sub_pos.mpr hσδ) (momentPulse flatPulse n).D
    exact ⟨C,fun T hT => by simpa only [sub_sub_cancel] using hC T hT⟩

/-- Total received tail energy of the four fixed transmissions. -/
def fourFlatPulseEnergy (T : ℝ) :=
  ∑ j : Fin 4, tailEnergy (momentPulse flatPulse j.val).D T

/-- A scalar sum of measured energies suffices. Each pulse has
nonnegative tail energy, so a large component cannot cancel. -/
theorem combined_flat_pulse_strip_iff {δ : ℝ} (hd : 0<δ) (hq : δ≤1/4) :
    (∀ σ : ℝ, 0<σ → σ<δ → ∃ C : ℝ, ∀ T : ℝ, 0≤T →
      fourFlatPulseEnergy T ≤ C*Real.exp (-2*σ*T)) ↔
    ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ := by
  rw [←four_flat_pulses_strip_iff hd hq]
  constructor
  · intro h n hn σ hs hσδ
    obtain ⟨C,hC⟩ := h σ hs hσδ
    refine ⟨C,fun T ht => ?_⟩
    have hj := Finset.single_le_sum (f:=fun j : Fin 4 => tailEnergy (momentPulse flatPulse j.val).D T)
      (fun j _ => tailEnergy_nonneg _ _) (Finset.mem_univ (⟨n,hn⟩:Fin 4))
    exact hj.trans (hC T ht)
  · intro h σ hs hσδ
    choose C hC using fun j : Fin 4 => h j.val j.isLt σ hs hσδ
    refine ⟨∑ j, C j,fun T ht => ?_⟩
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hC j T ht

/-- At the quarter-rate endpoint the same four explicit transmissions
give a scalar tail-energy criterion for RH. -/
theorem rh_iff_combined_flat_pulse_energy :
    RiemannHypothesis ↔ ∀ σ : ℝ, 0<σ → σ<1/4 → ∃ C : ℝ, ∀ T : ℝ, 0≤T →
      fourFlatPulseEnergy T ≤ C*Real.exp (-2*σ*T) := by
  have hs := zeroFreeStrip_tailEnergy_equivalences (δ:=1/4) (by norm_num) le_rfl
  exact ((combined_flat_pulse_strip_iff (by norm_num) le_rfl).trans
    (hs.1.trans RingdownRate.riemannHypothesis_iff_pulse_ringdown.symm)).symm

#print axioms flat_pulse_moment_recurrence
#print axioms four_flat_moments_have_no_common_zero
#print axioms four_flat_pulses_strip_iff
#print axioms rh_iff_combined_flat_pulse_energy
end GaloisForLFunctions.BlackHoleRingdown
