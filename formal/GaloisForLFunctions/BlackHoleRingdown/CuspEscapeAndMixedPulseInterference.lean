import GaloisForLFunctions.BlackHoleRingdown.TheEchoesOfAPulse
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownRateIsTheZeroFreeStrip
import GaloisForLFunctions.BlackHoleRingdown.TheMetricRingdown
import GaloisForLFunctions.BlackHoleRingdown.CausalIdentitiesCannotForceQuarterRingdown
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.HTGeometry.ConductorPlancherelPairing

/-!
# Cusp Escape, Mixed-Pulse Interference, and Five-Channel Modular Echoes

This module establishes the exact cusp-escape and mixed-pulse wave calculus on the modular surface:

1. **Mixed Pulses, Time Delays, Hecke Time-Propagation, and Mean-Zero Pulses**:
   Finite superpositions `mixedPulse idx c f`, delayed pulses `CompactPulse.delay d h`, Hecke-propagated
   pulses `heckeTimePulse p h`, and exact mean-zero pulses `meanZeroPulse h` and
   `balancedMeanZeroPulse δ b` (`meanCoefficient = 0`), with linearity of `pulseAmplitude`,
   `meanCoefficient`, `pulseEcho`, and `pulseReflected`.

2. **Five-Channel Arithmetic Decomposition of the Echo Train**:
   The cusp echo train `echoKernel τ = ∑' c, echoTerm c τ` splits disjointly into:
   - prompt bounce (`c = 1`, delay `0`, weight `1`),
   - primitive prime traversals (`c = p`, delay `2 log p`, weight `1 - 1/p`),
   - prime-square repeated traversals (`c = p²`, delay `4 log p`, weight `1 - 1/p`),
   - mixed two-prime traversals (`c = p q`, `p < q`, delay `2 log p + 2 log q`,
     weight `(1 - 1/p)(1 - 1/q)`),
   - higher composite traversals (`c ≥ 8`), which vanish identically on `τ ≤ 6 log 2`.

3. **Exact Unitary Plancherel Conservation, Cusp Escape Law, and Interference Expansion**:
   For every measurable unitary symbol `J : ℝ → ℂ` (`‖J ξ‖ = 1`), the reflected wavepacket
   `unitaryReflected J h` satisfies `∫ ‖unitaryReflected J h T‖² dT = ∫ ‖h S‖² dS`. Specializing to
   `pulseReflected` yields the exact cusp escape law past any finite cutoff `T₂ ≥ -S₀` and the exact
   Hermitian diagonal-plus-interference expansion for `mixedPulse idx c f`.

4. **Unconditional Escape Rate on Actual `ζ`**:
   Combining `riemannZeta_zero_mem_sub_quasiRH_strip` (`Θ ≤ 20999/24000`) with
   `RingdownRate.pulseField_decay_of_zeroFree` gives unconditional pointwise `O(e^{-σ T})` and
   unescaped tail `O(e^{-2σ T₂})` cusp escape for every compact mixed pulse at all
   `0 < σ < 3001/48000` (`> 1/16`).
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform Classical

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
  (riemannZeta_ne_zero_of_sub_seven_eighths_lt_re riemannZeta_zero_mem_sub_quasiRH_strip)

/-! ## 1. Mixed Pulses, Time Delays, Hecke Time-Propagation, and Mean-Zero Pulses -/

namespace CompactPulse

/-- The identically zero compact pulse. -/
def zero : CompactPulse where
  toFun := 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero

/-- Pointwise sum of two compact pulses. -/
def add (g h : CompactPulse) : CompactPulse where
  toFun S := g S + h S
  smooth := g.smooth.add h.smooth
  compact := g.compact.add h.compact

/-- Scalar multiple of a compact pulse. -/
def smul (c : ℂ) (h : CompactPulse) : CompactPulse where
  toFun S := c * h S
  smooth := contDiff_const.mul h.smooth
  compact := h.compact.mul_left (f := fun _ => c)

/-- Time-delayed compact pulse `(h.delay d) S = h (S - d)`. -/
def delay (d : ℝ) (h : CompactPulse) : CompactPulse where
  toFun S := h (S - d)
  smooth := h.smooth.comp (contDiff_id.sub contDiff_const)
  compact := by
    obtain ⟨S₀, _, hS₀⟩ := h.exists_support_bound
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(S₀ + |d|)) (b := S₀ + |d|)) fun S hS => ?_
    rw [Function.mem_support] at hS
    have hle : |S - d| ≤ S₀ := not_lt.mp fun hgt => hS (hS₀ (S - d) hgt)
    have habs : |S| ≤ S₀ + |d| := by
      calc |S| = |(S - d) + d| := by ring_nf
        _ ≤ |S - d| + |d| := abs_add_le _ _
        _ ≤ S₀ + |d| := by linarith
    exact abs_le.mp habs

@[simp] theorem zero_apply (S : ℝ) : (zero : CompactPulse) S = 0 := rfl
@[simp] theorem add_apply (g h : CompactPulse) (S : ℝ) : (g.add h) S = g S + h S := rfl
@[simp] theorem smul_apply (c : ℂ) (h : CompactPulse) (S : ℝ) : (smul c h) S = c * h S := rfl
@[simp] theorem delay_apply (d : ℝ) (h : CompactPulse) (S : ℝ) : (h.delay d) S = h (S - d) := rfl

theorem delay_eq_zero_of_support_bound {S₀ d : ℝ} (h : CompactPulse)
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {s : ℝ} (hs : S₀ + |d| < |s|) :
    (h.delay d) s = 0 := by
  change h (s - d) = 0
  refine hS₀ (s - d) ?_
  have h1 : |s| ≤ |s - d| + |d| := by
    calc |s| = |(s - d) + d| := by ring_nf
      _ ≤ |s - d| + |d| := abs_add_le _ _
  linarith

end CompactPulse

/-- Finite linear combination `∑ i ∈ idx, c i * f i S` of compact pulses, modeling a general mixed
pulse with arbitrary relative delays, phases, and profiles. -/
def mixedPulse {ι : Type*} (idx : Finset ι) (c : ι → ℂ) (f : ι → CompactPulse) : CompactPulse where
  toFun S := ∑ i ∈ idx, c i * f i S
  smooth := by
    induction idx using Finset.induction_on with
    | empty =>
      have heq : (fun S : ℝ => ∑ i ∈ (∅ : Finset ι), c i * f i S) = fun _ : ℝ => (0 : ℂ) := by
        funext S; simp
      rw [heq]; exact contDiff_const
    | insert a s ha ih =>
      have heq : (fun S : ℝ => ∑ i ∈ insert a s, c i * f i S) =
          fun S : ℝ => c a * f a S + ∑ i ∈ s, c i * f i S := by
        funext S; exact Finset.sum_insert ha
      rw [heq]
      exact (contDiff_const.mul (f a).smooth).add ih
  compact := by
    induction idx using Finset.induction_on with
    | empty =>
      have heq : (fun S : ℝ => ∑ i ∈ (∅ : Finset ι), c i * f i S) = (0 : ℝ → ℂ) := by
        funext S; simp
      rw [heq]
      exact HasCompactSupport.zero
    | insert a s ha ih =>
      have heq : (fun S : ℝ => ∑ i ∈ insert a s, c i * f i S) =
          fun S : ℝ => c a * f a S + ∑ i ∈ s, c i * f i S := by
        funext S; exact Finset.sum_insert ha
      rw [heq]
      exact ((f a).compact.mul_left (f := fun _ => c a)).add ih

@[simp] theorem mixedPulse_apply {ι : Type*} (idx : Finset ι) (c : ι → ℂ)
    (f : ι → CompactPulse) (S : ℝ) :
    mixedPulse idx c f S = ∑ i ∈ idx, c i * f i S := rfl

/-- Hecke time-propagated pulse `S ↦ h(S + log p) + h(S - log p)`. -/
def heckeTimePulse (p : ℕ) (h : CompactPulse) : CompactPulse :=
  (h.delay (-Real.log p)).add (h.delay (Real.log p))

@[simp] theorem heckeTimePulse_apply (p : ℕ) (h : CompactPulse) (S : ℝ) :
    heckeTimePulse p h S = h (S + Real.log p) + h (S - Real.log p) := by
  simp [heckeTimePulse, sub_neg_eq_add]

/-- Amplitude modulation under a time delay: delaying `h` by `d` multiplies `pulseAmplitude` by
`e^{-i w d}`. -/
theorem pulseAmplitude_delay (d : ℝ) (h : CompactPulse) (w : ℂ) :
    pulseAmplitude (h.delay d) w = Complex.exp (-(I * w * (d : ℂ))) * pulseAmplitude h w := by
  have hint_eq :
      (∫ S : ℝ, (h.delay d) S * Complex.exp (-(I * w * (S : ℂ)))) =
        Complex.exp (-(I * w * (d : ℂ))) *
          ∫ u : ℝ, h u * Complex.exp (-(I * w * (u : ℂ))) := by
    have hsub := integral_sub_right_eq_self (μ := volume)
      (fun u : ℝ => h u * Complex.exp (-(I * w * ((u + d : ℝ) : ℂ)))) d
    calc (∫ S : ℝ, (h.delay d) S * Complex.exp (-(I * w * (S : ℂ))))
        = ∫ S : ℝ, h (S - d) * Complex.exp (-(I * w * ((S - d + d : ℝ) : ℂ))) := by
            refine integral_congr_ae (Eventually.of_forall fun S => ?_)
            dsimp only
            rw [CompactPulse.delay_apply, sub_add_cancel]
      _ = ∫ u : ℝ, h u * Complex.exp (-(I * w * ((u + d : ℝ) : ℂ))) := hsub
      _ = ∫ u : ℝ, Complex.exp (-(I * w * (d : ℂ))) *
            (h u * Complex.exp (-(I * w * (u : ℂ)))) := by
            refine integral_congr_ae (Eventually.of_forall fun u => ?_)
            dsimp only
            have hexp : Complex.exp (-(I * w * ((u + d : ℝ) : ℂ))) =
                Complex.exp (-(I * w * (d : ℂ))) * Complex.exp (-(I * w * (u : ℂ))) := by
              rw [← Complex.exp_add]
              congr 1
              push_cast
              ring
            rw [hexp]
            ring
      _ = Complex.exp (-(I * w * (d : ℂ))) *
            ∫ u : ℝ, h u * Complex.exp (-(I * w * (u : ℂ))) :=
            integral_const_mul _ _
  rw [pulseAmplitude, pulseAmplitude, hint_eq]
  ring

theorem pulseAmplitude_add (g h : CompactPulse) (w : ℂ) :
    pulseAmplitude (g.add h) w = pulseAmplitude g w + pulseAmplitude h w := by
  rw [pulseAmplitude, pulseAmplitude, pulseAmplitude, ← mul_add,
    ← integral_add (g.integrable_mul_cexp w) (h.integrable_mul_cexp w)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun S => ?_)
  simp [add_mul]

theorem pulseAmplitude_smul (c : ℂ) (h : CompactPulse) (w : ℂ) :
    pulseAmplitude (CompactPulse.smul c h) w = c * pulseAmplitude h w := by
  rw [pulseAmplitude, pulseAmplitude, mul_left_comm, ← integral_const_mul c]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun S => ?_)
  simp [mul_assoc]

/-- Spectral amplitude of `heckeTimePulse p h`: multiplication by `2 cos(w log p)`. -/
theorem pulseAmplitude_heckeTimePulse (p : ℕ) (h : CompactPulse) (w : ℂ) :
    pulseAmplitude (heckeTimePulse p h) w =
      (Complex.exp (I * w * (Real.log p : ℂ)) + Complex.exp (-(I * w * (Real.log p : ℂ)))) *
        pulseAmplitude h w := by
  rw [heckeTimePulse, pulseAmplitude_add, pulseAmplitude_delay, pulseAmplitude_delay]
  have hneg : -(I * w * ((-Real.log p : ℝ) : ℂ)) = I * w * (Real.log p : ℂ) := by
    push_cast; ring
  rw [hneg, add_mul]

/-- Linearity of `pulseAmplitude` on a `mixedPulse`. -/
theorem pulseAmplitude_mixedPulse {ι : Type*} (idx : Finset ι) (c : ι → ℂ)
    (f : ι → CompactPulse) (w : ℂ) :
    pulseAmplitude (mixedPulse idx c f) w = ∑ i ∈ idx, c i * pulseAmplitude (f i) w := by
  rw [pulseAmplitude]
  have hpt : ∀ S : ℝ, mixedPulse idx c f S * Complex.exp (-(I * w * (S : ℂ))) =
      ∑ i ∈ idx, c i * (f i S * Complex.exp (-(I * w * (S : ℂ)))) := by
    intro S
    rw [mixedPulse_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum idx fun i _ => ((f i).integrable_mul_cexp w).const_mul (c i),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, pulseAmplitude]
  ring

/-- Linearity of `meanCoefficient` on a `mixedPulse`. -/
theorem meanCoefficient_mixedPulse {ι : Type*} (idx : Finset ι) (c : ι → ℂ)
    (f : ι → CompactPulse) :
    meanCoefficient (mixedPulse idx c f) = ∑ i ∈ idx, c i * meanCoefficient (f i) := by
  rw [meanCoefficient, pulseAmplitude_mixedPulse, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [meanCoefficient]
  ring

/-- Linearity of `pulseEcho` on a `mixedPulse`. -/
theorem pulseEcho_mixedPulse {ι : Type*} (idx : Finset ι) (c : ι → ℂ)
    (f : ι → CompactPulse) (T : ℝ) :
    pulseEcho (mixedPulse idx c f) T = ∑ i ∈ idx, c i * pulseEcho (f i) T := by
  rw [pulseEcho]
  have hpt : ∀ τ : ℝ, mixedPulse idx c f (T - τ) * ((echoKernel τ : ℝ) : ℂ) =
      ∑ i ∈ idx, c i * (f i (T - τ) * ((echoKernel τ : ℝ) : ℂ)) := by
    intro τ
    rw [mixedPulse_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum idx fun i _ => ((f i).integrable_pulse_mul_echoKernel T).const_mul (c i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, pulseEcho]

/-- Linearity of `pulseReflected` on a `mixedPulse`. -/
theorem pulseReflected_mixedPulse {ι : Type*} (idx : Finset ι) (c : ι → ℂ)
    (f : ι → CompactPulse) (T : ℝ) :
    pulseReflected (mixedPulse idx c f) T = ∑ i ∈ idx, c i * pulseReflected (f i) T := by
  have he := (mixedPulse idx c f).pulseEcho_eq T
  rw [pulseEcho_mixedPulse, meanCoefficient_mixedPulse, Finset.sum_mul] at he
  have hsum : (∑ i ∈ idx, c i * pulseEcho (f i) T) =
      (∑ i ∈ idx, c i * pulseReflected (f i) T) +
        ∑ i ∈ idx, c i * meanCoefficient (f i) * Complex.exp ((T : ℂ) / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(f i).pulseEcho_eq T]
    ring
  rw [hsum] at he
  exact add_right_cancel he.symm

/-- Canonical differential mean-zero pulse `(meanZeroPulse h)(S) = -(1/2) h(S) + h'(S)`. -/
def meanZeroPulse (h : CompactPulse) : CompactPulse :=
  pulseLin (-1 / 2) h

/-- Every `meanZeroPulse h` has vanishing zero-mode `meanCoefficient`. -/
theorem meanCoefficient_meanZeroPulse (h : CompactPulse) :
    meanCoefficient (meanZeroPulse h) = 0 := by
  rw [meanCoefficient, meanZeroPulse, pulseAmplitude_pulseLin]
  have hz : (-1 / 2 : ℂ) + I * (-I * (1 / 2)) = 0 := by
    linear_combination -(1 / 2 : ℂ) * I_sq
  rw [hz, zero_mul, mul_zero]

/-- Balanced two-lobe mean-zero pulse `S ↦ b(S + δ) - e^δ b(S - δ)`. -/
def balancedMeanZeroPulse (δ : ℝ) (b : CompactPulse) : CompactPulse :=
  (b.delay (-δ)).add (CompactPulse.smul (-((Real.exp δ : ℝ) : ℂ)) (b.delay δ))

@[simp] theorem balancedMeanZeroPulse_apply (δ : ℝ) (b : CompactPulse) (S : ℝ) :
    balancedMeanZeroPulse δ b S = b (S + δ) - ((Real.exp δ : ℝ) : ℂ) * b (S - δ) := by
  simp [balancedMeanZeroPulse, sub_eq_add_neg]

/-- Every `balancedMeanZeroPulse δ b` has vanishing `meanCoefficient`. -/
theorem meanCoefficient_balancedMeanZeroPulse (δ : ℝ) (b : CompactPulse) :
    meanCoefficient (balancedMeanZeroPulse δ b) = 0 := by
  rw [meanCoefficient, balancedMeanZeroPulse, pulseAmplitude_add, pulseAmplitude_smul,
    pulseAmplitude_delay, pulseAmplitude_delay]
  have e1 : -(I * (-I * (1 / 2)) * ((-δ : ℝ) : ℂ)) = (δ : ℂ) / 2 := by
    push_cast
    linear_combination -((δ : ℂ) / 2) * I_sq
  have e2 : -(I * (-I * (1 / 2)) * ((δ : ℝ) : ℂ)) = -(δ : ℂ) / 2 := by
    linear_combination ((δ : ℂ) / 2) * I_sq
  have hexp : ((Real.exp δ : ℝ) : ℂ) * Complex.exp (-(δ : ℂ) / 2) = Complex.exp ((δ : ℂ) / 2) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    ring
  rw [e1, e2, show -I * (1 / 2 : ℂ) = -(I * (1 / 2)) by ring]
  linear_combination -6 * pulseAmplitude b (-(I * (1 / 2))) * hexp

theorem balancedMeanZeroPulse_eq_zero_of_support_bound {δ B₀ : ℝ} (hδ : 0 ≤ δ)
    (b : CompactPulse) (hB₀ : ∀ s : ℝ, B₀ < |s| → b s = 0) {s : ℝ} (hs : B₀ + δ < |s|) :
    balancedMeanZeroPulse δ b s = 0 := by
  rw [balancedMeanZeroPulse, CompactPulse.add_apply, CompactPulse.smul_apply,
    CompactPulse.delay_eq_zero_of_support_bound b hB₀
      (by rwa [abs_neg, abs_of_nonneg hδ]),
    CompactPulse.delay_eq_zero_of_support_bound b hB₀
      (by rwa [abs_of_nonneg hδ])]
  simp

/-! ## 2. Five-Channel Arithmetic Decomposition of the Cusp Echo Train -/

/-- Higher-order composite denominators `c ≥ 2` with `Ω(c) ≥ 3` (neither prime, nor prime-square,
nor a product of two distinct primes). -/
def isHigherComposite (c : ℕ) : Prop :=
  2 ≤ c ∧ ¬ c.Prime ∧ ¬ (∃ p : ℕ, p.Prime ∧ c = p ^ 2) ∧
    ¬ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q)

/-- Filtered echo train over an arithmetic predicate `P : ℕ → Prop`. -/
def filteredEchoKernel (P : ℕ → Prop) (τ : ℝ) : ℝ :=
  ∑' c : ℕ, if P c then echoTerm c τ else 0

/-- Prompt echo channel (`c = 1`, delay `0`, weight `1`). -/
def promptEchoKernel (τ : ℝ) : ℝ := echoTerm 1 τ

/-- Primitive prime echo channel (`c = p` prime, delay `2 log p`, weight `1 - 1/p`). -/
def primitivePrimeEchoKernel (τ : ℝ) : ℝ := filteredEchoKernel Nat.Prime τ

/-- Repeated prime-square echo channel (`c = p²`, delay `4 log p`, weight `1 - 1/p`). -/
def primeSquareEchoKernel (τ : ℝ) : ℝ :=
  filteredEchoKernel (fun c => ∃ p : ℕ, p.Prime ∧ c = p ^ 2) τ

/-- Mixed two-prime echo channel (`c = p q` with `p < q` primes, delay `2 log p + 2 log q`,
weight `(1 - 1/p)(1 - 1/q)`). -/
def mixedTwoPrimeEchoKernel (τ : ℝ) : ℝ :=
  filteredEchoKernel (fun c => ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q) τ

/-- Higher-order composite echo channel (`Ω(c) ≥ 3`, starting at `c = 8 = 2³`). -/
def higherCompositeEchoKernel (τ : ℝ) : ℝ :=
  filteredEchoKernel isHigherComposite τ

@[simp] theorem echoTerm_zero (τ : ℝ) : echoTerm 0 τ = 0 := by
  simp [echoTerm, echoWeight]

theorem summable_filteredEchoTerm (P : ℕ → Prop) (τ : ℝ) :
    Summable fun c : ℕ => if P c then echoTerm c τ else 0 :=
  Summable.of_nonneg_of_le
    (fun c => by split_ifs <;> [exact echoTerm_nonneg c τ; exact le_rfl])
    (fun c => by split_ifs <;> [exact le_rfl; exact echoTerm_nonneg c τ])
    (summable_echoTerm τ)

theorem filteredEchoKernel_nonneg (P : ℕ → Prop) (τ : ℝ) :
    0 ≤ filteredEchoKernel P τ :=
  tsum_nonneg fun c => by split_ifs <;> [exact echoTerm_nonneg c τ; exact le_rfl]

theorem filteredEchoKernel_le_echoKernel (P : ℕ → Prop) (τ : ℝ) :
    filteredEchoKernel P τ ≤ echoKernel τ := by
  rw [filteredEchoKernel, echoKernel]
  exact (summable_filteredEchoTerm P τ).tsum_le_tsum
    (fun c => by split_ifs <;> [exact le_rfl; exact echoTerm_nonneg c τ])
    (summable_echoTerm τ)

theorem measurable_filteredEchoKernel (P : ℕ → Prop) : Measurable (filteredEchoKernel P) := by
  unfold filteredEchoKernel
  refine Measurable.tsum fun c => ?_
  by_cases hP : P c
  · simp only [if_pos hP]; exact measurable_echoTerm c
  · simp only [if_neg hP]; exact measurable_const

private theorem not_prime_and_prime_sq {c : ℕ} (hp : c.Prime) :
    ¬ ∃ p : ℕ, p.Prime ∧ c = p ^ 2 := by
  rintro ⟨p, hp', rfl⟩
  exact Nat.not_prime_mul hp'.ne_one hp'.ne_one (by simpa [sq] using hp)

private theorem not_prime_and_two_prime_mul {c : ℕ} (hp : c.Prime) :
    ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q := by
  rintro ⟨p, q, hp', hq', _, rfl⟩
  exact Nat.not_prime_mul hp'.ne_one hq'.ne_one hp

private theorem not_prime_sq_and_two_prime_mul {c : ℕ}
    (hsq : ∃ p : ℕ, p.Prime ∧ c = p ^ 2) :
    ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q := by
  rcases hsq with ⟨p, hp, rfl⟩
  rintro ⟨p₁, q₁, hp₁, hq₁, hlt, heq⟩
  have hdvd : p₁ ∣ p ^ 2 := ⟨q₁, heq⟩
  have hp_eq : p₁ = p := (Nat.prime_dvd_prime_iff_eq hp₁ hp).mp (hp₁.dvd_of_dvd_pow hdvd)
  subst hp_eq
  have hq_eq : p₁ = q₁ := Nat.mul_left_cancel hp₁.pos (by simpa [sq] using heq)
  exact hlt.ne hq_eq

private theorem echoTerm_five_channel_pointwise (c : ℕ) (τ : ℝ)
    {d1 : Decidable (c = 1)}
    {d2 : Decidable c.Prime}
    {d3 : Decidable (∃ p : ℕ, p.Prime ∧ c = p ^ 2)}
    {d4 : Decidable (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q)}
    {d5 : Decidable (isHigherComposite c)} :
    echoTerm c τ =
      (@ite _ (c = 1) d1 (echoTerm c τ) 0) +
      (@ite _ c.Prime d2 (echoTerm c τ) 0) +
      (@ite _ (∃ p : ℕ, p.Prime ∧ c = p ^ 2) d3 (echoTerm c τ) 0) +
      (@ite _ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q) d4 (echoTerm c τ) 0) +
      (@ite _ (isHigherComposite c) d5 (echoTerm c τ) 0) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp only [echoTerm_zero, ite_self, add_zero]
  rcases eq_or_ne c 1 with rfl | hc1
  · have hnsq : ¬ ∃ p : ℕ, p.Prime ∧ 1 = p ^ 2 := by
      rintro ⟨p, hp, h⟩; have := hp.two_le; nlinarith
    have hnmul : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 1 = p * q := by
      rintro ⟨p, q, hp, hq, _, h⟩; have := hp.two_le; have := hq.two_le; nlinarith
    have hnh : ¬ isHigherComposite 1 := fun h => by have := h.1; omega
    rw [@if_pos _ d1 rfl, @if_neg _ d2 Nat.not_prime_one, @if_neg _ d3 hnsq,
      @if_neg _ d4 hnmul, @if_neg _ d5 hnh]
    ring
  have hc2 : 2 ≤ c := by omega
  by_cases hp : c.Prime
  · rw [@if_neg _ d1 hc1, @if_pos _ d2 hp, @if_neg _ d3 (not_prime_and_prime_sq hp),
      @if_neg _ d4 (not_prime_and_two_prime_mul hp), @if_neg _ d5 (fun h => h.2.1 hp)]
    ring
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ c = p ^ 2
  · rw [@if_neg _ d1 hc1, @if_neg _ d2 hp, @if_pos _ d3 hsq,
      @if_neg _ d4 (not_prime_sq_and_two_prime_mul hsq), @if_neg _ d5 (fun h => h.2.2.1 hsq)]
    ring
  by_cases hmul : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q
  · rw [@if_neg _ d1 hc1, @if_neg _ d2 hp, @if_neg _ d3 hsq,
      @if_pos _ d4 hmul, @if_neg _ d5 (fun h => h.2.2.2 hmul)]
    ring
  · rw [@if_neg _ d1 hc1, @if_neg _ d2 hp, @if_neg _ d3 hsq,
      @if_neg _ d4 hmul, @if_pos _ d5 ⟨hc2, hp, hsq, hmul⟩]
    ring

/-- **Exact Five-Channel Arithmetic Decomposition of the Echo Kernel.** -/
theorem echoKernel_eq_five_channels (τ : ℝ) :
    echoKernel τ = promptEchoKernel τ + primitivePrimeEchoKernel τ +
      primeSquareEchoKernel τ + mixedTwoPrimeEchoKernel τ + higherCompositeEchoKernel τ := by
  have hs1 := summable_filteredEchoTerm (fun c => c = 1) τ
  have hs2 := summable_filteredEchoTerm Nat.Prime τ
  have hs3 := summable_filteredEchoTerm (fun c => ∃ p : ℕ, p.Prime ∧ c = p ^ 2) τ
  have hs4 := summable_filteredEchoTerm
    (fun c => ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q) τ
  have hs5 := summable_filteredEchoTerm isHigherComposite τ
  have hp1 : filteredEchoKernel (fun c => c = 1) τ = promptEchoKernel τ := by
    rw [filteredEchoKernel, promptEchoKernel, tsum_eq_single 1]
    · simp
    · intro c hc; simp [hc]
  rw [← hp1, primitivePrimeEchoKernel, primeSquareEchoKernel, mixedTwoPrimeEchoKernel,
    higherCompositeEchoKernel, filteredEchoKernel, filteredEchoKernel, filteredEchoKernel,
    filteredEchoKernel, filteredEchoKernel,
    ← hs1.tsum_add hs2, ← (hs1.add hs2).tsum_add hs3,
    ← ((hs1.add hs2).add hs3).tsum_add hs4,
    ← (((hs1.add hs2).add hs3).add hs4).tsum_add hs5, echoKernel]
  exact tsum_congr fun c => echoTerm_five_channel_pointwise c τ

/-- Every higher-order composite denominator satisfies `8 ≤ c`, with equality at `c = 8 = 2³`. -/
theorem eight_le_of_isHigherComposite {c : ℕ} (hc : isHigherComposite c) : 8 ≤ c := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hc2, hnp, hnsq, hnmul⟩ := hc
  interval_cases c
  · exact hnp Nat.prime_two
  · exact hnp Nat.prime_three
  · exact hnsq ⟨2, Nat.prime_two, rfl⟩
  · exact hnp Nat.prime_five
  · exact hnmul ⟨2, 3, Nat.prime_two, Nat.prime_three, by decide, rfl⟩
  · exact hnp (by decide)

theorem isHigherComposite_eight : isHigherComposite 8 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · rintro ⟨p, hp, h⟩
    have hp2 := hp.two_le
    rcases lt_or_ge p 3 with hlt | hge
    · have : p = 2 := by omega
      subst this; norm_num at h
    · nlinarith
  · rintro ⟨p, q, hp, hq, hlt, h⟩
    have hp2 := hp.two_le
    rcases eq_or_lt_of_le hp2 with rfl | hp3
    · have hq4 : q = 4 := by omega
      subst hq4
      exact absurd hq (by decide)
    · have hq4 : 4 ≤ q := by omega
      nlinarith

/-- Below `6 log 2 = 2 log 8`, all higher-order composite returns vanish identically. -/
theorem higherCompositeEchoKernel_eq_zero {τ : ℝ} (hτ : τ ≤ 6 * Real.log 2) :
    higherCompositeEchoKernel τ = 0 := by
  rw [higherCompositeEchoKernel, filteredEchoKernel]
  have hzero : ∀ c : ℕ, (if isHigherComposite c then echoTerm c τ else 0) = 0 := by
    intro c
    split_ifs with hc
    · have hc8 : (8 : ℝ) ≤ (c : ℝ) := by exact_mod_cast eight_le_of_isHigherComposite hc
      have hlog8 : 3 * Real.log 2 ≤ Real.log c := by
        have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
        have hl : Real.log 8 = 3 * Real.log 2 := by rw [h8, Real.log_pow]; norm_num
        linarith [Real.log_le_log (by norm_num) hc8]
      rw [echoTerm, if_neg]
      rw [echoDelay]
      linarith
    · rfl
  simp [hzero]

/-- On `τ ≤ 6 log 2`, `echoKernel` is exhausted by prompt + prime + prime-square + mixed two-prime
returns. -/
theorem echoKernel_eq_four_channels_of_le {τ : ℝ} (hτ : τ ≤ 6 * Real.log 2) :
    echoKernel τ = promptEchoKernel τ + primitivePrimeEchoKernel τ +
      primeSquareEchoKernel τ + mixedTwoPrimeEchoKernel τ := by
  rw [echoKernel_eq_five_channels τ, higherCompositeEchoKernel_eq_zero hτ, add_zero]

/-- Delay and weight of a prime-square traversal `c = p²`: delay `4 log p` and weight `1 - 1/p`. -/
theorem echoDelay_and_weight_prime_sq {p : ℕ} (hp : p.Prime) :
    echoDelay (p ^ 2) = 4 * Real.log p ∧ echoWeight (p ^ 2) = 1 - 1 / (p : ℝ) := by
  constructor
  · rw [echoDelay, Nat.cast_pow, Real.log_pow]
    ring
  · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have htot : Nat.totient (p ^ 2) = p * (p - 1) := by
      simpa [sq] using Nat.totient_prime_pow hp (by decide : 0 < 2)
    rw [echoWeight, htot, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_pow]
    field_simp

/-- Delay and multiplicative weight of a mixed two-prime traversal `c = p q` (`p ≠ q` primes). -/
theorem echoDelay_and_weight_prime_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    echoDelay (p * q) = echoDelay p + echoDelay q ∧
      echoWeight (p * q) = echoWeight p * echoWeight q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  constructor
  · rw [echoDelay, echoDelay, echoDelay, Nat.cast_mul, Real.log_mul hp0.ne' hq0.ne']
    ring
  · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
    rw [echoWeight, echoWeight, echoWeight, Nat.totient_mul hcop, Nat.cast_mul, Nat.cast_mul]
    field_simp

/-- Channel convolution of a pulse with `filteredEchoKernel P`. -/
def filteredPulseEcho (P : ℕ → Prop) (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ τ : ℝ, h (T - τ) * ((filteredEchoKernel P τ : ℝ) : ℂ)

theorem integrable_pulse_mul_filteredEchoKernel (P : ℕ → Prop) (h : CompactPulse) (T : ℝ) :
    Integrable fun τ : ℝ => h (T - τ) * ((filteredEchoKernel P τ : ℝ) : ℂ) := by
  have hdom := (h.integrable_pulse_mul_echoKernel T).norm
  have hmeas : Measurable fun τ : ℝ => h (T - τ) * ((filteredEchoKernel P τ : ℝ) : ℂ) :=
    (h.continuous_toFun.comp (continuous_const.sub continuous_id)).measurable.mul
      (Complex.measurable_ofReal.comp (measurable_filteredEchoKernel P))
  refine hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (filteredEchoKernel_nonneg P τ),
    Real.norm_of_nonneg ((filteredEchoKernel_nonneg P τ).trans (filteredEchoKernel_le_echoKernel P τ))]
  exact mul_le_mul_of_nonneg_left (filteredEchoKernel_le_echoKernel P τ) (norm_nonneg _)

/-- **Five-Channel Echo Decomposition of Any Compact Pulse (Including Mixed Pulses).** -/
theorem pulseEcho_eq_five_channels (h : CompactPulse) (T : ℝ) :
    pulseEcho h T =
      filteredPulseEcho (fun c => c = 1) h T +
      filteredPulseEcho Nat.Prime h T +
      filteredPulseEcho (fun c => ∃ p : ℕ, p.Prime ∧ c = p ^ 2) h T +
      filteredPulseEcho (fun c => ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q) h T +
      filteredPulseEcho isHigherComposite h T := by
  set P : Fin 5 → (ℕ → Prop) :=
    ![fun c => c = 1, Nat.Prime, fun c => ∃ p : ℕ, p.Prime ∧ c = p ^ 2,
      fun c => ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ c = p * q, isHigherComposite]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 5)),
      Integrable fun τ : ℝ => h (T - τ) * ((filteredEchoKernel (P i) τ : ℝ) : ℂ) :=
    fun i _ => integrable_pulse_mul_filteredEchoKernel (P i) h T
  have hp1 : ∀ τ : ℝ, filteredEchoKernel (fun c => c = 1) τ = promptEchoKernel τ := fun τ => by
    rw [filteredEchoKernel, promptEchoKernel, tsum_eq_single 1]
    · simp
    · intro c hc; simp [hc]
  have hsum_int := integral_finsetSum (Finset.univ : Finset (Fin 5)) hint
  have hpt : ∀ τ : ℝ, h (T - τ) * ((echoKernel τ : ℝ) : ℂ) =
      ∑ i : Fin 5, h (T - τ) * ((filteredEchoKernel (P i) τ : ℝ) : ℂ) := by
    intro τ
    rw [Fin.sum_univ_five]
    simp only [P, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [hp1 τ, echoKernel_eq_five_channels τ]
    unfold primitivePrimeEchoKernel primeSquareEchoKernel mixedTwoPrimeEchoKernel
      higherCompositeEchoKernel
    push_cast
    ring
  rw [pulseEcho, integral_congr_ae (Eventually.of_forall hpt), hsum_int, Fin.sum_univ_five]
  rfl

/-- On the finite window `T ≤ 6 log 2 - S₀`, the higher-composite echo contribution to `pulseEcho h`
vanishes identically. -/
theorem filteredPulseEcho_higherComposite_eq_zero (h : CompactPulse) {S₀ : ℝ}
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {T : ℝ} (hT : T ≤ 6 * Real.log 2 - S₀) :
    filteredPulseEcho isHigherComposite h T = 0 := by
  rw [filteredPulseEcho]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun τ => ?_)
  rcases le_or_gt τ (6 * Real.log 2) with hτ | hτ
  · dsimp only
    rw [show filteredEchoKernel isHigherComposite τ = higherCompositeEchoKernel τ from rfl,
      higherCompositeEchoKernel_eq_zero hτ]
    simp
  · have hs : S₀ < |T - τ| := by
      have := neg_abs_le (T - τ)
      linarith
    simp [hS₀ (T - τ) hs]

/-! ## 3. Exact Unitary Plancherel Identity, Cusp Escape Law, and Interference Expansion -/

/-- Reflected wavepacket of a pulse `h` against a general continuous-spectrum symbol `J : ℝ → ℂ`. -/
def unitaryReflected (J : ℝ → ℂ) (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ ξ : ℝ, pulseAmplitude h (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ))

theorem unitaryReflected_modular_eq (h : ℝ → ℂ) (T : ℝ) :
    unitaryReflected (fun ξ => scatteringPhase ((ξ : ℂ) * I)) h T = pulseReflected h T := rfl

private theorem fourier_pulse_eq_amplitude (h : CompactPulse) (v : ℝ) :
    𝓕 h.toFun v = (2 * Real.pi : ℂ) * pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ) := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [Real.fourier_real_eq_integral_exp_smul, pulseAmplitude, mul_inv_cancel_left₀ hpi]
  refine integral_congr_ae (Eventually.of_forall fun S => ?_)
  simp only [smul_eq_mul]
  have he : Complex.exp ((-2 * Real.pi * S * v : ℝ) * I) =
      Complex.exp (-(I * ((2 * Real.pi * v : ℝ) : ℂ) * (S : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [he, mul_comm]

theorem memLp_two_pulse (h : CompactPulse) : MemLp h.toFun 2 (volume : Measure ℝ) := by
  obtain ⟨C, hC⟩ := h.compact.exists_bound_of_continuous h.continuous_toFun
  refine (memLp_two_iff_integrable_sq_norm h.continuous_toFun.aestronglyMeasurable).mpr ?_
  refine (h.integrable_toFun.norm.const_mul (max C 0)).mono'
    (h.continuous_toFun.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun S => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right ((hC S).trans (le_max_left _ _)) (norm_nonneg _)

/-- **Spectral Amplitude Plancherel Identity.** -/
theorem integral_norm_sq_pulseAmplitude (h : CompactPulse) :
    2 * Real.pi * (∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2) = ∫ S : ℝ, ‖h S‖ ^ 2 := by
  have hpl := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq h.integrable_toFun
    (memLp_two_pulse h)
  have hpt : ∀ v : ℝ, ‖𝓕 h.toFun v‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ‖pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ)‖ ^ 2 := by
    intro v
    rw [fourier_pulse_eq_amplitude, norm_mul, mul_pow]
    congr 2
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp_rw [hpt] at hpl
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2) (2 * Real.pi)] at hpl
  have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
  rw [habs, smul_eq_mul] at hpl
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  calc 2 * Real.pi * (∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2)
      = (2 * Real.pi) ^ 2 * ((2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2) := by
          field_simp
    _ = ∫ S : ℝ, ‖h S‖ ^ 2 := hpl

theorem integrable_fourier_pulse (h : CompactPulse) : Integrable (𝓕 h.toFun) := by
  have hint : Integrable fun ξ : ℝ => pulseAmplitude h (ξ : ℂ) := by
    simpa using h.integrable_amplitude_line 0
  have hsub : Integrable fun v : ℝ =>
      (2 * Real.pi : ℂ) * pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ) :=
    (hint.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0)).const_mul _
  exact hsub.congr (Eventually.of_forall fun v => (fourier_pulse_eq_amplitude h v).symm)

theorem integrable_norm_sq_pulseAmplitude (h : CompactPulse) :
    Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 := by
  obtain ⟨Ca, _, hCa⟩ := h.exists_norm_amplitude_le 0
  have hint : Integrable fun ξ : ℝ => pulseAmplitude h (ξ : ℂ) := by
    simpa using h.integrable_amplitude_line 0
  have hcont : Continuous fun ξ : ℝ => pulseAmplitude h (ξ : ℂ) :=
    h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal
  refine (hint.norm.const_mul Ca).mono' (hcont.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right (hCa _ (by simp)) (norm_nonneg _)

/-- **Spectral Amplitude Autocorrelation Identity.** Integrating `‖a_h(ξ)‖² e^{-i ξ d}` recovers
`(2π)⁻¹ ∫ h(S - d) conj(h(S)) dS`. -/
theorem integral_norm_sq_pulseAmplitude_mul_cexp (h : CompactPulse) (d : ℝ) :
    (2 * Real.pi : ℂ) * (∫ ξ : ℝ, ((‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(I * (ξ : ℂ) * (d : ℂ)))) =
      ∫ S : ℝ, h (S - d) * (starRingEnd ℂ) (h S) := by
  have hpair := plancherel_pairing (h.delay d).integrable_toFun h.integrable_toFun
    (integrable_fourier_pulse h) h.continuous_toFun
  have hpt : ∀ v : ℝ, 𝓕 (h.delay d).toFun v * (starRingEnd ℂ) (𝓕 h.toFun v) =
      (2 * (Real.pi : ℂ)) ^ 2 *
        (((‖pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (-(I * ((2 * Real.pi * v : ℝ) : ℂ) * (d : ℂ)))) := by
    intro v
    rw [fourier_pulse_eq_amplitude (h.delay d) v, fourier_pulse_eq_amplitude h v,
      pulseAmplitude_delay, map_mul]
    have hconj : (starRingEnd ℂ) (2 * Real.pi : ℂ) = (2 * Real.pi : ℂ) := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl, Complex.conj_ofReal]
    rw [hconj]
    have hnorm : pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ) *
        (starRingEnd ℂ) (pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ)) =
        ((‖pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    linear_combination ((2 * (Real.pi : ℂ)) ^ 2 *
      Complex.exp (-(I * ((2 * Real.pi * v : ℝ) : ℂ) * (d : ℂ)))) * hnorm
  simp_rw [hpt] at hpair
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun ξ : ℝ => ((‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (-(I * (ξ : ℂ) * (d : ℂ)))) (2 * Real.pi)] at hpair
  have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
  rw [habs, Complex.real_smul] at hpair
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hinv_cast : (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = (2 * (Real.pi : ℂ))⁻¹ := by push_cast; rfl
  rw [hinv_cast] at hpair
  have hc2 : (2 * (Real.pi : ℂ)) ^ 2 * (2 * (Real.pi : ℂ))⁻¹ = 2 * (Real.pi : ℂ) := by
    field_simp
  calc (2 * Real.pi : ℂ) * (∫ ξ : ℝ, ((‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (-(I * (ξ : ℂ) * (d : ℂ))))
      = (2 * (Real.pi : ℂ)) ^ 2 * ((2 * (Real.pi : ℂ))⁻¹ *
          ∫ ξ : ℝ, ((‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp (-(I * (ξ : ℂ) * (d : ℂ)))) := by
          rw [← mul_assoc, hc2]
    _ = ∫ S : ℝ, (h.delay d).toFun S * (starRingEnd ℂ) (h.toFun S) := hpair
    _ = ∫ S : ℝ, h (S - d) * (starRingEnd ℂ) (h S) := rfl

/-- **Unitary Plancherel Conservation Law.** For every measurable unitary continuous-spectrum
symbol `J : ℝ → ℂ` (`‖J ξ‖ = 1`), `unitaryReflected J h` is square-integrable and preserves the
exact `L²` norm of `h` (including every mixed pulse with full interference). -/
theorem integrable_and_integral_norm_sq_unitaryReflected {J : ℝ → ℂ} (hJ : Measurable J)
    (hunit : ∀ ξ : ℝ, ‖J ξ‖ = 1) (h : CompactPulse) :
    Integrable (fun T : ℝ => ‖unitaryReflected J h T‖ ^ 2) ∧
      (∫ T : ℝ, ‖unitaryReflected J h T‖ ^ 2) = ∫ S : ℝ, ‖h S‖ ^ 2 := by
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  set G : ℝ → ℂ := fun v =>
    (2 * Real.pi : ℂ) * pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ) * J (2 * Real.pi * v)
    with hG_def
  have hint_a : Integrable fun ξ : ℝ => pulseAmplitude h (ξ : ℂ) := by
    simpa using h.integrable_amplitude_line 0
  have hG_meas : Measurable G :=
    ((measurable_const.mul
      (h.differentiable_amplitude.continuous.measurable.comp
        (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)))).mul
      (hJ.comp (measurable_const.mul measurable_id)))
  have hG_norm : ∀ v : ℝ,
      ‖G v‖ = 2 * Real.pi * ‖pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ)‖ := by
    intro v
    simp only [hG_def]
    rw [norm_mul, norm_mul, hunit, mul_one,
      show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hG_int : Integrable G := by
    have hdom : Integrable fun v : ℝ =>
        2 * Real.pi * ‖pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ)‖ :=
      (hint_a.norm.comp_mul_left' hpi0).const_mul (2 * Real.pi)
    exact hdom.mono' hG_meas.aestronglyMeasurable (Eventually.of_forall fun v => (hG_norm v).le)
  obtain ⟨Ca, _, hCa⟩ := h.exists_norm_amplitude_le 0
  have hG_L2 : MemLp G 2 (volume : Measure ℝ) := by
    refine (memLp_two_iff_integrable_sq_norm hG_meas.aestronglyMeasurable).mpr ?_
    refine (hG_int.norm.const_mul (2 * Real.pi * Ca)).mono'
      (hG_meas.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hG_norm v]
    exact mul_le_mul_of_nonneg_left (hCa _ (by simp)) (by positivity)
  have hFG : ∀ T : ℝ, 𝓕 G (-T) = unitaryReflected J h T := by
    intro T
    rw [Real.fourier_real_eq_integral_exp_smul, unitaryReflected]
    have hsub := Measure.integral_comp_mul_left
      (fun ξ : ℝ => pulseAmplitude h (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)))
      (2 * Real.pi)
    have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
    rw [habs, Complex.real_smul] at hsub
    have hpt : ∀ v : ℝ, Complex.exp ((-2 * Real.pi * v * -T : ℝ) * I) • G v =
        (2 * Real.pi : ℂ) * (pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ) *
          J (2 * Real.pi * v) *
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (T : ℂ))) := by
      intro v
      simp only [hG_def, smul_eq_mul]
      have he : Complex.exp ((-2 * Real.pi * v * -T : ℝ) * I) =
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (T : ℂ)) := by
        congr 1; push_cast; ring
      rw [he]; ring
    simp_rw [hpt]
    rw [integral_const_mul, hsub]
    have hpiC : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi0
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hpiC, one_mul]
  have hint_F := (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hG_int hG_L2).comp_neg
  have hU_int : Integrable fun T : ℝ => ‖unitaryReflected J h T‖ ^ 2 :=
    hint_F.congr (Eventually.of_forall fun T => by dsimp only; rw [hFG T])
  refine ⟨hU_int, ?_⟩
  have hpl := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hG_int hG_L2
  calc (∫ T : ℝ, ‖unitaryReflected J h T‖ ^ 2)
      = ∫ T : ℝ, ‖𝓕 G (-T)‖ ^ 2 :=
          integral_congr_ae (Eventually.of_forall fun T => by dsimp only; rw [hFG T])
    _ = ∫ u : ℝ, ‖𝓕 G u‖ ^ 2 := integral_neg_eq_self (fun u : ℝ => ‖𝓕 G u‖ ^ 2) volume
    _ = ∫ v : ℝ, ‖G v‖ ^ 2 := hpl
    _ = ∫ v : ℝ, (2 * Real.pi) ^ 2 * ‖pulseAmplitude h ((2 * Real.pi * v : ℝ) : ℂ)‖ ^ 2 := by
          refine integral_congr_ae (Eventually.of_forall fun v => ?_)
          dsimp only; rw [hG_norm v, mul_pow]
    _ = 2 * Real.pi * ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 := by
          rw [integral_const_mul, Measure.integral_comp_mul_left
            (fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2) (2 * Real.pi)]
          have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
          rw [habs, smul_eq_mul]
          field_simp
    _ = ∫ S : ℝ, ‖h S‖ ^ 2 := integral_norm_sq_pulseAmplitude h

theorem continuous_unitaryReflected {J : ℝ → ℂ} (hJ : Measurable J)
    (hb : ∀ ξ : ℝ, ‖J ξ‖ ≤ 1) (h : CompactPulse) :
    Continuous (unitaryReflected J h) := by
  have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ := by
    have h0 := (h.integrable_amplitude_line 0).norm
    exact h0.congr (Eventually.of_forall fun ξ => by simp)
  unfold unitaryReflected
  refine continuous_of_dominated (bound := fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖) ?_ ?_ hint_a ?_
  · intro T
    exact (((h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).measurable.mul
      hJ).mul (by fun_prop : Continuous fun ξ : ℝ =>
        Complex.exp (I * (ξ : ℂ) * (T : ℂ))).measurable).aestronglyMeasurable
  · intro T
    exact ae_of_all _ fun ξ => by
      rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb ξ)
  · exact ae_of_all _ fun ξ => by fun_prop

theorem continuous_pulseReflected (h : CompactPulse) : Continuous (pulseReflected h) :=
  continuous_unitaryReflected continuous_scatteringPhase_line.measurable
    (fun ξ => (norm_scatteringPhase_line ξ).le) h

theorem integrable_norm_sq_pulseReflected (h : CompactPulse) :
    Integrable fun T : ℝ => ‖pulseReflected h T‖ ^ 2 :=
  (integrable_and_integral_norm_sq_unitaryReflected
    continuous_scatteringPhase_line.measurable norm_scatteringPhase_line h).1

/-- **Plancherel Conservation for the Modular Reflected Wavepacket.** -/
theorem integral_norm_sq_pulseReflected (h : CompactPulse) :
    (∫ T : ℝ, ‖pulseReflected h T‖ ^ 2) = ∫ S : ℝ, ‖h S‖ ^ 2 :=
  (integrable_and_integral_norm_sq_unitaryReflected
    continuous_scatteringPhase_line.measurable norm_scatteringPhase_line h).2

private theorem integral_Iic_exp (a : ℝ) :
    (∫ T in Iic a, Real.exp T) = Real.exp a := by
  rw [← integral_indicator measurableSet_Iic, ← integral_neg_eq_self]
  have hae : ∀ᵐ σ : ℝ, σ ≠ -a := by
    rw [ae_iff]
    have hset : {σ : ℝ | ¬ σ ≠ -a} = ({-a} : Set ℝ) := by ext σ; simp
    rw [hset]; exact measure_singleton (-a)
  have heq : (fun σ : ℝ => (Iic a).indicator Real.exp (-σ)) =ᵐ[volume]
      (Ioi (-a)).indicator (fun σ : ℝ => Real.exp (-1 * σ)) := by
    refine hae.mono fun σ hσ => ?_
    dsimp only
    rcases lt_or_gt_of_ne hσ with hlt | hgt
    · rw [indicator_of_notMem (show -σ ∉ Iic a by simp; linarith),
        indicator_of_notMem (show σ ∉ Ioi (-a) by simp; linarith)]
    · rw [indicator_of_mem (show -σ ∈ Iic a by simp; linarith),
        indicator_of_mem (show σ ∈ Ioi (-a) from hgt)]
      ring_nf
  rw [integral_congr_ae heq, integral_indicator measurableSet_Ioi,
    integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) (-a)]
  ring_nf

/-- Pre-wavefront `L²` energy of `pulseReflected h`: before `-S₀`, only the mean term contributes. -/
theorem integral_Iic_norm_sq_pulseReflected (h : CompactPulse) {S₀ : ℝ}
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) :
    (∫ T in Iic (-S₀), ‖pulseReflected h T‖ ^ 2) =
      ‖meanCoefficient h‖ ^ 2 * Real.exp (-S₀) := by
  have hae : ∀ᵐ T : ℝ, T ≠ -S₀ := by
    rw [ae_iff]
    have hset : {T : ℝ | ¬ T ≠ -S₀} = ({-S₀} : Set ℝ) := by ext T; simp
    rw [hset]; exact measure_singleton (-S₀)
  have hcongr : (fun T : ℝ => ‖pulseReflected h T‖ ^ 2) =ᵐ[volume.restrict (Iic (-S₀))]
      fun T : ℝ => ‖meanCoefficient h‖ ^ 2 * Real.exp T := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
    refine hae.mono fun T hne hle => ?_
    have hlt : T < -S₀ := lt_of_le_of_ne hle hne
    rw [h.pulseReflected_before_wavefront hS₀ hlt, norm_neg, norm_mul, mul_pow, Complex.norm_exp]
    have hre : ((T : ℂ) / 2).re = T / 2 := by simp
    rw [hre, sq (Real.exp (T / 2)), ← Real.exp_add]
    congr 2
    ring
  rw [integral_congr_ae hcongr, integral_const_mul, integral_Iic_exp (-S₀)]

/-- **Exact Cusp Escape Identity.** For any compact pulse `h` supported in `[-S₀, S₀]` and any
finite cutoff `T₂ ≥ -S₀`, the unescaped late-time cusp return energy `∫_{T₂}^∞ ‖𝒮_h(T)‖² dT` equals
the initial `L²` energy minus the pre-wavefront zero-mode piece minus the escaped finite-window
energy on `(-S₀, T₂]`. -/
theorem integral_Ioi_norm_sq_pulseReflected (h : CompactPulse) {S₀ T₂ : ℝ}
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) (hT₂ : -S₀ ≤ T₂) :
    (∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2) =
      (∫ S : ℝ, ‖h S‖ ^ 2) - ‖meanCoefficient h‖ ^ 2 * Real.exp (-S₀) -
        ∫ T in Ioc (-S₀) T₂, ‖pulseReflected h T‖ ^ 2 := by
  set E : ℝ → ℝ := fun T => ‖pulseReflected h T‖ ^ 2
  have hE : Integrable E := integrable_norm_sq_pulseReflected h
  have hall : (∫ T in Iic T₂, E T) + (∫ T in Ioi T₂, E T) = ∫ T : ℝ, E T := by
    have h1 := integral_add_compl (s := Iic T₂) measurableSet_Iic hE
    rwa [compl_Iic] at h1
  have hdisj : Disjoint (Iic (-S₀)) (Ioc (-S₀) T₂) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.1.not_ge hx1
  have hunion : Iic (-S₀) ∪ Ioc (-S₀) T₂ = Iic T₂ := Iic_union_Ioc_eq_Iic hT₂
  have hsplit : (∫ T in Iic T₂, E T) =
      (∫ T in Iic (-S₀), E T) + ∫ T in Ioc (-S₀) T₂, E T := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc hE.integrableOn hE.integrableOn]
  have htot : (∫ T : ℝ, E T) = ∫ S : ℝ, ‖h S‖ ^ 2 := integral_norm_sq_pulseReflected h
  have hpre : (∫ T in Iic (-S₀), E T) = ‖meanCoefficient h‖ ^ 2 * Real.exp (-S₀) :=
    integral_Iic_norm_sq_pulseReflected h hS₀
  linarith

theorem integrable_pulseReflected_mul_conj (g h : CompactPulse) :
    Integrable fun T : ℝ => pulseReflected g T * (starRingEnd ℂ) (pulseReflected h T) := by
  have hg2 := integrable_norm_sq_pulseReflected g
  have hh2 := integrable_norm_sq_pulseReflected h
  have hcont : Continuous fun T : ℝ =>
      pulseReflected g T * (starRingEnd ℂ) (pulseReflected h T) :=
    (continuous_pulseReflected g).mul (continuous_conj.comp (continuous_pulseReflected h))
  refine ((hg2.add hh2).const_mul (1 / 2)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun T => ?_)
  dsimp only [Pi.add_apply]
  rw [norm_mul, RCLike.norm_conj]
  nlinarith [sq_nonneg (‖pulseReflected g T‖ - ‖pulseReflected h T‖)]

/-- **Exact Mixed-Pulse Interference Expansion.** On every window `W ⊆ ℝ` (bounded or unbounded),
the reflected energy of `mixedPulse idx c f` expands into diagonal energies plus all off-diagonal
Hermitian cross-interferences, with zero omitted terms. -/
theorem setIntegral_norm_sq_mixedPulse_reflected {ι : Type*} (idx : Finset ι) (c : ι → ℂ)
    (f : ι → CompactPulse) (W : Set ℝ) :
    (∫ T in W, ‖pulseReflected (mixedPulse idx c f) T‖ ^ 2) =
      (∑ i ∈ idx, ‖c i‖ ^ 2 * ∫ T in W, ‖pulseReflected (f i) T‖ ^ 2) +
        ∑ i ∈ idx, ∑ j ∈ idx.erase i,
          ((c i * (starRingEnd ℂ) (c j)) *
            ∫ T in W, pulseReflected (f i) T * (starRingEnd ℂ) (pulseReflected (f j) T)).re := by
  have hpt : ∀ T : ℝ, ‖pulseReflected (mixedPulse idx c f) T‖ ^ 2 =
      (∑ i ∈ idx, ‖c i‖ ^ 2 * ‖pulseReflected (f i) T‖ ^ 2) +
        ∑ i ∈ idx, ∑ j ∈ idx.erase i,
          ((c i * (starRingEnd ℂ) (c j)) *
            (pulseReflected (f i) T * (starRingEnd ℂ) (pulseReflected (f j) T))).re := by
    intro T
    rw [pulseReflected_mixedPulse]
    have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := fun z => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [hnorm, map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    have hdiag : ∀ i ∈ idx,
        (∑ j ∈ idx, ((c i * pulseReflected (f i) T) *
          (starRingEnd ℂ) (c j * pulseReflected (f j) T)).re) =
        ‖c i‖ ^ 2 * ‖pulseReflected (f i) T‖ ^ 2 +
          ∑ j ∈ idx.erase i,
            ((c i * (starRingEnd ℂ) (c j)) *
              (pulseReflected (f i) T * (starRingEnd ℂ) (pulseReflected (f j) T))).re := by
      intro i hi
      rw [← Finset.add_sum_erase _ _ hi]
      congr 1
      · rw [← hnorm (c i * pulseReflected (f i) T), norm_mul, mul_pow]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        congr 1
        ring
    rw [Finset.sum_congr rfl hdiag, Finset.sum_add_distrib]
  simp_rw [hpt]
  have hint_diag : ∀ i ∈ idx, Integrable
      (fun T : ℝ => ‖c i‖ ^ 2 * ‖pulseReflected (f i) T‖ ^ 2) (volume.restrict W) :=
    fun i _ => ((integrable_norm_sq_pulseReflected (f i)).const_mul _).integrableOn
  have hint_pair : ∀ i j : ι, Integrable
      (fun T : ℝ => ((c i * (starRingEnd ℂ) (c j)) *
        (pulseReflected (f i) T * (starRingEnd ℂ) (pulseReflected (f j) T))).re)
      (volume.restrict W) :=
    fun i j => (Complex.reCLM.integrable_comp
      (((integrable_pulseReflected_mul_conj (f i) (f j)).const_mul _))).integrableOn
  have hint_off : ∀ i ∈ idx, Integrable
      (fun T : ℝ => ∑ j ∈ idx.erase i,
        ((c i * (starRingEnd ℂ) (c j)) *
          (pulseReflected (f i) T * (starRingEnd ℂ) (pulseReflected (f j) T))).re)
      (volume.restrict W) :=
    fun i _ => integrable_finsetSum (idx.erase i) fun j _ => hint_pair i j
  rw [integral_add (integrable_finsetSum idx hint_diag) (integrable_finsetSum idx hint_off),
    integral_finsetSum idx hint_diag, integral_finsetSum idx hint_off]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum (idx.erase i) fun j _ => hint_pair i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hre := Complex.reCLM.integral_comp_comm
      (((integrable_pulseReflected_mul_conj (f i) (f j)).const_mul
        (c i * (starRingEnd ℂ) (c j))).integrableOn (s := W))
    simp only [Complex.reCLM_apply] at hre
    rw [hre, integral_const_mul]

/-! ## 4. Unconditional Cusp Escape on Actual `ζ` -/

private theorem scatteringPhase_eq_scatterQ_div (u : ℂ) :
    scatteringPhase u = ((2 : ℂ) / (2 * u - 1)) * scatterQ (u + 1 / 2) := by
  unfold scatteringPhase scatterQ
  rw [show 2 * (u + 1 / 2) - 1 = 2 * u by ring, show 2 * (u + 1 / 2) = 1 + 2 * u by ring]
  ring

private theorem differentiableAt_scatteringPhase_of_ne {u : ℂ} (hne : u ≠ 1 / 2)
    (hxi : xi (1 + 2 * u) ≠ 0) : DifferentiableAt ℂ scatteringPhase u := by
  have hd : 2 * u - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
  unfold scatteringPhase
  exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) u).div (by fun_prop) hd).mul
    (((xi_differentiable _).comp u (by fun_prop)).div
      ((xi_differentiable _).comp u (by fun_prop)) hxi)

/-- **Zero-Free Strip Gives Reflected Wavepacket and Tail Escape Rates.** If every zero of `ζ` with
`Re ρ > 0` satisfies `Re ρ ≤ 1 - 2δ` (`0 < σ < δ ≤ 1/4`), then every compact pulse `h` obeys
`‖pulseReflected h T‖ ≤ C e^{-σ T}` (`T ≥ 0`) and unescaped tail decay
`∫_{T₂}^∞ ‖pulseReflected h T‖² dT ≤ (C² / (2σ)) e^{-2σ T₂}` (`T₂ ≥ 0`). -/
theorem pulseReflected_decay_of_zeroFree {δ σ : ℝ} (hδ : δ ≤ 1 / 4) (hσ : 0 < σ)
    (hσδ : σ < δ) (hz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * δ)
    (h : CompactPulse) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ T : ℝ, 0 ≤ T → ‖pulseReflected h T‖ ≤ C * Real.exp (-σ * T)) ∧
      (∀ T₂ : ℝ, 0 ≤ T₂ →
        (∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2) ≤
          (C ^ 2 / (2 * σ)) * Real.exp (-2 * σ * T₂)) := by
  set Θ : ℝ := 1 - 2 * δ
  have hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 := fun z hz' h0 => by
    have := hz z h0 (by linarith)
    linarith
  obtain ⟨κ, hκ, hζ⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree (Θ := Θ) (by linarith)
    (by linarith) hzf (δ := 2 * (δ - σ)) (by linarith) (by linarith) (ε := 1) one_pos
  set boxU : Set ℂ := {u : ℂ | (-σ ≤ u.re ∧ u.re ≤ 0) ∧ 1 ≤ |u.im| ∧ |u.im| ≤ 3}
  have hboxU_c : IsCompact boxU := by
    have heq : boxU = ((Icc (-σ) 0) ×ℂ (Icc (-3 : ℝ) 3)) ∩ {u : ℂ | 1 ≤ |u.im|} := by
      ext u
      simp only [boxU, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζU : ContinuousOn (fun u : ℂ => (riemannZeta (1 + 2 * u))⁻¹) boxU := by
    intro u hu
    have hne1 : 1 + 2 * u ≠ 1 := fun he => by
      have him0 := congrArg Complex.im he; simp at him0
      have := hu.2.1; rw [him0, abs_zero] at this; linarith
    have hz0 : riemannZeta (1 + 2 * u) ≠ 0 := hzf _ (by simp [Θ]; linarith [hu.1.1])
    exact ((ContinuousAt.comp (f := fun v : ℂ => 1 + 2 * v)
      (differentiableAt_riemannZeta hne1).continuousAt (by fun_prop)).inv₀ hz0).continuousWithinAt
  obtain ⟨Mζ, hMζ⟩ := hboxU_c.exists_bound_of_continuousOn hcont_ζU
  have hζ_shift : ∀ s : ℂ, -σ + 1 / 2 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ (max (max Mζ 0) (4 / κ)) * |s.im| ^ 1 := by
    intro s hs1 hs2 hsim
    set u : ℂ := s - 1 / 2
    have hu_eq : 1 + 2 * u = 2 * s := by simp [u]; ring
    have hu1 : -σ ≤ u.re := by simp [u]; linarith
    have hu2 : u.re ≤ 0 := by simp [u]; linarith
    have huim : |u.im| = |s.im| := by simp [u]
    rw [← hu_eq, ← huim]
    have hpow1 : (1 : ℝ) ≤ |u.im| ^ 1 := by simpa [huim] using hsim
    rcases le_or_gt |u.im| 3 with hsmall | hbig
    · calc ‖(riemannZeta (1 + 2 * u))⁻¹‖
          ≤ Mζ := hMζ u ⟨⟨hu1, hu2⟩, by rwa [huim], hsmall⟩
        _ ≤ max (max Mζ 0) (4 / κ) * 1 := by
            rw [mul_one]; exact (le_max_left Mζ 0).trans (le_max_left _ _)
        _ ≤ max (max Mζ 0) (4 / κ) * |u.im| ^ 1 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have him : |(1 + 2 * u).im| = 2 * |u.im| := by
        have : (1 + 2 * u).im = 2 * u.im := by simp
        rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb := hζ (1 + 2 * u) (by simp [Θ]; linarith) (by rw [him]; linarith)
      rw [Real.rpow_neg_one, him] at hb
      have hpos : 0 < ‖riemannZeta (1 + 2 * u)‖ := lt_of_lt_of_le (by positivity) hb
      rw [norm_inv, inv_le_comm₀ hpos (by positivity)]
      have h2t : 2 + 2 * |u.im| ≤ 4 * |u.im| := by linarith
      calc (max (max Mζ 0) (4 / κ) * |u.im| ^ 1)⁻¹
          ≤ ((4 / κ) * |u.im|)⁻¹ := by
            rw [pow_one]
            exact inv_anti₀ (by positivity)
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        _ = κ * (4 * |u.im|)⁻¹ := by field_simp
        _ ≤ κ * (2 + 2 * |u.im|)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2t) hκ.le
        _ ≤ ‖riemannZeta (1 + 2 * u)‖ := hb
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le (by positivity) hζ_shift
  obtain ⟨Ca, _, hrap⟩ := h.rapidAmplitude.decay σ (NQ + 2)
  have hxi_left : ∀ u : ℂ, -σ ≤ u.re → xi (1 + 2 * u) ≠ 0 :=
    fun _ hu1 => RingdownRate.xi_ne_zero_of_zeroFree hδ hσδ hz hu1
  set Kbox : Set ℂ := Icc (-σ) 0 ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn (fun u => pulseAmplitude h (-I * u) * scatteringPhase u) Kbox := by
    intro u hu
    have hu' := Complex.mem_reProdIm.1 hu
    have hne : u ≠ 1 / 2 := fun he => by have := hu'.1.2; rw [he] at this; norm_num at this
    exact (((h.differentiable_amplitude _).comp u (by fun_prop)).mul
      (differentiableAt_scatteringPhase_of_ne hne (hxi_left u hu'.1.1))).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKbox.exists_bound_of_continuousOn hcontK
  set B : ℝ := max (2 * max B₀ 0) (CQ * Ca)
  have hB_left : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 →
      ‖pulseAmplitude h (-I * u) * scatteringPhase u‖ ≤ B / (1 + u.im ^ 2) := by
    intro u hu1 hu2
    by_cases hut : 1 ≤ |u.im|
    · have hφu : ‖scatteringPhase u‖ ≤ CQ * |u.im| ^ NQ := by
        rw [scatteringPhase_eq_scatterQ_div, norm_mul]
        have h2le : ‖(2 : ℂ) / (2 * u - 1)‖ ≤ 1 := by
          have him2 : (2 : ℝ) ≤ |(2 * u - 1).im| := by simp; linarith
          have hn2 : (2 : ℝ) ≤ ‖2 * u - 1‖ := him2.trans (Complex.abs_im_le_norm _)
          rw [norm_div, Complex.norm_ofNat, div_le_one (by linarith)]
          exact hn2
        have hQb : ‖scatterQ (u + 1 / 2)‖ ≤ CQ * |u.im| ^ NQ := by
          simpa using hQ (u + 1 / 2) (by simp; linarith) (by simp; linarith) (by simpa using hut)
        calc ‖(2 : ℂ) / (2 * u - 1)‖ * ‖scatterQ (u + 1 / 2)‖
            ≤ 1 * (CQ * |u.im| ^ NQ) := mul_le_mul h2le hQb (norm_nonneg _) (by positivity)
          _ = CQ * |u.im| ^ NQ := one_mul _
      have hw1 : (-I * u).re = u.im := by simp
      have hw2 : (-I * u).im = -u.re := by simp
      have ha := hrap (-I * u) (by rw [hw2, abs_neg, abs_le]; constructor <;> linarith)
      rw [hw1] at ha
      have ht1 : |u.im| ^ NQ ≤ (1 + |u.im|) ^ NQ :=
        pow_le_pow_left₀ (abs_nonneg _) (by linarith) NQ
      have ht2 : 1 + u.im ^ 2 ≤ (1 + |u.im|) ^ 2 := by nlinarith [abs_nonneg u.im, sq_abs u.im]
      rw [le_div_iff₀ (by positivity), norm_mul]
      calc ‖pulseAmplitude h (-I * u)‖ * ‖scatteringPhase u‖ * (1 + u.im ^ 2)
          ≤ ‖pulseAmplitude h (-I * u)‖ * (CQ * (1 + |u.im|) ^ NQ) * (1 + |u.im|) ^ 2 := by
            gcongr
            exact hφu.trans (mul_le_mul_of_nonneg_left ht1 hCQ)
        _ = CQ * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ (NQ + 2)) := by ring
        _ ≤ CQ * Ca := mul_le_mul_of_nonneg_left ha hCQ
        _ ≤ B := le_max_right _ _
    · have hut' := abs_le.1 (not_le.1 hut).le
      have hb := hB₀ u (Complex.mem_reProdIm.2 ⟨⟨hu1, hu2⟩, hut'⟩)
      have hsq : u.im ^ 2 ≤ 1 := by nlinarith
      rw [le_div_iff₀ (by positivity)]
      calc ‖pulseAmplitude h (-I * u) * scatteringPhase u‖ * (1 + u.im ^ 2)
          ≤ max B₀ 0 * 2 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
            (le_max_right _ _)
        _ ≤ B := by linarith [le_max_left (2 * max B₀ 0) (CQ * Ca)]
  set C : ℝ := B * Real.pi
  have hC0 : 0 ≤ C := by positivity
  have hpt_decay : ∀ T : ℝ, 0 ≤ T → ‖pulseReflected h T‖ ≤ C * Real.exp (-σ * T) := by
    intro T hT
    set Φ : ℂ → ℂ := fun u =>
      pulseAmplitude h (-I * u) * scatteringPhase u * Complex.exp (u * (T : ℂ)) with hΦ
    have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → -σ ≤ s.re ∧ s.re ≤ 0 := by
      intro s hs; rw [uIcc_of_ge (by linarith)] at hs; exact hs
    have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → DifferentiableAt ℂ Φ s := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
      exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
        (differentiableAt_scatteringPhase_of_ne hne (hxi_left s hs1))).mul (by fun_prop))
    have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → ‖Φ s‖ ≤ B / (1 + s.im ^ 2) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have he : ‖Complex.exp (s * (T : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        have : (s * (T : ℂ)).re = s.re * T := by simp
        rw [this]
        exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hs2 hT)
      simp only [hΦ]; rw [norm_mul]
      calc ‖pulseAmplitude h (-I * s) * scatteringPhase s‖ * ‖Complex.exp (s * (T : ℂ))‖
          ≤ B / (1 + s.im ^ 2) * 1 := mul_le_mul (hB_left s hs1 hs2) he (norm_nonneg _) (by positivity)
        _ = B / (1 + s.im ^ 2) := mul_one _
    have hshift := integral_vertical_line_shift_of_decay hd hbΦ
    have hpk : pulseReflected h T = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
      rw [pulseReflected]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hΦ]
      have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
      rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
      congr 2; ring
    rw [hpk, hshift]
    have hpt : ∀ t : ℝ,
        ‖Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * T) := by
      intro t
      have hre : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).re = -σ := by simp
      have him : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
      simp only [hΦ]; rw [norm_mul, Complex.norm_exp]
      have : ((((-σ : ℝ) : ℂ) + (t : ℂ) * I) * (T : ℂ)).re = -σ * T := by simp
      rw [this]
      have hb := hB_left _ (by rw [hre]) (by rw [hre]; linarith)
      rw [him, div_eq_mul_inv] at hb
      exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    have hint : Integrable fun t : ℝ => B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * T) :=
      (integrable_inv_one_add_sq.const_mul B).mul_const _
    calc ‖∫ t : ℝ, Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * T) :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
      _ = C * Real.exp (-σ * T) := by
          rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]
  refine ⟨C, hC0, hpt_decay, fun T₂ hT₂ => ?_⟩
  have hdom : IntegrableOn (fun T : ℝ => C ^ 2 * Real.exp (-2 * σ * T)) (Ioi T₂) :=
    (integrableOn_exp_mul_Ioi (by linarith) T₂).const_mul (C ^ 2)
  have hle : ∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2 ≤
      ∫ T in Ioi T₂, C ^ 2 * Real.exp (-2 * σ * T) := by
    refine setIntegral_mono_on (integrable_norm_sq_pulseReflected h).integrableOn hdom
      measurableSet_Ioi fun T hT => ?_
    have hT0 : 0 ≤ T := hT₂.trans (mem_Ioi.mp hT).le
    have hb := hpt_decay T hT0
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [mul_pow, sq (Real.exp (-σ * T)), ← Real.exp_add] at hsq
    refine hsq.trans (le_of_eq ?_)
    congr 2
    ring
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -2 * σ < 0) T₂]
  field_simp

/-- **Unconditional Sub-Seven-Eighths Cusp Escape Theorem.** Because `ζ` has no zeros with
`Re s > 20999 / 24000`, every compact pulse `h` (single or mixed, with all interference terms
retained) unconditionally escapes the modular cusp at every exponent `0 < σ < 3001 / 48000`
(`3001 / 48000 > 1 / 16`), both pointwise in `(x, Y)` and in reflected `L²` tail energy. -/
theorem unconditional_cusp_escape_sub_seven_eighths {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : σ < 3001 / 48000) (h : CompactPulse) :
    (∀ x Y : ℝ, 0 < Y → ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ : ℝ, 0 ≤ τ → ‖pulseField h τ x Y‖ ≤ C * Real.exp (-σ * τ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧
      (∀ T : ℝ, 0 ≤ T → ‖pulseReflected h T‖ ≤ C * Real.exp (-σ * T)) ∧
      (∀ T₂ : ℝ, 0 ≤ T₂ →
        (∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2) ≤
          (C ^ 2 / (2 * σ)) * Real.exp (-2 * σ * T₂))) := by
  have hz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * (3001 / 48000 : ℝ) := by
    intro ρ h0 hpos
    have hmem := riemannZeta_zero_mem_sub_quasiRH_strip hpos h0
    linarith [hmem.2]
  exact ⟨fun x Y hY =>
      RingdownRate.pulseField_decay_of_zeroFree (δ := 3001 / 48000) (by norm_num) hσ0 hσ hz h x hY,
    pulseReflected_decay_of_zeroFree (δ := 3001 / 48000) (by norm_num) hσ0 hσ hz h⟩

end GaloisForLFunctions.BlackHoleRingdown

end
