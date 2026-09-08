import GaloisForLFunctions.HTGeometry.FokasLenellsSingularPhase
import GaloisForLFunctions.HTGeometry.HermiteFourierEigen
import GaloisForLFunctions.RHTower.WeightOneCliffordLogClosure
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Origin-regularized scattering packets in the existing Fourier-Sobolev space

For every Schwartz profile `f`, the spectral datum `z² f(z)` evolves by
`exp(-it/(2z))` with a genuine L² weak derivative. The double zero cancels the
inverse-square term from differentiating the phase. The result is differentiable
at zero as well, so no point-supported distributional term is lost.

This realizes the weighted-Sobolev mechanism of Proposition 5.1 and equations
(5.8)–(5.11) of Yan–Zhang–Zhu, arXiv:2607.19649, on the corpus's actual
Fourier-Sobolev H¹ carrier. Every polynomial weight and the inverse-square weight
remain in every Lp space; the L² derivative cost is bounded linearly in time.
-/

open MeasureTheory Complex Filter Topology
open scoped SchwartzMap ENNReal LineDeriv
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def seed (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := mulXCLM (mulXCLM f)

def packet (f : 𝓢(ℝ, ℂ)) (t z : ℝ) : ℂ := phase t z * seed f z

def derivativeSeed (f : 𝓢(ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  (2 : ℂ) • mulXCLM f + seed (derivSCLM f) + (I*(t:ℂ)/2) • f

@[simp] theorem seed_apply (f : 𝓢(ℝ, ℂ)) (z : ℝ) :
    seed f z = (z:ℂ)^2 * f z := by simp [seed]; ring

theorem packet_memLp (f : 𝓢(ℝ, ℂ)) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (packet f t) p volume :=
  (memLp_phase_iff t p _).mpr ((seed f).memLp p volume)

theorem packet_inverse_square_ae (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (fun z : ℝ => packet f t z/(z:ℂ)^2) =ᵐ[volume]
      fun z => phase t z * f z := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with z hz
  have hzc : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
  simp only [packet, seed_apply]
  field_simp

theorem packet_inverse_square_memLp (f : 𝓢(ℝ, ℂ)) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (fun z : ℝ => packet f t z/(z:ℂ)^2) p volume :=
  ((memLp_phase_iff t p _).mpr (f.memLp p volume)).ae_eq
    (packet_inverse_square_ae f t).symm

theorem packet_derivative_zero (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (packet f t) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_zero_iff_norm_tendsto_zero]
  have heq : (fun z : ℝ => ‖z⁻¹ • (packet f t (0+z)-packet f t 0)‖) =
      fun z => ‖z‖ * ‖f z‖ := by
    funext z
    have hval : z⁻¹ • (packet f t (0+z)-packet f t 0) =
        (z:ℂ)*phase t z*f z := by
      by_cases hz : z = 0
      · subst z; simp [packet]
      · have hzc : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
        simp only [zero_add, packet, seed_apply, Complex.ofReal_zero, zero_pow (by omega : 2 ≠ 0),
          zero_mul, mul_zero, sub_zero, Complex.real_smul, Complex.ofReal_inv]
        field_simp
    rw [hval]
    simp
  rw [heq]
  have ht := ((continuous_norm.continuousAt : ContinuousAt (fun z : ℝ => ‖z‖) 0).mul
    f.continuous.continuousAt.norm).tendsto
  change Tendsto (fun z : ℝ => ‖z‖ * ‖f z‖) (𝓝 0)
    (𝓝 (‖(0:ℝ)‖ * ‖f 0‖)) at ht
  rw [norm_zero, zero_mul] at ht
  exact ht.mono_left (show (𝓝[≠] (0:ℝ)) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)

/-- The double-zero packet is differentiable even at the singular spectral origin. -/
theorem packet_hasDerivAt (f : 𝓢(ℝ, ℂ)) (t z : ℝ) :
    HasDerivAt (packet f t) (if z = 0 then 0 else phase t z * derivativeSeed f t z) z := by
  by_cases hz : z = 0
  · subst z; simpa using packet_derivative_zero f t
  rw [if_neg hz]
  have hp := (((hasDerivAt_const z t).div ((hasDerivAt_id z).const_mul 2)
    (mul_ne_zero (by norm_num) hz)).ofReal_comp.mul_const I).neg.cexp
  have hs := (((hasDerivAt_id z).ofReal_comp.pow 2).mul (f.hasDerivAt z))
  have h := hp.mul hs
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall fun y => by simp [packet, phase]
  · have hzc : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
    simp only [derivativeSeed, add_apply, smul_apply, smul_eq_mul, mulXCLM_apply,
      seed_apply, derivSCLM_apply, phase, id_eq, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply]
    push_cast
    field_simp
    ring

theorem packet_derivative_ae (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ∀ᵐ z : ℝ, HasDerivAt (packet f t) (phase t z * derivativeSeed f t z) z := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with z hz
  simpa [hz] using packet_hasDerivAt f t z

/-- The classical derivative is square integrable; the singular inverse-square
term has been canceled by the seed's double zero. -/
theorem packet_derivative_memLp (f : 𝓢(ℝ, ℂ)) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (deriv (packet f t)) p volume := by
  have h := (memLp_phase_iff t p _).mpr ((derivativeSeed f t).memLp p volume)
  apply h.ae_eq
  filter_upwards [packet_derivative_ae f t] with z hz
  exact hz.deriv.symm

/-- The derivative formula is a weak derivative as well: there is no point-supported
extra term at the singular origin. -/
theorem packet_weak_derivative_pairing (f g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (∫ z : ℝ, packet f t z * deriv (g : ℝ → ℂ) z) =
      -(∫ z : ℝ, deriv (packet f t) z * g z) := by
  apply integral_mul_deriv_eq_deriv_mul_of_integrable
  · intro z _
    exact (packet_hasDerivAt f t z).differentiableAt.hasDerivAt
  · intro z _
    exact g.hasDerivAt z
  · exact (packet_memLp f t 2).integrable_mul
      (by simpa only [coe_derivSCLM] using (derivSCLM g).memLp 2 volume)
  · exact (packet_derivative_memLp f t 2).integrable_mul (g.memLp 2 volume)
  · exact (packet_memLp f t 2).integrable_mul (g.memLp 2 volume)

/-- All polynomially weighted evolved double-zero packets remain integrable. -/
theorem packet_polynomial_weight_memLp (f : 𝓢(ℝ, ℂ)) (t : ℝ) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (fun z : ℝ => (z:ℂ)^n * packet f t z) p volume := by
  have hg := (memLp_phase_iff t p _).mpr
    (((mulXCLM ^ n) (seed f)).memLp p volume)
  have hx : ∀ (n : ℕ) (g : 𝓢(ℝ, ℂ)) (z : ℝ),
      (mulXCLM ^ n) g z = (z:ℂ)^n * g z := by
    intro n
    induction n with
    | zero => intro g z; simp
    | succ n ih =>
      intro g z
      rw [pow_succ', mul_apply_eq_comp, mulXCLM_apply, ih]
      ring
  apply hg.ae_eq
  exact Filter.Eventually.of_forall fun z => by
    change phase t z * ((mulXCLM ^ n) (seed f)) z = (z:ℂ)^n * packet f t z
    rw [hx]
    simp only [packet]
    ring

def packetL2 (f : 𝓢(ℝ, ℂ)) (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (packet_memLp f t 2).toLp (packet f t)

def packetDerivativeL2 (f : 𝓢(ℝ, ℂ)) (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (packet_derivative_memLp f t 2).toLp (deriv (packet f t))

/-- The packet's derivative is identified in the existing tempered-distribution carrier. -/
theorem packetL2_weak_derivative (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ∂_{(1:ℝ)} (packetL2 f t : 𝓢'(ℝ, ℂ)) =
      (packetDerivativeL2 f t : 𝓢'(ℝ, ℂ)) := by
  ext g
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  have hline : ∂_{(1:ℝ)} g = SchwartzMap.derivCLM ℂ ℂ g := by
    ext z
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.derivCLM_apply,
      fderiv_apply_one_eq_deriv]
  rw [hline]
  have hleft : (∫ z : ℝ, (-SchwartzMap.derivCLM ℂ ℂ g) z • packetL2 f t z) =
      -(∫ z : ℝ, packet f t z * deriv (g : ℝ → ℂ) z) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [(packet_memLp f t 2).coeFn_toLp] with z hz
    change (-SchwartzMap.derivCLM ℂ ℂ g) z •
      (packet_memLp f t 2).toLp (packet f t) z = _
    rw [hz]
    simp only [neg_apply, SchwartzMap.derivCLM_apply, smul_eq_mul]
    ring
  have hright : (∫ z : ℝ, g z • packetDerivativeL2 f t z) =
      (∫ z : ℝ, deriv (packet f t) z * g z) := by
    apply integral_congr_ae
    filter_upwards [(packet_derivative_memLp f t 2).coeFn_toLp] with z hz
    change g z • (packet_derivative_memLp f t 2).toLp (deriv (packet f t)) z = _
    rw [hz, smul_eq_mul, mul_comm]
  rw [hleft, hright, packet_weak_derivative_pairing, neg_neg]

/-- Evolved double-zero Schwartz profiles lie in the corpus's genuine Fourier-Sobolev H1. -/
theorem packetL2_mem_fourierL2H1 (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    packetL2 f t ∈ _root_.RHTower.fourierL2H1 :=
  (_root_.RHTower.mem_fourierL2H1_iff_exists_weakDerivative _).mpr
    ⟨packetDerivativeL2 f t, packetL2_weak_derivative f t⟩

theorem packetDerivativeL2_eq_evolution (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    packetDerivativeL2 f t = evolution t ((derivativeSeed f t).toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(packet_derivative_memLp f t 2).coeFn_toLp,
    evolution_ae t ((derivativeSeed f t).toLp 2 volume),
    (derivativeSeed f t).coeFn_toLp 2 volume, packet_derivative_ae f t]
    with z hd he hs hder
  change (packet_derivative_memLp f t 2).toLp (deriv (packet f t)) z = _
  rw [hd, hder.deriv, he, hs]

/-- The derivative cost grows at most linearly in time, with the exact inverse-square
coefficient `|t|/2`. -/
theorem packet_derivative_time_bound (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ‖packetDerivativeL2 f t‖ ≤ ‖(derivativeSeed f 0).toLp 2 volume‖ +
      (|t|/2)*‖f.toLp 2 volume‖ := by
  rw [packetDerivativeL2_eq_evolution, norm_evolution]
  have hseed : derivativeSeed f t = derivativeSeed f 0 + (I*(t:ℂ)/2) • f := by
    simp [derivativeSeed]
  rw [hseed]
  change ‖(SchwartzMap.toLpCLM ℂ ℂ 2 volume)
    (derivativeSeed f 0 + (I*(t:ℂ)/2) • f)‖ ≤ _
  rw [map_add, map_smul]
  apply le_trans (norm_add_le _ _)
  simp only [SchwartzMap.toLpCLM_apply, norm_smul, norm_div, norm_mul, norm_I,
    Complex.norm_real, Real.norm_eq_abs, norm_ofNat, one_mul]
  rfl

end
end GaloisForLFunctions.HTGeometry.FokasLenells
