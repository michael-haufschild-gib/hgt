import GaloisForLFunctions.BlackHoleRingdown.CompleteResolutionOfTheCuspEscapeQuestion
import GaloisForLFunctions.BlackHoleRingdown.DegreeOnePrimeGateRigidityAndIntegralTwins
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.TheMobiusReadingOfTheScatteringReturns
import GaloisForLFunctions.SelbergClass.DegreeOne.IntegralGateRigidity

/-!
# Complete Resolution of the Degree-One Integral Prime-Gate Scattering Question

This module gives the complete unconditional answer to whether the quarter-rate ringdown law (or
any positive `p = 2` sector cancellation rate) follows from causality, passivity, unitarity, the
`ζ` functional equation, and degree-one integral local prime gates at all primes, together with all
implications and positive rigidity corollaries:

1. **Bounce-Agnostic Prime-Sector Calculus & Unconditional Falsification at Every Rate `δ > 0`
   (`quartet_bounce_euler_factorization`, `quartet_centered_sector_delay`,
   `falsification_of_degree_one_integral_gate_axiom_class`)**:
   In `xiQuartet σ γ`, every local prime gate is identically the degree-one integral `ζ` gate
   `primeEchoGate p w = (1 - p^{-(2w+1)}) / (1 - p^{-2w})` (`a_p = 1 ∈ ℤ` for all `p ∈ ℙ`), while
   the causal single-bounce kernel is dressed by the retarded four-pole Lax–Phillips cavity impulse
   `quartetImpulseTail σ γ`. All arithmetic return identities (totient weights `φ(c)/c`, Möbius
   inversion `μ(n)/n`, repeated prime-power invariance, and the `p = 2` sector delay recurrence)
   hold identically, along with strict causality, `s ↦ 1 - s` symmetry, real-axis positivity,
   Schur passivity, Herglotz positivity, axis unitarity, and the `G_R`/`G_{RL}` pole-multiplicity
   dictionary. Yet for **every** `δ > 0` (in particular `δ = 3001 / 48000` and `δ = 1 / 4`),
   choosing `σ ∈ (max(7/8, 1 - 2δ), 1)` causes the reflected field, the centered `p = 2` sector
   envelope, the `p = 2` sector `L²` tail energy, and the `2^k` return cancellation error to
   strictly fail at rate `δ`. Any physical proof must therefore fix the bulk single-bounce
   transform to `B(w, 1/2)`.

2. **Positive Rigidity and Classification Corollaries Once the Single-Bounce Transform Is Fixed
   (`complete_resolution_of_degree_one_integral_gate_question`)**:
   - **Pure-bounce degree-one rational prime gates (`Theorem II.A`)**: Passive unitary degree-one
     rational local prime gates on `B(w, 1/2)` classify into `{u_p * zetaLocalGate p,
     u_p * flippedLocalGate p}`; the flipped integral gate `(1 - p · p^{-2w}) / (p(1 - p^{-2w}))`
     has poles restricted to `Re w = -1/2 < -1/4`, preserving unconditional `< 3001/48000` decay
     and `δ = 1/4 ↔ RiemannHypothesis`.
   - **Sharpness of degree one (`Theorem II.B`)**: For every prime `p ≥ 5` (unlike `p ∈ {2, 3}`),
     integral trace `r + u = p ∈ ℤ` (`r u = p`) produces a degree-two integral-coefficient passive
     pure-bounce horizon violating quarter-rate decay `δ = 1/4`.
   - **All-prime Selberg rigidity (`Theorem II.C`)**: In `ExtendedSelbergClass` at degree `1`,
     integral prime-power coefficients `a_p ∈ ℤ` automatically satisfy `a_p ∈ {-1, 0, 1}`,
     `internalShift = 0`, and `F = L(·, χ)` for a primitive quadratic character `χ` (without
     assuming Ramanujan or `ϑ < 1/2`), uniquely pinning `a_p = 1` and `F = ζ` iff `conductor = 1`
     iff `meromorphicOrderAt F 1 < 0`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology Finset
open scoped ContDiff FourierTransform Classical BigOperators ENNReal ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SelbergClass.DegreeOne

/-! ## 1. Causal Dressed Single-Bounce Kernel and Bounce-Agnostic Prime-Sector Calculus -/

/-- Causal dressed single-bounce kernel of `xiQuartet σ γ`: prompt modular `bounceKernel` on
`v > 0` plus causal convolution with `quartetImpulseTail σ γ`. -/
def quartetBounceKernel (σ γ : ℝ) (v : ℝ) : ℂ :=
  bounceWave 0 v +
    ∫ u : ℝ, quartetImpulseTail σ γ u * bounceWave 0 (v - u)

/-- Strict retarded causality of `quartetBounceKernel σ γ`. -/
theorem quartetBounceKernel_eq_zero_of_nonpos (σ γ : ℝ) {v : ℝ} (hv : v ≤ 0) :
    quartetBounceKernel σ γ v = 0 := by
  have hb0 : ∀ x : ℝ, x ≤ 0 → bounceWave 0 x = 0 := fun x hx => by
    simp [bounceWave, not_lt.mpr hx]
  rw [quartetBounceKernel, hb0 v hv, zero_add]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  dsimp only [Pi.zero_apply]
  rcases le_or_gt u 0 with hu | hu
  · simp [quartetImpulseTail, not_lt.mpr hu]
  · rw [hb0 (v - u) (by linarith), mul_zero]

private theorem integral_add₄ {f₁ f₂ f₃ f₄ : ℝ → ℂ}
    (h₁ : Integrable f₁) (h₂ : Integrable f₂) (h₃ : Integrable f₃) (h₄ : Integrable f₄) :
    (∫ x : ℝ, f₁ x + f₂ x + f₃ x + f₄ x) =
      (∫ x : ℝ, f₁ x) + (∫ x : ℝ, f₂ x) + (∫ x : ℝ, f₃ x) + (∫ x : ℝ, f₄ x) := by
  have h12 : Integrable (fun x : ℝ => f₁ x + f₂ x) := h₁.add h₂
  have h123 : Integrable (fun x : ℝ => f₁ x + f₂ x + f₃ x) := h12.add h₃
  rw [integral_add h123 h₄, integral_add h12 h₃, integral_add h₁ h₂]

private theorem quartetGate_eq_blaschke_four' {σ γ : ℝ} (h0 : 1 / 2 < σ) (hγ : 0 < γ) (w : ℂ) :
    let w₁ : ℂ := (((1 - σ) / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
    let w₂ : ℂ := ((σ / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
    quartetGate σ γ w =
      ((w - w₁) / (w + (starRingEnd ℂ) w₁)) *
      ((w - (starRingEnd ℂ) w₁) / (w + w₁)) *
      ((w - w₂) / (w + (starRingEnd ℂ) w₂)) *
      ((w - (starRingEnd ℂ) w₂) / (w + w₂)) := by
  have hq1 : quartetZero σ γ * (1 - quartetZero σ γ) ≠ 0 := fun hz => by
    have him := congrArg Complex.im hz
    simp only [quartetZero, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.zero_im] at him
    nlinarith
  have hq2 : (starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)) ≠ 0 := by
    have heq : (starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)) =
        (starRingEnd ℂ) (quartetZero σ γ * (1 - quartetZero σ γ)) := by simp [map_mul, map_sub]
    rw [heq]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hq1
  dsimp only
  set w₁ : ℂ := (((1 - σ) / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
  set w₂ : ℂ := ((σ / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
  have hp1 : ∀ z : ℂ, (1 - (2 * z) * (1 - 2 * z) / (quartetZero σ γ * (1 - quartetZero σ γ))) *
      (quartetZero σ γ * (1 - quartetZero σ γ)) = 4 * (z - (starRingEnd ℂ) w₁) * (z - w₂) := by
    intro z; rw [sub_mul, one_mul, div_mul_cancel₀ _ hq1]
    simp only [w₁, w₂, quartetZero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hp2 : ∀ z : ℂ, (1 - (2 * z) * (1 - 2 * z) /
      ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) *
      ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ))) =
      4 * (z - w₁) * (z - (starRingEnd ℂ) w₂) := by
    intro z; rw [sub_mul, one_mul, div_mul_cancel₀ _ hq2]
    simp only [w₁, w₂, quartetZero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hnum' : quartetFactor σ γ (2 * w) *
      ((quartetZero σ γ * (1 - quartetZero σ γ)) *
        ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) =
      16 * (w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂) := by
    calc quartetFactor σ γ (2 * w) * _
        = ((1 - (2 * w) * (1 - 2 * w) / (quartetZero σ γ * (1 - quartetZero σ γ))) *
            (quartetZero σ γ * (1 - quartetZero σ γ))) *
          ((1 - (2 * w) * (1 - 2 * w) /
            ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) *
            ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) := by
          unfold quartetFactor; ring
      _ = _ := by rw [hp1 w, hp2 w]; ring
  have hsym_den : quartetFactor σ γ (1 + 2 * w) = quartetFactor σ γ (2 * (-w)) := by
    have hq_sym : (1 + 2 * w) * (1 - (1 + 2 * w)) = (2 * (-w)) * (1 - 2 * (-w)) := by ring
    unfold quartetFactor; rw [hq_sym]
  have hden' : quartetFactor σ γ (1 + 2 * w) *
      ((quartetZero σ γ * (1 - quartetZero σ γ)) *
        ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) =
      16 * (w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂) := by
    rw [hsym_den]
    calc quartetFactor σ γ (2 * (-w)) * _
        = ((1 - (2 * (-w)) * (1 - 2 * (-w)) / (quartetZero σ γ * (1 - quartetZero σ γ))) *
            (quartetZero σ γ * (1 - quartetZero σ γ))) *
          ((1 - (2 * (-w)) * (1 - 2 * (-w)) /
            ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) *
            ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) := by
          unfold quartetFactor; ring
      _ = _ := by rw [hp1 (-w), hp2 (-w)]; ring
  have hprod_ne := mul_ne_zero hq1 hq2
  rw [quartetGate, ← mul_div_mul_right _ _ hprod_ne, hnum', hden']
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  calc (16 * (w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂)) /
          (16 * (w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂))
      = (16 * ((w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂))) /
          (16 * ((w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂))) := by
        congr 1 <;> ring
    _ = ((w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂)) /
          ((w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂)) :=
        mul_div_mul_left _ _ h16
    _ = _ := by simp only [div_mul_div_comm]

private theorem differentiableAt_quartetScatteringPhase {σ γ : ℝ} {w : ℂ}
    (hne : w ≠ 1 / 2) (hxi : xiQuartet σ γ (1 + 2 * w) ≠ 0) :
    DifferentiableAt ℂ (quartetScatteringPhase σ γ) w := by
  have hd : 2 * w - 1 ≠ 0 := fun h0' => hne (by linear_combination h0' / 2)
  unfold quartetScatteringPhase quartetReducedScattering
  exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) w).div (by fun_prop) hd).mul
    ((((differentiable_xiQuartet σ γ) _).comp w (by fun_prop)).div
      (((differentiable_xiQuartet σ γ) _).comp w (by fun_prop)) hxi)

private theorem continuous_quartetScatteringPhase_line {σ γ : ℝ} (h0 : 1 / 2 < σ)
    (h1 : σ < 1) (hγ : 0 < γ) :
    Continuous fun ξ : ℝ => quartetScatteringPhase σ γ ((ξ : ℂ) * I) := by
  obtain ⟨hschur, _⟩ := quartet_schur_and_unitary h0 h1 hγ
  refine continuous_iff_continuousAt.mpr fun ξ => ?_
  have hne : ((ξ : ℂ) * I) ≠ 1 / 2 := fun he => by have := congrArg Complex.re he; simp at this
  exact ContinuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) * I)
    (differentiableAt_quartetScatteringPhase hne (hschur _ (by simp) |>.1)).continuousAt
    (by fun_prop)

/-- Exact Laplace transform of `quartetImpulseTail σ γ` throughout `Re w > -(1 - σ) / 2`
(in particular on the entire closed right half-plane `Re w ≥ 0`). -/
theorem integrable_and_laplace_quartetImpulseTail {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hγ : 0 < γ) {w : ℂ} (hw : -((1 - σ) / 2) < w.re) :
    Integrable (quartetImpulseTail σ γ) ∧
    Integrable (fun u : ℝ => Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u) ∧
    1 + (∫ u : ℝ, Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u) =
      quartetGate σ γ w := by
  set a₁ : ℝ := (1 - σ) / 2
  set a₂ : ℝ := σ / 2
  set b : ℝ := γ / 2
  have ha₁ : 0 < a₁ := by dsimp [a₁]; linarith
  have ha₂ : 0 < a₂ := by dsimp [a₂]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  set p₁ : ℂ := -(a₁ : ℂ) + (b : ℂ) * I
  set p₂ : ℂ := -(a₁ : ℂ) - (b : ℂ) * I
  set p₃ : ℂ := -(a₂ : ℂ) + (b : ℂ) * I
  set p₄ : ℂ := -(a₂ : ℂ) - (b : ℂ) * I
  set c₁ : ℂ := -(4 * (a₁ : ℂ) * p₁) / (2 * I * (b : ℂ))
  set c₂ : ℂ := (4 * (a₁ : ℂ) * p₂) / (2 * I * (b : ℂ))
  set d₁ : ℂ := -(4 * (a₂ : ℂ) * p₃) / (2 * I * (b : ℂ))
  set d₂ : ℂ := (4 * (a₂ : ℂ) * p₄) / (2 * I * (b : ℂ))
  set R₁ : ℂ := c₁ * (1 + d₁ / (p₁ - p₃) + d₂ / (p₁ - p₄))
  set R₂ : ℂ := c₂ * (1 + d₁ / (p₂ - p₃) + d₂ / (p₂ - p₄))
  set R₃ : ℂ := d₁ * (1 + c₁ / (p₃ - p₁) + c₂ / (p₃ - p₂))
  set R₄ : ℂ := d₂ * (1 + c₁ / (p₄ - p₁) + c₂ / (p₄ - p₂))
  -- Single-exponential half-line Laplace helper
  have hexp_lap : ∀ z : ℂ, z.re < 0 →
      Integrable (fun u : ℝ => if 0 < u then Complex.exp (z * (u : ℂ)) else 0) ∧
      (∫ u : ℝ, if 0 < u then Complex.exp (z * (u : ℂ)) else 0) = (-z)⁻¹ := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
    have hm : Measurable fun u : ℝ => Complex.exp (z * (u : ℂ)) := by fun_prop
    have hint_on : IntegrableOn (fun u : ℝ => Complex.exp (z * (u : ℂ))) (Ioi (0 : ℝ)) := by
      refine (integrableOn_exp_mul_Ioi hz 0).mono' hm.aestronglyMeasurable
        (Eventually.of_forall fun u => le_of_eq ?_)
      rw [Complex.norm_exp, Complex.re_mul_ofReal]
    have h_ind : (fun u : ℝ => if 0 < u then Complex.exp (z * (u : ℂ)) else 0) =
        (Ioi (0 : ℝ)).indicator (fun u => Complex.exp (z * (u : ℂ))) := by
      funext u; by_cases hu : 0 < u <;> simp [hu]
    rw [h_ind]
    refine ⟨(integrable_indicator_iff measurableSet_Ioi).mpr hint_on, ?_⟩
    rw [integral_indicator measurableSet_Ioi]
    have hderiv : ∀ u : ℝ, HasDerivAt (fun s : ℝ => -(-z)⁻¹ * Complex.exp (z * (s : ℂ)))
        (Complex.exp (z * (u : ℂ))) u := by
      intro u
      have h1' : HasDerivAt (fun s : ℝ => z * (s : ℂ)) z u := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul z
      refine (h1'.cexp.const_mul (-(-z)⁻¹)).congr_deriv ?_
      rw [inv_neg, neg_neg, show z⁻¹ * (Complex.exp (z * (u : ℂ)) * z) =
        (z * z⁻¹) * Complex.exp (z * (u : ℂ)) by ring, mul_inv_cancel₀ hz0, one_mul]
    have hlim : Tendsto (fun s : ℝ => -(-z)⁻¹ * Complex.exp (z * (s : ℂ))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have htop : Tendsto (fun s : ℝ => (-z.re) * s) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (neg_pos.mpr hz) tendsto_id
      have hbot : Tendsto (fun s : ℝ => z.re * s) atTop atBot :=
        (tendsto_neg_atBot_iff.mpr (htop.congr fun s => by ring)).congr fun s => neg_neg _
      have hexp : Tendsto (fun s : ℝ => Real.exp (z.re * s)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hbot
      have hmul0 := hexp.const_mul ‖(-(-z)⁻¹ : ℂ)‖
      rw [mul_zero] at hmul0
      exact hmul0.congr fun s => by rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal]
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
      (fun u _ => hderiv u) hint_on hlim]
    simp
  have htail_expand : ∀ (z : ℂ) (u : ℝ),
      Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u =
        R₁ * (if 0 < u then Complex.exp ((p₁ - w) * (u : ℂ)) else 0) +
        R₂ * (if 0 < u then Complex.exp ((p₂ - w) * (u : ℂ)) else 0) +
        R₃ * (if 0 < u then Complex.exp ((p₃ - w) * (u : ℂ)) else 0) +
        R₄ * (if 0 < u then Complex.exp ((p₄ - w) * (u : ℂ)) else 0) := by
    intro _ u
    rcases le_or_gt u 0 with hu | hu
    · simp [quartetImpulseTail, not_lt.mpr hu]
    · simp only [quartetImpulseTail, if_pos hu]
      have he' : ∀ p_z : ℂ, Complex.exp (-w * (u : ℂ)) * Complex.exp (p_z * (u : ℂ)) =
          Complex.exp ((p_z - w) * (u : ℂ)) := fun p_z => by
        rw [← Complex.exp_add]; congr 1; ring
      dsimp only [a₁, a₂, b, p₁, p₂, p₃, p₄, c₁, c₂, d₁, d₂, R₁, R₂, R₃, R₄]
      linear_combination R₁ * he' p₁ + R₂ * he' p₂ + R₃ * he' p₃ + R₄ * he' p₄
  have htail_zero : ∀ u : ℝ, quartetImpulseTail σ γ u =
      R₁ * (if 0 < u then Complex.exp (p₁ * (u : ℂ)) else 0) +
      R₂ * (if 0 < u then Complex.exp (p₂ * (u : ℂ)) else 0) +
      R₃ * (if 0 < u then Complex.exp (p₃ * (u : ℂ)) else 0) +
      R₄ * (if 0 < u then Complex.exp (p₄ * (u : ℂ)) else 0) := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · simp [quartetImpulseTail, not_lt.mpr hu]
    · simp only [quartetImpulseTail, if_pos hu]
      dsimp only [a₁, a₂, b, p₁, p₂, p₃, p₄, c₁, c₂, d₁, d₂, R₁, R₂, R₃, R₄]
  have hint_0 : Integrable (quartetImpulseTail σ γ) := by
    have i1 := (hexp_lap p₁ (by simp [p₁]; linarith)).1.const_mul R₁
    have i2 := (hexp_lap p₂ (by simp [p₂]; linarith)).1.const_mul R₂
    have i3 := (hexp_lap p₃ (by simp [p₃]; linarith)).1.const_mul R₃
    have i4 := (hexp_lap p₄ (by simp [p₄]; linarith)).1.const_mul R₄
    exact (((i1.add i2).add i3).add i4).congr (Eventually.of_forall fun u => (htail_zero u).symm)
  have hre1 : (p₁ - w).re < 0 := by simp [p₁, a₁] at hw ⊢; linarith
  have hre2 : (p₂ - w).re < 0 := by simp [p₂, a₁] at hw ⊢; linarith
  have hre3 : (p₃ - w).re < 0 := by simp [p₃, a₂]; dsimp [a₁] at hw; linarith
  have hre4 : (p₄ - w).re < 0 := by simp [p₄, a₂]; dsimp [a₁] at hw; linarith
  obtain ⟨iw1, vw1⟩ := hexp_lap (p₁ - w) hre1
  obtain ⟨iw2, vw2⟩ := hexp_lap (p₂ - w) hre2
  obtain ⟨iw3, vw3⟩ := hexp_lap (p₃ - w) hre3
  obtain ⟨iw4, vw4⟩ := hexp_lap (p₄ - w) hre4
  have hint_w : Integrable fun u : ℝ => Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u :=
    ((((iw1.const_mul R₁).add (iw2.const_mul R₂)).add (iw3.const_mul R₃)).add
      (iw4.const_mul R₄)).congr (Eventually.of_forall fun u => (htail_expand 0 u).symm)
  refine ⟨hint_0, hint_w, ?_⟩
  rw [integral_congr_ae (Eventually.of_forall (htail_expand 0)),
    integral_add₄ (iw1.const_mul R₁) (iw2.const_mul R₂) (iw3.const_mul R₃) (iw4.const_mul R₄),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    vw1, vw2, vw3, vw4,
    show -(p₁ - w) = w - p₁ by ring, show -(p₂ - w) = w - p₂ by ring,
    show -(p₃ - w) = w - p₃ by ring, show -(p₄ - w) = w - p₄ by ring]
  -- Two-pair Blaschke partial-fraction identity
  have hgate4 := quartetGate_eq_blaschke_four' h0 hγ w
  set w₁ : ℂ := (a₁ : ℂ) + (b : ℂ) * I
  set w₂ : ℂ := (a₂ : ℂ) + (b : ℂ) * I
  have hib : 2 * I * (b : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (Complex.ofReal_ne_zero.mpr hb.ne')
  have hw1 : w - p₁ ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith [hre1]
  have hw2 : w - p₂ ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith [hre2]
  have hw3 : w - p₃ ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith [hre3]
  have hw4 : w - p₄ ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith [hre4]
  have hpair : ∀ (a : ℝ),
      let w_z : ℂ := (a : ℂ) + (b : ℂ) * I
      let q₁ : ℂ := -(a : ℂ) + (b : ℂ) * I
      let q₂ : ℂ := -(a : ℂ) - (b : ℂ) * I
      w - q₁ ≠ 0 → w - q₂ ≠ 0 →
      ((w - w_z) / (w + (starRingEnd ℂ) w_z)) * ((w - (starRingEnd ℂ) w_z) / (w + w_z)) =
        1 + (-(4 * (a : ℂ) * q₁) / (2 * I * (b : ℂ))) * (w - q₁)⁻¹ +
          ((4 * (a : ℂ) * q₂) / (2 * I * (b : ℂ))) * (w - q₂)⁻¹ := by
    intro a w_z q₁ q₂ hq1' hq2'
    have hd1 : w + (starRingEnd ℂ) w_z = w - q₁ := by
      simp [w_z, q₁, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have hd2 : w + w_z = w - q₂ := by simp [w_z, q₂]; ring
    rw [hd1, hd2, div_mul_div_comm]
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hq1' hq2') hib)
    have hlhs : ((w - w_z) * (w - (starRingEnd ℂ) w_z) / ((w - q₁) * (w - q₂))) *
        (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ))) =
        (w - w_z) * (w - (starRingEnd ℂ) w_z) * (2 * I * (b : ℂ)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ (mul_ne_zero hq1' hq2')]
    have hrhs1 : (-(4 * (a : ℂ) * q₁) / (2 * I * (b : ℂ))) * (w - q₁)⁻¹ *
        (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ))) = -(4 * (a : ℂ) * q₁) * (w - q₂) := by
      calc (-(4 * (a : ℂ) * q₁) / (2 * I * (b : ℂ))) * (w - q₁)⁻¹ *
              (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ)))
          = ((-(4 * (a : ℂ) * q₁) / (2 * I * (b : ℂ))) * (2 * I * (b : ℂ))) *
              ((w - q₁)⁻¹ * (w - q₁)) * (w - q₂) := by ring
        _ = -(4 * (a : ℂ) * q₁) * (w - q₂) := by
              rw [div_mul_cancel₀ _ hib, inv_mul_cancel₀ hq1', mul_one]
    have hrhs2 : ((4 * (a : ℂ) * q₂) / (2 * I * (b : ℂ))) * (w - q₂)⁻¹ *
        (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ))) = (4 * (a : ℂ) * q₂) * (w - q₁) := by
      calc ((4 * (a : ℂ) * q₂) / (2 * I * (b : ℂ))) * (w - q₂)⁻¹ *
              (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ)))
          = (((4 * (a : ℂ) * q₂) / (2 * I * (b : ℂ))) * (2 * I * (b : ℂ))) *
              ((w - q₂)⁻¹ * (w - q₂)) * (w - q₁) := by ring
        _ = (4 * (a : ℂ) * q₂) * (w - q₁) := by
              rw [div_mul_cancel₀ _ hib, inv_mul_cancel₀ hq2', mul_one]
    rw [hlhs, add_mul, add_mul, one_mul, hrhs1, hrhs2]
    simp only [w_z, q₁, q₂, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hres_mul : ∀ {u_p v_p : ℂ}, u_p ≠ v_p → w - u_p ≠ 0 → w - v_p ≠ 0 →
      (w - u_p)⁻¹ * (w - v_p)⁻¹ =
        (u_p - v_p)⁻¹ * (w - u_p)⁻¹ + (v_p - u_p)⁻¹ * (w - v_p)⁻¹ := by
    intro u_p v_p huv hwu hwv
    have h1' : u_p - v_p ≠ 0 := sub_ne_zero.mpr huv
    rw [show v_p - u_p = -(u_p - v_p) by ring, inv_neg]
    field_simp [h1', hwu, hwv]; ring
  have hp13 : p₁ ≠ p₃ := fun h => by have := congrArg Complex.re h; simp [p₁, p₃, a₁, a₂] at this; linarith
  have hp14 : p₁ ≠ p₄ := fun h => by have := congrArg Complex.re h; simp [p₁, p₄, a₁, a₂] at this; linarith
  have hp23 : p₂ ≠ p₃ := fun h => by have := congrArg Complex.re h; simp [p₂, p₃, a₁, a₂] at this; linarith
  have hp24 : p₂ ≠ p₄ := fun h => by have := congrArg Complex.re h; simp [p₂, p₄, a₁, a₂] at this; linarith
  rw [hgate4, show ((w - w₁) / (w + (starRingEnd ℂ) w₁)) * ((w - (starRingEnd ℂ) w₁) / (w + w₁)) *
      ((w - w₂) / (w + (starRingEnd ℂ) w₂)) * ((w - (starRingEnd ℂ) w₂) / (w + w₂)) =
    (((w - w₁) / (w + (starRingEnd ℂ) w₁)) * ((w - (starRingEnd ℂ) w₁) / (w + w₁))) *
      (((w - w₂) / (w + (starRingEnd ℂ) w₂)) * ((w - (starRingEnd ℂ) w₂) / (w + w₂))) by ring,
    hpair a₁ hw1 hw2, hpair a₂ hw3 hw4]
  have hm13 := hres_mul hp13 hw1 hw3
  have hm14 := hres_mul hp14 hw1 hw4
  have hm23 := hres_mul hp23 hw2 hw3
  have hm24 := hres_mul hp24 hw2 hw4
  simp only [R₁, R₂, R₃, R₄, div_eq_mul_inv]
  linear_combination -c₁ * d₁ * hm13 - c₁ * d₂ * hm14 - c₂ * d₁ * hm23 - c₂ * d₂ * hm24

/-- **Exact Single-Bounce + Degree-One Integral Euler-Gate Factorization of `quartetEchoKernel`.**
On `Re w > 1/2`, the Laplace transform of `quartetEchoKernel σ γ` factors into the Laplace
transform of the causal single-bounce kernel `quartetBounceKernel σ γ` times the infinite product
of the exact degree-one integral `ζ` gates `primeEchoGate p w` over all rational primes `p ∈ ℙ`. -/
theorem quartet_bounce_euler_factorization {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ)
    {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ v : ℝ, Complex.exp (-w * (v : ℂ)) * quartetBounceKernel σ γ v) =
      quartetGate σ γ w * Complex.betaIntegral w (1 / 2) ∧
    (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * quartetEchoKernel σ γ τ) =
      (∫ v : ℝ, Complex.exp (-w * (v : ℂ)) * quartetBounceKernel σ γ v) *
        (∏' p : Nat.Primes, primeEchoGate p w) := by
  have hw0 : 0 < w.re := by linarith
  have hw_tail : -((1 - σ) / 2) < w.re := by linarith
  obtain ⟨_, htail_w_int, htail_lap⟩ := integrable_and_laplace_quartetImpulseTail h0 h1 hγ hw_tail
  have hbw_int := integrable_bounceWave hw0
  have hbw_val := integral_bounceWave hw0
  have hconv_i : Integrable (fun p : ℝ × ℝ =>
      (Complex.exp (-w * (p.2 : ℂ)) * quartetImpulseTail σ γ p.2) *
        bounceWave w (p.1 - p.2)) (volume.prod volume) := by
    simpa using htail_w_int.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hbw_int
  have hpt_conv : ∀ v u : ℝ,
      Complex.exp (-w * (v : ℂ)) * (quartetImpulseTail σ γ u * bounceWave 0 (v - u)) =
        (Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u) * bounceWave w (v - u) := by
    intro v u
    by_cases hvu : 0 < v - u
    · simp only [bounceWave, if_pos hvu, neg_zero, zero_mul, Complex.exp_zero, one_mul]
      have hexp : Complex.exp (-w * (v : ℂ)) =
          Complex.exp (-w * (u : ℂ)) * Complex.exp (-w * ((v - u : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hexp]; ring
    · simp [bounceWave, hvu]
  have hpt_b0 : ∀ v : ℝ, Complex.exp (-w * (v : ℂ)) * bounceWave 0 v = bounceWave w v := by
    intro v
    by_cases hv : 0 < v <;> simp [bounceWave, hv]
  have hswap := integral_integral_swap
    (f := fun v u => (Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u) * bounceWave w (v - u))
    hconv_i
  have hint_conv : Integrable fun v : ℝ =>
      Complex.exp (-w * (v : ℂ)) * ∫ u : ℝ, quartetImpulseTail σ γ u * bounceWave 0 (v - u) := by
    refine hconv_i.integral_prod_left.congr (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => (hpt_conv v u).symm)
  have hval_conv : (∫ v : ℝ, Complex.exp (-w * (v : ℂ)) *
      ∫ u : ℝ, quartetImpulseTail σ γ u * bounceWave 0 (v - u)) =
      (quartetGate σ γ w - 1) * Complex.betaIntegral w (1 / 2) := by
    have hlhs : (∫ v : ℝ, Complex.exp (-w * (v : ℂ)) *
        ∫ u : ℝ, quartetImpulseTail σ γ u * bounceWave 0 (v - u)) =
        ∫ v : ℝ, ∫ u : ℝ, (Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u) *
          bounceWave w (v - u) := by
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun u => hpt_conv v u)
    rw [hlhs, hswap]
    have hinner : ∀ u : ℝ,
        (∫ v : ℝ, (Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u) * bounceWave w (v - u)) =
          (Complex.exp (-w * (u : ℂ)) * quartetImpulseTail σ γ u) * Complex.betaIntegral w (1 / 2) := by
      intro u
      rw [integral_const_mul, integral_sub_right_eq_self (bounceWave w) u, hbw_val]
    simp_rw [hinner]
    rw [integral_mul_const]
    congr 1
    linear_combination htail_lap
  have hbounce_lap : (∫ v : ℝ, Complex.exp (-w * (v : ℂ)) * quartetBounceKernel σ γ v) =
      quartetGate σ γ w * Complex.betaIntegral w (1 / 2) := by
    have hsplit : (fun v : ℝ => Complex.exp (-w * (v : ℂ)) * quartetBounceKernel σ γ v) =
        fun v : ℝ => bounceWave w v + Complex.exp (-w * (v : ℂ)) *
          ∫ u : ℝ, quartetImpulseTail σ γ u * bounceWave 0 (v - u) := by
      funext v; rw [quartetBounceKernel, mul_add, hpt_b0]
    rw [hsplit, integral_add hbw_int hint_conv, hbw_val, hval_conv]
    ring
  refine ⟨hbounce_lap, ?_⟩
  rw [hbounce_lap, laplace_quartetEchoKernel h0 h1 hγ hw,
    ← integral_cexp_mul_echoKernel_eq_completed hw,
    echoKernel_laplace_eq_beta_mul_tprod_primeEchoGate hw, mul_assoc]

/-! ### Dressed Pulse Bounce, Finite Return Sum, Möbius Inversion, and Prime-Sector Recurrence -/

/-- Causal single-bounce response of a compact pulse `h` in `xiQuartet σ γ`. -/
def quartetBounce (σ γ : ℝ) (h : CompactPulse) (u : ℝ) : ℂ :=
  ReturnCancellation.bounce h u +
    ∫ v : ℝ, quartetImpulseTail σ γ v * ReturnCancellation.bounce h (u - v)

/-- Individual denominator-`c` path return with exact totient weight `φ(c)/c` and delay `2 log c`. -/
def quartetPath (σ γ : ℝ) (h : CompactPulse) (c : ℕ) (t : ℝ) : ℂ :=
  (echoWeight c : ℂ) * quartetBounce σ γ h (t - echoDelay c)

/-- Dressed mean coefficient `quartetGate σ γ (1/2) * meanCoefficient h`. -/
def quartetMeanCoeff (σ γ : ℝ) (h : CompactPulse) : ℂ :=
  quartetGate σ γ (1 / 2) * meanCoefficient h

/-- Full time-domain echo response `quartetReflected + quartetMeanCoeff * e^{t/2}`. -/
def quartetPulseEcho (σ γ : ℝ) (h : CompactPulse) (t : ℝ) : ℂ :=
  quartetReflected σ γ h t + quartetMeanCoeff σ γ h * Complex.exp ((t : ℂ) / 2)

private theorem bounce_eq_zero_of_le_neg_support (h : CompactPulse) {S : ℝ}
    (hs : ∀ s : ℝ, S < |s| → h s = 0) {u : ℝ} (hu : u ≤ -S) :
    ReturnCancellation.bounce h u = 0 := by
  unfold ReturnCancellation.bounce
  refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
  have hv_pos : (0 : ℝ) < v := hv
  have hgt : S < |u - v| := lt_of_lt_of_le (by linarith) (neg_le_abs _)
  rw [hs _ hgt, zero_mul]

private theorem quartetBounce_eq_zero_of_le_neg_support (σ γ : ℝ) (h : CompactPulse) {S : ℝ}
    (hs : ∀ s : ℝ, S < |s| → h s = 0) {u : ℝ} (hu : u ≤ -S) :
    quartetBounce σ γ h u = 0 := by
  rw [quartetBounce, bounce_eq_zero_of_le_neg_support h hs hu, zero_add]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun v => ?_)
  dsimp only [Pi.zero_apply]
  rcases le_or_gt v 0 with hv | hv
  · simp [quartetImpulseTail, not_lt.mpr hv]
  · rw [bounce_eq_zero_of_le_neg_support h hs (by linarith), mul_zero]

private theorem quartetPath_eq_zero_outside_cutoff (σ γ : ℝ) (h : CompactPulse) {S : ℝ}
    (hs : ∀ s : ℝ, S < |s| → h s = 0) (t : ℝ) {c : ℕ}
    (hc : c ∉ Finset.Icc 1 (pathReturnCutoff (t + S))) :
    quartetPath σ γ h c t = 0 := by
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · simp [quartetPath, echoWeight]
  have hc' : pathReturnCutoff (t + S) < c :=
    lt_of_not_ge fun hle => hc (Finset.mem_Icc.mpr ⟨hpos, hle⟩)
  have he := (Nat.le_ceil (Real.exp ((t + S) / 2))).trans (Nat.cast_le.mpr hc'.le)
  have hl := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hpos)).mpr he
  rw [quartetPath, quartetBounce_eq_zero_of_le_neg_support σ γ h hs
    (by unfold echoDelay; linarith only [hl]), mul_zero]

private theorem integrable_tail_mul_bounce {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hγ : 0 < γ) (h : CompactPulse) (u : ℝ) :
    Integrable fun v : ℝ => quartetImpulseTail σ γ v * ReturnCancellation.bounce h (u - v) := by
  obtain ⟨S, hS_nn, hs⟩ := h.exists_support_bound
  obtain ⟨htail_int, _, _⟩ :=
    integrable_and_laplace_quartetImpulseTail h0 h1 hγ (w := 0) (by simp; linarith)
  -- Uniform bound and continuity of `bounce h` on `(-∞, u]` via compact support truncation to `(0, R)`
  have hcont_h : Continuous h.toFun := h.smooth.continuous
  obtain ⟨Mh, hMh_nn, hMh⟩ : ∃ Mh : ℝ, 0 ≤ Mh ∧ ∀ x : ℝ, ‖h x‖ ≤ Mh := by
    have hcomp : IsCompact (Icc (-S) S) := isCompact_Icc
    by_cases hne : (Icc (-S) S).Nonempty
    · obtain ⟨x₀, _, hx₀⟩ := hcomp.exists_isMaxOn hne hcont_h.norm.continuousOn
      refine ⟨‖h x₀‖, norm_nonneg _, fun x => ?_⟩
      by_cases hx : |x| ≤ S
      · exact hx₀ (abs_le.mp hx)
      · push Not at hx; rw [hs x hx, norm_zero]; exact norm_nonneg _
    · refine ⟨0, le_rfl, fun x => ?_⟩
      have : S < |x| := by
        by_contra hle; push Not at hle; exact hne ⟨x, abs_le.mp hle⟩
      rw [hs x this, norm_zero]
  set R : ℝ := max (u + S) 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbk_int : IntegrableOn (fun w : ℝ => bounceKernel w) (Ioo 0 R) := by
    have hbw1 := (integrableOn_and_integral_bounce (w := 1) (by norm_num)).1
    have hsub : IntegrableOn (fun w : ℝ => Complex.exp (-(1 : ℂ) * (w : ℂ)) *
        ((bounceKernel w : ℝ) : ℂ)) (Ioo 0 R) := hbw1.mono_set Ioo_subset_Ioi_self
    refine ((hsub.norm).const_mul (Real.exp R)).mono'
      (measurable_bounceKernel.aestronglyMeasurable.restrict)
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun w hw => ?_))
    have hbk_pos : 0 ≤ bounceKernel w := by
      unfold bounceKernel
      have : Real.exp (-w) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hw.1])
      positivity
    rw [Real.norm_of_nonneg hbk_pos, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_of_nonneg hbk_pos, show (-(1 : ℂ) * (w : ℂ)).re = -w by simp, ← mul_assoc,
      ← Real.exp_add]
    exact le_mul_of_one_le_left hbk_pos (Real.one_le_exp (by linarith [hw.2]))
  set Kb : ℝ := Mh * ∫ w in Ioo 0 R, bounceKernel w
  have hbounce_le : ∀ x : ℝ, x ≤ u → ‖ReturnCancellation.bounce h x‖ ≤ Kb := by
    intro x hx
    have hsupp_w : ReturnCancellation.bounce h x =
        ∫ w in Ioo 0 R, h (x - w) * ((bounceKernel w : ℝ) : ℂ) := by
      unfold ReturnCancellation.bounce
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      by_cases hw0 : 0 < w
      · by_cases hwR : w < R
        · rw [indicator_of_mem hw0, indicator_of_mem ⟨hw0, hwR⟩]
        · push Not at hwR
          have hgt : S < |x - w| := by
            have : u + S ≤ R := le_max_left _ _
            exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
          rw [indicator_of_mem hw0, indicator_of_notMem (fun hm => hwR.not_gt hm.2),
            hs _ hgt, zero_mul]
      · rw [indicator_of_notMem hw0, indicator_of_notMem (fun hm => hw0 hm.1)]
    rw [hsupp_w]
    calc ‖∫ w in Ioo 0 R, h (x - w) * ((bounceKernel w : ℝ) : ℂ)‖
        ≤ ∫ w in Ioo 0 R, Mh * bounceKernel w := by
          refine norm_integral_le_of_norm_le (hbk_int.const_mul Mh) ?_
          refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun w hw => ?_)
          have hbk_pos : 0 ≤ bounceKernel w := by
            unfold bounceKernel
            have : Real.exp (-w) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hw.1])
            positivity
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hbk_pos]
          exact mul_le_mul_of_nonneg_right (hMh _) hbk_pos
      _ = Kb := integral_const_mul _ _
  have hcont_b : ContinuousOn (fun x : ℝ => ReturnCancellation.bounce h x) (Iic u) := by
    have heq_on : EqOn (fun x : ℝ => ∫ w in Ioo 0 R, h (x - w) * ((bounceKernel w : ℝ) : ℂ))
        (fun x : ℝ => ReturnCancellation.bounce h x) (Iic u) := by
      intro x hx
      dsimp only
      unfold ReturnCancellation.bounce
      rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioi]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      by_cases hw0 : 0 < w
      · by_cases hwR : w < R
        · rw [indicator_of_mem ⟨hw0, hwR⟩, indicator_of_mem hw0]
        · push Not at hwR
          have hgt : S < |x - w| := by
            have : u + S ≤ R := le_max_left _ _
            have hxu : x ≤ u := hx
            exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
          rw [indicator_of_notMem (fun hm => hwR.not_gt hm.2), indicator_of_mem hw0,
            hs _ hgt, zero_mul]
      · rw [indicator_of_notMem (fun hm => hw0 hm.1), indicator_of_notMem hw0]
    have hcont_int : Continuous fun x : ℝ =>
        ∫ w in Ioo 0 R, h (x - w) * ((bounceKernel w : ℝ) : ℂ) := by
      refine continuous_of_dominated (bound := fun w => Mh * bounceKernel w) ?_ ?_
        (hbk_int.const_mul Mh) ?_
      · intro x
        exact ((hcont_h.comp (continuous_const.sub continuous_id)).measurable.mul
          (Complex.measurable_ofReal.comp measurable_bounceKernel)).aestronglyMeasurable.restrict
      · intro x
        refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun w hw => ?_)
        have hbk_pos : 0 ≤ bounceKernel w := by
          unfold bounceKernel
          have : Real.exp (-w) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hw.1])
          positivity
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hbk_pos]
        exact mul_le_mul_of_nonneg_right (hMh _) hbk_pos
      · exact Eventually.of_forall fun w => by fun_prop
    exact hcont_int.continuousOn.congr heq_on.symm
  have hmeas_prod : AEStronglyMeasurable
      (fun v : ℝ => quartetImpulseTail σ γ v * ReturnCancellation.bounce h (u - v)) volume := by
    have heq : (fun v : ℝ => quartetImpulseTail σ γ v * ReturnCancellation.bounce h (u - v)) =
        fun v : ℝ => quartetImpulseTail σ γ v *
          (Ici (0 : ℝ)).indicator (fun v' => ReturnCancellation.bounce h (u - v')) v := by
      funext v
      rcases le_or_gt 0 v with hv | hv
      · rw [indicator_of_mem hv]
      · simp [quartetImpulseTail, not_lt.mpr hv.le]
    rw [heq]
    have hcont_ind : ContinuousOn (fun v' : ℝ => ReturnCancellation.bounce h (u - v')) (Ici 0) :=
      hcont_b.comp (continuous_const.sub continuous_id).continuousOn fun v' hv' => by
        show u - v' ≤ u; have : (0 : ℝ) ≤ v' := hv'; linarith
    exact htail_int.aestronglyMeasurable.mul
      ((aestronglyMeasurable_indicator_iff measurableSet_Ici).mpr
        (hcont_ind.aestronglyMeasurable measurableSet_Ici))
  refine (htail_int.norm.const_mul Kb).mono' hmeas_prod (Eventually.of_forall fun v => ?_)
  rcases le_or_gt v 0 with hv | hv
  · simp [quartetImpulseTail, not_lt.mpr hv]
  · rw [norm_mul, mul_comm Kb]
    exact mul_le_mul_of_nonneg_left (hbounce_le (u - v) (by linarith)) (norm_nonneg _)

/-- **Exact Finite Return Expansion of `xiQuartet σ γ`.**
Every compact pulse `h` supported in `[-S, S]` obeys the exact finite totient-weighted return
expansion up to `pathReturnCutoff (B + S)` for all `t ≤ B`. -/
theorem quartet_finite_return_sum {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ)
    (h : CompactPulse) {S B t : ℝ} (hs : ∀ s : ℝ, S < |s| → h s = 0) (ht : t ≤ B) :
    ∑ c ∈ Finset.Icc 1 (pathReturnCutoff (B + S)), quartetPath σ γ h c t =
      quartetReflected σ γ h t + quartetMeanCoeff σ γ h * Complex.exp ((t : ℂ) / 2) := by
  set F : Finset ℕ := Finset.Icc 1 (pathReturnCutoff (B + S))
  have hpath_split : ∀ c ∈ F, quartetPath σ γ h c t =
      ReturnCancellation.path h c t +
        ∫ v : ℝ, quartetImpulseTail σ γ v * ReturnCancellation.path h c (t - v) := by
    intro c _
    rw [quartetPath, quartetBounce, mul_add, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only [ReturnCancellation.path]
    rw [show t - v - echoDelay c = t - echoDelay c - v by ring]
    ring
  rw [Finset.sum_congr rfl hpath_split, Finset.sum_add_distrib,
    ReturnCancellation.finite_return_sum h hs ht,
    ← integral_finsetSum F fun c _ =>
      ((integrable_tail_mul_bounce h0 h1 hγ h (t - echoDelay c)).const_mul (echoWeight c : ℂ)).congr
        (Eventually.of_forall fun v => by
          dsimp only [ReturnCancellation.path]
          rw [show t - v - echoDelay c = t - echoDelay c - v by ring]; ring)]
  -- Inside the integral, `quartetImpulseTail σ γ v = 0` for `v ≤ 0`, while for `v > 0`, `t - v ≤ B`!
  have hinner_sum : ∀ v : ℝ,
      quartetImpulseTail σ γ v * (∑ c ∈ F, ReturnCancellation.path h c (t - v)) =
        quartetImpulseTail σ γ v * pulseReflected h (t - v) +
          quartetImpulseTail σ γ v *
            (meanCoefficient h * Complex.exp (((t - v : ℝ) : ℂ) / 2)) := by
    intro v
    rcases le_or_gt v 0 with hv | hv
    · simp [quartetImpulseTail, not_lt.mpr hv]
    · rw [ReturnCancellation.finite_return_sum h hs (by linarith : t - v ≤ B), mul_add]
  have hsum_push : ∀ v : ℝ,
      (∑ c ∈ F, quartetImpulseTail σ γ v * ReturnCancellation.path h c (t - v)) =
        quartetImpulseTail σ γ v * (∑ c ∈ F, ReturnCancellation.path h c (t - v)) :=
    fun v => (Finset.mul_sum _ _ _).symm
  simp_rw [hsum_push, hinner_sum]
  obtain ⟨htail_int, _, _⟩ :=
    integrable_and_laplace_quartetImpulseTail h0 h1 hγ (w := 0) (by simp; linarith)
  obtain ⟨_, htail_half_int, htail_half_val⟩ :=
    integrable_and_laplace_quartetImpulseTail h0 h1 hγ (w := (1 / 2 : ℂ))
      (by simp; linarith)
  -- Integrability of the two terms on `v`
  have hint_mean : Integrable fun v : ℝ =>
      quartetImpulseTail σ γ v * (meanCoefficient h * Complex.exp (((t - v : ℝ) : ℂ) / 2)) := by
    have heq : (fun v : ℝ =>
        quartetImpulseTail σ γ v * (meanCoefficient h * Complex.exp (((t - v : ℝ) : ℂ) / 2))) =
        fun v : ℝ => (meanCoefficient h * Complex.exp ((t : ℂ) / 2)) *
          (Complex.exp (-(1 / 2 : ℂ) * (v : ℂ)) * quartetImpulseTail σ γ v) := by
      funext v
      have hexp : Complex.exp (((t - v : ℝ) : ℂ) / 2) =
          Complex.exp ((t : ℂ) / 2) * Complex.exp (-(1 / 2 : ℂ) * (v : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hexp]; ring
    rw [heq]; exact htail_half_int.const_mul _
  have hval_mean : meanCoefficient h * Complex.exp ((t : ℂ) / 2) +
      (∫ v : ℝ, quartetImpulseTail σ γ v *
        (meanCoefficient h * Complex.exp (((t - v : ℝ) : ℂ) / 2))) =
      quartetMeanCoeff σ γ h * Complex.exp ((t : ℂ) / 2) := by
    have heq : (fun v : ℝ =>
        quartetImpulseTail σ γ v * (meanCoefficient h * Complex.exp (((t - v : ℝ) : ℂ) / 2))) =
        fun v : ℝ => (meanCoefficient h * Complex.exp ((t : ℂ) / 2)) *
          (Complex.exp (-(1 / 2 : ℂ) * (v : ℂ)) * quartetImpulseTail σ γ v) := by
      funext v
      have hexp : Complex.exp (((t - v : ℝ) : ℂ) / 2) =
          Complex.exp ((t : ℂ) / 2) * Complex.exp (-(1 / 2 : ℂ) * (v : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hexp]; ring
    rw [heq, integral_const_mul, quartetMeanCoeff]
    linear_combination (meanCoefficient h * Complex.exp ((t : ℂ) / 2)) * htail_half_val
  -- Fubini on `pulseReflected h (t - v)` and `(v, ξ)`
  have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
    ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
  set G : ℝ × ℝ → ℂ := fun p =>
    quartetImpulseTail σ γ p.1 *
      (pulseAmplitude h (p.2 : ℂ) * scatteringPhase ((p.2 : ℂ) * I) *
        Complex.exp (I * (p.2 : ℂ) * ((t - p.1 : ℝ) : ℂ)))
  have hG_meas : AEStronglyMeasurable G (volume.prod volume) := by
    have hm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => quartetImpulseTail σ γ p.1)
        (volume.prod volume) := htail_int.aestronglyMeasurable.comp_fst
    have hcont2 : Continuous fun p : ℝ × ℝ =>
        pulseAmplitude h (p.2 : ℂ) * scatteringPhase ((p.2 : ℂ) * I) *
          Complex.exp (I * (p.2 : ℂ) * ((t - p.1 : ℝ) : ℂ)) := by
      have hc1 : Continuous fun p : ℝ × ℝ => pulseAmplitude h (p.2 : ℂ) :=
        h.differentiable_amplitude.continuous.comp (Complex.continuous_ofReal.comp continuous_snd)
      have hc2 : Continuous fun p : ℝ × ℝ => scatteringPhase ((p.2 : ℂ) * I) :=
        continuous_scatteringPhase_line.comp continuous_snd
      have hc3 : Continuous fun p : ℝ × ℝ => Complex.exp (I * (p.2 : ℂ) * ((t - p.1 : ℝ) : ℂ)) := by
        fun_prop
      exact (hc1.mul hc2).mul hc3
    exact hm1.mul hcont2.aestronglyMeasurable
  have hG_int : Integrable G (volume.prod volume) := by
    refine (htail_int.norm.smul_prod hint_a).mono' hG_meas (Eventually.of_forall fun p => ?_)
    dsimp only [G]
    rw [smul_eq_mul, norm_mul, norm_mul, norm_mul, norm_scatteringPhase_line, mul_one,
      norm_exp_I_mul, mul_one]
  have hint_refl : Integrable fun v : ℝ => quartetImpulseTail σ γ v * pulseReflected h (t - v) := by
    refine hG_int.integral_prod_left.congr (Eventually.of_forall fun v => ?_)
    dsimp only [G]
    unfold pulseReflected unitaryReflected
    exact (integral_const_mul _ _).symm
  have hval_refl : pulseReflected h t +
      (∫ v : ℝ, quartetImpulseTail σ γ v * pulseReflected h (t - v)) =
      quartetReflected σ γ h t := by
    have hlhs : (∫ v : ℝ, quartetImpulseTail σ γ v * pulseReflected h (t - v)) =
        ∫ v : ℝ, ∫ ξ : ℝ, G (v, ξ) := by
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only [G]
      unfold pulseReflected unitaryReflected
      exact (integral_const_mul _ _).symm
    rw [hlhs, integral_integral_swap (f := fun v ξ => G (v, ξ)) hG_int]
    have hinner_ξ : ∀ ξ : ℝ, (∫ v : ℝ, G (v, ξ)) =
        pulseAmplitude h (ξ : ℂ) * ((quartetGate σ γ ((ξ : ℂ) * I) - 1) *
          scatteringPhase ((ξ : ℂ) * I)) * Complex.exp (I * (ξ : ℂ) * (t : ℂ)) := by
      intro ξ
      obtain ⟨_, _, hlap_ξ⟩ := integrable_and_laplace_quartetImpulseTail h0 h1 hγ
        (w := (ξ : ℂ) * I) (by simp; linarith)
      have hpt : ∀ v : ℝ, G (v, ξ) =
          (pulseAmplitude h (ξ : ℂ) * scatteringPhase ((ξ : ℂ) * I) *
            Complex.exp (I * (ξ : ℂ) * (t : ℂ))) *
          (Complex.exp (-(((ξ : ℂ) * I)) * (v : ℂ)) * quartetImpulseTail σ γ v) := by
        intro v
        dsimp only [G]
        have hexp : Complex.exp (I * (ξ : ℂ) * ((t - v : ℝ) : ℂ)) =
            Complex.exp (I * (ξ : ℂ) * (t : ℂ)) *
              Complex.exp (-(((ξ : ℂ) * I)) * (v : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hexp]; ring
      simp_rw [hpt]
      rw [integral_const_mul]
      linear_combination (pulseAmplitude h (ξ : ℂ) * scatteringPhase ((ξ : ℂ) * I) *
        Complex.exp (I * (ξ : ℂ) * (t : ℂ))) * hlap_ξ
    simp_rw [hinner_ξ]
    have hint_mod := h.integrable_amplitude_mul continuous_scatteringPhase_line.measurable
      (fun ξ => (norm_scatteringPhase_line ξ).le) t
    obtain ⟨_, hunit⟩ := quartet_schur_and_unitary h0 h1 hγ
    have hcont_q := continuous_quartetScatteringPhase_line h0 h1 hγ
    have hint_diff : Integrable fun ξ : ℝ =>
        pulseAmplitude h (ξ : ℂ) * ((quartetGate σ γ ((ξ : ℂ) * I) - 1) *
          scatteringPhase ((ξ : ℂ) * I)) * Complex.exp (I * (ξ : ℂ) * (t : ℂ)) := by
      have hint_q := h.integrable_amplitude_mul hcont_q.measurable (fun ξ => (hunit ξ).2.le) t
      refine (hint_q.sub hint_mod).congr (Eventually.of_forall fun ξ => ?_)
      dsimp only
      have hph : quartetScatteringPhase σ γ ((ξ : ℂ) * I) =
          quartetGate σ γ ((ξ : ℂ) * I) * scatteringPhase ((ξ : ℂ) * I) := by
        unfold quartetScatteringPhase quartetReducedScattering xiQuartet quartetGate scatteringPhase
        ring
      rw [hph]; ring
    rw [pulseReflected, ← integral_add hint_mod hint_diff, quartetReflected, unitaryReflected]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    have hph : quartetScatteringPhase σ γ ((ξ : ℂ) * I) =
        quartetGate σ γ ((ξ : ℂ) * I) * scatteringPhase ((ξ : ℂ) * I) := by
      unfold quartetScatteringPhase quartetReducedScattering xiQuartet quartetGate scatteringPhase
      ring
    rw [hph]; ring
  rw [integral_add hint_refl hint_mean]
  linear_combination hval_refl + hval_mean

/-- **Exact Möbius Scattering Returns on `xiQuartet σ γ`.**
Möbius-weighted delayed observations of `quartetPulseEcho σ γ` recover `μ(n)/n` times the causal
dressed single-bounce `quartetBounce σ γ`, identically as on `ζ`. -/
theorem quartet_mobius_scattering_returns {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ)
    (h : CompactPulse) (B : ℝ) :
    ∃ N : ℕ, ∀ t ≤ B,
      (∑ d ∈ Finset.Icc 1 N, (μ d : ℂ) * quartetPulseEcho σ γ h (t - echoDelay d)) =
        ∑ n ∈ Finset.Icc 1 N, ((μ n : ℂ) / n) * quartetBounce σ γ h (t - echoDelay n) := by
  obtain ⟨S, _, hs⟩ := h.exists_support_bound
  set N : ℕ := pathReturnCutoff (B + S)
  refine ⟨N, fun t ht => ?_⟩
  set J : Finset ℕ := Finset.Icc 1 N
  set U : Finset (ℕ × ℕ) := (J ×ˢ J).filter fun p => p.1 * p.2 ≤ N
  set W : ℕ × ℕ → ℂ := fun p =>
    (μ p.1 : ℂ) * (echoWeight p.2 : ℂ) * quartetBounce σ γ h (t - echoDelay (p.1 * p.2))
  have habove : ∀ {n : ℕ}, N < n → quartetBounce σ γ h (t - echoDelay n) = 0 := by
    intro n hn
    have hp := Nat.zero_lt_of_lt hn
    have hexp := (Nat.le_ceil (Real.exp ((B + S) / 2))).trans (Nat.cast_le.mpr hn.le)
    have hlog := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hp)).mpr hexp
    exact quartetBounce_eq_zero_of_le_neg_support σ γ h hs (by unfold echoDelay; linarith)
  have hfibres : ∀ n ∈ J, U.filter (fun p => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
    intro n hn
    ext p
    rw [mem_filter, Nat.mem_divisorsAntidiagonal]
    constructor
    · exact fun hp => ⟨hp.2, Nat.ne_of_gt (mem_Icc.mp hn).1⟩
    · rintro ⟨he, hn0⟩
      have hx : 0 < p.1 := Nat.pos_of_ne_zero fun hz => hn0 (by simpa [hz] using he.symm)
      have hy : 0 < p.2 := Nat.pos_of_ne_zero fun hz => hn0 (by simpa [hz] using he.symm)
      have hxn : p.1 ≤ n := Nat.le_of_dvd (mem_Icc.mp hn).1 ⟨p.2, he.symm⟩
      have hyn : p.2 ≤ n := Nat.le_of_dvd (mem_Icc.mp hn).1 ⟨p.1, by rw [← he, Nat.mul_comm]⟩
      exact ⟨mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_Icc.mpr ⟨hx, hxn.trans (mem_Icc.mp hn).2⟩,
          mem_Icc.mpr ⟨hy, hyn.trans (mem_Icc.mp hn).2⟩⟩,
        he.trans_le (mem_Icc.mp hn).2⟩, he⟩
  have hmap : ∀ p ∈ U, p.1 * p.2 ∈ J := by
    intro p hp
    obtain ⟨hp', hle⟩ := mem_filter.mp hp
    obtain ⟨h₁, h₂⟩ := mem_product.mp hp'
    exact mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp h₁).1 (mem_Icc.mp h₂).1, hle⟩
  have hzero : ∀ p ∈ J ×ˢ J, p ∉ U → W p = 0 := by
    intro p hp hn
    have hlate : N < p.1 * p.2 := lt_of_not_ge fun hle => hn (mem_filter.mpr ⟨hp, hle⟩)
    simp only [W, habove hlate, mul_zero]
  have hinv : ∀ n : ℕ, 0 < n →
      ∑ z ∈ n.divisorsAntidiagonal, (μ z.1 : ℂ) * (echoWeight z.2 : ℂ) = (μ n : ℂ) / n := by
    intro n hn
    apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun a => (μ a : ℂ) / a) (g := fun a => (echoWeight a : ℂ))).mp _ n hn
    intro m hm
    exact_mod_cast _root_.RHTower.Sieve.sum_moebius_div_divisors_eq_totient_div hm
  calc (∑ d ∈ J, (μ d : ℂ) * quartetPulseEcho σ γ h (t - echoDelay d))
      = ∑ d ∈ J, (μ d : ℂ) * ∑ c ∈ J, quartetPath σ γ h c (t - echoDelay d) := by
          refine sum_congr rfl fun d hd => congrArg ((μ d : ℂ) * ·) ?_
          have hd0 : 0 ≤ echoDelay d := echoDelay_nonneg d
          exact (quartet_finite_return_sum h0 h1 hγ h hs (by linarith : t - echoDelay d ≤ B)).symm
    _ = ∑ p ∈ J ×ˢ J, W p := by
          rw [sum_product]
          refine sum_congr rfl fun d hd => ?_
          rw [mul_sum]
          refine sum_congr rfl fun c hc => ?_
          dsimp only [W, quartetPath]
          have hdel : echoDelay (d * c) = echoDelay d + echoDelay c := by
            rw [echoDelay, Nat.cast_mul, Real.log_mul
              (Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hd).1; omega))
              (Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hc).1; omega))]
            unfold echoDelay; ring
          rw [hdel, sub_add_eq_sub_sub, mul_assoc]
    _ = ∑ p ∈ U, W p := (sum_subset (filter_subset _ _) hzero).symm
    _ = ∑ n ∈ J, ∑ z ∈ n.divisorsAntidiagonal, W z := by
          rw [← sum_fiberwise_of_maps_to hmap W]
          exact sum_congr rfl fun n hn => by rw [hfibres n hn]
    _ = ∑ n ∈ J, ((μ n : ℂ) / n) * quartetBounce σ γ h (t - echoDelay n) := by
          refine sum_congr rfl fun n hn => ?_
          rw [← hinv n (mem_Icc.mp hn).1, sum_mul]
          exact sum_congr rfl fun z hz => by simp only [W, (Nat.mem_divisorsAntidiagonal.mp hz).1]

/-- All other paths at arrival `echoDelay c + u` in `xiQuartet σ γ`, after subtracting the mean. -/
def quartetOthers (σ γ : ℝ) (h : CompactPulse) (S u : ℝ) (c : ℕ) : ℂ :=
  (∑ m ∈ (ReturnCancellation.denominators S u c).erase c,
    quartetPath σ γ h m (echoDelay c + u)) -
    quartetMeanCoeff σ γ h * Complex.exp (((echoDelay c + u : ℝ) : ℂ) / 2)

/-- Exact single-return erasure identity in `xiQuartet σ γ`. -/
theorem quartet_erase_one_return {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ)
    (h : CompactPulse) {S : ℝ} (hS : 0 ≤ S) (hs : ∀ s : ℝ, S < |s| → h s = 0)
    (u : ℝ) {c : ℕ} (hc : 0 < c) :
    quartetOthers σ γ h S u c + (echoWeight c : ℂ) * quartetBounce σ γ h u =
      quartetReflected σ γ h (echoDelay c + u) := by
  have hmem : c ∈ ReturnCancellation.denominators S u c := by
    refine mem_Icc.mpr ⟨hc, ?_⟩
    have hc' : (0 : ℝ) < c := Nat.cast_pos.mpr hc
    have he : (c : ℝ) ≤ Real.exp ((echoDelay c + max u 0 + S) / 2) := by
      calc (c : ℝ) = Real.exp (Real.log c) := (Real.exp_log hc').symm
        _ ≤ _ := Real.exp_le_exp.mpr (by unfold echoDelay; linarith only [le_max_right u 0, hS])
    exact Nat.cast_le.mp (he.trans (Nat.le_ceil _))
  have he := quartet_finite_return_sum h0 h1 hγ h hs
    (by linarith only [le_max_left u 0] : echoDelay c + u ≤ echoDelay c + max u 0)
  change (∑ m ∈ ReturnCancellation.denominators S u c, quartetPath σ γ h m (echoDelay c + u)) = _ at he
  rw [← sum_erase_add _ _ hmem] at he
  have hpath : quartetPath σ γ h c (echoDelay c + u) =
      (echoWeight c : ℂ) * quartetBounce σ γ h u := by
    rw [quartetPath, add_sub_cancel_left]
  rw [hpath] at he
  unfold quartetOthers
  linear_combination he

/-- Denominator-`q` multiple echo sector in `xiQuartet σ γ`. -/
def quartetMultipleEcho (σ γ : ℝ) (h : CompactPulse) (q : ℕ) (t : ℝ) : ℂ :=
  ∑' a : ℕ, quartetPath σ γ h (q * a) t

/-- Centered prime-`p` sector wavepacket in `xiQuartet σ γ`. -/
def quartetCenteredPrimeSector (σ γ : ℝ) (h : CompactPulse) (p : ℕ) (u : ℝ) : ℂ :=
  quartetMultipleEcho σ γ h p (echoDelay p + u) -
    ((p : ℂ) / (p + 1)) * quartetMeanCoeff σ γ h * Complex.exp ((u : ℂ) / 2)

/-- Late-time `L²` tail energy of the `p`-sector in `xiQuartet σ γ`. -/
def quartetSectorTailEnergy (σ γ : ℝ) (p : ℕ) (h : CompactPulse) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi T, ENNReal.ofReal (‖quartetCenteredPrimeSector σ γ h p u‖ ^ 2)

private theorem echoWeight_prime_mul' {p : ℕ} (hp : p.Prime) (a : ℕ) :
    echoWeight (p * a) = if p ∣ a then echoWeight a else (1 - 1 / (p : ℝ)) * echoWeight a := by
  have hp0 := (Nat.cast_pos.mpr hp.pos : (0 : ℝ) < p).ne'
  unfold echoWeight
  rw [Nat.cast_mul]
  split_ifs with hd
  · rw [Nat.totient_mul_of_prime_of_dvd hp hd, Nat.cast_mul, mul_div_mul_left _ _ hp0]
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
    by_cases ha : a = 0
    · subst a; simp
    field_simp [hp0, (by exact_mod_cast ha : (a : ℝ) ≠ 0)]

private theorem quartetPath_prime_tower (σ γ : ℝ) (h : CompactPulse) {p : ℕ} (hp : p.Prime)
    (k a : ℕ) (u : ℝ) :
    quartetPath σ γ h (p ^ (k + 1) * a) (echoDelay (p ^ (k + 1)) + u) =
      (echoWeight (p * a) : ℂ) * quartetBounce σ γ h (u - echoDelay a) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [quartetPath, echoWeight]
  have hw : echoWeight (p ^ (k + 1) * a) = echoWeight (p * a) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, echoWeight_prime_mul' hp, if_pos, ih]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  have hdel : echoDelay (p ^ (k + 1) * a) = echoDelay (p ^ (k + 1)) + echoDelay a := by
    rw [echoDelay, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (pow_pos hp.pos _).ne') (by exact_mod_cast ha.ne')]
    unfold echoDelay; ring
  rw [quartetPath, hw, hdel]
  congr 2; ring

/-- Exact prime-power sector repetition in `xiQuartet σ γ`. -/
theorem quartet_repeated_prime_sector (σ γ : ℝ) (h : CompactPulse) {p : ℕ} (hp : p.Prime)
    (k : ℕ) (u : ℝ) :
    quartetMultipleEcho σ γ h (p ^ (k + 1)) (echoDelay (p ^ (k + 1)) + u) =
      quartetMultipleEcho σ γ h p (echoDelay p + u) := by
  unfold quartetMultipleEcho
  exact tsum_congr fun a => (quartetPath_prime_tower σ γ h hp k a u).trans
    (by simpa using (quartetPath_prime_tower σ γ h hp 0 a u).symm)

/-- **Bounce-Agnostic Centered Prime-Sector Delay Recurrence on `xiQuartet σ γ`.** -/
theorem quartet_centered_sector_delay {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ)
    (h : CompactPulse) {p : ℕ} (hp : p.Prime) (u : ℝ) :
    quartetCenteredPrimeSector σ γ h p u =
      (1 - 1 / (p : ℂ)) * quartetReflected σ γ h u +
        (1 / (p : ℂ)) * quartetCenteredPrimeSector σ γ h p (u - echoDelay p) := by
  obtain ⟨S, _, hs⟩ := h.exists_support_bound
  have hpath_sum : HasSum (fun a : ℕ => quartetPath σ γ h a u) (quartetPulseEcho σ γ h u) := by
    have he : HasSum (fun a : ℕ => quartetPath σ γ h a u)
        (∑ a ∈ Finset.Icc 1 (pathReturnCutoff (u + S)), quartetPath σ γ h a u) :=
      hasSum_sum_of_ne_finset_zero fun a ha => quartetPath_eq_zero_outside_cutoff σ γ h hs u ha
    rwa [quartet_finite_return_sum h0 h1 hγ h hs le_rfl] at he
  let A : ℕ → ℂ := fun a => quartetPath σ γ h a u
  let B : ℕ → ℂ := fun a => if p ∣ a then A a else 0
  have hA : Summable A := hpath_sum.summable
  have hB : Summable B :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 (pathReturnCutoff (u + S))) fun a ha => by
      dsimp only [B, A]
      rw [quartetPath_eq_zero_outside_cutoff σ γ h hs u ha, ite_self]
  have htsum_mult : (∑' a, B a) = quartetMultipleEcho σ γ h p u := by
    have hi : Function.Injective (fun a : ℕ => p * a) := fun _ _ he => Nat.eq_of_mul_eq_mul_left hp.pos he
    have hsupp : Function.support B ⊆ Set.range (fun a : ℕ => p * a) := by
      intro a ha
      by_contra hn
      exact ha (if_neg fun ⟨d, hd⟩ => hn ⟨d, hd.symm⟩)
    simpa only [B, A, if_pos (dvd_mul_right p _), quartetMultipleEcho] using (hi.tsum_eq hsupp).symm
  have hterm : ∀ a : ℕ, quartetPath σ γ h (p * a) (echoDelay p + u) =
      (1 - 1 / (p : ℂ)) * A a + (1 / (p : ℂ)) * B a := by
    intro a
    have h0' := quartetPath_prime_tower σ γ h hp 0 a u
    simp only [zero_add, pow_one] at h0'
    rw [h0', echoWeight_prime_mul' hp]
    by_cases hd : p ∣ a <;> simp only [B, A, quartetPath, hd, ↓reduceIte,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast] <;> ring
  have hdelay : quartetMultipleEcho σ γ h p (echoDelay p + u) =
      (1 - 1 / (p : ℂ)) * quartetPulseEcho σ γ h u +
        (1 / (p : ℂ)) * quartetMultipleEcho σ γ h p u := by
    calc quartetMultipleEcho σ γ h p (echoDelay p + u)
        = ∑' a, ((1 - 1 / (p : ℂ)) * A a + (1 / (p : ℂ)) * B a) := tsum_congr hterm
      _ = _ := by
          rw [(hA.mul_left _).tsum_add (hB.mul_left _), tsum_mul_left, tsum_mul_left,
            hpath_sum.tsum_eq, htsum_mult]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  have hshift : Complex.exp (((u - echoDelay p : ℝ) : ℂ) / 2) =
      Complex.exp ((u : ℂ) / 2) / (p : ℂ) := by
    rw [echoDelay, Complex.ofReal_sub, sub_div, Complex.exp_sub]
    congr 1
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat,
      show (2 : ℂ) * ↑(Real.log p) / 2 = ↑(Real.log p) by ring,
      ← Complex.ofReal_exp, Real.exp_log (Nat.cast_pos.mpr hp.pos), Complex.ofReal_natCast]
  unfold quartetCenteredPrimeSector
  rw [hdelay, quartetPulseEcho, show echoDelay p + (u - echoDelay p) = u by ring, hshift]
  field_simp [hp0, hp1]; ring

/-- **Bounce-Agnostic Prime-Sector Weighted-Bound Equivalence and Exact Two-Copy Inversion.** -/
theorem quartet_prime_sector_equivalence_and_inverse {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hγ : 0 < γ) {p : ℕ} (hp : p.Prime) :
    (∀ (h : CompactPulse) {δ : ℝ}, 0 ≤ δ → δ < 1 / 2 →
      (ReturnCancellation.weightedBound δ (quartetCenteredPrimeSector σ γ h p) ↔
        ReturnCancellation.weightedBound δ (quartetReflected σ γ h))) ∧
    (∀ (h : CompactPulse) (u : ℝ),
      quartetCenteredPrimeSector σ γ (ReturnCancellation.inverseSectorInput p h) p u =
        quartetReflected σ γ h u) := by
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hd : 0 < echoDelay p := mul_pos (by norm_num) hlog
  have hsector_before : ∀ (g : CompactPulse) {S : ℝ}, (∀ s : ℝ, S < |s| → g s = 0) →
      ∀ {u : ℝ}, u ≤ -S → quartetCenteredPrimeSector σ γ g p u =
        -(((p : ℂ) / (p + 1)) * quartetMeanCoeff σ γ g * Complex.exp ((u : ℂ) / 2)) := by
    intro g S hs u hu
    have hz : ∀ a : ℕ, quartetPath σ γ g (p * a) (echoDelay p + u) = 0 := by
      intro a
      have he := quartetPath_prime_tower σ γ g hp 0 a u
      simp only [zero_add, pow_one] at he
      rw [he, quartetBounce_eq_zero_of_le_neg_support σ γ g hs
        (by linarith only [hu, echoDelay_nonneg a]), mul_zero]
    simp [quartetCenteredPrimeSector, quartetMultipleEcho, hz]
  have hwb_iff : ∀ (g : CompactPulse) {δ : ℝ}, 0 ≤ δ → δ < 1 / 2 →
      (ReturnCancellation.weightedBound δ (quartetCenteredPrimeSector σ γ g p) ↔
        ReturnCancellation.weightedBound δ (quartetReflected σ γ g)) := by
    intro g δ hδ0 hδ_half
    set b : ℝ := Real.exp (δ * echoDelay p) / (p : ℝ)
    set a : ℂ := 1 - 1 / (p : ℂ)
    set Y : ℝ → ℂ := fun u => (Real.exp (δ * u) : ℂ) * quartetCenteredPrimeSector σ γ g p u
    set F : ℝ → ℂ := fun u => (Real.exp (δ * u) : ℂ) * quartetReflected σ γ g u
    have hb0 : 0 ≤ b := div_nonneg (Real.exp_pos _).le hp0.le
    have hb1 : b < 1 := by
      apply (div_lt_one hp0).mpr
      rw [← Real.exp_log hp0]
      exact Real.exp_lt_exp.mpr (by unfold echoDelay; nlinarith)
    have ha_ne : a ≠ 0 := by
      have hr : 0 < 1 - 1 / (p : ℝ) := sub_pos.mpr ((div_lt_one hp0).mpr hp1)
      simpa [a] using Complex.ofReal_ne_zero.mpr hr.ne'
    have hrec : ∀ u : ℝ, Y u = a * F u + (b : ℂ) * Y (u - echoDelay p) := by
      intro u
      have hE : (Real.exp (δ * echoDelay p) : ℂ) * (Real.exp (δ * (u - echoDelay p)) : ℂ) =
          (Real.exp (δ * u) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Real.exp_add, show δ * echoDelay p + δ * (u - echoDelay p) = δ * u by ring]
      dsimp only [Y, F, a, b]
      rw [quartet_centered_sector_delay h0 h1 hγ g hp u, Complex.ofReal_div, Complex.ofReal_natCast]
      linear_combination -(1 / (p : ℂ)) * quartetCenteredPrimeSector σ γ g p (u - echoDelay p) * hE
    obtain ⟨S, hS_nn, hs⟩ := g.exists_support_bound
    have hbefore : ∀ u ≤ -S, ‖Y u‖ ≤ ‖((p : ℂ) / (p + 1)) * quartetMeanCoeff σ γ g‖ := by
      intro u hu
      have hu0 : u ≤ 0 := by linarith
      have he₁ : Real.exp (δ * u) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hδ0 hu0)
      have he₂ : Real.exp (u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      dsimp only [Y]
      rw [hsector_before g hs hu, norm_mul, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp, Complex.div_ofNat_re,
        Complex.ofReal_re]
      exact (mul_le_of_le_one_left (by positivity) he₁).trans
        (mul_le_of_le_one_right (norm_nonneg _) he₂)
    -- Bounded delay equivalence
    have hbn : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0]
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨(C + b * C) / ‖a‖, fun u => (le_div_iff₀ (norm_pos_iff.mpr ha_ne)).mpr ?_⟩
      calc ‖F u‖ * ‖a‖ = ‖a * F u‖ := by rw [norm_mul, mul_comm]
        _ = ‖Y u - (b : ℂ) * Y (u - echoDelay p)‖ := by rw [hrec u, add_sub_cancel_right]
        _ ≤ ‖Y u‖ + ‖(b : ℂ) * Y (u - echoDelay p)‖ := norm_sub_le _ _
        _ ≤ C + b * C := by
            rw [norm_mul (b : ℂ), hbn]
            exact add_le_add (hC _) (mul_le_mul_of_nonneg_left (hC _) hb0)
    · rintro ⟨C, hC⟩
      set M₀ : ℝ := ‖((p : ℂ) / (p + 1)) * quartetMeanCoeff σ γ g‖
      set L : ℝ := max M₀ (‖a‖ * C / (1 - b))
      have hL : ‖a‖ * C ≤ L * (1 - b) := (div_le_iff₀ (sub_pos.mpr hb1)).mp (le_max_right _ _)
      have hstretch : ∀ (n : ℕ) (u : ℝ), u ≤ -S + n * echoDelay p → ‖Y u‖ ≤ L := by
        intro n
        induction n with
        | zero =>
          intro u hu
          exact (hbefore u (by simpa using hu)).trans (le_max_left _ _)
        | succ n ih =>
          intro u hu
          have hback : u - echoDelay p ≤ -S + n * echoDelay p := by push_cast at hu; linarith
          rw [hrec u]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul a, norm_mul (b : ℂ), hbn]
          linarith [mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a),
            mul_le_mul_of_nonneg_left (ih _ hback) hb0]
      refine ⟨L, fun u => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_ge ((u - (-S)) / echoDelay p)
      exact hstretch n u (by linarith [(div_le_iff₀ hd).mp hn])
  refine ⟨hwb_iff, fun h u => ?_⟩
  -- Exact two-copy inversion `quartetCenteredPrimeSector σ γ (inverseSectorInput p h) p u = quartetReflected σ γ h u`
  set g : CompactPulse := ReturnCancellation.inverseSectorInput p h
  set b : ℂ := 1 / (p : ℂ)
  have hb_lt1 : ‖b‖ < 1 := by
    dsimp [b]; rw [norm_div, norm_one, Complex.norm_natCast]
    exact (div_lt_one hp0).mpr hp1
  have ha_ne : 1 - b ≠ 0 := sub_ne_zero.mpr fun h₁ => hb_lt1.ne (by rw [← h₁, norm_one])
  obtain ⟨_, hunit⟩ := quartet_schur_and_unitary h0 h1 hγ
  have hcont_q := continuous_quartetScatteringPhase_line h0 h1 hγ
  have href_unif : ∀ f : CompactPulse, ∀ t : ℝ,
      ‖quartetReflected σ γ f t‖ ≤ ∫ ξ : ℝ, ‖pulseAmplitude f (ξ : ℂ)‖ := by
    intro f t
    have hint_f : Integrable fun ξ : ℝ => ‖pulseAmplitude f (ξ : ℂ)‖ :=
      ((f.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
    unfold quartetReflected unitaryReflected
    refine norm_integral_le_of_norm_le hint_f (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, norm_mul, (hunit ξ).2, mul_one, norm_exp_I_mul, mul_one]
  have hg_wb0 : ReturnCancellation.weightedBound 0 (quartetReflected σ γ g) :=
    ⟨∫ ξ : ℝ, ‖pulseAmplitude g (ξ : ℂ)‖, fun t => by simpa using href_unif g t⟩
  obtain ⟨Cg, hCg⟩ := (hwb_iff g le_rfl (by norm_num)).mpr hg_wb0
  set D : ℝ → ℂ := fun t => quartetCenteredPrimeSector σ γ g p t - quartetReflected σ γ h t
  set CD : ℝ := Cg + ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖
  have hD_le : ∀ t : ℝ, ‖D t‖ ≤ CD := fun t =>
    (norm_sub_le _ _).trans (add_le_add (by simpa using hCg t) (href_unif h t))
  -- Linearity of `quartetReflected σ γ` on `inverseSectorInput p h`
  have hfilter : ∀ t : ℝ, quartetReflected σ γ g t =
      (1 - b)⁻¹ * (quartetReflected σ γ h t - b * quartetReflected σ γ h (t - echoDelay p)) := by
    intro t
    have hi_h := h.integrable_amplitude_mul hcont_q.measurable (fun ξ => (hunit ξ).2.le) t
    have hi_d := (h.delay (echoDelay p)).integrable_amplitude_mul hcont_q.measurable
      (fun ξ => (hunit ξ).2.le) t
    dsimp only [g, ReturnCancellation.inverseSectorInput]
    unfold quartetReflected unitaryReflected
    simp only [pulseAmplitude_smul, pulseAmplitude_add, pulseAmplitude_delay]
    have hpt : ∀ ξ : ℝ,
        ((1 - b)⁻¹ * (pulseAmplitude h (ξ : ℂ) +
          (-b) * (Complex.exp (-(I * (ξ : ℂ) * (echoDelay p : ℂ))) * pulseAmplitude h (ξ : ℂ)))) *
          quartetScatteringPhase σ γ ((ξ : ℂ) * I) * Complex.exp (I * (ξ : ℂ) * (t : ℂ)) =
        (1 - b)⁻¹ * (pulseAmplitude h (ξ : ℂ) * quartetScatteringPhase σ γ ((ξ : ℂ) * I) *
            Complex.exp (I * (ξ : ℂ) * (t : ℂ)) -
          b * (pulseAmplitude h (ξ : ℂ) * quartetScatteringPhase σ γ ((ξ : ℂ) * I) *
            Complex.exp (I * (ξ : ℂ) * ((t - echoDelay p : ℝ) : ℂ)))) := by
      intro ξ
      have hexp : Complex.exp (-(I * (ξ : ℂ) * (echoDelay p : ℂ))) *
          Complex.exp (I * (ξ : ℂ) * (t : ℂ)) =
          Complex.exp (I * (ξ : ℂ) * ((t - echoDelay p : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      linear_combination -(1 - b)⁻¹ * b * pulseAmplitude h (ξ : ℂ) *
        quartetScatteringPhase σ γ ((ξ : ℂ) * I) * hexp
    have hi_shift : Integrable fun ξ : ℝ =>
        pulseAmplitude h (ξ : ℂ) * quartetScatteringPhase σ γ ((ξ : ℂ) * I) *
          Complex.exp (I * (ξ : ℂ) * ((t - echoDelay p : ℝ) : ℂ)) :=
      h.integrable_amplitude_mul hcont_q.measurable (fun ξ => (hunit ξ).2.le) (t - echoDelay p)
    simp_rw [hpt]
    rw [integral_const_mul, integral_sub hi_h (hi_shift.const_mul b), integral_const_mul]
  have hD_rec : ∀ t : ℝ, D t = b * D (t - echoDelay p) := by
    intro t
    dsimp only [D]
    rw [quartet_centered_sector_delay h0 h1 hγ g hp t, hfilter t]
    change (1 - b) * ((1 - b)⁻¹ * _) + b * _ - _ = _
    rw [← mul_assoc, mul_inv_cancel₀ ha_ne, one_mul]; ring
  have hD_pow : ∀ n : ℕ, ‖D u‖ ≤ ‖b‖ ^ n * CD := by
    have hn : ∀ n : ℕ, D u = b ^ n * D (u - n * echoDelay p) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [ih, hD_rec (u - n * echoDelay p), pow_succ, Nat.cast_succ,
          show u - n * echoDelay p - echoDelay p = u - ((n : ℝ) + 1) * echoDelay p by ring]
        ring
    intro n
    rw [hn n, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hD_le _) (by positivity)
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg b) hb_lt1).mul_const CD
  rw [zero_mul] at hlim
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto' hlim hD_pow) (norm_nonneg _)))

/-! ## 2. Complete Eternal-AdS `G_R` and `G_{RL}` Pole-Multiplicity Dictionary for `xiQuartet σ γ` -/

/-- Retarded, advanced, and two-boundary Wightman correlators of `xiQuartet σ γ`. -/
def quartetRetardedCorrelator (σ γ : ℝ) (ν : ℂ) : ℂ :=
  quartetScatteringPhase σ γ (-I * ν)

def quartetAdvancedCorrelator (σ γ : ℝ) (ν : ℂ) : ℂ :=
  quartetScatteringPhase σ γ (I * ν)

def quartetWightmanRL (σ γ : ℝ) (ν : ℂ) : ℂ :=
  (quartetRetardedCorrelator σ γ ν - quartetAdvancedCorrelator σ γ ν) /
    (2 * I * Complex.sinh (Real.pi * ν))

/-- **Exact `G_R` and `G_{RL}` Zero-to-Pole Multiplicity Dictionary for `xiQuartet σ γ`.**
Every zero `η` of `xiQuartet σ γ` (including every nontrivial zero of `ζ` and the slow quartet
`quartetZero σ γ`) lies in `0 < Re η < 1` and produces an isolated pole of both
`quartetRetardedCorrelator σ γ` and `quartetWightmanRL σ γ` at `I * (η - 1) / 2` of exact
order `-meromorphicOrderAt (xiQuartet σ γ) η < 0`. -/
theorem quartet_correlator_pole_dictionary {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ)
    {η : ℂ} (hη : xiQuartet σ γ η = 0) :
    0 < η.re ∧ η.re < 1 ∧
    meromorphicOrderAt (quartetRetardedCorrelator σ γ) (I * (η - 1) / 2) =
      -meromorphicOrderAt (xiQuartet σ γ) η ∧
    meromorphicOrderAt (quartetWightmanRL σ γ) (I * (η - 1) / 2) =
      -meromorphicOrderAt (xiQuartet σ γ) η ∧
    meromorphicOrderAt (quartetWightmanRL σ γ) (I * (η - 1) / 2) < 0 := by
  obtain ⟨hschur, _⟩ := quartet_schur_and_unitary h0 h1 hγ
  have hge1 : ∀ s : ℂ, 1 ≤ s.re → xiQuartet σ γ s ≠ 0 := by
    intro s hs
    have heq : s = 1 + 2 * ((s - 1) / 2) := by ring
    rw [heq]
    exact (hschur ((s - 1) / 2) (by simp; linarith)).1
  have hlt1 : η.re < 1 := lt_of_not_ge fun h => hge1 η h hη
  have hgt0 : 0 < η.re := by
    by_contra hle; push Not at hle
    exact hge1 (1 - η) (by simp; linarith) (by rw [xiQuartet_one_sub]; exact hη)
  set ν : ℂ := I * (η - 1) / 2 with hν_def
  have hcoord : -I * ν = (η - 1) / 2 := by rw [hν_def]; linear_combination (-(η - 1) / 2) * I_sq
  have hd : HasDerivAt (fun z : ℂ => -I * z) (-I) ν := hasDerivAt_const_mul (-I)
  have hret_ord : meromorphicOrderAt (quartetRetardedCorrelator σ γ) ν =
      -meromorphicOrderAt (xiQuartet σ γ) η := by
    have hcomp : meromorphicOrderAt (quartetRetardedCorrelator σ γ) ν =
        meromorphicOrderAt (quartetScatteringPhase σ γ) ((η - 1) / 2) := by
      rw [← hcoord]
      exact meromorphicOrderAt_comp_of_deriv_ne_zero
        (f := quartetScatteringPhase σ γ) (g := fun z : ℂ => -I * z) (by fun_prop)
        (by rw [hd.deriv]; exact neg_ne_zero.mpr I_ne_zero)
    rw [hcomp]
    exact scatteringPhase_meromorphicOrderAt_at_zero (differentiable_xiQuartet σ γ)
      hge1 (xiQuartet_one_sub σ γ) hη
  obtain ⟨_, hneg_ord, _⟩ := meromorphicOrderAt_pos_of_entire_zero
    (differentiable_xiQuartet σ γ) hge1 hη
  have him : ν.im = (η.re - 1) / 2 := by rw [hν_def]; simp
  have habs0 : 0 < |ν.im| := abs_pos.mpr (by rw [him]; linarith)
  have habs1 : |ν.im| < 1 := by rw [him, abs_of_neg (by linarith)]; linarith
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ν) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one habs0 habs1)
  have hadv_an : AnalyticAt ℂ (fun z => -quartetAdvancedCorrelator σ γ z) ν := by
    set U : Set ℂ := {z : ℂ | z ≠ -(I / 2) ∧ xiQuartet σ γ (1 + 2 * I * z) ≠ 0}
    have hUo : IsOpen U :=
      isOpen_ne.inter (isOpen_ne.preimage ((differentiable_xiQuartet σ γ).continuous.comp (by fun_prop)))
    have hdiff : DifferentiableOn ℂ (quartetAdvancedCorrelator σ γ) U := by
      intro z hz
      have hne : I * z ≠ 1 / 2 := fun h => hz.1 (by linear_combination -I * h + z * I_sq)
      have h2' : xiQuartet σ γ (1 + 2 * (I * z)) ≠ 0 := by simpa [mul_assoc] using hz.2
      exact ((differentiableAt_quartetScatteringPhase hne h2').comp z
        (by fun_prop)).differentiableWithinAt
    have hmemU : ν ∈ U := ⟨fun h => by have := congrArg Complex.im h; simp [him] at this; linarith,
      hge1 _ (by simp [him]; linarith)⟩
    exact ((hdiff.analyticOnNhd hUo) ν hmemU).neg
  have hlt_ord : meromorphicOrderAt (quartetRetardedCorrelator σ γ) ν <
      meromorphicOrderAt (fun z => -quartetAdvancedCorrelator σ γ z) ν :=
    lt_of_lt_of_le (by rw [hret_ord]; exact hneg_ord) hadv_an.meromorphicOrderAt_nonneg
  have hden_an : AnalyticAt ℂ (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) ν :=
    AnalyticAt.inv (by fun_prop) hsinh_ne
  have hW_eq : quartetWightmanRL σ γ =
      (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) *
        (quartetRetardedCorrelator σ γ + fun z => -quartetAdvancedCorrelator σ γ z) := by
    funext z; simp only [quartetWightmanRL, Pi.mul_apply, Pi.add_apply]; ring
  have hwight_ord : meromorphicOrderAt (quartetWightmanRL σ γ) ν =
      -meromorphicOrderAt (xiQuartet σ γ) η := by
    rw [hW_eq, meromorphicOrderAt_mul_of_ne_zero hden_an (inv_ne_zero hsinh_ne),
      meromorphicOrderAt_add_eq_left_of_lt hadv_an.meromorphicAt hlt_ord, hret_ord]
  exact ⟨hgt0, hlt1, hret_ord, hwight_ord, by rw [hwight_ord]; exact hneg_ord⟩

/-! ## 3. Single-Pulse `L²` Sector Tail-Energy & Prime-Power Tower Obstructions -/

/-- **Single-Pulse `L²` Decay Obstruction on `quartetReflected σ γ`.**
Whenever `pulseAmplitude h` is nonvanishing at `-I * ((quartetZero σ γ - 1) / 2)`, even the `L²`
tail integral `∫_T^∞ ‖quartetReflected σ γ h u‖² du` violates `O(e^{-2 δ T})` for every
`δ > (1 - σ) / 2`. -/
theorem not_quartetReflected_l2_tail_decay_gt {σ γ δ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hγ : 0 < γ) (h : CompactPulse)
    (ha_ne : pulseAmplitude h (-I * ((quartetZero σ γ - 1) / 2)) ≠ 0)
    (hδ : (1 - σ) / 2 < δ) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      (∫⁻ u in Ioi T, ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2)) ≤
        ENNReal.ofReal (C * Real.exp (-2 * δ * T)) := by
  rintro ⟨C₀, hC₀_nn, hC₀⟩
  -- Deduce `∫_{u > 0} ‖F u‖² e^{2 δ₁ u} du < ∞` for `(1 - σ)/2 < δ₂ < δ₁ < δ`, making `Lpos` holomorphic on `Re w > -δ₂`
  set δ₁ : ℝ := ((1 - σ) / 2 + 2 * δ) / 3
  set δ₂ : ℝ := (2 * ((1 - σ) / 2) + δ) / 3
  have hδ₂_gt : (1 - σ) / 2 < δ₂ := by dsimp [δ₂]; linarith
  have hδ₂_lt₁ : δ₂ < δ₁ := by dsimp [δ₁, δ₂]; linarith
  have hδ₁_lt : δ₁ < δ := by dsimp [δ₁]; linarith
  have hδ₁_pos : 0 < δ₁ := lt_trans (by positivity) (hδ₂_gt.trans hδ₂_lt₁)
  obtain ⟨hschur, hunit⟩ := quartet_schur_and_unitary h0 h1 hγ
  have hcont_q := continuous_quartetScatteringPhase_line h0 h1 hγ
  have hGc : Continuous (quartetReflected σ γ h) :=
    continuous_unitaryReflected hcont_q.measurable (fun ξ => (hunit ξ).2.le) h
  -- Bound `∫⁻ u in Ioi 0, ENNReal.ofReal (‖F u‖² * e^{2 δ₁ u}) < ⊤` by summing over `[n, n+1)`
  have hsq_lint : (∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u))) < ⊤ := by
    have hsub : Ioi (0 : ℝ) ⊆ ⋃ n : ℕ, Ico (n : ℝ) ((n : ℝ) + 1) := by
      intro u hu
      have hu0 : 0 ≤ u := le_of_lt hu
      refine mem_iUnion.mpr ⟨⌊u⌋₊, ?_⟩
      exact ⟨Nat.floor_le hu0, Nat.lt_floor_add_one u⟩
    have hblock : ∀ n : ℕ,
        (∫⁻ u in Ico (n : ℝ) ((n : ℝ) + 1),
          ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u))) ≤
        ENNReal.ofReal (Real.exp (2 * δ₁) * C₀ * (Real.exp (-2 * (δ - δ₁))) ^ n) := by
      intro n
      have hmono_pt : ∀ u ∈ Ico (n : ℝ) ((n : ℝ) + 1),
          ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u)) ≤
            ENNReal.ofReal (Real.exp (2 * δ₁ * ((n : ℝ) + 1))) *
              ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2) := by
        intro u hu
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [hu.2])) (sq_nonneg _))
      have hset_sub : Ioc (n : ℝ) ((n : ℝ) + 1) ⊆ Ioi (n : ℝ) := fun _ hx => hx.1
      have hae_eq : (Ico (n : ℝ) ((n : ℝ) + 1) : Set ℝ) =ᵐ[volume] Ioc (n : ℝ) ((n : ℝ) + 1) :=
        Ico_ae_eq_Ioc
      calc (∫⁻ u in Ico (n : ℝ) ((n : ℝ) + 1),
              ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u)))
          ≤ ∫⁻ u in Ico (n : ℝ) ((n : ℝ) + 1),
              ENNReal.ofReal (Real.exp (2 * δ₁ * ((n : ℝ) + 1))) *
                ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2) :=
            setLIntegral_mono' measurableSet_Ico hmono_pt
        _ = ENNReal.ofReal (Real.exp (2 * δ₁ * ((n : ℝ) + 1))) *
              ∫⁻ u in Ico (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2) :=
            lintegral_const_mul _ (hGc.norm.pow 2).ennreal_ofReal
        _ = ENNReal.ofReal (Real.exp (2 * δ₁ * ((n : ℝ) + 1))) *
              ∫⁻ u in Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2) := by
            rw [setLIntegral_congr hae_eq]
        _ ≤ ENNReal.ofReal (Real.exp (2 * δ₁ * ((n : ℝ) + 1))) *
              ∫⁻ u in Ioi (n : ℝ), ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2) :=
            mul_le_mul_left' (lintegral_mono_set hset_sub) _
        _ ≤ ENNReal.ofReal (Real.exp (2 * δ₁ * ((n : ℝ) + 1))) *
              ENNReal.ofReal (C₀ * Real.exp (-2 * δ * (n : ℝ))) :=
            mul_le_mul_left' (hC₀ (n : ℝ) (Nat.cast_nonneg n)) _
        _ = ENNReal.ofReal (Real.exp (2 * δ₁) * C₀ * (Real.exp (-2 * (δ - δ₁))) ^ n) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul]
            congr 1
            have hexp : Real.exp (2 * δ₁ * ((n : ℝ) + 1)) * (C₀ * Real.exp (-2 * δ * (n : ℝ))) =
                C₀ * (Real.exp (2 * δ₁) * Real.exp (2 * δ₁ * (n : ℝ) + -2 * δ * (n : ℝ))) := by
              rw [show 2 * δ₁ * ((n : ℝ) + 1) = 2 * δ₁ + 2 * δ₁ * (n : ℝ) by ring,
                Real.exp_add, mul_left_comm _ C₀, mul_assoc, ← Real.exp_add]
            rw [hexp]
            have hexp2 : 2 * δ₁ * (n : ℝ) + -2 * δ * (n : ℝ) = (n : ℝ) * (-2 * (δ - δ₁)) := by ring
            rw [hexp2]; ring
    have hgeom_sum : Summable fun n : ℕ =>
        Real.exp (2 * δ₁) * C₀ * (Real.exp (-2 * (δ - δ₁))) ^ n :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by linarith))).mul_left _
    calc (∫⁻ u in Ioi (0 : ℝ),
            ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u)))
        ≤ ∫⁻ u in ⋃ n : ℕ, Ico (n : ℝ) ((n : ℝ) + 1),
            ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u)) :=
          lintegral_mono_set hsub
      _ ≤ ∑' n : ℕ, ∫⁻ u in Ico (n : ℝ) ((n : ℝ) + 1),
            ENNReal.ofReal (‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u)) :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (2 * δ₁) * C₀ * (Real.exp (-2 * (δ - δ₁))) ^ n) :=
          ENNReal.tsum_le_tsum hblock
      _ = ENNReal.ofReal (∑' n : ℕ, Real.exp (2 * δ₁) * C₀ * (Real.exp (-2 * (δ - δ₁))) ^ n) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hgeom_sum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hsq_int : IntegrableOn
      (fun u : ℝ => ‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u)) (Ioi 0) := by
    have hcont_w : Continuous fun u : ℝ =>
        ‖quartetReflected σ γ h u‖ ^ 2 * Real.exp (2 * δ₁ * u) :=
      (hGc.norm.pow 2).mul (by fun_prop)
    refine ⟨hcont_w.aestronglyMeasurable.restrict, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_eq_of_lt ?_ hsq_lint
    refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u _ => ?_))
    rw [Real.enorm_eq_ofReal (by positivity)]
  -- By AM-GM, `Lpos w := ∫ u in Ioi 0, e^{-w u} quartetReflected σ γ h u` is `DifferentiableOn` `Re w > -δ₂`!
  have hLpos_d : DifferentiableOn ℂ
      (fun w : ℂ => ∫ τ in Ioi (0 : ℝ), Complex.exp (-w * (τ : ℂ)) * quartetReflected σ γ h τ)
      {w : ℂ | -δ₂ < w.re} := by
    have hUo : IsOpen {w : ℂ | -δ₂ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    refine differentiableOn_integral_of_locally_bounded (ν := volume.restrict (Ioi (0 : ℝ)))
      (F := fun (τ : ℝ) (w : ℂ) => Complex.exp (-w * (τ : ℂ)) * quartetReflected σ γ h τ) hUo
      (fun τ => (by fun_prop : Differentiable ℂ fun w : ℂ =>
        Complex.exp (-w * (τ : ℂ)) * quartetReflected σ γ h τ).differentiableOn)
      (fun w _ => ((by fun_prop : Continuous fun τ : ℝ =>
        Complex.exp (-w * (τ : ℂ))).mul hGc).aestronglyMeasurable.restrict) ?_
    intro w₀ hw₀
    have hw₀' : -δ₂ < w₀.re := hw₀
    set r : ℝ := (w₀.re + δ₂) / 2
    have hr_pos : 0 < r := by dsimp [r]; linarith
    set c : ℝ := -(w₀.re - r)
    have hc_lt : c < δ₁ := by dsimp [c, r]; linarith
    have hexp_tail : IntegrableOn (fun τ : ℝ => Real.exp (-2 * (δ₁ - c) * τ)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    set B_fn : ℝ → ℝ := fun τ =>
      (‖quartetReflected σ γ h τ‖ ^ 2 * Real.exp (2 * δ₁ * τ) +
        Real.exp (-2 * (δ₁ - c) * τ)) / 2
    have hB_int : Integrable B_fn (volume.restrict (Ioi (0 : ℝ))) :=
      (hsq_int.add hexp_tail).div_const 2
    refine ⟨r, hr_pos, fun w hw => ?_, B_fn, hB_int, ?_⟩
    · have hd := Complex.abs_re_le_norm (w - w₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have habs : |w.re - w₀.re| ≤ r := by simpa using hd.trans hw
      show -δ₂ < w.re
      dsimp [r] at habs
      linarith [(abs_le.mp habs).1]
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
      intro w hw
      have hτ_pos : (0 : ℝ) < τ := hτ
      have hd := Complex.abs_re_le_norm (w - w₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have habs : |w.re - w₀.re| ≤ r := by simpa using hd.trans hw
      have hw_re_ge : w₀.re - r ≤ w.re := by linarith [(abs_le.mp habs).1]
      rw [norm_mul, Complex.norm_exp, show (-w * (τ : ℂ)).re = -w.re * τ by simp]
      have hexp_le : Real.exp (-w.re * τ) ≤ Real.exp (c * τ) :=
        Real.exp_le_exp.mpr (by dsimp [c]; nlinarith)
      set X : ℝ := ‖quartetReflected σ γ h τ‖ * Real.exp (δ₁ * τ)
      set Y : ℝ := Real.exp (-(δ₁ - c) * τ)
      have hXY : Real.exp (c * τ) * ‖quartetReflected σ γ h τ‖ = X * Y := by
        dsimp [X, Y]
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      have hX2 : X ^ 2 = ‖quartetReflected σ γ h τ‖ ^ 2 * Real.exp (2 * δ₁ * τ) := by
        dsimp [X]; rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; congr 2; ring
      have hY2 : Y ^ 2 = Real.exp (-2 * (δ₁ - c) * τ) := by
        dsimp [Y]; rw [sq, ← Real.exp_add]; congr 1; ring
      calc Real.exp (-w.re * τ) * ‖quartetReflected σ γ h τ‖
          ≤ Real.exp (c * τ) * ‖quartetReflected σ γ h τ‖ :=
            mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)
        _ = X * Y := hXY
        _ ≤ B_fn τ := by dsimp [B_fn]; rw [← hX2, ← hY2]; nlinarith [sq_nonneg (X - Y)]
  -- For `t ≤ -S`, `quartet_finite_return_sum` identifies `quartetReflected` with `-quartetMeanCoeff * e^{t/2}`,
  -- making `Lneg` holomorphic on `Re w < 1/2` and `quartetReflected` integrable on `ℝ`
  obtain ⟨S, hS_nn, hs⟩ := h.exists_support_bound
  have href_before : ∀ t : ℝ, t ≤ -S →
      quartetReflected σ γ h t = -quartetMeanCoeff σ γ h * Complex.exp ((t : ℂ) / 2) := by
    intro t ht
    have hsum0 : ∑ c ∈ Finset.Icc 1 (pathReturnCutoff (t + S)), quartetPath σ γ h c t = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [quartetPath, quartetBounce_eq_zero_of_le_neg_support σ γ h hs
        (by linarith [echoDelay_nonneg c]), mul_zero]
    have hfin := quartet_finite_return_sum h0 h1 hγ h hs (le_refl t)
    rw [hsum0] at hfin
    linear_combination -hfin
  -- Bound `‖quartetReflected σ γ h τ‖ ≤ Kneg * e^{τ / 2}` for ALL `τ ≤ 0`!
  have href_unif : ∀ τ : ℝ, ‖quartetReflected σ γ h τ‖ ≤ ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ := by
    intro τ
    have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
      ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
    unfold quartetReflected unitaryReflected
    refine norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, norm_mul, (hunit ξ).2, mul_one, norm_exp_I_mul, mul_one]
  set Kneg : ℝ := max ‖quartetMeanCoeff σ γ h‖
    ((∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖) * Real.exp (S / 2))
  have hKneg_nn : 0 ≤ Kneg := le_trans (norm_nonneg _) (le_max_left _ _)
  have href_neg_bound : ∀ τ : ℝ, τ ≤ 0 →
      ‖quartetReflected σ γ h τ‖ ≤ Kneg * Real.exp ((1 / 2) * τ) := by
    intro τ hτ0
    by_cases hτS : τ ≤ -S
    · rw [href_before τ hτS, norm_mul, norm_neg, Complex.norm_exp,
        show ((τ : ℂ) / 2).re = (1 / 2) * τ by simp; ring]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · push Not at hτS
      calc ‖quartetReflected σ γ h τ‖
          ≤ ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ := href_unif τ
        _ = ((∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖) * Real.exp (S / 2)) * Real.exp (-(S / 2)) := by
            rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ Kneg * Real.exp ((1 / 2) * τ) :=
            mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr (by linarith))
              (Real.exp_pos _).le hKneg_nn
  -- `Lneg w := ∫ σ' in Ioi 0, e^{w σ'} quartetReflected σ γ h (-σ')` is holomorphic on `Re w < 1/2`!
  set Lpos : ℂ → ℂ := fun w =>
    ∫ τ in Ioi (0 : ℝ), Complex.exp (-w * (τ : ℂ)) * quartetReflected σ γ h τ
  set Lneg₀ : ℂ → ℂ := fun z =>
    ∫ σ' in Ioi (0 : ℝ), Complex.exp (-z * (σ' : ℂ)) * quartetReflected σ γ h (-σ')
  have hLneg₀_d : DifferentiableOn ℂ Lneg₀ {z : ℂ | -(1 / 2 : ℝ) < z.re} := by
    refine RingdownRate.differentiableOn_laplace (hGc.comp continuous_neg) hKneg_nn fun σ' hσ' => ?_
    simpa [mul_neg, neg_mul] using href_neg_bound (-σ') (by linarith)
  set Lneg : ℂ → ℂ := fun w => Lneg₀ (-w)
  have hLneg_d : DifferentiableOn ℂ Lneg {w : ℂ | w.re < 1 / 2} := by
    intro w hw
    have hw' : -w ∈ {z : ℂ | -(1 / 2 : ℝ) < z.re} := by show -(1 / 2 : ℝ) < (-w).re; simp; exact hw
    have hopen : IsOpen {z : ℂ | -(1 / 2 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact ((hLneg₀_d (-w) hw').differentiableAt (hopen.mem_nhds hw')).comp w
      differentiableAt_id.neg |>.differentiableWithinAt
  -- Fourier inversion on `ℝ` identifies `Lpos + Lneg` along `i ℝ`, which accumulates at `0`
  have hg_pos_int : IntegrableOn (quartetReflected σ γ h) (Ioi (0 : ℝ)) := by
    have hexp_tail0 : IntegrableOn (fun τ : ℝ => Real.exp (-2 * δ₁ * τ)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine ((hsq_int.add hexp_tail0).div_const 2).mono' hGc.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ _ => ?_)
    set X : ℝ := ‖quartetReflected σ γ h τ‖ * Real.exp (δ₁ * τ)
    set Y : ℝ := Real.exp (-δ₁ * τ)
    have hXY : ‖quartetReflected σ γ h τ‖ = X * Y := by
      dsimp [X, Y]; rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hX2 : X ^ 2 = ‖quartetReflected σ γ h τ‖ ^ 2 * Real.exp (2 * δ₁ * τ) := by
      dsimp [X]; rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; congr 2; ring
    have hY2 : Y ^ 2 = Real.exp (-2 * δ₁ * τ) := by
      dsimp [Y]; rw [sq, ← Real.exp_add]; congr 1; ring
    rw [hXY, ← hX2, ← hY2]
    nlinarith [sq_nonneg (X - Y)]
  have hg_neg_int : IntegrableOn (quartetReflected σ γ h) (Iic (0 : ℝ)) := by
    have hdom_i : IntegrableOn (fun σ' : ℝ => Kneg * Real.exp (-(1 / 2) * σ')) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul Kneg
    have hdom : IntegrableOn (fun τ : ℝ => Kneg * Real.exp ((1 / 2) * τ)) (Iic 0) := by
      rw [← integrable_indicator_iff measurableSet_Iic]
      have h1' := ((integrable_indicator_iff measurableSet_Ioi).mpr hdom_i).comp_neg
      refine h1'.congr ?_
      have hae : ∀ᵐ τ : ℝ, τ ≠ 0 := by
        rw [ae_iff]; have : {τ : ℝ | ¬ τ ≠ 0} = ({0} : Set ℝ) := by ext; simp
        rw [this]; exact measure_singleton 0
      refine hae.mono fun τ hτ => ?_
      dsimp only
      rcases lt_or_gt_of_ne hτ with hlt | hgt
      · rw [indicator_of_mem (show -τ ∈ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_mem (show τ ∈ Iic (0 : ℝ) from hlt.le)]; ring_nf
      · rw [indicator_of_notMem (show -τ ∉ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_notMem (show τ ∉ Iic (0 : ℝ) by simp; linarith)]
    exact hdom.mono' hGc.aestronglyMeasurable.restrict
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun τ hτ =>
        href_neg_bound τ hτ))
  have hg_int : Integrable (quartetReflected σ γ h) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hg_neg_int.union hg_pos_int
  -- Fourier inversion on `ℝ` for `F(v) := 2π a_h(2π v) quartetScatteringPhase σ γ (2π v I)`
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpiC : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi0
  set f₀ : ℝ → ℂ := fun ξ => pulseAmplitude h (ξ : ℂ) * quartetScatteringPhase σ γ ((ξ : ℂ) * I)
  have hf₀_cont : Continuous f₀ :=
    (h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).mul hcont_q
  have hf₀_int : Integrable f₀ := by
    simpa [f₀] using h.integrable_amplitude_mul hcont_q.measurable (fun ξ => (hunit ξ).2.le) 0
  set F : ℝ → ℂ := fun v => (2 * Real.pi : ℂ) * f₀ (2 * Real.pi * v)
  have hF_cont : Continuous F := continuous_const.mul (hf₀_cont.comp (by fun_prop))
  have hF_int : Integrable F := (hf₀_int.comp_mul_left' hpi0).const_mul (2 * Real.pi : ℂ)
  have hFinv_eq : 𝓕⁻ F = quartetReflected σ γ h := by
    funext τ
    rw [fourierInv_eq_integral_exp]
    have hg_sub := Measure.integral_comp_mul_left
      (fun ξ : ℝ => f₀ ξ * Complex.exp (I * (ξ : ℂ) * (τ : ℂ))) (2 * Real.pi)
    rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), Complex.real_smul] at hg_sub
    have hrw : ∀ v : ℝ, Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) • F v =
        (2 * Real.pi : ℂ) * (f₀ (2 * Real.pi * v) *
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ))) := by
      intro v; simp only [F, smul_eq_mul]
      have he : Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) =
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ)) := by
        congr 1; push_cast; ring
      rw [he]; ring
    simp_rw [hrw]
    rw [integral_const_mul, hg_sub]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hpiC, one_mul]
    rfl
  have hFF_int : Integrable (𝓕 F) := by
    have hFF_eq : 𝓕 F = fun x => quartetReflected σ γ h (-x) := funext fun x => by
      have h1' := Real.fourierInv_eq_fourier_neg F (-x)
      rw [neg_neg, hFinv_eq] at h1'; exact h1'.symm
    rw [hFF_eq]; exact hg_int.comp_neg
  have hinv := hF_cont.fourier_fourierInv_eq hF_int hFF_int
  rw [hFinv_eq] at hinv
  have haxis_lap : ∀ η : ℝ, Lpos ((η : ℂ) * I) + Lneg ((η : ℂ) * I) =
      2 * Real.pi * pulseAmplitude h (η : ℂ) * quartetScatteringPhase σ γ ((η : ℂ) * I) := by
    intro η
    have hval := congrFun hinv (η / (2 * Real.pi))
    rw [Real.fourier_real_eq_integral_exp_smul] at hval
    set H : ℝ → ℂ := fun τ => Complex.exp (-(((η : ℂ) * I)) * (τ : ℂ)) * quartetReflected σ γ h τ
    have hH_eq : ∀ τ : ℝ,
        Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) •
          quartetReflected σ γ h τ = H τ := by
      intro τ; simp only [smul_eq_mul, H]
      congr 1; congr 1
      have hdiv : -2 * Real.pi * τ * (η / (2 * Real.pi)) = -η * τ := by field_simp
      rw [hdiv]; push_cast; ring
    have hH_int : Integrable H := by
      refine hg_int.norm.mono' ((by fun_prop : Continuous fun τ : ℝ =>
        Complex.exp (-(((η : ℂ) * I)) * (τ : ℂ))).mul hGc).aestronglyMeasurable
        (Eventually.of_forall fun τ => ?_)
      simp only [H, norm_mul, Complex.norm_exp]
      have : (-(((η : ℂ) * I)) * (τ : ℂ)).re = 0 := by simp
      rw [this, Real.exp_zero, one_mul]
    have hsplit := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hH_int
    rw [compl_Ioi] at hsplit
    have hneg_eq : (∫ τ in Iic (0 : ℝ), H τ) = Lneg ((η : ℂ) * I) := by
      dsimp only [Lneg, Lneg₀]
      rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ioi,
        ← integral_neg_eq_self]
      have hae : ∀ᵐ σ' : ℝ, σ' ≠ 0 := by
        rw [ae_iff]; have : {σ' : ℝ | ¬ σ' ≠ 0} = ({0} : Set ℝ) := by ext; simp
        rw [this]; exact measure_singleton 0
      refine integral_congr_ae (hae.mono fun σ' hσ' => ?_)
      dsimp only
      rcases lt_or_gt_of_ne hσ' with hlt | hgt
      · rw [indicator_of_notMem (show -σ' ∉ Iic (0 : ℝ) by simp; linarith),
          indicator_of_notMem (show σ' ∉ Ioi (0 : ℝ) by simp; linarith)]
      · rw [indicator_of_mem (show -σ' ∈ Iic (0 : ℝ) by simp; linarith),
          indicator_of_mem (show σ' ∈ Ioi (0 : ℝ) from hgt)]
        simp only [H]; push_cast; ring_nf
    calc Lpos ((η : ℂ) * I) + Lneg ((η : ℂ) * I)
        = (∫ τ in Ioi (0 : ℝ), H τ) + ∫ τ in Iic (0 : ℝ), H τ := by rw [hneg_eq]
      _ = ∫ τ : ℝ, H τ := hsplit
      _ = ∫ τ : ℝ, Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) •
            quartetReflected σ γ h τ :=
          integral_congr_ae (Eventually.of_forall fun τ => (hH_eq τ).symm)
      _ = F (η / (2 * Real.pi)) := hval
      _ = 2 * Real.pi * pulseAmplitude h (η : ℂ) * quartetScatteringPhase σ γ ((η : ℂ) * I) := by
          dsimp only [F, f₀]; rw [mul_div_cancel₀ _ hpi0]; ring
  -- Analytic identity on `D = {w : ℂ | -δ₂ < w.re ∧ w.re < 1/2}` via `i ℝ` accumulation at `0`!
  set Dom : Set ℂ := {w : ℂ | -δ₂ < w.re ∧ w.re < 1 / 2}
  have hDom_o : IsOpen Dom :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hDom_c : IsPreconnected Dom :=
    ((convex_halfSpace_re_gt (-δ₂)).inter (convex_halfSpace_re_lt (1 / 2))).isPreconnected
  set Φ₁ : ℂ → ℂ := fun w => (2 * w - 1) * xiQuartet σ γ (1 + 2 * w) * (Lpos w + Lneg w)
  set Φ₂ : ℂ → ℂ := fun w =>
    2 * Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xiQuartet σ γ (2 * w)
  have hUpos : IsOpen {w : ℂ | -δ₂ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUneg : IsOpen {w : ℂ | w.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  have hcx := differentiable_xiQuartet σ γ
  have hΦ₁a : AnalyticOnNhd ℂ Φ₁ Dom := by
    refine DifferentiableOn.analyticOnNhd ?_ hDom_o
    intro w hw
    have h1' := (hLpos_d w hw.1).differentiableAt (hUpos.mem_nhds hw.1)
    have h2' := (hLneg_d w hw.2).differentiableAt (hUneg.mem_nhds hw.2)
    exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) w).mul
      ((hcx _).comp w (by fun_prop))).mul (h1'.add h2')).differentiableWithinAt
  have hΦ₂a : AnalyticOnNhd ℂ Φ₂ Dom := by
    refine DifferentiableOn.analyticOnNhd ?_ hDom_o
    intro w _
    exact ((((differentiableAt_const _).mul
      ((h.differentiable_amplitude _).comp w (by fun_prop))).mul (by fun_prop)).mul
      ((hcx _).comp w (by fun_prop))).differentiableWithinAt
  have h0_mem : (0 : ℂ) ∈ Dom := ⟨by simp; linarith [hδ₂_gt], by simp⟩
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), Φ₁ w = Φ₂ w := by
    rw [Filter.frequently_iff]
    intro V hV
    rw [mem_nhdsWithin] at hV
    obtain ⟨U, hUo, h0U, hUV⟩ := hV
    obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hUo 0 h0U
    set η : ℝ := r / 2
    have hη_pos : 0 < η := half_pos hr_pos
    set w_η : ℂ := (η : ℂ) * I
    have hw_ne : w_η ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hη_pos.ne') I_ne_zero
    have hw_U : w_η ∈ U := hr_ball (by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hη_pos.le]
      dsimp [η]; linarith)
    refine ⟨w_η, hUV ⟨hw_U, hw_ne⟩, ?_⟩
    have h2w : 2 * w_η - 1 ≠ 0 := fun h0' => by have := congrArg Complex.re h0'; simp [w_η] at this
    have hxi : xiQuartet σ γ (1 + 2 * w_η) ≠ 0 := (hschur w_η (by simp [w_η])).1
    have hrot : -I * w_η = (η : ℂ) := by dsimp [w_η]; linear_combination -(η : ℂ) * I_sq
    dsimp only [Φ₁, Φ₂]
    rw [haxis_lap η, hrot]
    unfold quartetScatteringPhase quartetReducedScattering
    calc (2 * w_η - 1) * xiQuartet σ γ (1 + 2 * w_η) *
            (2 * ↑Real.pi * pulseAmplitude h ↑η *
              ((1 + 2 * w_η) / (2 * w_η - 1) *
                (xiQuartet σ γ (2 * w_η) / xiQuartet σ γ (1 + 2 * w_η))))
        = ((2 * w_η - 1) * (2 * w_η - 1)⁻¹) *
            (xiQuartet σ γ (1 + 2 * w_η) * (xiQuartet σ γ (1 + 2 * w_η))⁻¹) *
            (2 * ↑Real.pi * pulseAmplitude h ↑η * (1 + 2 * w_η) * xiQuartet σ γ (2 * w_η)) := by
          simp only [div_eq_mul_inv]; ring
      _ = 2 * ↑Real.pi * pulseAmplitude h ↑η * (1 + 2 * w_η) * xiQuartet σ γ (2 * w_η) := by
          rw [mul_inv_cancel₀ h2w, mul_inv_cancel₀ hxi, one_mul, one_mul]
  have hEq : EqOn Φ₁ Φ₂ Dom := hΦ₁a.eqOn_of_preconnected_of_frequently_eq hΦ₂a hDom_c h0_mem hfreq
  -- Evaluate `Φ₁ p₀ = Φ₂ p₀` at `p₀ = (quartetZero σ γ - 1) / 2 ∈ Dom`!
  set p₀ : ℂ := (quartetZero σ γ - 1) / 2
  have hp₀_re : p₀.re = (σ - 1) / 2 := by dsimp [p₀, quartetZero]; simp
  have hp₀_Dom : p₀ ∈ Dom := ⟨by rw [hp₀_re]; linarith [hδ₂_gt], by rw [hp₀_re]; linarith⟩
  have hp_eq := hEq hp₀_Dom
  have hp1_eq : 1 + 2 * p₀ = quartetZero σ γ := by dsimp [p₀]; ring
  have hpxi : xiQuartet σ γ (1 + 2 * p₀) = 0 := by
    rw [hp1_eq]; exact xiQuartet_eval_quartetZero h0 hγ
  dsimp only [Φ₁, Φ₂] at hp_eq
  rw [hpxi, mul_zero, zero_mul] at hp_eq
  have h12p : 1 + 2 * p₀ ≠ 0 := by
    intro h0'; rw [hp1_eq] at h0'
    have := congrArg Complex.re h0'; simp [quartetZero] at this; linarith
  have hxi2p : xiQuartet σ γ (2 * p₀) ≠ 0 := by
    rw [← xiQuartet_one_sub σ γ (2 * p₀), show (1 : ℂ) - 2 * p₀ = 1 + 2 * (-p₀) by ring]
    exact (hschur (-p₀) (by rw [Complex.neg_re, hp₀_re]; linarith)).1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpiC ha_ne) h12p) hxi2p hp_eq.symm

/-- **Simultaneous Prime-Sector, Tail-Energy, and Prime-Power Tower Obstruction on `xiQuartet σ γ`.**
For every prime `p` (in particular `p = 2`), whenever `pulseAmplitude h` is nonvanishing at
`-I * ((quartetZero σ γ - 1) / 2)` and `(1 - σ) / 2 < δ`:
1. on `g = inverseSectorInput p h`, the centered `p`-sector wavepacket violates `O(e^{-δ u})`;
2. on `g = inverseSectorInput p h`, the `p`-sector `L²` tail energy violates `O(e^{-2 δ T})`;
3. if `δ < 1/2`, `quartetCenteredPrimeSector σ γ h p` itself violates `O(e^{-δ u})`;
4. the `p`-power return cancellation error at `c = p ^ k` violates geometric rate
   `C * e^{-δ u} * (e^{-2 δ log p})^k`. -/
theorem not_quartet_prime_sector_and_tower_decay_gt {σ γ δ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hγ : 0 < γ) {p : ℕ} (hp : p.Prime) (h : CompactPulse)
    (ha_ne : pulseAmplitude h (-I * ((quartetZero σ γ - 1) / 2)) ≠ 0)
    (hδ : (1 - σ) / 2 < δ) :
    let g := ReturnCancellation.inverseSectorInput p h
    (¬ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖quartetCenteredPrimeSector σ γ g p u‖ ≤ C * Real.exp (-δ * u)) ∧
    (¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      quartetSectorTailEnergy σ γ p g T ≤ ENNReal.ofReal (C * Real.exp (-2 * δ * T))) ∧
    (δ < 1 / 2 → ¬ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖quartetCenteredPrimeSector σ γ h p u‖ ≤ C * Real.exp (-δ * u)) ∧
    (∀ {S : ℝ}, 0 ≤ S → (∀ s : ℝ, S < |s| → h s = 0) →
      ¬ ∃ C : ℝ, ∀ (u : ℝ) (k : ℕ), 1 ≤ k → 0 ≤ echoDelay (p ^ k) + u →
        ‖quartetOthers σ γ h S u (p ^ k) + ((1 - 1 / (p : ℝ) : ℝ) : ℂ) * quartetBounce σ γ h u‖ ≤
          C * Real.exp (-δ * u) * (Real.exp (-2 * δ * Real.log p)) ^ k) := by
  intro g
  obtain ⟨hwb_iff, hinv_eq⟩ := quartet_prime_sector_equivalence_and_inverse h0 h1 hγ hp
  have hnot_refl := not_quartetReflected_decay_gt h0 h1 hγ h ha_ne hδ
  have hnot_l2 := not_quartetReflected_l2_tail_decay_gt h0 h1 hγ h ha_ne hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨C, hC⟩
    exact hnot_refl ⟨C, fun u hu => by rw [← hinv_eq h u]; exact hC u hu⟩
  · rintro ⟨C, hC0, hC⟩
    refine hnot_l2 ⟨C, hC0, fun T hT => ?_⟩
    have hCT := hC T hT
    dsimp only [quartetSectorTailEnergy, g] at hCT
    simp_rw [hinv_eq h] at hCT
    exact hCT
  · intro hδ_half ⟨C, hC⟩
    have hδ0 : 0 < δ := lt_trans (by positivity) hδ
    obtain ⟨S, hS_nn, hs⟩ := h.exists_support_bound
    have hsec_before : ∀ u : ℝ, u ≤ -S →
        quartetCenteredPrimeSector σ γ h p u =
          -(((p : ℂ) / (p + 1)) * quartetMeanCoeff σ γ h * Complex.exp ((u : ℂ) / 2)) := by
      intro u hu
      have hz : ∀ a : ℕ, quartetPath σ γ h (p * a) (echoDelay p + u) = 0 := by
        intro a
        have he := quartetPath_prime_tower σ γ h hp 0 a u
        simp only [zero_add, pow_one] at he
        rw [he, quartetBounce_eq_zero_of_le_neg_support σ γ h hs
          (by linarith only [hu, echoDelay_nonneg a]), mul_zero]
      simp [quartetCenteredPrimeSector, quartetMultipleEcho, hz]
    -- Iterate `quartet_centered_sector_delay` forward from `u ≤ -S` to bound `quartetCenteredPrimeSector` on `u ≤ 0`
    obtain ⟨_, hunit⟩ := quartet_schur_and_unitary h0 h1 hγ
    have href_unif : ∀ t : ℝ, ‖quartetReflected σ γ h t‖ ≤ ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ := by
      intro t
      have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
        ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
      unfold quartetReflected unitaryReflected
      refine norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun ξ => ?_)
      rw [norm_mul, norm_mul, (hunit ξ).2, mul_one, norm_exp_I_mul, mul_one]
    have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hd_pos : 0 < echoDelay p := mul_pos (by norm_num) (Real.log_pos hp1)
    set M_ref : ℝ := ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖
    set M_neg : ℝ := max ‖((p : ℂ) / (p + 1)) * quartetMeanCoeff σ γ h‖ M_ref
    have hsec_nonpos : ∀ (n : ℕ) (u : ℝ), u ≤ 0 → u ≤ -S + n * echoDelay p →
        ‖quartetCenteredPrimeSector σ γ h p u‖ ≤ M_neg := by
      intro n
      induction n with
      | zero =>
        intro u hu0 huS
        rw [hsec_before u (by simpa using huS), norm_neg, norm_mul, Complex.norm_exp,
          show ((u : ℂ) / 2).re = u / 2 by simp]
        exact (mul_le_of_le_one_right (norm_nonneg _)
          (Real.exp_le_one_iff.mpr (by linarith))).trans (le_max_left _ _)
      | succ n ih =>
        intro u hu0 huS
        have hback : u - echoDelay p ≤ -S + n * echoDelay p := by push_cast at huS; linarith
        rw [quartet_centered_sector_delay h0 h1 hγ h hp u]
        have h1mp : ‖1 - 1 / (p : ℂ)‖ = 1 - 1 / (p : ℝ) := by
          have hr : 0 ≤ 1 - 1 / (p : ℝ) := sub_nonneg.mpr ((div_le_one hp0).mpr hp1.le)
          have hc : (1 - 1 / (p : ℂ)) = ((1 - 1 / (p : ℝ) : ℝ) : ℂ) := by push_cast; rfl
          rw [hc, Complex.norm_real, Real.norm_of_nonneg hr]
        have h1p : ‖(1 / (p : ℂ))‖ = 1 / (p : ℝ) := by
          rw [norm_div, norm_one, Complex.norm_natCast]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, h1mp, h1p]
        have hb1 : ‖quartetReflected σ γ h u‖ ≤ M_neg := (href_unif u).trans (le_max_right _ _)
        have hb2 : ‖quartetCenteredPrimeSector σ γ h p (u - echoDelay p)‖ ≤ M_neg :=
          ih _ (by linarith) hback
        have hp_nn : 0 ≤ 1 / (p : ℝ) := by positivity
        have hp_sub : 0 ≤ 1 - 1 / (p : ℝ) := sub_nonneg.mpr ((div_le_one hp0).mpr hp1.le)
        nlinarith
    have hwb_sec : ReturnCancellation.weightedBound δ (quartetCenteredPrimeSector σ γ h p) := by
      refine ⟨max (max C 0) M_neg, fun u => ?_⟩
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      rcases le_or_gt 0 u with hu | hu
      · calc Real.exp (δ * u) * ‖quartetCenteredPrimeSector σ γ h p u‖
            ≤ Real.exp (δ * u) * (max C 0 * Real.exp (-δ * u)) :=
              mul_le_mul_of_nonneg_left
                ((hC u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
                (Real.exp_pos _).le
          _ = max C 0 := by rw [mul_left_comm, ← Real.exp_add]; simp
          _ ≤ max (max C 0) M_neg := le_max_left _ _
      · obtain ⟨n, hn⟩ := exists_nat_ge ((u - (-S)) / echoDelay p)
        have hle_neg := hsec_nonpos n u hu.le (by linarith [(div_le_iff₀ hd_pos).mp hn])
        have hexp_le : Real.exp (δ * u) ≤ 1 :=
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hδ0.le hu.le)
        exact ((mul_le_of_le_one_left (norm_nonneg _) hexp_le).trans hle_neg).trans (le_max_right _ _)
    obtain ⟨Cr, hCr⟩ := (hwb_iff h hδ0.le hδ_half).mp hwb_sec
    refine hnot_refl ⟨Cr, fun u _ => ?_⟩
    have hb := hCr u
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hb
    exact (le_div_iff₀' (Real.exp_pos _)).mpr hb |>.trans_eq
      (by rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul])
  · intro S hS hs ⟨C, hC⟩
    have hδ0 : 0 < δ := lt_trans (by positivity) hδ
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hd_pos : 0 < echoDelay p := mul_pos (by norm_num) (Real.log_pos hp1)
    obtain ⟨_, hunit⟩ := quartet_schur_and_unitary h0 h1 hγ
    have href_unif : ∀ t : ℝ, ‖quartetReflected σ γ h t‖ ≤ ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ := by
      intro t
      have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
        ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
      unfold quartetReflected unitaryReflected
      refine norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun ξ => ?_)
      rw [norm_mul, norm_mul, (hunit ξ).2, mul_one, norm_exp_I_mul, mul_one]
    -- Every `T ≥ echoDelay p` decomposes as `T = echoDelay (p^k) + u` with `k ≥ 1` and `u ≥ 0`!
    set C_early : ℝ := (∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖) * Real.exp (δ * echoDelay p)
    refine hnot_refl ⟨max C C_early, fun T hT => ?_⟩
    by_cases hTd : T < echoDelay p
    · calc ‖quartetReflected σ γ h T‖
          ≤ ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ := href_unif T
        _ = C_early * Real.exp (-(δ * echoDelay p)) := by
            dsimp [C_early]; rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ max C C_early * Real.exp (-δ * T) :=
            mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr (by nlinarith))
              (Real.exp_pos _).le
              (le_trans (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (Real.exp_pos _).le)
                (le_max_right C C_early))
    · push Not at hTd
      set k : ℕ := ⌊T / echoDelay p⌋₊
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr <|
        (Nat.floor_pos.mpr ((one_le_div hd_pos).mpr hTd)).ne'
      set u : ℝ := T - (k : ℝ) * echoDelay p
      have hu0 : 0 ≤ u := sub_nonneg.mpr <|
        (le_div_iff₀ hd_pos).mp (Nat.floor_le (div_nonneg hT hd_pos.le))
      have hdel_pk : echoDelay (p ^ k) = (k : ℝ) * echoDelay p := by
        unfold echoDelay; push_cast; rw [Real.log_pow]; ring
      have hwt_pk : echoWeight (p ^ k) = 1 - 1 / (p : ℝ) := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        unfold echoWeight
        rw [Nat.totient_prime_pow hp (Nat.succ_pos j), Nat.cast_mul, Nat.cast_pow,
          Nat.cast_sub hp.one_le, Nat.cast_one, pow_succ]
        have hp_ne : (p : ℝ) ≠ 0 := by positivity
        have hpow_ne : (p : ℝ) ^ j ≠ 0 := pow_ne_zero j hp_ne
        field_simp [hp_ne, hpow_ne]
      have hT_eq : echoDelay (p ^ k) + u = T := by rw [hdel_pk]; dsimp [u]; ring
      have her := quartet_erase_one_return h0 h1 hγ h hS hs u (pow_pos hp.pos k)
      rw [hwt_pk, hT_eq] at her
      rw [← her]
      calc ‖quartetOthers σ γ h S u (p ^ k) + ((1 - 1 / (p : ℝ) : ℝ) : ℂ) * quartetBounce σ γ h u‖
          ≤ C * Real.exp (-δ * u) * (Real.exp (-2 * δ * Real.log p)) ^ k :=
            hC u k hk1 (by rw [hT_eq]; exact hT)
        _ = C * Real.exp (-δ * T) := by
            rw [← Real.exp_nat_mul, mul_assoc C, ← Real.exp_add]
            congr 2; unfold echoDelay at u; dsimp [u]; ring
        _ ≤ max C C_early * Real.exp (-δ * T) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-! ## 4. Master Resolution Theorem and Complete Corollaries -/

/-- **Unconditional Falsification of the Degree-One Integral Prime-Gate Scattering Axiom Class
at Every Positive Decay Rate `δ > 0`.**
For **every** `δ > 0` (including `δ = 3001 / 48000` and `δ = 1 / 4`), there exist `σ ∈ (7/8, 1)`
and `γ > 0` such that `xiQuartet σ γ`:
1. is strictly causal (`quartetEchoKernel σ γ τ = 0` and `quartetBounceKernel σ γ τ = 0` for `τ ≤ 0`),
   and its Laplace transform on `Re w > 1/2` factors into the causal single-bounce transform times
   `∏'_{p ∈ ℙ} primeEchoGate p w` — with **exact degree-one integral `ζ` gates at every prime**;
2. is entire, satisfies `ξ(1 - s) = ξ(s)` and strict real-axis positivity `0 < Re ξ(x)` on `ℝ`;
3. is globally Schur-passive with nonnegative Herglotz admittance on `Re w ≥ 0` and unitary on `i ℝ`;
4. obeys the exact `G_R` and `G_{RL}` zero-to-pole multiplicity dictionary at every zero of `xiQuartet`
   (including every nontrivial zero of `ζ`) and every arithmetic return / Möbius / `p = 2` sector
   recurrence identity;
5. yet has explicit compactly supported smooth pulses on which `quartetReflected σ γ`, the centered
   `p = 2` sector wavepacket, the `p = 2` sector `L²` tail energy, and the `2^k` prime-power
   cancellation error all **strictly fail** at rate `δ`! -/
theorem falsification_of_degree_one_integral_gate_axiom_class {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : ℝ, 7 / 8 < σ ∧ σ < 1 ∧
      ∀ γ : ℝ, 0 < γ →
        (∀ τ : ℝ, τ ≤ 0 → quartetEchoKernel σ γ τ = 0 ∧ quartetBounceKernel σ γ τ = 0) ∧
        (∀ w : ℂ, 1 / 2 < w.re →
          (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * quartetEchoKernel σ γ τ) =
            (∫ v : ℝ, Complex.exp (-w * (v : ℂ)) * quartetBounceKernel σ γ v) *
              (∏' p : Nat.Primes, primeEchoGate p w)) ∧
        Differentiable ℂ (xiQuartet σ γ) ∧
        (∀ s : ℂ, xiQuartet σ γ (1 - s) = xiQuartet σ γ s) ∧
        (∀ x : ℝ, 0 < (xiQuartet σ γ (x : ℂ)).re) ∧
        (∀ w : ℂ, 0 ≤ w.re → ‖quartetReducedScattering σ γ w‖ ≤ 1 ∧
          0 ≤ ((1 - quartetReducedScattering σ γ w) / (1 + quartetReducedScattering σ γ w)).re) ∧
        (∀ t : ℝ, ‖quartetScatteringPhase σ γ ((t : ℂ) * I)‖ = 1) ∧
        (∀ η : ℂ, xiQuartet σ γ η = 0 →
          meromorphicOrderAt (quartetRetardedCorrelator σ γ) (I * (η - 1) / 2) =
            -meromorphicOrderAt (xiQuartet σ γ) η ∧
          meromorphicOrderAt (quartetWightmanRL σ γ) (I * (η - 1) / 2) =
            -meromorphicOrderAt (xiQuartet σ γ) η ∧
          meromorphicOrderAt (quartetWightmanRL σ γ) (I * (η - 1) / 2) < 0) ∧
        (∀ (h : CompactPulse) (u : ℝ),
          quartetCenteredPrimeSector σ γ h 2 u =
            (1 / 2 : ℂ) * quartetReflected σ γ h u +
              (1 / 2 : ℂ) * quartetCenteredPrimeSector σ γ h 2 (u - echoDelay 2)) ∧
        (∃ h g : CompactPulse,
          (¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
            ‖quartetReflected σ γ h τ‖ ≤ C * Real.exp (-δ * τ)) ∧
          (¬ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
            ‖quartetCenteredPrimeSector σ γ g 2 u‖ ≤ C * Real.exp (-δ * u)) ∧
          (¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
            quartetSectorTailEnergy σ γ 2 g T ≤ ENNReal.ofReal (C * Real.exp (-2 * δ * T))) ∧
          (δ < 1 / 2 → ¬ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
            ‖quartetCenteredPrimeSector σ γ h 2 u‖ ≤ C * Real.exp (-δ * u))) := by
  set σ : ℝ := max (15 / 16) (1 - δ)
  have hσ78 : 7 / 8 < σ := lt_of_lt_of_le (by norm_num : (7 / 8 : ℝ) < 15 / 16) (le_max_left _ _)
  have hσ1 : σ < 1 := max_lt (by norm_num) (by linarith)
  have hσ_half : 1 / 2 < σ := by linarith
  have hδ_gt : (1 - σ) / 2 < δ := by
    have : 1 - δ ≤ σ := le_max_right _ _
    linarith
  refine ⟨σ, hσ78, hσ1, fun γ hγ => ?_⟩
  obtain ⟨hschur, hunit⟩ := quartet_schur_and_unitary hσ_half hσ1 hγ
  set p₀ : ℂ := (quartetZero σ γ - 1) / 2
  set h₀ : CompactPulse := excitingPulse p₀
  have ha_ne : pulseAmplitude h₀ (-I * p₀) ≠ 0 := pulseAmplitude_excitingPulse_ne_zero p₀
  obtain ⟨hnot_g_env, hnot_g_tail, hnot_h_env, _⟩ :=
    not_quartet_prime_sector_and_tower_decay_gt hσ_half hσ1 hγ Nat.prime_two h₀ ha_ne hδ_gt
  refine ⟨fun τ hτ => ⟨quartetEchoKernel_eq_zero_of_nonpos σ γ hτ,
      quartetBounceKernel_eq_zero_of_nonpos σ γ hτ⟩,
    fun w hw => (quartet_bounce_euler_factorization hσ_half hσ1 hγ hw).2,
    differentiable_xiQuartet σ γ,
    xiQuartet_one_sub σ γ,
    xiQuartet_real_pos hσ_half hγ,
    fun w hw => ⟨(hschur w hw).2.2.1, (hschur w hw).2.2.2⟩,
    fun t => (hunit t).2,
    fun η hη => ⟨(quartet_correlator_pole_dictionary hσ_half hσ1 hγ hη).2.2.1,
      (quartet_correlator_pole_dictionary hσ_half hσ1 hγ hη).2.2.2.1,
      (quartet_correlator_pole_dictionary hσ_half hσ1 hγ hη).2.2.2.2⟩,
    fun h u => by
      have hd := quartet_centered_sector_delay hσ_half hσ1 hγ h Nat.prime_two u
      norm_num at hd ⊢
      exact hd,
    ⟨h₀, ReturnCancellation.inverseSectorInput 2 h₀,
      not_quartetReflected_decay_gt hσ_half hσ1 hγ h₀ ha_ne hδ_gt,
      hnot_g_env, hnot_g_tail, hnot_h_env⟩⟩

/-- **Master Capstone Theorem: Complete Unconditional Solution to the Degree-One Integral
Prime-Gate Question, Its `p = 2` Sector Test, the Schur-Twin Contrast, and All Positive Rigidity
and Classification Corollaries.** -/
theorem complete_resolution_of_degree_one_integral_gate_question :
    -- (I) Falsification of the general scattering axiom class & `p = 2` sector test at both
    --     `δ = 3001 / 48000` and `δ = 1 / 4` (and indeed every `δ > 0`):
    (∀ δ : ℝ, 0 < δ → ∃ σ : ℝ, 7 / 8 < σ ∧ σ < 1 ∧
      (∀ τ : ℝ, τ ≤ 0 → quartetEchoKernel σ 1 τ = 0 ∧ quartetBounceKernel σ 1 τ = 0) ∧
      (∀ w : ℂ, 1 / 2 < w.re →
        (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * quartetEchoKernel σ 1 τ) =
          (∫ v : ℝ, Complex.exp (-w * (v : ℂ)) * quartetBounceKernel σ 1 v) *
            (∏' p : Nat.Primes, primeEchoGate p w)) ∧
      Differentiable ℂ (xiQuartet σ 1) ∧
      (∀ s : ℂ, xiQuartet σ 1 (1 - s) = xiQuartet σ 1 s) ∧
      (∀ x : ℝ, 0 < (xiQuartet σ 1 (x : ℂ)).re) ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖quartetReducedScattering σ 1 w‖ ≤ 1 ∧
        0 ≤ ((1 - quartetReducedScattering σ 1 w) / (1 + quartetReducedScattering σ 1 w)).re) ∧
      (∀ t : ℝ, ‖quartetScatteringPhase σ 1 ((t : ℂ) * I)‖ = 1) ∧
      (∃ h g : CompactPulse,
        (¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ‖quartetReflected σ 1 h τ‖ ≤ C * Real.exp (-δ * τ)) ∧
        (¬ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
          ‖quartetCenteredPrimeSector σ 1 g 2 u‖ ≤ C * Real.exp (-δ * u)) ∧
        (¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
          quartetSectorTailEnergy σ 1 2 g T ≤ ENNReal.ofReal (C * Real.exp (-2 * δ * T))))) ∧
    -- (II) Actual modular `p = 2` sector vs. Prime-2 Schur Twin contrast:
    ((RiemannHypothesis ↔ ∀ σ : ℝ, 0 < σ → σ < 1 / 4 → ∀ h : CompactPulse,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
          ReturnCancellation.sectorTailEnergy 2 h T ≤ ENNReal.ofReal (C * Real.exp (-2 * σ * T))) ∧
     (∀ σ : ℝ, 0 < σ → σ < 3001 / 48000 → ∀ h : CompactPulse,
        ReturnCancellation.weightedBound σ (ReturnCancellation.centeredPrimeSector h 2)) ∧
     (∃ α : ℝ, 7 / 8 < α ∧ α < 1 ∧ ∃ h : CompactPulse,
        ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
          ‖deformedReflectedField α h τ‖ ≤ C * Real.exp (-(3001 / 48000 : ℝ) * τ))) ∧
    -- (III) Pure-bounce `B(w, 1/2)` degree-one rational prime-gate dichotomy & RH equivalence:
    (∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ {ε : ℕ → ℂ}, (∀ p ∈ S, ‖ε p‖ = 1) →
      (∀ σ : ℝ, 0 < σ → σ < 3001 / 48000 → ∀ h : CompactPulse,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
          ‖finiteFlippedReflected S ε h τ‖ ≤ C * Real.exp (-σ * τ)) ∧
      (RiemannHypothesis ↔ ∀ σ : ℝ, 0 < σ → σ < 1 / 4 → ∀ h : CompactPulse,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
          ‖finiteFlippedReflected S ε h τ‖ ≤ C * Real.exp (-σ * τ))) ∧
    -- (IV) Sharpness of degree one: integral-trace degree-two slow modes exist for every `p ≥ 5`:
    (∀ p : ℕ, 5 ≤ p → ∃ h : CompactPulse,
      ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖twinReflected p (p : ℝ) h τ‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * τ)) ∧
    -- (V) Extended Selberg class degree-one integral prime-gate rigidity & unique `ζ` pinning:
    (∀ (F : ExtendedSelbergClass), F.gammaData.degree = 1 → ∀ {a : ℕ → ℤ},
      F.coeff 1 = 1 →
      (∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → F.coeff (m * n) = F.coeff m * F.coeff n) →
      (∀ {p : ℕ}, p.Prime → ∀ k : ℕ, F.coeff (p ^ k) = ((a p : ℤ) : ℂ) ^ k) →
      (∀ {p : ℕ}, p.Prime → a p = -1 ∨ a p = 0 ∨ a p = 1) ∧
      F.gammaData.internalShift = 0 ∧
      (F.gammaData.conductor = 1 ↔ meromorphicOrderAt F 1 < 0) ∧
      (F.gammaData.conductor = 1 →
        (∀ {p : ℕ}, p.Prime → a p = 1) ∧ ∀ s : ℂ, s ≠ 1 → F s = riemannZeta s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨σ, hσ78, hσ1, H⟩ := falsification_of_degree_one_integral_gate_axiom_class hδ
    obtain ⟨hcaus, heuler, hdiff, hfe, hreal, hpass, hunit, _, _, ⟨h, g, hn1, hn2, hn3, _⟩⟩ :=
      H 1 one_pos
    exact ⟨σ, hσ78, hσ1, hcaus, heuler, hdiff, hfe, hreal, hpass, hunit, h, g, hn1, hn2, hn3⟩
  · refine ⟨ReturnCancellation.rh_iff_one_prime_tail Nat.prime_two, ?_, ?_⟩
    · intro σ hσ0 hσ_top h
      have hzf : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re →
          ρ.re ≤ 1 - 2 * (3001 / 48000 : ℝ) := by
        intro ρ h0' hpos
        linarith [(GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip
          hpos h0').2]
      exact (ReturnCancellation.strip_iff_one_prime_sector
        (δ := 3001 / 48000) (by norm_num) (by norm_num) Nat.prime_two).mp hzf σ hσ0 hσ_top h
    · obtain ⟨α, hα78, hα1, _, _, _, _, _, _, hfail⟩ :=
        universal_causal_ringdown_infimum_zero (δ := 3001 / 48000) (by norm_num)
      exact ⟨α, hα78, hα1, hfail⟩
  · intro S hS ε hε
    exact finiteFlipped_strip_and_rh_equivalence S hS hε
  · intro p hp5
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfail4⟩ :=
      integral_trace_degree_two_slow_mode_of_ge_five hp5
    exact hfail4
  · intro F hd a h1 hmul hpow
    obtain ⟨hsigns, hθ0, _⟩ := degreeOne_integral_gate_classification F hd h1 hmul hpow
    obtain ⟨hiff, hpin⟩ := degreeOne_integral_gate_eq_zeta_iff F hd h1 hmul hpow
    exact ⟨hsigns, hθ0, hiff, fun hc => ⟨(hpin hc).2.1, (hpin hc).2.2⟩⟩

#print axioms quartet_bounce_euler_factorization
#print axioms quartet_finite_return_sum
#print axioms quartet_mobius_scattering_returns
#print axioms quartet_centered_sector_delay
#print axioms quartet_prime_sector_equivalence_and_inverse
#print axioms quartet_correlator_pole_dictionary
#print axioms not_quartetReflected_l2_tail_decay_gt
#print axioms not_quartet_prime_sector_and_tower_decay_gt
#print axioms falsification_of_degree_one_integral_gate_axiom_class
#print axioms complete_resolution_of_degree_one_integral_gate_question

end GaloisForLFunctions.BlackHoleRingdown
