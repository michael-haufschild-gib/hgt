import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszIncrementsAreLipschitzInL1
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheGreenCornerReadsThePotential

/-!
# The endpoint traces are absolutely continuous before contact

For disjoint `(a_i, b_i)` in a compact precontact interval, put `Δ_i = s_{b_i} − ρ_i s_{a_i}` and `Φ = Σ_i |Δ_i|`.

**Partial variation** (`exists_partial_variation_bound`). `sup_t Φ(t) ≤ C₁ (V(η) + δ/η) + C₂ δ`, with `δ = Σ_i (b_i − a_i)`,
for every `η > 0`. In particular `x ↦ s_x(t)` has bounded variation, uniformly in `t`, and the variation over a set
of small measure is uniformly small.

The proof reads each `Δ_i(t)` in a chart. Near the left edge, which does not move, `Δ_i = G[F_{b_i} − ρ_i F_{a_i}]`. Near the
right edge, read from the edge of the smaller window `y = 2a_i − t`,

  `Δ_i(t) = ∫_{(0,y]} v(s) (𝓡_{b_i}(y − s + τ_i) − ρ_i 𝓡_{a_i}(y − s)) ds + ∫_{(y, y+τ_i]} v(s) 𝓡_{b_i}(y + τ_i − s) ds`,

`τ_i = 2(b_i − a_i)`. The second integral is at most `A (V(2b_i − t) − V(2a_i − t))`, whose sum is the `v`-mass of a set
of measure `2δ`. In the first integral, the forcing difference is `M[|Δ_i|](T) + c ‖Δ_i‖₁`, with `T = 2a_i − w` the physical
point, and the level `2a_i − (y − s) = t + s` does not depend on `i`. So the sum over `i` passes under the integral,
and the double causal average of `M[Φ]` is at most `V(ε) K ‖Φ‖_∞ + K ‖Φ‖₁/ε`. Take `K V(ε) ≤ ½` and absorb. The
`L¹` mass is `≲ δ` by the Lipschitz bound.

**Traces** (`absolutelyContinuousOnInterval_leftTraceAt`). `x ↦ τ_L(x, z)` is absolutely continuous on every compact precontact
interval, for every `z`.

**The potential** (`absolutelyContinuousOnInterval_canonicalPotential`). So is `Ψ`, and `Ψ(b) − Ψ(a) = ∫_a^b Ψ′`, with `Ψ′`
integrable (`integral_deriv_canonicalPotential`): the potential `q = Ψ′` is a function, before contact.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

local notation "v" => logarithmicCausalKernel
local notation "V" => logarithmicRenewalMass

/-! ### The level mass of a density -/

/-- The causal average of a density at a level. -/
def levelMass (g : ℝ → ℝ) (p : ℝ) : ℝ := ∫ w, v (w - p) * g w

private theorem integrable_kernel_shift (p : ℝ) : Integrable (fun w : ℝ => v (w - p)) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure ℝ) (-p)).integrable_comp_of_integrable
      logarithmicCausalKernel_mass_one.1

private theorem integral_kernel_shift (p : ℝ) : ∫ w : ℝ, v (w - p) = 1 := by
  rw [integral_sub_right_eq_self, logarithmicCausalKernel_mass_one.2]

theorem integrable_kernel_mul {g : ℝ → ℝ} (hgm : Measurable g) {G : ℝ} (hgG : ∀ y, |g y| ≤ G)
    (p : ℝ) : Integrable (fun w => v (w - p) * g w) :=
  (integrable_kernel_shift p).mul_bdd hgm.aestronglyMeasurable
    (Eventually.of_forall fun y => by rwa [Real.norm_eq_abs])

theorem levelMass_nonneg {g : ℝ → ℝ} (hg0 : ∀ y, 0 ≤ g y) (p : ℝ) : 0 ≤ levelMass g p :=
  integral_nonneg fun w => mul_nonneg (logarithmicCausalKernel_nonneg _) (hg0 w)

theorem levelMass_le {g : ℝ → ℝ} (hgm : Measurable g) (hg0 : ∀ y, 0 ≤ g y) {G : ℝ}
    (hgG : ∀ y, g y ≤ G) (p : ℝ) : levelMass g p ≤ G := by
  have hab : ∀ y, |g y| ≤ G := fun y => by
    rw [abs_of_nonneg (hg0 y)]
    exact hgG y
  calc
    _ ≤ ∫ w, v (w - p) * G :=
      integral_mono (integrable_kernel_mul hgm hab p) ((integrable_kernel_shift p).mul_const G)
        fun w => mul_le_mul_of_nonneg_left (hgG w) (logarithmicCausalKernel_nonneg _)
    _ = G := by rw [integral_mul_const, integral_kernel_shift, one_mul]

/-- The near part of the kernel sees the sup norm, the far part the `L¹` norm. -/
theorem levelMass_le_split {g : ℝ → ℝ} (hgm : Measurable g) (hgi : Integrable g) (hg0 : ∀ y, 0 ≤ g y)
    {G ε : ℝ} (hG : 0 ≤ G) (hgG : ∀ y, g y ≤ G) (hε : 0 < ε) (p : ℝ) :
    levelMass g p ≤ G * V ε + (∫ y, g y) / ε := by
  have h := norm_logarithmicBackwardConvolution_le_of_majorant (f := fun y => (g y : ℂ)) (B := 0)
    hgm hgi hg0 hG hgG hε (Eventually.of_forall fun y => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hg0 y), add_zero]) p
  have he : logarithmicBackwardConvolution (fun y => (g y : ℂ)) p = ((levelMass g p : ℝ) : ℂ) := by
    rw [levelMass, ← integral_complex_ofReal]
    unfold logarithmicBackwardConvolution
    apply integral_congr_ae
    filter_upwards with y
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_of_nonneg (levelMass_nonneg hg0 p), add_zero] at h
  exact h

theorem measurable_levelMass {g : ℝ → ℝ} (hgm : Measurable g) : Measurable (levelMass g) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  exact ((measurable_logarithmicCausalKernel.comp (measurable_snd.sub measurable_fst)).mul
    (hgm.comp measurable_snd)).stronglyMeasurable

/-! ### The chart majorant -/

theorem integrable_chartMajorant (N : Finset ℕ) {S : ℝ → ℂ} (hi : Integrable S) :
    Integrable (chartMajorant N S) ∧
      ∫ y, chartMajorant N S y = chartSupConstant N * ∫ t, ‖S t‖ := by
  have hn : Integrable (fun t => ‖S t‖) := hi.norm
  have hshift (τ : ℝ) : Integrable (fun y => ‖S (y + τ)‖) := hn.comp_add_right τ
  have hminus (τ : ℝ) : Integrable (fun y => ‖S (y - τ)‖) := hn.comp_sub_right τ
  have hterm (n : ℕ) : Integrable (fun y => criticalMellinAtomWeight n *
      (‖S (y + Real.log n)‖ + ‖S (y - Real.log n)‖)) :=
    ((hshift _).add (hminus _)).const_mul _
  have hsum : Integrable (fun y => ∑ n ∈ N, criticalMellinAtomWeight n *
      (‖S (y + Real.log n)‖ + ‖S (y - Real.log n)‖)) :=
    integrable_finsetSum _ fun n _ => hterm n
  refine ⟨(hn.const_mul _).add hsum, ?_⟩
  unfold chartMajorant
  rw [integral_add (hn.const_mul _) hsum, integral_const_mul,
    integral_finsetSum _ fun n _ => hterm n]
  unfold chartSupConstant chartPrimeMass
  rw [add_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_add (hshift _) (hminus _),
    integral_add_right_eq_self (fun y => ‖S y‖), integral_sub_right_eq_self (fun y => ‖S y‖)]
  ring

/-- The majorant is invariant under reflection. -/
theorem chartMajorant_reflect (N : Finset ℕ) (S : ℝ → ℂ) (c w : ℝ) :
    chartMajorant N (fun t => S (c - t)) w = chartMajorant N S (c - w) := by
  unfold chartMajorant
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show c - (w + Real.log n) = c - w - Real.log n by ring,
    show c - (w - Real.log n) = c - w + Real.log n by ring, add_comm (‖S (c - w - Real.log n)‖)]

/-! ### Translating a chart forcing -/

theorem chartPrime_translate (N : Finset ℕ) (S : ℝ → ℂ) (τ w : ℝ) :
    chartPrime N S (w + τ) = chartPrime N (fun t => S (t + τ)) w := by
  unfold chartPrime
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show w + τ + Real.log n = w + Real.log n + τ by ring,
    show w + τ - Real.log n = w - Real.log n + τ by ring]

theorem chartBounded_translate (S : ℝ → ℂ) (τ w : ℝ) :
    chartBounded S (w + τ) = chartBounded (fun t => S (t + τ)) w := by
  have h1 : (∫ t : ℝ, (archLogRemainder |w + τ - t| : ℂ) * S t) =
      ∫ t : ℝ, (archLogRemainder |w - t| : ℂ) * S (t + τ) := by
    rw [← integral_add_right_eq_self (fun t : ℝ => (archLogRemainder |w + τ - t| : ℂ) * S t) τ]
    apply integral_congr_ae
    filter_upwards with t
    rw [show w + τ - (t + τ) = w - t by ring]
  have h2 (σ : ℝ) : (∫ t : ℝ, (Real.exp (σ * t) : ℂ) * S t) =
      (Real.exp (σ * τ) : ℂ) * ∫ t : ℝ, (Real.exp (σ * t) : ℂ) * S (t + τ) := by
    rw [← integral_add_right_eq_self (fun t : ℝ => (Real.exp (σ * t) : ℂ) * S t) τ,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [show σ * (t + τ) = σ * τ + σ * t by ring, Real.exp_add]
    push_cast
    ring
  have e1 : (Real.exp ((1 / 2) * (w + τ)) : ℂ) * (Real.exp ((-1 / 2) * τ) : ℂ) =
      (Real.exp ((1 / 2) * w) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have e2 : (Real.exp ((-1 / 2) * (w + τ)) : ℂ) * (Real.exp ((1 / 2) * τ) : ℂ) =
      (Real.exp ((-1 / 2) * w) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  unfold chartBounded
  rw [h1, h2, h2]
  linear_combination (-(∫ t : ℝ, (Real.exp ((-1 / 2) * t) : ℂ) * S (t + τ))) * e1 -
    (∫ t : ℝ, (Real.exp ((1 / 2) * t) : ℂ) * S (t + τ)) * e2

theorem commutatorIntegral_translate (Ca Cb : ChartCutoff) {τ : ℝ}
    (hshift : ∀ r, Cb.toFun r = Ca.toFun (r - τ)) (S : ℝ → ℂ) (w : ℝ) :
    Cb.commutatorIntegral S (w + τ) = Ca.commutatorIntegral (fun t => S (t + τ)) w := by
  unfold ChartCutoff.commutatorIntegral
  rw [← integral_add_right_eq_self
    (fun t : ℝ => logarithmicCutoffKernel Cb.toFun (w + τ) t * S t) τ]
  apply integral_congr_ae
  filter_upwards with t
  unfold logarithmicCutoffKernel
  rw [hshift (w + τ), hshift (t + τ), add_sub_cancel_right, add_sub_cancel_right,
    show w + τ - (t + τ) = w - t by ring]

/-- The size of a chart combination. -/
theorem norm_chart_combination_le (C : ChartCutoff) (N : Finset ℕ) {S : ℝ → ℂ} (hi : Integrable S)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (w : ℝ) (hb : C.toFun w ≠ 0 → ‖chartBounded S w‖ ≤ Bd) :
    ‖(C.toFun w : ℂ) * (chartMass * S w + chartBounded S w + chartPrime N S w) +
        C.commutatorIntegral S w‖ ≤ chartMajorant N S w + Bd + C.lip / 2 * ∫ t, ‖S t‖ := by
  refine (norm_add_le _ _).trans ?_
  have hcomm := C.norm_commutatorIntegral_le hi w
  have hmaj := chartMajorant_nonneg N S w
  suffices h : ‖(C.toFun w : ℂ) * (chartMass * S w + chartBounded S w + chartPrime N S w)‖ ≤
      chartMajorant N S w + Bd by
    linarith only [h, hcomm]
  by_cases h0 : C.toFun w = 0
  · rw [h0, Complex.ofReal_zero, zero_mul, norm_zero]
    linarith only [hmaj, hBd0]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsum : ‖chartMass * S w + chartBounded S w + chartPrime N S w‖ ≤ chartMajorant N S w + Bd := by
    have he : chartMass * S w + chartBounded S w + chartPrime N S w =
        (chartMass * S w + chartPrime N S w) + chartBounded S w := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_mass_add_prime_le N S w) (hb h0))
  calc
    _ ≤ 1 * (chartMajorant N S w + Bd) := mul_le_mul (C.abs_le w) hsum (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-! ### The Green representation of a shifted pair -/

private theorem integrable_kernel_readout (f : LogarithmicHalfLineL2) {A : ℝ}
    (hf : ∀ᵐ x ∂volume, ‖(f : RealLineL2) x‖ ≤ A) (c : ℝ) :
    Integrable (fun s : ℝ => (v s : ℂ) * logarithmicBackwardConvolution (f : RealLineL2) (c - s)) :=
  (Complex.ofRealCLM.integrable_comp logarithmicCausalKernel_mass_one.1).mul_bdd
    ((measurable_logarithmicBackwardConvolution
      (Lp.stronglyMeasurable (f : RealLineL2)).measurable).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    (Eventually.of_forall fun s => norm_logarithmicBackwardConvolution_le hf _)

/-- The renewal mass is additive across a level. -/
theorem logarithmicRenewalMass_add {y τ : ℝ} (hy : 0 ≤ y) (hτ : 0 ≤ τ) :
    V (y + τ) = V y + ∫ s in Ioc y (y + τ), v s := by
  unfold logarithmicRenewalMass
  rw [← Ioc_union_Ioc_eq_Ioc hy (le_add_of_nonneg_right hτ)]
  exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    logarithmicCausalKernel_mass_one.1.integrableOn logarithmicCausalKernel_mass_one.1.integrableOn

/-- The difference of two Green solutions, read from the edge of the second. -/
theorem norm_green_shift_sub_le (f₁ f₂ : LogarithmicHalfLineL2) (ρ : ℂ) {τ y A₁ A₂ : ℝ}
    (hτ : 0 ≤ τ) (hy : 0 ≤ y) (h₁ : ∀ᵐ x ∂volume, ‖(f₁ : RealLineL2) x‖ ≤ A₁)
    (h₂ : ∀ᵐ x ∂volume, ‖(f₂ : RealLineL2) x‖ ≤ A₂) :
    ‖logarithmicGreenRepresentative f₂ (y + τ) - ρ * logarithmicGreenRepresentative f₁ y‖ ≤
      A₂ * (V (y + τ) - V y) + ∫ s in Ioc 0 y, v s *
        ‖logarithmicBackwardConvolution (f₂ : RealLineL2) (y - s + τ) -
          ρ * logarithmicBackwardConvolution (f₁ : RealLineL2) (y - s)‖ := by
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = logarithmicBackwardConvolution (f₁ : RealLineL2) := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R₂, R₂ = logarithmicBackwardConvolution (f₂ : RealLineL2) := ⟨_, rfl⟩
  have hi₁ := integrable_kernel_readout f₁ h₁ y
  have hi₂ := integrable_kernel_readout f₂ h₂ (y + τ)
  rw [← hR₁] at hi₁
  rw [← hR₂] at hi₂
  rw [← hR₁, ← hR₂]
  have hsplit : logarithmicGreenRepresentative f₂ (y + τ) =
      (∫ s in Ioc 0 y, (v s : ℂ) * R₂ (y + τ - s)) + ∫ s in Ioc y (y + τ), (v s : ℂ) * R₂ (y + τ - s) := by
    unfold logarithmicGreenRepresentative
    rw [← hR₂, ← Ioc_union_Ioc_eq_Ioc hy (le_add_of_nonneg_right hτ)]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi₂.integrableOn
      hi₂.integrableOn
  have hG₁ : logarithmicGreenRepresentative f₁ y = ∫ s in Ioc 0 y, (v s : ℂ) * R₁ (y - s) := by
    unfold logarithmicGreenRepresentative
    rw [← hR₁]
  have hdiff : logarithmicGreenRepresentative f₂ (y + τ) - ρ * logarithmicGreenRepresentative f₁ y =
      (∫ s in Ioc y (y + τ), (v s : ℂ) * R₂ (y + τ - s)) +
        ∫ s in Ioc 0 y, (v s : ℂ) * (R₂ (y - s + τ) - ρ * R₁ (y - s)) := by
    have hcomb : (∫ s in Ioc 0 y, (v s : ℂ) * (R₂ (y - s + τ) - ρ * R₁ (y - s))) =
        (∫ s in Ioc 0 y, (v s : ℂ) * R₂ (y + τ - s)) - ρ * ∫ s in Ioc 0 y, (v s : ℂ) * R₁ (y - s) := by
      rw [← integral_const_mul, ← integral_sub hi₂.integrableOn (hi₁.integrableOn.const_mul ρ)]
      apply integral_congr_ae
      filter_upwards with s
      rw [show y - s + τ = y + τ - s by ring]
      ring
    rw [hsplit, hG₁, hcomb]
    ring
  rw [hdiff]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hv : ∀ s ∈ Ioc y (y + τ), ‖(v s : ℂ) * R₂ (y + τ - s)‖ ≤ v s * A₂ := fun s _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _), hR₂]
      exact mul_le_mul_of_nonneg_left (norm_logarithmicBackwardConvolution_le h₂ _)
        (logarithmicCausalKernel_nonneg _)
    have hle : ‖∫ s in Ioc y (y + τ), (v s : ℂ) * R₂ (y + τ - s)‖ ≤ ∫ s in Ioc y (y + τ), v s * A₂ :=
      norm_integral_le_of_norm_le ((logarithmicCausalKernel_mass_one.1.mul_const A₂).integrableOn)
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hv))
    rw [integral_mul_const] at hle
    rw [logarithmicRenewalMass_add hy hτ]
    linarith only [hle]
  · refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with s
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]

/-- The readout of a shifted pair is the readout of the forcing difference. -/
theorem norm_readout_shift_sub_le (f₁ f₂ : LogarithmicHalfLineL2) (ρ : ℂ) {τ p A₁ A₂ B : ℝ}
    (hp : 0 ≤ p) (h₁ : ∀ᵐ x ∂volume, ‖(f₁ : RealLineL2) x‖ ≤ A₁)
    (h₂ : ∀ᵐ x ∂volume, ‖(f₂ : RealLineL2) x‖ ≤ A₂) {g : ℝ → ℝ} (hgm : Measurable g)
    {G : ℝ} (hgG : ∀ y, |g y| ≤ G)
    (hdom : ∀ᵐ w ∂volume, 0 ≤ w → ‖(f₂ : RealLineL2) (w + τ) - ρ * (f₁ : RealLineL2) w‖ ≤ g w + B)
    (hg0 : ∀ y, 0 ≤ g y) (hB : 0 ≤ B) :
    ‖logarithmicBackwardConvolution (f₂ : RealLineL2) (p + τ) -
        ρ * logarithmicBackwardConvolution (f₁ : RealLineL2) p‖ ≤ levelMass g p + B := by
  have hk (q : ℝ) : Integrable (fun y : ℝ => (v (y - q) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (integrable_kernel_shift q)
  have hi₁ : Integrable (fun y : ℝ => (v (y - p) : ℂ) * (f₁ : RealLineL2) y) :=
    (hk p).mul_bdd (Lp.aestronglyMeasurable _) h₁
  have ht₂ := (measurePreserving_add_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae h₂
  have hi₂ : Integrable (fun y : ℝ => (v (y - p) : ℂ) * (f₂ : RealLineL2) (y + τ)) :=
    (hk p).mul_bdd ((Lp.aestronglyMeasurable _).comp_quasiMeasurePreserving
      (measurePreserving_add_right (volume : Measure ℝ) τ).quasiMeasurePreserving) ht₂
  have hval : logarithmicBackwardConvolution (f₂ : RealLineL2) (p + τ) -
      ρ * logarithmicBackwardConvolution (f₁ : RealLineL2) p =
      ∫ w : ℝ, (v (w - p) : ℂ) * ((f₂ : RealLineL2) (w + τ) - ρ * (f₁ : RealLineL2) w) := by
    have h2 : logarithmicBackwardConvolution (f₂ : RealLineL2) (p + τ) =
        ∫ w : ℝ, (v (w - p) : ℂ) * (f₂ : RealLineL2) (w + τ) := by
      unfold logarithmicBackwardConvolution
      rw [← integral_add_right_eq_self
        (fun y : ℝ => (v (y - (p + τ)) : ℂ) * (f₂ : RealLineL2) y) τ]
      apply integral_congr_ae
      filter_upwards with w
      rw [show w + τ - (p + τ) = w - p by ring]
    rw [h2]
    unfold logarithmicBackwardConvolution
    rw [← integral_const_mul, ← integral_sub hi₂ (hi₁.const_mul ρ)]
    apply integral_congr_ae
    filter_upwards with w
    ring
  have hab : ∀ y, |g y| ≤ G := hgG
  have hmaj : Integrable (fun w => v (w - p) * g w + v (w - p) * B) :=
    (integrable_kernel_mul hgm hab p).add ((integrable_kernel_shift p).mul_const B)
  rw [hval]
  calc
    _ ≤ ∫ w, (v (w - p) * g w + v (w - p) * B) := by
      apply norm_integral_le_of_norm_le hmaj
      filter_upwards [hdom] with w hw
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _),
        ← mul_add]
      by_cases hwp : w - p ≤ 0
      · rw [logarithmicCausalKernel_of_nonpos hwp, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (hw (by linarith only [not_le.mp hwp, hp]))
          (logarithmicCausalKernel_nonneg _)
    _ = _ := by
      rw [integral_add (integrable_kernel_mul hgm hab p) ((integrable_kernel_shift p).mul_const B),
        integral_mul_const, integral_kernel_shift, one_mul]
      rfl

/-- **The difference of two Green solutions, in terms of the level mass of the forcing difference.** -/
theorem norm_green_shift_le_level (f₁ f₂ : LogarithmicHalfLineL2) (ρ : ℂ) {τ y A₁ A₂ B : ℝ}
    (hτ : 0 ≤ τ) (hy : 0 ≤ y) (h₁ : ∀ᵐ x ∂volume, ‖(f₁ : RealLineL2) x‖ ≤ A₁)
    (h₂ : ∀ᵐ x ∂volume, ‖(f₂ : RealLineL2) x‖ ≤ A₂) {g : ℝ → ℝ} (hgm : Measurable g)
    {G : ℝ} (hgG : ∀ y, |g y| ≤ G)
    (hdom : ∀ᵐ w ∂volume, 0 ≤ w → ‖(f₂ : RealLineL2) (w + τ) - ρ * (f₁ : RealLineL2) w‖ ≤ g w + B)
    (hg0 : ∀ y, 0 ≤ g y) (hB : 0 ≤ B) :
    ‖logarithmicGreenRepresentative f₂ (y + τ) - ρ * logarithmicGreenRepresentative f₁ y‖ ≤
      A₂ * (V (y + τ) - V y) + ∫ s in Ioc 0 y, v s * (levelMass g (y - s) + B) := by
  refine (norm_green_shift_sub_le f₁ f₂ ρ hτ hy h₁ h₂).trans (add_le_add le_rfl ?_)
  have hA₁ : 0 ≤ A₁ := (norm_nonneg _).trans (h₁.exists.choose_spec)
  have hA₂ : 0 ≤ A₂ := (norm_nonneg _).trans (h₂.exists.choose_spec)
  have hm₁ := (measurable_logarithmicBackwardConvolution
    (Lp.stronglyMeasurable (f₁ : RealLineL2)).measurable)
  have hm₂ := (measurable_logarithmicBackwardConvolution
    (Lp.stronglyMeasurable (f₂ : RealLineL2)).measurable)
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hgG 0)
  have hi₁ : IntegrableOn (fun s => v s * ‖logarithmicBackwardConvolution (f₂ : RealLineL2) (y - s + τ) -
      ρ * logarithmicBackwardConvolution (f₁ : RealLineL2) (y - s)‖) (Ioc 0 y) := by
    refine (logarithmicCausalKernel_mass_one.1.mul_bdd (c := A₂ + ‖ρ‖ * A₁) ?_ ?_).integrableOn
    · exact (((hm₂.comp ((measurable_const.sub measurable_id).add_const τ)).sub
        ((hm₁.comp (measurable_const.sub measurable_id)).const_mul ρ)).norm).aestronglyMeasurable
    · refine Eventually.of_forall fun s => ?_
      rw [norm_norm]
      refine (norm_sub_le _ _).trans (add_le_add (norm_logarithmicBackwardConvolution_le h₂ _) ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_logarithmicBackwardConvolution_le h₁ _) (norm_nonneg _)
  have hi₂ : IntegrableOn (fun s => v s * (levelMass g (y - s) + B)) (Ioc 0 y) := by
    refine (logarithmicCausalKernel_mass_one.1.mul_bdd (c := G + B) ?_ ?_).integrableOn
    · exact (((measurable_levelMass hgm).comp (measurable_const.sub measurable_id)).add_const
        B).aestronglyMeasurable
    · refine Eventually.of_forall fun s => ?_
      rw [Real.norm_of_nonneg (add_nonneg (levelMass_nonneg hg0 _) hB)]
      exact add_le_add (levelMass_le hgm hg0 (fun y => (le_abs_self _).trans (hgG y)) _) le_rfl
  refine setIntegral_mono_on hi₁ hi₂ measurableSet_Ioc fun s hs => ?_
  exact mul_le_mul_of_nonneg_left (norm_readout_shift_sub_le f₁ f₂ ρ (sub_nonneg.mpr hs.2) h₁ h₂ hgm hgG
    hdom hg0 hB) (logarithmicCausalKernel_nonneg _)

/-- Summing causal integrals of nonnegative levels over their domains. -/
theorem sum_setIntegral_kernel_le (S : Finset ℕ) (E : ℕ → ℝ → ℝ) (x : ℕ → ℝ)
    (hEm : ∀ i ∈ S, Measurable (E i)) (hE0 : ∀ i ∈ S, ∀ s, 0 ≤ E i s)
    (hEB : ∀ i ∈ S, ∃ B, ∀ s, E i s ≤ B) {Θ : ℝ} (hΘ : ∀ s, ∑ i ∈ S, E i s ≤ Θ) :
    ∑ i ∈ S, ∫ s in Ioc 0 (x i), v s * E i s ≤ Θ := by
  have hi (i : ℕ) (hi : i ∈ S) : Integrable (fun s => v s * E i s) := by
    obtain ⟨B, hB⟩ := hEB i hi
    exact logarithmicCausalKernel_mass_one.1.mul_bdd (hEm i hi).aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [Real.norm_of_nonneg (hE0 i hi s)]
        exact hB s)
  have hnn (i : ℕ) (hi : i ∈ S) (s : ℝ) : 0 ≤ v s * E i s :=
    mul_nonneg (logarithmicCausalKernel_nonneg _) (hE0 i hi s)
  calc
    _ ≤ ∑ i ∈ S, ∫ s, v s * E i s := Finset.sum_le_sum fun i hS =>
      setIntegral_le_integral (hi i hS) (Eventually.of_forall (hnn i hS))
    _ = ∫ s, ∑ i ∈ S, v s * E i s := (integral_finsetSum _ hi).symm
    _ ≤ ∫ s, v s * Θ := by
      apply integral_mono (integrable_finsetSum _ hi)
        (logarithmicCausalKernel_mass_one.1.mul_const Θ)
      intro s
      simp only
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hΘ s) (logarithmicCausalKernel_nonneg _)
    _ = Θ := by rw [integral_mul_const, logarithmicCausalKernel_mass_one.2, one_mul]

/-- The `v`-mass of disjoint intervals of small total length is small. -/
theorem sum_setIntegral_kernel_disjoint_le (S : Finset ℕ) (α β : ℕ → ℝ)
    (hαβ : ∀ i ∈ S, α i ≤ β i)
    (hdis : Set.PairwiseDisjoint (↑S : Set ℕ) fun i => Ioc (α i) (β i)) {η : ℝ} (hη : 0 < η) :
    ∑ i ∈ S, ∫ s in Ioc (α i) (β i), v s ≤ V η + (∑ i ∈ S, (β i - α i)) / η := by
  have hint := logarithmicCausalKernel_mass_one.1
  have hpt (i : ℕ) (hi : i ∈ S) : ∫ s in Ioc (α i) (β i), v s ≤
      (∫ s in Ioc (α i) (β i) ∩ Ioc 0 η, v s) + (β i - α i) / η := by
    have hu : Ioc (α i) (β i) = (Ioc (α i) (β i) ∩ Ioc 0 η) ∪ (Ioc (α i) (β i) \ Ioc 0 η) :=
      (Set.inter_union_diff _ _).symm
    conv_lhs => rw [hu]
    rw [setIntegral_union (Set.disjoint_sdiff_right.mono_left Set.inter_subset_right)
      (measurableSet_Ioc.diff measurableSet_Ioc) hint.integrableOn hint.integrableOn]
    refine add_le_add le_rfl ?_
    have hb : ∀ s ∈ Ioc (α i) (β i) \ Ioc 0 η, v s ≤ 1 / η := by
      intro s hs
      by_cases hs0 : s ≤ 0
      · rw [logarithmicCausalKernel_of_nonpos hs0]
        positivity
      · have hsη : η < s := by
          by_contra hle
          exact hs.2 ⟨not_le.mp hs0, not_lt.mp hle⟩
        exact (antitoneOn_logarithmicCausalKernel hη (not_le.mp hs0) hsη.le).trans
          (logarithmicCausalKernel_le_inv hη)
    have hm : MeasurableSet (Ioc (α i) (β i) \ Ioc 0 η) := measurableSet_Ioc.diff measurableSet_Ioc
    have hfin : volume (Ioc (α i) (β i) \ Ioc 0 η) < ⊤ :=
      (measure_mono diff_subset).trans_lt (by simp)
    calc
      _ ≤ ∫ _ in Ioc (α i) (β i) \ Ioc 0 η, 1 / η :=
        setIntegral_mono_on hint.integrableOn (integrableOn_const hfin.ne) hm hb
      _ = (volume (Ioc (α i) (β i) \ Ioc 0 η)).toReal * (1 / η) := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
      _ ≤ (volume (Ioc (α i) (β i))).toReal * (1 / η) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact ENNReal.toReal_mono (by simp) (measure_mono diff_subset)
      _ = _ := by
        rw [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (hαβ i hi))]
        ring
  have hunion : ∑ i ∈ S, ∫ s in Ioc (α i) (β i) ∩ Ioc 0 η, v s ≤ V η := by
    have hdis' : Set.PairwiseDisjoint (↑S : Set ℕ) fun i => Ioc (α i) (β i) ∩ Ioc 0 η :=
      fun i hi j hj hij => (hdis hi hj hij).mono inter_subset_left inter_subset_left
    rw [← integral_biUnion_finset S (fun i _ => measurableSet_Ioc.inter measurableSet_Ioc) hdis'
      (fun i _ => hint.integrableOn)]
    unfold logarithmicRenewalMass
    exact setIntegral_mono_set hint.integrableOn
      (Eventually.of_forall logarithmicCausalKernel_nonneg)
      (HasSubset.Subset.eventuallyLE (iUnion₂_subset fun i _ => inter_subset_right))
  calc
    _ ≤ ∑ i ∈ S, ((∫ s in Ioc (α i) (β i) ∩ Ioc 0 η, v s) + (β i - α i) / η) :=
      Finset.sum_le_sum hpt
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
      linarith only [hunion]

namespace WeilHilbertBeforeContact

/-! ### One increment in the two charts -/

/-- The forcing difference in a chart fixed at the left edge. -/
theorem forcing_diff_left {a b c : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1)
    (Z : ChartCutoff) (hZa : ∀ x, 2 * a.1.1 ≤ x → Z.toFun x = 0)
    (hZc : ∀ x, 2 * c.1.1 ≤ x → Z.toFun x = 0) (z : ℂ) :
    ∀ᵐ w ∂volume, 0 ≤ w →
      ‖((chartForcing Z b z : LogarithmicHalfLineL2) : RealLineL2) (w + 0) -
        chartPhase z (b.1.1 - a.1.1) * ((chartForcing Z a z : LogarithmicHalfLineL2) : RealLineL2) w‖ ≤
      chartMajorant (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) (chartIncrement a b z) w +
        (chartBoundedConstant (2 * c.1.1) (2 * c.1.1) + Z.lip / 2) * ∫ r, ‖chartIncrement a b z r‖ := by
  have hi := (continuous_chartIncrement a b z).integrable_of_hasCompactSupport
    (hasCompactSupport_chartIncrement hab z)
  have hIn : 0 ≤ ∫ r, ‖chartIncrement a b z r‖ := integral_nonneg fun _ => norm_nonneg _
  have hB := chartBoundedConstant_nonneg (2 * c.1.1) (2 * c.1.1)
  filter_upwards [chartForcing_sub_ae Z hab hbc hZa z] with w hw hw0
  rw [add_zero, hw hw0, zero_add]
  have hbd := norm_chart_combination_le Z (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) hi
    (Bd := chartBoundedConstant (2 * c.1.1) (2 * c.1.1) * ∫ r, ‖chartIncrement a b z r‖)
    (mul_nonneg hB hIn) w (fun hne => by
      have hw2 : w ≤ 2 * c.1.1 := by
        by_contra hlt
        exact hne (hZc w (not_le.mp hlt).le)
      exact norm_chartBounded_le (continuous_chartIncrement a b z)
        (hasCompactSupport_chartIncrement hab z) hw0 hw2
        (fun t ht => chartIncrement_eq_zero hab z (Or.inl ht))
        (fun t ht => chartIncrement_eq_zero hab z (Or.inr (by linarith only [ht, hbc]))))
  refine hbd.trans (le_of_eq ?_)
  ring

/-- The forcing difference read from the moving right edge. -/
theorem forcing_diff_right {a b c : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1)
    (Ca Cb : ChartCutoff) (hCa : ∀ x, 2 * a.1.1 ≤ x → Ca.toFun x = 0)
    (hCb : ∀ x, 2 * b.1.1 ≤ x → Cb.toFun x = 0)
    (hshift : ∀ r, Cb.toFun r = Ca.toFun (r - 2 * (b.1.1 - a.1.1))) (z : ℂ) :
    ∀ᵐ w ∂volume, 0 ≤ w →
      ‖((chartForcing Cb b (-z) : LogarithmicHalfLineL2) : RealLineL2) (w + 2 * (b.1.1 - a.1.1)) -
        chartPhase z (b.1.1 - a.1.1) *
          ((chartForcing Ca a (-z) : LogarithmicHalfLineL2) : RealLineL2) w‖ ≤
      chartMajorant (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) (chartIncrement a b z) (2 * a.1.1 - w) +
        (chartBoundedConstant (2 * c.1.1) (2 * c.1.1) + Ca.lip / 2) * ∫ r, ‖chartIncrement a b z r‖ := by
  obtain ⟨N, hNd⟩ : ∃ N, N = Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊ := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = b.1.1 - a.1.1 := ⟨_, rfl⟩
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = 2 * h := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := by
    rw [hh]
    linarith only [hab]
  have hτ0 : 0 ≤ τ := by
    rw [hτd]
    linarith only [hh0]
  rw [← hh, ← hτd] at hshift ⊢
  rw [← hNd]
  have ht := (measurePreserving_add_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae
    (chartForcing_ae Cb b hCb (-z) (N := N) (by rw [hNd]; exact chartPrimeWindow_subset hbc)
      (fun n hn hn' => chartPrimeWindow_beyond (by rw [← hNd]; exact hn) hn'))
  have ha := chartForcing_ae Ca a hCa (-z) (N := N)
    (by rw [hNd]; exact chartPrimeWindow_subset (hab.trans hbc))
    (fun n hn hn' => chartPrimeWindow_beyond (by rw [← hNd]; exact hn) hn')
  obtain ⟨Sb, hSb⟩ : ∃ Sb : ℝ → ℂ, Sb = fun t => chartSource b (-z) (t + τ) := ⟨_, rfl⟩
  have hSbc : Continuous Sb := by
    rw [hSb]
    exact (continuous_chartSource b (-z)).comp (by fun_prop)
  have hSbs : HasCompactSupport Sb := by
    rw [hSb]
    exact (hasCompactSupport_chartSource b (-z)).comp_homeomorph (Homeomorph.addRight τ)
  have hSac := continuous_chartSource a (-z)
  have hSas := hasCompactSupport_chartSource a (-z)
  have hY : (fun t => Sb t - chartPhase z h * chartSource a (-z) t) =
      fun t => chartIncrement a b z (2 * a.1.1 - t) := by
    funext t
    rw [hSb, chartIncrement, chartSource_reflect b (-z), chartSource_reflect a (-z), neg_neg, ← hh]
    congr 2
    rw [hτd, hh]
    ring
  have hΔi := (continuous_chartIncrement a b z).integrable_of_hasCompactSupport
    (hasCompactSupport_chartIncrement hab z)
  obtain ⟨Y, hYd⟩ : ∃ Y : ℝ → ℂ, Y = fun t => chartIncrement a b z (2 * a.1.1 - t) := ⟨_, rfl⟩
  have hYi : Integrable Y := by
    rw [hYd]
    exact hΔi.comp_sub_left _
  have hYL : ∫ t, ‖Y t‖ = ∫ r, ‖chartIncrement a b z r‖ := by
    rw [hYd]
    exact integral_sub_left_eq_self (fun r => ‖chartIncrement a b z r‖) volume _
  have hIn : 0 ≤ ∫ r, ‖chartIncrement a b z r‖ := integral_nonneg fun _ => norm_nonneg _
  have hB := chartBoundedConstant_nonneg (2 * c.1.1) (2 * c.1.1)
  filter_upwards [ht, ha] with w hw₁ hw₂ hw0
  rw [hw₁ (by linarith only [hw0, hτ0]), hw₂ hw0]
  have hexp : Complex.exp (-I * star (-z) * ((w + τ - b.1.1 : ℝ) : ℂ)) =
      chartPhase z h * Complex.exp (-I * star (-z) * ((w - a.1.1 : ℝ) : ℂ)) := by
    rw [chartPhase, ← Complex.exp_add]
    congr 1
    simp only [RCLike.star_def, map_neg]
    rw [hτd, hh]
    push_cast
    ring
  have hCaw : Cb.toFun (w + τ) = Ca.toFun w := by
    rw [hshift (w + τ), add_sub_cancel_right]
  have hcomb : (Cb.toFun (w + τ) : ℂ) * (Complex.exp (-I * star (-z) * ((w + τ - b.1.1 : ℝ) : ℂ)) +
        chartMass * chartSource b (-z) (w + τ) + chartBounded (chartSource b (-z)) (w + τ) +
        chartPrime N (chartSource b (-z)) (w + τ)) +
        Cb.commutatorIntegral (chartSource b (-z)) (w + τ) -
      chartPhase z h * ((Ca.toFun w : ℂ) * (Complex.exp (-I * star (-z) * ((w - a.1.1 : ℝ) : ℂ)) +
        chartMass * chartSource a (-z) w + chartBounded (chartSource a (-z)) w +
        chartPrime N (chartSource a (-z)) w) + Ca.commutatorIntegral (chartSource a (-z)) w) =
      (Ca.toFun w : ℂ) * (chartMass * Y w + chartBounded Y w + chartPrime N Y w) +
        Ca.commutatorIntegral Y w := by
    rw [hCaw, chartBounded_translate, chartPrime_translate, commutatorIntegral_translate Ca Cb hshift,
      hexp]
    rw [← hSb, hYd, ← hY, chartBounded_sub_mul hSbc hSbs hSac hSas, chartPrime_sub_mul,
      commutatorIntegral_sub_mul Ca (hSbc.integrable_of_hasCompactSupport hSbs)
        (hSac.integrable_of_hasCompactSupport hSas)]
    have hSbw : chartSource b (-z) (w + τ) = Sb w := by rw [hSb]
    rw [hSbw]
    ring
  rw [hcomb]
  have hbd := norm_chart_combination_le Ca N hYi
    (Bd := chartBoundedConstant (2 * c.1.1) (2 * c.1.1) * ∫ r, ‖chartIncrement a b z r‖)
    (mul_nonneg hB hIn) w (fun hne => by
      have hw2 : w < 2 * a.1.1 := by
        by_contra hlt
        exact hne (hCa w (not_lt.mp hlt))
      obtain ⟨Y', hY'⟩ : ∃ Y' : ℝ → ℂ, Y' = fun t => chartIncrement a b z (2 * b.1.1 - t) := ⟨_, rfl⟩
      have hY'c : Continuous Y' := by
        rw [hY']
        exact (continuous_chartIncrement a b z).comp (by fun_prop)
      have hY's : HasCompactSupport Y' := by
        rw [hY']
        apply HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * b.1.1))
        intro t ht
        refine chartIncrement_eq_zero hab z ?_
        have hs : ¬(0 ≤ t ∧ t ≤ 2 * b.1.1) := ht
        rcases not_and_or.mp hs with h' | h'
        · exact Or.inr (by linarith only [not_le.mp h'])
        · exact Or.inl (by linarith only [not_le.mp h'])
      have hYY' : Y = fun t => Y' (t + τ) := by
        funext t
        rw [hYd, hY']
        simp only
        congr 1
        rw [hτd, hh]
        ring
      have hL' : ∫ t, ‖Y' t‖ = ∫ r, ‖chartIncrement a b z r‖ := by
        rw [hY']
        exact integral_sub_left_eq_self (fun r => ‖chartIncrement a b z r‖) volume _
      rw [hYY', ← chartBounded_translate, ← hL']
      exact norm_chartBounded_le hY'c hY's (by linarith only [hw0, hτ0])
        (by rw [hτd, hh]; linarith only [hw2, hbc])
        (fun t ht => by
          rw [hY']
          exact chartIncrement_eq_zero hab z (Or.inr (by linarith only [ht])))
        (fun t ht => by
          rw [hY']
          exact chartIncrement_eq_zero hab z (Or.inl (by linarith only [ht, hbc]))))
  have hm : chartMajorant N Y w = chartMajorant N (chartIncrement a b z) (2 * a.1.1 - w) := by
    rw [hYd]
    exact chartMajorant_reflect N _ _ _
  rw [hm, hYL] at hbd
  refine hbd.trans (le_of_eq ?_)
  ring

theorem levelMass_reflect (m : ℝ → ℝ) (C p : ℝ) :
    levelMass (fun w => m (C - w)) p = levelMass (fun w => m (-w)) (p - C) := by
  unfold levelMass
  rw [← integral_add_right_eq_self (fun w : ℝ => v (w - p) * m (C - w)) C]
  apply integral_congr_ae
  filter_upwards with w
  rw [show w + C - p = w - (p - C) by ring, show C - (w + C) = -w by ring]

private theorem chartMajorant_bound (N : Finset ℕ) {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1)
    (z : ℂ) : ∃ G, ∀ y, |chartMajorant N (chartIncrement a b z) y| ≤ G := by
  obtain ⟨M, hM⟩ := (hasCompactSupport_chartIncrement hab z).exists_bound_of_continuous
    (continuous_chartIncrement a b z)
  refine ⟨chartSupConstant N * M, fun y => ?_⟩
  rw [abs_of_nonneg (chartMajorant_nonneg N _ y)]
  exact chartMajorant_le N hM y

/-- **The left chart of one increment.** -/
theorem increment_left_le {a b c : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1)
    (Z : ChartCutoff) (hZa : ∀ x, 2 * a.1.1 ≤ x → Z.toFun x = 0)
    (hZc : ∀ x, 2 * c.1.1 ≤ x → Z.toFun x = 0) (z : ℂ) {A₁ A₂ : ℝ}
    (h₁ : ∀ᵐ y ∂volume, ‖((chartForcing Z a z : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₁)
    (h₂ : ∀ᵐ y ∂volume, ‖((chartForcing Z b z : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₂)
    {t : ℝ} (hone : Z.toFun t = 1) :
    ‖chartIncrement a b z t‖ ≤ ∫ s in Ioc 0 t, v s *
      (levelMass (chartMajorant (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) (chartIncrement a b z)) (t - s) +
        (chartBoundedConstant (2 * c.1.1) (2 * c.1.1) + Z.lip / 2) * ∫ r, ‖chartIncrement a b z r‖) := by
  by_cases ht : t ≤ 0
  · rw [chartIncrement_eq_zero hab z (Or.inl ht), norm_zero, Ioc_eq_empty (not_lt.mpr ht)]
    simp
  have hZb : ∀ x, 2 * b.1.1 ≤ x → Z.toFun x = 0 := fun x hx => hZa x (by linarith only [hx, hab])
  obtain ⟨N, hNd⟩ : ∃ N, N = Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊ := ⟨_, rfl⟩
  rw [← hNd]
  have hdom := forcing_diff_left hab hbc Z hZa hZc z
  rw [← hNd] at hdom
  obtain ⟨G, hG⟩ := chartMajorant_bound N hab z
  have hS := continuous_chartIncrement a b z
  have hIn : 0 ≤ ∫ r, ‖chartIncrement a b z r‖ := integral_nonneg fun _ => norm_nonneg _
  have hc := chartBoundedConstant_nonneg (2 * c.1.1) (2 * c.1.1)
  have hlip : 0 ≤ Z.lip / 2 := div_nonneg Z.lip_nonneg (by norm_num)
  have hmain := norm_green_shift_le_level (chartForcing Z a z) (chartForcing Z b z)
    (chartPhase z (b.1.1 - a.1.1)) (τ := 0) (y := t) le_rfl (not_le.mp ht).le h₁ h₂
    (continuous_chartMajorant N hS).measurable hG hdom (chartMajorant_nonneg N _)
    (mul_nonneg (add_nonneg hc hlip) hIn)
  rw [add_zero, sub_self, mul_zero, zero_add, logarithmicGreenRepresentative_chartForcing Z b hZb z t,
    logarithmicGreenRepresentative_chartForcing Z a hZa z t, hone, Complex.ofReal_one, one_mul,
    one_mul] at hmain
  exact hmain

/-- **The right chart of one increment.** -/
theorem increment_right_le {a b c : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1)
    (Ca Cb : ChartCutoff) (hCa : ∀ x, 2 * a.1.1 ≤ x → Ca.toFun x = 0)
    (hCb : ∀ x, 2 * b.1.1 ≤ x → Cb.toFun x = 0)
    (hshift : ∀ r, Cb.toFun r = Ca.toFun (r - 2 * (b.1.1 - a.1.1))) (z : ℂ) {A₁ A₂ : ℝ}
    (hA₂ : 0 ≤ A₂)
    (h₁ : ∀ᵐ y ∂volume, ‖((chartForcing Ca a (-z) : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₁)
    (h₂ : ∀ᵐ y ∂volume, ‖((chartForcing Cb b (-z) : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₂)
    {t : ℝ} (hone : Ca.toFun (2 * a.1.1 - t) = 1)
    (hone' : ∀ r, r ≤ 2 * (b.1.1 - a.1.1) → Cb.toFun r = 1) :
    ‖chartIncrement a b z t‖ ≤
      A₂ * (∫ s in Ioc (2 * a.1.1 - t) (2 * b.1.1 - t), v s) +
      ∫ s in Ioc 0 (2 * a.1.1 - t), v s *
        (levelMass (fun w => chartMajorant (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊)
          (chartIncrement a b z) (-w)) (-t - s) +
          (chartBoundedConstant (2 * c.1.1) (2 * c.1.1) + Ca.lip / 2) *
            ∫ r, ‖chartIncrement a b z r‖) := by
  obtain ⟨N, hNd⟩ : ∃ N, N = Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊ := ⟨_, rfl⟩
  rw [← hNd]
  have hdom := forcing_diff_right hab hbc Ca Cb hCa hCb hshift z
  rw [← hNd] at hdom
  obtain ⟨h, hh⟩ : ∃ h, h = b.1.1 - a.1.1 := ⟨_, rfl⟩
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = 2 * h := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by
    rw [hτd, hh]
    linarith only [hab]
  rw [← hh, ← hτd] at hdom hshift hone'
  obtain ⟨y, hy⟩ : ∃ y, y = 2 * a.1.1 - t := ⟨_, rfl⟩
  rw [← hy] at hone ⊢
  have hyt : 2 * b.1.1 - t = y + τ := by
    rw [hy, hτd, hh]
    ring
  rw [hyt]
  have hS := continuous_chartIncrement a b z
  have hIn : 0 ≤ ∫ r, ‖chartIncrement a b z r‖ := integral_nonneg fun _ => norm_nonneg _
  have hc := chartBoundedConstant_nonneg (2 * c.1.1) (2 * c.1.1)
  have hlip : 0 ≤ Ca.lip / 2 := div_nonneg Ca.lip_nonneg (by norm_num)
  have hnn : 0 ≤ ∫ s in Ioc y (y + τ), v s :=
    integral_nonneg fun s => logarithmicCausalKernel_nonneg s
  by_cases hy0 : 0 ≤ y
  · obtain ⟨G, hG⟩ := chartMajorant_bound N hab z
    have hgm : Measurable fun w => chartMajorant N (chartIncrement a b z) (2 * a.1.1 - w) :=
      (continuous_chartMajorant N hS).measurable.comp (measurable_const.sub measurable_id)
    have hmain := norm_green_shift_le_level (chartForcing Ca a (-z)) (chartForcing Cb b (-z))
      (chartPhase z h) hτ0 hy0 h₁ h₂ (g := fun w => chartMajorant N (chartIncrement a b z) (2 * a.1.1 - w))
      hgm (fun w => hG _) hdom (fun w => chartMajorant_nonneg N _ _)
      (mul_nonneg (add_nonneg hc hlip) hIn)
    rw [logarithmicGreenRepresentative_chartForcing Cb b hCb (-z) (y + τ),
      logarithmicGreenRepresentative_chartForcing Ca a hCa (-z) y, hshift (y + τ),
      add_sub_cancel_right, hone, Complex.ofReal_one, one_mul, one_mul] at hmain
    have hval : chartSource b (-z) (y + τ) - chartPhase z h * chartSource a (-z) y =
        chartIncrement a b z t := by
      rw [chartIncrement, chartSource_reflect b (-z), chartSource_reflect a (-z), neg_neg, ← hh, ← hyt,
        hy]
      congr 2 <;> ring
    rw [hval, logarithmicRenewalMass_add hy0 hτ0] at hmain
    have hsimp : V y + (∫ s in Ioc y (y + τ), v s) - V y = ∫ s in Ioc y (y + τ), v s := by ring
    rw [hsimp] at hmain
    refine hmain.trans (add_le_add le_rfl (le_of_eq ?_))
    apply integral_congr_ae
    filter_upwards with s
    rw [levelMass_reflect (chartMajorant N (chartIncrement a b z)) (2 * a.1.1) (y - s)]
    congr 3
    rw [hy]
    ring
  · push Not at hy0
    rw [Ioc_eq_empty (not_lt.mpr hy0.le)]
    simp only [Measure.restrict_empty, integral_zero_measure, add_zero]
    have htz : chartIncrement a b z t = chartSource b (-z) (y + τ) := by
      rw [chartIncrement, chartSource_eq_zero a z (Or.inr (by linarith only [hy, hy0])), mul_zero,
        sub_zero, chartSource_reflect, hyt]
    rw [htz]
    by_cases hr : y + τ ≤ 0
    · rw [chartSource_eq_zero b (-z) (Or.inl hr), norm_zero]
      exact mul_nonneg hA₂ hnn
    · have hG := logarithmicGreenRepresentative_chartForcing Cb b hCb (-z) (y + τ)
      rw [hone' _ (by linarith only [hy0]), Complex.ofReal_one, one_mul] at hG
      rw [← hG]
      have hle := norm_logarithmicGreenRepresentative_le (chartForcing Cb b (-z))
        (fun r _ => norm_logarithmicBackwardConvolution_le h₂ r) (x := y + τ)
      refine hle.trans (mul_le_mul_of_nonneg_left ?_ hA₂)
      unfold logarithmicRenewalMass
      exact setIntegral_mono_set logarithmicCausalKernel_mass_one.1.integrableOn
        (Eventually.of_forall logarithmicCausalKernel_nonneg)
        (HasSubset.Subset.eventuallyLE (Ioc_subset_Ioc_left hy0.le))

/-- The readout of the trace increment in the left chart. -/
theorem trace_increment_le {a b c : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1)
    (Z : ChartCutoff) (hZa : ∀ x, 2 * a.1.1 ≤ x → Z.toFun x = 0)
    (hZc : ∀ x, 2 * c.1.1 ≤ x → Z.toFun x = 0) (z : ℂ) {κ : ℝ} (hκ : 0 < κ)
    (hone : ∀ x, x ≤ κ → Z.toFun x = 1) {A₁ A₂ : ℝ}
    (h₁ : ∀ᵐ y ∂volume, ‖((chartForcing Z a z : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₁)
    (h₂ : ∀ᵐ y ∂volume, ‖((chartForcing Z b z : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A₂) :
    ‖evalVectorLeftTrace b z - chartPhase z (b.1.1 - a.1.1) * evalVectorLeftTrace a z‖ ≤
      levelMass (chartMajorant (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) (chartIncrement a b z)) 0 +
        (chartBoundedConstant (2 * c.1.1) (2 * c.1.1) + Z.lip / 2) * ∫ r, ‖chartIncrement a b z r‖ := by
  have hZb : ∀ x, 2 * b.1.1 ≤ x → Z.toFun x = 0 := fun x hx => hZa x (by linarith only [hx, hab])
  obtain ⟨G, hG⟩ := chartMajorant_bound (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) hab z
  have hS := continuous_chartIncrement a b z
  have hIn : 0 ≤ ∫ r, ‖chartIncrement a b z r‖ := integral_nonneg fun _ => norm_nonneg _
  have hc := chartBoundedConstant_nonneg (2 * c.1.1) (2 * c.1.1)
  have hlip : 0 ≤ Z.lip / 2 := div_nonneg Z.lip_nonneg (by norm_num)
  have hmain := norm_readout_shift_sub_le (chartForcing Z a z) (chartForcing Z b z)
    (chartPhase z (b.1.1 - a.1.1)) (τ := 0) (p := 0) le_rfl h₁ h₂
    (continuous_chartMajorant _ hS).measurable hG (forcing_diff_left hab hbc Z hZa hZc z)
    (chartMajorant_nonneg _ _) (mul_nonneg (add_nonneg hc hlip) hIn)
  rw [add_zero, logarithmicBackwardConvolution_chartForcing_zero Z b hZb hκ hone z,
    logarithmicBackwardConvolution_chartForcing_zero Z a hZa hκ hone z] at hmain
  exact hmain

/-! ### The absorption -/

/-- The chart forcings of a compact precontact interval have one bound. -/
theorem exists_uniform_chartForcing_bound (a₁ a₂ : PrecontactAperture) (z : ℂ) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a : PrecontactAperture, a₁.1.1 ≤ a.1.1 → a.1.1 ≤ a₂.1.1 →
      ∀ C : ChartCutoff, C.lip ≤ Λ → (∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0) →
        ∀ᵐ y ∂volume, ‖((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤ A := by
  obtain ⟨Az, hAz0, hAz⟩ := exists_uniform_endpoint_data a₁ a₂ z
  obtain ⟨A, hAd⟩ : ∃ A, A = Real.exp (2 * a₂.1.1 * |z.im|) +
      chartSupConstant (Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊) * Az +
      chartBoundedConstant (2 * a₂.1.1) (2 * a₂.1.1) * Az + Λ / 2 * Az := ⟨_, rfl⟩
  have hK := chartSupConstant_nonneg (Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊)
  have hB := chartBoundedConstant_nonneg (2 * a₂.1.1) (2 * a₂.1.1)
  refine ⟨A, by rw [hAd]; positivity, fun a h1 h2 C hlip hC => ?_⟩
  filter_upwards [chartForcing_sup_le C h2 hC z (M := Az) (L := Az) (hAz a h1 h2).2.2.1
    (hAz a h1 h2).2.1] with y hy
  refine hy.trans ?_
  rw [hAd]
  have h5 : C.lip / 2 * Az ≤ Λ / 2 * Az :=
    mul_le_mul_of_nonneg_right (by linarith only [hlip]) hAz0
  linarith only [h5]

/-- The right cutoff, fixed in physical coordinates: one up to `A − c`, zero from `A − c/2`. -/
def rightCutoff (A c : ℝ) (hc : 0 < c) : ChartCutoff :=
  ChartCutoff.linear (A - c) (A - c / 2) (by linarith only [hc])

theorem rightCutoff_lip (A c : ℝ) (hc : 0 < c) : (rightCutoff A c hc).lip = 2 / c := by
  change 1 / (A - c / 2 - (A - c)) = 2 / c
  rw [show A - c / 2 - (A - c) = c / 2 by ring]
  field_simp

theorem rightCutoff_one (A c : ℝ) (hc : 0 < c) {x : ℝ} (hx : x ≤ A - c) :
    (rightCutoff A c hc).toFun x = 1 :=
  ChartCutoff.linear_eq_one _ hx

theorem rightCutoff_zero (A c : ℝ) (hc : 0 < c) {x : ℝ} (hx : A ≤ x) :
    (rightCutoff A c hc).toFun x = 0 :=
  ChartCutoff.linear_eq_zero _ (by linarith only [hx, hc])

theorem rightCutoff_shift (A τ c : ℝ) (hc : 0 < c) (r : ℝ) :
    (rightCutoff (A + τ) c hc).toFun r = (rightCutoff A c hc).toFun (r - τ) := by
  change min (max ((A + τ - c / 2 - r) / (A + τ - c / 2 - (A + τ - c))) 0) 1 =
    min (max ((A - c / 2 - (r - τ)) / (A - c / 2 - (A - c))) 0) 1
  congr 3
  · ring
  · ring

/-- The sum of chart majorants is controlled by the sup of the sum of the sources. -/
theorem sum_chartMajorant_le (S N : Finset ℕ) (Δ : ℕ → ℝ → ℂ) {M : ℝ}
    (hM : ∀ t, ∑ i ∈ S, ‖Δ i t‖ ≤ M) (y : ℝ) :
    ∑ i ∈ S, chartMajorant N (Δ i) y ≤ chartSupConstant N * M := by
  have he : ∑ i ∈ S, chartMajorant N (Δ i) y = ‖chartMass‖ * ∑ i ∈ S, ‖Δ i y‖ +
      ∑ n ∈ N, criticalMellinAtomWeight n *
        (∑ i ∈ S, ‖Δ i (y + Real.log n)‖ + ∑ i ∈ S, ‖Δ i (y - Real.log n)‖) := by
    unfold chartMajorant
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [he]
  have hM1 : ‖chartMass‖ * ∑ i ∈ S, ‖Δ i y‖ ≤ ‖chartMass‖ * M :=
    mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)
  have hM2 : ∑ n ∈ N, criticalMellinAtomWeight n *
      (∑ i ∈ S, ‖Δ i (y + Real.log n)‖ + ∑ i ∈ S, ‖Δ i (y - Real.log n)‖) ≤
      ∑ n ∈ N, criticalMellinAtomWeight n * (2 * M) :=
    Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
      (by linarith only [hM (y + Real.log n), hM (y - Real.log n)])
      (criticalMellinAtomWeight_nonneg_chart n)
  rw [← Finset.sum_mul] at hM2
  unfold chartSupConstant chartPrimeMass
  nlinarith only [hM1, hM2]

/-- The sum of level masses of a family of densities. -/
theorem sum_levelMass_le (S : Finset ℕ) (m : ℕ → ℝ → ℝ) (hm : ∀ i ∈ S, Measurable (m i))
    (hm0 : ∀ i ∈ S, ∀ y, 0 ≤ m i y) (hmi : ∀ i ∈ S, Integrable (m i))
    (hmG : ∀ i ∈ S, ∃ G, ∀ y, |m i y| ≤ G) {T J ε : ℝ} (hT : 0 ≤ T)
    (hsum : ∀ y, ∑ i ∈ S, m i y ≤ T) (hJ : ∑ i ∈ S, ∫ y, m i y ≤ J) (hε : 0 < ε) (q : ℝ) :
    ∑ i ∈ S, levelMass (m i) q ≤ T * V ε + J / ε := by
  have hgm : Measurable fun y => ∑ i ∈ S, m i y := Finset.measurable_fun_sum _ hm
  have hgi : Integrable fun y => ∑ i ∈ S, m i y := integrable_finsetSum _ hmi
  have hg0 (y : ℝ) : 0 ≤ ∑ i ∈ S, m i y := Finset.sum_nonneg fun i hi => hm0 i hi y
  have hsplit := levelMass_le_split hgm hgi hg0 hT hsum hε q
  have he : levelMass (fun y => ∑ i ∈ S, m i y) q = ∑ i ∈ S, levelMass (m i) q := by
    unfold levelMass
    rw [← integral_finsetSum _ fun i hi => by
      obtain ⟨G, hG⟩ := hmG i hi
      exact integrable_kernel_mul (hm i hi) hG q]
    apply integral_congr_ae
    filter_upwards with w
    rw [Finset.mul_sum]
  rw [he, integral_finsetSum _ hmi] at hsplit
  exact hsplit.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hJ hε.le))

/-- **The partial variation of the Riesz sources and of the traces is uniformly small.** -/
theorem exists_partial_variation_bound {a₁ a₂ : PrecontactAperture} (ha₁₂ : a₁.1.1 ≤ a₂.1.1) (z : ℂ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (S : Finset ℕ) (Aa Bb : ℕ → PrecontactAperture),
      (∀ i ∈ S, a₁.1.1 ≤ (Aa i).1.1 ∧ (Aa i).1.1 ≤ (Bb i).1.1 ∧ (Bb i).1.1 ≤ a₂.1.1) →
      Set.PairwiseDisjoint (↑S : Set ℕ) (fun i => Ioc (Aa i).1.1 (Bb i).1.1) →
      ∀ η : ℝ, 0 < η →
        (∀ t, ∑ i ∈ S, ‖chartIncrement (Aa i) (Bb i) z t‖ ≤
          C₁ * (V η + (∑ i ∈ S, (2 * (Bb i).1.1 - 2 * (Aa i).1.1)) / η) +
            C₂ * ∑ i ∈ S, ((Bb i).1.1 - (Aa i).1.1)) ∧
        ∑ i ∈ S, ‖evalVectorLeftTrace (Bb i) z -
            chartPhase z ((Bb i).1.1 - (Aa i).1.1) * evalVectorLeftTrace (Aa i) z‖ ≤
          C₁ * (V η + (∑ i ∈ S, (2 * (Bb i).1.1 - 2 * (Aa i).1.1)) / η) +
            C₂ * ∑ i ∈ S, ((Bb i).1.1 - (Aa i).1.1) := by
  obtain ⟨c, hcd⟩ : ∃ c, c = a₁.1.1 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcd]
    exact a₁.1.2
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℝ, Λ = 2 / c := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by
    rw [hΛd]
    positivity
  obtain ⟨Az, hAz0, hAz⟩ := exists_uniform_chartForcing_bound a₁ a₂ z hΛ
  obtain ⟨An, hAn0, hAn⟩ := exists_uniform_chartForcing_bound a₁ a₂ (-z) hΛ
  obtain ⟨CL, hCL0, hCL⟩ := exists_chartIncrement_lipschitz a₁ a₂ z
  obtain ⟨Mz, hMz0, hMz⟩ := exists_uniform_chartSource_bound a₁ a₂ z
  obtain ⟨N, hNd⟩ : ∃ N, N = Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊ := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K, K = chartSupConstant N := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKd]
    exact chartSupConstant_nonneg N
  obtain ⟨c₁, hc₁d⟩ : ∃ c₁, c₁ = chartBoundedConstant (2 * a₂.1.1) (2 * a₂.1.1) + Λ / 2 := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by
    rw [hc₁d]
    exact add_nonneg (chartBoundedConstant_nonneg _ _) (by positivity)
  obtain ⟨ε, hε, hsmall⟩ : ∃ ε : ℝ, 0 < ε ∧ K * V ε ≤ 1 / 2 := by
    have ht := tendsto_logarithmicRenewalMass_zero.const_mul K
    rw [mul_zero] at ht
    have hev := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨ρ, hb, hp⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨ρ, hp, (show K * V ρ < 1 / 2 from hb).le⟩
  refine ⟨2 * An, 2 * ((K / ε + c₁) * CL), by positivity, by positivity,
    fun S Aa Bb hS hdis η hη => ?_⟩
  -- The left cutoff.
  have hcd2 : c < 3 * c / 2 := by linarith only [hc]
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = ChartCutoff.linear c (3 * c / 2) hcd2 := ⟨_, rfl⟩
  have hZone : ∀ x, x ≤ c → Z.toFun x = 1 := fun x hx => by
    rw [hZd]
    exact ChartCutoff.linear_eq_one hcd2 hx
  have hZzero : ∀ x, 3 * c / 2 ≤ x → Z.toFun x = 0 := fun x hx => by
    rw [hZd]
    exact ChartCutoff.linear_eq_zero hcd2 hx
  have hZlip : Z.lip = Λ := by
    rw [hZd, hΛd]
    change 1 / (3 * c / 2 - c) = 2 / c
    rw [show 3 * c / 2 - c = c / 2 by ring]
    field_simp
  have hZlip' : Z.lip ≤ Λ := hZlip.le
  have hca (i : ℕ) (hi : i ∈ S) : c ≤ (Aa i).1.1 := by
    rw [hcd]
    exact (hS i hi).1
  have hab (i : ℕ) (hi : i ∈ S) : (Aa i).1.1 ≤ (Bb i).1.1 := (hS i hi).2.1
  have hb₂ (i : ℕ) (hi : i ∈ S) : (Bb i).1.1 ≤ a₂.1.1 := (hS i hi).2.2
  have ha₂ (i : ℕ) (hi : i ∈ S) : (Aa i).1.1 ≤ a₂.1.1 := (hab i hi).trans (hb₂ i hi)
  have hb₁ (i : ℕ) (hi : i ∈ S) : a₁.1.1 ≤ (Bb i).1.1 := (hS i hi).1.trans (hab i hi)
  have hZa (i : ℕ) (hi : i ∈ S) : ∀ x, 2 * (Aa i).1.1 ≤ x → Z.toFun x = 0 := fun x hx =>
    hZzero x (by linarith only [hx, hca i hi, hc])
  have hZb (i : ℕ) (hi : i ∈ S) : ∀ x, 2 * (Bb i).1.1 ≤ x → Z.toFun x = 0 := fun x hx =>
    hZa i hi x (by linarith only [hx, hab i hi])
  have hca₂ : c ≤ a₂.1.1 := by
    rw [hcd]
    exact ha₁₂
  have hZc : ∀ x, 2 * a₂.1.1 ≤ x → Z.toFun x = 0 := fun x hx =>
    hZzero x (by linarith only [hx, hca₂, hc])
  -- The family.
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → ℝ → ℂ, Δ = fun i => chartIncrement (Aa i) (Bb i) z := ⟨_, rfl⟩
  have hΔc (i : ℕ) : Continuous (Δ i) := by
    rw [hΔ]
    exact continuous_chartIncrement _ _ _
  have hΔi (i : ℕ) (hi : i ∈ S) : Integrable (Δ i) := by
    rw [hΔ]
    exact (continuous_chartIncrement _ _ _).integrable_of_hasCompactSupport
      (hasCompactSupport_chartIncrement (hab i hi) z)
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℝ → ℝ, m = fun i => chartMajorant N (Δ i) := ⟨_, rfl⟩
  obtain ⟨Li, hLi⟩ : ∃ Li : ℕ → ℝ, Li = fun i => ∫ r, ‖Δ i r‖ := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = ∑ i ∈ S, Li i := ⟨_, rfl⟩
  have hLi0 (i : ℕ) : 0 ≤ Li i := by
    rw [hLi]
    exact integral_nonneg fun _ => norm_nonneg _
  have hL0 : 0 ≤ L := by
    rw [hLd]
    exact Finset.sum_nonneg fun i _ => hLi0 i
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ∑ i ∈ S, ((Bb i).1.1 - (Aa i).1.1) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact Finset.sum_nonneg fun i hi => sub_nonneg.mpr (hab i hi)
  have hLδ : L ≤ CL * δ := by
    rw [hLd, hδ, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [hLi]
    simp only
    rw [hΔ]
    exact hCL _ _ (hS i hi).1 (hS i hi).2.1 (hS i hi).2.2
  obtain ⟨D, hDd⟩ : ∃ D, D = ∑ i ∈ S, (2 * (Bb i).1.1 - 2 * (Aa i).1.1) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDd]
    exact Finset.sum_nonneg fun i hi => by linarith only [hab i hi]
  rw [← hδ, ← hDd]
  -- The sup of the sum.
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ, Φ = fun t => ∑ i ∈ S, ‖Δ i t‖ := ⟨_, rfl⟩
  have hΦ0 (t : ℝ) : 0 ≤ Φ t := by
    rw [hΦ]
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  have hbdd : BddAbove (range Φ) := by
    refine ⟨∑ i ∈ S, (Mz + ‖chartPhase z ((Bb i).1.1 - (Aa i).1.1)‖ * Mz), ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [hΦ]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [hΔ]
    refine (norm_sub_le _ _).trans (add_le_add (hMz _ (hb₁ i hi) (hb₂ i hi) t).1 ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMz _ (hS i hi).1 (ha₂ i hi) t).1 (norm_nonneg _)
  obtain ⟨M, hMd⟩ : ∃ M, M = ⨆ t, Φ t := ⟨_, rfl⟩
  have hM (t : ℝ) : Φ t ≤ M := by
    rw [hMd]
    exact le_ciSup hbdd t
  have hM0 : 0 ≤ M := (hΦ0 0).trans (hM 0)
  have hM' (t : ℝ) : ∑ i ∈ S, ‖Δ i t‖ ≤ M := by
    have := hM t
    rw [hΦ] at this
    exact this
  -- The two families of level masses.
  have hmm (i : ℕ) : Measurable (m i) := by
    rw [hm]
    exact (continuous_chartMajorant N (hΔc i)).measurable
  have hm0 (i : ℕ) (y : ℝ) : 0 ≤ m i y := by
    rw [hm]
    exact chartMajorant_nonneg N _ y
  have hmi (i : ℕ) (hi : i ∈ S) : Integrable (m i) := by
    rw [hm]
    exact (integrable_chartMajorant N (hΔi i hi)).1
  have hmG (i : ℕ) (hi : i ∈ S) : ∃ G, ∀ y, |m i y| ≤ G := by
    rw [hm, hΔ]
    exact chartMajorant_bound N (hab i hi) z
  have hmint (i : ℕ) (hi : i ∈ S) : ∫ y, m i y = K * Li i := by
    rw [hm, hKd, hLi]
    exact (integrable_chartMajorant N (hΔi i hi)).2
  have hJ : ∑ i ∈ S, ∫ y, m i y ≤ K * L := by
    rw [hLd, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => (hmint i hi).le
  have hsumM (y : ℝ) : ∑ i ∈ S, m i y ≤ K * M := by
    rw [hm, hKd]
    exact sum_chartMajorant_le S N Δ hM' y
  have hT : 0 ≤ K * M := mul_nonneg hK0 hM0
  have hLevel (q : ℝ) : ∑ i ∈ S, levelMass (m i) q ≤ K * M * V ε + K * L / ε :=
    sum_levelMass_le S m (fun i _ => hmm i) (fun i _ => hm0 i) hmi hmG hT hsumM hJ hε q
  have hLevel' (q : ℝ) : ∑ i ∈ S, levelMass (fun w => m i (-w)) q ≤ K * M * V ε + K * L / ε := by
    refine sum_levelMass_le S (fun i w => m i (-w)) (fun i _ => (hmm i).comp measurable_neg)
      (fun i _ y => hm0 i _) (fun i hi => (hmi i hi).comp_neg) (fun i hi => ?_) hT (fun y => hsumM _)
      ?_ hε q
    · obtain ⟨G, hG⟩ := hmG i hi
      exact ⟨G, fun y => hG _⟩
    · refine le_trans (le_of_eq ?_) hJ
      refine Finset.sum_congr rfl fun i _ => ?_
      exact integral_neg_eq_self (fun y => m i y) volume
  obtain ⟨Θ, hΘd⟩ : ∃ Θ, Θ = K * M * V ε + K * L / ε + c₁ * L := ⟨_, rfl⟩
  have hsumc : ∑ i ∈ S, c₁ * Li i = c₁ * L := by
    rw [hLd, Finset.mul_sum]
  have hΘ (q : ℝ) : ∑ i ∈ S, (levelMass (m i) q + c₁ * Li i) ≤ Θ := by
    rw [Finset.sum_add_distrib, hsumc, hΘd]
    linarith only [hLevel q]
  have hΘ' (q : ℝ) : ∑ i ∈ S, (levelMass (fun w => m i (-w)) q + c₁ * Li i) ≤ Θ := by
    rw [Finset.sum_add_distrib, hsumc, hΘd]
    linarith only [hLevel' q]
  have hEm (i : ℕ) (t : ℝ) : Measurable fun s => levelMass (m i) (t - s) + c₁ * Li i :=
    ((measurable_levelMass (hmm i)).comp (measurable_const.sub measurable_id)).add_const _
  have hEm' (i : ℕ) (t : ℝ) :
      Measurable fun s => levelMass (fun w => m i (-w)) (-t - s) + c₁ * Li i :=
    ((measurable_levelMass ((hmm i).comp measurable_neg)).comp
      (measurable_const.sub measurable_id)).add_const _
  have hE0 (i : ℕ) (q : ℝ) : 0 ≤ levelMass (m i) q + c₁ * Li i :=
    add_nonneg (levelMass_nonneg (hm0 i) q) (mul_nonneg hc₁0 (hLi0 i))
  have hE0' (i : ℕ) (q : ℝ) : 0 ≤ levelMass (fun w => m i (-w)) q + c₁ * Li i :=
    add_nonneg (levelMass_nonneg (fun y => hm0 i _) q) (mul_nonneg hc₁0 (hLi0 i))
  have hEB (i : ℕ) (hi : i ∈ S) : ∃ B, ∀ q, levelMass (m i) q + c₁ * Li i ≤ B := by
    obtain ⟨G, hG⟩ := hmG i hi
    exact ⟨G + c₁ * Li i, fun q => add_le_add
      (levelMass_le (hmm i) (hm0 i) (fun y => (le_abs_self _).trans (hG y)) q) le_rfl⟩
  have hEB' (i : ℕ) (hi : i ∈ S) : ∃ B, ∀ q, levelMass (fun w => m i (-w)) q + c₁ * Li i ≤ B := by
    obtain ⟨G, hG⟩ := hmG i hi
    exact ⟨G + c₁ * Li i, fun q => add_le_add
      (levelMass_le ((hmm i).comp measurable_neg) (fun y => hm0 i _)
        (fun y => (le_abs_self _).trans (hG _)) q) le_rfl⟩
  -- The bound in the two charts.
  have hleft (t : ℝ) (ht : t ≤ c) : Φ t ≤ Θ := by
    have h1 : ∀ i ∈ S, ‖Δ i t‖ ≤ ∫ s in Ioc 0 t, v s * (levelMass (m i) (t - s) + c₁ * Li i) := by
      intro i hi
      have h := increment_left_le (hab i hi) (hb₂ i hi) Z (hZa i hi) hZc z
        (hAz _ (hS i hi).1 (ha₂ i hi) Z hZlip' (hZa i hi))
        (hAz _ (hb₁ i hi) (hb₂ i hi) Z hZlip' (hZb i hi)) (hZone t ht)
      rw [hZlip, ← hc₁d, ← hNd] at h
      rw [hm, hLi, hΔ]
      exact h
    rw [hΦ]
    refine (Finset.sum_le_sum h1).trans ?_
    exact sum_setIntegral_kernel_le S (fun i s => levelMass (m i) (t - s) + c₁ * Li i) (fun _ => t)
      (fun i _ => hEm i t) (fun i _ s => hE0 i _)
      (fun i hi => (hEB i hi).imp fun B hB s => hB _) (fun s => hΘ _)
  have hright (t : ℝ) (ht : c ≤ t) : Φ t ≤ An * (V η + D / η) + Θ := by
    have h1 : ∀ i ∈ S, ‖Δ i t‖ ≤ An * (∫ s in Ioc (2 * (Aa i).1.1 - t) (2 * (Bb i).1.1 - t), v s) +
        ∫ s in Ioc 0 (2 * (Aa i).1.1 - t), v s *
          (levelMass (fun w => m i (-w)) (-t - s) + c₁ * Li i) := by
      intro i hi
      have hA := (Aa i).1.2
      have e2 : 2 * (Bb i).1.1 = 2 * (Aa i).1.1 + 2 * ((Bb i).1.1 - (Aa i).1.1) := by ring
      have hshift : ∀ r, (rightCutoff (2 * (Bb i).1.1) c hc).toFun r =
          (rightCutoff (2 * (Aa i).1.1) c hc).toFun (r - 2 * ((Bb i).1.1 - (Aa i).1.1)) := fun r => by
        rw [← rightCutoff_shift, ← e2]
      have h := increment_right_le (hab i hi) (hb₂ i hi) (rightCutoff (2 * (Aa i).1.1) c hc)
        (rightCutoff (2 * (Bb i).1.1) c hc) (fun x hx => rightCutoff_zero _ _ hc hx)
        (fun x hx => rightCutoff_zero _ _ hc hx) hshift z hAn0
        (hAn _ (hS i hi).1 (ha₂ i hi) _ (by rw [rightCutoff_lip, ← hΛd])
          (fun x hx => rightCutoff_zero _ _ hc hx))
        (hAn _ (hb₁ i hi) (hb₂ i hi) _ (by rw [rightCutoff_lip, ← hΛd])
          (fun x hx => rightCutoff_zero _ _ hc hx))
        (rightCutoff_one _ _ hc (by linarith only [ht]))
        (fun r hr => rightCutoff_one _ _ hc (by linarith only [hr, hca i hi, hA]))
      rw [rightCutoff_lip, ← hΛd, ← hc₁d, ← hNd] at h
      rw [hm, hLi, hΔ]
      exact h
    rw [hΦ]
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ hAn0) ?_
    · have hdis' : Set.PairwiseDisjoint (↑S : Set ℕ)
          (fun i => Ioc (2 * (Aa i).1.1 - t) (2 * (Bb i).1.1 - t)) := by
        intro i hi j hj hij
        refine Set.disjoint_left.mpr fun x hx hy => ?_
        have hd := hdis hi hj hij
        refine Set.disjoint_left.mp hd (a := (x + t) / 2) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · linarith only [hx.1]
        · linarith only [hx.2]
        · linarith only [hy.1]
        · linarith only [hy.2]
      have hsum := sum_setIntegral_kernel_disjoint_le S (fun i => 2 * (Aa i).1.1 - t)
        (fun i => 2 * (Bb i).1.1 - t) (fun i hi => by linarith only [hab i hi]) hdis' hη
      refine hsum.trans (le_of_eq ?_)
      congr 2
      rw [hDd]
      exact Finset.sum_congr rfl fun i _ => by ring
    · exact sum_setIntegral_kernel_le S (fun i s => levelMass (fun w => m i (-w)) (-t - s) + c₁ * Li i)
        (fun i => 2 * (Aa i).1.1 - t) (fun i _ => hEm' i t) (fun i _ s => hE0' i _)
        (fun i hi => (hEB' i hi).imp fun B hB s => hB _) (fun s => hΘ' _)
  have hV0 : 0 ≤ V η := logarithmicRenewalMass_nonneg η
  have hX : 0 ≤ V η + D / η := by positivity
  have hAnX : 0 ≤ An * (V η + D / η) := mul_nonneg hAn0 hX
  have hall (t : ℝ) : Φ t ≤ An * (V η + D / η) + Θ := by
    rcases le_total t c with ht | ht
    · linarith only [hleft t ht, hAnX]
    · exact hright t ht
  have hMle : M ≤ An * (V η + D / η) + Θ := by
    rw [hMd]
    exact ciSup_le hall
  -- Absorption.
  have habs : K * M * V ε ≤ M / 2 := by
    have := mul_le_mul_of_nonneg_right hsmall hM0
    linarith only [this]
  have hΘle : Θ ≤ M / 2 + (K / ε + c₁) * L := by
    rw [hΘd]
    have he : K * L / ε + c₁ * L = (K / ε + c₁) * L := by ring
    linarith only [habs, he]
  have hfac : 0 ≤ K / ε + c₁ := by positivity
  have hLfin : (K / ε + c₁) * L ≤ (K / ε + c₁) * CL * δ := by
    have := mul_le_mul_of_nonneg_left hLδ hfac
    linarith only [this]
  have hMfin : M ≤ 2 * An * (V η + D / η) + 2 * ((K / ε + c₁) * CL) * δ := by
    linarith only [hMle, hΘle, hLfin]
  refine ⟨fun t => ?_, ?_⟩
  · have := hM t
    rw [hΦ] at this
    rw [hΔ] at this
    exact this.trans hMfin
  · have h1 : ∀ i ∈ S, ‖evalVectorLeftTrace (Bb i) z -
        chartPhase z ((Bb i).1.1 - (Aa i).1.1) * evalVectorLeftTrace (Aa i) z‖ ≤
        levelMass (m i) 0 + c₁ * Li i := by
      intro i hi
      have h := trace_increment_le (hab i hi) (hb₂ i hi) Z (hZa i hi) hZc z hc hZone
        (hAz _ (hS i hi).1 (ha₂ i hi) Z hZlip' (hZa i hi))
        (hAz _ (hb₁ i hi) (hb₂ i hi) Z hZlip' (hZb i hi))
      rw [hZlip, ← hc₁d, ← hNd] at h
      rw [hm, hLi, hΔ]
      exact h
    refine (Finset.sum_le_sum h1).trans ((hΘ 0).trans ?_)
    linarith only [hΘle, hMfin, hAnX, hLfin, hM0, mul_nonneg (mul_nonneg hfac hCL0) hδ0]

/-! ### Absolute continuity -/

open Classical in
/-- The left trace as a function of the real aperture, extended by zero past contact. -/
def leftTraceAt (z : ℂ) (x : ℝ) : ℂ :=
  if h : x ∈ precontactSet then evalVectorLeftTrace (toPrecontact h) z else 0

theorem leftTraceAt_coe (z : ℂ) (b : PrecontactAperture) :
    leftTraceAt z b.1.1 = evalVectorLeftTrace b z := by
  have hb : b.1.1 ∈ precontactSet := ⟨b.1.2, b.2⟩
  rw [leftTraceAt, dif_pos hb]
  rfl

open Classical in
/-- A real aperture as a precontact aperture, with a default past contact. -/
def precontactOr (d : PrecontactAperture) (x : ℝ) : PrecontactAperture :=
  if h : x ∈ precontactSet then toPrecontact h else d

theorem precontactOr_coe (d : PrecontactAperture) {x : ℝ} (h : x ∈ precontactSet) :
    (precontactOr d x).1.1 = x := by
  rw [precontactOr, dif_pos h]
  rfl

private theorem Icc_precontact {a₁ a₂ : PrecontactAperture} {x : ℝ} (hx : x ∈ Icc a₁.1.1 a₂.1.1) :
    x ∈ precontactSet :=
  ⟨a₁.1.2.trans_le hx.1, (EReal.coe_le_coe_iff.mpr hx.2).trans_lt a₂.2⟩

/-- **The left trace is absolutely continuous before contact.** -/
theorem absolutelyContinuousOnInterval_leftTraceAt (z : ℂ) {a₁ a₂ : PrecontactAperture}
    (h : a₁.1.1 ≤ a₂.1.1) : AbsolutelyContinuousOnInterval (leftTraceAt z) a₁.1.1 a₂.1.1 := by
  rw [absolutelyContinuousOnInterval_iff]
  intro e he
  obtain ⟨C₁, C₂, hC₁, hC₂, hV⟩ := exists_partial_variation_bound h z
  obtain ⟨A₀, hA₀, hA₀b⟩ := exists_uniform_endpoint_data a₁ a₂ z
  obtain ⟨η, hη, hηs⟩ : ∃ η : ℝ, 0 < η ∧ C₁ * logarithmicRenewalMass η < e / 2 := by
    have ht := tendsto_logarithmicRenewalMass_zero.const_mul C₁
    rw [mul_zero] at ht
    have hev := ht.eventually (Iio_mem_nhds (show (0 : ℝ) < e / 2 by positivity))
    obtain ⟨ρ, hb, hp⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨ρ, hp, hb⟩
  obtain ⟨D, hDd⟩ : ∃ D, D = C₁ * 2 / η + C₂ + 2 * ‖z‖ * A₀ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDd]
    positivity
  have hδ₁ : 0 < (e / 2) / (D + 1) := by positivity
  have hδ₂ : 0 < 1 / (‖z‖ + 1) := by positivity
  refine ⟨min ((e / 2) / (D + 1)) (1 / (‖z‖ + 1)), lt_min hδ₁ hδ₂, fun E hE hsum => ?_⟩
  obtain ⟨n, I'⟩ := E
  obtain ⟨hmem, hdis⟩ := hE
  simp only at hmem hdis hsum ⊢
  rw [uIcc_of_le h] at hmem
  obtain ⟨S, hSd⟩ : ∃ S, S = Finset.range n := ⟨_, rfl⟩
  rw [← hSd] at hmem hdis hsum ⊢
  obtain ⟨lo, hlo⟩ : ∃ lo : ℕ → ℝ, lo = fun i => min (I' i).1 (I' i).2 := ⟨_, rfl⟩
  obtain ⟨hi', hhi⟩ : ∃ hi' : ℕ → ℝ, hi' = fun i => max (I' i).1 (I' i).2 := ⟨_, rfl⟩
  have hloI (i : ℕ) (hi : i ∈ S) : lo i ∈ Icc a₁.1.1 a₂.1.1 := by
    rw [hlo]
    rcases le_total (I' i).1 (I' i).2 with hle | hle
    · simpa only [min_eq_left hle] using (hmem i hi).1
    · simpa only [min_eq_right hle] using (hmem i hi).2
  have hhiI (i : ℕ) (hi : i ∈ S) : hi' i ∈ Icc a₁.1.1 a₂.1.1 := by
    rw [hhi]
    rcases le_total (I' i).1 (I' i).2 with hle | hle
    · simpa only [max_eq_right hle] using (hmem i hi).2
    · simpa only [max_eq_left hle] using (hmem i hi).1
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℕ → PrecontactAperture, Aa = fun i => precontactOr a₁ (lo i) := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ Bb : ℕ → PrecontactAperture, Bb = fun i => precontactOr a₁ (hi' i) := ⟨_, rfl⟩
  have hAv (i : ℕ) (hi : i ∈ S) : (Aa i).1.1 = lo i := by
    rw [hAa]
    exact precontactOr_coe a₁ (Icc_precontact (hloI i hi))
  have hBv (i : ℕ) (hi : i ∈ S) : (Bb i).1.1 = hi' i := by
    rw [hBb]
    exact precontactOr_coe a₁ (Icc_precontact (hhiI i hi))
  have hlh (i : ℕ) : lo i ≤ hi' i := by
    rw [hlo, hhi]
    exact min_le_max
  have hfam : ∀ i ∈ S, a₁.1.1 ≤ (Aa i).1.1 ∧ (Aa i).1.1 ≤ (Bb i).1.1 ∧ (Bb i).1.1 ≤ a₂.1.1 := by
    intro i hi
    rw [hAv i hi, hBv i hi]
    exact ⟨(hloI i hi).1, hlh i, (hhiI i hi).2⟩
  have hfdis : Set.PairwiseDisjoint (↑S : Set ℕ) (fun i => Ioc (Aa i).1.1 (Bb i).1.1) := by
    intro i hi j hj hij
    have hd := hdis hi hj hij
    have hmS (k : ℕ) (hk : k ∈ S) : Ioc (Aa k).1.1 (Bb k).1.1 = uIoc (I' k).1 (I' k).2 := by
      rw [hAv k hk, hBv k hk, hlo, hhi]
      rfl
    simp only [Function.onFun]
    rw [hmS i hi, hmS j hj]
    exact hd
  obtain ⟨hvar, htr⟩ := hV S Aa Bb hfam hfdis η hη
  -- The sum of the lengths.
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = ∑ i ∈ S, ((Bb i).1.1 - (Aa i).1.1) := ⟨_, rfl⟩
  have hdist (i : ℕ) (hi : i ∈ S) : dist (I' i).1 (I' i).2 = (Bb i).1.1 - (Aa i).1.1 := by
    rw [hAv i hi, hBv i hi, hlo, hhi, Real.dist_eq]
    simp only
    rw [max_sub_min_eq_abs']
  have hδsum : ∑ i ∈ S, dist (I' i).1 (I' i).2 = δ := by
    rw [hδd]
    exact Finset.sum_congr rfl hdist
  rw [hδsum] at hsum
  have hδ0 : 0 ≤ δ := by
    rw [hδd]
    exact Finset.sum_nonneg fun i hi => sub_nonneg.mpr (hfam i hi).2.1
  have hD2 : ∑ i ∈ S, (2 * (Bb i).1.1 - 2 * (Aa i).1.1) = 2 * δ := by
    rw [hδd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hD2, ← hδd] at htr
  -- Each term.
  have hterm (i : ℕ) (hi : i ∈ S) : dist (leftTraceAt z (I' i).1) (leftTraceAt z (I' i).2) ≤
      ‖evalVectorLeftTrace (Bb i) z -
        chartPhase z ((Bb i).1.1 - (Aa i).1.1) * evalVectorLeftTrace (Aa i) z‖ +
      2 * ‖z‖ * ((Bb i).1.1 - (Aa i).1.1) * A₀ := by
    have hh0 : 0 ≤ (Bb i).1.1 - (Aa i).1.1 := sub_nonneg.mpr (hfam i hi).2.1
    have hhδ : (Bb i).1.1 - (Aa i).1.1 ≤ δ := by
      rw [hδd]
      exact Finset.single_le_sum (f := fun k => (Bb k).1.1 - (Aa k).1.1)
        (fun k hk => sub_nonneg.mpr (hfam k hk).2.1) hi
    have hsm : ((Bb i).1.1 - (Aa i).1.1) * ‖z‖ ≤ 1 := by
      have h1 : (Bb i).1.1 - (Aa i).1.1 ≤ 1 / (‖z‖ + 1) :=
        hhδ.trans (hsum.le.trans (min_le_right _ _))
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith only [h1, hh0, norm_nonneg z]
    have hph := norm_chartPhase_sub_one_le z hh0 hsm
    have hTb : ‖evalVectorLeftTrace (Aa i) z‖ ≤ A₀ := (hA₀b (Aa i) (hfam i hi).1
      ((hfam i hi).2.1.trans (hfam i hi).2.2)).1
    have hsplit : evalVectorLeftTrace (Bb i) z - evalVectorLeftTrace (Aa i) z =
        (evalVectorLeftTrace (Bb i) z -
          chartPhase z ((Bb i).1.1 - (Aa i).1.1) * evalVectorLeftTrace (Aa i) z) +
        (chartPhase z ((Bb i).1.1 - (Aa i).1.1) - 1) * evalVectorLeftTrace (Aa i) z := by ring
    have hvals : dist (leftTraceAt z (I' i).1) (leftTraceAt z (I' i).2) =
        ‖evalVectorLeftTrace (Bb i) z - evalVectorLeftTrace (Aa i) z‖ := by
      have hA' : leftTraceAt z (lo i) = evalVectorLeftTrace (Aa i) z := by
        rw [← leftTraceAt_coe, hAv i hi]
      have hB' : leftTraceAt z (hi' i) = evalVectorLeftTrace (Bb i) z := by
        rw [← leftTraceAt_coe, hBv i hi]
      rw [← hA', ← hB', ← dist_eq_norm, hlo, hhi]
      simp only
      rcases le_total (I' i).1 (I' i).2 with hle | hle
      · rw [min_eq_left hle, max_eq_right hle, dist_comm]
      · rw [min_eq_right hle, max_eq_left hle]
    rw [hvals, hsplit]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul]
    exact mul_le_mul hph hTb (norm_nonneg _) (by positivity)
  have hsumterm : ∑ i ∈ S, dist (leftTraceAt z (I' i).1) (leftTraceAt z (I' i).2) ≤
      (C₁ * (logarithmicRenewalMass η + 2 * δ / η) + C₂ * δ) + 2 * ‖z‖ * δ * A₀ := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add htr (le_of_eq ?_)
    rw [hδd, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hDδ : D * δ ≤ (D + 1) * ((e / 2) / (D + 1)) := by
    have h1 : δ ≤ (e / 2) / (D + 1) := hsum.le.trans (min_le_left _ _)
    nlinarith only [mul_le_mul_of_nonneg_left h1 hD0, hδ₁]
  have hcancel : (D + 1) * ((e / 2) / (D + 1)) = e / 2 := by
    field_simp
  have hexp : (C₁ * (logarithmicRenewalMass η + 2 * δ / η) + C₂ * δ) + 2 * ‖z‖ * δ * A₀ =
      C₁ * logarithmicRenewalMass η + D * δ := by
    rw [hDd]
    ring
  rw [hexp] at hsumterm
  linarith only [hsumterm, hDδ, hcancel, hηs]

/-! ### From the traces to the potential -/

theorem absolutelyContinuousOnInterval_congr {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (h : ∀ x ∈ uIcc a b, g x = f x) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro e he
  obtain ⟨δ, hδ, hb⟩ := hf e he
  refine ⟨δ, hδ, fun E hE hs => ?_⟩
  have heq : ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) =
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) :=
    Finset.sum_congr rfl fun i hi => by
      rw [h _ (hE.1 i hi).1, h _ (hE.1 i hi).2]
  rw [heq]
  exact hb E hE hs

/-- Lipschitz maps preserve absolute continuity. -/
theorem absolutelyContinuousOnInterval_comp {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {K : NNReal} {s : Set X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hs : ∀ x ∈ uIcc a b, f x ∈ s)
    (hg : LipschitzOnWith K g s) : AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro e he
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hb⟩ := hf (e / ((K : ℝ) + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hsum => ?_⟩
  have h1 := hb E hE hsum
  calc
    _ ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (f (E.2 i).1) (f (E.2 i).2) :=
      Finset.sum_le_sum fun i hi => hg.dist_le_mul _ (hs _ (hE.1 i hi).1) _ (hs _ (hE.1 i hi).2)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((K : ℝ) + 1) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) :=
      mul_le_mul_of_nonneg_right (by linarith only) (Finset.sum_nonneg fun _ _ => dist_nonneg)
    _ < ((K : ℝ) + 1) * (e / ((K : ℝ) + 1)) := mul_lt_mul_of_pos_left h1 hK
    _ = e := by field_simp

/-- **The anchor reflection is absolutely continuous before contact.** -/
theorem absolutelyContinuousOnInterval_anchorReflection {a₁ a₂ : PrecontactAperture}
    (h : a₁.1.1 ≤ a₂.1.1) : AbsolutelyContinuousOnInterval anchorReflection a₁.1.1 a₂.1.1 := by
  have hcomp (z : ℂ) : AbsolutelyContinuousOnInterval (fun x => (leftTraceAt z x).re) a₁.1.1 a₂.1.1 :=
    absolutelyContinuousOnInterval_comp (s := univ) (absolutelyContinuousOnInterval_leftTraceAt z h)
      (fun _ _ => mem_univ _) Complex.reCLM.lipschitz.lipschitzOnWith
  obtain ⟨U, hU⟩ : ∃ U : ℝ → ℝ, U = fun x => (leftTraceAt I x).re := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = fun x => (leftTraceAt (-I) x).re := ⟨_, rfl⟩
  have hUac : AbsolutelyContinuousOnInterval U a₁.1.1 a₂.1.1 := hU ▸ hcomp I
  have hRac : AbsolutelyContinuousOnInterval R a₁.1.1 a₂.1.1 := hR ▸ hcomp (-I)
  have hUc := hUac.continuousOn
  rw [uIcc_of_le h] at hUc
  have hUne (x : ℝ) (hx : x ∈ Icc a₁.1.1 a₂.1.1) : U x ≠ 0 := by
    have hp := Icc_precontact hx
    have := anchorLeftTrace_re_ne_zero (toPrecontact hp)
    rw [hU]
    simp only
    rw [show x = (toPrecontact hp).1.1 from rfl, leftTraceAt_coe]
    exact this
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr h) hUc.abs
  obtain ⟨u₀, hu₀d⟩ : ∃ u₀, u₀ = |U x₀| := ⟨_, rfl⟩
  have hu₀ : 0 < u₀ := by
    rw [hu₀d]
    exact abs_pos.mpr (hUne x₀ hx₀)
  have hUlow (x : ℝ) (hx : x ∈ uIcc a₁.1.1 a₂.1.1) : U x ∈ {y : ℝ | u₀ ≤ |y|} := by
    rw [uIcc_of_le h] at hx
    rw [hu₀d]
    exact hmin hx
  have hinvLip : LipschitzOnWith (Real.toNNReal (1 / u₀ ^ 2)) (fun y : ℝ => y⁻¹) {y : ℝ | u₀ ≤ |y|} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : u₀ ≤ |x| := hx
    have hy' : u₀ ≤ |y| := hy
    have hxne : x ≠ 0 := abs_pos.mp (hu₀.trans_le hx')
    have hyne : y ≠ 0 := abs_pos.mp (hu₀.trans_le hy')
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
    have he : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
      field_simp
    rw [he, abs_div, abs_mul, abs_sub_comm y x, div_eq_mul_inv, one_div, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hprod : u₀ ^ 2 ≤ |x| * |y| := by
      rw [sq]
      exact mul_le_mul hx' hy' hu₀.le (abs_nonneg _)
    exact inv_anti₀ (by positivity) hprod
  have hinvac := absolutelyContinuousOnInterval_comp hUac hUlow hinvLip
  have hprod := hRac.mul hinvac
  refine absolutelyContinuousOnInterval_congr hprod fun x hx => ?_
  rw [uIcc_of_le h] at hx
  have hp := Icc_precontact hx
  have hc := anchorReflection_coe (toPrecontact hp)
  have hl : leftTraceAt I x = evalVectorLeftTrace (toPrecontact hp) I := leftTraceAt_coe I (toPrecontact hp)
  have hr : leftTraceAt (-I) x = evalVectorLeftTrace (toPrecontact hp) (-I) :=
    leftTraceAt_coe (-I) (toPrecontact hp)
  change anchorReflection x = _ / _ at hc
  rw [hc, evalVectorRightTrace_eq_leftTrace_neg, ← hl, ← hr, hU, hR]
  rfl

/-- **The canonical potential is absolutely continuous before contact.** -/
theorem absolutelyContinuousOnInterval_canonicalPotential {base : ℝ} (hbase : base ∈ precontactSet)
    {a₁ a₂ : PrecontactAperture} (h : a₁.1.1 ≤ a₂.1.1) :
    AbsolutelyContinuousOnInterval (canonicalPotential base) a₁.1.1 a₂.1.1 := by
  have hr := absolutelyContinuousOnInterval_anchorReflection h
  have hrc := hr.continuousOn
  rw [uIcc_of_le h] at hrc
  have habs : ContinuousOn (fun x => |anchorReflection x|) (Icc a₁.1.1 a₂.1.1) := hrc.abs
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr h) habs
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = |anchorReflection x₀| := ⟨_, rfl⟩
  have hρ1 : ρ < 1 := by
    rw [hρd]
    exact abs_lt.mpr (anchorReflection_mem (Icc_precontact hx₀))
  have hρ0 : 0 ≤ ρ := by
    rw [hρd]
    exact abs_nonneg _
  have hmem (x : ℝ) (hx : x ∈ uIcc a₁.1.1 a₂.1.1) : anchorReflection x ∈ Icc (-ρ) ρ := by
    rw [uIcc_of_le h] at hx
    have hle : |anchorReflection x| ≤ ρ := by
      rw [hρd]
      exact hmax hx
    exact abs_le.mp hle
  have hρs : 0 < 1 - ρ ^ 2 := by nlinarith only [hρ0, hρ1]
  have hart : LipschitzOnWith (Real.toNNReal (1 / (1 - ρ ^ 2))) Real.artanh (Icc (-ρ) ρ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hb : ∀ t ∈ Icc (-ρ) ρ, ‖1 / (1 - t ^ 2)‖ ≤ 1 / (1 - ρ ^ 2) := fun t ht => by
      have ht2 : t ^ 2 ≤ ρ ^ 2 := sq_le_sq' ht.1 ht.2
      rw [Real.norm_of_nonneg (one_div_nonneg.mpr (by linarith only [ht2, hρs]))]
      exact one_div_le_one_div_of_le hρs (by linarith only [ht2])
    have hd : ∀ t ∈ Icc (-ρ) ρ, HasDerivWithinAt Real.artanh (1 / (1 - t ^ 2)) (Icc (-ρ) ρ) t :=
      fun t ht => (hasDerivAt_artanh ⟨by linarith only [ht.1, hρ1], by linarith only [ht.2, hρ1]⟩).hasDerivWithinAt
    have hmv := (convex_Icc (-ρ) ρ).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
    exact hmv
  have hL := absolutelyContinuousOnInterval_comp hr hmem hart
  -- The gauge.
  have ha₁p : a₁.1.1 ∈ precontactSet := ⟨a₁.1.2, a₁.2⟩
  have ha₂p : a₂.1.1 ∈ precontactSet := ⟨a₂.1.2, a₂.2⟩
  have hlo : min base a₁.1.1 ∈ precontactSet := by
    rcases le_total base a₁.1.1 with hle | hle
    · rwa [min_eq_left hle]
    · rwa [min_eq_right hle]
  have hhi : max base a₂.1.1 ∈ precontactSet := by
    rcases le_total base a₂.1.1 with hle | hle
    · rwa [max_eq_right hle]
    · rwa [max_eq_left hle]
  have hle : min base a₁.1.1 ≤ max base a₂.1.1 :=
    (min_le_right _ _).trans (h.trans (le_max_right _ _))
  have hsub : Icc (min base a₁.1.1) (max base a₂.1.1) ⊆ precontactSet := fun _ ht =>
    ⟨hlo.1.trans_le ht.1, (EReal.coe_le_coe_iff.mpr ht.2).trans_lt hhi.2⟩
  have hI := intervalIntegrable_precontactCanonicalDrift hle hsub
  have hgauge := hI.absolutelyContinuousOnInterval_intervalIntegral (c := base) (by
    rw [uIcc_of_le hle]
    exact ⟨min_le_left _ _, le_max_left _ _⟩)
  have hgm : AbsolutelyContinuousOnInterval (precontactCanonicalGauge base) a₁.1.1 a₂.1.1 := by
    refine hgauge.mono ?_
    rw [uIcc_of_le h, uIcc_of_le hle]
    exact Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
  refine absolutelyContinuousOnInterval_congr (hL.add hgm) fun x hx => ?_
  rw [uIcc_of_le h] at hx
  exact canonicalPotential_eq base (Icc_precontact hx)

/-- **The potential is the integral of its derivative: `q = Ψ′` is a function before contact.** -/
theorem integral_deriv_canonicalPotential {base : ℝ} (hbase : base ∈ precontactSet)
    {a₁ a₂ : PrecontactAperture} (h : a₁.1.1 ≤ a₂.1.1) :
    IntervalIntegrable (deriv (canonicalPotential base)) volume a₁.1.1 a₂.1.1 ∧
      ∫ x in a₁.1.1..a₂.1.1, deriv (canonicalPotential base) x =
        canonicalPotential base a₂.1.1 - canonicalPotential base a₁.1.1 := by
  have hac := absolutelyContinuousOnInterval_canonicalPotential hbase h
  exact ⟨hac.intervalIntegrable_deriv, hac.integral_deriv_eq_sub⟩

end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
