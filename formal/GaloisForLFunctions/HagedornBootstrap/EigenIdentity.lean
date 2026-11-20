import GaloisForLFunctions.HagedornBootstrap.CardyWeight
import GaloisForLFunctions.HagedornBootstrap.BesselSeries

/-!
# The eigen-identity of the spinless bootstrap

Written in `t = |r|²/2`, the planar Fourier transform of a radial function is
`ĝ(s) = 2π ∫₀^∞ g(t) J₀(4π√(st)) dt`, and every crossing functional obeys `ĝ = −g`. The corpus
`J₀` is the Cardy kernel at negative order, `J₀(4π√(st)) = K_{−s}(t)`, and `K_α(t)` is an entire
function of the product `αt`. So the transform has one formula for every real `s`,

  `ĝ(s) = 2π ∫₀^∞ g(t) K_{−s}(t) dt`,

and at `s = −α ≤ 0` the relation `ĝ = −g` is the **eigen-identity**
`g(−α) = −2π ∫₀^∞ g(t) K_α(t) dt`: the values of a functional below the BTZ threshold are Cardy-weighted
integrals of its values above it.

This file proves the identity unconditionally for the crossing kernel
`Ξ_β(t) = e^{−2πβt} − β⁻¹e^{−2πt/β}` and for every finite combination of crossing kernels, at every
real `s`. The engine is the Laplace transform `2π∫₀^∞ K_α(t) e^{−2πβt} dt = β⁻¹e^{2πα/β}`, now for
every real `α`. Taking the second difference at `a, a − 1, a − 2` gives the vacuum value of a
functional as minus its integral against the Cardy density:
`g(−a) − 2g(−a + 1) + g(−a + 2) = −2π ∫₀^∞ g(t) V(t) dt`.
-/

noncomputable section

open Real Set MeasureTheory Finset

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### The Laplace transform of the Cardy kernel at every real order -/

/-- **`2π∫₀^∞ K_α(t) e^{−2πβt} dt = β⁻¹ e^{2πα/β}` for every real `α` and `β > 0`.** -/
theorem laplace_cardyKernel_real (α : ℝ) {β : ℝ} (hβ : 0 < β) :
    2 * π * ∫ t in Ioi 0, cardyKernel α t * Real.exp (-(2 * π * β * t)) =
      β⁻¹ * Real.exp (2 * π * α / β) := by
  set r := 2 * π * β with hr
  have hr0 : 0 < r := by positivity
  set c : ℕ → ℝ := fun i => (4 * π ^ 2 * α) ^ i / (i.factorial : ℝ) ^ 2 with hc
  set F : ℕ → ℝ → ℝ := fun i t => c i * (t ^ i * Real.exp (-(r * t))) with hF
  have hFint : ∀ i, Integrable (F i) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_pow_mul_exp_neg i hr0).const_mul (c i)
  have hFval : ∀ i, ∫ t in Ioi 0, F i t = c i * (i.factorial / r ^ (i + 1)) := fun i => by
    simp only [hF]; rw [integral_const_mul, integral_pow_mul_exp_neg i hr0]
  -- absolute values: `|c_i| = (4π²|α|)ⁱ/(i!)²`
  have habs : ∀ i, |c i| = (4 * π ^ 2 * |α|) ^ i / (i.factorial : ℝ) ^ 2 := fun i => by
    simp only [hc]
    rw [abs_div, abs_pow, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (i.factorial : ℝ)),
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2)]
  have hFnorm : ∀ i, ∫ t in Ioi 0, ‖F i t‖ = |c i| * (i.factorial / r ^ (i + 1)) := fun i => by
    have : ∀ t ∈ Ioi (0 : ℝ), ‖F i t‖ = |c i| * (t ^ i * Real.exp (-(r * t))) := fun t ht => by
      simp only [hF, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (pow_nonneg (mem_Ioi.mp ht).le i), abs_of_pos (Real.exp_pos _)]
    rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
      integral_pow_mul_exp_neg i hr0]
  -- the coefficient series is `r⁻¹ Σ (4π²α/r)ⁱ/i!`
  have hcoef : ∀ (γ : ℝ) (i : ℕ), (4 * π ^ 2 * γ) ^ i / (i.factorial : ℝ) ^ 2 *
      (i.factorial / r ^ (i + 1)) = r⁻¹ * ((4 * π ^ 2 * γ / r) ^ i / i.factorial) := by
    intro γ i
    have hf : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
    rw [div_pow]
    field_simp
    ring
  have hexp : ∀ x : ℝ, HasSum (fun i : ℕ => x ^ i / i.factorial) (Real.exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hsumI : HasSum (fun i => ∫ t in Ioi 0, F i t) (r⁻¹ * Real.exp (4 * π ^ 2 * α / r)) := by
    simp_rw [hFval]
    simp only [hc]
    simp_rw [hcoef α]
    exact (hexp _).mul_left r⁻¹
  have hsumN : Summable fun i => ∫ t in Ioi 0, ‖F i t‖ := by
    simp_rw [hFnorm, habs, hcoef |α|]
    exact ((hexp _).mul_left r⁻¹).summable
  have hswap := integral_tsum_of_summable_integral_norm hFint hsumN
  rw [hsumI.tsum_eq] at hswap
  have hpt : ∫ t in Ioi 0, (∑' i, F i t) = ∫ t in Ioi 0, cardyKernel α t * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have hk := ((summable_cardyTerm (4 * π ^ 2 * α * t)).hasSum).mul_right (Real.exp (-(r * t)))
    rw [show cardyKernel α t = ∑' i : ℕ, (4 * π ^ 2 * α * t) ^ i / (i.factorial : ℝ) ^ 2 from rfl,
      ← hk.tsum_eq]
    congr 1; funext i
    simp only [hF, hc]
    rw [mul_pow]; ring
  rw [hpt] at hswap
  rw [show (fun t => cardyKernel α t * Real.exp (-(2 * π * β * t))) =
    fun t => cardyKernel α t * Real.exp (-(r * t)) from rfl, ← hswap]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [hr, show 4 * π ^ 2 * α / (2 * π * β) = 2 * π * α / β by field_simp; ring]
  field_simp

/-- The Gaussian against the Cardy kernel is integrable for every real order. -/
theorem integrableOn_cardyKernel_mul_exp (α : ℝ) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun t => cardyKernel α t * Real.exp (-(2 * π * β * t))) (volume.restrict (Ioi 0)) := by
  by_contra hni
  have h := laplace_cardyKernel_real α hβ
  rw [integral_undef hni, mul_zero] at h
  have : 0 < β⁻¹ * Real.exp (2 * π * α / β) := by positivity
  linarith

/-! ### The planar transform with one kernel for all `s` -/

/-- The planar Fourier transform in the variable `t`, with the kernel `K_{−s}`:
`ĝ(s) = 2π ∫₀^∞ g(t) K_{−s}(t) dt`. -/
def planarTransform (g : ℝ → ℝ) (s : ℝ) : ℝ := 2 * π * ∫ t in Ioi 0, g t * cardyKernel (-s) t

/-- For `s ≥ 0` it is the Fourier–Bessel transform with the corpus `J₀`. -/
theorem planarTransform_eq_besselJ0 (g : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    planarTransform g s = 2 * π * ∫ t in Ioi 0, g t * RHTower.besselJ0 (4 * π * √(s * t)) := by
  unfold planarTransform
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [besselJ0_eq_cardyKernel_neg hs (mem_Ioi.mp ht).le]

/-- For `s = −α ≤ 0` it integrates against the Cardy kernel `K_α`. -/
theorem planarTransform_neg (g : ℝ → ℝ) (α : ℝ) :
    planarTransform g (-α) = 2 * π * ∫ t in Ioi 0, g t * cardyKernel α t := by
  unfold planarTransform; rw [neg_neg]

/-- **The Gaussian transform at every real `s`:** `e^{−2πβt} ↦ β⁻¹ e^{−2πs/β}`. -/
theorem planarTransform_gaussian {β : ℝ} (hβ : 0 < β) (s : ℝ) :
    planarTransform (fun t => Real.exp (-(2 * π * β * t))) s = β⁻¹ * Real.exp (-(2 * π * s / β)) := by
  unfold planarTransform
  have h := laplace_cardyKernel_real (-s) hβ
  rw [show 2 * π * -s / β = -(2 * π * s / β) by ring] at h
  rw [← h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  ring

/-! ### The crossing kernel -/

/-- The crossing kernel `Ξ_β(t) = e^{−2πβt} − β⁻¹ e^{−2πt/β}` in the variable `t`. -/
def crossingT (β t : ℝ) : ℝ := Real.exp (-(2 * π * β * t)) - β⁻¹ * Real.exp (-(2 * π * β⁻¹ * t))

theorem integrableOn_crossingT_mul (β : ℝ) (hβ : 0 < β) (α : ℝ) :
    Integrable (fun t => crossingT β t * cardyKernel α t) (volume.restrict (Ioi 0)) := by
  have h1 := integrableOn_cardyKernel_mul_exp α hβ
  have h2 := (integrableOn_cardyKernel_mul_exp α (inv_pos.mpr hβ)).const_mul β⁻¹
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, crossingT]
  ring

/-- **The crossing kernel is a `−1` eigenfunction at every real `s`**, including the
continuation below the BTZ threshold. -/
theorem planarTransform_crossingT {β : ℝ} (hβ : 0 < β) (s : ℝ) :
    planarTransform (crossingT β) s = -crossingT β s := by
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ
  have h1 := planarTransform_gaussian hβ s
  have h2 := planarTransform_gaussian hb s
  have i1 := integrableOn_cardyKernel_mul_exp (-s) hβ
  have i2 := (integrableOn_cardyKernel_mul_exp (-s) hb).const_mul β⁻¹
  unfold planarTransform at h1 h2 ⊢
  have e : (fun t => crossingT β t * cardyKernel (-s) t) =
      fun t => cardyKernel (-s) t * Real.exp (-(2 * π * β * t)) -
        β⁻¹ * (cardyKernel (-s) t * Real.exp (-(2 * π * β⁻¹ * t))) := by
    funext t; unfold crossingT; ring
  have e1 : ∫ t in Ioi 0, (fun t => Real.exp (-(2 * π * β * t))) t * cardyKernel (-s) t =
      ∫ t in Ioi 0, cardyKernel (-s) t * Real.exp (-(2 * π * β * t)) := by
    congr 1; funext t; ring
  have e2 : ∫ t in Ioi 0, (fun t => Real.exp (-(2 * π * β⁻¹ * t))) t * cardyKernel (-s) t =
      ∫ t in Ioi 0, cardyKernel (-s) t * Real.exp (-(2 * π * β⁻¹ * t)) := by
    congr 1; funext t; ring
  rw [e1] at h1
  rw [e2, inv_inv] at h2
  rw [e, integral_sub i1 i2, integral_const_mul, mul_sub, h1]
  unfold crossingT
  rw [show 2 * π * (β⁻¹ * ∫ t in Ioi 0, cardyKernel (-s) t * Real.exp (-(2 * π * β⁻¹ * t))) =
    β⁻¹ * (2 * π * ∫ t in Ioi 0, cardyKernel (-s) t * Real.exp (-(2 * π * β⁻¹ * t))) by ring, h2]
  have : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
  rw [show -(2 * π * s / β) = -(2 * π * β⁻¹ * s) by ring, show -(2 * π * s / β⁻¹) = -(2 * π * β * s) by
    field_simp]
  rw [← mul_assoc, this, one_mul]
  ring

/-- **The eigen-identity for the crossing kernel:** `Ξ_β(−α) = −2π ∫₀^∞ Ξ_β(t) K_α(t) dt`. -/
theorem eigenIdentity_crossingT {β : ℝ} (hβ : 0 < β) (α : ℝ) :
    crossingT β (-α) = -(2 * π * ∫ t in Ioi 0, crossingT β t * cardyKernel α t) := by
  have h := planarTransform_crossingT hβ (-α)
  rw [planarTransform_neg] at h
  linarith

/-! ### Finite combinations of crossing kernels -/

/-- A finite combination `g = Σ_j c_j Ξ_{β_j}` of crossing kernels. -/
def crossingCombination {ι : Type*} (S : Finset ι) (c β : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ S, c j * crossingT (β j) t

/-- **The eigen-identity for every finite combination of crossing kernels.** -/
theorem eigenIdentity_combination {ι : Type*} (S : Finset ι) (c β : ι → ℝ)
    (hβ : ∀ j ∈ S, 0 < β j) (α : ℝ) :
    crossingCombination S c β (-α) =
      -(2 * π * ∫ t in Ioi 0, crossingCombination S c β t * cardyKernel α t) := by
  unfold crossingCombination
  have hint : ∀ j ∈ S, Integrable (fun t => c j * (crossingT (β j) t * cardyKernel α t))
      (volume.restrict (Ioi 0)) := fun j hj => (integrableOn_crossingT_mul (β j) (hβ j hj) α).const_mul _
  have e : (fun t => (∑ j ∈ S, c j * crossingT (β j) t) * cardyKernel α t) =
      fun t => ∑ j ∈ S, c j * (crossingT (β j) t * cardyKernel α t) := by
    funext t; rw [Finset.sum_mul]; congr 1; funext j; ring
  rw [e, integral_finsetSum S hint, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_const_mul, eigenIdentity_crossingT (hβ j hj)]
  ring

/-! ### The vacuum value -/

/-- **The vacuum value is minus the Cardy-weighted integral:** for every finite combination of
crossing kernels and every real `a`,
`g(−a) − 2g(−a + 1) + g(−a + 2) = −2π ∫₀^∞ g(t) V(t) dt` with `V = K_a − 2K_{a−1} + K_{a−2}`. -/
theorem vacuumValue_eq_cardy {ι : Type*} (S : Finset ι) (c β : ι → ℝ) (hβ : ∀ j ∈ S, 0 < β j)
    (a : ℝ) :
    crossingCombination S c β (-a) - 2 * crossingCombination S c β (-(a - 1)) +
        crossingCombination S c β (-(a - 2)) =
      -(2 * π * ∫ t in Ioi 0, crossingCombination S c β t * cardyWeight a t) := by
  have hint : ∀ α : ℝ, Integrable (fun t => crossingCombination S c β t * cardyKernel α t)
      (volume.restrict (Ioi 0)) := by
    intro α
    have : Integrable (fun t => ∑ j ∈ S, c j * (crossingT (β j) t * cardyKernel α t))
        (volume.restrict (Ioi 0)) :=
      integrable_finsetSum S fun j hj => (integrableOn_crossingT_mul (β j) (hβ j hj) α).const_mul _
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [crossingCombination, Finset.sum_mul]
    congr 1; funext j; ring
  rw [eigenIdentity_combination S c β hβ a, eigenIdentity_combination S c β hβ (a - 1),
    eigenIdentity_combination S c β hβ (a - 2)]
  have e : (fun t => crossingCombination S c β t * cardyWeight a t) =
      fun t => crossingCombination S c β t * cardyKernel a t -
        2 * (crossingCombination S c β t * cardyKernel (a - 1) t) +
        crossingCombination S c β t * cardyKernel (a - 2) t := by
    funext t; unfold cardyWeight; ring
  have i12 : Integrable (fun t => crossingCombination S c β t * cardyKernel a t -
      2 * (crossingCombination S c β t * cardyKernel (a - 1) t)) (volume.restrict (Ioi 0)) :=
    (hint a).sub ((hint (a - 1)).const_mul 2)
  rw [e, integral_add i12 (hint (a - 2)), integral_sub (hint a) ((hint (a - 1)).const_mul 2),
    integral_const_mul]
  ring

end GaloisForLFunctions.HagedornBootstrap
