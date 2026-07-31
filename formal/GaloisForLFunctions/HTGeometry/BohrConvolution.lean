import GaloisForLFunctions.HTGeometry.BohrMeanInvariance

/-!
# Fourier-mode extraction: convolution against a trigonometric kernel

Averaging a translate of `f` against the character `e^{-iμu}` extracts exactly the `μ`-th
Bohr–Fourier mode:

`M_u( f(u+t) · e^{-iμu} ) = a_f(μ) · e^{iμt}`.

Against a trigonometric kernel `K = ∑_i c_i e^{-iμ_i u}` the same computation returns the
corresponding weighted partial sum of the Bohr–Fourier series,

`M_u( f(u+t) · K(u) ) = ∑_i c_i a_f(μ_i) e^{iμ_i t}`.

This is the mechanism of the Bochner–Fejér construction: every such convolution is a trigonometric
polynomial with the *right* coefficients, and what remains for the approximation theorem is only the
choice of weights `c_i` making these polynomials converge uniformly to `f`.  In particular, if every
Bohr coefficient vanishes then every such convolution vanishes identically.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- **Mode extraction.**  Averaging a translate of `f` against a character returns that Fourier
mode. -/
theorem bohrMean_translate_mul_bohrChar {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (mu t : ℝ) :
    bohrMean (fun u => f (u + t) * bohrChar mu u) = expChar mu t * bohrCoefficient f mu :=
  bohrCoefficient_comp_add_const hfc hfa t mu

/-- **Convolution against a trigonometric kernel returns the corresponding weighted partial sum of
the Bohr–Fourier series.** -/
theorem bohrMean_translate_mul_trigKernel {ι : Type*} (s : Finset ι) (c : ι → ℂ) (mu : ι → ℝ)
    {f : ℝ → ℂ} (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f) (t : ℝ) :
    bohrMean (fun u => f (u + t) * ∑ i ∈ s, c i * bohrChar (mu i) u)
      = ∑ i ∈ s, (c i * bohrCoefficient f (mu i)) * expChar (mu i) t := by
  have hfct : Continuous fun u : ℝ => f (u + t) := hfc.comp (continuous_id.add continuous_const)
  have hfat : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => f (u + t) :=
    isBohrAlmostPeriodic_comp_add_const hfa t
  have hfun : (fun u : ℝ => f (u + t) * ∑ i ∈ s, c i * bohrChar (mu i) u)
      = fun u : ℝ => ∑ i ∈ s, c i * (f (u + t) * bohrChar (mu i) u) := by
    funext u
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun,
    bohrMean_sum (F := fun i => fun u : ℝ => c i * (f (u + t) * bohrChar (mu i) u)) s
      (fun i _ => continuous_const.mul (hfct.mul (continuous_bohrChar _)))
      (fun i _ => isBohrAlmostPeriodic_const_mul _
        (isBohrAlmostPeriodic_mul_bohrChar hfct hfat _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bohrMean_const_mul (f := fun u : ℝ => f (u + t) * bohrChar (mu i) u) (c i)
    (hfct.mul (continuous_bohrChar _)) (isBohrAlmostPeriodic_mul_bohrChar hfct hfat _),
    bohrMean_translate_mul_bohrChar hfc hfa (mu i) t]
  ring

/-- If every Bohr coefficient of `f` vanishes, every convolution of `f` against a trigonometric
kernel vanishes identically.  An approximation theorem expressing `f` as a uniform limit of such
convolutions would then force `f = 0`; that approximation step is the remaining analytic input. -/
theorem bohrMean_translate_mul_trigKernel_eq_zero {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (mu : ι → ℝ) {f : ℝ → ℂ} (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f)
    (hspec : ∀ lam : ℝ, bohrCoefficient f lam = 0) (t : ℝ) :
    bohrMean (fun u => f (u + t) * ∑ i ∈ s, c i * bohrChar (mu i) u) = 0 := by
  rw [bohrMean_translate_mul_trigKernel s c mu hfc hfa t]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hspec (mu i), mul_zero, zero_mul]

/-- The convolution is a trigonometric polynomial with the expected coefficients: its Bohr
coefficient at `lam` collects the weights `c i · a_f(μ i)` over the frequencies equal to `lam`. -/
theorem bohrCoefficient_trigKernel_convolution {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (mu : ι → ℝ) {f : ℝ → ℂ} (lam : ℝ) :
    bohrCoefficient
        (fun t => ∑ i ∈ s, (c i * bohrCoefficient f (mu i)) * expChar (mu i) t) lam
      = ∑ i ∈ s, if mu i = lam then c i * bohrCoefficient f (mu i) else 0 :=
  bohrCoefficient_sum_expChar s (fun i => c i * bohrCoefficient f (mu i)) mu lam

end

end GaloisForLFunctions
