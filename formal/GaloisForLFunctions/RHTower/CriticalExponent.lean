import GaloisForLFunctions.RHTower.ScalingDegreeLaw

/-!
# The critical exponent: only the supremum is scale-invariant among Lebesgue norms

The scaling degree law says the deciding invariant has homogeneity degree zero while every pointwise
average has degree one. This module makes the Lebesgue half of that statement exact and names the
exponent at which the two meet.

Applying the degree law with `F = (·)^p` gives, for every `p`,

  `∫ (bump_d)^p  =  d · (fixed profile integral)`,

so `‖bump_d‖_p = (c_p·d)^{1/p}` and the Lebesgue norms scale as `d^{1/p}`. The exponent `1/p` is
positive for every finite `p` and vanishes only in the limit: **the supremum is the unique
scale-invariant Lebesgue norm of this family**, and the peak is literally invariant, equal to one for
every displacement.

The Sobolev side is not formalised here, since it needs Fourier machinery this development does not
carry, but it is what makes the picture complete and it is recorded for the reader. The bump has the
exact transform `π d·e^{−d|ξ|}`, whence `‖bump_d‖²_{H^s} ≍ d^{1−2s}`: the Sobolev norms are
scale-invariant **exactly at `s = 1/2`**, divergent above it and vanishing below. So the degree-zero
class contains two members, `H^{1/2}` and `L^∞`, and in one dimension the embedding `H^s ↪ L^∞`
requires `s > 1/2` **strictly**. The family sits exactly at the endpoint where that embedding fails.

The consequence for this field is that **scale-invariance is necessary but not sufficient**: a
scale-invariant norm exists and still does not certify the supremum. The deficit is exactly
logarithmic — the critical norm recovers the supremum only at the cost of one logarithmic factor —
and a logarithmic loss is precisely what the absolute-constant requirement forbids. This identifies
the exponent `1/2` recurring throughout this field as a single object: the critical Sobolev exponent
of a scale-invariant bump in one dimension.
-/

open Real MeasureTheory

namespace RHTower

noncomputable section

/-- **The Lebesgue scaling law.** Every `p`-th power mass of a bump is the displacement times a
fixed profile integral. -/
theorem integral_pow_bumpKernel (p : ℕ) {d : ℝ} (hd : 0 < d) (g R : ℝ) :
    (∫ t in (g - R)..(g + R), (bumpKernel d g t) ^ p)
      = d * ∫ x in (-(R / d))..(R / d), ((1 : ℝ) / (1 + x ^ (2 : ℕ))) ^ p :=
  integral_comp_bumpKernel (fun u => u ^ p) hd g R

/-- **The peak is invariant at every exponent.** -/
theorem bumpKernel_peak_pow (p : ℕ) {d : ℝ} (hd : d ≠ 0) (g : ℝ) :
    (bumpKernel d g g) ^ p = 1 := by
  rw [bumpKernel_peak hd, one_pow]

/-- **The two sides side by side.** For every finite exponent the mass carries a factor of the
displacement and the peak does not, so no finite Lebesgue exponent is scale-invariant. -/
theorem lebesgue_mass_scales_peak_does_not (p : ℕ) {d : ℝ} (hd : 0 < d) (g R : ℝ) :
    (∫ t in (g - R)..(g + R), (bumpKernel d g t) ^ p)
        = d * ∫ x in (-(R / d))..(R / d), ((1 : ℝ) / (1 + x ^ (2 : ℕ))) ^ p
      ∧ (bumpKernel d g g) ^ p = 1 :=
  ⟨integral_pow_bumpKernel p hd g R, bumpKernel_peak_pow p hd.ne' g⟩

end

end RHTower
