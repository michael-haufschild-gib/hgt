import GaloisForLFunctions.HTGeometry.PowerSubstitutionForwardDA
import GaloisForLFunctions.HTGeometry.EvenPowerCanonicalProductDA

/-!
# The cyclic-norm dichotomy

Differential algebraicity is invariant under every monomial change of variable `z ↦ c z^q`: the
descent was proved in `PowerSubstitutionDifferentialDescent`, the forward direction in
`PowerSubstitutionForwardDA`.  Combined with the exact cyclic-norm law this settles the differential
status of the `q`-fold root-of-unity norm

`N_{p/q}(z) = ∏_{j<q} W_{p/q}(ω^j z) = W_p((-1)^{q+1} z^q)`

in terms of the integer-exponent product `W_p`: the norm is differentially algebraic when `p` is
even, and hypertranscendental whenever `W_p` is.
-/

namespace HTGeometry

open GaloisForLFunctions

/-- **Forward monomial transfer.**  For an entire `f`, `c ≠ 0` and `q ≥ 1`, differential
algebraicity of `f` gives differential algebraicity of `z ↦ f(c z^q)`. -/
theorem differentiallyAlgebraic_comp_const_mul_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {c : ℂ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q)
    (h : DifferentiallyAlgebraic f) : DifferentiallyAlgebraic (fun z : ℂ => f (c * z ^ q)) := by
  have hfd : Differentiable ℂ f := Complex.analyticOnNhd_univ_iff_differentiable.mp hf
  have hscaledA : AnalyticOnNhd ℂ (fun w : ℂ => f (c * w)) Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact hfd.comp (by fun_prop)
  have hcompA : AnalyticOnNhd ℂ (fun z : ℂ => (fun w : ℂ => f (c * w)) (z ^ q)) Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact hfd.comp (by fun_prop)
  have hscaledDA : DifferentiallyAlgebraic (fun w : ℂ => f (c * w)) :=
    h.comp_const_mul_uncond hc
  have hres : DifferentiallyAlgebraic (fun z : ℂ => (fun w : ℂ => f (c * w)) (z ^ q)) :=
    differentiallyAlgebraic_comp_pow (f := fun w : ℂ => f (c * w)) hq
      (differentiable_iteratedDeriv_of_entire hscaledA)
      (differentiable_iteratedDeriv_of_entire hcompA) hscaledDA
  exact hres

/-- **Monomial invariance of differential algebraicity.** -/
theorem differentiallyAlgebraic_comp_const_mul_pow_iff {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {c : ℂ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) :
    DifferentiallyAlgebraic (fun z : ℂ => f (c * z ^ q)) ↔ DifferentiallyAlgebraic f :=
  ⟨differentiallyAlgebraic_of_comp_const_mul_pow hf hc hq,
    differentiallyAlgebraic_comp_const_mul_pow hf hc hq⟩

/-- **Even branch of the cyclic-norm dichotomy.**  For an even numerator the `q`-fold norm of the
rational-power canonical product is differentially algebraic. -/
theorem differentiallyAlgebraic_cyclicNorm_of_even {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpe : Even p) {ω : ℂ} (hω : IsPrimitiveRoot ω q) :
    DifferentiallyAlgebraic
      (fun z : ℂ => ∏ j ∈ Finset.range q,
        powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnorm : (fun z : ℂ => ∏ j ∈ Finset.range q,
        powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z))
      = fun z : ℂ => powerCanonicalProduct (p : ℝ) ((-1) ^ (q + 1) * z ^ q) :=
    funext fun z => prod_powerCanonicalProduct_primitiveRoot hp hq hω z
  rw [hnorm]
  exact differentiallyAlgebraic_comp_const_mul_pow
    (analyticOnNhd_powerCanonicalProduct hpR) (pow_ne_zero _ (by norm_num)) hq
    (differentiallyAlgebraic_powerCanonicalProduct_of_even hp hpe)

/-- **Hypertranscendental branch of the cyclic-norm dichotomy.** -/
theorem hypertranscendental_cyclicNorm_of_hypertranscendental {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hHT : Hypertranscendental (powerCanonicalProduct (p : ℝ))) {ω : ℂ}
    (hω : IsPrimitiveRoot ω q) :
    Hypertranscendental
      (fun z : ℂ => ∏ j ∈ Finset.range q,
        powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnorm : (fun z : ℂ => ∏ j ∈ Finset.range q,
        powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z))
      = fun z : ℂ => powerCanonicalProduct (p : ℝ) ((-1) ^ (q + 1) * z ^ q) :=
    funext fun z => prod_powerCanonicalProduct_primitiveRoot hp hq hω z
  rw [hnorm]
  intro hDA
  exact hHT (differentiallyAlgebraic_of_comp_const_mul_pow
    (analyticOnNhd_powerCanonicalProduct hpR) (pow_ne_zero _ (by norm_num)) hq hDA)

end HTGeometry

