import GaloisForLFunctions.HTGeometry.RationalPowerCyclicNorm
import GaloisForLFunctions.HTGeometry.PowerSubstitutionDifferentialDescent
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.HypertranscendencePolynomial

/-!
# Hypertranscendence transfers from integer to rational power canonical products

For a positive rational exponent `p/q` the `q`-fold root-of-unity norm of `W_{p/q}` is the
integer-power product `W_p` in the variable `z^q`.  Since differential algebraicity is stable under
finite products of entire functions and under argument scaling, and descends along `z ↦ z^q`, the
hypertranscendence of `W_p` forces the hypertranscendence of `W_{p/q}` for *every* denominator `q`.

* `differentiallyAlgebraic_of_comp_const_mul_pow` — differential algebraicity descends along every
  nonconstant monomial change of variable `z ↦ c z^q`.
* `hypertranscendental_powerCanonicalProduct_ratio` — `W_p` hypertranscendental implies
  `W_{p/q}` hypertranscendental, for all positive integers `p, q`.
-/

namespace HTGeometry

open GaloisForLFunctions

/-- Every iterated derivative of an entire function is differentiable. -/
theorem differentiable_iteratedDeriv_of_entire {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (m : ℕ) : Differentiable ℂ (iteratedDeriv m F) :=
  fun z => (GaloisForLFunctions.HTGeometry.analyticOnNhd_iteratedDeriv hF m z
    (Set.mem_univ z)).differentiableAt

/-- Differential algebraicity of entire functions is closed under finite products. -/
theorem differentiallyAlgebraic_finsetProd {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → ℂ → ℂ) (hA : ∀ i ∈ s, AnalyticOnNhd ℂ (F i) Set.univ)
    (hDA : ∀ i ∈ s, DifferentiallyAlgebraic (F i)) :
    DifferentiallyAlgebraic (fun z => ∏ i ∈ s, F i z) := by
  induction s using Finset.induction with
  | empty => simpa using differentiallyAlgebraic_const (1 : ℂ)
  | insert a B haB ih =>
      have hAa : AnalyticOnNhd ℂ (F a) Set.univ := hA a (Finset.mem_insert_self a B)
      have hDAa : DifferentiallyAlgebraic (F a) := hDA a (Finset.mem_insert_self a B)
      have hAB : ∀ i ∈ B, AnalyticOnNhd ℂ (F i) Set.univ :=
        fun i hi => hA i (Finset.mem_insert_of_mem hi)
      have hDAB : ∀ i ∈ B, DifferentiallyAlgebraic (F i) :=
        fun i hi => hDA i (Finset.mem_insert_of_mem hi)
      have hrest : DifferentiallyAlgebraic (fun z => ∏ i ∈ B, F i z) := ih hAB hDAB
      have hrestA : AnalyticOnNhd ℂ (fun z => ∏ i ∈ B, F i z) Set.univ :=
        fun z _ => B.analyticAt_fun_prod fun i hi => hAB i hi z (Set.mem_univ z)
      have := GaloisForLFunctions.HTGeometry.differentiallyAlgebraic_mul hAa hrestA hDAa hrest
      simpa [Finset.prod_insert haB] using this

/-- **Descent along a monomial change of variable.**  If `f` is entire, `c ≠ 0` and `q ≥ 1`, then
`z ↦ f(c z^q)` satisfying an algebraic differential equation forces `f` to satisfy one. -/
theorem differentiallyAlgebraic_of_comp_const_mul_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {c : ℂ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q)
    (h : DifferentiallyAlgebraic (fun z => f (c * z ^ q))) : DifferentiallyAlgebraic f := by
  have hscaled : AnalyticOnNhd ℂ (fun w : ℂ => f (c * w)) Set.univ := by
    intro w _
    have hinner : AnalyticAt ℂ (fun w : ℂ => c * w) w :=
      analyticAt_const.mul analyticAt_id
    exact (hf (c * w) (Set.mem_univ _)).comp hinner
  have hjets : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m (fun w : ℂ => f (c * w))) :=
    differentiable_iteratedDeriv_of_entire hscaled
  have hpull : DifferentiallyAlgebraic (fun z : ℂ => (fun w : ℂ => f (c * w)) (z ^ q)) := h
  have hbase : DifferentiallyAlgebraic (fun w : ℂ => f (c * w)) :=
    differentiallyAlgebraic_of_comp_pow hjets hq hpull
  exact (differentiallyAlgebraic_comp_const_mul_iff_uncond hc).mp hbase

/-- **Hypertranscendence transfer.**  If the integer-power canonical product `W_p` is
hypertranscendental, then so is the rational-power canonical product `W_{p/q}` for every positive
denominator `q`.

If `W_{p/q}` satisfied an algebraic differential equation, so would each rotation
`z ↦ W_{p/q}(ω^j z)` and hence their product; by the exact cyclic-norm law that product is
`z ↦ W_p((-1)^{q+1} z^q)`, and monomial descent would return an algebraic differential equation for
`W_p`. -/
theorem hypertranscendental_powerCanonicalProduct_ratio {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hHT : Hypertranscendental (powerCanonicalProduct (p : ℝ))) :
    Hypertranscendental (powerCanonicalProduct ((p : ℝ) / (q : ℝ))) := by
  classical
  intro hDA
  apply hHT
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have ha : 0 < (p : ℝ) / (q : ℝ) := div_pos hpR hqR
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω q :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / q), Complex.isPrimitiveRoot_exp q hq.ne'⟩
  have hωne : ω ≠ 0 := hω.ne_zero hq.ne'
  have hAratio : AnalyticOnNhd ℂ (powerCanonicalProduct ((p : ℝ) / (q : ℝ))) Set.univ :=
    analyticOnNhd_powerCanonicalProduct ha
  have hArot : ∀ j ∈ Finset.range q,
      AnalyticOnNhd ℂ (fun z : ℂ => powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z))
        Set.univ := by
    intro j _ z _
    exact (hAratio (ω ^ j * z) (Set.mem_univ _)).comp (analyticAt_const.mul analyticAt_id)
  have hDArot : ∀ j ∈ Finset.range q,
      DifferentiallyAlgebraic
        (fun z : ℂ => powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z)) :=
    fun j _ => hDA.comp_const_mul_uncond (pow_ne_zero j hωne)
  have hprod : DifferentiallyAlgebraic
      (fun z : ℂ => ∏ j ∈ Finset.range q,
        powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z)) :=
    differentiallyAlgebraic_finsetProd (Finset.range q) _ hArot hDArot
  have hnorm : (fun z : ℂ => ∏ j ∈ Finset.range q,
        powerCanonicalProduct ((p : ℝ) / (q : ℝ)) (ω ^ j * z))
      = fun z : ℂ => powerCanonicalProduct (p : ℝ) ((-1) ^ (q + 1) * z ^ q) := by
    funext z
    exact prod_powerCanonicalProduct_primitiveRoot hp hq hω z
  rw [hnorm] at hprod
  have hcne : ((-1 : ℂ) ^ (q + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact differentiallyAlgebraic_of_comp_const_mul_pow
    (analyticOnNhd_powerCanonicalProduct hpR) hcne hq hprod

end HTGeometry

