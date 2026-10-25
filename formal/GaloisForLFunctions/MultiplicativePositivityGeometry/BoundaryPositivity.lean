import GaloisForLFunctions.MultiplicativePositivityGeometry.PositiveDefiniteFunctions

/-!
# Boundary positivity: nonnegative log-coefficients make the boundary divisor positive definite

A weighted frequency family `(wᵢ, λᵢ)` has the cosine trace `u ↦ Σᵢ wᵢ cos(λᵢ u)`, the real part of
the general Dirichlet series `Σᵢ wᵢ e^{-iλᵢ u}` on a vertical line. The logarithmic derivative of an
Euler product with nonnegative log-coefficients restricted to `Re s = 1 + x` is such a trace, e.g.
`Re(−ζ'/ζ)(1 + x + iu) = Σ Λ(n) n^{-1-x} cos(u log n)`.

* `isEvenPosDef_cosineTrace`: nonnegative summable weights give an even positive-definite trace.
  Its Gram form is `Σᵢ wᵢ ((Σⱼ cⱼ cos λᵢxⱼ)² + (Σⱼ cⱼ sin λᵢxⱼ)²)`.
* `IsBoundaryDivisor`: damped nonnegative weights whose normalized traces `x · trace(u)` converge to
  `D(u)` as the damping `x ↓ 0`. For an Euler product, `D(u)` is the pole order minus the zero order
  at `1 + iu`.
* `IsBoundaryDivisor.isEvenPosDef` (**boundary positivity theorem**): every boundary divisor is an
  even positive-definite function on the discrete group `ℝ`. Coefficient positivity of the Euler
  product is, on the boundary line, exactly a positive-definiteness constraint on its divisor; every
  harmonic (Fejér-type) forcing argument is one of its Gram inequalities.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- Cosine trace of a weighted frequency family. -/
noncomputable def cosineTrace {ι : Type*} (w lam : ι → ℝ) (u : ℝ) : ℝ :=
  ∑' i, w i * Real.cos (lam i * u)

theorem summable_cosineTrace_terms {ι : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (lam : ι → ℝ) (u : ℝ) :
    Summable fun i => w i * Real.cos (lam i * u) :=
  Summable.of_norm_bounded hs fun i => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_of_le_one_right (hw i) (Real.abs_cos_le_one _)

theorem cosineTrace_neg {ι : Type*} (w lam : ι → ℝ) (u : ℝ) :
    cosineTrace w lam (-u) = cosineTrace w lam u := by
  simp only [cosineTrace, mul_neg, Real.cos_neg]

/-- One frequency: the real Gram form of `cos(λ(xⱼ − xₖ))` is a sum of two squares. -/
theorem gram_cos_eq {n : ℕ} (lam : ℝ) (x c : Fin n → ℝ) :
    ∑ j, ∑ k, c j * c k * Real.cos (lam * (x j - x k)) =
      (∑ j, c j * Real.cos (lam * x j)) ^ 2 + (∑ j, c j * Real.sin (lam * x j)) ^ 2 := by
  simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib, mul_sub, Real.cos_sub]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Nonnegative summable weights give an even positive-definite cosine trace. -/
theorem isEvenPosDef_cosineTrace {ι : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (lam : ι → ℝ) : IsEvenPosDef (cosineTrace w lam) where
  even u := cosineTrace_neg w lam u
  posDef n x c := by
    have hall : HasSum
        (fun i => ∑ j, ∑ k, c j * c k * (w i * Real.cos (lam i * (x j - x k))))
        (∑ j, ∑ k, c j * c k * cosineTrace w lam (x j - x k)) :=
      hasSum_sum fun j _ => hasSum_sum fun k _ =>
        ((summable_cosineTrace_terms hw hs lam (x j - x k)).hasSum).mul_left _
    refine hall.nonneg fun i => ?_
    have h : ∑ j, ∑ k, c j * c k * (w i * Real.cos (lam i * (x j - x k))) =
        w i * ∑ j, ∑ k, c j * c k * Real.cos (lam i * (x j - x k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h, gram_cos_eq]
    exact mul_nonneg (hw i) (by positivity)

/-- A boundary datum: damped nonnegative weights on fixed frequencies whose normalized cosine
traces converge, as the damping `x` tends to `0⁺`, to the boundary divisor `D`. -/
structure IsBoundaryDivisor {ι : Type*} (lam : ι → ℝ) (w : ℝ → ι → ℝ) (D : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 < x → ∀ i, 0 ≤ w x i
  summable : ∀ x, 0 < x → Summable (w x)
  tendsto : ∀ u, Tendsto (fun x => x * cosineTrace (w x) lam u) (𝓝[>] 0) (𝓝 (D u))

/-- **Boundary positivity theorem.** Every boundary divisor of nonnegative weights is an even
positive-definite function on `ℝ`. -/
theorem IsBoundaryDivisor.isEvenPosDef {ι : Type*} {lam : ι → ℝ} {w : ℝ → ι → ℝ}
    {D : ℝ → ℝ} (hD : IsBoundaryDivisor lam w D) : IsEvenPosDef D :=
  isEvenPosDef_of_tendsto (l := 𝓝[>] (0 : ℝ)) (F := fun x u => x * cosineTrace (w x) lam u)
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (isEvenPosDef_cosineTrace (hD.nonneg x hx) (hD.summable x hx) lam).smul
        (le_of_lt hx))
    hD.tendsto

end GaloisForLFunctions.MultiplicativePositivityGeometry
