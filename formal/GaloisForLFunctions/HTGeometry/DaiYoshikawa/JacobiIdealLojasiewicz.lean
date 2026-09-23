import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The Łojasiewicz bound at an isolated critical point

Lemma 6.2 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), turns the algebraic fact that the Jacobi ideal of an isolated
critical point contains a power of the maximal ideal into the analytic bound

```text
‖df(ζ)‖² ≥ K₀ ‖ζ‖^{2ν} .
```

The analytic content is one application of Cauchy–Schwarz to the algebraic relation
`ζᵢ^ν = Σⱼ gᵢⱼ ∂f/∂ζⱼ`, followed by the elementary comparison between the `ν`-th power of a sum and
the sum of `ν`-th powers.  Both steps are proved here, for an arbitrary finite number of
coordinates; the input is the relation itself, which is where the algebra of the Jacobi ideal
enters.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Cauchy–Schwarz for the Jacobi relation.**

If `z i = Σⱼ G i j · d j`, then `Σᵢ ‖z i‖² ≤ (Σᵢⱼ ‖G i j‖²)(Σⱼ ‖d j‖²)`. -/
theorem sum_normSq_le_of_eq_sum_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ] {z : ι → 𝕜} {G : ι → κ → 𝕜} {d : κ → 𝕜}
    (hz : ∀ i, z i = ∑ j, G i j * d j) :
    (∑ i, ‖z i‖ ^ (2 : ℕ)) ≤ (∑ i, ∑ j, ‖G i j‖ ^ (2 : ℕ)) * ∑ j, ‖d j‖ ^ (2 : ℕ) := by
  have hrow : ∀ i, ‖z i‖ ^ (2 : ℕ) ≤ (∑ j, ‖G i j‖ ^ (2 : ℕ)) * ∑ j, ‖d j‖ ^ (2 : ℕ) := by
    intro i
    have hnorm : ‖z i‖ ≤ ∑ j, ‖G i j‖ * ‖d j‖ := by
      rw [hz i]
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    have hCS : (∑ j, ‖G i j‖ * ‖d j‖) ^ (2 : ℕ)
        ≤ (∑ j, ‖G i j‖ ^ (2 : ℕ)) * ∑ j, ‖d j‖ ^ (2 : ℕ) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    refine le_trans ?_ hCS
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc (∑ i, ‖z i‖ ^ (2 : ℕ)) ≤ ∑ i, (∑ j, ‖G i j‖ ^ (2 : ℕ)) * ∑ j, ‖d j‖ ^ (2 : ℕ) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, ∑ j, ‖G i j‖ ^ (2 : ℕ)) * ∑ j, ‖d j‖ ^ (2 : ℕ) := by rw [← Finset.sum_mul]

/-- **The power of a sum against the sum of powers.**

For nonnegative `a` over a nonempty finite index set, `(Σ a i)^ν ≤ (card)^ν Σ (a i)^ν`. -/
theorem pow_sum_le_card_pow_mul_sum_pow
    {ι : Type*} [Fintype ι] [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ν : ℕ) :
    (∑ i, a i) ^ ν ≤ (Fintype.card ι : ℝ) ^ ν * ∑ i, (a i) ^ ν := by
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) a ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hsum : (∑ i, a i) ≤ (Fintype.card ι : ℝ) * a i₀ := by
    calc (∑ i, a i) ≤ ∑ _i : ι, a i₀ := Finset.sum_le_sum fun i _ => hmax i (Finset.mem_univ i)
      _ = (Fintype.card ι : ℝ) * a i₀ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hpow : (∑ i, a i) ^ ν ≤ ((Fintype.card ι : ℝ) * a i₀) ^ ν :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => ha i) hsum ν
  rw [mul_pow] at hpow
  refine hpow.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.single_le_sum (f := fun i => (a i) ^ ν)
    (fun i _ => pow_nonneg (ha i) ν) (Finset.mem_univ i₀)

/-- **Lemma 6.2 of Dai–Yoshikawa.**

If the coordinates satisfy the Jacobi relation `ζᵢ^ν = Σⱼ Gᵢⱼ · dⱼ` with `Σᵢⱼ ‖Gᵢⱼ‖² ≤ M`, then the
norm of the differential dominates a power of the norm of the coordinates:

```text
(Σᵢ ‖ζᵢ‖²)^ν ≤ (card)^ν · M · Σⱼ ‖dⱼ‖² .
```
-/
theorem pow_sum_normSq_le_of_jacobi_relation
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    {ζ : ι → 𝕜} {G : ι → κ → 𝕜} {d : κ → 𝕜} {M : ℝ} {ν : ℕ}
    (hrel : ∀ i, ζ i ^ ν = ∑ j, G i j * d j)
    (hM : (∑ i, ∑ j, ‖G i j‖ ^ (2 : ℕ)) ≤ M) :
    (∑ i, ‖ζ i‖ ^ (2 : ℕ)) ^ ν ≤ (Fintype.card ι : ℝ) ^ ν * (M * ∑ j, ‖d j‖ ^ (2 : ℕ)) := by
  have hstep := sum_normSq_le_of_eq_sum_mul (z := fun i => ζ i ^ ν) (G := G) (d := d) hrel
  have hnorm : ∀ i, ‖ζ i ^ ν‖ ^ (2 : ℕ) = (‖ζ i‖ ^ (2 : ℕ)) ^ ν := by
    intro i
    rw [norm_pow]
    ring
  simp only [hnorm] at hstep
  have hpm := pow_sum_le_card_pow_mul_sum_pow (a := fun i => ‖ζ i‖ ^ (2 : ℕ))
    (fun i => by positivity) ν
  refine hpm.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine hstep.trans ?_
  exact mul_le_mul_of_nonneg_right hM (Finset.sum_nonneg fun j _ => by positivity)

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
