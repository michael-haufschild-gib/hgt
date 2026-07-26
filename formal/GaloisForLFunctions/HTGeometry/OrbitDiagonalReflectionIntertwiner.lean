import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Orbit-diagonal intertwiners of a reflection-graded clock

A *pointed reflection orbit* is a one-parameter family `U` acting on a Hilbert space together with
a linear reflection `J` fixing a base point `ξ` and reversing the parameter,

```text
J ξ = ξ ,        J (U h ξ) = U (-h) ξ .
```

A source clock graded by a sign character `m` (`m² = 1`) sends the positive sector basis vector to
`m` times the negative one and back.  A **basis-diagonal orbit synthesis**

```text
W e⁺ = a • U t ξ ,        W e⁻ = b • U (-t) ξ
```

intertwines the graded clock with the reflection exactly when

```text
a = m · b ,
```

so the intertwiner is forced to consume the character.  Consequently the character cancels from
every descended coefficient: both the even and the odd orbit sums carry the character-free weight
`c · b`, where `c` is the ungraded source weight.  This is `orbitDiagonal_descended_coefficients`.

No positivity, unitarity or continuity of `U` is used: only `J` linear with the two displayed
relations, and `U t ξ ≠ 0`.
-/

namespace HTGeometry

section Intertwiner

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Forced sign erasure.**  A basis-diagonal orbit synthesis intertwines a sign-graded clock with
the reflection on both sectors precisely when its two coefficients differ by the character. -/
theorem orbitDiagonal_intertwines_iff
    (U : ℝ → K →L[ℂ] K) (J : K →L[ℂ] K) (xi : K)
    (hJU : ∀ h : ℝ, J (U h xi) = U (-h) xi)
    (hne : ∀ h : ℝ, U h xi ≠ 0)
    (m a b : ℂ) (hm : m ^ 2 = 1) (t : ℝ) :
    (J (a • U t xi) = (m * b) • U (-t) xi ∧
        J (b • U (-t) xi) = (m * a) • U t xi) ↔ a = m * b := by
  have hJneg : J (U (-t) xi) = U t xi := by
    have h := hJU (-t)
    rwa [neg_neg] at h
  constructor
  · rintro ⟨hplus, -⟩
    rw [map_smul, hJU t] at hplus
    have hsub : (a - m * b) • U (-t) xi = 0 := by
      rw [sub_smul, hplus, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · linear_combination (norm := ring_nf) h
    · exact absurd h (hne (-t))
  · intro hab
    have hba : b = m * a := by
      rw [hab, ← mul_assoc]
      rw [show m * m = m ^ 2 by ring, hm, one_mul]
    constructor
    · rw [map_smul, hJU t, hab]
    · rw [map_smul, hJneg, hba]

/-- **Character cancellation.**  Under the forced relation `a = m·b` both descended orbit
coefficients of a character-graded source weight `m·c` are the character-free weight `c·b`. -/
theorem orbitDiagonal_descended_coefficients (m c b : ℂ) (hm : m ^ 2 = 1) :
    (m * c) * (m * b) = c * b ∧ (m * (m * c)) * b = c * b := by
  have hmm : m * m = 1 := by
    rw [show m * m = m ^ 2 by ring, hm]
  constructor
  · calc (m * c) * (m * b) = (m * m) * (c * b) := by ring
      _ = c * b := by rw [hmm, one_mul]
  · calc (m * (m * c)) * b = (m * m) * (c * b) := by ring
      _ = c * b := by rw [hmm, one_mul]

end Intertwiner


section Divergence

variable {ι : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Block covariance bound.**  A nonnegatively weighted finite block whose pairwise covariances
are all at least `γ` has energy at least `γ` times the square of its total weight. -/
theorem mul_sq_sum_le_norm_sq_sum {B : Finset ι} {v : ι → K} {w : ι → ℝ} {γ : ℝ}
    (hw : ∀ i ∈ B, 0 ≤ w i)
    (hcov : ∀ i ∈ B, ∀ j ∈ B, γ ≤ (inner ℂ (v i) (v j)).re) :
    γ * (∑ i ∈ B, w i) ^ 2 ≤ ‖∑ i ∈ B, (w i : ℂ) • v i‖ ^ 2 := by
  have hexpand : (inner ℂ (∑ i ∈ B, (w i : ℂ) • v i) (∑ j ∈ B, (w j : ℂ) • v j) : ℂ)
      = ∑ i ∈ B, ∑ j ∈ B, ((w i : ℂ) * (w j : ℂ)) * inner ℂ (v i) (v j) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  have hre : ‖∑ i ∈ B, (w i : ℂ) • v i‖ ^ 2
      = ∑ i ∈ B, ∑ j ∈ B, w i * w j * (inner ℂ (v i) (v j)).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (∑ i ∈ B, (w i : ℂ) • v i)]
    rw [show (RCLike.re (inner ℂ (∑ i ∈ B, (w i : ℂ) • v i) (∑ j ∈ B, (w j : ℂ) • v j)))
        = (inner ℂ (∑ i ∈ B, (w i : ℂ) • v i) (∑ j ∈ B, (w j : ℂ) • v j) : ℂ).re from rfl]
    rw [hexpand, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re]
  rw [hre]
  have hlhs : γ * (∑ i ∈ B, w i) ^ 2 = ∑ i ∈ B, ∑ j ∈ B, γ * (w i * w j) := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hlhs]
  refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
  have hij : 0 ≤ w i * w j := mul_nonneg (hw i hi) (hw j hj)
  nlinarith [hcov i hi j hj]

omit [InnerProductSpace ℂ K] in
/-- **Cofinal block no-go.**  A family admitting arbitrarily late finite blocks of energy at least
`γ > 0` is not summable: the orbit synthesis leaves the Hilbert domain. -/
theorem not_summable_of_cofinal_blocks {f : ι → K} {γ : ℝ} (hγ : 0 < γ)
    (h : ∀ s : Finset ι, ∃ B : Finset ι, Disjoint B s ∧ γ ≤ ‖∑ i ∈ B, f i‖) :
    ¬ Summable f := by
  intro hsum
  obtain ⟨s, hs⟩ := hsum.vanishing (Metric.ball_mem_nhds (0 : K) hγ)
  obtain ⟨B, hdisj, hB⟩ := h s
  have hmem := hs B hdisj
  rw [Metric.mem_ball, dist_zero_right] at hmem
  linarith

end Divergence

end HTGeometry
