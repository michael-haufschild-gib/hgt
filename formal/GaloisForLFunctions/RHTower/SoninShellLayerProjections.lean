import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# The layers of a cutoff tower are orthogonal projections

The difference of two nested physical cutoffs is the projection onto the shell between them.  Two
such shells that do not overlap annihilate each other, so the layers of a tower of increasing radii
form an orthogonal family whose partial sums telescope to the difference of the extreme cutoffs.

This is the decomposition every estimate on a step multiplier along the tower needs: it turns the
operator into an orthogonal sum with one scalar per layer.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- The shell projection between two physical radii. -/
def evenIndicatorLayer (s t : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  evenIndicatorCutoff t - evenIndicatorCutoff s

@[simp] theorem evenIndicatorLayer_self (s : ℝ) : evenIndicatorLayer s s = 0 := by
  rw [evenIndicatorLayer, sub_self]

theorem adjoint_evenIndicatorLayer (s t : ℝ) :
    ContinuousLinearMap.adjoint (evenIndicatorLayer s t) = evenIndicatorLayer s t := by
  rw [evenIndicatorLayer, ContinuousLinearMap.adjoint.map_sub, adjoint_evenIndicatorCutoff,
    adjoint_evenIndicatorCutoff]

/-- **Disjoint shells annihilate.**  A shell below a radius and a shell above it multiply to
zero. -/
theorem evenIndicatorLayer_mul_of_le {s t u v : ℝ} (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    evenIndicatorLayer s t * evenIndicatorLayer u v = 0 := by
  have h₁ : evenIndicatorCutoff t * evenIndicatorCutoff v = evenIndicatorCutoff t :=
    evenIndicatorCutoff_mul_of_le t v (htu.trans huv)
  have h₂ : evenIndicatorCutoff t * evenIndicatorCutoff u = evenIndicatorCutoff t :=
    evenIndicatorCutoff_mul_of_le t u htu
  have h₃ : evenIndicatorCutoff s * evenIndicatorCutoff v = evenIndicatorCutoff s :=
    evenIndicatorCutoff_mul_of_le s v (hst.trans (htu.trans huv))
  have h₄ : evenIndicatorCutoff s * evenIndicatorCutoff u = evenIndicatorCutoff s :=
    evenIndicatorCutoff_mul_of_le s u (hst.trans htu)
  rw [evenIndicatorLayer, evenIndicatorLayer, sub_mul, mul_sub, mul_sub, h₁, h₂, h₃, h₄,
    sub_self, sub_self, sub_zero]

/-- The reversed product of two disjoint shells also vanishes. -/
theorem evenIndicatorLayer_mul_of_le' {s t u v : ℝ} (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    evenIndicatorLayer u v * evenIndicatorLayer s t = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint (evenIndicatorLayer_mul_of_le hst htu huv)
  change ContinuousLinearMap.adjoint
      (evenIndicatorLayer s t ∘L evenIndicatorLayer u v) =
    ContinuousLinearMap.adjoint (0 : evenSubspace →L[ℂ] evenSubspace) at h
  rw [ContinuousLinearMap.adjoint_comp, adjoint_evenIndicatorLayer,
    adjoint_evenIndicatorLayer, ContinuousLinearMap.adjoint.map_zero] at h
  exact h

/-- **Orthogonality of disjoint shells.**  Their images pair to zero. -/
theorem inner_evenIndicatorLayer_apply_eq_zero {s t u v : ℝ} (hst : s ≤ t) (htu : t ≤ u)
    (huv : u ≤ v) (x y : evenSubspace) :
    ⟪evenIndicatorLayer s t x, evenIndicatorLayer u v y⟫_ℂ = 0 := by
  have hzero : evenIndicatorLayer u v (evenIndicatorLayer s t x) = 0 := by
    have hprod := DFunLike.congr_fun (evenIndicatorLayer_mul_of_le' hst htu huv) x
    simpa using hprod
  have h := ContinuousLinearMap.adjoint_inner_right (evenIndicatorLayer u v)
    (evenIndicatorLayer s t x) y
  rw [adjoint_evenIndicatorLayer] at h
  rw [h, hzero, inner_zero_left]

/-- **Telescoping.**  The layers of a tower sum to the difference of the extreme cutoffs. -/
theorem sum_evenIndicatorLayer (ρ : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, evenIndicatorLayer (ρ k) (ρ (k + 1)) =
      evenIndicatorCutoff (ρ n) - evenIndicatorCutoff (ρ 0) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, evenIndicatorLayer]
      abel

/-- A shell of the tower is idempotent when the radii increase. -/
theorem evenIndicatorLayer_mul_self {s t : ℝ} (hst : s ≤ t) :
    evenIndicatorLayer s t * evenIndicatorLayer s t = evenIndicatorLayer s t := by
  have hss : evenIndicatorCutoff s * evenIndicatorCutoff s = evenIndicatorCutoff s :=
    evenIndicatorCutoff_mul_of_le s s le_rfl
  have htt : evenIndicatorCutoff t * evenIndicatorCutoff t = evenIndicatorCutoff t :=
    evenIndicatorCutoff_mul_of_le t t le_rfl
  have hst' : evenIndicatorCutoff s * evenIndicatorCutoff t = evenIndicatorCutoff s :=
    evenIndicatorCutoff_mul_of_le s t hst
  have hts : evenIndicatorCutoff t * evenIndicatorCutoff s = evenIndicatorCutoff s :=
    evenIndicatorCutoff_mul_of_le_rev s t hst
  rw [evenIndicatorLayer, sub_mul, mul_sub, mul_sub, htt, hts, hst', hss]
  abel

end RHTower
