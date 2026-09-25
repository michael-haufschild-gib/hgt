import GaloisForLFunctions.RHTower.DivisorTateCohomology
import GaloisForLFunctions.RHTower.ClockDegeneracy

/-!
# The boundary map: its image, and what its rank counts

Cohomology discards the free orbits, so the object to control is the boundary map itself. This module
describes it completely and identifies what its rank measures.

**The image is exactly characterised.** A cochain is a coboundary if and only if it is invariant
under the reflection and vanishes on the critical line. One direction is immediate; the other is the
canonical section by the left half of the strip. So

  `im N = { f : f∘σ = f and f|_{critical line} = 0 }`,

a completely explicit subspace, with no quotient taken anywhere. In particular `im N = 0` is the
hypothesis, and the free orbits are a basis: over `𝔽₂` a cochain in the image is freely determined by
its values on the left half-slices, one bit per free orbit.

**The rank is fibrewise, and it is the classical deficiency.** The reflection preserves ordinates, so
the boundary map is fibred over the ordinate map and its rank is the sum over ordinates of the
free-orbit count of each slice. Each slice splits as one point of the critical line, at most, plus
free orbits in pairs, so over any finite set of ordinates

  `(total zero count) = (critical-line count) + 2·(free-orbit count)`.

That is the classical relation between all zeros and the zeros on the line, in exact finite form, and
the hypothesis is precisely that the two counts agree on every window. So the lane developed here and
the classical count of critical-line zeros decide the *same* integer; what differs is that the
classical tools reach it through averages, which the scaling degree law shows cannot work, while the
boundary map reaches it fibrewise, one ordinate at a time.

The rank is therefore the target, it is a sum of local integers, and it is the classical deficiency.
Nothing here bounds it; what is established is that the object is now completely explicit and that no
quotient is hiding it.
-/

namespace RHTower

noncomputable section

/-- A coboundary is reflection-invariant. -/
theorem divisorNorm_invariant (g : XiDivisorSupport → ZMod 2) (ρ : XiDivisorSupport) :
    divisorNorm g (supportPartner ρ) = divisorNorm g ρ := by
  rw [divisorNorm, divisorNorm, supportPartner_involutive ρ]
  exact add_comm _ _

/-- **The image of the boundary map, exactly.** A cochain is a coboundary precisely when it is
reflection-invariant and vanishes on the critical line. -/
theorem mem_range_divisorNorm_iff (f : XiDivisorSupport → ZMod 2) :
    (∃ g, divisorNorm g = f)
      ↔ ((∀ ρ : XiDivisorSupport, f (supportPartner ρ) = f ρ)
          ∧ ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2 → f ρ = 0) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨divisorNorm_invariant g, fun ρ h => divisorNorm_eq_zero_of_fixed g h⟩
  · rintro ⟨hinv, hfix⟩
    exact ⟨leftSection f, divisorNorm_leftSection hinv hfix⟩

/-- **The rank is fibrewise.** Over any finite set of ordinates the total zero count splits as the
critical-line count plus twice the free-orbit count. -/
theorem sum_ncard_xiSlice (S : Finset ℝ) :
    ∑ t ∈ S, (xiSlice t).ncard
      = ∑ t ∈ S, (xiSliceFixed t).ncard + 2 * ∑ t ∈ S, (xiSliceLeft t).ncard := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => ncard_xiSlice t

/-- **The hypothesis is the vanishing of the deficiency on every window.** This is the classical
relation between all zeros and the zeros on the critical line, in exact finite form. -/
theorem riemannHypothesis_iff_window_counts_agree :
    RiemannHypothesis ↔ ∀ S : Finset ℝ,
      ∑ t ∈ S, (xiSlice t).ncard = ∑ t ∈ S, (xiSliceFixed t).ncard := by
  constructor
  · intro h S
    rw [sum_ncard_xiSlice S]
    have hzero : ∀ t ∈ S, (xiSliceLeft t).ncard = 0 := fun t _ =>
      (Set.ncard_eq_zero (xiSliceLeft_finite t)).mpr
        (riemannHypothesis_iff_xiSliceLeft_empty.mp h t)
    rw [Finset.sum_congr rfl hzero]
    simp
  · intro h
    refine riemannHypothesis_iff_xiSliceLeft_empty.mpr fun t => ?_
    refine (Set.ncard_eq_zero (xiSliceLeft_finite t)).mp ?_
    have hS := h {t}
    rw [sum_ncard_xiSlice {t}] at hS
    simp only [Finset.sum_singleton] at hS
    omega

/-- **One bit per free orbit.** A coboundary is determined by its values on the left half of the
strip, and those values are unconstrained. -/
theorem divisorNorm_leftSection_of_mem_range {f : XiDivisorSupport → ZMod 2}
    (h : ∃ g, divisorNorm g = f) : divisorNorm (leftSection f) = f := by
  obtain ⟨hinv, hfix⟩ := (mem_range_divisorNorm_iff f).mp h
  exact divisorNorm_leftSection hinv hfix

end

end RHTower
