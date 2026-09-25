import GaloisForLFunctions.RHTower.FreeOrbitCountBound

/-!
# Bounding the local integers, and what any bound must look like

The single remaining object is `Σ_t #(free orbits in the slice at t)`. A bound on it is the
hypothesis, so nothing here proves one. What is proved is the shape any bound must have, and that
shape is restrictive enough to be worth stating as a law.

**An unconditional bound exists.** The potential dominates the free-orbit count of a slice, and the
potential is dominated termwise by twice a fixed Cauchy weight, so

  `#(free orbits at t) ≤ Σ_ρ 1/(1 + (t − Im ρ)²)`,

the Cauchy-weighted local zero density. This is unconditional and it is the natural estimate: the
right-hand side is the standard local counting weight for the divisor, of size a constant times the
logarithm of the height.

**Every bound must be an absolute constant.** The free-orbit count is an *integer*, and the potential
dominates twice it, so a bound `U(t) < 2` forces the count to be zero, while a bound `U(t) ≤ B` with
`B ≥ 2` forces nothing at all. The threshold is exactly two and there is no slack in it. So the
required estimate is uniform in the height, an absolute constant, whereas the natural estimate and
every analytic estimate in this field grow with the height. That is the difficulty in its final form:
**not that the available bounds are weak, but that they have the wrong dependence on the height, and
the target admits no lossy version.** An estimate losing any constant factor, or any factor of the
logarithm, is not a partial result here — it is no result.

This also explains the shape of the quantisation: the target being an integer is what removes the
slack. Against a real-valued target a bound within a constant factor would be progress; against an
integer the only useful bound is one that crosses the threshold, and the threshold is fixed.
-/

namespace RHTower

noncomputable section

/-- The potential is dominated by twice the Cauchy-weighted local zero density. -/
theorem poissonPotential_le_cauchyWeight (t : ℝ) :
    poissonPotential t
      ≤ 2 * ∑' ρ : XiDivisorSupport, (1 : ℝ) / (1 + (t - (ρ : ℂ).im) ^ (2 : ℕ)) := by
  have h := Summable.tsum_le_tsum (poissonBumpTerm_le t) (summable_poissonBumpTerm t)
    ((summable_supportWeight t).mul_left 2)
  rw [tsum_mul_left] at h
  exact h

/-- **The unconditional bound on a local integer**: the free-orbit count of a slice is at most the
Cauchy-weighted local zero density. -/
theorem ncard_xiSliceLeft_le_cauchyWeight (t : ℝ) :
    ((xiSliceLeft t).ncard : ℝ)
      ≤ ∑' ρ : XiDivisorSupport, (1 : ℝ) / (1 + (t - (ρ : ℂ).im) ^ (2 : ℕ)) := by
  have h1 := ncard_xiSliceOffLine_le_poissonPotential t
  rw [ncard_xiSliceOffLine] at h1
  have h2 := poissonPotential_le_cauchyWeight t
  push_cast at h1
  linarith

/-- The window form. -/
theorem sum_ncard_xiSliceLeft_le_cauchyWeight (S : Finset ℝ) :
    ((∑ t ∈ S, (xiSliceLeft t).ncard : ℕ) : ℝ)
      ≤ ∑ t ∈ S, ∑' ρ : XiDivisorSupport, (1 : ℝ) / (1 + (t - (ρ : ℂ).im) ^ (2 : ℕ)) := by
  push_cast
  exact Finset.sum_le_sum fun t _ => ncard_xiSliceLeft_le_cauchyWeight t

/-- **No lossy bound is of any use.** Crossing the threshold two kills the local integer outright;
failing to cross it gives nothing, because the integer is an integer. -/
theorem xiSliceLeft_eq_empty_of_poissonPotential_lt_two {t : ℝ} (h : poissonPotential t < 2) :
    xiSliceLeft t = ∅ := by
  refine (Set.ncard_eq_zero (xiSliceLeft_finite t)).mp ?_
  by_contra hc
  have hpos : 0 < (xiSliceLeft t).ncard := Nat.pos_of_ne_zero hc
  have h1 := ncard_xiSliceOffLine_le_poissonPotential t
  rw [ncard_xiSliceOffLine] at h1
  have hge : (2 : ℝ) ≤ ((2 * (xiSliceLeft t).ncard : ℕ) : ℝ) := by
    have h1' : (1 : ℝ) ≤ ((xiSliceLeft t).ncard : ℝ) := by exact_mod_cast hpos
    push_cast
    linarith
  linarith

/-- **The threshold is the whole content.** The hypothesis is equivalent to crossing it at every
ordinate, and the quantity crossed is an absolute constant, uniform in the height. -/
theorem riemannHypothesis_iff_forall_poissonPotential_lt_two' :
    RiemannHypothesis ↔ ∀ t : ℝ, poissonPotential t < 2 := by
  constructor
  · intro h t
    rw [poissonPotential_eq_zero_of_riemannHypothesis h t]
    norm_num
  · intro h
    exact riemannHypothesis_iff_xiSliceLeft_empty.mpr fun t =>
      xiSliceLeft_eq_empty_of_poissonPotential_lt_two (h t)

end

end RHTower
