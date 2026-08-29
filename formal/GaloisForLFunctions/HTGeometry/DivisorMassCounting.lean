import GaloisForLFunctions.HTGeometry.NevanlinnaTranslationCharacteristic

/-!
# The total divisor mass is controlled by the counting functions

The mass `∑_u |n_u|` of the divisor of a meromorphic function in the disc of radius `R` splits into
its zero part and its pole part.  Each is a `poleMultiplicityMass` — the pole part of `f` and the
pole part of `f⁻¹` — so the corpus estimate

```text
log 2 · poleMultiplicityMass f R ≤ N(2R, f)
```

applied to `f` and to `f⁻¹` bounds the whole mass by `N(2R,f) + N(2R,1/f)`.

Together with `|n|^α ≤ |n|` for `0 < α ≤ 1` and integer `n`, this converts the divisor weight in the
logarithmic-derivative estimate into a counting function, which the first main theorem then compares
with the characteristic.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real ValueDistribution MeromorphicOn

/-- A power `α ≤ 1` of the absolute value of an integer does not exceed it. -/
theorem rpow_abs_intCast_le {n : ℤ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ((|n| : ℤ) : ℝ) ^ α ≤ ((|n| : ℤ) : ℝ) := by
  rcases eq_or_lt_of_le (abs_nonneg n) with h | h
  · have hzero : ((|n| : ℤ) : ℝ) = 0 := by
      rw [← h]
      norm_num
    rw [hzero, Real.zero_rpow (ne_of_gt hα0)]
  · have hone : (1 : ℝ) ≤ ((|n| : ℤ) : ℝ) := by
      have : (1 : ℤ) ≤ |n| := h
      exact_mod_cast this
    calc ((|n| : ℤ) : ℝ) ^ α ≤ ((|n| : ℤ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hone hα1
      _ = ((|n| : ℤ) : ℝ) := Real.rpow_one _

/-- **The divisor mass splits into the two pole masses.** -/
theorem divisorMass_eq_add {f : ℂ → ℂ} {R : ℝ} :
    (∑ᶠ u : ℂ, |((divisor f (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)|)
      = poleMultiplicityMass f R + poleMultiplicityMass f⁻¹ R := by
  classical
  have hpt : ∀ u : ℂ, |((divisor f (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)|
      = ((divisor f (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)⁻
        + ((divisor f⁻¹ (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)⁻ := by
    intro u
    have hinv : (divisor f⁻¹ (closedBall (0 : ℂ) |R|)) u
        = -(divisor f (closedBall (0 : ℂ) |R|) u) := by
      rw [MeromorphicOn.divisor_inv]
      rfl
    rw [hinv]
    push_cast
    rw [negPart_neg, add_comm]
    exact (posPart_add_negPart _).symm
  have h1 : Function.HasFiniteSupport
      (fun u : ℂ => ((divisor f (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)⁻) := by
    have hfin := (divisor f (closedBall (0 : ℂ) |R|)).finiteSupport
      (isCompact_closedBall (0 : ℂ) |R|)
    refine hfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hzero
    apply hu
    rw [hzero]
    simp
  have h2 : Function.HasFiniteSupport
      (fun u : ℂ => ((divisor f⁻¹ (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)⁻) := by
    have hfin := (divisor f⁻¹ (closedBall (0 : ℂ) |R|)).finiteSupport
      (isCompact_closedBall (0 : ℂ) |R|)
    refine hfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hzero
    apply hu
    rw [hzero]
    simp
  rw [poleMultiplicityMass, poleMultiplicityMass, ← finsum_add_distrib h1 h2]
  exact finsum_congr hpt

/-- **The counting bridge.**  The total divisor mass in the disc of radius `R` is controlled by the
zero- and pole-counting functions at twice the radius. -/
theorem log_two_mul_divisorMass_le_logCounting {f : ℂ → ℂ} (hf : Meromorphic f) {R : ℝ}
    (hR : 1 ≤ R) :
    Real.log 2 * (∑ᶠ u : ℂ, |((divisor f (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)|)
      ≤ logCounting f ⊤ (2 * R) + logCounting f 0 (2 * R) := by
  have hinv : Meromorphic f⁻¹ := fun z => (hf z).inv
  have h₁ := log_two_mul_poleMultiplicityMass_le_logCounting hf hR
  have h₂ := log_two_mul_poleMultiplicityMass_le_logCounting hinv hR
  rw [ValueDistribution.logCounting_inv] at h₂
  rw [divisorMass_eq_add, mul_add]
  linarith

/-- **The `α`-power divisor weight is at most the divisor mass.** -/
theorem divisorMass_rpow_le {f : ℂ → ℂ} {R α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ᶠ u : ℂ, (|(divisor f (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α)
      ≤ ∑ᶠ u : ℂ, |((divisor f (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)| := by
  classical
  set D : ℂ → ℤ := fun u => divisor f (closedBall (0 : ℂ) |R|) u with hD
  have hfin : (Function.support D).Finite :=
    (divisor f (closedBall (0 : ℂ) |R|)).finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  have hsub₁ : Function.support (fun u => (|D u| : ℝ) ^ α) ⊆ hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hzero
    apply hu
    rw [hzero]
    simp [Real.zero_rpow (ne_of_gt hα0)]
  have hsub₂ : Function.support (fun u => |((D u : ℤ) : ℝ)|) ⊆ hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hzero
    apply hu
    rw [hzero]
    simp
  rw [finsum_eq_sum_of_support_subset _ hsub₁, finsum_eq_sum_of_support_subset _ hsub₂]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← Int.cast_abs]
  exact rpow_abs_intCast_le hα0 hα1

end GaloisForLFunctions.HTGeometry
