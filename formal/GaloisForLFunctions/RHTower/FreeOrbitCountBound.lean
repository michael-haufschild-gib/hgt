import GaloisForLFunctions.RHTower.CriticalLinePoissonPotential
import GaloisForLFunctions.RHTower.ClockDegeneracy

/-!
# The free-orbit count bounds the potential

The scaling degree law says the hypothesis is decided only by degree-zero functionals, and that the
degree-zero class contains an integer-valued member: the count. An integer-valued invariant is a
qualitative object, not a measurement, and it is not produced by any limit of measurements — which is
the exact content of the blindness results in this lane.

This module supplies the conversion **inside** the degree-zero class, between the two ends that were
developed separately here: the count of free orbits of the functional-equation involution on a slice,
and the analytic potential on the critical line.

At the ordinate `t` every off-line zero of that ordinate sits directly above or below the base point,
so its bump is at full height and contributes exactly `1`. The free orbits of the slice therefore
count themselves inside the potential:

  `#(free part of the slice at t) ≤ U(t)`,

and the free part has even cardinality, twice the left half-slice, because the involution exchanges
the halves. So a single free orbit already forces `U(t) ≥ 2`, recovering the threshold from the
count rather than from the pair.

The reading is that the potential is not measuring a quantity that happens to detect zeros; it is
dominating a count. The hypothesis is the vanishing of that count at every ordinate, and the count is
the number of free orbits of an involution — a property of the symmetry acting on the divisor, not of
any analytic size. The analysis enters only to bound the count from above, which is the one direction
the degree law leaves open.
-/

namespace RHTower

noncomputable section

/-- The free part of a slice: the off-line divisor points at a given ordinate. -/
def xiSliceOffLine (t : ℝ) : Set XiDivisorSupport := xiSliceLeft t ∪ xiSliceRight t

theorem xiSliceOffLine_finite (t : ℝ) : (xiSliceOffLine t).Finite :=
  (xiSliceLeft_finite t).union (xiSliceRight_finite t)

theorem disjoint_xiSliceLeft_xiSliceRight (t : ℝ) :
    Disjoint (xiSliceLeft t) (xiSliceRight t) := by
  rw [Set.disjoint_left]
  intro ρ hL hR
  exact absurd hR.2 (not_lt.mpr (le_of_lt hL.2))

/-- **The free part of a slice has even cardinality**, twice the left half: the involution exchanges
the two halves. -/
theorem ncard_xiSliceOffLine (t : ℝ) :
    (xiSliceOffLine t).ncard = 2 * (xiSliceLeft t).ncard := by
  rw [xiSliceOffLine, Set.ncard_union_eq (disjoint_xiSliceLeft_xiSliceRight t)
    (xiSliceLeft_finite t) (xiSliceRight_finite t), ncard_xiSliceRight]
  ring

/-- An off-line point of the slice sits directly above or below the base point, so its bump is at
full height. -/
theorem poissonBumpTerm_eq_one_of_mem_xiSliceOffLine {t : ℝ} {ρ : XiDivisorSupport}
    (h : ρ ∈ xiSliceOffLine t) : poissonBumpTerm t ρ = 1 := by
  have him : (ρ : ℂ).im = t := by
    rcases h with hL | hR
    · exact hL.1
    · exact hR.1
  have hre : (ρ : ℂ).re ≠ 1 / 2 := by
    rcases h with hL | hR
    · exact ne_of_lt hL.2
    · exact ne_of_gt hR.2
  have hb := poissonBumpTerm_self hre
  rwa [him] at hb

/-- **The potential dominates the free-orbit count.** -/
theorem ncard_xiSliceOffLine_le_poissonPotential (t : ℝ) :
    (((xiSliceOffLine t).ncard : ℕ) : ℝ) ≤ poissonPotential t := by
  classical
  have hfin := xiSliceOffLine_finite t
  have hsum := Summable.sum_le_tsum (f := fun ρ => poissonBumpTerm t ρ)
    hfin.toFinset (fun i _ => poissonBumpTerm_nonneg t i) (summable_poissonBumpTerm t)
  have hcong : ∑ ρ ∈ hfin.toFinset, poissonBumpTerm t ρ = (hfin.toFinset.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun ρ hρ =>
      poissonBumpTerm_eq_one_of_mem_xiSliceOffLine (hfin.mem_toFinset.mp hρ)),
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcong] at hsum
  rwa [Set.ncard_eq_toFinset_card _ hfin]

/-- **One free orbit already forces the threshold**, recovered from the count rather than the pair. -/
theorem two_le_poissonPotential_of_xiSliceLeft_nonempty {t : ℝ}
    (h : (xiSliceLeft t).Nonempty) : 2 ≤ poissonPotential t := by
  have hpos : 0 < (xiSliceLeft t).ncard := (Set.ncard_pos (xiSliceLeft_finite t)).mpr h
  have hle := ncard_xiSliceOffLine_le_poissonPotential t
  rw [ncard_xiSliceOffLine] at hle
  have : (2 : ℝ) ≤ ((2 * (xiSliceLeft t).ncard : ℕ) : ℝ) := by
    have : 1 ≤ (xiSliceLeft t).ncard := hpos
    push_cast
    exact_mod_cast Nat.mul_le_mul_left 2 this
  linarith

/-- **The hypothesis is the vanishing of the free-orbit count at every ordinate.** -/
theorem riemannHypothesis_iff_forall_ncard_xiSliceOffLine_eq_zero :
    RiemannHypothesis ↔ ∀ t : ℝ, (xiSliceOffLine t).ncard = 0 := by
  constructor
  · intro h t
    rw [ncard_xiSliceOffLine,
      (Set.ncard_eq_zero (xiSliceLeft_finite t)).mpr
        (riemannHypothesis_iff_xiSliceLeft_empty.mp h t)]
  · intro h
    refine riemannHypothesis_iff_xiSliceLeft_empty.mpr fun t => ?_
    refine (Set.ncard_eq_zero (xiSliceLeft_finite t)).mp ?_
    have := h t
    rw [ncard_xiSliceOffLine] at this
    omega

end

end RHTower
