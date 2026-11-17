import GaloisForLFunctions.GaloisTheoryOfZeros.ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit

/-!
# A proper monodromy group divides the off-line zeros into groups of eight

The forward monodromy group `G₊` of the heat flow is either the group `W` of all signed
permutations of finite support or a subgroup of index two. If it is proper, every nonreal count
`N(t)`, `t > 0`, is divisible by `8` (`eight_dvd_nonrealZeroCount`). When only finitely many zeros
of `ζ` lie off the critical line, `N(t)` equals their number (divisor copies, with multiplicity)
for all small `t > 0` (`RHTower.DeBruijn.eventually_nonrealZeroCount_eq_of_finite`).

* `eight_dvd_card_offLine_of_not_mem_forwardMonodromy`: in the finite stratum a proper `G₊` makes
  the number of off-line zeros divisible by `8`. The off-line zeros come in quartets
  `ρ, ρ̄, 1 − ρ, 1 − ρ̄`, so their number is four times the multiplicity of the zeros with
  `Re ρ > ½`, `Im ρ > 0`, and this multiplicity is even.
* `mem_forwardMonodromy_of_card_offLine_eq_four`: a single simple off-line quartet forces `G₊ = W`.
-/

open Filter Topology RHTower RHTower.DeBruijn

noncomputable section

namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- **A proper monodromy group counts the off-line zeros modulo eight.** If finitely many zeros of
`ζ` lie off the line and some signed permutation of finite support is not a forward monodromy,
the number of off-line zeros, counted with multiplicity, is divisible by `8`. -/
theorem eight_dvd_card_offLine_of_not_mem_forwardMonodromy
    (hF : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) {b : ℂ} {hb₀ : 0 < b.re}
    {hbb : b ∉ branchTimes} {w : Equiv.Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite)
    (hwG : w ∉ forwardMonodromy b hb₀ hbb) : 8 ∣ hF.toFinset.card := by
  obtain ⟨s, hs, hs0⟩ :=
    ((eventually_nonrealZeroCount_eq_of_finite hF).and eventually_mem_nhdsWithin).exists
  rw [← hs]
  exact eight_dvd_nonrealZeroCount (hb₀ := hb₀) (hbb := hbb) hw hfin hwG hs0

/-- If the number of off-line zeros is not divisible by `8`, every signed permutation of finite
support of a forward fibre is a forward monodromy. -/
theorem mem_forwardMonodromy_of_not_eight_dvd_card_offLine
    (hF : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) (h8 : ¬ 8 ∣ hF.toFinset.card)
    {b : ℂ} (hb₀ : 0 < b.re) (hbb : b ∉ branchTimes)
    {w : Equiv.Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ forwardMonodromy b hb₀ hbb := by
  by_contra hwG
  exact h8 (eight_dvd_card_offLine_of_not_mem_forwardMonodromy hF hw hfin hwG)

/-- **A single simple off-line quartet forces the full group**: if exactly four zero copies lie off
the line, `G₊ = W`. -/
theorem mem_forwardMonodromy_of_card_offLine_eq_four
    (hF : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) (h4 : hF.toFinset.card = 4)
    {b : ℂ} (hb₀ : 0 < b.re) (hbb : b ∉ branchTimes)
    {w : Equiv.Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ forwardMonodromy b hb₀ hbb :=
  mem_forwardMonodromy_of_not_eight_dvd_card_offLine hF (by rw [h4]; decide) hb₀ hbb hw hfin

end GaloisForLFunctions.GaloisTheoryOfZeros
