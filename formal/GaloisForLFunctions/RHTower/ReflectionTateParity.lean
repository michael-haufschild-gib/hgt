import GaloisForLFunctions.RHTower.WeilLagFunctionHerglotz
import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase

/-!
# The hypothesis is the triviality of a `ℤ/2`-action, not an inequality

Two involutions act on the divisor of `ξ`: the functional equation `ρ ↦ 1 − ρ`, which fixes no
zero, and the **Hermitian reflection** `ρ ↦ 1 − conj ρ`, which fixes exactly the critical line.
The second is the corpus's `lagPartner`.  This module records that

  `RiemannHypothesis ↔ ∀ q, (lagPartner q).1 = q.1`,

i.e. RH is exactly the statement that this canonical `ℤ/2`-action on the divisor is **trivial** —
that the permutation module `⊕_ρ ℤ` carries no free orbit.  Off-line zeros are precisely the free
orbits, and they come in pairs.

The invariant separating the two cases is therefore `2`-torsion: it is the class of a free orbit in
a `ℤ[ℤ/2]`-module.  The horizontal grade `a = 2 Re ρ − 1` is the reflection-**odd** coordinate, and
`ℝ` is torsion free, so the reflection's fixed locus in `ℝ` is `{0}`: every reflection-**even**
real-valued reader — every norm, energy, signature, positivity, or squared amplitude in the corpus —
takes the same value on a copy and on its partner and therefore cannot see a free orbit at all.
That is the structural reason positivity has been universally blind, and it is the same
torsion-freeness that makes the reflection kernel of the lag function fail
(`LagReflectionKernelNoGo`).
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The Hermitian reflection fixes exactly the critical line -/

/-- The Hermitian reflection is an involution on the divisor support. -/
theorem lagPartner_fst_involutive (q : XiZeroCopy) :
    ((lagPartner (lagPartner q)).1 : ℂ) = (q.1 : ℂ) := by
  rw [lagPartner_coe, lagPartner_coe, map_sub, map_one, Complex.conj_conj]
  ring

/-- **The fixed points of the Hermitian reflection are exactly the critical-line copies.** -/
theorem lagPartner_fst_eq_iff (q : XiZeroCopy) :
    ((lagPartner q).1 : ℂ) = (q.1 : ℂ) ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [lagPartner_coe]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring

/-- An off-line copy has a genuinely free reflection orbit. -/
theorem lagPartner_fst_ne_of_re_ne_half {q : XiZeroCopy} (h : (q.1 : ℂ).re ≠ 1 / 2) :
    ((lagPartner q).1 : ℂ) ≠ (q.1 : ℂ) :=
  fun he => h ((lagPartner_fst_eq_iff q).mp he)

/-- **The hypothesis is the triviality of the Hermitian `ℤ/2`-action on the divisor.** -/
theorem riemannHypothesis_iff_lagPartner_fst_eq :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, ((lagPartner q).1 : ℂ) = (q.1 : ℂ) := by
  constructor
  · intro hRH q
    exact (lagPartner_fst_eq_iff q).mpr (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
  · intro h
    exact riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase
      fun q => (lagPartner_fst_eq_iff q).mp (h q)

/-! ## The grade is reflection-odd, and `ℝ` is torsion free -/

/-- The horizontal grade `a = 2 Re ρ − 1` of a divisor copy. -/
def horizontalGrade (q : XiZeroCopy) : ℝ := 2 * (q.1 : ℂ).re - 1

/-- **The grade is reflection-odd.** -/
theorem horizontalGrade_lagPartner (q : XiZeroCopy) :
    horizontalGrade (lagPartner q) = -horizontalGrade q := by
  unfold horizontalGrade
  rw [lagPartner_coe]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  ring

/-- The reflection's fixed locus in `ℝ` is the single point `0`: `ℝ` has no `2`-torsion. -/
theorem horizontalGrade_lagPartner_eq_iff (q : XiZeroCopy) :
    horizontalGrade (lagPartner q) = horizontalGrade q ↔ horizontalGrade q = 0 := by
  rw [horizontalGrade_lagPartner]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

theorem horizontalGrade_eq_zero_iff (q : XiZeroCopy) :
    horizontalGrade q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  unfold horizontalGrade
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **The hypothesis in grade coordinates.** -/
theorem riemannHypothesis_iff_horizontalGrade_eq_zero :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, horizontalGrade q = 0 := by
  rw [riemannHypothesis_iff_lagPartner_fst_eq]
  exact forall_congr' fun q =>
    (lagPartner_fst_eq_iff q).trans (horizontalGrade_eq_zero_iff q).symm

/-- **Reflection-even readers are blind to free orbits.**  Every real-valued reader that is even in
the grade — every norm, energy, squared amplitude, signature or positivity in the corpus — takes the
same value on a copy and on its Hermitian partner, so it cannot distinguish a fixed orbit from a
free one. -/
theorem reflectionEven_reader_eq_at_partner (F : ℝ → ℝ) (hF : ∀ a : ℝ, F (-a) = F a)
    (q : XiZeroCopy) :
    F (horizontalGrade (lagPartner q)) = F (horizontalGrade q) := by
  rw [horizontalGrade_lagPartner]; exact hF _

/-- The square of the grade is such a reader, and it is nonnegative for **every** value of the
grade: the canonical reflection-even coordinate is automatically consistent with an off-line copy. -/
theorem sq_horizontalGrade_nonneg (q : XiZeroCopy) : 0 ≤ horizontalGrade q ^ (2 : ℕ) :=
  sq_nonneg _

theorem sq_horizontalGrade_lagPartner (q : XiZeroCopy) :
    horizontalGrade (lagPartner q) ^ (2 : ℕ) = horizontalGrade q ^ (2 : ℕ) := by
  rw [horizontalGrade_lagPartner]; ring

end

end RHTower
