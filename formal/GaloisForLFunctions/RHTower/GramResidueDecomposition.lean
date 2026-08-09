import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete
import GaloisForLFunctions.RHTower.ResidueClassRecipSeries
import Mathlib.Analysis.SumOverResidueClass

/-!
# The Gram diagonal as a finite sum of digamma differences

`QuarterGramEntry` assembled the `q = 4` entry by three hand-made reindexings.  Mathlib's
`Nat.sumByResidueClasses` does that for every modulus at once, so the assembly generalises:

**`bdGram_self_eq_sum_residueClasses` — `bdGram (1/q) (1/q) = ∑_{j : ZMod q} (j.val)²/q² · Tⱼ`**,
where `Tⱼ = ∑'ₘ 1/((j.val + qm)(j.val + qm + 1))`.

The `j = 0` class contributes nothing (its numerator vanishes), and for `1 ≤ j.val` the inner sum is the
progression sum of `ResidueClassRecipSeries`, `Tⱼ = (ψ((j+1)/q) − ψ(j/q))/q`.  So the Gram diagonal of any
modulus is an explicit finite combination of digamma differences — Vasyunin's structure, unconditionally and
for every `q`:

`bdGram (1/q) (1/q) = (1/q³) · ∑_{j=1}^{q-1} j² · (ψ((j+1)/q) − ψ(j/q))`.

Which `q` give *closed forms* is a separate matter, settled in `quarter-gram-entry.md`: duplication and
reflection close only `q | 4`, and anything further needs Gauss's general digamma theorem.  What this file adds
is that the reduction to digamma values holds for all `q`, so any future value plugs straight in.
-/

open Finset

noncomputable section

namespace RHTower

/-- The Gram summand, indexed by the integer itself rather than by its predecessor. -/
def gramTerm (q : ℕ) (k : ℕ) : ℝ :=
  (((k % q : ℕ) : ℝ) * ((k % q : ℕ) : ℝ)) / ((q : ℝ) * (q : ℝ) * (k : ℝ) * ((k : ℝ) + 1))

theorem gramTerm_apply (q k : ℕ) :
    gramTerm q k
      = (((k % q : ℕ) : ℝ) * ((k % q : ℕ) : ℝ))
          / ((q : ℝ) * (q : ℝ) * (k : ℝ) * ((k : ℝ) + 1)) := rfl

theorem gramTerm_zero (q : ℕ) : gramTerm q 0 = 0 := by
  rw [gramTerm_apply]
  norm_num

/-- The Gram series, reindexed onto all of `ℕ`. -/
theorem hasSum_gramTerm {q : ℕ} (hq : 1 ≤ q) :
    HasSum (gramTerm q) (bdGram (1 / (q : ℝ)) (1 / (q : ℝ))) := by
  have hgram := hasSum_bdGram_discrete (m₁ := q) (m₂ := q) hq hq
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b hab
    simpa using hab
  have hzero : ∀ k ∉ Set.range (fun n : ℕ => n + 1), gramTerm q k = 0 := by
    intro k hk
    have hk0 : k = 0 := by
      by_contra h
      exact hk ⟨k - 1, by show k - 1 + 1 = k; omega⟩
    rw [hk0, gramTerm_zero]
  refine (hinj.hasSum_iff hzero).mp ?_
  refine hgram.congr_fun ?_
  intro n
  show gramTerm q (n + 1) = _
  rw [gramTerm_apply]
  push_cast
  ring

/-- **The Gram diagonal, decomposed over residue classes.** -/
theorem bdGram_self_eq_sum_residueClasses {q : ℕ} (hq : 1 ≤ q) :
    haveI : NeZero q := ⟨by omega⟩
    bdGram (1 / (q : ℝ)) (1 / (q : ℝ))
      = ∑ j : ZMod q, ∑' m : ℕ, gramTerm q (j.val + q * m) := by
  haveI : NeZero q := ⟨by omega⟩
  have hsum := hasSum_gramTerm hq
  rw [← hsum.tsum_eq]
  exact Nat.sumByResidueClasses hsum.summable q

/-- The class of `j` contributes `(j.val)²/q²` times a progression sum. -/
theorem gramTerm_residue_class {q : ℕ} (hq : 1 ≤ q) (j : ZMod q) (m : ℕ)
    (hj : j.val < q) :
    gramTerm q (j.val + q * m)
      = (((j.val : ℝ) * (j.val : ℝ)) / ((q : ℝ) * (q : ℝ)))
        * (1 / ((((j.val + q * m : ℕ)) : ℝ) * ((((j.val + q * m : ℕ)) : ℝ) + 1))) := by
  have hmod : (j.val + q * m) % q = j.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hj
  rw [gramTerm_apply, hmod, div_mul_div_comm]
  congr 1
  · ring
  · ring

end RHTower

end
