# Monogenicity in algebra form (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Extension of module 44,
`MonogenicOfDigitExpansion.lean`.  See [[research/monogenicity_no_completeness_2026_08_06]].

## Added

**`adjoin_singleton_eq_top`** — `Algebra.adjoin A ({x} : Set B) = ⊤` for a finite extension of DVRs
with trivial residue extension and `x` a uniformizer.  From `span_pow_eq_top` via
`Submodule.span_le` into `Subalgebra.toSubmodule (Algebra.adjoin A {x})`.

## The mathlib bridge this unlocks (next step, not yet done)

`Mathlib/RingTheory/DedekindDomain/Different.lean`:

    conductor_mul_differentIdeal (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
      conductor A x * differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))}

Note the hypothesis is at the **fraction-field** level (`adjoin K {x} = ⊤` in `L`), not the ring
level — so `adjoin_singleton_eq_top` needs transporting up, and `conductor A x = ⊤` needs deriving
from `A[x] = B`.  Doing both would turn module 42's "derivative of the characteristic polynomial"
into `differentIdeal A B = (maximalIdeal B)^(e−1)` — the different exponent theorem proper.

The setup cost is the Dedekind/fraction-field instance bundle (`K`, `L`, `IsIntegralClosure B A L`),
which is why it was not attempted in the same iteration.

## Lean note

`Algebra.subset_adjoin rfl` leaves the algebra instance stuck ("typeclass instance problem is
stuck", metavariables).  Name the membership: `Algebra.subset_adjoin (Set.mem_singleton x)`, bound
to a `have` with an explicit type.

## Remaining for Theorem A

1. Transport monogenicity to the fraction field + conductor = ⊤ ⇒ the different proper.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
