# Route L: reconstruction of the cyclic Gibbs diagonal

Status: formalized and audited; 12 unconditional theorems. RH remains unproved.
Date: 2026-09-11.
Module: `GaloisForLFunctions.RHTower.Deninger.DeningerGibbsCyclicDiagonalRecovery`.

## Exact source and theorem

Fix `sigma>1/2`, the C16 summability domain `D_sigma`, and its actual
normalized Gibbs reader. For `T in D_sigma`, define the all-integer
pair-cyclicity condition by

`Reader_sigma(S_n^* T S_n) = Reader_sigma(T P_n)` for every `n!=1`.

Here `S_n`, `S_n^*` and `P_n` are the existing ordinary-integer Wold shift,
backward shift and divisibility projection. C16 proves both displayed
products belong to the same domain.

The exact classification is

`all-integer pair cyclicity iff (T e_k)(k)=0 for every k!=1`.

Thus the diagonal of a cyclic admitted operator is supported at the unit.
The statement concerns the specified diagonal reader and Wold pairs. It does
not claim that the full operator is supported at the unit or that the reader
is cyclic on all products.

Consequently, **no summable diagonal correction to the actual reciprocal
Green source `Q` can make every integer Wold pair cyclic for this fixed
reader**. Precisely, there is no `T in D_sigma` for which both

`sum_k ((T-Q)e_k)(k)` is a summable complex family,

and the displayed all-integer pair-cyclicity condition hold.

No positivity, self-adjointness, finite-support condition or prime-only
replacement is assumed. All integer divisibility readouts, including
composites, occur in the theorem.

## Positive arithmetic reconstruction theorem

For any summable complex families `f,g` on positive integers,

`[for every n, sum_(n|k) f(k)=sum_(n|k) g(k)] implies f=g`.

If instead all sums for `n!=1` vanish, the family is supported at the unit.
These statements are proved independently of Gibbs weights. They recover
all diagonal coefficients from a complete family of incidence readouts,
not merely the total trace.

## Dependency-closed paper proof

1. Divisibility sets `D_n={k:n|k}` form a pi-system: their intersection is
   `D_lcm(n,m)`. They generate the full sigma-algebra on positive integers.
   Indeed, the singleton `{k}` is the intersection of `D_n` when `n|k` and
   their complements otherwise. Two integers with the same complete
   divisibility pattern divide each other and are equal.
2. A summable complex family is integrable against counting measure and
   hence defines a countably additive vector measure by integration on
   subsets. If its value is zero on every `D_n`, pi-lambda induction proves
   the vector measure is zero. Evaluation on singletons recovers every
   coefficient. Applying this to a difference proves injectivity. To handle
   only `n!=1`, subtract the total mass concentrated at the unit and apply
   injectivity; the nonunit coefficients vanish.
3. For `T in D_sigma`, apply this reconstruction to
   `f(k)=k^(-2*sigma)*k*(T e_k)(k)`. Its multiples sums equal the unnormalized
   traces of `T P_n`. C16's source-derived exchange law has multiplier
   `exp((2*sigma-1)*log n)`, which is not one for `n!=1`. Pair cyclicity
   therefore makes each nontrivial multiples sum zero. Reconstruction and
   the nonzero diagonal weights give `(T e_k)(k)=0` for `k!=1`.
4. Conversely, if the diagonal is supported at the unit, every nontrivial
   divisibility trace is zero. The same exchange law gives pair cyclicity.
5. Such a diagonal has finite support and is summable. If the diagonal of
   `T-Q` were also summable, their difference would make the reciprocal
   diagonal `1/k` summable. The exact p-series criterion excludes this.

This proof uses countable additivity, not an interchange of an unverified
infinite Möbius inversion series.

## Scope and remaining obstacle

C18 tests corrections to the literal ordinary-integer `Q` while keeping the
C16 reader fixed. It does not assume the full rectangular Gamma tensor is
identified with this scalar model by a summability-preserving map. The
subsequent [full-source shell scalarization](route-l-full-gamma-shell-flattening.md)
constructs one specific bounded map with a summable correction. Its
physical-reader agreement and Xi-jet fidelity remain unproved.

The positive survivor is the full reconstruction theorem and exact cyclic
diagonal classification. The correction obstruction is stronger than
checking `Q` alone: it includes every summable signed diagonal correction
whose corrected operator belongs to the actual reader domain.

This does not prove RH or exclude route L. A singular comparison outside
this correction class, retaining the existing physical value and Xi
multiplicity, remains unproved.

## Corpus and recent-paper tests

Deep/method searches were partial. They did not provide the reconstruction
as a ready theorem; direct mathlib source inspection supplied the pi-lambda
induction, vector measures from integrable densities, and the counting
measure criterion. The corpus's `CofinalUnitProfileResidue` gives the related
summable-difference/residue method used in the final contradiction.

The [August 2026 Markovian holonomy universality theorem](https://arxiv.org/html/2608.15923v1)
requires a fixed limiting symbol, common boundary data, and uniform spectral
summability. It does not supply those comparisons for this arithmetic
source. The present proof retains the entire family of incidence readouts
and uses proven summability to reconstruct coefficients. Other broad-search
and nonlinear-first-variation tests are recorded under C18 in the main
attack ledger. No external conjecture or paper claim is a Lean premise.

## Verification

- Scratch `lake env lean /tmp/route_l_divisibility_recovery.lean`: passed without warnings.
- Final targeted `lake build GaloisForLFunctions.RHTower.Deninger.DeningerGibbsCyclicDiagonalRecovery`:
  passed; only the new module built, dependencies replayed. No umbrella build.
- All 12 theorem declarations audited through `/tmp/route_l_cyclic_diagonal_axioms.lean`:
  only `propext`, `Classical.choice`, `Quot.sound`; no added axioms.
- `scripts/formal_tools.py lint`: passed, with existing file-size warnings.
- Import wired into `GaloisForLFunctions.RHTower`. No numerical experiment is used.
