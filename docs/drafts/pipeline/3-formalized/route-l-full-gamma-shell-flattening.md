# Route L: full Gamma source and reciprocal Green scalarization

Date: 2026-09-11.
Status: formalized and audited; 24 unconditional theorems. RH remains unproved.
Module: `GaloisForLFunctions.RHTower.DeningerGammaSixFullSourceScalarization`.

## Actual source and fixed comparison

Use the existing complete countertransported Gamma-six tensor-square source,
its sorted ordinary-integer shell coordinates, and the canonical normalized
coefficient functional `ell` of the nonzero leading tensor. These are the
literal objects in `DeningerGammaSixFullSourcePrincipalClass`.

At coordinate `n`, put

`x_n=n+216`, `lambda_n=6^(-floor(log_6(x_n)))`,

`d_n=1/(x_n*lambda_n)`.

The source-defined profile satisfies `1/6<=d_n<=1`. It is invariant under
the exact degree-six Wold map `W(n)=6*n+1080`. Thus multiplication by `d`
is a bounded scalar operator of norm at most one, and the bounded tensor
reader `C=D*ell` commutes with the corresponding vector/scalar Wold
pullbacks. The associated rectangular Wold compressions intertwine exactly.
No divisor or critical-line hypothesis is used to choose this map.

## Complete source identity

The actual source column is its principal tensor `lambda_n*v` plus its
complete remainder `R_n`, with `sum_n norm(R_n)<infinity`. Since `ell(v)=1`,

`C(F_n)=1/(n+216)+e_n`, `e_n=d_n*ell(R_n)`.

Every leading-tail, tail-leading, and tail-tail term remains in `R_n`.
The proof gives `abs(e_n)<=norm(ell)*norm(R_n)`, hence `e` is summable.
At bounded-operator level, the scalarized full operator differs from the
scalarized principal operator by a trace-class operator.

Place these complete scalar columns at positive-integer labels `k>=216`
and put zero at the omitted finite head. The resulting literal diagonal
endomorphism `T` satisfies

`sum_k abs((T e_k)(k)-1/k)<infinity`.

The finite head contributes the exact correction `-1/k`; it is not silently
removed. This establishes a concrete full-source-to-scalar-model comparison
that C18--C19 had explicitly left unconstructed.

## The physical test and surviving first normal residue

For every `sigma>1/2`, this fixed `T` belongs to the actual Gibbs summability
domain. Indeed `k^(1-2*sigma)<=1`, so the weighted summable correction is
summable, and the reciprocal principal term has the proven p-series
admission. C19 then proves that `T` cannot satisfy all prime Wold pair
cyclicity for the fixed physical Gibbs reader.

The same source-defined normalization also transports the existing literal
logarithmic Wold transgression. With `L_n` the original logarithmic shell
weight and `H_n=d_n*L_n`,

`H_(Wn)-H_n/6 = (log(6)/6)/(n+216) > 0`.

Thus matching the leading reciprocal symbol and respecting degree-six
transport does not erase the first normal residue. This is an exact
identity for the existing logarithmic shell principal jet, not a claim of
transporting every derivative of the full tensor or every Xi jet.

## Dependency-closed paper proof

1. Existing shell bounds give `1/x_n<=lambda_n<=6/x_n`. Inverting their
   positive products proves the two-sided bounds on `d_n`.
2. `x_(Wn)=6*x_n` and `lambda_(Wn)=lambda_n/6`, so `d_(Wn)=d_n`.
   Their product identity is `d_n*lambda_n=1/x_n`.
3. Apply the canonical bounded coefficient functional to the entire source
   decomposition. Its normalization on the leading tensor gives the
   displayed reciprocal principal term. Its operator norm bounds the full
   remainder, and the existing vector-column summability gives summability
   of the scalar error.
4. Shifting the natural index by 216 and applying the exact summability
   criterion under a finite index shift handles the omitted head. Construct
   the diagonal endomorphism on the existing positive-integer sequence
   space; its diagonal coefficients are exactly these scalar columns.
5. Dominate its weighted error by the unweighted absolute error for
   `sigma>=1/2`, and add the admitted Green principal term for strict
   inequality. The already proved prime-incidence obstruction applies to
   this actual `T` and its proved correction, without a new comparison
   hypothesis.
6. Define the bounded reader as scalar diagonal multiplication composed
   with the existing tensor reader. Coordinate evaluation proves both the
   full-source formula and exact Wold-pullback naturality. Bounded left
   composition preserves the known rectangular trace-class remainder.
7. Multiply the existing identity
   `L_(Wn)-L_n/6=(log(6)/6)*lambda_n` by `d_n` and use step 2. Positivity
   follows from `log(6)>0` and `x_n>0`.

## Scope and remaining obstacle

This map is an explicit bounded source scalarization. It is not asserted
to equal the native normalized cyclic reader or the existing Burnol/Sonin
reader. Degree-six intertwining does not assert all-prime intertwining.
The scalar functional preserves the nonzero leading tensor coefficient;
faithfulness on every Xi-jet and multiplicity space remains unproved.

The construction therefore tests and rejects this particular normal
comparison as a source of prime cyclicity. It does not retire route L or
exclude singular comparisons at the critical endpoint. RH remains unproved.
The positive survivor is the full-source reciprocal decomposition, exact
bounded-operator transport, and retained first-normal residue.

## Corpus and paper audit

The full-source/coface and shell-normalization deep/method searches reported
partial coverage. The applicable current-corpus ingredients were inspected
directly, including the logarithmic Wold identity retrieved by method
search. Broad June--September searches and the exact limitations of the
stochastic RG and finite-dimensional mixed-state RG papers are recorded
under C20 in the main attack ledger. No external conjecture, positivity
assumption, conditional expectation or quantum channel is a Lean premise.

## Verification

- `lake env lean /tmp/route_l_full_gamma_flattening.lean`: passed, no warnings.
- Targeted final `lake build GaloisForLFunctions.RHTower.DeningerGammaSixFullSourceScalarization`:
  passed; only new module built, dependencies replayed. Umbrella import wired.
- All 24 theorem declarations audited through `/tmp/route_l_full_gamma_scalarization_axioms.lean`:
  only `propext`, `Classical.choice`, `Quot.sound`; no added axioms.
- `scripts/formal_tools.py lint`: passed, with existing file-size warnings.
- No numerical experiment or full umbrella build.
