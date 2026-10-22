# Route L: bounded physical probes of the complete Gamma source

Date: 2026-09-11.
Status: formalized and audited; 18 theorems.
Module: `GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixBoundedSoninProbe`.
RH remains unproved.

## Candidate and exact result

C20 constructs one bounded scalarization of the actual complete Gamma-six
source. C21 tests whether a different bounded probe, in particular a literal
Sonin completed-Mellin evaluation or finite jet, can remove its reciprocal
obstruction while retaining a nonzero leading coefficient.

Write the existing full source column as

`F_n=lambda_n*v+R_n`, with `sum_n norm(R_n)<infinity`,

and use C20's source-defined profile

`d_n=1/((n+216)*lambda_n)`, `1/6<=d_n<=1`.

For every bounded complex linear functional `L` on the tensor carrier,

`d_n*L(F_n)=L(v)/(n+216)+e_n`,

`e_n=d_n*L(R_n)`, `abs(e_n)<=norm(L)*norm(R_n)`.

Place the full columns at positive integers at least 216 and put zero at
the omitted finite head. The resulting diagonal `a_L` satisfies

`sum_k abs(a_L(k)-L(v)/k)<infinity`,

and the sharp positive classification is

`a_L is summable <=> L(v)=0`.

Every such full-source diagonal operator belongs to every open Gibbs domain
`sigma>1/2`. If it is prime-pair cyclic for that domain's fixed reader, then
`L(v)=0`. This implication is not claimed to be reversible: a nonzero
summable remainder can still fail the prime tests.

## Literal physical evaluations and jets

Fix a positive aperture `b`. Let `B` be any bounded linear map from the tensor
carrier into the existing Burnol co-Poisson quotient. At each point `w` of
`1/2<Re(w)<1`, pull back the existing completed-Mellin evaluation vector:

`L_w(f)=<k_(w,b),B(f)>=MellinCompleted(B(f))(w)`.

The second equality is the existing reproducing-kernel theorem, proved on
the actual quotient. Use `sigma=Re(w)` for its Gibbs test. If every `L_w`
passes all prime-pair cyclicity tests, the scalar result gives
`MellinCompleted(B(v))(w)=0` for every right-strip point. The already proved
Mellin separation theorem then gives `B(v)=0` in the physical quotient.

Conversely, `B(v) != 0` supplies a detecting right-strip point with nonzero
principal coefficient and failed prime cyclicity. In particular, no
bounded injective quotient map passes this whole family of tests.

For any bounded map into the literal extended Sonin space, the existing
all-order jet bridge supplies each finite completed-Mellin derivative as a
bounded pullback probe. Its scalar diagonal is summable exactly when the
corresponding derivative of the leading image vanishes. Prime cyclicity
forces that derivative to vanish. All source remainder terms are retained.

## Dependency-closed paper proof

1. Apply `L` to the existing exact source decomposition. Multiply by `d_n`
   and use `d_n*lambda_n=1/(n+216)`.
2. The operator norm inequality and `d_n<=1` dominate the complete scalar
   error by `norm(L)*norm(R_n)`. Vector-column norm summability proves
   absolute scalar summability. A finite shift accounts for the omitted head.
3. If `a_L` is summable and `L(v)!=0`, subtract its summable error and divide
   by `L(v)`. This would make `1/k` summable, contradicting the current
   corpus's exact Gibbs p-series criterion at `sigma=1/2`. If `L(v)=0`,
   the summable error is the whole diagonal, proving the converse.
4. For `sigma>1/2`, the Gibbs diagonal weight is at most one. Dominate the
   weighted error and add the admitted scalar multiple of the Green term.
5. Prime-pair cyclicity is homogeneous on the actual Gibbs domain. If
   `L(v)!=0`, replace `L` by `L(v)^(-1)*L`; its complete operator is a
   summable correction to `Q` and would remain prime cyclic. C19 excludes it.
6. Compose the actual bounded quotient evaluation vector with `B`. Its
   reproducing identity identifies the scalar probe with the literal
   completed-Mellin value. Apply step 5 at each point, then the existing
   co-Poisson Mellin separation theorem. Nonzero images have a detecting
   point by that same separation theorem.
7. For each finite jet, compose the existing bounded completed-Mellin jet
   evaluator on the extended Sonin carrier with the proposed bounded map.
   Steps 1--5 apply to this actual jet probe with no assumed jet identity.

## Scope and surviving problem

No bounded source-to-Sonin map is constructed here. These are universally
quantified classification theorems for such maps, not a comparison premise
used to derive RH. The leading tensor is the existing theta tensor square;
its image is not automatically a Xi divisor's nonzero top jet.

The candidate fails when required to preserve a nonzero physical leading
image and make all the displayed probes prime cyclic. It does not exclude
maps annihilating the leading tensor while retaining a nonzero remainder,
source-dependent unbounded probes, stronger source norms, or singular
comparisons. Those alternatives still need the actual prime transport,
fixed-reader agreement, and all Xi multiplicity/jet data. Route L is open.

The positive survivor is the exact full-source decomposition and sharp
summability criterion for every bounded scalar and finite physical jet
probe, together with the detecting-point theorem in the actual quotient.

## Search and method audit

Two deep/method searches tested completed-Sonin source compatibility and
bounded-probe principal coefficients. Both reported partial coverage, with
706108 ready and 779 stale method records. Candidate kernels and finite
trace continuation did not supply the missing source comparison. Direct
source inspection located the applicable quotient reproducing vector,
Mellin separation, all-order jet bridge, and complete tensor decomposition.

Broad arXiv terms were `interpolation`, `modular`, and `tomography`.
The [September 5 extended-Gevrey interpolation paper](https://arxiv.org/html/2609.06258v1)
controls all derivative orders from a sparse sequence only after quantitative
derivative bounds are supplied (Theorem 3.4); it gives no arithmetic reader
identity. The [September 9 finite-element interpolation paper](https://arxiv.org/html/2609.10374v1)
uses Taylor remainders and averaging on specified Sobolev mesh domains; no
matching source domain or comparison is provided here. Neither is imported
as a mathematical premise or claimed to solve the compatibility problem.

## Verification

- `lake env lean /tmp/route_l_bounded_sonin_probe.lean`: passed, all 18 theorems,
  including literal finite-jet classification, no warnings.
- Targeted final `lake build GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixBoundedSoninProbe`: passed; only the new module built, dependencies replayed. Umbrella import wired.
- All 18 theorem declarations audited through `/tmp/route_l_bounded_sonin_probe_axioms.lean`: only `propext`, `Classical.choice`, `Quot.sound`; no added axioms.
- `scripts/formal_tools.py lint`: passed, existing file-size warnings only.
- Scoped whitespace check passed; no owned Lean or search process remains.
- No numerical experiment or umbrella build.
