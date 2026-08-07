# Finite source ports cannot homogenize the Hedenmalm theta system

- **ID:** `hedenmalm-finite-source-port-obstruction`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Statement:** Every complex function subspace containing the actual completed theta source
  `XiC` and stable under spectral-coordinate multiplication is infinite-dimensional. Hence no
  rank-two or fixed finite-dimensional compensating port can remove the affine Hedenmalm source
  while retaining its descended generator.

## Goal

Test the proposed Frankenstein step “use the new bilateral endpoint decay of the Hedenmalm root
mode inside an existing finite translation/moderation carrier.” The test must preserve the actual
theta source, the spectral-coordinate generator, and finite dimensionality; replacing any of
these by an abstract wrapper would not address the source-forced system.

## Conjecture loop

### C3 — endpoint decay supplies a finite bilateral-moderation eigenvector

`[FALSIFIED AS STATED] [TYPE FAILURE]` The physical source mode satisfies the affine equation

```text
(D + z) u = -thetaSource,
```

whereas the bilateral-moderation endpoint consumes a homogeneous integer-shell eigenrecurrence.
The existing algebraic homogenization quotients the Fourier-side system by the coordinate-stable
module `XiC(z) C[z]`; it supplies neither a normed completion nor a shell action transporting the
physical endpoint estimates. Physical decay therefore cannot be inserted into the moderation
endpoint without first constructing a non-erasing, norm-conservative descent. The corpus theorem
`normConservative_sourceCharacterFibre_descent_dichotomy` shows that such a descent is itself
neutrality-forcing, so assuming it would move rather than solve the RH core.

### C4 — the necessary source port is intrinsically infinite

`[PAPER-PROVED]` Strengthen the failed finite-carrier proposal to an exact obstruction. Let
`S <= (C -> C)` be a complex vector subspace satisfying

```text
XiC in S,
F in S  ->  (z |-> z F(z)) in S.
```

Then `S` is not finite-dimensional.

## Paper proof under hostile audit

Define

```text
M : C[z] -> (C -> C),       M(P)(z) = P(z) XiC(z).
```

1. `M` is complex-linear.
2. `XiC(0) != 0`, and analyticity implies continuity at zero. Thus `XiC` is nonzero on a
   neighbourhood `U` of zero. Every neighbourhood of zero in `C` is infinite.
3. If `M(P)=M(Q)`, then `(P-Q)(z)=0` for every `z in U`, because `XiC(z) != 0` there. A complex
   polynomial with infinitely many roots is zero. Therefore `P=Q`; `M` is injective.
4. The monomials `1,z,z^2,...` are linearly independent in `C[z]`; injectivity of `M` makes
   `XiC,z XiC,z^2 XiC,...` linearly independent as functions.
5. The existing minimality theorem
   `eval_mul_XiC_mem_of_coordinateMultiplication_stable` puts every `P XiC` in `S`. For
   `n=finrank_C(S)+1`, the first `n` orbit vectors therefore give `n` linearly independent vectors
   in `S`, contradicting the finite-dimensional rank bound.

No RH instance, zero-reality assumption, numerical computation, hypertranscendence theorem, or
unproved analytic continuation is used. The nonzero germ at the spectral centre already forces
the infinite cyclic source orbit.

## Hostile tests

- **Could zeros of `XiC` make multiplication by it non-injective in the pointwise function ring?**
  No. Global cancellation is unnecessary; the zero-free neighbourhood of zero gives infinitely
  many polynomial test points.
- **Could a finite port contain only the source and one compensator?** No. Generator stability
  repeatedly produces every coordinate multiple, and those multiples are independent.
- **Does quotienting erase the divisor modes as well as the source?** No. The corpus theorem
  `xiThetaEigenFourier_notMem_xiPolynomialModule` proves every Hedenmalm divided divisor mode
  survives the algebraic quotient.
- **Does this prove RH?** No. It classifies the size of any honest homogenizing port. The next open
  core is an infinite cyclic completion carrying both a useful conservative action and a faithful
  embedding of the surviving divisor modes.

## Internal and external frontier

- `[CORPUS]` `eval_mul_XiC_mem_of_coordinateMultiplication_stable` and
  `xiThetaEigenFourier_notMem_xiPolynomialModule` in
  `XiHedenmalmInvariantHomogenization.lean` prove algebraic minimality and divisor faithfulness.
- `[CORPUS]` `XiC_analytic` and `XiC_zero_ne` in `XiHadamardFactorization.lean` provide the nonzero
  analytic germ.
- `[CORPUS]` `normConservative_sourceCharacterFibre_descent_dichotomy` in
  `SourceCharacterFibreConservativeDescentLaw.lean` blocks an assumed conservative finite descent.
- `[LITERATURE]` Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494v1,
  gives the actual forced root mode and endpoint decay but does not construct a finite invariant
  source port or the obstruction above.
- The abstract fact that a multiplication-cyclic subspace generated by a nonzero analytic germ is
  infinite-dimensional is elementary. Scientific value here is the corpus-specific bridge:
  minimal Hedenmalm homogenization plus faithful divisor survival plus the conservative-descent
  wall. No priority claim is made.

## No-go closure

- **Exact killing mechanism:** affine physical source mode has no typed map into the homogeneous
  shell recurrence; the only corpus homogenization requires the entire coordinate orbit.
- **Strongest positive survivor:** every honest coordinate-stable Hedenmalm source port is
  infinite-dimensional, while the algebraic quotient by its minimal orbit remains divisor-faithful.
- **New insight:** finite boundary defects from other routes cannot be the missing compensator.
  Viable Frankenstein route must use an infinite cyclic/Krylov port and prove conservativity on
  that actual completion; this is a sharper target than another endpoint-decay estimate.
- **Status:** paper proof dependency-closed; exact Lean formalization next.

## Gates

- [x] 0 -> 1: actual-source statement, exact failed bridge, and hostile test identified
- [x] 1 -> 2: complete dependency-closed paper proof
- [ ] 2 -> 3: exact Lean theorem and axiom/lint gates
- [ ] 3 -> 4: publication-ready

## Log

- 2026-08-07 — C3 rejected: physical endpoint decay and algebraic/shell moderation live in
  different carriers, and no conservative descent exists in the corpus.
- 2026-08-07 — C4 extracted as positive survivor and proved from the nonzero central Xi germ,
  polynomial root finiteness, coordinate stability, and the finite-rank bound. Promoted to Stage 2.
