# Algebraic moving-fiber prime--Weyl parallelogram route to RH

- **ID:** `algebraic-moving-fiber-prime-weyl-parallelogram-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Lean bridge:**
  `formal/GaloisForLFunctions/RHTower/PrimeAlgebraicTranslationWeylPhase.lean`
- **Inputs:** `PrimeDyadicWeyl.lean`, `SEMEventualSplit.lean`,
  `EulerTranslationGroupoid.lean`, `GelfondSchneiderProof/Statement.lean`
- **Positive successor to:** `moving-fiber-prime-weyl-parallelogram.md`

## Claim

The moving-fiber prime--Weyl square does not need flat or trivial determinant holonomy.  A much
weaker arithmetic descent would suffice.

Fix a prime `p`, a positive integer `q`, and the rational-imaginary displacement

```text
t_q = I/q.                                                       (1)
```

The exact source Weyl relation is

```text
T_(t_q) M_p = exp(-(log p)t_q) M_p T_(t_q).                      (2)
```

If a moving root cluster has total multiplicity `d`, the scalar action on its determinant line is

```text
H_(p,q,d) = exp(-(log p)t_q)^d = p^(-(d/q)I).                    (3)
```

The exponent `-(d/q)I` is algebraic and irrational whenever `d>0`.  Gelfond--Schneider therefore
gives

```text
H_(p,q,d) algebraic  <->  d=0.                                  (4)
```

Consequently, a source-canonical moving root-cluster determinant line whose holonomy both obeys
`(3)` and descends to a number field cannot carry a positive-rank cluster.  This replaces the
false claim that a closed groupoid square must have holonomy one.

## Arbitrarily local form

Lean proves `norm(t_q)=1/q` and that for every positive isolating radius `epsilon`, some positive
`q` satisfies `norm(t_q)<epsilon`.  Therefore the arithmetic collision is compatible with an
arbitrarily small moving cluster.  It is not blocked by the nonzero fixed-point obstruction of the
dyadic prime clock.

Given a hypothetical right-half zero `rho`, choose a closed disc around `rho` contained in the
open right half and with zero-free boundary.  The existing eventual-SEM machinery supplies a
finite root census on such a disc.  Then choose `q` large enough that all four translated windows
needed by the prime--Weyl square remain inside a common isolating neighborhood.  The cluster rank
at the initial vertex is

```text
d = ord_rho(Xi)>0.                                               (5)
```

The local transcendence theorem turns algebraic determinant descent into `d=0`, contradicting
`(5)`.

## Two-ended chain

```text
completed prime--Gamma source and its exact global prime--Weyl relation
  -> hypothetical Xi zero rho with Re(rho)>1/2
  -> source-defined isolating window contained in the open right half
       [standard local analytic geometry; must be integrated with the source model]
  -> choose q with norm(I/q) below the window transport radius
       [PROVED LEAN]
  -> four-vertex moving source/root-cluster groupoid of constant rank
       d=ord_rho(Xi)>0
       [OPEN CORE A: source moving-cluster construction]
  -> determinant transport around the T_(I/q)--M_p square
  -> exact holonomy H_(p,q,d)=p^(-(d/q)I)
       [global scalar law PROVED LEAN;
        OPEN CORE B: determinant comparison]
  -> determinant line and transport descend over a number field
       [OPEN CORE C: arithmetic descent]
  -> H_(p,q,d) is algebraic
  -> Gelfond--Schneider forces d=0
       [PROVED LEAN]
  -> contradiction at every right-half zero
  -> Xi has no zero in Re(s)>1/2
  -> RH.                                                         (6)
```

The reverse end is also closed formally.  Lean packages an algebraic determinant-descent
interface and proves that, for fixed `p` and nonzero `q`, producing such an interface at every
hypothetical right-half Xi zero is equivalent to RH.  This is a consumer theorem.  It does not
pretend that the source producer in Open Cores A--C has been constructed.

## Why this is stronger than the old positive residue

The earlier parallelogram analysis correctly proved that a groupoid loop may have arbitrary
nontrivial scalar holonomy.  It identified determinant-line flatness as a sufficient extra datum,
but flatness is far stronger than necessary and its vanishing class coincides with the existing
completed-SEM contour charge.

Here the loop may be curved and its holonomy may be nontrivial.  Only arithmetic descent is asked
for.  Gelfond--Schneider proves the positive source obstruction:

> every positive-rank rational-imaginary prime--Weyl determinant holonomy is transcendental.

Thus a number-field realization is automatically rank zero.  The discarded flatness problem has
been replaced by a different source question: whether the moving determinant transport has an
algebraic Betti/étale form before analytic period evaluation.

## Candidate source constructions `[CONJECTURE]`

1. **Algebraic Betti/étale determinant line.** Construct the moving finite SEM complex over a
   number field from prime incidence and the Gamma functional equation, then compare its Betti
   monodromy with analytic prime--Weyl transport.
2. **Finite Grushin determinant descent.** Use a source-defined Grushin problem on the moving
   isolating window.  Its effective finite operator already carries the root multiplicity.  The
   required new theorem is that the determinant transition matrices admit an algebraic model while
   analytic comparison retains the scalar in `(3)`.
3. **Relative determinant gerbe.** Place the four vertices in a relative determinant gerbe.  Its
   algebraic cocycle need not be trivial; it only needs a number-field characteristic polynomial.
   The analytic realization must have eigenvalue `(3)`.
4. **Right-half boundary cohomology.** Define the finite cluster as a relative cohomology group of
   the open right half and its critical-line boundary.  The geometric half-plane selector is
   source-pure and avoids enumerating zeros.  An algebraic comparison functor would make the
   determinant monodromy algebraic only for this relative sector.

The fourth candidate most directly prevents the construction from also excluding known
critical-line zeros.

## Attacks and firewalls

1. **A closed square does not imply holonomy one.** This route never uses that false implication.
   The loop may carry arbitrary curvature; only an independent algebraic model can trigger `(4)`.
2. **Finite dimensionality does not imply algebraicity.** A complex matrix with Gamma or
   exponential entries may have transcendental determinant.  Open Core C requires a genuine
   number-field form, not a finite analytic truncation.
3. **Raw Gamma/Stokes data are not algebraic.** Existing Tate-local analysis shows that raw
   archimedean Stokes multipliers contain powers of `2*pi*I`.  Algebraicity must occur on the
   Betti/étale side before the period comparison.
4. **The determinant scalar can be gauged away from an unframed divisor.** The construction must
   retain a framed determinant line or relative determinant object.  Passing only to a principal
   ideal loses `(3)`.
5. **The four vertices are different fibers.** Open Core A must construct transport and constant
   rank over all four windows.  No determinant-of-an-endomorphism shortcut is allowed.
6. **Translation is not an Xi symmetry.** The other vertices contain translated source functions,
   not Xi itself.  The groupoid must live over the source orbit of functions and return to the
   initial fiber only after the full commutator square.
7. **Critical-line zeros must not be excluded.** A universal algebraic descent for every positive
   root cluster would contradict known critical-line zeros.  The actual producer must be relative
   to the open right-half sector, or vanish on functional-equation fixed clusters for a proved
   source reason.
8. **The right-half selector must be geometric, not divisor-fed.** A disc contained in
   `Re(s)>1/2` is allowed.  Selecting a block only after listing off-line Xi zeros is circular.
9. **The Weyl scalar must survive analytic comparison.** Algebraic transition matrices may be
   conjugated, but a scalar eigenvalue cannot change under conjugation.  A rescaling that removes
   `(3)` changes the framed comparison and must appear as an explicit period factor.
10. **Branch control is load-bearing.** Lean uses principal `Complex.cpow`; the analytic
    determinant comparison must yield the same branch.  The exponential form in `(3)` fixes it.
11. **Choosing `q` is not target fitting.** `q` is chosen only from the isolating transport radius,
    independently of `d`.  Gelfond--Schneider excludes every `d>0` for every nonzero `q`.
12. **Bare algebraicity remains a consumer.** Defining the holonomy to be `(3)` and postulating it
    algebraic is RH-equivalent.  The only proof-bearing work is a source construction of Open Cores
    A--C.

## Formal status

- `[PROVED LEAN]` `norm(I/q)=1/q` and positive steps occur below every positive radius;
- `[PROVED LEAN]` the exact prime--Weyl relation at `I/q`;
- `[PROVED LEAN]` the rank-`d` determinant scalar equals `p^(-(d/q)I)`;
- `[PROVED LEAN]` this phase is transcendental for every `d>0` and `q>0`;
- `[PROVED LEAN]` algebraicity of the phase is equivalent to `d=0`;
- `[PROVED LEAN]` existence of the minimal algebraic determinant-descent interface is equivalent
  to rank zero;
- `[PROVED LEAN]` the local right-half descent consumer is equivalent to RH;
- `[OPEN CORE]` moving root-cluster groupoid from the completed source;
- `[OPEN CORE]` multiplicity-exact determinant comparison retaining the prime--Weyl scalar;
- `[OPEN CORE]` noncircular number-field descent relative to the open right half;
- `[CLOSED SHORTCUT]` flatness or trivial holonomy is neither automatic nor required.

The formal bridge is infrastructure, not claimed as new science.  The only significance target is
the complete source assembly through the three open cores to `(6)`.
