# Selberg multiple-twist square-fibre trace

- **ID:** `selberg-multiple-twist-square-fibre-trace`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper candidate)
- **Source:** Kaczorowski--Perelli, *Multiple standard twists of L-functions* (2026),
  Theorems 1--2; new consequence isolated here
- **Statement:** For equal-degree `F,G in S^sharp`, the anti-diagonal Bohr mean of the
  normalized Kaczorowski--Perelli residue fibre is exactly its square-fibre coefficient, hence at
  the square spectral point indexed by `r` it extracts
  `a_F(r) * conjugate(a_G(r))` up to the explicit root-number and power factor.

## Goal

Expose the Selberg prime pairing as an exact fixed-point trace of a published meromorphic tensor
object.  This is a bridge, not a proof of Selberg orthogonality: continuation of the tensor does not
by itself justify taking the unbounded anti-diagonal trace of its regular part.

## Gates

- [x] 0 -> 1 in-progress: exact fibre, flow, normalization, and killing tests identified
- [ ] 1 -> 2 fully-proven: complete proof checked against the published residue normalization and
  hostile novelty audit complete
- [ ] 2 -> 3 formalized: Kaczorowski--Perelli tensor and exact trace theorem proved in Lean from
  definitions, without an axiomatic or Prop-only continuation provider
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, provenance, and Lean certificate

## Exact setup

Let `F,G in S^sharp` have the same positive degree `d`, conductors `q_F,q_G`, coefficients
`a_F(n),a_G(n)`, and root numbers `omega_F,omega_G`.  Put

```
kappa = 1/(2d),     H_1 = conjugate(F),     H_2 = G.
```

Then `d*kappa+d*kappa=1`.  For positive `alpha`, Kaczorowski--Perelli attach the multiple standard
twist

```
M(s_1,s_2;alpha)
  = sum_{m,n >= 1} conjugate(a_F(m)) a_G(n)
      m^(-s_1) n^(-s_2) e(-alpha (mn)^kappa)
```

in its domain of absolute convergence and continue it meromorphically to `C^2`.  Their normalized
finite residue fibre is

```
Xi(s_1,s_2;alpha)
  = omega_conjugate(F) omega_G
      sum_{alpha_(m,n)=alpha}
        a_F(m) conjugate(a_G(n)) m^(s_1-1) n^(s_2-1),

alpha_(m,n)
  = (mn / (q_F q_G kappa^(2d)))^(1/(2d)).
```

The actual residue on every polar hyperplane is an explicit nowhere-identically-zero elementary
factor times `W_l(s_1,s_2) Xi(s_1,s_2;alpha)`.  The theorem below concerns `Xi`; this removes
irrelevant gamma/conductor factors and the polynomial `W_l` before taking the trace.

## Frozen claim: square-fibre trace law

For every `s_1,s_2 in C` and spectral `alpha`,

```
lim_{T -> infinity} (1/(2T)) integral_{-T}^T
  Xi(s_1+it,s_2-it;alpha) dt

= omega_conjugate(F) omega_G
    sum_{r >= 1, alpha_(r,r)=alpha}
      a_F(r) conjugate(a_G(r)) r^(s_1+s_2-2).                 (SF)
```

The sum on the right has at most one term.  In particular, if

```
alpha_r = 2d * r^(1/d) / (q_F q_G)^(1/(2d))
```

and `a_F(r)a_G(r) != 0`, then the mean at `alpha_r`, divided by the explicit root-number and power
factor, is exactly `a_F(r) conjugate(a_G(r))`.  Taking `r=p` exposes the local coefficient appearing
in both Selberg conjectures.

## Paper proof

Kaczorowski--Perelli's spectrum equation fixes the product `mn`: if two pairs lie in the same
`alpha`-fibre, then their products are equal.  Consequently every fibre is finite.  Substitute
`(s_1+it,s_2-it)` in their formula for `Xi`.  Its `(m,n)` term becomes its value at `t=0` times

```
exp(i t log(m/n)).
```

Since the fibre is finite, interchange sum and integral.  For a real number `lambda`,

```
(1/(2T)) integral_{-T}^T exp(i t lambda) dt
```

equals `1` when `lambda=0` and tends to `0` otherwise.  Here `lambda=log(m/n)`, so the surviving
terms are exactly `m=n`.  This proves `(SF)`.  Injectivity of `r -> r^(1/d)` for `d>0` shows that
the right side contains at most one term.  Finally

```
alpha_(r,r)
  = (r^2/(q_F q_G kappa^(2d)))^(1/(2d))
  = 2d * r^(1/d)/(q_F q_G)^(1/(2d)).
```

No limiting interchange over an infinite Dirichlet series occurs in this proof.

## Hostile conjecturing loop

### Loop 1 -- deform the exponents and Fourier-project the diagonal

**Conjecture.** Replace the real exponents by
`kappa_1=kappa+it`, `kappa_2=kappa-it`; Fourier averaging should select `m=n` while retaining the
Kaczorowski--Perelli continuation.

**Killed.** The phase becomes

```
e(-alpha (mn)^kappa exp(i t log(m/n))).
```

For `m != n`, its modulus is exponential in the imaginary part of the complex phase.  Along
subsequences of `t`, individual terms grow exponentially and do not even tend to zero.  Moreover
the published theorem requires positive real `kappa_nu`.  The proposed deformation destroys the
defining series before any continuation argument begins.

**Positive survivor.** Keep `kappa` real and move along the unitary anti-diagonal in the `s`
variables.  This gives `(SF)` without changing the phase or leaving the theorem's parameter range.

### Loop 2 -- continue first, then take the anti-diagonal mean

**Conjecture.** Meromorphic continuation of `M` to `C^2` automatically gives meromorphic
continuation of its anti-diagonal Bohr mean, hence of the twisted Hadamard series

```
sum_n a_F(n) conjugate(a_G(n)) n^(-w) e(-alpha n^(1/d)).
```

**Killed as an implication.** The paper proves bounds only on bounded domains; its constants depend
on the domain and on `alpha`.  The anti-diagonal mean leaves every bounded domain.  Pointwise
meromorphic continuation supplies no uniform-in-`t` normal family, so exchanging continuation with
the `T -> infinity` mean is unjustified.  At `alpha=0` this operation is exactly the missing
Hadamard/Rankin--Selberg continuation, so treating it as automatic is circular.

**Positive survivor.** `(SF)` remains valid for every normalized residue fibre because each fibre
is finite.  Therefore the polar part has an exact diagonal trace even though the regular part does
not yet have a trace.

### Loop 3 -- use polar geometry for all degree pairs

**Conjecture.** The same fixed-hyperplane trace treats `F,G` of arbitrary degrees.

**Killed.** The polar hyperplanes have normal `(d_F,d_G)`.  The ordinary diagonal-extracting flow
has direction `(1,-1)` and is tangent exactly when `d_F=d_G`.  For unequal degrees it moves
transversely through the polar foliation.  This is independent of the choice of `kappa_nu`.

**Positive survivor.** Equal-degree Selberg pairing is the fixed-point sector of the universal
polar geometry; unequal-degree pairing lies in a transverse sector.  Any complete trace theorem
must state and exploit this dichotomy rather than hide it in a common estimate.

## Higher universal principle

The repeated failures are shadows of one missing operation:

```
meromorphic tensor continuation  --X-->  meromorphic Hadamard trace.
```

`X` is not another standard twist, coefficient identity, or functional equation.  It is a
trace-class/uniformity theorem for the anti-diagonal flow.  Existing additive-to-quadratic failures,
frequency accumulation, degree barriers, and the missing naive Rankin--Selberg continuation all
say the same thing: the Selberg axioms provide tensor continuation data but no justified diagonal
trace on the regular part.  The 2026 residue formula proves that the desired prime pairing is
already present as the zero-frequency fixed point of each square fibre.

## Exact open core

Prove a non-circular trace theorem for the **regular part** of `M`, uniform along the unbounded
anti-diagonal and sufficiently uniform as `alpha -> 0` to recover the untwisted Hadamard series near
`w=1`.  The Kaczorowski--Perelli bounded-domain estimates do not provide either uniformity.

## Novelty audit

- Internal search found no reference to the March 2026 multiple-standard-twist paper and no prior
  square-fibre/anti-diagonal residue extraction.
- The source paper states the finite residue formula and multivariable continuation, but does not
  state `(SF)`, connect its zero Fourier mode to Selberg prime pairing, or formulate the
  tangent/transverse degree dichotomy.
- Targeted arXiv searches for `multiple standard twist` with `Hadamard`, `diagonal coefficients`,
  and `anti-diagonal mean` found the source paper but no prior statement of `(SF)`.
- Classification remains **BRIDGE** until a broader citation audit and expert audit are complete.

## References

- J. Kaczorowski and A. Perelli, *Multiple standard twists of L-functions*, J. Number Theory 284
  (2026), 188--213; arXiv:2603.13885.
- K. Soundararajan, *Strong multiplicity one for the Selberg class*, Canad. Math. Bull. 47 (2004),
  468--474; arXiv:math/0210299.

## Log

- 2026-08-14 -- created in Stage 1 after internal-corpus and current-literature audit; three initial
  conjecture/kill/pivot cycles recorded; exact regular-part trace uniformity isolated.

## Loop 3 refinement — degree-weighted tangent trace

**Conjecture.** For unequal degrees, replace the ordinary anti-diagonal by the
tangent flow

```
(s_1, s_2) -> (s_1 + i d_G t, s_2 - i d_F t).
```

It is tangent to the polar hyperplanes with normal `(d_F,d_G)`.  On a finite
Kaczorowski--Perelli fibre its `(m,n)` term has frequency

```
d_G log m - d_F log n,
```

so its Bohr mean survives exactly when `m^d_G = n^d_F`.

**Proof / failure to reach Selberg pairing.** The finite-fibre Fourier proof is
the same as for `(SF)`, with this weighted frequency.  It supplies an exact
degree-resonance trace and stays tangent to polar geometry, but it gives the
same-index condition `m=n` only when `d_F=d_G`.  Thus it cannot establish
Selberg orthogonality for unequal degrees.

**Strongest positive survivor.** The finite residue fibre carries a canonical
degree-resonance trace, selected by the unique polar-tangent direction.  This
is stronger than the earlier geometric dichotomy: it gives the exact surviving
coefficient relation rather than only saying that the ordinary flow is
transverse.

**Lean status.** Scratch formalization of the finite Bohr/Fourier resonance is
in progress.  It must be dependency-closed before this no-go closure can move
to Stage 2.

- 2026-08-15 -- literature audit verified Kaczorowski--Perelli Theorems 1--2
  and their gamma-cleared entire quotient; it also verified that their theorem
  contains no Selberg-orthogonality or prime-correlation implication.  The
  unbounded-flow and `alpha -> 0` uniformity remain the exact open core.
