# Prime-shift residue graph criterion for RH

- **ID:** `prime-shift-residue-closability-criterion`
- **Stage:** 2-fully-proven / not-new
- **Type:** theorem (paper), `[BRIDGE]`
- **Statement:** There is a canonical densely defined linear residue functional on the vanishing-tail
  subspace `M_0` of the logarithmic Marcinkiewicz prime-tail space.  It is invariant under finite
  Euler units, and it is closable if and only if the Riemann hypothesis holds.  Every hypothetical
  right-half zero supplies an explicit sequence converging to zero on which the functional has
  constant nonzero value.  The closability equivalence is an instance of a general dense-kernel
  graph lemma, so it is an exact RH encoding rather than a new proof mechanism.

## Grade-one prime source

Let

```text
Q(s)=sum_p (log p)p^(-s),        Re s>1.                  (1)
```

Prime-zeta Möbius inversion gives, with `A=-zeta'/zeta`,

```text
Q(s)=sum_(k>=1) mu(k)A(ks).                              (2)
```

On the open right strip

```text
S_+={z : 1/2<Re z<1},                                    (3)
```

every term with `k>=2` is holomorphic because `Re(kz)>1`.  Hence `Q` has a canonical meromorphic
continuation to `S_+`, and

```text
Res_(s=z) Q(s) = -ord_z(zeta).                            (4)
```

The fixed archimedean completed-flux channel is holomorphic on `S_+`, so (4) is also the complete
nontrivial-zero residue of the prime--archimedean source.

## Shift characters

For `z in S_+`, define the normalized prime character

```text
tau_z(p)=p^(1/2-z).                                       (5)
```

It lies in `M_0`, the closure of finite-support fields in the logarithmic Marcinkiewicz space:

```text
sum_p (log p)/p * |tau_z(p)|
  = sum_p (log p)p^(-1-(Re z-1/2)) < infinity.            (6)
```

The associated grade-one prime series is an exact shift:

```text
sum_p (log p)tau_z(p)p^(-s)
  = Q(s+z-1/2).                                           (7)
```

Thus its residue at the fixed critical base `s=1/2` is

```text
r(z):=Res_(s=1/2) Q(s+z-1/2)
     =Res_(w=z)Q(w)
     =-ord_z(zeta).                                       (8)
```

No zero is inserted into the definition: `r(z)` is defined for every point of the right strip and
is zero except at poles of the fixed continued prime source.

## Algebraic independence modulo finite support

Let `E` be the complex span of the characters `tau_z`, `z in S_+`.  Distinct characters are
linearly independent modulo finite support.

Indeed, suppose

```text
sum_(j=1)^N c_j tau_(z_j)
```

vanishes at every sufficiently large prime.  Then the exponential polynomial

```text
F(w)=sum_(j=1)^N c_j exp((1/2-z_j)w)                      (9)
```

vanishes at every sufficiently large `w=log p`.  A nonzero exponential polynomial has only
`O(R)` zeros in `|w|<=R`, while there are `pi(exp R)` prime logarithms in that disk.  Hence `F=0`.
Linear independence of distinct exponentials gives every `c_j=0`.

Consequently

```text
E intersect c00(Primes)=0.                               (10)
```

## Canonical residue functional

On the algebraic domain

```text
D_res=c00(Primes) direct_sum E  subset M_0,               (11)
```

define

```text
R_res(f + sum_j c_j tau_(z_j))
  = sum_j c_j r(z_j).                                     (12)
```

Equation (10) makes this well-defined, and (8) makes it canonical.  Since `c00` is dense in `M_0`
by definition, `D_res` is dense in `M_0`.  It is **not** dense in `M_log`: equation (6) puts every
generator of `E` in `M_0`, while the unit Euler field has nonzero class in `M_log/M_0`.

The functional vanishes on every finite prime field, so finite Euler-factor changes do not alter
it.  It is not a chosen Banach limit or a Hahn--Banach extension; it is the residue of the uniquely
continued grade-one prime source after the exact shift (7).

## Closability theorem

The following are equivalent:

```text
(i)   the Riemann hypothesis holds;
(ii)  R_res is the zero functional on D_res;
(iii) R_res is closable as a densely defined linear functional
      M_0 -> C.                                           (13)
```

### RH implies zero

Under RH, zeta has no zero in `S_+`.  Equation (4) gives `r(z)=0` for every `z in S_+`; therefore
`R_res=0`.  The zero functional is closable.

### Non-RH gives an explicit nonclosability sequence

If RH fails, FE and Schwarz symmetry supply a zeta zero `rho in S_+` of multiplicity `m>=1`.
Equation (8) gives

```text
R_res(tau_rho)=-m.                                       (14)
```

Let `tau_rho^(Y)` be the finite truncation retaining only primes `p<=Y`.  By (6),

```text
x_Y=tau_rho-tau_rho^(Y) -> 0 in M_0.                     (15)
```

But `tau_rho^(Y)` lies in `c00`, so

```text
R_res(x_Y)=-m                                             (16)
```

for every `Y`.  A closable linear functional must send every domain sequence converging to zero,
whose images converge, to image limit zero.  Equations (15)--(16) contradict closability.

Thus (iii) implies RH, completing (13).

### Abstract graph lemma

The closure mechanism is completely general.  Let `X` be a topological vector space, let `C` be a
dense linear subspace, let `D` be a linear domain containing `C`, and let `L : D -> K` be linear into
a Hausdorff scalar field with `L|_C=0`.  Then

```text
L is closable  iff  L=0.                                 (17)
```

Indeed, for `x in D`, choose `c_n in C` with `c_n -> x`.  Then `x-c_n -> 0` and
`L(x-c_n)=L(x)`.  Closability forces `L(x)=0`.  The converse is immediate.  Apply this with
`X=M_0`, `C=c00`, `D=D_res`, and `L=R_res`.

## Positive interpretation

The theorem constructs the canonical dual incidence assignment that the bounded quotient could not
supply.  It is necessarily singular:

```text
right-half zero
  <-> a null sequence of prime tails carrying a nonzero fixed residue
  <-> nonclosability of R_res.                            (18)
```

This is a static description of the graph defect of a source-defined functional.  There is no
evolution parameter, operator spectrum, positivity cone, or zero enumeration.  The finite
truncations in (15) are proof witnesses only; they are not promoted to a carrier or limiting model.

## Relation to the infinite-jet image

The exact infinite-jet classifier first extracts the unique von Mangoldt coefficient field from a
completed flux jet.  That field determines `Q` and therefore `R_res`.  Hence closability is an
all-order compatibility of the **classified source image plus its global divisor**, not a separate
condition imposed on an arbitrary realizer.

The chain is now exact:

```text
infinite completed-flux jet
  -> extracted von Mangoldt ray field
  -> continued grade-one source Q
  -> canonical shift-residue graph R_res
  -> closability iff RH.                                  (19)
```

## Attack and route verdict

The equivalence (13) does not create a new RH route.  By (17), proving closability from any premise
is exactly proving that every residue value vanishes.  Continuity, boundedness, simultaneous
FE-character membership, or absence of right-strip poles therefore inserts RH-strength directly.

The Euler ray equations alone cannot repair this graph.  Every `tau_z` with `Re z>1/2` belongs to
`M_0`, and its finite truncations are valid finite Euler parameter fields converging to it.  Passing
to all prime-power grades preserves this approximation coordinatewise and in every ordinary
absolutely weighted grade topology.  Thus the ray algebra supplies no closed condition separating
an off-line residue character from finite Euler data.

The positive conclusion is a separation theorem for the research program:

```text
the surviving unit source tail lives in M_log/M_0;
every right-half residue character lives in M_0;
the canonical residue graph is densely defined only on M_0.                (20)
```

A genuine source--divisor incidence constraint must couple these two complementary pieces.  It
cannot be obtained by declaring the `M_0` residue graph closable.

The source pole at `s=1` does not create a false witness because the shift domain is the strict
strip `1/2<Re z<1`; the known pole direction `z=1` is excluded.  Scaled prime-zeta singularities
`rho/k` with `k>=2` lie at `Re<=1/2` when `rho` is a nontrivial zero, so they are excluded as well.

## Scientific status

This is `[BRIDGE]`, not new scientific knowledge.  Its parents are classical prime-zeta Möbius
inversion, exponential-polynomial independence, Marcinkiewicz tail spaces, and the abstract graph
lemma (17).  The exact source notation is project-specific, while the mechanism is routine once the
domain and dense kernel are identified.

Its research value is negative only in wording but positive in content: it classifies the residue
reader as a vanishing-tail graph object and proves that the nonzero Euler tail and the off-line
residue witness occupy complementary topological layers.  The next object must be a nonlocal
incidence law coupling those layers.
