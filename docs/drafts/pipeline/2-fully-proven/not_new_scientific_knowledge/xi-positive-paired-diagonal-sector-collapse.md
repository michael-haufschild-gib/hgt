# Xi positive-paired diagonal collapses the source matrix gate

- **ID:** `xi-positive-paired-diagonal-sector-collapse`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[TOP-DOWN INTERFACE DISCHARGE]`, `[VALUE RELATION]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal parents:**
  `XiHurwitzOrientationPositivePairedSource.lean`,
  `PrimeArchReciprocalSquareSectorGate.lean`,
  `PrimeArchExactOffLineQuartetAccretivity.lean`

## Statement

Write

```text
T(z)=continuedPrimeArchSourceRelativeTrace(z)
```

on its continued prime--Gamma domain, and let

```text
K+(z,w)=ccmPositivePairedReducedKernel(z,w)
```

be the real one-sided Schwarz-paired Cauchy kernel already formalized in
`XiHurwitzOrientationPositivePairedSource.lean`.  Whenever `Im z != 0` and the displayed
quantities are defined,

```text
K+(z,z)
  =2 Re((conj(T(z))-T(z))/(z-conj(z))+T(z)/z)
  =(2 Re(z)/Im(z)) Im(-T(z)/z).                            (1)
```

Thus its diagonal is exactly the reciprocal-square sector observable from
`PrimeArchReciprocalSquareSectorGate.lean`; it is not an independent source condition.

Let `R >= 0` satisfy `XiOffLineQuartetAccretiveBand R`, and define the exterior diagonal
condition

```text
for every continued-source point z,
  R < Re z and 0 < Im z < 1/2
    -> 0 <= K+(z,z).                                      (2)
```

Then

```text
(2) <-> RiemannHypothesis.                                (3)
```

In particular this applies at the formalized rational radius `R=218/25`.  Consequently, for the
actual reduced source kernel at that radius,

```text
all finite reduced source matrices are positive semidefinite
  <-> every one-point diagonal is nonnegative
  <-> RH.                                                 (4)
```

The first implication in `(4)` is formal matrix specialization.  The reverse implication is not a
generic kernel theorem; it passes through RH using `(3)` and the already formalized RH-to-matrix
positivity theorem.

## Proof of the diagonal identity

Put `z=x+iy` and `T(z)=u+iv`, with `y != 0`.  On the diagonal the definition of the reduced kernel
gives

```text
K+(z,z)/2
  =Re((conj(T)-T)/(z-conj(z))+T/z)
  =-v/y+Re(T/z).
```

Since

```text
Re(T/z)=(u x+v y)/(x^2+y^2),
Im(-T/z)=(u y-v x)/(x^2+y^2),
```

one obtains

```text
-v/y+Re(T/z)=(x/y) Im(-T/z),
```

which is `(1)`.

## Exterior local-pole theorem

Assume RH fails.  Choose an off-critical Xi divisor point and use functional-equation and Schwarz
symmetry so that its centered spectral coordinate `alpha` satisfies

```text
0 < Im alpha < 1/2,
0 < Re alpha.
```

The exact off-line quartet height law gives the stronger inequality

```text
R+1/2 < Re alpha.                                         (5)
```

Let `m>0` be the multiplicity at `alpha`.  Along regular horizontal points

```text
z_t=alpha+t,  t<0,  t -> 0,
```

the normalized logarithmic-derivative pole law gives

```text
t*(-logDeriv(XiC)(z_t)/z_t) -> -m/alpha,
Im(-m/alpha)=m Im(alpha)/|alpha|^2>0.                     (6)
```

For all sufficiently small negative `t`, `(5)` keeps `Re z_t>R`, while `(6)` gives

```text
Re(z_t)*Im(-logDeriv(XiC)(z_t)/z_t)<0.                    (7)
```

The regular points `z_t` lie in the continued prime--Gamma domain and there
`T(z_t)=logDeriv(XiC)(z_t)`.  Since `Im z_t>0`, equations `(1)` and `(7)` yield

```text
K+(z_t,z_t)<0,
```

contradicting `(2)`.  Hence `(2)` implies RH.

Conversely, RH makes the complete Xi Weil Hilbert quadratic form nonnegative.  The formal theorem
`xiWeilHilbertQuadratic_positivePairedCauchy_eq_reducedKernel` identifies its value on one paired
Cauchy generator with `K+(z,z)`, proving `(2)`.

## Countable value family

Condition `(2)` may be restricted to continued-source points with Gaussian-rational real and
imaginary parts.  Indeed, `K+(z,z)` is continuous on the open regular source domain.  If it were
negative at one regular exterior point, it would remain negative on a small open ball contained in
that domain, and the ball would contain a Gaussian-rational point.  Therefore

```text
K+(z,z)>=0 on all regular Gaussian-rational points with
R<Re z and 0<Im z<1/2
  -> (2)
  -> RH.                                                  (8)
```

This is a countable scalar value family.  It contains no coefficient vectors, off-diagonal kernel
entries, limiting measures, or zero-selected test point.

## What this discharges

The previous one-sided source target required positive semidefiniteness of every finite matrix

```text
(K+(z_i,z_j))_(i,j).
```

That is no longer the smallest sufficient hypothesis.  The exact remaining source target can be
stated as the scalar inequality

```text
2 Re((conj(T(z))-T(z))/(z-conj(z))+T(z)/z) >= 0            (9)
```

only at positive exterior regular points, or even only at the countable Gaussian-rational family
in `(8)`.  By `(1)`, this is also the positive-frequency exterior part of the reciprocal-square
sector sign.  The quartet height law ensures that every hypothetical off-line pole is already in
that exterior region, so no central-band propagation theorem is needed for the implication to RH.

## Non-circularity boundary

The theorem does not prove `(9)`.  It proves that finite source-matrix passivity, algebraic-span
positivity, and off-diagonal Cauchy relations are unnecessary for this route.  A valid provider for
`(9)` must come from the explicit prime sum plus Gamma boundary expression for `T(z)` and may not
use Xi zero locations, Weil positivity, a real-rootedness assumption, or an RH-equivalent limiting
measure.

The reduction is classified as a bridge.  Diagonal positivity does not imply kernel positivity in
general reproducing-kernel or generalized Nevanlinna theory; the collapse here uses the special Xi
quartet height gap and the signed local pole of the exact source function.  No scientific novelty
claim is made.

## Formalization target

1. **Done in Lean:** prove the algebraic identity `(1)` from
   `ccmPositivePairedReducedKernel` and `continuedPrimeArchReciprocalSquareTrace`; the same module
   identifies the reciprocal-square trace with `normalizedPrimeArchMomentGerm` away from zero.
2. **Done in Lean:** strengthen the local pole theorem to retain an arbitrary neighborhood of the
   zero and hence any strict exterior lower bound below `Re alpha`.
3. **Done in Lean:** combine that refinement with
   `xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine` and the Xi symmetries.
4. **Done in Lean:** package `(3)` at a general exact quartet radius and at `218/25`.
5. **Done in Lean:** identify diagonal passivity with the existing finite-matrix passivity through
   the two Xi-specific RH capstones.

## Gates

- [x] exact diagonal/sector value relation proved on paper
- [x] exterior local-pole contradiction proved on paper
- [x] full matrix condition reduced to scalar diagonal values
- [x] scalar family reduced to a countable dense source family
- [x] formalize the diagonal identity and its moment-germ form in Lean
- [x] formalize the exterior-preserving local pole refinement
- [x] formalize the diagonal criterion and matrix-collapse capstones
- [ ] prove the prime--Gamma scalar inequality `(9)`
- [ ] prove RH

## Literature calibration

The classical reproducing-kernel criterion requires positivity of every finite Gram matrix, not
merely nonnegativity of its diagonal; see Aronszajn, *Theory of Reproducing Kernels*,
[DOI 10.1090/S0002-9947-1950-0051437-7](https://doi.org/10.1090/S0002-9947-1950-0051437-7).
The indefinite analogue organizes kernels by their finite number of negative squares rather than by
diagonal signs; see Krein--Langer, *Über einige Fortsetzungsprobleme, die eng mit der Theorie
hermitescher Operatoren im Raume \(\Pi_\kappa\) zusammenhängen. Teil I*,
[DOI 10.1002/mana.19770770116](https://doi.org/10.1002/mana.19770770116).
The semilocal Weil-form setting and its prime-place trace architecture are supplied by
Connes--Consani--Moscovici, *On the Scaling Hamiltonian*,
[arXiv:2310.18423](https://arxiv.org/abs/2310.18423),
[DOI 10.1007/s43034-024-00388-z](https://doi.org/10.1007/s43034-024-00388-z).

These sources do not provide a generic diagonal-to-kernel-positivity implication, nor was an exact
published instance of identity `(1)` for the Xi continued prime--Gamma source located.  The present
collapse is therefore recorded conservatively as a project bridge: its proof uses the Xi-specific
quartet height bound and the signed local-pole limit, while its unsolved input remains the explicit
source inequality `(9)`.
