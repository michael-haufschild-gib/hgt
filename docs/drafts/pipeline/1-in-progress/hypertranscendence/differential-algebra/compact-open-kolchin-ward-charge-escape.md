# Compact-open Kolchin blindness and quantized Ward charge escape

- **ID:** `compact-open-kolchin-ward-charge-escape`
- **Stage:** 1-in-progress
- **Type:** THEOREM / HT GEOMETRY / RIEMANN-DIVISOR NO-GO
- **Scientific status:** `[PAPER PROOF COMPLETE] [NOVELTY AUDIT ACTIVE] [LEAN CONNECTOR MISSING]`
- **Scope:** exact boundary on hypertranscendence-based and compact-open local approaches to
  Riemann-divisor exclusion

## Question answered

Can completed functional symmetry, Schwarz symmetry, real-axis positivity, hypertranscendence,
the complete even-shift differential matroid over every scalar Euler valuation layer, and
arbitrarily accurate local knowledge of every holomorphic jet exclude an off-critical
functional-equation orbit?

No.  There is an explicit sequence with all those data fixed or convergent, but with one
off-critical quartet at every stage.  Its positive Ward density disappears uniformly from every
bounded height window while retaining the exact total mass `8 pi`.  The obstruction is therefore
a noncompact, source-marked divisor charge, not missing differential-algebraic complexity.

## Exact family

Fix `0 < a < 1/2`.  For `b > 0`, put

```text
z = s - 1/2,
Q_(a,b)(s) = (((z-a)^2+b^2) ((z+a)^2+b^2)),
G_(a,b)(s) = Q_(a,b)(s) / b^4,
F_(a,b)(s) = G_(a,b)(s) xi(s).
```

Let `b_n -> +infinity`; the canonical sequence is `b_n=n+1`.

The added strict-right upper point is

```text
rho_(a,b)=1/2+a+i b.
```

Its Euler-edge Ward density is

```text
W_(a,b)(t)
 = 2 [
     2(a+1/2)/((a+1/2)^2+(t+b)^2)
     +
     2(a+1/2)/((a+1/2)^2+(t-b)^2)
   ].
```

## Main theorem

For every fixed `a` with `0<a<1/2`:

1. **Exact completed symmetries and positivity.**  Every `F_(a,b)` is entire,
   hypertranscendental, satisfies

   ```text
   F_(a,b)(1-s)=F_(a,b)(s),
   F_(a,b)(conj s)=conj(F_(a,b)(s)),
   ```

   and has positive gauge on the real axis.  It contains the off-critical quartet

   ```text
   1/2 +/- a +/- i b
   ```

   with multiplicity one in the gauge.

2. **Compact-open all-jet invisibility.**

   ```text
   G_(a,b_n) -> 1,
   F_(a,b_n) -> xi
   ```

   locally uniformly on `C`.  For every derivative order `j`,

   ```text
   d^j F_(a,b_n) -> d^j xi
   ```

   locally uniformly.  On compact sets the complete logarithmic source correction

   ```text
   G'_(a,b_n)/G_(a,b_n)
   ```

   and all of its derivatives converge locally uniformly to zero.

3. **Exact Kolchin blindness.**  Multiplication by `G_(a,b)` is a nonzero rational base gauge,
   hence

   ```text
   C(s)<F_(a,b)>_differential = C(s)<xi>_differential.
   ```

   More strongly, write

   ```text
   D_m(f)(s) = (f'/f)(s+2m) - (f'/f)(s),  m>=1.
   ```

   Then

   ```text
   D_m(F_(a,b)) = D_m(xi) + r_(m,a,b),   r_(m,a,b) in C(s).
   ```

   Therefore every finite even-shift differential matroid, every generated differential field,
   and every differential-independence statement is identical for `F_(a,b)` and `xi`, both over
   `C(s)` and after adjoining all scalar prime-valuation layers.  In particular the maximal
   all-valuation Kolchin rank of the actual Xi even-shift frame survives every quartet surgery.

4. **Rank-one singular fracture.**  Let `S={0<Re(s)<1}`, `R=C[partial]`, and take a finite
   nonempty packet `I` of positive even-shift labels.  Modulo functions holomorphic on `S`,

   ```text
   [D_m(F_(a,b))]=[-F'_(a,b)/F_(a,b)]
   ```

   for every `m in I`.  The map

   ```text
   Phi_I : R^I -> meromorphic(S)/holomorphic(S),
   (P_m) |-> [sum_m P_m(partial) D_m(F_(a,b))]
   ```

   has

   ```text
   ker Phi_I = {(P_m): sum_m P_m=0},
   im Phi_I  = R[-F'_(a,b)/F_(a,b)].
   ```

   Thus maximal arithmetic differential rank collapses under the principal-part functor to one
   free singular mode, with kernel the `A_(|I|-1)` root module.  That unique common mode carries
   the complete divisor with multiplicity.

5. **Quantized charge escape.**

   ```text
   W_(a,b)(t) >= 0,
   integral_R W_(a,b)(t) dt = 8 pi
   ```

   for every `b>0`.  Nevertheless, for every `R>=0` and `b>R`,

   ```text
   sup_(|t|<=R) W_(a,b)(t) <= 8/(b-R)^2.
   ```

   Hence `W_(a,b_n)` converges uniformly to zero on every bounded height window although its
   total mass remains exactly one `8 pi` quantum.  The charge is not destroyed; it escapes to
   the height boundary.

6. **Source marking is complete for the finite defect.**  The rational logarithmic correction

   ```text
   q_(a,b)=G'_(a,b)/G_(a,b)
   ```

   has simple poles of residue one at the four inserted points.  Uniqueness of rational polar
   parts recovers the full finite quartet, including location and multiplicity, from `q_(a,b)`.
   The Ward density is its positive strict-right boundary projection, and its mass is the
   augmentation character `8 pi` on the quartet monoid.

## Proof

### Symmetry, positivity, and hypertranscendence

In the centered coordinate `z=s-1/2`, the polynomial `Q_(a,b)` is even and has real
coefficients.  Hence it is fixed by `s |-> 1-s` and commutes with complex conjugation.  On the
real axis both quadratic factors are strictly positive because `b>0`.  Its four roots are
`z=+/-a+/-i b`.  Multiplication of a hypertranscendental analytic function by a nonzero
polynomial preserves hypertranscendence.

### Compact-open convergence

The normalized gauge has the exact expansion

```text
G_(a,b)(s)
 = (1+(z-a)^2/b^2)(1+(z+a)^2/b^2)
 = 1 + 2(z^2+a^2)/b^2 + (z^2-a^2)^2/b^4.             (1)
```

On every compact set, `z` is bounded.  Equation `(1)` and each of its finitely many derivatives
converge uniformly to the corresponding derivative of `1`.  Multiplication by the fixed entire
function `xi` gives locally uniform convergence of `F_(a,b)`; holomorphic jet convergence gives
all derivative orders.

For sufficiently large `b`, `(1)` is uniformly separated from zero on any prescribed compact.
Since `G'_(a,b)` and all its derivatives converge uniformly to zero there, the quotient rule
gives locally uniform convergence of every derivative of `G'_(a,b)/G_(a,b)` to zero.

### Differential-field invariance

Because `G_(a,b)` and its inverse belong to `C(s)`,

```text
F_(a,b)=G_(a,b) xi,
xi=G_(a,b)^(-1) F_(a,b),
```

so the generated differential fields coincide.  Logarithmic differentiation gives

```text
F'_(a,b)/F_(a,b) = xi'/xi + G'_(a,b)/G_(a,b).
```

Taking an even-shift difference proves the displayed affine-gauge formula for `D_m`.  Addition
of a base-field family preserves differential adjunction, differential independence, and the
represented differential matroid.  The complete scalar valuation-layer field contains the
rational coordinate field, so the same conclusion holds over that larger base.

### Singular rank fracture

For `m>=1` and `s in S`, `Re(s+2m)>1`.  Both `xi(s+2m)` and
`G_(a,b)(s+2m)` are nonzero, since all gauge roots have real part in `(0,1)`.  Thus the shifted
logarithmic derivative is holomorphic on `S`, giving

```text
[D_m(F_(a,b))]=[-F'_(a,b)/F_(a,b)].
```

Let `P=sum_m P_m`.  Then

```text
[sum_m P_m(partial)D_m(F_(a,b))]
  =[-P(partial)(F'_(a,b)/F_(a,b))].
```

At any gauge zero `rho`, the logarithmic derivative has principal part `1/(s-rho)`.  If `P` has
degree `r` and leading coefficient `c_r != 0`, then
`P(partial)(F'/F)` has a pole of order `r+1` with leading coefficient
`c_r (-1)^r r!`; lower derivatives cannot cancel it.  Hence the class is zero only if `P=0`.
This proves the kernel and image.  The kernel of coefficient summation is generated by
`e_m-e_n`, the root module.

### Ward quantization and escape

Each summand of `W_(a,b)` is a positive Lorentzian.  Translation invariance and

```text
integral_R 2x/(x^2+t^2) dt = 2 pi
```

give total mass `8 pi`.

Put `x=a+1/2`; then `0<x<1`.  If `|t|<=R<b`, both
`|t+b|` and `|t-b|` are at least `b-R`.  Dropping the positive `x^2` terms and using `x<1`
gives

```text
W_(a,b)(t)
 <= 2(2/(b-R)^2+2/(b-R)^2)
 = 8/(b-R)^2.
```

The right side tends to zero for every fixed `R`, proving compact-window escape.

### Polar completeness

For a polynomial with simple roots,

```text
Q'/Q = sum_rho 1/(s-rho).
```

If two finite polar sums agree, their difference is a vanishing rational polar sum.
Uniqueness of partial fractions forces equality of every pole and residue.  Thus the marked
source correction recovers the quartet exactly, while the unmarked differential field does not.

## Consequences

### Differential-algebraic zero-exclusion no-go

No criterion invariant under rational differential gauge—and therefore no criterion depending
only on hypertranscendence, differential transcendence degree, generated differential fields,
finite or countable shift matroids, or their all-valuation Euler-layer refinements—can imply
critical-line zero exclusion on this natural completed-symmetry class.

This is stronger than observing that functional equations alone do not imply RH: the complete
known hypertranscendental shift geometry is held fixed.

### Compact-local zero-exclusion no-go

No finite-height or compact-open all-jet stability argument can supply the missing exclusion.
The counterexamples converge to Xi through every local holomorphic jet while a full divisor
quantum moves to infinity.  A successful route must control a source-marked boundary at infinity,
not add more local jets.

### Exact positive successor

The correct object is the source-marked common singular mode

```text
d log f  modulo holomorphic source gauges,
```

with its residue divisor and Ward boundary measure retained before passage to the unpointed
differential field.  The law identifies this object and proves its finite-defect completeness;
it does not assert RH.

## Literature boundary

- Gauthier--Xarles prove that arbitrarily small functional-equation-preserving perturbations of
  L-functions may satisfy or fail the corresponding RH, even generically.  Their theorem does not
  keep the complete differential field or actual all-valuation Xi shift matroid fixed, does not
  identify the rank-one principal-part fracture, and has no quantized Ward/source index.
- Chiang--Feng prove difference independence of the Riemann zeta function over small-growth
  meromorphic coefficients.
- Ostrowski--Mordukhai-Boltovskoi and later Gamma--zeta independence results establish
  hypertranscendence and differential independence, but do not locate which quotient carries the
  Riemann divisor.
- Classical uniqueness of partial fractions and the Poisson-kernel integral supply ingredients,
  not the combined Kolchin-blindness/charge-escape theorem.

Primary novelty search has not found the exact theorem.  Absence from search is not proof of
priority; the final paper must state the scope narrowly and cite the perturbation literature as
the closest predecessor.

## Hostile significance audit

The theorem fails publication-level significance if presented as any one of:

- “multiplying by a polynomial preserves hypertranscendence”;
- “functional equations do not imply RH”;
- “a translated Poisson kernel has constant mass”;
- “partial fractions recover poles.”

Its irreducible content is the simultaneous law:

```text
identical complete all-valuation Kolchin geometry
  + compact-open convergence of every holomorphic/source jet
  + arbitrary off-critical quartet at every stage
  + exact rank-one singular quotient
  + one conserved 8 pi charge escaping every bounded height window.
```

The result is a scoped no-go for hypertranscendence-based zero exclusion and a positive
classification of the missing datum.  It is not a proof of RH, not a no-go for source-marked
methods, and not a no-go for Hilbert--Polya in general.

## Gates

- [x] dependency-closed paper proof
- [x] explicit compact-window escape bound
- [x] exact differential-gauge scope
- [x] rank-one principal-part theorem
- [x] positive source-marked successor
- [ ] primary-source novelty audit complete
- [ ] exact Lean connector for normalized compact-open family and escape bound
- [ ] exact Lean connector for even-shift rational-gauge invariance
- [ ] exact Lean connector for singular rank fracture
- [ ] publication-ready manuscript with no formalization mentioned
- [ ] antagonistic general-journal review

