# Von Mangoldt--Gamma pointed Ward reconstruction and Bianchi Gram

- **ID:** `von-mangoldt-gamma-pointed-ward-bianchi-gram`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean), POINTED SOURCE/Bianchi GRAM PRODUCER
- **Scientific status:** `[PROVED] [LEAN-VERIFIED] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `von-mangoldt-gamma-bivariate-hausdorff-moment.md`
- **Cofinal child:** `von-mangoldt-gamma-cofinal-pointed-ward-euler-germ.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaPointedWardReconstruction.lean`

## Theorem

For one rate `lambda`, put

```text
I_b(lambda)=integral_[0,1] u^b exp(-lambda(1-u)) du.
```

The pointed unit-interval Ward law is

```text
lambda I_(b+1)(lambda)+(b+1)I_b(lambda)=1.               (1)
```

It is the fundamental theorem of calculus applied to
`u^(b+1) exp(-lambda(1-u))`: the left endpoint vanishes and the upper endpoint is the source
point `1`.

For the finite exponential source, let

```text
S_x(a)=sum_p q_p exp(-x lambda_p) lambda_p^a
```

and let `B_x(a,b)` be the fixed bivariate Gamma-remainder moment from the parent theorem.  Summing
`(1)` over the source gives the exact positive reconstruction

```text
S_x(a)=B_x(a+1,b+1)+(b+1)B_x(a,b),                       (2)
```

for every `a,b`.  Thus every raw Euler logarithmic jet is the pointed boundary of the same
bivariate integral object, expressed as a sum of two nonnegative interior moments.

Let `A_N(i)` be the finite von Mangoldt--Gamma anomaly and choose `b<N`.  The reverse indices at
depths `N` and `N+1` select the same physical coordinate.  Combining `(2)` with the exact anomaly
dictionary gives

```text
S_x(N)
 =(b+1)! (-1)^N Re(
     A_(N+1)(N-1-b)-A_N(N-1-b)).                         (3)
```

Every nonempty aperture has `S_x(N)>0`; hence the adjacent-depth Bianchi current in `(3)` is
strictly oriented at every depth and coordinate.

The matrix strengthening is the principal result.  For arbitrary exponent maps `a_i,b_i` with

```text
b_i+b_j<a_i+a_j,
```

form the matrix whose `ij` entry is the right side of `(3)` at
`N=a_i+a_j`, `b=b_i+b_j`.  Lean proves the exact identity

```text
C_ij=S_x(a_i+a_j)=<v_i,v_j>,

v_i(p)=sqrt(q_p exp(-x lambda_p)) lambda_p^(a_i).        (4)
```

Consequently every such mixed adjacent-depth Bianchi matrix is positive semidefinite.  Equation
`(4)` is an explicit source Stinespring feature map, not positivity inferred from a target Xi
kernel.

## What this closes

The parent bivariate theorem represented each Gamma anomaly coordinate by a common positive
integral kernel.  The present theorem adds the missing point and boundary map:

1. the unit-interval endpoint reconstructs every raw logarithmic source jet;
2. adjacent Gamma depths are connected by the exact Bianchi boundary current;
3. the current is strictly oriented coordinatewise for every nonempty aperture;
4. arbitrary mixed Bianchi currents form one literal raw-source Gram;
5. the finite Bianchi environment therefore has an explicit positive feature realization.

This is the finite pointed compatibility layer demanded by source-anomaly dilation proposals.  It
does not construct their unbounded inverse incidence or critical corona limit.

The cofinal child now closes the aperture limit and identifies the limiting Gram entrywise with
the analytic logarithmically weighted Euler germ.  Thus the remaining gap is not finite-to-infinite
source reconstruction; it is inverse-critical coupled transport.

## Anti-theatre and novelty gate

The calculus and Gram ingredients are classical, and `(3)` is compatible with the existing
algebraic Bianchi identity.  The project-specific contribution is the exact common-measure
dictionary `(1)--(4)` for the von Mangoldt--Gamma clock.  It is classified as a corpus bridge, not
new scientific knowledge and not an RH result.

The theorem is stronger than repackaging coordinate positivity: a single mixed matrix can contain
different Gamma depths, and its equality with the raw source Gram is exact.  It is weaker than the
critical theorem: all objects in `(1)--(4)` remain finite and on the absolute-Euler source side.

## RH boundary

The direct coefficient-energy transport cannot be used: inverse half-translation multiplies the
prime channels by `p^(1/2)` and is uniformly expansive.  Equation `(4)` supplies the positive
Gamma Bianchi environment that a coupled completion may use to absorb this expansion, but it does
not prove that the absorption occurs.

The remaining chain is

```text
fixed bivariate von Mangoldt--Gamma measure                         PROVED
  -> pointed Ward reconstruction of raw Euler jets                 PROVED
  -> positive mixed Gram for the Gamma Bianchi environment         PROVED
  -> cofinal analytic Euler-germ reconstruction                     PROVED
  -> [OPEN] assemble the source-Julia and Bianchi feature legs
       into the unbounded channel-resolved inverse incidence
  -> [OPEN] identify the shifted-polar/critical-Mellin environment
       and prove the completed defect is a positive compression
  -> normalized prime--Gamma/Xi Hankel positivity
  -> RH.                                                           (5)
```

The next theorem must control the cross terms of the coupled inverse incidence.  Taking the direct
sum of the positive source-Julia Gram and `(4)` would discard exactly those cross terms and would
not imply RH.

## Lean certificate

Principal declarations:

- `exponentialRemainderMoment_pointedWard`
- `finiteExponentialGammaRawMoment_eq_pointedWard`
- `finiteVonMangoldtGammaRawMoment_eq_anomalyBianchi`
- `finiteVonMangoldtGammaAnomalyBianchi_oriented_re_pos`
- `finiteExponentialGammaRawGram_apply`
- `finiteVonMangoldtGammaAnomalyBianchiMixedGram_eq_rawGram`
- `finiteVonMangoldtGammaAnomalyBianchiMixedGram_posSemidef`

Verification:

- exact target build passed;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- no numerical computation;
- no RH or target-positivity hypothesis.

## Gates

- [x] exact pointed Ward boundary law
- [x] raw source-jet reconstruction from two bivariate moments
- [x] exact adjacent-depth anomaly/Bianchi identity
- [x] strict finite-aperture Bianchi orientation
- [x] explicit raw-source feature map
- [x] arbitrary mixed-depth Bianchi Gram positivity
- [x] cofinal analytic Euler-germ reconstruction (child theorem)
- [x] unconditional Lean formalization
- [x] exact build and axiom audit
- [ ] unbounded channel-resolved inverse incidence
- [ ] coupled Gamma/polar/Mellin positive defect
- [ ] critical Xi Hankel positivity
- [ ] RH
