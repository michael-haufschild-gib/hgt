# Route P complex pointed four-unit polarization

- **ID:** `route-p-complex-pointed-four-unit-polarization`
- **Label:** P-G167
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / SOURCE POLARIZATION
- **RH status:** open
- **Computation used:** no
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePComplexPointedFourUnitPolarization.lean`

## Fresh-corpus synthesis

P-G166 proves that graph-normalized pointed continued-Xi variation is carried by the full-Euler
transverse Fisher source alone; its critical squared norm is four.  P-G159/P-G160 separately prove
that complex logarithmic phases give a genuine non-diagonal Hardy Gram and that four units are the
sharp boundary budget.  The missing composition is to complexify P-G166 before scalar observation,
on the full positive-integer Euler carrier rather than a post-divisor interpolation space.

For `sigma>1`, `Re u>=0`, and `n>=1`, define

```text
h_sigma(u;n)
  = exp(-u (sigma-1) log n) sqrt(P_sigma(n)),
P_sigma(n)=n^(-sigma)/zeta(sigma).
```

Let `T_sigma` be P-G166's centered full-Euler Fisher source.  Conjecture P-G167 is the exact
division-free package

```text
<h_sigma(u),h_sigma(v)>
  = zeta(sigma+(v+conj u)(sigma-1))/zeta(sigma),                 (167.1)

<T_sigma,h_sigma(u)>
  = 2 D_sigma(u)
      [F(sigma+u(sigma-1))-F(sigma)],                            (167.2)
```

where `D_sigma(u)=(sigma-1)` times the Euler overlap and the existing sign convention is absorbed
into `T_sigma=-FisherTangent`.  Thus the augmented
packet `{h_sigma(u_i)} union {T_sigma}` is an actual positive semidefinite Hilbert Gram, not an
assumed kernel.  Division by the nonzero graph denominator yields the holomorphic pointed
prime-current difference, and adding the literal archimedean difference yields the exact pointed
continued-Xi trace at every safe complex node.

## Why this is relevant to the 75% gate

The cubic Hellinger/Bohr receiver needs a positive two-node complex kernel plus an `N/4` source
budget.  P-G167 would supply the missing pre-scalar polarization while preserving exactly the
four-unit transverse source whose boundary accounting predicts that budget.  Imaginary motion is
unitary and therefore carries ordinate dephasing without paying another radial four units.

This does **not** yet prove the `N/4` dyadic Euler--Gamma estimate.  Remaining quantitative theorem
must identify the height-localized second variation of this Gram with the cubic zero energy and
show that Gamma diagonal contributes at most one quarter of the full zero census, with the
summable cubic Euler diagonal contributing lower order.

## Hostile falsifiers

1. If the full-Euler complex overlap is not `(167.1)`, P-G167 is false.
2. If graph normalization introduces a phase-dependent norm cost, four-unit accounting fails.
3. If second variation produces ordinary Hardy/Cauchy power one rather than the cubic kernel after
   the prescribed finite difference, this composition does not feed the 75% receiver.
4. A scalar trace identity alone is insufficient; the Lean artifact must expose an actual Gram and
   prove positive semidefiniteness before scalarization.
5. No coefficient may depend on a Xi zero, zero height, or target interpolation polynomial.
6. Any divisor-mass component left in the reporter pays the orthogonal radial-gauge toll
   `|d|^2`; collapse of the natural `4+|d|^2` budget to four is RH-equivalent.  Therefore the
   proposed source must stay pointed and transverse rather than hide this mode in normalization.

## Conjecture loop

- **C1:** use P-G166 scalar pointed trace directly. **Rejected:** no polarization.
- **C2:** polarize by an abstract rank-one outer product. **Rejected:** receiver theatre; no literal
  source Gram.
- **C3:** complexify the actual full-Euler damped state and retain the same transverse Fisher
  vector. **Selected:** source-defined, coefficient-faithful, and norm-preserving in ordinate.

## Gates

- [x] corpus noncollision and source-provenance audit
- [x] dependency-closed paper algebra for `(167.1)`--`(167.2)`
- [x] Lean complex full-Euler state and summability
- [x] Lean exact non-diagonal overlap
- [x] Lean transverse coefficient and graph-normal Xi reporter
- [x] Lean augmented-Gram positivity
- [x] scratch compile, targeted forbidden-token scan, and axiom audit
- [x] identify cubic second-variation landing (P-G168)
- [ ] global lint (blocked by unrelated unreachable Suzuki modules; Route-P modules are umbrella-wired)
- [ ] prove dyadic `N/4` Euler--Gamma budget
