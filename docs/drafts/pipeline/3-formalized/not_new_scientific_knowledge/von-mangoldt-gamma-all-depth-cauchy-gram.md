# Von Mangoldt--Gamma all-depth Cauchy Gram

- **ID:** `von-mangoldt-gamma-all-depth-cauchy-gram`
- **Stage:** 3-formalized
- **Type:** `[SOURCE-SPECIFIC POSITIVITY]`, `[FINITE GAUSS--WARD PACKET]`, `[BRIDGE]`
- **Scientific status:** `[PROVED LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaAllDepthCauchy.lean`.
- **Parents:**
  `von-mangoldt-gamma-all-depth-oriented-anomaly.md`;
  `../../2-fully-proven/not_new_scientific_knowledge/von-mangoldt-gamma-clock-descent-anomaly.md`;
  `../../1-in-progress/prime-gamma-reflection-decimation-defect-resolvent-rh.md`.
- **Statement:** The full finite von Mangoldt--Gamma descent anomaly admits a source-defined
  positive Cauchy Gram simultaneously over all resolved source atoms and all Gamma-jet
  coordinates.  Restoring the second source-mass square root recovers each actual oriented
  anomaly numerator exactly.

## Exact finite packet

Put

```text
R_m(lambda)=(-1)^(m+1)
  (sum_(h<m)(-lambda)^h/h!-exp(-lambda)).               (1)
```

For source weights `q_p>=0`, rates `lambda_p`, depth `N`, and `i<N`, define

```text
A_(N,i)(w;p)
 =sqrt(q_p) lambda_p^i R_(N-i)(lambda_p)/(w+lambda_p).  (2)
```

The formalized all-coordinate anomaly identity gives

```text
sqrt(q_p)(w+lambda_p)A_(N,i)(w;p)
 =(-1)^(N+1) Re(alpha_N(e_p)_i)                         (3)
```

at base point zero whenever the denominator is nonzero.  Thus `(2)` is not an independently
chosen positive proxy: its numerator is the square-root polarization of the actual source-to-Gamma
comparison anomaly.

For any finite Cauchy point packet `w_a`, form the source vector indexed by `(p,i)` and its Gram

```text
G_(a,b)=sum_(p,i)
  A_(N,i)(w_a;p) conjugate(A_(N,i)(w_b;p)).             (4)
```

Lean proves `G>=0` for arbitrary finite source and point sets.  With

```text
q_n=Lambda(n)/n,       lambda_n=log n,                  (5)
```

this gives the unconditional finite all-prime-power/Gamma-jet packet required on the interior of
the von Mangoldt Hilbert scale.

## Two-boundary balanced compression

The operator-theoretic Weil formulation uses the two Mellin balance conditions at characters
`+1/2` and `-1/2`.  The finite anomaly packet now carries their exact source-side analogue.  Let

```text
B_(M,N)=span{A_(M,N)(+1/2),A_(M,N)(-1/2)}               (6)
```

inside the joint finite prime-power/Gamma-coordinate Hilbert space, and define

```text
A_bal(w)=Proj_(B_(M,N)^perp) A(w).                      (7)
```

Lean proves

```text
A_bal(+1/2)=A_bal(-1/2)=0,                              (8)
<A_bal(w),A(+1/2)>=<A_bal(w),A(-1/2)>=0,                (9)
Gram(A_bal(w_a))>=0.                                    (10)
```

Thus the finite causal/polar charge modes can be removed canonically without choosing Xi zeros,
postulating common-charge vanishing, or losing positivity.  This does not prove that the
RH-faithful divisor seam charge vanishes.  It constructs a source domain on which both boundary
functionals vanish before the divisor comparison is made.

This choice is aligned with Connes--Consani's operator-theoretic formulation in
[The Scaling Hamiltonian](https://arxiv.org/abs/1910.14368), where Weil positivity is imposed after
the two conditions
`integral h(x)x^(+1/2)d*x=integral h(x)x^(-1/2)d*x=0`; their semi-local boundary theorem remains a
conjectural global step, not a result imported here.  Their
[archimedean trace analysis](https://arxiv.org/abs/2006.13771) identifies compression by cutoff
projections and the surviving trace difference, but does not supply the all-prime completed
boundary identity needed here.

## What remains

The positive finite radial packet and its codimension-at-most-two balanced compression are now
closed.  The actual Euler unit field is still outside the Hilbert carrier.  The open theorem is
not another finite positivity construction: it is convergence of the balanced projection as the
source aperture and radial damping approach the nonnormal Euler boundary, followed by the source
value identity comparing that boundary form with the inverse-tilted completed prime--Gamma moment
jets.

Reconstruction, source-effectivity, or the existence of the completed germ cannot supply this
identity.  Those data do not preserve the pre-continuation positive square root.

## Lean certificate

The wired module proves:

- `finiteExponentialAllDepthCauchyFeature_mul`;
- `sqrtWeight_mul_allDepthCauchyFeature_mul_eq_orientedAnomaly`;
- `finiteExponentialAllDepthCauchyGram_apply`;
- `finiteExponentialAllDepthCauchyGram_posSemidef`;
- `finiteVonMangoldtRealWeight_nonneg`;
- `sqrtVonMangoldtWeight_mul_allDepthCauchyFeature_mul_eq_orientedAnomaly`;
- `finiteVonMangoldtAllDepthCauchyGram_posSemidef`;
- `finiteVonMangoldtAllDepthBalancedCauchyVector_plus_half_eq_zero`;
- `finiteVonMangoldtAllDepthBalancedCauchyVector_neg_half_eq_zero`;
- `inner_balancedCauchyVector_boundary_plus_half_eq_zero`;
- `inner_balancedCauchyVector_boundary_neg_half_eq_zero`;
- `finiteVonMangoldtAllDepthBalancedCauchyGram_posSemidef`.

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.  Its direct check and exact
targeted build pass.  The displayed declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Proof chain

```text
exact all-coordinate von Mangoldt--Gamma anomaly
  -> positive finite radial Cauchy/Gauss--Ward packet
  -> positive finite two-boundary balanced compression
  -> [OPEN] balanced nonnormal Euler-boundary convergence
  -> [OPEN] inverse-tilted completed moment-jet comparison
  -> complete prime--Gamma Hankel cone
  -> RH.                                                  (6)
```

## Gates

- [x] construct all-depth anomaly Cauchy features
- [x] identify every feature numerator with the actual oriented anomaly
- [x] form the joint source-coordinate/Gamma-coordinate finite Gram
- [x] prove finite positive semidefiniteness
- [x] specialize to the actual resolved von Mangoldt source
- [x] construct the canonical two-boundary balanced projection
- [x] prove both boundary modes and pairings vanish
- [x] prove positivity survives the balanced compression
- [x] wire, target-build, and audit axioms
- [ ] prove convergence of the balanced projections under aperture/radial escape
- [ ] pass the balanced Gram to the Euler unit boundary
- [ ] compare with inverse-tilted completed prime--Gamma moment jets
- [ ] RH
