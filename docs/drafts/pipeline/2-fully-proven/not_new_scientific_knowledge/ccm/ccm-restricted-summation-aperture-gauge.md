# Restricted summation has an invisible aperture gauge

- **ID:** `ccm-restricted-summation-aperture-gauge`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent source:** Connes--Consani--Moscovici, *Zeta Spectral Triples*, Sections 7--8;
  Connes--Consani, *Spectral triples and zeta-cycles*, Sections 3 and 6
- **Statement:** On the aperture `[lambda^(-1),lambda]`, the restricted summation map factors through
  the quotient by even zero-integral corrections supported inside
  `(-lambda^(-1),lambda^(-1))`. Every quotient class has a representative with `f(0)=0`, so the CCM
  approximant admits an exact global-radical source representative while retaining its genuine
  zero-extended prolate endpoints.

## Setup

For `lambda>1`, define

```text
E(f)(u)=u^(1/2) sum_(n>=1) f(nu),
R_lambda E(f)=E(f)|_[lambda^(-1),lambda].
```

Let `C_even` be any linear class of even functions on `R` containing even smooth compactly
supported functions and on which the displayed sums are defined on the aperture. Put

```text
K_lambda={b in C_c^infinity(R)_even:
          support(b) subset (-lambda^(-1),lambda^(-1)),
          integral_R b=0}.
```

## Theorem

`[PROVED HERE]` The following hold.

1. `K_lambda subset ker(R_lambda E)`.
2. The evaluation map `ev_0:K_lambda->C`, `ev_0(b)=b(0)`, is surjective.
3. Consequently, if `f in C_even` has zero integral, there is a function `f_0` of the same ambient
   regularity as `f`, differing from `f` by a smooth compactly supported function, such that

   ```text
   f_0(0)=0,
   integral_R f_0=0,
   R_lambda E(f_0)=R_lambda E(f).
   ```

In particular, the finite-aperture image depends only on the class of `f` modulo `K_lambda`, and
the condition `f(0)=0` has a representative in every zero-integral class.

## Proof

Choose `a` with `0<a<lambda^(-1)`. Let `phi` be an even smooth bump supported in `(-a,a)` with
`phi(0)=1`. Let `psi` be an even smooth bump supported in `(-a,a)`, with support disjoint from a
neighborhood of zero and with nonzero integral. Then

```text
b=phi-(integral phi/integral psi)*psi
```

is even, smooth, supported in `(-a,a)`, and satisfies

```text
b(0)=1,   integral b=0.                                 (1)
```

For `u in [lambda^(-1),lambda]` and `n>=1`,

```text
nu>=lambda^(-1)>a.
```

Therefore `b(nu)=0` and hence

```text
R_lambda E(b)=0.                                        (2)
```

Scalar multiples of `b` prove surjectivity of `ev_0` on `K_lambda`. If `f` has zero integral, set

```text
f_0=f-f(0)b.
```

Equation (1) gives `f_0(0)=0` and `integral f_0=0`, while (2) gives
`R_lambda E(f_0)=R_lambda E(f)`. This proves all assertions.

## CCM consequence

The global radical construction uses the codimension-two source space

```text
S_0^even={f: f(0)=Fourier(f)(0)=0}
```

and `Fourier(f)(0)=integral f`. The finite-lambda CCM seed `h_lambda` is defined by enforcing the
second condition exactly. Since the compressed-Fourier eigenvalues of `h_(0,lambda)` and
`h_(4,lambda)` are distinct, `h_lambda(0)` is generally nonzero. The theorem shows that this point
defect is not an invariant of the finite-aperture approximant: subtracting `h_lambda(0)b` leaves
`k_lambda=R_lambda E(h_lambda)` exactly unchanged while enforcing both scalar conditions.

This observation identifies the correct invariant: the quotient source class after passing through
`R_lambda E`. The nonzero two-mode determinant measures a representative choice, while the aperture
vector has an exact representative satisfying both global-radical scalar conditions.

## Exact limitation

The prolate functions used by CCM are functions on `[-lambda,lambda]` extended by zero. They are
piecewise smooth but generally do not vanish to infinite order at the endpoints. Adding the central
bump above preserves that endpoint regularity; it does not put the source in the Schwartz space.
Thus the remaining analytic issue is not the two scalar conditions. It is the closability of the
global-radical/Poisson argument on zero-extended prolate sources at the exponentially small leakage
scale.

Equivalently, a proof must control the lower tail

```text
1_(0,lambda^(-1)) E(f),
```

which Poisson identifies with the inverted upper tail of `E(Fourier(f))`. That arithmetic summation
tail, not the point constraint, is the first genuine Weil--prolate transfer operator.

## Lean status

**Formalized unconditionally, 2026-08-04**, in
`formal/GaloisForLFunctions/RHTower/CCMApertureGauge.lean`.

- **`summationMap`** — `E(f)(u) = sqrt u * sum_(n>=1) f(nu)`, as a `tsum` over `n >= 1`.
- **`ApertureCorrector`** — the class `K_lambda`: smooth, even, vanishing for `lambda^(-1) <= |x|`,
  total integral zero.
- **`summationMap_eq_zero_of_vanishing`**, **`apertureCorrector_mem_kernel`** — part `1`,
  `K_lambda ⊆ ker(R_lambda E)`.  The proof is the card's: on the aperture the *first* sampling point
  already satisfies `nu >= u >= lambda^(-1)`, so every term vanishes.
- **`summationMap_sub_of_vanishing`** — the correction is invisible **termwise**.  This is worth
  isolating: no summability hypothesis appears anywhere in this module, because the two series have
  equal terms on the aperture whether or not either converges.  The card's linear class `C_even` "on
  which the displayed sums are defined" is therefore not needed for parts `1` and `3`; it is needed
  only to make `E(f)` itself meaningful off the aperture.
- **`exists_centralCorrector`** — the corrector `b`, with `b(0) = 1`, `integral b = 0`, even, smooth,
  supported in `(-a, a)` for arbitrary `a > 0`.  The construction differs from the card's: instead of a
  second bump placed off centre (which then has to be symmetrised to stay even), take
  `b = phi - c x^2 phi` for a single bump `phi` centred at the origin.  The factor `x^2` is even and
  vanishes at the origin, which are exactly the two properties the card's `psi` was chosen for, and
  `integral x^2 phi > 0` because `phi > 0` on its open support ball.
- **`exists_apertureCorrector_apply_zero`** — part `2`, surjectivity of `ev_0` on `K_lambda`, by
  scaling `b`.
- **`exists_zero_center_representative`** — part `3`: for an even integrable `f` of zero integral,
  `f_0 = f - f(0) b` satisfies `f_0(0) = 0`, `integral f_0 = 0`, `f_0` even, and
  `R_lambda E(f_0) = R_lambda E(f)`.  The two scalar conditions of the global-radical source space
  `S_0^even` are thus both enforced on the same representative, which is the CCM consequence the card
  draws.
- **`summationMap_eq_of_sub_apertureCorrector`** — the gauge statement itself: `R_lambda E` depends
  only on the class of the source modulo `K_lambda`.

Two remarks matching the card's own limitation.  The representative differs from `f` by a globally
smooth compactly supported function, so it has exactly the endpoint regularity of `f` and is *not*
Schwartz — the module proves `HasCompactSupport b` and smoothness of `b`, never smoothness of `f_0`.
And the lower tail `1_(0,lambda^(-1)) E(f)` is untouched by this module; that object is the subject of
`ccm-poisson-tail-l2-unboundedness.md`, whose `sqrt N` lower bound and coherent extremal packet are
formalized in `CCMArithmeticTailUnbounded.lean`.

## Gates

- [x] `K_lambda` contained in the kernel of the restricted summation map
- [x] central evaluation surjective on `K_lambda`
- [x] zero-centre representative with both scalar conditions
- [x] Lean: the corrector constructed (even, smooth, arbitrarily small support, unit central value,
      zero integral)
- [x] Lean: part `1` unconditional
- [x] Lean: part `2` unconditional
- [x] Lean: part `3` unconditional
- [x] Lean: gauge invariance of the finite-aperture image
- [ ] closability of the global-radical/Poisson argument on zero-extended prolate sources at the
      exponentially small leakage scale

## Novelty verdict

The support argument is elementary once the restricted summation map is written down. It usefully
repairs the source-domain bookkeeping in the CCM route, but it fails the anti-theatre and
parent-theory gates for new scientific knowledge. Its correct classification is `[BRIDGE]`.
