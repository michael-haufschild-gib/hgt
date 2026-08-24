# Hypertranscendental gauge saturation of one de Branges spectral class

- **ID:** `de-branges-ht-gauge-saturation`
- **Stage:** 3-formalized
- **Type:** THEOREM / DE BRANGES--HILBERT--POLYA IMPLEMENTATION NO-GO / BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every Hermite--Biehler function admits continuum many positive real zero-free HT
  gauges which leave its inner quotient, every canonical real spectrum, reproducing-kernel
  geometry, and de Branges space unchanged up to explicit unitary equivalence. The gauges may also
  preserve arbitrary finite jets on an arbitrary discrete conjugation-stable set. Consequently
  DA/HT status of a structure function cannot be the missing selector in any de Branges,
  Hilbert--Polya, or phase-spectral Connes implementation which factors through those gauge-invariant
  data.

## Hermite--Biehler data

For an entire function `F`, put

```text
F#(z)=conj(F(conj(z))).                                    (1)
```

An entire function `E` is Hermite--Biehler when

```text
|E#(z)|<|E(z)|,   Im(z)>0.                                 (2)
```

Write

```text
A_E=(E+E#)/2,
B_E=(E-E#)/(2i),
Theta_E=E#/E.                                               (3)
```

The canonical real spectra are the zero sets of

```text
A_E cos(alpha)+B_E sin(alpha),   alpha in R.               (4)
```

The de Branges space `H(E)` has norm

```text
||F||_E^2=integral_R |F(x)/E(x)|^2 dx,                     (5)
```

together with the standard bounded-type conditions on `F/E` and `F#/E` in the upper half-plane.

## Real zero-free gauge invariance `[SEARCH]`

Let `H` be a zero-free entire function satisfying

```text
H#=H.                                                       (6)
```

Then:

1. `EH` is Hermite--Biehler;
2. `Theta_(EH)=Theta_E`;
3. `A_(EH)=H A_E` and `B_(EH)=H B_E`;
4. every canonical spectrum (4), including multiplicity, is unchanged;
5. multiplication by `H` is a unitary map

   ```text
   U_H:H(E)->H(EH),   U_H(F)=HF;                           (7)
   ```

6. the reproducing kernels satisfy

   ```text
   K_(EH)(z,w)=H(z)conj(H(w))K_E(z,w).                     (8)
   ```

### Proof

Equation (6) gives `(EH)#=H E#`. Multiplication by the common nonzero factor `|H(z)|` preserves
the strict inequality (2), proving the first claim, and cancellation gives the second. The third
claim follows by inserting `(EH)#=HE#` into (3). Since `H` is zero-free, it introduces no zeros in
any real linear combination of `A_E` and `B_E`, proving the fourth.

For (7), if `F in H(E)`, then

```text
(HF)/(HE)=F/E,
(HF)#/(HE)=F#/E.
```

Thus membership and norm are preserved. Conversely, if `G in H(EH)`, then `G/H` is entire because
`H` is zero-free, and the same identities put `G/H` in `H(E)`. Hence multiplication is onto and
unitary. Formula (8) follows either from the standard kernel formula or by transporting point
evaluation through this unitary. `square`

## Symmetric HT gauges with discrete Hermite passports `[PROVED]`

Let `S subset C` be discrete and closed under conjugation. Let `m:S->N` satisfy
`m(conj(a))=m(a)`. There are continuum many entire functions `H` such that:

1. `H#=H`;
2. `H` is zero-free and `H(x)>0` for every real `x`;
3. `H` is HT over `C(z)`; and
4. for every `a in S`,

   ```text
   H(z)-1=O((z-a)^(m(a)+1)).                               (9)
   ```

### Construction and proof

Choose an entire Weierstrass product `W_0` vanishing at every `a in S` to order at least
`m(a)+1`, and put

```text
W=W_0 W_0#.
```

Then `W#=W` and `W` has at least the required zero orders. Let

```text
h(z)=1/Gamma(z).
```

The function `h` is real entire and HT by Holder's theorem. For real `t`, put

```text
Q_t=W exp(t h).                                             (10)
```

At most one complex value of `t` can make `Q_t` DA. Indeed, if distinct `t,u` did so, their ratio
`exp((t-u)h)` would be DA; its logarithmic derivative `(t-u)h'` would be DA, which would make `h`
DA after one integration. Choose a real nonexceptional `t` and write `Q=Q_t`. Then `Q` is real
entire, HT, and has the prescribed zeros.

For every nonzero real `c`, define

```text
H_c=exp(cQ).                                                (11)
```

It is real entire, zero-free, and positive on the real axis. If `H_c` were DA, then
`Q'=H_c'/(cH_c)` would be DA, forcing `Q` to be DA. Thus every `H_c`, `c!=0`, is HT. Since `Q`
vanishes to the required orders, (9) follows from `exp(cQ)-1=cQ+O(Q^2)`. Distinct real `c` give
continuum many gauges. `square`

## Fixed-class saturation theorem `[PROVED]`

Let `E` be any Hermite--Biehler function and use the gauges `H_c` above. Then, for all but at most
one real `c`,

```text
E_c=H_cE                                                   (12)
```

is HT. Every `E_c` has exactly the same data (2)--(8) as `E`, and

```text
E_c(z)-E(z)=O((z-a)^(m(a)+1))                              (13)
```

at every `a in S`.

Indeed, if `E_c` and `E_d` were both DA for distinct `c,d`, then their quotient
`exp((c-d)Q)` would be DA, contradicting the HT of `Q`. Thus at most one parameter is exceptional.
Equation (13) follows by multiplying (9) by the entire function `E`.

If `E` is DA, then `c=0` is the unique possible DA parameter and every `c!=0` gives an HT
structure function in the same de Branges spectral class.

## Explicit DA/HT pair `[PROVED]`

Fix `a>0` and take

```text
E_0(z)=exp(-iaz).                                          (14)
```

For `Im(z)>0`, `|E_0(z)|=exp(a Im(z))>|E_0#(z)|`, so `E_0` is Hermite--Biehler and DA. Let

```text
q(z)=1/Gamma(z)+1/Gamma(1-z),
H(z)=exp(q(z)),
E_1(z)=H(z)E_0(z).                                         (15)
```

Euler reflection gives a quadratic algebraic equation for `Gamma(z)` over the differential field
generated by `q`; hence Holder's theorem makes `q` HT. If `H` were DA, its logarithmic derivative
would make `q` DA. Thus `H` and `E_1` are HT. The pair `E_0,E_1` has:

```text
Theta_(E_0)=Theta_(E_1),
canonical spectra(E_0)=canonical spectra(E_1),
H(E_0) unitarily equivalent to H(E_1).                     (16)
```

One representative is DA and the other HT.

## Sharp finite-order boundary `[PROVED]`

No zero-free HT entire gauge can have finite order. A zero-free entire function of finite order is,
by Hadamard factorization, `exp(P)` for a polynomial `P`; it is DA. Therefore every HT gauge in the
theorem has infinite order.

More precisely, let `E_1,E_2` be finite-order Hermite--Biehler functions without real zeros and
assume

```text
E_1#/E_1=E_2#/E_2.                                         (17)
```

The zeros of this common inner quotient in the upper half-plane record the reflected lower-half
zero divisor of each structure function. Hence `E_1` and `E_2` have the same divisor, and Hadamard
factorization gives

```text
E_1/E_2=exp(P)                                              (18)
```

for a polynomial `P`. Equation (17) says this quotient is real entire, so after changing `P` by an
irrelevant integral multiple of `2pi i`, it may be taken real. The gauge `exp(P)` is DA.

Consequently DA versus HT status is invariant among all finite-order representatives of one exact
de Branges inner quotient. If one representative is DA, all are DA; if one is HT, all are HT.

This is the exact escape from the no-go. A de Branges construction which canonically fixes finite
exponential type, order, mean type, source normalization, or a specific canonical-system
Hamiltonian has retained information not present in the gauge class above.

## Exact implementation no-go

The theorem excludes any de Branges, Hilbert--Polya, or phase-spectral Connes implementation whose
proposed extra selector depends only on:

1. the Hermite--Biehler quotient `E#/E`;
2. all canonical real spectra (4);
3. the de Branges space up to unitary multiplication;
4. its reproducing kernel up to the gauge covariance (8);
5. arbitrary sitewise-finite Hermite observations on a discrete set; and
6. DA versus HT status of the chosen structure-function representative.

Within one exact class of the first five data, both DA and continuum many HT representatives occur.
Thus differential type contributes no spectral or positivity selector.

The theorem does **not** exclude the full de Branges or Hilbert--Polya routes. Their decisive input
may be a canonical finite-type normalization, an exact source-selected Hamiltonian, a divisor
identification with `Xi`, or a positivity theorem not invariant under the gauge.

## Scientific verdict

The result is a route-useful but scientifically routine synthesis. Real zero-free multiplication is
the elementary gauge equivalence already implicit in the definition of `H(E)`. The HT saturation
uses Holder, Weierstrass products, exponential pencils, and discrete Hermite interpolation. Once
the gauge question is posed, no new parent mechanism is required. The anti-theatre and
parent-theory gates therefore reject a novelty claim.

Primary parent references:

1. L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice--Hall, 1968.
2. L. de Branges, *The Riemann hypothesis for Hilbert spaces of entire functions*, Bull. Amer.
   Math. Soc. 15 (1986), 1--17,
   https://www.math.purdue.edu/~branges/riemann-hilbert.pdf.
3. Holder's theorem for `Gamma`, the Weierstrass product theorem, and Hadamard factorization.

## Lean status

Fully formalized unconditionally in Lean 4. Exact implementation spans:

- `RHTower/DeBrangesGaugeInvariance.lean`: HB equivalence, `A/B` covariance, canonical spectra,
  exact inner quotient, and kernel covariance;
- `RHTower/DeBrangesGaugeUnitary.lean`: actual subtype of entire de Branges functions with both
  Hardy membership conditions, boundary-quotient norm, and explicit surjective linear isometry
  `F ↦ H F` with inverse `G ↦ G/H`;
- `RHTower/DeBrangesHTGaugeSaturation.lean`: injective real continuum of positive zero-free
  Schwarz-real HT gauges, arbitrary conjugation-stable discrete Hermite passports, exact spectrum
  multiplicities, fixed-class saturation, and DA uniqueness;
- `RHTower/DeBrangesExplicitGammaGauge.lean`: explicit DA/HT representatives in one exact class;
- `HTGeometry/FiniteOrderEntireQuotient.lean` and
  `RHTower/DeBrangesFiniteOrderRigidity.lean`: full divisor recovery from equal inner quotients,
  finite-order quotient growth via Nevanlinna proximity, exponential-polynomial Schwarz-real gauge,
  and exact DA/HT-type equivalence;
- `HTGeometry/FiniteOrderZeroFreeDifferentialAlgebraic.lean`: no zero-free finite-order HT gauge.

All leaf checks and targeted builds pass. Axiom audits of new capstones report only `propext`,
`Classical.choice`, and `Quot.sound`. Modules are wired into `HTGeometry` and `RHTower`; neither
umbrella was built.

## Gates

- [x] Real zero-free gauge invariance proved.
- [x] Continuum HT saturation with discrete Hermite passports proved.
- [x] Explicit DA/HT pair in one spectral class proved.
- [x] Finite-order escape boundary and finite-order gauge rigidity proved.
- [x] Exact noncategorical route no-go stated.
- [x] Scientific-novelty claim rejected.
- [x] Whole theorem formalized unconditionally in Lean.

## Formalization completion (2026-08-24)

Every paper theorem above now has a closed Lean proof, including previously missing actual-space
unitary and arbitrary finite-order rigidity layers. Card moved to Stage 3 after targeted leaf builds
and fresh axiom audit.
