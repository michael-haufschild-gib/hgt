# First-moment quadratic zero-free law

- **ID:** `first-moment-quadratic-zero-free-law`
- **Stage:** 1-in-progress
- **Type:** `[PAPER-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [UNCONDITIONAL] [RH-FACING]`
- **Target:** a universal source-stability theorem whose theta specialization supplies a proved
  zero-free endpoint for an affine Riemann--Xi deformation
- **Prior exact specialization:**
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityTransversePick.lean`

## Universal statement

Let

```text
H_R = {s in C : Re(s)>0}.
```

Fix `kappa>0` and `M>0`.  Suppose `B : H_R -> C` obeys the transverse sector law

```text
Re(s) |B(s)| <= |s| Re(B(s))                       (S)
```

at every nonreal `s` in `H_R`, and the positive-axis first-moment cap

```text
0 <= B(r) <= M r                                   (T)
```

for every real `r>0`.  Then

```text
Q_(B,kappa,M)(s)
  = (kappa^2-s^2) B(s) - kappa^2 M s               (Q)
```

has no zero in `H_R`.

No holomorphy is needed for the pointwise exclusion theorem.  When `B` is holomorphic, `(Q)` is a
holomorphic right-half-plane stability law.

## Positive-source generator

Let `mu` be a positive source on `[0,infinity)` with finite positive first moment

```text
M = integral t dmu(t) > 0,
```

and define its Bernstein--Laplace increment

```text
B_mu(s) = integral (1-exp(-s t)) dmu(t).
```

The pointwise inequality

```text
Re(s) |1-exp(-s t)| <= |s| (1-Re(exp(-s t)))
```

integrates against the positive source to give `(S)`.  On the positive axis,

```text
0 <= 1-exp(-r t) <= r t
```

gives `(T)`.  Therefore every such positive source generates the zero-free family

```text
(kappa^2-s^2) B_mu(s) - kappa^2 M s != 0
```

throughout `Re(s)>0`.

For the first formal closure, an absolutely continuous source `dmu(t)=h(t)dt` is sufficient.
The measure-valued extension uses the identical pointwise proof and is promoted only after exact
formal closure.

## Paper proof

Take `s=a+i b`, `a>0`, and suppose `Q_(B,kappa,M)(s)=0`.

If `b!=0`, put `D=kappa^2-s^2`.  Since `D!=0`,

```text
B(s) = kappa^2 M s / D.
```

Substitution into `(S)` and cancellation of the positive factor `kappa^2 M` gives

```text
a |D| <= Re(s conjugate(D))
          = a (kappa^2-|s|^2).
```

Hence

```text
|kappa^2-s^2| <= kappa^2-|s|^2.                    (1)
```

The right side of `(1)` is nonnegative, while

```text
|kappa^2-s^2|^2-(kappa^2-|s|^2)^2
  = 4 kappa^2 b^2 > 0,                              (2)
```

contradicting `(1)`.

If `b=0`, write `s=r>0`.  For `r>=kappa`,

```text
Q(r) = (kappa^2-r^2)B(r)-kappa^2 M r < 0.
```

For `0<r<kappa`, `(T)` gives

```text
Q(r)
 <= (kappa^2-r^2) M r-kappa^2 M r
 = -M r^3 < 0.
```

Thus `Q` has no zero in the open right half-plane.

## Theta--Xi specialization

For the completed theta density in the corpus, put

```text
rho(t)=4 T''(t),
h(t)=-rho'(t),
B(s)=integral h(t)(1-exp(-s t)) dt.
```

The proved integration-by-parts identities give

```text
M=integral t h(t) dt=integral rho(t) dt=1,
B(s)=s F(i s),
```

where

```text
F(z)=integral rho(t) exp(i t z) dt.
```

At `kappa=1/2`,

```text
Q(s)/s
  = (1/4-s^2)F(i s)-1/4
  = E(i s),
E(z)=(z^2+1/4)F(z)-1/4.
```

The universal law therefore recovers the unconditional upper-half-plane zero-freeness of `E`.
With

```text
E#(z)=(z^2+1/4)F(-z)-1/4,
H_tau(z)=((1+tau)/2)E(z)+((1-tau)/2)E#(z),
```

the existing exact identities are

```text
H_1=E,
H_(-1)=E#,
H_0=2 z^2 XiC.
```

Thus the Riemann problem sits at the midpoint of an explicit affine pencil with a source-generated
zero-free endpoint and a pole-free projective chart.  This is a zero-transport route, not an RH
equivalence or a zero-exclusion claim for `H_0`.

## Falsifiers and hostile checks

1. **Sign loss:** squaring the source orientation before deriving `(S)` destroys the theorem.
   The proof uses the unsquared positive source.
2. **No source positivity:** signed sources need not obey `(S)` or `(T)`; the conclusion is not
   claimed for them.
3. **Vanishing first moment:** `M>0` is essential to the cancellation and strict real-axis bound.
4. **False Hermite--Biehler upgrade:** zero-freeness of `E` does not imply `|E|>|E#|`; the corpus
   refutes that global strict gap.
5. **No midpoint transport:** the theorem does not assert that zero-freeness propagates from
   `H_1` to `H_0`.  Boundary entry and noncompact escape are the exact unresolved transport
   mechanisms.
6. **Known component:** sector preservation for Bernstein functions is classical.  Candidate
   novelty is the sharp quadratic completion law and its exact theta--Xi specialization, not the
   sector fact alone.

## Required closure

- [x] dependency-closed paper proof of abstract stability law;
- [x] exact theta specialization already formalized;
- [ ] formalize arbitrary-`kappa`, arbitrary-`M` stability law;
- [ ] formalize positive-density generator and first-moment axis cap;
- [ ] determine whether full measure-valued promotion is efficient and dependency-clean;
- [ ] primary-literature collision audit for `(Q)`;
- [ ] publication manuscript;
- [ ] antagonistic general-journal review;
- [ ] final Lean, axiom, lint, PDF, and stale-process audits.
