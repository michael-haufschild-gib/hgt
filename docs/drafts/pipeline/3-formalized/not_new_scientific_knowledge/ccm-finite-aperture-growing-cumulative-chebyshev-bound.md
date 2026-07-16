# The finite-aperture growing critical-Mellin channel needs only Chebyshev growth

- **ID:** `ccm-finite-aperture-growing-cumulative-chebyshev-bound`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONNES-SOURCE BRIDGE
- **Scientific status:** `[FULLY PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMCriticalMellinGrowingCumulativeBound.lean`

## Theorem

Write

```text
J(h)=exp(h)-1+h-Psi(exp(h)).                                    (1)
```

Then for every `h>=0`,

```text
|J(h)|<=1+h+(log 4+5)exp(h),                                   (2)

exp(-h)|J(h)|<=log 4+7.                                        (3)
```

Consequently the exact clipped center mass

```text
M(H)=integral_0^H exp(-h)|J(h)|dh+exp(-H)|J(H)|                 (4)
```

obeys

```text
M(H)<=(log 4+7)(H+1),     H>=0.                                (5)
```

The proof uses the exact growing-half-density identity and Chebyshev's elementary explicit bound

```text
Psi(x)<=(log 4+4)x.
```

No prime-number-theorem remainder, zero-free region, or RH-strength estimate enters.

## Connes-route consequence

The Poisson-center cross term is clipped at the finite CCM aperture. If its radial factor has the
BV envelope

```text
|R_lambda(t)|<=B_lambda/sqrt(lambda)*exp(-t/2),
```

then `(5)` prices the coupled center channel by

```text
O(|g_lambda(0)|*B_lambda*(H+1)/lambda).
```

At `H=2 log lambda`, `g_lambda(0)=O(d_lambda)`, and bounded fixed-mode variation, this is
`O(d_lambda log(lambda)/lambda)=o(d_lambda)`. Thus the quantitative PNT remainder is not a gate in
the continuous-polar source theorem.

## Verification

The exact `criticalCumulative=Psi` identification, the pointwise bounds `(2)`--`(3)`, and the
finite-aperture mass bound `(5)` were checked in the project toolchain. Their axiom audit contains
only `propext`, `Classical.choice`, and `Quot.sound`; there are no project axioms or placeholders.
