# CCM Guinand--Weil literal polar--prime source

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / arithmetic pre-quotient source
- **Novelty scope:** corpus-new typed continuous-dual realization and exact normalization weld;
  underlying pole/prime Stieltjes formula is present in published CCM work
- **External anchor:** Akiva Groskin, arXiv:2607.02828, finite source-measure calculus and
  prime/pole source prescription
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilLiteralPolarPrimeSource.lean`

## Literal channels before quotienting

For positive half-aperture `a`, transport logarithmic position `h in [0,2a]` to physical horizon

```text
omega_a(h)=1-h/(2a).                                             (1)
```

Lean constructs two separate elements of `C([0,1],R)^*`:

```text
L_pole(f)=integral_0^(2a) f(omega_a(h)) 2 cosh(h/2) dh,           (2)

L_prime(f)=sum_(2<=k<=floor(exp(2a)))
             -Lambda(k)/sqrt(k) f(omega_a(log k)).               (3)
```

The pole functional is proved bounded by an explicit compact-aperture norm estimate. Every visible
prime-power logarithm is proved to lie inside `[0,2a]`, so `(3)` uses literal unclamped horizons.
The two channels are combined only after both are typed and verified:

```text
L_polar-prime=L_pole+L_prime.                                    (4)
```

## Exact physical-mode weld

For physical frequency `xi_n=pi*n/a`, integral Fourier periodicity gives

```text
sin(2*pi*n*omega_a(h)) = -sin(xi_n*h).                            (5)
```

Therefore the odd source value of `(4)` is the negative critical-Mellin Stieltjes sine pairing,
divided by `pi`. Lean proves unconditionally for every `a>0` and `n`:

```text
psi_(L_polar-prime)(n)
  = ccmPublishedPolarPrimeSineCoefficient(a,xi_n).                (6)
```

Equation `(6)` closes all signs, endpoint normalization, the prime cutoff, and the `pi` factor. It
is an equality inside the source-native quotient, not a post-hoc comparison of scalar formulas.

## CCM-FU consequence

The polar and finite-prime pieces of the published restricted-Weil source now have an explicit
pre-quotient provenance in the same continuous dual used by the exact `2N+1` observer theorem.
C60 subsequently proves that the literal Gamma density is a singular mixed-order channel and closes
the full odd value against `ccmPublishedSourceSineCoefficient`. Remaining packet-matrix debt is the
endpoint-renormalized weighted-cosine diagonal. No positivity, Ward transport, or RH conclusion is
claimed here.

## Lean declarations

- `ccmGuinandWeilLogToHorizon`
- `ccmGuinandWeilPrimeLog_mem`
- `ccmGuinandWeilPrimeHorizon`
- `ccmGuinandWeilSineCoordinate_logToHorizon`
- `ccmGuinandWeilPrimeSourceFunctional`
- `ccmGuinandWeilPoleSourceFunctional`
- `ccmGuinandWeilPolarPrimeSourceFunctional`
- `ccmCriticalMellinStieltjesPairing_sine_re_interval`
- `ccmGuinandWeilPolarPrimeSourceValue_physical_eq_published`

Targeted `lake env lean` and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilLiteralPolarPrimeSource` pass. `#print axioms` reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`,
`admit`, `opaque`, or `unsafe` declaration is used.
