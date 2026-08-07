# Burnol Cartier zero-transfer head gain

- **ID:** `burnol-cartier-zero-transfer-head-gain`
- **Stage:** 1-in-progress
- **Type:** `[LEAN-PROVED] [NEW SCIENTIFIC KNOWLEDGE] [ROUTE R FRONTIER]`
- **Exact claim:** the Cauchy divided shift generates a canonical isometric Blaschke zero-transfer;
  at every right-half Xi divisor its value on the fixed `[1/2,1]` co-Poisson atom is an actual
  extended-Sonin source whose forward and cosine aperture heads carry explicit reciprocal gains.

## Conjecture loop

1. **Total-space functional-equation sewing.** `[FALSIFIED]` Cosine reflection exchanges the
   `rho` and `1-rho` fibres and inverts the ladder character. It does not identify the two fibres;
   that identification is already the critical-line assertion.
2. **Finite-head Green determination of the physical port.** `[FALSIFIED]` Aperture-head data do
   not determine the Hilbert Cauchy port. Nonzero zero-head Sonin directions retain strictly
   positive Herglotz energy in the open right half-plane.
3. **Blaschke zero-transfer and oriented head gain.** `[PROVED]` For
   `delta = Re rho - 1/2` and the forward divided shift `M_rho`, put
   `Z_rho = I - 2 delta M_rho`. The exact Herglotz identity gives `||Z_rho f||=||f||`. At a zeta
   zero, Burnol division makes `M_rho f` an extended-Sonin source, hence so is `Z_rho f`.

## Paper proof

Let `m_rho(t)=1/(rho-(1/2+it))`. Pointwise on the critical line,

```text
Re m_rho(t) = delta |m_rho(t)|^2,
|1-2 delta m_rho(t)| = 1.
```

Therefore `Z_rho=I-2 delta M_rho` is an isometry on the full Mellin `L2` carrier. This construction
uses no divisor or RH input.

For the fixed co-Poisson atom `f0=P(v^-1 1_[1/2,1])`, the two exact aperture-head values are

```text
head(f0)   = -1,
head(F f0) = -log 2.
```

If `zeta(rho)=0`, Burnol's head laws for the zero-divided shift give

```text
head(M_rho f0)   =  1/(1-rho),
head(F M_rho f0) = -log(2)/rho.
```

Since `2 delta = rho-(1-conj rho)`, the zero-transfer has heads

```text
head(Z_rho f0)   = -conj(rho)/(1-rho),
head(F Z_rho f0) = -log(2) (1-conj(rho))/rho.
```

The two gains are reciprocal under conjugation:

```text
beta_rho = 1/conj(alpha_rho),
alpha_rho = conj(rho)/(1-rho).
```

They are not individually unimodular off the critical line. On the open right half of the strip,
`|alpha_rho| > 1` and `|beta_rho| < 1`; moreover

```text
|alpha_rho|=1  <->  Re rho=1/2.
```

Thus the remaining fixed-source-orientation problem is separate conservation of one explicit
local aperture-head norm. Lean proves that this local law is equivalent to the previous global
physical-port sewing producer and implies the existing RH endpoint. This card does not assume or
prove that pre-divisor conservation law.

## Hostile audit

- Total Hilbert norm preservation alone is nonselective: every right-half parameter has the
  isometric Blaschke transfer, while its two boundary heads exchange amplitude reciprocally.
- Sonin landing alone is nonselective: it follows from zero division at any hypothetical off-line
  zeta zero.
- The selecting statement is fixed forward-head norm preservation. Lean proves it is RH-strength,
  but it is a local coefficient law rather than the previous global Hilbert-port sewing.
- General Blaschke zero transfer is standard de Branges/Hardy theory. Novelty claim is restricted
  to the coefficient-faithful Route R synthesis with the literal fixed co-Poisson atom and its two
  exact aperture phases.

## Gates

- [x] internal corpus and failed-route audit
- [x] primary-literature collision audit
- [x] conjecture/attack loop
- [x] dependency-closed Lean formalization
- [ ] umbrella, targeted module build, axiom audit
