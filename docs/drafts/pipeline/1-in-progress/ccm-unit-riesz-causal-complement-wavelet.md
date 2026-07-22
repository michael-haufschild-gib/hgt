# CCM unit-Riesz causal-complement wavelet

- **ID:** `ccm-unit-riesz-causal-complement-wavelet`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE, `[OPEN RH CORE]`
- **Scientific status:** `[CONJECTURE] [CONNES/CCM SOURCE-SPECIFIC] [NOT RH YET]`
- **Parent theorem:**
  `../2-fully-proven/new_scientific_knowledge/ccm-unit-riesz-mobius-wavelet-reduction.md`
- **Connector theorem:**
  `../2-fully-proven/new_scientific_knowledge/ccm-unit-riesz-markov-virial-landau-law.md`

## Exact open statement

Use `h_0(t)=exp(-t)-sum_(n<=exp(t))mu(n)/n` and the unit-Riesz wavelet

```text
Phi_T(u)=u W(exp(T-u)),
K_T=Phi_T',
W(t)=3/t sum_(1<=r<=t)(1-sqrt(r/t)).                     (1)
```

Prove, for every `epsilon>0`,

```text
integral_0^T h_0(u)K_T(u)du
 >=-C_epsilon exp(-(1/2-epsilon)T)                       (2)
```

at `T=log N`, `N>=2`, directly from the coupled Euler floor-remainder source.

## Why this is the frontier rather than a renamed conclusion

The parent theorem proves

```text
J_N=2sqrt(N)/3 * [A_T-1-<h_0,K_T>],                     (3)

0<=1-A_T<=(3T^2/2+T+1)exp(-T).                          (4)
```

Thus `(2)` is exactly the unresolved half-unit cancellation after all deterministic aperture,
Volterra, polar, progression-quadrature, and future-Möbius terms are removed.  It is RH-equivalent
after the Landau connector, so no theorem in current literature can supply it without resolving
the same frontier.

Unlike the full weighted-Mertens condition

```text
exp(alpha t)m_0(t) in L2 for every alpha<1/2,             (5)
```

`(2)` asks for one one-sided zero-mean coefficient per scale.  Proving `(5)` would be circularly
overpowered; attack `(2)` through the exact floor-remainder structure of `h_0`.

## Scientific-method attack

### Conjecture `UNIT-RIESZ-CAUSAL-COMPLEMENT-SATURATION`

The critical floor-remainder component is asymptotically nonnegative against the moving
unit-Riesz derivative wavelet at the half-unit rate `(2)`.

### Required mechanism

Construct a source-fixed factorization of `<h_0,K_T>` before taking scalar absolute values.  The
factorization must couple:

1. the floor remainder and centered Möbius boundary from `m_0+h_0=exp(-t)`;
2. both lobes of the zero-mean `K_T`;
3. every squarefree Euler grade before the exact von-Mangoldt collapse;
4. the moving staircase points `T-log n`, where `K_T` changes derivative.

An acceptable provider is a signed causal graph pairing whose negative part is a boundary square
with coefficient `exp(-T/2)` or smaller.  A norm bound on `h_0` or `K_T` separately is not enough.

### Falsifiers

- A source-compatible packet with `<h_0,K_T><<-exp(-(1/2-epsilon)T)` falsifies `(2)` and RH.
- A proposed convex/probability proof is invalid unless it survives the exact positive-renewal
  collapse `S_N=3P_N/N`; abstract norm-one contraction has no remaining saving.
- A proof using only `h_0 in L2` is invalid: arbitrary `L2` vectors can align with one wavelet lobe.
- Any estimate of `Q_N-1` and the quadrature assembly separately is invalid by exact compensation.
- Any zero sum, assumed zero-free strip beyond the classical one, or continued Weil positivity is
  circular.

## Immediate next lemma

The first-crossing calculation is now complete.  With

```text
d(v)=d/dv W(exp(v)),
V_h(t)=integral_0^t h_0(u)du-t h_0(t),
```

the connector theorem proves

```text
d>=0,  integral d=1,
<h_0,K_T>=(d*V_h)(T),
V_h(t)=1-(1+t)exp(-t)-Q(exp(t)),
Q(X)=-sum_(n<=X)mu(n)log(n)/n.                           (6)
```

It also proves that `(2)` implies RH by a one-sided Landau argument.  Generic coisometry is
retired: `(6)` contains no algebraic `exp(-T/2)` gain, and its continued transform retains every
off-critical zero as a genuine simple pole.

Immediate target is now source-specific: prove the lower bound for the joined Markov average in
`(6)` from a signed first-crossing pairing of `1-Q`, without estimating `Q` pointwise.

## Status

- `[PROVED]` all identities `(1)`, `(3)`, `(4)` and their source derivation;
- `[PROVED]` complete future dressing leaves only positive prime-power renewal;
- `[PROVED]` exact Markov--virial factorization and explicit probability transform;
- `[PROVED]` one-sided Landau connector from `(2)` to RH;
- `[RETIRED]` generic critical Schur/coisometry as half-unit exponent provider;
- `[OPEN RH CORE]` causal-complement wavelet lower bound `(2)`;

RH is not proved.
