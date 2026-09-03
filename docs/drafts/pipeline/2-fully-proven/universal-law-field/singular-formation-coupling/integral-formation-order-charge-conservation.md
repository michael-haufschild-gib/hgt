# Integral formation-order charge conservation

- **ID:** `ULF-IFOCC-001`
- **Stage:** `2-fully-proven`
- **Type:** unconditional cross-organ conservation theorem
- **Parent:** `ULF-TPFOI-001`, `ULF-PHSGRC-001`
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH SELECTION]`
- **Lean status:** not formalized; no Lean was written or built in this research pass

## Big-picture interpretation

The unit carried by the prime--Hodge nuclear defect is not merely a normalization. It is the
discrete residue of the singular change of formation order required to turn physical Euler depth
into theta first-exit depth. Fredholm index, nuclear trace, tail codimension, and connection residue
are four gauges of one integral charge.

This supplies a mechanism, not new vocabulary: changing a positive depth law of order `-alpha` to
one of order `-beta` forces a half-density connection with charge `(alpha-beta)/2`. For the literal
Pluecker and theta laws, `(alpha,beta)=(6,4)`, so the charge is exactly one.

## Checked frontier and parent theories

Corpus searches were run for tail exponent/index conservation, successive log-ratio residues,
weighted-shift index, and half-density logarithmic connections.

- `[CORPUS]` `primeHodgeHistory_index_exitFlux_integralNuclear_conservation` proves
  `-index(C)=Tr(T)=1` together with the exit/Hodge flux readings.
- `[CORPUS]` `ULF-TPFOI-001` paper-proves that the fixed-edge physical Pluecker depth law satisfies
  `pi_e~C e^-6`, theta satisfies `w_e~(315/8)e^-4`, and their unique positive half-density is
  first-order unbounded.
- `[CORPUS]` `SoninCompletionMustGrowLinearly` independently rules out every sublinear completion
  restoring all Sonin floors, but contains no source-native connection residue.
- `[CORPUS]` `PrimeDepthBVWoldSourceNormalSchattenBridge` makes divisor-specialized inverse-depth
  graph admission equivalent to RH; the theorem below is strictly pre-divisor.

Closest external parents are regular variation, weighted shifts, Fedosov index trace formulas, and
singular traces. In particular:

- `[LITERATURE]` Berkani, *A trace formula for the index of B-Fredholm operators*,
  <https://arxiv.org/abs/1609.01695>, identifies Fredholm index with a commutator trace in a broad
  operator setting.
- `[LITERATURE]` Carey--Phillips--Sukochev, *Spectral flow and Dixmier traces*,
  <https://arxiv.org/abs/math/0205076>, relates index theory to weak-ideal asymptotics and singular
  traces.
- `[LITERATURE]` Gesztesy--Latushkin--Makarov--Sukochev--Tomilov,
  *The index formula and the spectral shift function for relatively trace class perturbations*,
  <https://arxiv.org/abs/1004.1582>, connects Fredholm index, spectral flow, and spectral shift.

Those theories do not establish the source-specific Pluecker/theta equality below. Priority of the
exact arithmetic fusion remains unverified.

## Formation-order residue

For a positive sequence `h=(h_e)`, define its discrete logarithmic formation residue, when the
limit exists, by

```text
Res_form(h)=lim_(e->infinity) e log(h_(e+1)/h_e).       (IFOCC.1)
```

For two positive depth laws `mu,nu`, their positive half-density is

```text
S(mu->nu)_e=sqrt(nu_e/mu_e).                            (IFOCC.2)
```

When `mu` and `nu` are rationally regularly varying with respective exponents `-alpha` and
`-beta`, define their half-order charge by

```text
q(mu,nu)=(alpha-beta)/2.                                (IFOCC.3)
```

“Rationally regularly varying” here means that, after multiplication by the leading power, each
sequence extends to a rational function of the real depth near infinity. This excludes oscillatory
`o(1)` pathologies and is exactly satisfied by the physical Pluecker and theta formulas.

## The theorem

Fix a physical prime edge `p<q`. Let `pi^(p,q)` be its normalized Pluecker denominator depth law,
`w` theta's Mellin-six first-exit law, and

```text
s_e=sqrt(w_e/pi_e^(p,q)).
```

**Theorem IFOCC.** The following exact conservation identity holds:

```text
Res_form(s)
  = q(pi^(p,q),w)
  = (6-4)/2
  = 1
  = -FredholmIndex(C)
  = Tr(T_1).                                             (IFOCC.4)
```

The value is independent of the chosen prime edge. Moreover formation charge is antisymmetric and
additive whenever all three rationally regular comparisons exist:

```text
q(mu,nu)=-q(nu,mu),
q(mu,omega)=q(mu,nu)+q(nu,omega).                       (IFOCC.5)
```

Thus the integer is a relative completion charge, not a fitted normalization.

## Proof

Write `P_e` for the physical six-minor Pluecker partition on the fixed edge. The proof of
`ULF-TPFOI-001` gives

```text
e^6 P_e -> K_pq>0.
```

More is automatic from the literal formula. Extend depth `e` to a real variable `x`. Every rate is
affine in `x`; every raw minor is a quotient of polynomials in `x`; hence

```text
x^6 P(x)=H(1/x)
```

for a rational function `H` regular at zero with `H(0)=K_pq>0`. Taylor expansion at zero gives

```text
H(y)=K_pq+h_1 y+O(y^2).
```

Consequently

```text
H(1/(e+1))/H(1/e)=1+O(e^-2)
```

and therefore

```text
P_(e+1)/P_e
  =(e/(e+1))^6 (1+O(e^-2))
  =1-6/e+O(e^-2).                                      (1)
```

The Fisher factor and normalization constant are depth-independent, so the same expansion holds
for `pi`:

```text
pi_(e+1)/pi_e=1-6/e+O(e^-2).                           (2)
```

Theta's flux telescopes exactly:

```text
w_(e+1)/w_e=(2e+3)/(2e+11)=1-4/e+O(e^-2).             (3)
```

Using `s_e^2=w_e/pi_e`, equations `(2)` and `(3)` yield

```text
(s_(e+1)/s_e)^2
  =(1-4/e+O(e^-2))/(1-6/e+O(e^-2))
  =1+2/e+O(e^-2).
```

The positive square root gives

```text
s_(e+1)/s_e=1+1/e+O(e^-2),
e log(s_(e+1)/s_e)->1.                                 (4)
```

This proves the first three equalities in `(IFOCC.4)`. The last two are the unconditional corpus
conservation theorem for the theta survival shift and the unit-aperture prime--Hodge defect:
`-FredholmIndex(C)=Tr(T_1)=1`.

Finally, `(IFOCC.5)` follows immediately from exponent differences; equivalently, positive
half-densities multiply pointwise:

```text
S(mu->omega)=S(nu->omega) S(mu->nu),
```

and logarithmic connection residues add. QED.

## Hostile review

**Wrong first:** regular-variation exponents, logarithmic derivatives, trace-index formulas, and
additivity of relative orders are classical. None separately defines a new field.

**Possible fatal collision:** a generic theorem saying “power-law exponent equals log-ratio limit”
is rediscovered analysis. The scientific residue is only the corpus-specific fact that the
source-native physical Pluecker law has exponent six, the self-dual theta law has exponent four,
and their half-difference equals the independently constructed Fredholm/nuclear unit.

**Correctness attack:** `f_e~c e^r` alone would not control consecutive ratios; oscillatory errors
could destroy `(IFOCC.1)`. The literal Pluecker law is rational in depth, and the proof explicitly
uses that stronger fact. No regularity is smuggled in.

**Circularity attack:** no zero, divisor copy, Xi landing, horizontal grade, or positivity
equivalent to RH occurs. The equality is unconditional and pre-divisor.

**Significance verdict:** survives preliminary attack as a nontrivial fusion law. It reconstructs
one integer from three structurally different organs and predicts the exact singular order of any
coefficient-faithful source completion. It still does not prove that completed Xi uses this
half-density or that the residual completion boundary vanishes.

## New risky consequence and RH-chain edge

`(IFOCC.4)` predicts that any literal Pluecker-to-theta completion retaining the source blocks has
a universal unit logarithmic shift anomaly:

```text
s_(e+1)/s_e=1+1/e+O(e^-2),
```

independent of the prime edge. Therefore an admissible global completion must carry one common
first-order graph connection while its block coefficients remain prime-dependent. A bounded
prime-independent scalar ghost cannot realize this law.

The exact open edge is now:

```text
derive the unit graph connection from literal integer/Poisson completion
  -> prove its nonseparable Pluecker sandwich preserves unsquared Euler coefficients
  -> identify its renormalized boundary with completed Xi
  -> prove residual boundary zero
  -> formation-boundary fusion forces neutral grade.
```
