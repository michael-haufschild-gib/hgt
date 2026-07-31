# Suzuki critical wall-field resolvent dressing law

- **ID:** `suzuki-critical-wall-field-resolvent-dressing-law`
- **Stage:** 2 — fully proved on paper
- **Type:** SOURCE-TYPE CORRECTION / RESOLVENT WELD / KREIN COMPENSATION CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC] [LEAN-PROVED]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `suzuki-critical-wall-field-square-root-weld.md`,
  `suzuki-affine-resolvent-krein-defect.md`
- **RH used:** no
- **Computation used:** no

## Frontier correction

Bare Gamma wall amplitude `b_e` is source coordinate, not restricted-Weil endpoint response.
Suzuki deficiency state is obtained by applying `(A_a-lambda I)^(-1)` to source.  It therefore
depends on shift and spectral level before any boundary observation.  Literal endpoint equality
`v(-a)=b_e` would delete this resolvent and is not correct source architecture.

Correct first object is one-mode resolvent-dressed wall field.

## Theorem A: exact dressed affine residual `[PAPER-PROVED] [LEAN-PROVED]`

Fix spectral level `s`, shift `lambda`, and define

```text
r_lambda(s)=1/(s-lambda),
D_lambda(s;t)=r_lambda(s) omega_e(t).
```

For distinct shifts `alpha,beta`, define affine zero-shift extrapolation

```text
D_aff=(beta D_alpha-alpha D_beta)/(beta-alpha).
```

Then

```text
D_0-D_aff=K_(alpha,beta)(s) omega_e(t),                 (1)

K_(alpha,beta)(s)
 =r_0(s)-(beta r_alpha(s)-alpha r_beta(s))/(beta-alpha)
 =alpha beta/[s(s-alpha)(s-beta)].                     (2)
```

Second equality requires `s`, `s-alpha`, and `s-beta` nonzero.

### Proof

Factor common `omega_e` from affine combination.  Remaining scalar is exactly corpus's affine
resolvent Krein defect.  Common-denominator expansion gives `(2)`.

## Theorem B: symmetric-square Krein closure `[PAPER-PROVED] [LEAN-PROVED]`

Self-pair residual with same source wall field.  Square-root weld gives

```text
omega_e(t)[D_0(s;t)-D_aff(s;t)]
 =K_(alpha,beta)(s) omega_e(t)^2
 =K_(alpha,beta)(s)
   Lambda(n)/sqrt(n) exp(i t log n).                   (3)
```

Thus affine endpoint mismatch is not an unspecified residual.  In source-symmetric channel it is
exact scalar Krein defect times same far-hinge numerator already forced by prime source.

## Theorem C: exact negative-mode compensation debt `[PAPER-PROVED] [LEAN-PROVED]`

Assume below-spectrum negative shifts

```text
alpha<beta<0,  beta<s,  s!=0.
```

Existing scalar theorem gives `sign K_(alpha,beta)(s)=sign s`.  At zero height, phase in `(3)` is
one and `Lambda(n)/sqrt(n)>0`.  Therefore

```text
s<0 -> Re{omega_e(0)[D_0-D_aff]}<0,                    (4)
s>0 -> Re{omega_e(0)[D_0-D_aff]}>0.                    (5)
```

Every negative restricted-Weil spectral coordinate creates strict source-weighted compensation
debt.  Two-shift affine resolvent block cannot itself be positive; Gamma/polar, marked Robin, or
holonomy block must pay exact negative-mode term before rectangular semiboundedness.

## Scientific consequence

Wall source has three forced degrees:

```text
far source numerator        omega_e^2,
one-mode deficiency input   r_lambda(s) omega_e,
affine self-paired residual K_(alpha,beta)(s) omega_e^2. (6)
```

This corrects proposed endpoint realization twice: observer innovation acts after bare source,
and restricted-Weil resolvent acts before boundary observation.  Correct full target is spectral
superposition of dressed field against actual boundary observation, not raw equality to `b_e`.

### `SUZUKI-RESOLVENT-DRESSED-WALL-WARD` `[CONJECTURE]`

Represent actual affine-sewn endpoint reporter as spectral integral/sum of
`r_lambda(s) omega_e` with genuine restricted-Weil boundary observation.  Pair source-symmetric
Krein residual `(3)` with marked Robin, polar--Gamma continuum, and holonomy blocks.  Prove total
fixed-width rectangular Ward defect uniformly lower bounded.  Existing connector then proves RH.

First unresolved source implication is no longer `endpoint=b_e`; it is:

```text
actual boundary endpoint functional of (A_a-lambda I)^(-1) source
 = boundary observation of resolvent-dressed wall field,                  (7)
```

with sufficient domain/trace control to sum spectral modes and identify compensation in `(3)`.

## Hostile audit

1. **No raw endpoint equality.**  `b_e` is input Cholesky coordinate.
2. **No arbitrary observation sign.**  `(4)--(5)` concern source self-pair only; generic endpoint
   functional can change sign.
3. **Bilinear, not Hermitian square.**  Away from `t=0`, `omega_e^2` retains delay phase.
4. **Spectral center excluded.**  Zero-shift resolvent has pole at `s=0`.
5. **Actual operator not instantiated.**  Corpus lacks Lean construction of analytic
   restricted-Weil operator and endpoint trace domain.
6. **Negative modes not assumed.**  Conditional sign classification does not assert existence of
   negative spectrum and does not use RH or its negation.
7. **No estimates.**  Every identity is rational/exact prime-power algebra.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## Novelty audit

- Scalar resolvent identity and sign are already formalized `[BRIDGE]`.
- Prime-power square-root weld is parent result.
- Internal search found no theorem closing affine resolvent residual through exact
  Gamma/von-Mangoldt wall-field square or deriving weighted sign law `(3)--(5)`.
- Candidate novelty is exact source-specific composition and corrected endpoint architecture;
  external priority remains unverified.

## Formalization gates

- [x] exact paper derivation and source-type correction
- [x] dressed affine residual and rational formula
- [x] symmetric-square closure
- [x] strict positive/negative zero-height sign classification
- [x] unconditional Lean formalization
- [ ] actual restricted-Weil spectral measure and boundary observation
- [ ] mixed compensation block lower bound
- [ ] RH
