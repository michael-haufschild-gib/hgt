# Adaptive even-contact arithmetic source and one-block capacity

- **ID:** mass-shifted-adaptive-even-contact-source-one-block-capacity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, after (9.3.406)
- **Statement:** At every first nonzero even Padé contact, admitted lift `P X^(m-1)` emits completed mixed arithmetic source `2(n+m) delta_(2n+2m)`; positive rank fill survives exactly one Hankel block and next block is indefinite.

## Goal

Replace vague “cofinal rank plateau” by exact admission-sensitive arithmetic law. This is not an
orientation map: flat face first selects monic null amplitude `P`; parity lift is applied to that
amplitude; adaptive Euler shear is formed bilinearly; completed rational-Gamma/von-Mangoldt
aggregate is formed last.

## Gates

- [x] 0 → 1 in-progress: exact source type and hostile counterexample audit
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [ ] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: independent novelty/priority audit

## Exact theorem `[PROVED HERE]`

Let `s` be shifted-Xi real reciprocal moments at mass `y>0`. Let `c` define a flat Hankel face,
with nonzero terminal coefficient, and let `P` be its terminal-normalized monic null polynomial of
degree `n`. Write `delta_k` for difference between `s_k` and canonical finite-atomic flat shadow.
Fix `m>0` and assume

```text
delta_k = 0 for k < K := 2*n + 2*m.
```

Put `A_m := P * X^(m-1)`. Then completed adaptive mixed-amplitude source satisfies

```text
S_mix^sharp(y, A_m) = 2 * (n+m) * delta_K.                 (ECS.1)
```

If `delta_K > 0`, then

```text
H_(n+m+1)(s) is PSD, but H_(n+m+2)(s) is not PSD.         (ECS.2)
```

Same statements hold for actual inverse-Hankel canonical admission vector at flat face.

## Proof

Existing adjacent-defect arithmetic law applied at lift `m-1` gives

```text
S_mix^sharp(y, P X^(m-1))
 = 2 * ((2(n+m-1)+1) P.nextCoeff * delta_(K-1)
        + (n+m) * delta_K).
```

Contact hypothesis kills `delta_(K-1)`, proving (ECS.1). This uses literal completed packet,
already identified with common-amplitude rational-Gamma continuum minus von Mangoldt formation,
so equality is source-first and pre-reflection.

For first half of (ECS.2), flat atomic Hankel block of size `n+m+1` is PSD and only new entry is
terminal rank-one correction `delta_K e e^T`. Positivity of `delta_K` makes correction PSD.

For second half, set

```text
U := P X^(m-1),    V := P X^(m+1).
```

Both lie in polynomial coordinate space of `H_(n+m+2)`. Atomic flat shadow annihilates every
multiple of `P`. Since `deg(U^2)=K-2`, contact hypothesis gives `L_s(U^2)=0`. Meanwhile

```text
U*V = P^2 X^(2m) = (P X^m)^2,
```

and monicity plus vanishing below `K` gives `L_s(UV)=delta_K != 0`. If `H_(n+m+2)` were PSD,
zero quadratic energy of `U` would put its coefficient vector in matrix kernel, forcing pairing
with every visible vector—including `V`—to vanish. Contradiction. Thus next block is indefinite.

Every dependency is already proved in corpus: flat atomic shadow, adjacent-defect source law,
even-contact rank-one fill, first-contact square identity, and PSD zero-energy kernel rigidity.

## Hostile audit

- `m=0` is excluded: no predecessor lift `X^(m-1)` exists. First visible even successor is `m=1`.
- No sign is inferred from finite face. `delta_K>0` is explicit first-even contact orientation;
  (ECS.1) transports it into source and (ECS.2) classifies exact capacity.
- No RH-equivalent positivity is assumed. Theorem allows next block to fail and therefore does not
  prove RH.
- Degenerate Hamburger extension/kernel-ideal mechanism is classical; external frontier includes
  Bolotnikov’s PSD Hankel extension analysis and recurrence-rank/finite-atomic moment theory.
  Scientific delta is shifted-Xi arithmetic-source identification plus exact one-block exhaustion,
  not generic flat-extension fact.
- Fixed reporter objection does not apply: amplitude is admitted before shear; result is completed
  mixed source itself.

## No-go closure

- **Exact killing theorem/mechanism:** Conjecture that positive even contact can sustain arbitrary
  rank-filled plateau is false. Older zero-norm lift pairs nontrivially with two-step successor.
- **Strongest positive survivor:** (ECS.1)–(ECS.2), completed even-contact source plus exact one-block
  capacity.
- **New insight:** One fixed flat face never supports unbounded rank fill. Remaining escape is only
  nonuniform drift of first contact order/face degree across cofinal family.
- **Status:** paper-proved; Lean pending.

## Log

- 2026-08-11 — conjectured, hostile-audited, paper-proved; moved directly to Stage 2.
