# Route U prime-wall endpoint invisibility

- **ID:** `route-u-prime-wall-endpoint-invisibility`
- **Stage:** 3-formalized
- **Type:** THEOREM / source-wall rigidity
- **Routes:** U primary
- **Source:** odd first-failure prime-power quantization and Suzuki logarithmic form domain

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

At a first odd Route-U loss, the arithmetic staircase theorem forces the critical aperture to a
prime-power wall `sigma=log(n)/2` and makes the entering atom's response strictly positive. Must
that response be oriented by a new arithmetic inequality, or is it already constrained by
hard-edge Paley--Wiener admission?

## Theorem U-ENDPOINT

Let

```text
g(x) = x H(x^2),
b = log(n)/(4 pi),
n >= 2.
```

Assume `g` is in `L2(R)` and its mathlib-normalized Fourier transform vanishes almost everywhere
outside `[-b,b]`. Then the exact entering prime-wall response vanishes:

```text
routeUHardEdgePrimeJumpOddResponse n H H = 0.               (1)
```

At wall `sigma=log(n)/2`, the prime atom has physical cosine frequency `log(n)=4 pi b`.
Consequently, whenever the two literal hard-edge integrals exist,

```text
OddForm_(log(n)/2)(H) = OddForm_(incoming(n))(H).            (2)
```

In particular, incoming nonnegativity implies wall nonnegativity. Membership of `g` in Suzuki's
exact logarithmic form domain at aperture `b` supplies the Fourier-support premise of `(1)`
without any regularity upgrade.

All statements are unconditional: no RH premise, added axiom, numerical certificate, or
computational evaluation occurs.

## Heavy conjecture loop

### U-E1 — entering prime atom needs a source-specific sign inequality

**Conjecture.** After first-failure quantization, progress requires comparing incoming odd margin
against a positive von Mangoldt cosine response.

**Attack.** Rewrite squared-variable odd response on full real line. It is a constant multiple of

```text
integral g(x)^2 cos(log(n) x) dx.
```

At wall, `g` has Fourier bandwidth `b=log(n)/(4 pi)`. Displayed coefficient is exactly extreme
difference frequency `2b` in mathlib's Fourier normalization.

**Verdict:** false under genuine endpoint admission. Response is zero, not merely bounded.

### U-E2 — endpoint overlap may carry a nonzero boundary contribution

**Conjecture.** Fourier supports of `g` and its extreme translate touch at one endpoint, so inner
product can retain a boundary atom.

**Attack.** Work in `L2`, not pointwise Paley--Wiener representatives. Translated supports
intersect only at singleton endpoint, which is Lebesgue-null. Plancherel gives exact orthogonality.

**Verdict:** false. Endpoint contact contributes no `L2` mass. Proved in Lean without pointwise
Fourier inversion.

### U-E3 — Suzuki admission controls only inverse-Fourier support

**Conjecture.** Corpus form-domain predicate cannot feed endpoint theorem because it stores compact
support on inverse-Fourier side.

**Attack.** Use Fourier-squared reflection. Reflection preserves symmetric aperture interval, so
inverse-Fourier support implies forward-Fourier support almost everywhere.

**Verdict:** false. Exact adapter is Lean-proved.

### U-E4 — endpoint invisibility closes Route U

**Conjecture.** Since every admitted first prime wall is invisible, Route-U first crossing is fully
excluded.

**Attack.** Audit finite-to-limit bridge. Existing compactness preserves smaller-aperture
nonnegativity under form-domain domination, but corpus does not yet prove source-selected divided
odd descendant is an element of critical Suzuki form domain with required identification and
integral hypotheses.

**Verdict:** failed. Prime-wall orientation is closed; odd-state admission and source-derived
incoming-to-wall passage remain. Degenerate parity-doubled first birth still needs its own source
contradiction.

## Dependency-closed proof

Let `u` be complex `L2` image of `g`. If `Fourier(u)` is supported in `[-b,b]`, multiplication of
`u` by phase of normalized frequency `-2b` translates `Fourier(u)` by `2b`. Original and
translated supports are disjoint except at `-b`, hence

```text
inner u (phase(-2b) u) = 0.                                 (3)
```

Taking real parts of `(3)` gives

```text
integral g(x)^2 cos(4 pi b x) dx = 0.                       (4)
```

Substitute `b=log(n)/(4 pi)`. Exact squared-variable substitution already proved for Route-U jump
turns `(4)` into `(1)`. Literal finite-sum successor law says wall form is incoming form minus that
response, proving `(2)`.

For Suzuki admission, form-domain embedding fixes inverse Fourier transform under central-interval
cutoff. Fourier inversion in `L2` identifies forward transform with reflection of that compactly
supported vector. Symmetry of interval supplies support hypothesis used above.

## Higher universal principle

**A hard source wall placed at twice state bandwidth is spectrally invisible in quadratic
energy.** Prime-power quantization and Paley--Wiener admission are not separate constraints: wall
frequency is exactly extremal difference frequency of admitted aperture. Apparent jump-orientation
problem was shadow of endpoint support geometry.

This changes Route U's open core. No stronger inequality for entering von Mangoldt atom is needed
once admission is established. Progress must now prove source-selected odd descendant reaches
exact endpoint form domain and inherits incoming nonnegativity; otherwise obstruction occurs
before, not at, arithmetic jump.

## Significance and positive survivor

Combining U-ENDPOINT with earlier first-failure theorem gives contradiction schema:

```text
first odd loss
  -> prime-power wall and strictly positive entering response
  + endpoint Suzuki admission
  -> entering response = 0.
```

Thus simple odd first loss is impossible after admission bridge. Strongest positive survivor is
exact no-loss theorem `(2)`, not a proposed source sign. Remaining work is sharply localized to
form-domain admission/incoming nonnegativity and separate degenerate branch.

## External novelty audit

- Andersen--de Jeu develop real Paley--Wiener support theory for `Lp` functions and distributions,
  <https://arxiv.org/abs/0804.3014>.
- Targeted searches on 2026-08-16 found classical bandwidth/support results but no theorem joining
  literal shifted-Xi hard-edge aperture `log(n)/2`, its entering von Mangoldt atom, Suzuki's
  logarithmic form domain, and exact vanishing of odd prime-wall response.
- No external novelty claim is made; this card records a corpus-specific theorem and unsuccessful
  collision search.

## Gates

- [x] 0 -> 1: jump-orientation conjecture attacked; endpoint-invisibility survivor isolated
- [x] 1 -> 2: dependency-closed proof and external novelty audit
- [x] 2 -> 3: unconditional Lean theorem, direct checks, exact leaf builds, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Modules:

- `formal/GaloisForLFunctions/RHTower/L2FourierEndpointOrthogonality.lean`;
- `formal/GaloisForLFunctions/RHTower/SuzukiHlogEndpointSupport.lean`;
- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeOddPrimeWallEndpointInvisibility.lean`.

Capstones:

- `integral_sq_mul_cos_four_pi_eq_zero_of_bandSupport`;
- `suzukiHlogFormDomain_fourier_bandSupport`;
- `routeUHardEdgePrimeJumpOddResponse_eq_zero_of_suzukiHlogAdmission`;
- `routeUHardEdgeOddForm_log_nat_half_eq_incoming_of_bandSupport`;
- `routeUHardEdgeOddForm_log_nat_half_nonneg_of_incoming_and_bandSupport`.

Each module passed direct `lake env lean`; each exact leaf target passed `lake build`. Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`. Forbidden declaration scan is clean.
All three modules are imported by `RHTower.lean`; no umbrella or full-project build was run.

## Log

- 2026-08-16 — Jump-orientation conjecture replaced by endpoint orthogonality.
- 2026-08-16 — Suzuki inverse/forward support adapter and literal prime-wall no-loss theorem proved.
- 2026-08-16 — Lean modules checked, exact leaf-built, axiom-audited, and wired.
