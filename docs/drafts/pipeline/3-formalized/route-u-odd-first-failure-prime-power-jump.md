# Route U odd first-failure prime-power jump

- **ID:** `route-u-odd-first-failure-prime-power-jump`
- **Stage:** 3-formalized
- **Type:** THEOREM / arithmetic quantization of odd-sector failure
- **Routes:** U primary
- **Source:** literal hard-edge density and parity-jet odd form

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

Route U retains a state whose restricted-Weil form is nonnegative at every smaller aperture, but
whose odd descendant may fail at the self-selected critical aperture.  Can this failure arise by
continuous archimedean drift at an arbitrary aperture, or must it be carried by a literal new
prime--Gamma source atom?

## Theorem U-JUMP

The literal hard-edge density is

```text
V_sigma(x) = theta_infinity(x)
  - sum_{2 <= m <= floor(exp(2 sigma))}
      Lambda(m)/sqrt(m) cos(x log m).                         (1)
```

Its archimedean term is independent of `sigma`; aperture enters only through the integer cutoff.
Define the incoming point below the `n`th wall by

```text
sigma_n^- = (1/2) log(n - 1/2),       n >= 2.                (2)
```

Lean proves

```text
floor(exp(2 sigma_n^-)) = n-1,
floor(exp(2 * (log n)/2)) = n,
sigma_n^- < (log n)/2.                                      (3)
```

Hence the exact right-continuous density jump is

```text
V_(log n/2)(x)
  = V_(sigma_n^-)(x) - Lambda(n)/sqrt(n) cos(x log n).       (4)
```

For an odd squared-variable state `H`, let `J_n(H)` be the integral response of the one new atom:

```text
J_n(H) = integral_(u>0)
  u H(u)^2 Lambda(n)/sqrt(n) cos(sqrt(u) log n)/sqrt(u) du.  (5)
```

Under exactly the two integrability hypotheses needed for integral linearity,

```text
OddForm_(log n/2)(H)
  = OddForm_(sigma_n^-)(H) - J_n(H).                        (6)
```

Therefore incoming nonnegativity and outgoing negativity imply `J_n(H)>0`.

Most importantly, suppose for one fixed `H`

```text
OddForm_sigma(H) < 0,
OddForm_tau(H) >= 0 for every tau < sigma,
floor(exp(2 sigma)) >= 2.                                  (7)
```

Then unconditionally

```text
exists n >= 2,
  IsPrimePow(n),
  sigma = (log n)/2.                                      (8)
```

Thus a first odd-sector failure is quantized to a literal prime-power wall.

## Heavy conjecture loop

### U-J1 — continuous Gamma drift can create first odd failure

**Conjecture.** The hard-edge form varies continuously with aperture, so its odd eigenvalue can
cross zero at an arbitrary real `sigma`.

**Attack.** Inspect the actual density rather than its conceptual description.  The Gamma--Hardy
rate has no aperture parameter.  Between consecutive values of `floor(exp(2 sigma))`, the entire
density and every even/odd form are exactly constant.

**Verdict:** false.  There is no continuous within-chamber drift.

### U-J2 — a cutoff wall at a composite non-prime-power can carry failure

**Conjecture.** Integer cutoff jumps alone quantize failure, but any integer wall is possible.

**Attack.** The newly entering coefficient is exactly `Lambda(n)`.  If `n` is not a prime power,
`Lambda(n)=0`; Lean proves the densities and odd forms on the two adjacent chambers are identical.
This contradicts a first sign loss.

**Verdict:** false.  Only prime-power walls survive.

### U-J3 — the surviving wall has a signed one-atom law

**Conjecture.** Even at a prime-power wall, only support changes; no exact odd response can be
isolated because the hard-edge form contains a polar atom and an improper integral.

**Attack.** The polar term is independent of aperture and cancels.  Under the two explicit
integrability conditions, linearity of the Lebesgue integral turns `(4)` into `(6)` with no
remainder.  Sign loss forces the entering response strictly positive.

**Verdict:** proved on paper and in Lean.

### U-J4 — positive jump response already contradicts the source

**Conjecture.** `J_n(H)>0` conflicts with von Mangoldt positivity.

**Attack.** `Lambda(n)>0`, but cosine response is signed; positive `J_n(H)` is compatible with the
new atom lowering the Weil form.  Positivity of the arithmetic coefficient alone gives no
contradiction.

**Verdict:** failed.  Remaining producer is an exact comparison between incoming odd margin and
the single prime-power response, not a sign slogan.

## Dependency-closed proof

Inside one floor chamber, equality of frequency bounds makes `(1)` definitionally identical, so
every hard-edge pairing is identical.  If `X=exp(2 sigma)` is not its natural floor `n`, choose

```text
Y=(n+X)/2,
tau=(log Y)/2.
```

Then `tau<sigma` and `floor(exp(2 tau))=n`.  A negative form at `sigma` would equal the form at this
strictly smaller `tau`, contradicting `(7)`.  Hence `X=n`, so `sigma=log n/2`.

The explicit incoming aperture `(2)` has cutoff `n-1`.  If `Lambda(n)=0`, the finite-sum successor
identity makes both adjacent densities equal, again contradicting `(7)`.  Thus `Lambda(n)!=0`, and
the exact mathlib support theorem for von Mangoldt gives `IsPrimePow(n)`.  Expanding the same
finite-sum successor identity without setting `Lambda(n)=0` proves `(4)`.  Integral subtraction
then proves `(6)` and its strict response sign.

## Higher universal principle

**Hard-edge aperture is an arithmetic staircase, not a continuous deformation.**  Gamma supplies
the fixed chamber background; prime powers are the only walls.  A first spectral sign change is
therefore a codimension-one source event carried by one von Mangoldt atom.

This reinterprets Route U's former “odd-sector admission” problem.  For the fixed limit state to
remain nonnegative below critical aperture but fail at critical aperture, it must meet a single
prime-power wall with enough positive cosine response to exhaust the incoming margin.  Root-jet
geometry determines candidate state; prime-power incidence determines crossing.

## Significance and positive survivor

The simple critical-ground branch no longer needs a global odd-sector theorem across all
apertures.  Its exact surviving inequality at one prime power `n=p^k` is

```text
J_n(H) <= OddForm_(sigma_n^-)(H).                            (9)
```

Proving `(9)` for the source-selected divided state prevents first failure.  Alternatively, finite
first-contact ancestry may identify strict violation of `(9)` with a super-apex or radial-flux
event.  Either route is source-specific and one-atom; more continuous aperture compactness cannot
advance it.

In the degenerate branch, the same theorem localizes every negative terminal odd signature to one
prime-power wall before parity-doubled nullity is invoked.  The higher contact source must therefore
be compared to that wall atom, not to an unspecified full Euler tail.

## External novelty audit

- Classical explicit formulae identify `Lambda(n)` as supported on prime powers; see Weil's
  explicit-formula framework and modern localized Weil-form discussion.
- Suzuki's recent screw-function treatment contains cutoff sums over `n <= exp(|t|)` and localized
  Weil operators, <https://arxiv.org/abs/2606.09096>.
- Targeted searches on 2026-08-16 found no external theorem proving that first loss of the literal
  Route-U odd hard-edge form is forced to an exact prime-power aperture, no incoming chamber
  formula `(2)`--`(4)`, and no one-atom odd-response law `(6)` for the source-selected hard-edge
  state.  Novelty remains unverified and is not claimed.

## Gates

- [x] 0 -> 1: hostile continuous-drift and non-prime-wall conjectures; exact survivor
- [x] 1 -> 2: dependency-closed proof and external novelty audit
- [x] 2 -> 3: unconditional Lean theorem, direct check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeOddFirstFailurePrimePowerJump.lean`.

Capstones:

- `routeUHardEdgeDensity_log_nat_half_eq_incoming_sub_primeJump`;
- `routeUHardEdgeOddForm_log_nat_half_eq_incoming_sub_primeJumpResponse`;
- `routeUHardEdgePrimeJumpOddResponse_pos_of_sign_loss`;
- `exists_primePower_of_routeUOddForm_firstFailure`.

Direct `lake env lean` and exact leaf `lake build` succeeded.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  Forbidden declaration scan is clean.  Module is imported by
`RHTower.lean`; no umbrella or full-project build was run.

## Log

- 2026-08-16 — Continuous aperture-drift conjecture falsified from literal density.
- 2026-08-16 — First odd failure classified at a prime-power wall.
- 2026-08-16 — Exact one-atom response and strict sign formalized and axiom-audited.
