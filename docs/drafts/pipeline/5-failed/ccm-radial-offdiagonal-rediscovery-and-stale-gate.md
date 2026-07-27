# REDISCOVERED: the weighted radial off-diagonal charge was already proved — and why a stale gate caused it

- **ID:** `ccm-radial-offdiagonal-rediscovery-and-stale-gate`
- **Stage:** 5-failed (retired as duplicate)
- **Type:** REDISCOVERY RECORD + PROCESS FIX
- **Verdict:** `REDISCOVERED`
- **Read this before re-attempting:** the weighted radial off-diagonal charge, the far-field
  endpoint chirp, or the punctured Poisson dual of the CCM seed.

## What was attempted

A proof that the complete von Mangoldt-weighted off-diagonal radial Gram sum for the constrained
CCM `h_0`--`h_4` seed is `o(d_1)`, via

1. a far-field endpoint-chirp representation of `q_lambda`;
2. a uniform off-diagonal bound `|G_lambda(j,k)| <= C d_1/(c j k |j-k|)` for `j,k >= 2`;
3. a first-row bound and a seam analysis at `k ~ c`;
4. the exact partial-fraction row sum `sum_(j != K) 1/(j|j-K|) = (2H_(K-1) + H_K)/K`;
5. the punctured Poisson dual `b_lambda(s) = t^(-1/2) sum_(m>=1) g_lambda(m/t)`.

## What was already in the corpus (verified file by file)

| Attempted item | Already proved in |
|---|---|
| item 2, verbatim as `(8)` | `2-fully-proven/not_new_scientific_knowledge/ccm-exact-radial-nonstationary-sector-bound.md` |
| item 4, as `(9)`: `sum_(j>=2;j!=k) 1/(jk|j-k|) <= C(1+log k)/k^2` | same card |
| the weighted assembly, as `(10)`, including `sum_k log k(1+log k)/k^2` | same card |
| the first-row bounds | `ccm-exact-high-radial-first-row-bv-bound.md`, `ccm-exact-finite-aperture-first-row-vanishing.md`, `ccm-limiting-radial-first-row-weber-bound.md` |
| item 5, verbatim as `(19a)`--`(19b)`, including "the final term is exactly the Poisson center" and the finiteness of the `m`-sum | `2-fully-proven/needs-audit/constrained-prolate-continuous-polar-charge-law.md`; formalized in `ConstrainedProlatePoissonMuntz.lean` |

## What was outright WRONG

Item 1's amplitude constant. The attempt derived

```text
g_lambda(lambda)^2 = 4 pi lambda d_1        (WRONG)
```

by matching the far-field chirp against the **single-mode** radial density
`1/(pi x sqrt(x^2-1))` of `constrained-prolate-radial-leakage-divisibility-spectrum.md` eq `(15)`,
instead of the **constrained-source** density `(8/(11 pi))/(x sqrt(x^2-1))` of eq `(5)`. Redoing
the match with `(5)` gives `16 pi/11`, which is the value already proved — by a Hellmann--Feynman
identity, not by inverting a weak limit — in

```text
2-fully-proven/not_new_scientific_knowledge/ccm-constrained-endpoint-euler-response-constant.md, (13):
|g_lambda(lambda)|^2/(lambda d_1(lambda)) -> 16 pi/11.
```

The structural claim (far field is an endpoint chirp of frequency `lambda`, amplitude of order
`sqrt(lambda d_1)`) survives; only the constant was wrong, and all downstream bounds were stated
up to constants. But the *method* used to obtain it — inverting a weak limit pointwise with
`mean(sin^2) = 1/2` — is not a proof, and the corpus already had the correct proof.

## The process failure, and the fix

The attempt was launched off the gate list of
`2-fully-proven/new_scientific_knowledge/constrained-prolate-radial-leakage-divisibility-spectrum.md`,
which still shows

```text
- [ ] simultaneous weighted off-diagonal limit
```

That gate is **stale**: the work was completed in a *different* card
(`ccm-exact-radial-nonstationary-sector-bound.md`, `(8)`--`(10)`) and the parent's checklist was
never updated. Searching the parent card's own gates is therefore **not** a sufficient
novelty check in this corpus.

**Rule extracted:** before attacking any `[ ]` gate, grep the whole pipeline for the *statement*,
not for the gate text or the parent card. Cards in `2-fully-proven/not_new_scientific_knowledge/`
are exactly where completed bridges go, and they are easy to miss because their titles do not
repeat the parent's vocabulary.

## What survived, and is retained

- **The seam diagnosis.** The first-row transfer genuinely splits at `k ~ c`, because the
  stationary point `x_* = sqrt(1 + 1/k^2)` of the difference phase enters the endpoint boundary
  layer `x - 1 <~ c^(-2)` exactly there. The corpus states the same thing as "a hybrid transfer
  ... uniformly through `k/c`" (`ccm-exact-radial-nonstationary-sector-bound.md`, after `(11)`).
- **The structural reason no `1/lambda` gain exists in the far regime.** Integration by parts
  against a chirp of frequency `lambda k` gains `(lambda k)^(-1)` but costs a factor `lambda`,
  because `q_lambda` itself oscillates at frequency `lambda`. Net gain per integration by parts
  is `1/k`, never `1/lambda`. Consequently a first-row bound of pure size `d_1/k^2` yields only
  `O(d_1)` — the same order as the diagonal charge — so the stationary-phase `c^(-1/2)` is
  load-bearing. This is a correct and reusable observation about the lane.
- **The Lean module** `formal/GaloisForLFunctions/RHTower/RadialGramOffDiagonalDecay.lean`, which
  formalizes `(9)` and the convergence of `sum_k log k(1+log k)/k^2`. The source card explicitly
  recorded "No Lean file is added", so this is a genuine formalization of an existing bridge —
  labelled as such, not as new knowledge. Axiom-clean; lint passes.

## Status of the lane after this audit

`2-fully-proven/needs-audit/constrained-prolate-continuous-polar-charge-law.md` marks `(17)`, `(11)`, `(18)` and the exterior
seed law `(32)` all **proved on paper**, with only two gates left:

```text
- [ ] formalize the concrete radial-PSWF/Bessel realization and (51) unconditionally in Lean
- [ ] prove the true cofinal Weil floor (RH-bearing)
```

and it states that "any vanishing negative-floor allowance already proves RH; it is not
preliminary spectral engineering". So this lane's remaining items are exactly one formalization
task and one RH-equivalent statement. There is no third kind of open problem left in it.
