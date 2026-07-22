# CCM aperture-resolvent Riesz-sector frontier

- **ID:** `ccm-aperture-resolvent-riesz-sector`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE, `[OPEN RH CORE]`
- **Scientific status:** `[CONJECTURE] [CONNES/CCM SOURCE-SPECIFIC] [RH-SUFFICIENT GATE OPEN]`
- **Parent result:**
  `../2-fully-proven/new_scientific_knowledge/ccm-critical-mellin-aperture-resolvent-law.md`
- **Statement:** The unit aperture-resolvent mean of the normalized Chebyshev error has a
  one-sided all-epsilon subpower upper bound.

## Exact source target

Let

```text
E(X)=psi(X)-X,
J(X)=X^(-1) integral_0^X E(y)y^(-1/2)dy.                (1)
```

Prove directly from the completed von Mangoldt source that, for every `epsilon>0`, there are
`C_epsilon,N_epsilon` such that

```text
J(n) <= C_epsilon n^epsilon       for all n>=N_epsilon. (2)
```

No zero location, Weil positivity, real-rootedness, or RH-equivalent limiting measure may enter
the proof.

## Why this is the actual remaining Connes frontier

Exponential averaging over the true CCM rectangular aperture has already removed the fixed-width
filter phase:

```text
integral_0^infinity exp(-L)M_L(w)dL=-1/(w+1),           (3)
```

and the causal Volterra memory collapses exactly.  The averaged completed-error adjacent block is
`-J(exp x)`.  For every hypothetical zeta mode `w=rho-1/2` with `Re(w)>0`, `(3)` is nonzero and has
strictly negative real part.  Restricting widths to `L<=x/2` adds only an exponentially decaying
tail when `Re(w)<1/2`.  Neither censorship nor aperture boundary can remove an off-critical mode.

The missing statement is therefore not another filter estimate.  It is sector membership of the
actual integrated Chebyshev source `(1)`.

## Scientific-method attack

### Conjecture `CCM-APERTURE-RESOLVENT-RIESZ-SECTOR`

The signed Stieltjes source underlying `(1)` belongs to the upper subpower sector `(2)` after the
prime and polar channels are coupled before scalar absolute values.

### Falsifiable route

1. Derive the Mellin transform of `(1)` in its absolute-convergence half-plane.  Up to the finite
   `0<y<1` term it is

   ```text
   1/(s+1) * [
     -zeta'(s+1/2)/((s+1/2)zeta(s+1/2))
     -1/(s-1/2)].                                      (4)
   ```

2. Apply the power-corrected one-sided Landau argument.  This connector is now paper-proved in
   `../2-fully-proven/not_new_scientific_knowledge/ccm-unit-riesz-markov-virial-landau-law.md`:
   the transformed Markov--virial coefficient has every off-critical zero as a genuine pole and
   no matching real singularity at its nonnegative-function abscissa.
3. Attack `(2)` at source level using the exact Stieltjes form

   ```text
   integral_0^X psi(y)y^(-1/2)dy
    =2 sqrt(X) psi(X)-2 sum_(q<=X) Lambda(q)sqrt(q),     (5)
   ```

   retaining both terms as one compensated prime transport.  Separate absolute values are
   forbidden: they lose the RH-scale cancellation.
4. Hostile test any proposed positivity representation against complex amplitudes and sparse
   prime shells.  A positive kernel alone is insufficient because `E` is signed.

## Current status

- `[PROVED]` exact aperture-resolvent filter `(3)`;
- `[PROVED]` causal Volterra cancellation and source identity `(1)`;
- `[PAPER-PROVED]` admissible aperture tail cannot censor `0<Re(w)<1/2` modes;
- `[PAPER-PROVED]` one-sided Landau connector for the equivalent Markov--virial coefficient;
- `[OPEN RH CORE]` unconditional source-sector bound `(2)`.

RH is not proved.  Solving only the Landau connector does not prove RH; solving `(2)` plus that
connector does.

## Gates

- [x] 0 → 1: well-posed, source-pure, falsifiable, exact transform route
- [ ] 1 → 2: prove source bound `(2)` without zero assumptions
- [ ] 2 → 3: formalize source identity, connector, and composition to `RiemannHypothesis`
- [ ] 3 → 4: novelty and publication audit

## Log

- 2026-07-22 — created after aperture averaging eliminated detector-phase and admissible-tail
  obstructions; isolated weighted Chebyshev Riesz sector as surviving Connes source theorem.
