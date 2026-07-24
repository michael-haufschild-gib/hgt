# Chart–Region Exchange and Margin–Supply Legendre Neutrality

- **ID:** `xi-ward-chart-exchange-legendre-neutrality-obstructions`
- **Stage:** 1-in-progress
- **Type:** TWO NO-GO THEOREMS with positive residues (direct-core attack round)
- **Scientific status:** `[PAPER-PROVED BY AGENT ROUND] [NEEDS DESK AUDIT] [NOT LEAN YET] [NOT RH]`
- **Source:** hgt-fields-medalist direct attack round 2026-07-24 (report logged on
  `ht-capacity-ward-holonomy-rh.md`); parent objects in
  `XiWardZeroFreeMarginPrimeLogSampling.lean` and the Ward criterion family.

## Theorem A† (Chart–Region Exchange)

> For `σ₀ ∈ (1/2, 1)`: an *arithmetic chart certificate* on `Re s > σ₀` — a
> sequence of finite prime data (finite Euler logs plus counterterms) with a
> modulus of uniform convergence on compacts of the half-plane — exists if and
> only if ζ is zero-free on `Re s > σ₀`.

Proof outline (both directions elementary given corpus assets):
(⇐) On the zero-free region define `P := log Z_sq − log D₂` branch-wise; the
finite Euler sums converge uniformly on compacts by standard zero-free-region
partial summation.  (⇒) A uniform-on-compacts limit of entire finite stages is
holomorphic and single-valued; its exponential recovers the transition datum,
so no zero of multiplicity `m ≥ 1` can sit in the region (its loop charge `m`
would be the limit of the finite-stage loop charges, all zero — Hurwitz).
Partial summation back out gives `π(x) − Li(x) ≪ x^{σ₀+ε}`, i.e. the region.

**Content:** cocycle triviality cannot be forced by chart refinement —
`H¹`-vanishing supply *is* the zero-free region; the cartography lane is
margin-bounded by theorem.  **Positive residue:** since finite
exponential/character stages carry zero winding, any finite-stage carrier of
the divisor must be *quadratic* (Ward matrices; Bombieri truncation
eigenvalues — which provably do carry it).

## Theorem B† (Margin–Supply Legendre Neutrality)

> Consider the transfer loop
> `[zero-free margin exponent A] → [ψ-error exponent θ = 1/(A+1)] →
> [shrinking-window prime supply] → [adapted two-channel Weil test] →
> [output margin exponent A_out]`.
> Then `A_out = (1−θ)/θ = A` for every `A`: the loop is the identity on the
> exponent ladder, and strictly contractive on constants (the optimized
> `max_S [c·S^θ − m·S]` at `m = c'/log^A` yields output constant
> `K = ((A)c/(A+1))·(c/(A+1))^{1/A}/c'^{1/A} < 1` throughout the realizable
> constant range; closure would need a region→PNT transfer constant
> `> ((A+1)/A)^{A/(A+1)}·(A+1)^{1/(A+1)} ≈ 1.384` at `A = 9`, while all
> norm-type contour transfers have constant `< 1`).

**Content:** no iteration of norm-type explicit-formula arguments escapes its
input exponent class; RH sits in the power-savings class `θ = 1`, unreachable
from any log-savings class.  The corpus's two formalized constants — margin
exponent `9` and PNT exponent `1/10` — are exactly Legendre-dual: a new
conservation law of the formalized corpus.  The Beurling counterfeit
(Diamond–Montgomery–Vorhauer: generalized primes with better PNT error and
near-dlVP zeros) shows the loop's input class genuinely cannot exclude zeros:
the loop never consumes more than Beurling-available data plus additive FE
corrections.  **Positive residue:** the sole surviving currency is multi-node
positivity (sign, not size) — Ward/Weil quadratic forms.

## Edge blindness (companion identity)

> `Re (ξ'/ξ)(1/2+it) = 0` wherever `ξ(1/2+it) ≠ 0`.

Since `ξ` is real on the critical line (Schwarz reflection + FE),
`d/dt ξ(1/2+it) = i·ξ'(1/2+it)` is real·i, so `ξ'/ξ` is purely imaginary on
the line.  The full logarithmic derivative is blind to off-line pairs on the
edge; only *relative* positivity (the strict-right sub-sum `r`, Weil/Ward
forms) detects the divisor split — the precise reason the Ward lane's
`Re r ≥ 0` carries information at all.  Small, Lean-ready.

## Gates

- [ ] desk-audit A† (uniform-convergence ⇒ chart single-valuedness; the
      partial-summation constants; the Hurwitz loop-charge limit)
- [ ] desk-audit B† (the Legendre computation symbolically — no numerics in
      the promoted proof; the "all norm-type transfers have k < 1" clause
      needs a precise class definition or a downgrade to the audited cases)
- [ ] formalize edge blindness (needs corpus ξ reality-on-line assets)
- [ ] formalize A† (Hurwitz/loop-charge machinery; corpus monodromy
      quantization at `prime-boundary-perturbative-jet-monodromy-escape`)
- [ ] state B† as a precise theorem about a defined transfer-operator class,
      then formalize the exponent-identity part

## No-go closure

- **Exact killing mechanism:** A† kills chart/cocycle refinement supply;
  B† kills all norm-type explicit-formula loops (size-based transfers).
- **Strongest positive survivors:** finite-stage quadratic carriers (Ward
  matrices); threshold-8 doubled budget; the 2×2 moiré family
  (`xi-ward-moire-prime-pair-attack.md`).
