# Landau--Gonek Theta-One Disproof: Parity Obstruction

- **ID:** `landau-gonek-theta-one-disproof-parity-obstruction`
- **Stage:** 5-failed
- **Type:** FAILED ROUTE / claimed unconditional RH disproof
- **Scientific status:** `[REFUTED] [EXACT MAIN-TERM CANCELLATION] [NO RH CONSEQUENCE]`
- **Source:** Tatenda Kubalalika, *The Riemann Hypothesis is False*, 2026 preprint;
  `../2-fully-proven/needs-audit/kubalalika-parity-corrected-main-term-cancellation.md`;
  `../2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/kubalalika-parity-weighted-near-diagonal-tail.md`
- **Statement:** The proposed proof that the supremum `Theta` of the real parts of nontrivial zeta
  zeros equals `1` fails: the source omits a parity condition, and restoring it makes the two linear
  main terms cancel exactly.

## Goal

Audit the preprint's claimed unconditional proof that `Theta=1`, retaining any valid analytic
residue and refusing to formalize an assumed linear asymptotic as if it were a proof.

## Fatal Parity Omission

In the near-diagonal range the source writes `2n=m+r`. Since `n` is an integer, the new variables
must satisfy

`r congruent m (mod 2)`.                                  (1)

Equations (15)--(17) and (27)--(30) subsequently sum over every integer `r`; condition (1) has been
lost. For von Mangoldt weight, even `m` contribute only when `m` is a power of two and hence give
`o(T)`. The linear main term therefore comes from odd `m`, for which only odd `r` are admissible.

The source uses the full Fourier sawtooth

`sum_(r>=1) sin(r*theta)/r`.

The parity-correct expression is instead

`sum_(r odd) sin(r*theta)/r = (pi/4)*sgn(sin(theta))`      (2)

away from the jump points. The finite-sum error is `o(T)` after the same spacing count used by the
source, applied at both periods.

## Exact Cancellation

Let

`J(alpha)=alpha*integral_[alpha,infinity] sgn(sin x)/x^2 dx`.

The prime number theorem converts the corrected endpoint sum at `Y=alpha*T` into

`(T/4)*J(alpha)+o(T)`.

Since `H=2T+O(1)`, the large-`n` range contributes

`T/4*(J(1)-J(2))+o(T) = T*log(2)/(2*pi)+o(T)`.            (3)

The source's small-`n` Landau--Gonek range contributes

`-T*log(2)/(2*pi)+o(T)`.                                  (4)

Equations (3) and (4) cancel. The full sum has no nonzero linear main term from this decomposition,
so the asserted positive coefficient and the final contradiction do not survive.

## Audit Status

1. **Parity:** fatal omission found and corrected; the corrected main terms cancel exactly.
2. **Near-diagonal exponential tail:** the preprint differentiates in the wrong variable and then
   inserts `Lambda(m)` into an unweighted cancellation. A separate reciprocal-prime argument gives
   the genuinely required parity-weighted tail as `O(T^(53/54)log(T)^C)=o(T)`.
3. **Contour identity:** the contour lies between heights `T` and `H`, so the pole at `s=1` is not
   enclosed. This does not repair the parity failure.
4. **Final `Theta<1` bound:** even if this terminal comparison is granted, the required nonzero
   linear asymptotic has disappeared.

## Falsifiers

- Restoring the exact lattice condition `2n=m+r` must leave a nonzero linear coefficient. It does
  not: the coefficient cancels exactly.
- Any attempted resurrection must exhibit a separately derived order-`T` term omitted from the
  audited decomposition. Reusing the unrestricted sawtooth is invalid.

## Anti-Theatre Gate

- The exact substitution lattice was checked before accepting the Fourier main term.
- The valid parity-weighted tail estimate is retained, but it is not presented as progress toward a
  contradiction whose main term has vanished.
- No Lean capstone is created with the false linear asymptotic as a hypothesis.
- No numerical zero data or numerical constant evaluation was used.

## Open Core

`[CLOSED AS FAILED]` The route's load-bearing nonzero linear term is destroyed by the mandatory
parity condition. The positive residue is the independent parity-weighted `53/54` tail estimate and
the exact square-wave endpoint law, not an RH disproof.

## Gates

- [x] Finite statement and unconditional RH-disproof consequence identified.
- [x] Wrong-variable and invalid prime-weight insertion isolated.
- [x] Parity-weighted near-diagonal tail proved `o(T)` independently.
- [x] Lost congruence in `2n=m+r` identified.
- [x] Correct odd-harmonic Fourier law inserted.
- [x] Corrected endpoint main term derived from the prime number theorem.
- [x] Large- and small-`n` linear terms shown to cancel exactly.
- [x] Route retired without theorem theatre or conditional Lean packaging.

## Log

- 2026-07-17 -- Opened after direct inspection of the nine-page 2026 preprint.
- 2026-07-17 -- Corrected the initial repair attempt: an unweighted oscillatory estimate cannot be
  promoted through the pointwise bound on `Lambda`.
- 2026-07-17 -- Closed the tail gap independently: reciprocal-prime estimates give
  `O(T^(53/54)log(T)^C)` with `Lambda(m)` retained.
- 2026-07-17 -- Found the fatal lattice omission: `r congruent m (mod 2)`. The parity-corrected
  square-wave main term is `+T log(2)/(2*pi)` and cancels the small-`n` Landau--Gonek term exactly.
  Retired the route; no Lean theorem was created from the false source asymptotic.
