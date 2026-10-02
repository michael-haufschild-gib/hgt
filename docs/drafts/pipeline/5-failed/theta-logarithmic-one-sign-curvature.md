# Route RN: eventual one-sign logarithmic curvature is impossible

- **ID:** RN-P-7a
- **Stage:** 5-failed
- **Type:** FALSIFIED (eventual one-sign mechanism); THEOREM (Lean, cofinal two-sign survivor)
- **Source:** `docs/reports/rh-current-frontier-map.md`, Route RN; RN conjecture-loop log.
- **Statement:** For every `N`, there are `m≥N` with `(log k)^(2m)(0)>0` and with `(log k)^(2m)(0)<0`, for the literal completed theta source `k`.

## Goal

Test the all-even curvature-sign mechanism suggested by the successful
fourth-log derivative argument. This is a statement about the actual source,
not a Gaussian countermodel or numerical jet computation. It does not settle
the all-rank Schur residual conjecture or RH.

## Gates

- [x] Source-pure formulation and corpus search.
- [x] Dependency-closed paper proof below.
- [x] Lean leaf compiled, wired, and axioms audited.
- [x] Final `lake env lean` leaf audit passed, exit 0, no warnings.

## Paper proof [PROVED HERE]

Write `φ` for the corpus's complex theta source, analytic on
`|Im z|<B`, where `B=π/4`, and positive on the real axis. The corpus proves
an actual zero `ζ=i t`, `0<t<B`. Define `g(z)=z φ'(z)/φ(z)`.

Since `φ(0)>0`, analytic continuation of analytic order on the connected
strip shows that the zero at `ζ` has finite positive order `n`. The existing
logarithmic-derivative residue theorem gives
`(z-ζ)g(z)→ζ n≠0`. Let `p` be the canonical Taylor series of `g` at zero.
Its radius is positive. If its radius were at least `B`, its sum would be
analytic on the ball of radius `B`. Meromorphic identity continuation from
the initial Taylor germ would identify it with `g` on punctured neighborhoods
throughout that ball, including at `ζ`. Multiplying by `z-ζ` would then give
both limits zero and `ζ n`, a contradiction. Thus its radius `R` satisfies
`0<R<B`.

The real Taylor coefficients are
`a_j=j*(log k)^(j)(0)/j!`: differentiating `x*(log k)'(x)` proves
`g^(j)(x)=x*(log k)^(j+1)(x)+j*(log k)^(j)(x)` on the real axis.
Odd coefficients vanish by the source's modular reflection.

Suppose the coefficients are eventually nonnegative. Subtract the finite
initial Taylor polynomial. The remaining series has nonnegative coefficients
and unchanged radius `R`, because adding or subtracting a polynomial cannot
alter the radius. Its sum agrees meromorphically with `g` minus that polynomial
on the ball of radius `R`. The latter function is analytic at the positive
real boundary point `R`, since `φ(R)>0`. This supplies the continuation across
`R` forbidden by the corpus's Vivanti--Pringsheim theorem. Thus coefficients
are not eventually nonnegative. Applying the same argument to `-g` excludes
eventual nonpositivity.

Both signs therefore occur beyond every index; odd coefficients vanish,
so both occur beyond every even index. For positive even `j`, the multiplier
`j/j!` is positive. The corresponding logarithmic center jets have both signs
cofinally, as claimed.

## No-go closure

- **Killing mechanism:** Neither eventual orientation of all even logarithmic
  center derivatives is possible. The literal source zero, positive real
  analyticity, and Pringsheim force arbitrarily late violations.
- **Strongest positive survivor:** The exact cofinal two-sign logarithmic-jet
  theorem, with the retained pole and strict Taylor-radius bound.
- **New insight:** Fourth-log negativity cannot be iterated into an eventual
  all-even curvature cone. An all-rank Schur proof must control signed projected
  source derivatives; scalar `p(x)/x` monotonicity alone has not supplied that
  control.
- **Status:** Paper dependency-closed and formalized in
  `ThetaCuspLogJetOscillation.lean`, namespace `RHTower.ThetaLogJet`.
  `logJet_cofinal_positive` and `logJet_cofinal_negative` quantify only over
  `N : ℕ`; no conjectural source premise. `radius_lt_strip` retains the actual
  pole argument. The targeted `lake --old build` passed. All five public
  theorems have only `propext`, `Classical.choice`, and `Quot.sound` in their
  axiom audit. The leaf is wired into `RHTower.lean`; final direct leaf audit
  passed. No unconditional all-rank sign result or RH proof follows.

## Verification scope

The complete proof and API checks passed in `/tmp/rn_log_jet_check.lean`.
`lake --old build GaloisForLFunctions.RHTower.ThetaCuspLogJetOscillation`
passed; no umbrella build was run. `scripts/formal_tools.py lint` found no
issue in the new leaf, but failed on 11 unrelated unwired modules recorded
in the RN working log. No numerical jet evaluation, new axiom, or heartbeat
increase was used.

Final audit:
`lake env lean GaloisForLFunctions/RHTower/ThetaCuspLogJetOscillation.lean`
passed with exit 0 and no output.

## Log

- 2026-10-02 — Corpus-grounded paper proof; local meromorphic Pringsheim
  adaptation and literal-source coefficient bridge formalized. Eventual
  curvature-sign branch retired with its exact two-sign positive survivor.
