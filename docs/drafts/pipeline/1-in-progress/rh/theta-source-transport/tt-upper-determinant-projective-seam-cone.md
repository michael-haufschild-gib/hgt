# Complete upper determinant on the projective seam source cone

- **ID:** TT-C115-UPPER-DETERMINANT
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Route TT; current corpus full weighted quadratic and C114 source seam tube.
- **Statement:** The complete actual upper-center determinant at load 10^13 is strictly positive for every center x>0.

## Hard target and stronger candidate

Let `Q=upperCenterDeterminant (10000000000000:ℂ)`, retaining every native
source moment through order fourteen, all cofactor terms, and the entire
load contribution. The actual-source target is
`0<(eval (actualSquarePoint x) Q).re` for every x>0, with no missing source
sign assumed.

The stronger candidate is positivity on the following semialgebraic region.
Put `h=1/K`, `r=K²(9-U)`, `a=K(1-3Z)` and require

- `0<U<9`, `K>5/4`, `0<Z<1/3`, `0<r≤361/25`;
- `r*(1/12-7h/72)<a-h²a²`;
- `r-6K-4+2U(K+2/3)Z>0`;
- `0<(9-U)(9K²-6K-4-9KZ)<6KU`.

Each constraint comes from the current actual-source corpus; no numerical
sampling or literature assumption defines this candidate. Sufficiency is
unproved. A counterexample to this enlarged region would require another
source correlation, not imply failure of the actual determinant or RH.

## Attack and current evidence

Actual all-direction upper-quadratic positivity near the seam and complete
actual upper-determinant positivity in the tail are already production
theorems. Neither proves the intervening sign. The new tube removes
nonphysical seam values of the projective coordinate.

The immediate algebraic work extends the exact weightedJet recurrence from
the clean general tenth jet to orders eleven through fourteen. Lean proves
each polynomial identity and performs every coefficient normalization.
External scripts only transcribe verified printed expressions, regroup
syntax, and generate bounded proof obligations; no coefficient arithmetic,
numerical experiment, CAS, truncation, or added premise is used.

The full normalized determinant is then tested against the displayed source
constraints. A positive certificate must include every term. A failed sign
candidate must retain a proved obstruction and its strongest positive
survivor before any route retirement.

## C115 second sign candidate: propagation from the terminal limit

The same complete polynomial admits a second, source-derived sign test.
The corpus proves that the actual `Q/k^34` tends to a complex number with
strictly positive real part, and that U tends to 9. The seam scaling of the
quadratic suggests examining

`N(x) = Re Q(actualSquarePoint x)/(u(x)^52*k(x)^34)`.

**Conjecture, not proved:** N is nonincreasing on the entire positive ray.
Its already-established terminal normalization would give a strictly
positive limit `L/9^26`, where L is the real leading coefficient of the
terminal determinant. Monotonicity would therefore imply the desired
global determinant sign. No monotonicity premise is added to Lean.

Here is the exact polynomial obstruction to test. Write F for squareLie,
so `F_U=12UK(9-U)`, `F_K=(12K+4)UZ`, and the actual time derivative is
F/(6u). Set

`H = K*F(Q) - 26*K*(12K*(9-U))*Q - 34*((12K+4)*UZ)*Q`.

The chain and quotient rules give

`N' = Re H(actualSquarePoint x)/(6*u*U^26*K^35)`.

The denominator is positive. Thus a complete nonpositive source certificate
for H would propagate the proved positive terminal limit backwards across
the missing compact interval. The exponent 34 comes from the audited
terminal polynomial degree; 26 corresponds to the seam source scaling,
not a fitted numerical parameter. C116 now supplies a dependency-closed
proof of the exact global U^26 factorization, now audited in three production
leaves with all 19 public declarations using only the standard three axioms.
The sign of H remains open. This candidate and the direct cone
certificate use the same complete polynomial; neither retires the other.

Corpus search `/tmp/tt_c115_determinant_transport_search.json` and direct
inspection of `actualUpperDeterminant_normalized_tendsto` supplied the
existing terminal input. No global monotonicity producer was found.

## Log

- 2026-10-06 — All 45 tenth-jet production leaves and all 1459 public
  declaration axiom audits passed, standard three axioms only. C116 exact
  U^26 reduction also passed its full production audit. The reduced core
  transport sign remains open; C117's positive seam-limit audit is running.

- 2026-10-06 — C115: corpus deep search completed with partial results;
  actual weighted recurrence, source incidence and full cofactor definitions
  verified directly. Terminal specializations do not replace the general
  source model. Clean tenth-jet audit live; eleventh-jet transcription and
  exact recurrence proof generator prepared, not run. Final RH goal unchanged.
- 2026-10-06 — Clean tenth-jet chain completed in scratch and staged as
  45 production modules, 1459 declarations; direct production audits pending.
  Eleventh-jet recurrence blocks are being checked. The direct cone sign
  and terminal-propagation monotonicity remain unproved research targets.
- 2026-10-06 — All 28 eleventh-jet recurrence blocks and the complete
  `weightedJet11ExactPieces_eq` identity passed scratch Lean audits, using
  only propext, Classical.choice and Quot.sound. Clean tenth-jet partition
  re-audit passed. Control 5's complete derivative sign passed, bringing
  scratch controls to 15/19. Production tenth-jet audits are running serially;
  eleventh-jet column reconstruction follows. Compact determinant positivity
  remains open; none of these identities supplies its missing sign.

- 2026-10-06 — C117 complete in production: full complex incidence and
  exact reduced determinant identity, positive nonzero source seam limit,
  and near-seam determinant positivity. Four leaves / 25 public axiom
  audits passed, standard three axioms only. The source limit of N is
  lambda^2*delta/k(0)^34; its order relative to L/9^26 is still unproved.
  These two positive limits do not imply a sign across the compact region.
