# CCM-FU: extensions selected from actual negative support

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], proposed source-specific step in complete reserve extension
- **Goal:** Uniform complete signed Abel bound and RH; both remain open.
- **Parent:** [reserve-extension induction](ccm-fu-reserve-extension-induction.md).

## Frozen question

The cutoff21 triangle theorem forces nonempty negative oriented coordinates
along every complete order. The mixed-transverse comparison pays their
creation only from a field with nonnegative nonempty coordinates. To continue
the induction, test whether existing defects themselves identify a next prime.

For the complete actual oriented field A_P, set

`N(P) = union {R : R nonempty and A_P(R)<0}`.

Every prime in N(P) is unprocessed. Selecting one moves a negative partner
into a positive contribution on a smaller label, although it may also create
other defects. Freeze this proposed arithmetic statement: every proper state
with `Phi(P)<=B=Q_empty` and nonempty N(P) has q in N(P) such that P+q is
terminal or `Phi(P+q)<=B`. The budget is unchanged; no homogeneous descent
or bound on defect count is assumed. This is a derived induction candidate,
not a replacement for the uniform source bound.

## Discriminating experiment

Process every one of the8860 saved subset states through cutoff32 in
`defect-reserve-reanalysis.json`, checking energies against `subset-states.csv`.
Recover the complete fields by the already established isolated late-prime
identity and subset inversion; do not regenerate the main source table.
Use the original tolerance `1e-12*max(1,B)` for both certificates and signs.

Test the frozen implication at every eligible state. Separately determine
whether a complete certified path exists under the rule that q must lie in
N(P) whenever N(P) is nonempty. When N(P) is empty, every unprocessed prime
remains eligible. This checks whether any local failure blocks the whole
policy. Save all failures, complete source fields, every outgoing successor,
and reachability in both the original and policy-restricted graphs.

Independently reconstruct all source fields at every failed cutoff at80
decimal digits and repeat both tests, using the same predicates and tolerance.
The prior head-supported-path results do not decide either question: they
forbid the defects which this policy uses. No larger range is scheduled.

Run only on the supplied RunPod endpoint, at most eight worker processes,
one thread per numerical library, a60-second foreground deadline. Download
script, output and hashes to the computations record and remove owned remote
files and workers. Numerical results supply no Lean premise. A failure
rejects this policy or its universal extension claim only, not PE4 or RH.

## Result and attempted proof

All3949 eligible states pass the frozen extension implication, and every
saved cutoff has a complete certified path obeying the support rule. The
full8860-state reconstruction agrees with all saved good energies, defect
energies and certificates at the original tolerance. No failure triggered
the independent80-digit audit. The [record](../2-fully-proven/computations/ccm-fu-defect-supported-extension-2026-09-07/README.md)
contains all paths and input/script/output hashes. This is numerical evidence
only; the extension implication remains unproved.

The exact transport gives a necessary directional fact at every cutoff,
without any sign assumption on the current field. If q is outside N(P),
every q-containing partner is nonnegative. For each q-free R,

`A_(P+q)(R)=A_P(R)-A_P(R+q)<=A_P(R)`.

Every old negative coordinate is q-free and its negative part can only
increase. Coordinates containing q disappear but were nonnegative. Hence
`D_(P+q)>=D_P` and `G_(P+q)<=G_P`. Conversely q lies in N(P) exactly when
some q-free coordinate strictly increases. Thus any strict total defect
decrease must select q in N(P). These exact facts apply to already mixed
fields and are [formalized independently](../3-formalized/ccm-fu-negative-support-transport.md)
of the numerical test.

This observation does **not** prove the proposed extension. A prime inside
N(P) can simultaneously absorb some negative partners and create new
negative differences elsewhere. A prime outside N(P) can still pay its
increased defect through a decrease in good energy. In particular restricting
the choices to N(P) cannot be justified by defect monotonicity alone.

The missing arithmetic comparison remains, for at least one q in N(P),

`sqrt(G_(P+q) D_(P+q)) <= (B-Q_P)/2 + sum_R A_P(R) A_P(R+q)`.

The sum retains every q-free label, including the head. The current
certificate bounds only the old geometric mean, and membership in N(P)
supplies only one negative partner, not this complete signed inequality.
No uniform source estimate, completed induction, or RH proof is obtained.
