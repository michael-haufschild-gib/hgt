# Li even-cross completed-Abel sublinear-tail repair no-go

- **ID:** LI-CAB8
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `LiEvenCrossCompletedAbelFiniteCriticalPrefixOscillationNoGo.lean`; corpus searches for completed-Abel current, summable phase recurrence, and LI-CAB5
- **Statement:** No nonempty finite packet of genuine critical-line Xi copies can be made nonnegative in every Li mode by adding an `o(n)` real correction.

## Goal

Kill proof chain

`finite critical prefix + sublinear tail repair`
`=> LI-CAB5 completed-Abel current nonnegativity`
`=> LI-CAB3`
`=> RH`.

This is a producer no-go, not an RH negation: under RH, any actual infinite divisor tail must cancel every fixed critical prefix at linear scale along cofinal mode subsequences.

## Gates

- [x] 0 → 1 in-progress: corpus-derived statement, exact RH chain, proof strategy
- [x] 1 → 2 fully-proven: dependency-closed paper proof below
- [ ] 2 → 3 formalized: Lean module, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready

## Conjecture and hostile audit

For `0 < v ≤ 1/4`, a nonempty packet `q : Fin d → XiCriticalLineResolventCopy`, and its current `J(n)`, there is `c>0` such that above every threshold one finds both

`J(n) > c(n+1)` and `J(n) < -c(n+1)`.

Consequently, if `R(n)/(n+1) → 0`, neither `J+R ≥ 0` in every mode nor `J+R ≤ 0` in every mode is possible.

Repeated zeros and rational relations among phases are allowed. No zero ordinate, linear-independence hypothesis, RH assumption, or computation enters.

## Paper proof

Each critical atom has the exact corpus identity

`J_q(n) = (n+1) a_q(v) sin((n+1) ω_q(v))`,

with `a_q(v)>0` and `0<ω_q(v)<π`. For the finite packet set

`S(m)=Σ_i a_i sin(m ω_i)` and `δ=S(1)>0`.

Delayed simultaneous phase recurrence gives, above every threshold, an integer `k` for which all `kω_i` are close modulo `2π` to zero. Choose the common phase error so that its weighted Lipschitz loss is below `δ/2`. Then

`S(k+1)>δ/2` and `S(k-1)<-δ/2`.

Since `J(n)=(n+1)S(n+1)`, take `c=δ/2`. This proves cofinal positive and negative linear excursions.

Now let `R(n)/(n+1)→0`. Eventually `|R(n)/(n+1)|<c/2`. Choose a negative excursion after that threshold. Division by the positive factor `n+1` gives

`(J(n)+R(n))/(n+1)<-c+c/2<0`,

contradicting all-mode nonnegativity. Positive excursions give the sign-reversed result.

## No-go closure

- **Exact killing theorem/mechanism:** finite critical packets have cofinal linear excursions of both signs; an `o(n)` correction cannot repair either sign globally.
- **Strongest positive survivor:** every viable LI-CAB5 infinite tail must carry cofinal `Ω(n)` countercurrent against every fixed nonempty critical prefix. Infinite-tail cancellation is quantitatively essential, not merely nonuniform.
- **New insight:** finite-prefix convergence in any topology controlling `current/(n+1)` uniformly at infinity cannot prove LI-CAB5. A viable route needs a genuinely infinite cancellation law at leading linear scale.
- **Status:** paper proof dependency-closed; external search found classical Li criteria, finite Li tests, and Kronecker–Weyl/prime-race oscillation, but no completed-Abel adjacent-current or sublinear-repair theorem. Priority remains `[NOVELTY UNVERIFIED]` pending expert review.

## Log

- 2026-08-29 — corpus audit rejected duplicated continuous-descent and Haar-refinement conjectures; LI-CAB8 selected as first non-duplicated route-killing frontier.
