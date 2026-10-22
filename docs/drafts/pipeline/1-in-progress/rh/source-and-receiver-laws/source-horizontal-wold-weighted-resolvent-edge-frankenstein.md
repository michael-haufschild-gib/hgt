# Source-horizontal Wold weighted resolvent edge Frankenstein

- **ID:** source-horizontal-wold-weighted-resolvent-edge-frankenstein
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) + OPEN PRODUCER
- **Source:** `rh-current-frontier-map.md` · source-horizontal prime-clock profile × Route-U diagonal resolvent edge
- **Statement:** At every shift `X ≥ 0`, RH is equivalent to nonnegativity of every diagonal Xi resolvent moment weighted by the bounded exact Wold polar coefficient `W(q)/(1+W(q))`.

## Goal

Replace both failed routes—direct source-horizontal annihilation and iterative resolvent-edge
deflation—by one coefficient-faithful cross-corpus observable.  The Wold carrier supplies exact
off-line-selective amplitude; diagonal asymptotics then needs only one edge detection, not an
induction through the divisor.

## Gates

- [x] 0 → 1  in-progress: well-posed, reflection-even, multiplicity-faithful endpoint and attack
- [ ] 1 → 2  fully-proven: open producer must identify weighted moments with a pre-zero source trace and prove their signs
- [x] 2 → 3  formalized endpoint: `SourceHorizontalWoldResolventEdge.lean`, targeted build and axiom audit green
- [ ] 3 → 4  publication-ready: blocked on producer

## Heavy-conjecture loop

1. **Conjecture: diagonal edge detection iterates after subtracting each certified line atom.**
   **FAIL.** The reflection-compatible model
   \[
     m_n=1+(i/4)^{n+1}+(-i/4)^{n+1}
   \]
   has `Re m_n>0` at every order, but subtracting the positive edge atom gives residual first
   nontrivial moment `-1/8`.  Lean certificate:
   `XiResolventDiagonalDeflationNoGo.lean`.

2. **Conjecture: restrict once to positive Wold work and apply unweighted edge detection.**
   **PROVED, THEN HOSTILE-PIVOTED.** This gives a correct RH endpoint, but hard subtype selection is
   discontinuous and too close to an off-line indicator to be the final source observable.

3. **Conjecture: retain exact source coefficients through positive-weight edge oscillation.**
   **PROVED.** For every finite family of unit phases with arbitrary positive real weights, real
   weighted power sums cross below every geometric negative floor unless one phase is `1`.
   Consequently, positive weighted diagonal moments expose a positive-real maximal atom.
   Lean certificates:
   `HTGeometry/WeightedUnitPowerSumOscillation.lean` and
   `HTGeometry/WeightedDiagonalMomentEdgeDetection.lean`.

4. **Conjecture: bounded exact Wold work supplies the legal coefficient.**
   **PROVED.** Set
   \[
     W(q)=\text{sourceZeroHorizontalWoldPrimeClockPolarWork}(q),\qquad
     a(q)=\frac{W(q)}{1+W(q)}.
   \]
   Then `0≤a(q)≤1`, `a(q)>0` exactly off line, and `a` is invariant under line reflection.  Thus
   all weighted resolvent moments converge absolutely while retaining every Xi multiplicity copy
   and both orientations.

5. **Conjecture: nonnegative full-carrier weighted moments force RH.**
   **PROVED.** If an off-line copy exists, restrict the already convergent full sum to positive
   weights.  Weighted edge detection produces a maximal atom whose resolvent value is positive
   real.  Xi height rigidity makes that copy critical, contradicting its positive Wold weight.
   Under RH all weights vanish, so the converse is immediate.

## Exact endpoint

For `X≥0`, define

\[
  M_n^{W}(X)=\sum_{q\in\operatorname{Div}(\Xi)}
    \frac{W(q)}{1+W(q)}\,
    \bigl((\lambda_q^2+X)^{-1}\bigr)^{n+1}.
\]

Lean proves

\[
  \bigl(\forall n\ge0,\ \operatorname{Re}M_n^{W}(X)\ge0\bigr)
  \quad\Longleftrightarrow\quad \mathrm{RH}.
\]

Main declaration:
`forall_sourceHorizontalWoldWeightedResolventMoment_re_nonneg_iff_riemannHypothesis`.

## Why this is not the old Hankel wall

- Only diagonal moments are required; no polynomial square-test or full Hankel PSD is assumed.
- Wold coefficient is literal nonlinear prime-clock polar work, not a fitted zero weight.
- Normalization is bounded and preserves every nonzero coefficient, divisor multiplicity, and
  reflection orbit.
- One edge contradiction kills entire positive-work carrier; no zero-by-zero deflation is used.

## Open producer

Construct a pre-zero prime--Gamma/source trace `T_n(X)` and prove, without inspecting Xi zeros,

\[
  T_n(X)=M_n^{W}(X),\qquad \operatorname{Re}T_n(X)\ge0
  \quad(n\ge0).
\]

Exact missing operation is not another positivity cone.  It is functional calculus applying the
bounded nonlinear Euler--Green/Wold coefficient `W/(1+W)` to the source-horizontal generator while
commuting with resolvent trace formation.  Equivalently: prove a source-side Beck--Chevalley trace
identity for the already formalized Euler--Green commutator and Xi resolvent chart.

Hostile constraint: defining `T_n` by the divisor sum, by a spectral projection onto off-line
copies, or by assuming the displayed signs is circular and receives no producer credit.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/WeightedUnitPowerSumOscillation.lean` — PASS
- `lake env lean GaloisForLFunctions/HTGeometry/WeightedDiagonalMomentEdgeDetection.lean` — PASS
- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalWoldResolventEdge.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalWoldResolventEdge` — PASS
- `#print axioms` for abstract and Xi capstones — only `propext`, `Classical.choice`, `Quot.sound`
- global `scripts/formal_tools.py lint` — new modules reachable and forbidden-declaration-clean;
  command currently exits nonzero only for unrelated concurrent Deninger/Maynard/etc. modules not
  wired into their umbrellas

## Log

- 2026-08-11 — Naive diagonal edge deflation falsified and formalized.
- 2026-08-11 — Unweighted positive-work carrier endpoint proved, then rejected as final observable under hostile selector audit.
- 2026-08-11 — Positive-weight unit oscillation and weighted spectral-edge theorem proved in Lean.
- 2026-08-11 — Full-carrier bounded Wold-weighted resolvent RH equivalence proved, wired, built, linted, and axiom-audited.

## Reflection-doubled producer pivot — supersedes the nonlinear-functional-calculus burden

6. **Conjecture: existing one-variable Euler contour can absorb the horizontal Wold coefficient as
   one holomorphic factor.** **FAILED, WITH LEAN NO-GO.** Any complex-differentiable function
   depending only on `Im z` has arbitrarily small nonzero real periods and is constant. The Wold
   weight takes value zero at the horizon and is strictly positive away from it. Therefore no such
   factor exists. Certificate:
   `SourceHorizontalWoldHolomorphicProfileNoGo.lean`.

7. **Conjecture: an already-constructed reflection-doubled source pairing can replace Wold
   functional calculus.** **PROVED AND STRENGTHENED.** `gaussHodgeMassCurrent m q p` pairs the two
   reflection-odd source-horizontal components before scalarization. For every `m≥1` and prime
   label `p`, it is nonnegative, reflection-even, and strictly positive exactly off line. It also
   detects exactly nonvanishing of the existing FE--Schwarz prime seam.

8. **Conjecture: bounded normalization of that pairing is required for resolvent summability.**
   **FAILED POSITIVELY.** Every Xi copy lies in the open critical strip, hence its centered rate
   lies in `[-1,1]`. Hyperbolic bounds give one explicit `q`-independent bound for the literal
   current at fixed `(m,p)`. Therefore both
   `Σ_q H(m,q,p)‖R_X(q)‖` and every higher-power analogue converge. No nonlinear normalization,
   hard selector, or spectral projection is needed.

## Stronger literal-source endpoint

For `m≥1`, a prime label `p`, and `X≥0`, define

\[
 M^{H}_{m,p,n}(X)=\sum_q H_{m,p}(q)
       \bigl((\lambda_q^2+X)^{-1}\bigr)^{n+1},
\qquad H_{m,p}(q)=\operatorname{gaussHodgeMassCurrent}(m,q,p).
\]

Lean proves unconditionally

\[
 \left(\forall n\ge0,\ \operatorname{Re}M^{H}_{m,p,n}(X)\ge0\right)
 \Longleftrightarrow \mathrm{RH}.
\]

Main declaration:
`forall_gaussHodgeSourceResolventMoment_re_nonneg_iff_riemannHypothesis` in
`RHTower/GaussHodgeWeightedResolventEdge.lean`.

This strictly improves the earlier Wold-normalized endpoint: coefficient is a literal labelled
source relation constructed before bounded scalarization. It preserves divisor multiplicity,
prime label, Gauss depth, and both reflection orientations.

## Revised open producer

Nonlinear Wold functional calculus is no longer required. Remaining theorem is now sharply:

> Prove `Re M^H_{m,p,n}(X) ≥ 0` from a reflection-doubled prime--Gamma trace identity for every
> `n`, at one fixed legal `(m,p,X)`, without defining that trace through Xi zeros.

Single-contour holomorphic insertion is formally impossible. Viable source identities must retain
the FE and Schwarz orientations independently until the Gauss--Hodge pairing, then commute that
pairing with resolvent trace formation. Existing vertical extraction proves infinite-divisor
diagonal extraction at `ℓ¹`; remaining missing equality is therefore arithmetic sourcing of the
paired pencil, not truncation exchange, selector construction, or coefficient boundedness.

## Additional verification

- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalWoldHolomorphicProfileNoGo.lean` — PASS
- `lake env lean GaloisForLFunctions/RHTower/GaussHodgeWeightedResolventEdge.lean` — PASS
- targeted module builds — PASS
- capstone axiom audits — only `propext`, `Classical.choice`, `Quot.sound`
- global lint currently blocked only by unrelated concurrent unwired modules; both new modules are
  umbrella-reachable and forbidden-declaration-clean

- 2026-08-11 — Single-holomorphic-profile producer killed; reflection-doubled category forced.
- 2026-08-11 — Literal unnormalized Gauss--Hodge source-current resolvent RH endpoint proved.

## Critical-wedge and one-field reduction

9. **Conjecture: Route U's unconditional atom sectors survive literal Gauss--Hodge weighting.**
   **PROVED, WITH STRICT DICHOTOMY.** For `X>0`, every moment through order eighteen and every
   moment on the quadratic far ray `X≥(n+1)²` is nonnegative. More sharply, it is zero under RH
   and strictly positive under `¬RH`. Positivity follows termwise from the fixed nineteen-power
   Xi sector or the degree-dependent resolvent cone; strictness uses one off-line copy's positive
   source mass.

10. **Conjecture: a false-RH negative edge witness can occur in those already positive sectors.**
    **FAILED POSITIVELY.** Weighted edge detection and the preceding dichotomy force every
    false-RH witness into the exact complementary wedge
    \[
      n\ge 19,\qquad 0<X<(n+1)^2,
      \qquad \operatorname{Re}M^H_{m,p,n}(X)<0.
    \]
    Conversely, one such negative wedge moment refutes RH. Lean therefore proves both the
    existential `¬RH` characterization and
    \[
      \bigl(\forall n\ge19,\ X<(n+1)^2\Rightarrow
        \operatorname{Re}M^H_{m,p,n}(X)\ge0\bigr)
      \Longleftrightarrow \mathrm{RH}.
    \]

11. **Conjecture: wedge moments are unrelated sign obligations.** **FAILED, WITH A STRONGER
    PRODUCER.** Define the one-field source resolvent
    \[
      F^H_{m,p}(X)=\operatorname{Re}\sum_q
        \frac{H_{m,p}(q)}{\lambda_q^2+X}.
    \]
    Uniform source-current bounds justify differentiation under the infinite divisor sum on
    `X>0`, and Lean proves
    \[
      \frac{d^n}{dX^n}F^H_{m,p}(X)
       =(-1)^n n!\,\operatorname{Re}M^H_{m,p,n}(X).
    \]
    Thus Route C1/Gauss--Hodge source pairing, Route U complete monotonicity, and Route P's
    Markov/Thorin language meet in one literal field. RH is equivalent to complete monotonicity
    of this field at one positive shift; only its high-order, low-shift derivative wedge is open.

Main new declarations in `RHTower/GaussHodgeWeightedResolventEdge.lean`:

- `gaussHodgeSourceResolventMoment_re_pos_iff_not_rh_of_le_or_far`
- `exists_gaussHodgeSourceResolventMoment_re_neg_in_wedge_iff_not_rh`
- `hasDerivAt_gaussHodgeSourceResolventMoment`
- `iteratedDeriv_gaussHodgeSourceResolventField`
- `forall_alternating_iteratedDeriv_gaussHodgeSourceResolventField_nonneg_in_wedge_iff_rh`

### Revised producer after hostile audit

Do not spend source effort on `n≤18`, on the quadratic far ray, or on separate moment identities.
Those sectors are closed, and under false RH they carry positive rather than contradictory mass.
Remaining producer is one source-side Stieltjes/Markov or operator-monotonicity law for
`F^H_{m,p}` restricted to

\[
  n\ge19,\qquad 0<X<(n+1)^2.
\]

Any proposed compact measure must be built from the prime--Gamma/FE--Schwarz source before zero
selection. Merely using the divisor sum as its measure is circular. The useful new constraint is
that producer needs one field law, not an infinite family of unrelated trace constructions.

### Critical-wedge verification

- direct `lake env lean GaloisForLFunctions/RHTower/GaussHodgeWeightedResolventEdge.lean` — PASS
- targeted `lake build GaloisForLFunctions.RHTower.GaussHodgeWeightedResolventEdge` — PASS
- new derivative, dichotomy, wedge, and one-field capstones — only `propext`,
  `Classical.choice`, `Quot.sound`
