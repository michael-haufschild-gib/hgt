# T2 natural Abel-wall square-energy no-go

- **ID:** T2-NAT-ABEL-L2-WALL
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md`, Route T2 literal natural Wold square-energy producer
- **Statement:** For every `t > 1/2`, the literal natural Wold square energy `WoldNatResidualSquareEnergy t` is false.

## Goal
Kill Route T2's entire cofinal square-energy producer.  Its RH gate asks for energy at every
`1/4 < t < 3/4`; nonexistence at any (indeed every) `t > 1/2` makes that premise inconsistent.
The intended proof uses an unconditional Hardy critical-line zeta zero, not RH or any zero-location
hypothesis.

## Gates
- [x] 0 → 1  in-progress: source-pure statement, exact proof chain, corpus/literature audit
- [ ] 1 → 2  fully-proven: complete natural-Abel continuation identity and pole contradiction
- [ ] 2 → 3  formalized: closed Lean theorem, targeted build, axioms and lint audits
- [ ] 3 → 4  publication-ready: standalone theorem, proof, novelty comparison, Lean certificate

## Corpus-derived proof chain
1. Put `R_N = xiHeatCassiniWoldNatResidualLogDiscrepancy N` and
   `F(s) = sum_{N>=1} R_N N^{-s}`.  The energy is exactly weighted `ell^2` membership of `R_N`.
2. If `E(t) < infinity`, `t > 1/2`, Cauchy--Schwarz gives absolute convergence and holomorphy of
   `F` on `Re(s) > 1-t`; in particular at every critical-line point `rho`.
3. Equivalently, the natural Abel current
   `A(s) = sum_{N>=1} R_N (N^{-s}-(N+1)^{-s})` is holomorphic on `Re(s) > -t` and is continuous at
   every translated critical point `s0 = rho-1`.  The sharp majorant on `Re(s)>=-1/2` is
   `C |R_N| N^{-1/2}`; Cauchy--Schwarz reduces it to `E(t)` and `sum N^{-2t}`.
4. Finite Abel summation on the natural cutoff gives, first for `Re(s)>0`,
   `A(s) = WoldCurrent(s) - IntegerLogMesh(s) + boundary`, because
   `R_N-R_{N-1} = WoldNatWeight(N) - (log N-log(N-1))`.
5. Continue the integer logarithmic mesh by subtracting its `1/N` principal term:
   `log(N/(N-1))-1/N = O(N^{-2})`.  Its remainder is holomorphic on `Re(s)>-1`, while the
   principal term is `zeta(s+1)` and is regular at every nonreal `s0=rho-1`.
6. The corpus theorem
   `xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue` gives residue `-m != 0` for the
   Wold current at every critical-line zero.  Analytic continuation of step 4 therefore forces the
   natural Abel current to have the same nonzero pole at `s0`.
7. Hardy's unconditional critical-zero theorem supplies such a nonreal `rho`.  Steps 3 and 6
   contradict.  Hence `not_woldNatResidualSquareEnergy_of_half_lt` and, immediately, failure of
   the complete cofinal T2 producer.

## Conjecturing loop
- **C1 (failed):** energy directly implies absolute critical prime-edge variation.  Cauchy duality
  exposes a weighted square prime-gap moment, so this reintroduces Route T's open mesh producer.
- **C2 (active):** use every natural cutoff and the natural Abel current.  Its dual is the ordinary
  convergent p-series `sum N^{-2t}`; no prime-gap estimate remains.
- **Positive survivor if endpoint fails:** the same argument is sharp for every `t>1/2`; it does
  not claim the endpoint `t=1/2`, where the dual series becomes harmonic.

## Novelty audit (through 2026-08-30)
- Corpus has the natural square-energy RH gate, the adaptive cubic obstruction only for `t>3/4`,
  the critical Wold pole carrier, and generic square-summable Dirichlet-series holomorphy.  It has
  no natural-cutoff Abel current, no weighted-energy-to-critical-wall theorem, and no `t>1/2`
  no-go.
- Zhao (2025) treats signed first means of the three classical Mertens errors; Bhattacharya,
  Martin, and Simpson (2025) treat correlations and sign distributions of weighted prime-counting
  errors; Brent, Platt, and Trudgian (2021) treat mean square of `psi(x)-x`.  None states the
  discrete Wold residual energy threshold or the natural-Abel pole mechanism above.

## Lean infrastructure required by the proof
- weighted square-energy → square-summable normalized residual coefficient;
- natural residual ordinary L-series holomorphy on `Re(s)>1-t`;
- natural Abel-current summability and critical-wall radial continuity for `t>1/2`;
- integer logarithmic-mesh continuation on `Re(s)>-1` and exact Abel identity with the corpus Wold
  continuation;
- residue contradiction using an unconditional critical-line zeta zero.

## Log
- 2026-08-30 — Stage 1 frozen after corpus research and current-literature audit.  C1 rejected;
  C2 selected because it removes the prime-gap-energy circularity.

## Formal progress — 2026-08-30
The Hilbert-to-wall premise is now closed unconditionally in
`XiHeatCassiniWoldNaturalAbelCriticalWall.lean`:

- `summable_abs_woldNatResidual_mul_succ_rpow_neg_half_of_squareEnergy`: for every `t > 1/2`,
  square energy implies `Summable (|R_(N+1)| (N+1)^(-1/2))` by exact Cauchy--Schwarz against
  `sum (N+1)^(-2t)`.
- `summable_woldNatResidualAbelAtom_of_squareEnergy`: the natural Abel current converges absolutely
  at every nonzero `s` with `Re(s) >= -1/2`.
- `tendsto_woldNatResidualAbelCurrent_critical_radial_of_squareEnergy`: at every nonreal point
  `s0` on `Re(s0) = -1/2`, the current tends radially to its finite wall value.

This is the significant analytic premise needed for the contradiction with the corpus's nonzero
Wold residue.  It strictly improves the prior adaptive cubic obstruction from `t > 3/4` to critical
wall control for every `t > 1/2`, with no prime-gap hypothesis.  Remaining full route-kill burden is
now only the global continuation identity: continue the integer logarithmic mesh and identify the
natural Abel current with Wold continuation minus that regular mesh on the connected upper
half-strip.  The frontier map was not edited.

Verification: direct `lake env lean` passed; targeted module build passed; `#print axioms` reports
only `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide formal lint reaches this
module but currently fails on unrelated concurrently present modules not wired into their umbrellas;
it reports no forbidden declaration in this module.

## [PAPER-PROVED] Full no-go proof — 2026-08-30
This section supersedes the earlier Stage-1 status.  The exact claim is now dependency-closed on
paper and moves to Stage 2.

Fix `t > 1/2` and suppose `WoldNatResidualSquareEnergy t`.  Write `R_N` for the centered natural
Wold discrepancy and `q_N(s)=N^{-s}`.

1. The formalized Cauchy--Schwarz theorem gives
   `sum_{N>=1} |R_N| N^{-1/2} < infinity`.  Consequently
   `A(s)=sum_{N>=1} R_N(q_N(s)-q_{N+1}(s))` is holomorphic on
   `U={s | Re(s)>-1/2 and Im(s)>0}` and has a finite radial limit at every nonreal point of the
   wall `Re(s)=-1/2`.  Local holomorphy follows from the unit-window derivative bound and a ball
   contained in `U`, uniformly dominated by the same summable wall sequence.
2. Put `ell_n=log n-log(n-1)` for `n>=2` and `d_n=ell_n-1/n`.  Log concavity gives
   `1/n <= ell_n <= 1/(n-1)`, hence `0 <= d_n <= 1/(n(n-1)) <= 2/n^2`.  Therefore
   `D(s)=sum_{n>=2} d_n n^{-s}` is holomorphic for `Re(s)>-1`, and
   `Lcont(s)=zeta(s+1)-1+D(s)` is holomorphic on `U`.  On `Re(s)>0`, absolute convergence gives
   `Lcont(s)=sum_{n>=2} ell_n n^{-s}`.
3. Since `R_N-R_{N-1}=w_N-ell_N` for `N>=2`, finite Abel summation gives
   `sum_{N=1}^M R_N(q_N-q_{N+1})
      = R_1 q_1 + sum_{N=2}^M (w_N-ell_N)q_N - R_M q_{M+1}`.
   Here `R_1=-C`, where `C` is the Wold holonomy constant.  The unconditional natural Wold
   holonomy theorem gives `R_M -> 0`; for `Re(s)>0` the terminal term vanishes.  Reindexing the
   prime-supported `w_N` series gives the corpus Wold current.  Thus
   `A(s)+C+Lcont(s)=WoldCurrent(s)` on `Re(s)>0`.
4. The Wold critical continuation has first term
   `-zeta'(s+1)/zeta(s+1)` minus the critical higher-valuation tail; later shifts are holomorphic
   on `U`.  Define its zeta-cleared realization `Wclear` by replacing the first quotient after
   multiplication by `zeta(s+1)` with `-zeta'(s+1)` and multiplying every remaining term by
   `zeta(s+1)`.  Since `2 Re(s+1)>1` on `U`, the critical higher-valuation term has no doubled-zeta
   pole there.  Hence `Wclear` is holomorphic throughout `U`.
5. On the nonempty open subset `V={s in U | Re(s)>0}`, Euler zero-freeness, step 3, and the corpus
   safe/critical Wold continuation laws give
   `zeta(s+1)(A(s)+C+Lcont(s))=Wclear(s)`.  The set `U` is convex, hence preconnected.  Analytic
   uniqueness extends this identity to every `s in U`.
6. Hardy's unconditional dyadic theorem supplies `rho=1/2+i tau` with `tau>0` and
   `zeta(rho)=0`.  Put `s0=rho-1`.  Zeta zeros are isolated, so on a punctured neighborhood of
   `s0`, `zeta(s+1) != 0`.  Cancelling the cleared identity there yields
   `A(s)+C+Lcont(s)=WoldCriticalContinuation(s)` for the positive radial approach to `s0`.
7. Multiplication by `s-s0` sends the left side radially to zero: `A` has the finite wall limit
   from step 1, while `Lcont` is holomorphic at the nonreal point `s0`.  The corpus theorem
   `xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue` sends the right side to `-m` for
   some integer `m>=1`.  Therefore `0=-m`, contradiction.

Thus `[PAPER-PROVED]`:
`forall t, 1/2 < t -> not (WoldNatResidualSquareEnergy t)`.
The T2 cofinal producer asks for energy at every `1/4<t<3/4`; choosing any `t` in `(1/2,3/4)`
contradicts this theorem, so the complete producer is a dead end once the exact paper proof is
formalized.

## [FORMALIZED — ROUTE KILLED] Lean certificate — 2026-08-30

This section supersedes all earlier stage/type fields. Stage 3 is complete.

Closed theorems:

- `not_woldNatResidualSquareEnergy_of_half_lt`: for every real `t > 1/2`,
  `¬ WoldNatResidualSquareEnergy t`.
- `not_woldNatResidualSquareEnergy_cofinal_threeQuarter`: negation of the exact T2 producer
  `∀ t, 1/4 < t → t < 3/4 → WoldNatResidualSquareEnergy t`.

Formal dependency chain:

- `XiHeatCassiniWoldNaturalLogMeshContinuation.lean`: exact logarithmic-mesh decomposition and
  holomorphic continuation to `Re(s) > -1` away from `s=0`.
- `XiHeatCassiniWoldNaturalAbelContinuationIdentity.lean`: natural Abel holomorphy and exact safe
  identity with the Wold current.
- `XiHeatCassiniWoldNaturalSquareEnergyHalfNoGo.lean`: zeta-cleared analytic continuation,
  unconditional Hardy-zero residue contradiction, and exact producer negation.

Audits: each new module passed direct `lake env lean`; targeted builds passed, including final
`lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyHalfNoGo`; `#print
axioms` for both terminal theorems reports only `propext`, `Classical.choice`, and `Quot.sound`;
all three modules contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`. They are wired into
`GaloisForLFunctions.RHTower`. Repository-wide lint still reports unrelated pre-existing/uncommitted
owned modules missing from umbrellas; it does not report these three modules as unreachable.

**Consequence:** T2's cofinal natural square-energy branch is formally retired. Any replacement T2
route must abandon that producer rather than strengthen its estimates.
