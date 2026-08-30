# T2 Prime-Clock Interior Abel Singularity No-Go

- **ID:** T2-PCIAS-NG
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `XiHeatCassiniWoldPositiveTenthAllSourceGraphNoGo.lean` and `XiHeatCassiniWoldNaturalAbelSingularDivisorTomography.lean`
- **Statement:** The literal-prime-clock witness `r_N = exp(-h_N/20)`, despite lying in every proved polynomial graph domain and satisfying the proved height-`1/10` Bohr law, has a Stieltjes--Abel germ with no continuous extension at the strict-interior abscissa `s=-1/20`.

## Goal

Kill the topology-only T2 producer class against the exact RH endpoint.  Tested chain:

`all proved harmonic/Fisher/essential-edge polynomial graph laws + positive-height Bohr law`

`⇒ strict-interior Abel regularity`

`⇒ regularity of woldNatSingularAbelContinuation on -1/2 < Re(s) < 0`

`⇔ RH` by `riemannHypothesis_iff_woldNatSingularAbelContinuation_strictRight_regular`.

The first implication is false already on the literal ordered-prime clock.  No zeta zero or RH statement enters the witness or its Abel current.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom and lint audit
- [ ] 3 → 4  publication-ready: standalone paper theorem + proof + Lean certificate

## Paper proof

**[PROVED HERE]** Let `h_N=log p_N`, `g_N=h_{N+1}-h_N`, and first take arbitrary `α>0`.  For `0<q<α`, the negative radial Stieltjes atom of `r_N=exp(-αh_N)` at `s=-α+q` is

`a_N(q)=exp(-q h_{N+1})(1-exp(-(α-q)g_N)) ≥ 0`.

Since `1-exp(-x)≤x`, monotonicity of `h_N`, and `q>0` give

`a_N(q) ≤ α g_N exp(-q h_N)`,

the corpus exponential log-cell telescope proves absolute summability for every `-α<s<0`.

Set `q_M=α/(2+αh_M)`.  If `N<M`, then `q_Mh_{N+1}<1` and `α-q_M≥α/2`.  Also `g_N≤1` by Bertrand.  From

`x exp(-x) ≤ 1-exp(-x)`

one gets

`a_N(q_M) ≥ (α/2) exp(-(1+α)) g_N`.

Therefore

`sum_N a_N(q_M) ≥ (α/2) exp(-(1+α)) sum_{N<M} g_N`

`= (α/2) exp(-(1+α))(h_M-h_0) → +∞`.

Meanwhile `q_M→0`.  Any continuous extension at `s=-α` would give a finite limit along this ray, contradiction.  Taking `α=1/20` identifies the witness exactly with `t2BohrTerminalCounterResidual`.  Existing Lean theorems provide its primitive vanishing, all three all-order polynomial graph laws, and height-`1/10` Bohr square summability.  Hence the stated T2 regularity principle is false.

## No-go closure

- **Exact killing theorem/mechanism:** `not_T2PrimeClockBohrAllSourceGraphInteriorAbelRegularityPrinciple`.  The proved source laws admit an honest open-strip Abel germ with a nonremovable strict-interior singularity.
- **Strongest positive survivor:** `summable_primeClockExpResidualStieltjesAtom` plus `not_exists_continuousAt_primeClockExpResidualStieltjesCurrent` give the exact generic abscissa law for every `α>0`.  Together with `tendsto_primeClockTerminal_of_exponentialGraphEnergy`, this isolates positive exponential source radius as sufficient terminal control; all finite polynomial graph domains are insufficient.
- **New insight:** viable T2 producer must carry positive exponential radius, source-marked noncompact boundary mass, or an arithmetic identity invisible to finite graph topology.  Smoothness to every polynomial generator order is not even enough to prevent a singularity strictly inside the RH-detecting sector.
- **Status:** formalized in `GaloisForLFunctions.RHTower.XiHeatCassiniWoldPrimeClockInteriorAbelSingularityNoGo`; targeted build passed.  Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.  Global lint reports only pre-existing unrelated unreachable modules; this module is wired into `GaloisForLFunctions.RHTower` and introduces no forbidden declaration.

## Novelty audit

- Internal corpus searches found terminal-divergence and all-source graph counterexamples, but no strict-interior Stieltjes singularity theorem or exact generic abscissa law for this literal prime clock.
- Current literature search found general Dirichlet/Beurling abscissa theory, but no theorem combining this ordered-prime witness, the three T2 graph structures, the Bohr law, and the RH-equivalent strict-interior tomography endpoint.  Status: `SEARCHED, NOT FOUND`; this is not a claim of exhaustive bibliographic nonexistence.

## Log

- 2026-08-30 — conjectured from corpus search after divisor tomography exposed strict-interior regularity as exact T2→RH premise.
- 2026-08-30 — paper proof closed and formalized; topology-only all-source graph/Bohr producer route retired.
