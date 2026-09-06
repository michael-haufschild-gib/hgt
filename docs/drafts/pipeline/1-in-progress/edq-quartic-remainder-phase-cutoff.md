# EDQ quartic remainder and explicit phase cutoff

- **ID:** EDQ-QUARTIC-PHASE
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), Q1-Q4 closed; RH producer open
- **Goal:** unconditional formal proof or falsification of RH through EDQ. This card handles a quantitative source bridge, not the missing RH producer.

## Full proof chain and current cut

Literal Euler deletion and its ordinary-cutoff zero landing -> retained complex chronological remainder -> source-derived orientation including the exceptional finite head -> exclusion of every off-line zero -> closed Lean RH theorem. The corpus has the first two steps. Existing remainder phase is eventually negative for each fixed parameter; a quantitative joint cutoff and the exceptional-head orientation are distinct obligations.

## Frozen statements

Write `b(x)=(fract(x)^2-fract(x))/2`, `P(x)=integral_0^x (b(y)+1/12)dy`, and `H(x)=fract(x)^2*(1-fract(x))^2/24`.

**Q1 [BRIDGE]:** `P(x)=fract(x)^3/6-fract(x)^2/4+fract(x)/12`, `H'=P` everywhere, including integers, `H(n)=0`, and `0<=H<=1/384`.

**Q2 [BRIDGE]:** for `Re(s)>-1` and integer `N>=1`, the literal Bernoulli tail satisfies

`T_s(N)=-N^(-s-1)/(12*(s+1))+(s+2)*(s+3)*integral_N^infinity H(x)*x^(-s-4)dx`.

The last integral has norm at most `N^(-Re(s)-3)/(384*(Re(s)+3))`.

**Q3 [BRIDGE]:** let `g_s(n)=n^(-s)*conjugate(R_s(n))/(conjugate(s)*(conjugate(s)+1))`, where `R_s` is the actual ordinary remainder. For `0<Re(s)`, `0<Im(s)`, `n>=1`,

`| n^(2*Re(s)+1)*g_s(n) + 1/(12*(conjugate(s)+1)) |`

`<= |s+2|*|s+3|/(384*(Re(s)+3)*n^2)`.

Consequently its imaginary part is negative whenever

`|s+2|*|s+3|*|s+1|^2 < 32*(Re(s)+3)*Im(s)*n^2`.

**Q4 [BRIDGE]:** for every `0<Re(s)<=1`, `Im(s)>=1`, and positive integer `n` with `Im(s)^3<=n^2`, `Im(g_s(n))<0`.

## Paper proof

The centered quadratic integrates to the displayed cubic on one unit cell. Its mean is zero and its endpoint values agree, so the primitive is periodic. The quartic differentiates to that cubic; both one-sided derivatives at every integer are zero. Its bound follows from `0<=r(1-r)<=1/4` for `0<=r<=1`.

Integrate `P(x)*x^(-s-3)` by parts using `H'=P`. The lower boundary is zero at integer N. The upper boundary tends to zero because H is bounded and `Re(s)>-1`. Absolute integrability justifies the half-line operation. This gives `(s+3)*integral H(x)*x^(-s-4)dx`. Substitute into the corpus's exact `bernoulliTail_eq_mean_add_primitive` to prove Q2.

Apply Q2 to `conjugate(s)`. The original power-sum remainder is exactly `s(s+1)T_s`, so normalization and positive-real-base power multiplication yield Q3. The leading imaginary part is `-Im(s)/(12*|s+1|^2)`; the displayed strict comparison makes the absolute error smaller than its magnitude.

For Q4 put `sigma=Re(s)` and `t=Im(s)`. The strip and `t>=1` give `|s+1|^2<=5t^2`, `|s+2|^2<=10t^2`, and `|s+3|^2<=17t^2`. The arithmetic-geometric inequality gives `|s+2|*|s+3|<=27t^2/2`. Their product with `|s+1|^2` is at most `135t^4/2`, strictly smaller than `96t^4`. Since `sigma+3>3` and `n^2>=t^3`, the Q3 sign criterion holds.

## Scope and adversarial audit

- No zero equation, unproved sign input, numerical certificate, or RH-equivalent premise enters Q1-Q4.
- Q4 is a superlinear cutoff, weaker than frozen conjecture R's proposed `t<2*pi*n`. It neither proves nor modifies R, B2, or C.
- A high zero's unit term remains in the exceptional head. Tail negativity cannot determine that term's sign; RH remains open.
- Integer derivative joins, the boundary at infinity, conjugation, scaling, and strict margin all require Lean verification. A norm bound alone is not a phase proof.
- These are consequences of exact Euler-Maclaurin primitives, not a claimed novel RH architecture or literature novelty.

## Corpus and source provenance

Whole-corpus index searches used Bernoulli/Fourier, primitive, sine/monotone, nonstationary phase, logarithmic prefix, remainder phase, complex trapezoid sign, expanding clock, and uniform phase threshold terms. Source inspection: `EulerDeletionRemainderFirstCoefficient`, `EulerDeletionPowerSumRemainder`, `ArithmeticPrimeSievePhase`, `ArithmeticClockFirstVariation`, `ArithmeticLinearPhasePrefix`, `DQPTEulerMaclaurin`, and `HTGeometry.EulerMaclaurinSecondOrder`. Search ranking is not an exhaustive novelty audit.

Current external checks: [DLMF Bernoulli Fourier expansions](https://dlmf.nist.gov/24.8), [DLMF Hurwitz-zeta identities](https://dlmf.nist.gov/25.11). The proof starts from the local corpus and does not import a literature theorem as an axiom.

## Work plan

- [x] Inspect EDQ ledger, route-independent constraints, memories, and current corpus.
- [x] Freeze Q1-Q4 and audit the paper argument.
- [x] Formalize the exact quartic source identity and bound.
- [x] Formalize the quantitative phase criterion and strip cutoff.
- [x] Scratch-check, audit axioms, build only final leaves, wire umbrellas, run lint (two unrelated wiring failures recorded).
- [x] Update current frontier and route-independent knowledge with only verified conclusions.
- [ ] Continue the missing exceptional-head/joint-signature source orientation toward RH.

## Verification state

Q1-Q4 pass a combined scratch Lean check and separate source checks without warnings. Both final targeted leaf builds pass, rebuilding only the requested leaves. All modules are wired into `RHTower.lean`; the corpus index is refreshed and retrieves the capstone. The all-declaration axiom audit passes for all sixteen public declarations: only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms or computational certificates. All owned Lean processes completed. Global `lint --check-generated` fails on two unrelated missing umbrella imports: `RHTower.ThetaCuspModularCompactTube` and `HTGeometry.PolynomialODEJetRankThreeCompactExpansion`; output is `/tmp/edq_quartic_lint.log`. No unconditional RH theorem or falsification has been constructed. See [the formal certificate](../3-formalized/edq-quartic-remainder-phase-cutoff.md).
