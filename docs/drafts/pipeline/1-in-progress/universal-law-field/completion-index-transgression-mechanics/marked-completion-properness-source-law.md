# Marked-completion properness source law

- **ID:** `ULF-MCPS-1`
- **Stage:** 1-in-progress
- **Type:** higher-mechanism conjecture
- **Status:** collapse/mark/joint-reconstruction laws Lean-certified; proposed source-budget closure
  retired after collision audit
- **RH claim:** conditional only on the explicit source law in Section 4

## 1. Big-picture interpretation

Corpus does not describe one geometric state with many scalar coordinates. It describes one
irreversible operation:

1. source formation carries oriented rapidity and positive work;
2. completion collapses every nonzero magnitude to one of two phase classes `+h,-h`;
3. reflection forgets orientation after external pairing, leaving one occupation quantum
   `h tensor h`;
4. signed index, determinant, and internal multiplication then cancel that quantum;
5. a proper source mark remains upstairs and measures how much history was required to produce the
   completed occupation.

Thus mixed Lorentzian inertia is not bad positivity to remove. It is the fixed two-channel carrier
of a reflected formation event. Krein negative squares and unsigned theta defects count effective
events; rapidity/Gamma curvature measures their formation cost; Roos completion records causal
orientation. These are three forced executions of one collapse--mark mechanism.

## 2. Corpus search before conjecture

Searches used `scripts/formal_tools.py research` for:

- external tensor curvature, harmonic quantization, and Big-Witt pair atoms;
- fixed mixed inertia, Krein--Langer negative squares, and balanced-index cancellation;
- source Gamma paired curvature and Lorentz rapidity;
- recurrent observer/open history and bounded formation work;
- source coproduct/diagonal laws and three-way completion exchange.

Relevant exact facts:

1. actual theta Green boundaries retain a cofinal `(1,1)` inertia block;
2. every off-line Krein pair contributes one negative square, with multiplicity-aware jet channels;
3. signed balanced index is always zero while unsigned defect energy is `2n`;
4. Route-R completion sends every `t>0` to `-h`, every `t<0` to `+h`, and zero to zero;
5. external curvature is the same `h tensor h` for every nonzero `t`, with exact Big-Witt kernel
   `1/(pq)`;
6. source Gamma paired cost is `E(t)=2(cosh(t)-1)` and cannot factor through external curvature;
7. `(oriented class,E(t))` jointly reconstructs `t`;
8. generic bounded-work/properness theorems force zero grade, but current Xi versions are receiver
   predicates;
9. information-neutral lifts preserve off-wall superselection; determinant and signed-index
   doubles cancel; arbitrary exactification can relocate the anomaly into a compensator.

No searched theorem constructs a divisor-independent source action whose boundedness at a closed Xi
observer is proved before horizontal-grade extraction.

## 3. Five laws

### Law A -- occupation collapse

Completion has three oriented values `{-h,0,+h}` and two even values `{0,h tensor h}`. It records
whether an event occurred and its orientation, not its rapidity magnitude.

### Law B -- non-descending mark

Formation cost is a mark on the pre-completion history. It is not a scalar observable of the
completed occupation. Equal nonzero completed curvature may have unequal cost.

### Law C -- joint reconstruction

Oriented occupation plus cost reconstructs rapidity exactly. The mark is therefore neither
auxiliary metadata nor a new detector fitted to Xi; it is precisely the information completion
provably erased.

### Law D -- effective reflection

Reflection reverses orientation but does not negate occupation or cost. Signed group completion
cancels the two legs; effective formation keeps both. Any admissible compensator must be paid in the
same positive mark before cancellation.

### Law E -- recurrent-lift properness

A completed observer may close while its lifted marked history remains open. If one literal source
conservation law gives a uniform action budget for every closed observer lift, and every nonzero
occupation adds a fixed positive action increment, recurrence forces zero occupation.

This is the only new conjectural law. Laws A--D are already exact theorems or consequences of the
fresh fusion theorem.

## 4. Exact source conjecture

Construct before divisor specialization a nonnegative literal prime--Gamma formation action

`A_N(s)`, `N in N`, `0 < Re(s) < 1`,

with no normalization depending on an Xi zero, satisfying:

1. **source definition:** `A_N` is built from the finite source formation/recovery packets and their
   actual cofinal comparison;
2. **increment identity:**
   `A_(N+1)(s)-A_N(s)=E(2 Re(s)-1)`
   or a coefficient-faithful positive multiple with the same exact radical;
3. **compensator accounting:** every exactification/counterchannel contributes nonnegative action
   to the same ledger, so action cannot be moved to an uncharged summand;
4. **closed-observer budget:** the source conservation identity proves
   `Xi(s)=0 -> exists B, forall N, A_N(s)<=B`;
5. **formation naturality:** functional-equation reflection and common recovery act before the
   budget is evaluated and preserve the action ledger.

Clause 4 must be derived from a source Green/Stokes/formation identity, not taken as a definition of
admissibility.

## 5. Exact RH closure

Let `rho` be any Xi support point and put `t=2 Re(rho)-1`. Clause 4 gives a uniform upper bound for
`A_N(rho)`. Telescoping clause 2 gives

`A_N(rho)=A_0(rho)+N E(t)`.

Nonnegativity and arbitrary `N` force `E(t)=0`. Existing Gamma-six rigidity gives `t=0`, hence
`Re(rho)=1/2`. Since `rho` was arbitrary, RH follows.

Equivalently, the effective completion occupation vanishes because `C(t)=0 iff t=0`.

## 6. Why this is not the old bounded-work receiver

Existing endpoints define work directly as `N` times an already extracted grade defect and then ask
for boundedness. That is an exact RH equivalence but not a producer.

MCPS-1 requires one independently defined source action first. Increment and boundedness must both
be theorems about that same action, and compensators must be charged by construction. Failure to
construct such an action kills the mechanism.

## 7. Hostile falsifiers

Retire MCPS-1 if any occurs:

1. `A_N` uses a selected zero, its horizontal grade, or its completion class in its definition;
2. budget is postulated as an admissibility condition rather than proved from literal source
   conservation;
3. an all-cross Big-Witt or stabilization compensator cancels the increment at zero action cost;
4. source action has an off-wall closed observer with uniformly bounded marked lift;
5. comparison sees only the completed occupation and therefore cannot distinguish rapidity cost;
6. the resulting source statement is algebraically equivalent to `E(t)=0` before the source
   identity is used.

## 8. Next attack

Search the actual finite prime--Gamma formation modules for a source action already defined before
Xi specialization. Test its adjacent-depth difference against Gamma-six paired curvature. If the
increment matches, audit every correction/counterchannel for nonnegative accounting. Only then
attempt the closed-observer budget. Do not invent another per-zero energy.

## 9. Collision audit and retirement

Fresh corpus search after writing Section 4 found that its closure architecture already exists:

- `SourceHorizontalWoldPrimeClockProfile` defines literal pre-divisor polar work, proves a quartic
  proper lower bound, and proves bounded scale-orbit work iff grade zero;
- `SuzukiObserverJetFormation` constructs a literal completed-source weighted action and proves its
  linear bound implies RH;
- `SuzukiObserverJetLinearActionClassification` proves that strongest global action bound is itself
  equivalent to RH;
- `CompletionKernelPairTransversalityLaw` already proves abstract non-descent, transverse repair,
  and dense-fibre reporter rigidity.

Therefore Section 4 does not supply the missing higher mechanism. It restates the known action
endpoint with a better explanation of why the mark is necessary. `ULF-MCPS-1` is retired as a
closure proposal.

Positive survivor: `ULF-CIT-12` is still new corpus information. It proves exactly which data
completion erases and why cost must remain on the pre-completion history. Any next mechanism must
*derive* source-history admissibility or finite action from a stronger formation law; assuming a
budget, descent, support saturation, or coefficient-faithful comparison repeats an existing
RH-equivalent gate.
