# PW-B actual Gamma global absolute admission

- **ID:** PW-B-GAMMA-GLOBAL-ABSOLUTE-ADMISSION-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** For the actual Gamma/Möbius coefficient family, the sum of individual atom `L¹(dx)` norms on the positive ray converges exactly when the coefficient parameter has positive real part. The full logarithmic derivative has the same exact boundary. Both complete sources are integrable in that open region, with justified series/integral interchange.

## Exact source and measure

Use the actual ray source `Q(x)=sqrt(x)*exp(-x)` for `x>0`, and retain
all coefficients in

`A_(b,n)(x)=mu(n)*exp(-b*log(n))*Q(n*x)`.

The source is `M_b(x)=sum_n A_(b,n)(x)` and its actual coefficient derivative
is `E_b(x)=sum_n -log(n)*A_(b,n)(x)`, as proved in the
[parameter-generator leaf](pw-b-gamma-parameter-generator.md).
The zero index vanishes. The measure here is explicitly Lebesgue `dx`
on `x>0`, not logarithmic measure or a singular weighted energy.

## Proof and sharp positive survivor

The Gamma integral gives

`C=integral_(x>0) |Q(x)| dx=Gamma(3/2)>0`.

Each individual atom is integrable at every complex `b`. Positive dilation
contributes the Jacobian `1/n`; the coefficient norm contributes
`|mu(n)|*n^(-Re(b))`. Thus, for every natural index, including the zero
coefficient handled separately,

`integral |A_(b,n)| dx = C*|mu(n)|*n^(-Re(b)-1)`.

The derivative-atom norm integral is exactly

`C*log(n)*|mu(n)|*n^(-Re(b)-1)`.

If `Re(b)>0`, the bound `|mu(n)|<=1` and the p-series criterion give
summability of the first mass series. The existing logarithmic p-series
estimate gives summability of the derivative mass series.

Conversely, restrict either summable series to primes. There `|mu(p)|=1`.
For the source, the exact prime criterion
`sum_p p^r converges iff r<-1` forces `Re(b)>0`.
For the derivative, `log(p)>=log(2)>0` first controls the same prime
series and gives the identical restriction. The positive Gamma factor
can be removed without changing summability.

Therefore **both absolute admission classes are exactly `Re(b)>0`**.
In particular both original mass series fail at `b=0`. This is not merely
a failed sufficient estimate: prime restriction proves necessity for
these particular mass series.

The positive survivor is proved too. The Tonelli/Bochner domination
lemma applies to the actual atoms throughout the open region, proving
`M_b` and `E_b` integrable there. Both complete series pass through the
ray integral with all coefficients retained. No interchange of a parameter
derivative and the global integral at zero is asserted.

## What this does and does not settle

Literal PW response -> FE partner imbalance -> positive Deninger Ward
transmutation -> independently source-forced fixed-grade balance -> RH
remains the chain. This leaf locates the exact endpoint of the direct
absolute atom argument for the actual source. It does not identify the
coefficient parameter with the spectral Ward parameter, establish critical
finite energy, or produce vanishing balance. RH remains unproved; PW-B
remains active.

Divergence of the sum of atom norms does **not** imply nonintegrability of
the signed summed source. The [signed endpoint successor](pw-b-gamma-signed-endpoint.md)
now proves this distinction for the actual source. A direct Gamma difference
estimate has integrated cost `(Gamma(3/2)+Gamma(5/2))/n^2`; unconditional
inverse-square Mertens summability admits the complete Abel assembly, with
the finite identity and terminal term checked. Thus `M_0` is integrable,
has zero mass and has strictly positive finite `L¹` norm. Its arithmetic
reconstruction has exact nonzero series/integral defect `Gamma(3/2)`.
The global logarithmic-current and spectral Ward identifications remain
separate obligations.

## Search and novelty audit

Four partial-coverage deep searches, one lexical search and the audited
methods are saved in
[search artifact](../1-in-progress/pw-b-gamma-global-admission-searches.json).
The decisive methods are the current Gamma integral and positive dilation
APIs, `Nat.Primes.summable_rpow`, `Mertens.summable_log_div_rpow`, and the
corpus's generic Bochner-series integrability lemma. Broad deep retrieval
also returned unrelated or hypothesis-bearing candidates; none is a premise.
The result is an exact admission audit for this literal source, not a new
general p-series or Gamma-integral theorem.

Broad recent searches inspected [cascade intermittency](https://arxiv.org/abs/2606.18995)
(June 17), [pipe dream rectification](https://arxiv.org/abs/2608.23530)
(August 24), and [acoustic disguising](https://arxiv.org/abs/2606.08524)
(June 7). Their respective cascade laws, restricted combinatorial symmetry,
and closed-surface Green-function driving do not supply an arithmetic
endpoint cancellation theorem under the hypotheses currently proved here.
No external theorem is inserted as an axiom.

## Formal surface and validation

Leaf: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaMobiusGlobalAdmission.lean`.
Fifteen public theorems and two definitions. The premise-free
`pwGammaMobiusGlobalAdmission_closed` packages both exact admission classes,
the positive integrability survivor, and the two zero-parameter failures.
The two integral-interchange theorems are also proved separately.

Validation completed:

- Scratch and direct file checks passed with `lake env lean <file>`.
- Final audit used only `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusGlobalAdmission`; target compiled in 67 seconds. Dependency jobs replayed cached results.
- All 15 public theorem axiom audits passed in `/tmp/pwb-gamma-global-axioms.lean`; no axioms beyond `propext`, `Classical.choice`, `Quot.sound` occur.
- `scripts/formal_tools.py lint` passed. Index regenerated all three formal ledgers and records the 15 theorems and two definitions.
- All 17 public names have one declaration in the corpus. Task-scoped diff and new-file whitespace checks passed.
- Umbrella import wired. No umbrella/full build or numerical experiment ran. All owned Lean and research processes finished.

Audit logs: `/tmp/pwb-gamma-global-{scratch,direct,build,axioms,lint,index}.txt`.
