# Sharp primitive-energy frontier at prescribed successor covariance

- **ID:** bvi-discrete-green-energy-jordan-spectrum
- **Stage:** 3-formalized
- **Type:** THEOREM; COUNTED009
- **Source:** The field's exact successor gradient; existing centered sawtooth,
  complete-period fractional-atom averaging, and continuous Franel/Jordan forms.
- **Statement:** Determine the least internal-period primitive energy at every
  admissible variance and successor covariance, classify all extremizers, and
  classify every universal linear inequality in these three observables.

## Significance and current evidence

The full discrete covariance already exists in
`RHTower/EulerDeletionMobiusPeriodCovariance.lean` (all420 lines inspected).
Its `sum_residueCombination_centered_sq` supplies the energy bridge. Neither
that covariance nor the continuous Franel/Jordan diagonal is new. The missing
arithmetic result is the joint sharp boundary for variance, successor covariance,
and primitive energy, with equality and realization classifications.

The package is one connected contribution. A generic diagonal inequality,
coordinate inverse, or Franel identity alone does not qualify. Verified as contribution009; total9 / 250.

## Candidate to audit symbolically

Write `P=N!`, `Y_q=Σ[1,N;q|d]c(d)/d`, `H=Y_1`, and
`U_c(k)=-Σ[1,N]c(d)*centeredDiscreteSawtooth(d,k)`.
The known successor law is `U_c(k+1)-U_c(k)=S_c(k+1)-H`.

Write `V=Σ[2,N]φ(q)Y_q²`, `C=Σ[2,N]μ(q)Y_q²`, and
`E=average(U_c²)`. The known inverse realizes every finite coordinate profile.

Dependency-closed paper proof, for all natural `N` and arbitrary real data:

1. Reuse exact discrete covariance and zero mean to obtain `average(U_c)=0` and
   `12*average(U_c^2)=Q_Franel(c)-H^2=Σ[2,N]J₂(q)Y_q^2`.
   The known gradient and telescoping show every additive primitive equals
   `U_c` plus a constant; zero period mean uniquely fixes that constant.
2. `J₂(n)≥nφ(n)`: reuse the multiplicative `gcdPowKernel 2` and identify it
   with `jordanTotient2`. At a prime power put `A=p^k`, `B=p^(k-1)`;
   `J₂=A²-B²`, `φ=A-B`, and `J₂-Aφ=B(A-B)≥0`. Coprime induction multiplies
   nonnegative inequalities. Cases0 and1 are exact.
3. For `q≥2`, the three inequalities and complete equality sets are
   `J₂≥5φ+2μ` ({2,3}), `J₂≥6φ+4μ` ({3,4}),
   `J₂≥6φ+12μ` ({4,6}). For `q≥10`, totient≤2 classification and totient
   evenness give `φ≥4`; the previous lower bound and `μ≤1` make all gaps
   strictly positive. All cases2 through9 follow symbolically from prime-power
   and coprime formulas. The triples `(J₂,φ,μ)` are
   `(3,1,-1),(8,2,-1),(12,2,0),(24,4,-1),(24,2,1),(48,6,-1),
   `(48,4,0),(72,6,0)` respectively.
4. Summation gives `12E≥5V+2C`, `12E≥6V+4C`, `12E≥6V+12C`.
   Nonnegative summands give exact equality iff every coordinate outside the
   corresponding two labels vanishes.
5. At every level `N=n+6`, every admissible `(H,V,C)` has minimum
   `12E=max(5V+2C,6V+4C,6V+12C)`. Admissibility is precisely
   `V≥0`, `-V≤C`, `2C≤V`, independently of `H`.
   Realize coordinates `Y1=H,Y2=a,Y3=b,Y4=c,Y6=d` with others zero:
   `V=a²+2b²+2c²+2d²`, `C=-a²-b²+d²`,
   `12E=3a²+8b²+12c²+24d²`.
   In the three intervals separated by `C=-V/2` and `C=0`, choose squares
   `(a²,b²,c²,d²)=(-V-2C,V+C,0,0)`,
   `(0,-C,(V+2C)/2,0)`, or `(0,0,(V-2C)/2,C)`.
   Admissibility proves nonnegativity, so real square roots give witnesses.
6. Pure prime modes have `H=0,V=p-1,C=-1,E=(p²-1)/12`.
   Unbounded primes therefore give, for every real `K`, a witness `V≥1` and
   `E>K*V`. This obstruction is accompanied by the sharp positive frontier.
7. Complete universal inequality classification:
   `∀N c,0≤αV+βC+γE` iff `γ≥0` and
   `4α-4β+γ≥0`, `6α-3β+2γ≥0`, `2α+γ≥0`, `2α+β+2γ≥0`.
   Necessity: pure modes2,3,4,6 give the four facets; prime escape forces
   `γ≥0` (choose `K=(|α|+|β|+1)/(-γ)` if `γ<0`).
   Sufficiency: treat q2 directly. For q≥3 and μ≤0 decompose
   `(φ,μ)=(-μ)(2,-1)+((φ+2μ)/2)(2,0)` and use the second Jordan facet.
   For μ≥0 use `(φ,μ)=((φ-2μ)/2)(2,0)+μ(2,1)` and the third facet.
   Existing half-decorrelation bounds make both coefficients nonnegative.
   Multiply by `Y_q²` and sum. No assertion of arbitrary energies above the
   frontier: covariance endpoints have additional rigidity.

Do not use experiments. Do not substitute a continuous Franel identity for the
discrete integer-cycle statement. No external-family averaging or asymptotic
cancellation claim.

## Corpus audit and durable plan

- Objective and complete field README read; truncation in one tool response was
  recovered by targeted ranges. Root/formal instructions and formal guides read.
  Architecture/testing docs absent. Starting ledger: **8 / 250** verified.
- Dilation/commutator deep search: all20 candidates,20 source arguments, one
  ingredient set inspected. Generation1450384, semantic coverage unavailable,
  no request errors. Proposed valuation/class-field ingredient set is inapplicable.
- Cubic correlation deep search: all20 candidates,20 source arguments, one
  ingredient set inspected. Generation1450384, older snapshot and unavailable
  semantic coverage. No errors. Proposed prime-log ingredient set is irrelevant.
  Existing `CubicSievePhaseRecovery` declaration inventory already covers signed
  odd-mode recovery/parity obstruction; no duplicate contribution pursued.
- `sawtooth covariance gcd` lexical query had no hits. Broadened to
  `centeredDiscreteSawtooth`: all19 hits inspected. Existing zero mean and scalar
  square sum are relevant building blocks. Existing mean-centered Ramanujan Gram
  uses reciprocal pronic weights, not uniform integer-cycle averages.
- Deep `Ramanujan prefix variance Jordan totient`: all20 candidates,20 source
  arguments and one ingredient set inspected.
  Generation1450405, older snapshot, semantic coverage unavailable, no errors.
  The proposed inverse/dual-energy set alone does not prove the candidate.
- Franel/Jordan source section read; `jordanTotient2` lexical search had five
  hits, all inspected. `GcdPowerDiagonalization.lean` fully read (161 lines).
- Deep discrete covariance search: all20 candidates,20 source arguments, one
  ingredient set inspected; generation1450428, semantic coverage unavailable,
  no errors. It exposed the existing complete discrete Gram, reused above.
- Deep Jordan/totient/Möbius search: all20 candidates,20 source arguments and
  one ingredient set inspected; generation1450464, semantic coverage unavailable,
  no errors. Generic Möbius inversion does not provide the three sharp facets.
- Deep primitive-energy/successor-region search: all20 candidates,20 source
  arguments and one ingredient set inspected; generation1450464, partial=true,
  semantic retrieval timed out, semantic coverage unavailable. Returned hits
  and proposed ingredient set are unrelated to this joint finite moment problem.
  This is a local inspected-corpus novelty claim, not exhaustive global novelty.

1. [x] Finish source audit and search equivalent discrete-period energy statements.
2. [x] Close dependency-closed paper proof and novelty/significance audit.
3. [x] Probe installed APIs, formalize the exact unconditional package.
4. [x] Original-source check, all public axiom audits, wiring, exhaustive index,
   lint, artifact checks, ledger/memories, cleanup; only then consider count009.

`update_plan` unavailable; this card is the durable plan. Temporary prefix:
`/tmp/bvi9-*`. All search jobs are terminal.
Both original-source checks passed without diagnostics; all22 public axiom
closures contain exactly `propext`, `Classical.choice`, `Quot.sound`.
All34 named declarations matched the lexical index and all22 public declarations
matched cache/API. All21 field leaves are wired. Artifacts installed atomically.
One overlapping check launch was caught and terminated by owned PID (exit143);
all subsequent checks ran sequentially and both final checks passed.

Local corpus only; no RH focus, no hgtl7, no computations, no README edits,
one owned Lean process at a time, no full/umbrella builds. Preserve other work.

## No-go closure

If the proposed arithmetic cost or rigidity fails, record the exact obstruction
and strongest nontrivial positive survivor before retiring it. Do not count a
generic diagonal inequality, renamed inverse, or already known Franel formula.

## Final verification

Exact commands used `lake --old env lean -j 1 --root=/Users/michael/Documents/code/hgt/formal -o <isolated-cache/module.olean> <original-source.lean>`. No full or umbrella build.

- `DiscretePrimitiveEnergyAndJordanComparison`: 291 lines, 16 named, 9 public.
  Source SHA256 `95fde6856fe8c5b66a769b4551440e4c86dbefa4dae8c2d2aa53a2ed868993f6`.
  Olean SHA256 `46d341cf5c9bbdd6db27427c1effe065c2d8b7f89bac1bbf0b0bb62280c22c9b` (1269128 bytes).
- `SharpPrimitiveEnergySuccessorFrontier`: 435 lines, 18 named, 13 public.
  Source SHA256 `2489fb5a471a59028f1f7c8b17360097d26b64741b3ae7f98cb18f1b16f163ee`.
  Olean SHA256 `146e06306a8043ac321d6d36d9e7cd3bed2fef575653599c7dde7b5ddba25d8d` (1791736 bytes).
- Axiom log: `logs/bvi-root-2026-10-18-primitive-energy-axioms.txt`;
  SHA256 `673643c2971132e599d670fca4d6238679c9d1a2ab618cb4df73a0c039448b14`.
- Read-only README unchanged: `fd49791f7d68e197372bfb55bf0289d3c19d24a39bfdb67eb8881d76a0b869e9`.
- Lint exit1: 381 unrelated large-file warnings;
  no owned-module or proof-debt finding. All remaining errors:
  - `GaloisForLFunctions.RHTower.GammaThetaFullSupportCreation` (unwired foreign leaf).
  - `GaloisForLFunctions.RHTower.GammaThetaFullSupportSource` (unwired foreign leaf).
  - `GaloisForLFunctions.RHTower.GammaThetaSupportWeightBounds` (unwired foreign leaf).
  - `GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailMass` (unwired foreign leaf).
  - `GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailPhaseCells` (unwired foreign leaf).
  - `GaloisForLFunctions.BiScaleUncertainty.SquarefreeGaussianCompletion` (unwired foreign leaf).
- Guarded cleanup removed all 22 owned temporary paths; source, artifact,
  axiom-log and README hashes preserved. All owned jobs are terminal.
  Contribution count: **9 / 250**; goal remains active.

No-go closure: a level-uniform energy/variance upper bound fails by prime escape.
The exact three-facet lower frontier, its full extremizer classification, explicit
realization, and universal inequality cone are the nontrivial positive survivor.
Paper proof and Lean proof are complete.
