# APT complete-form estimates and native model detection

- **ID:** APT-REVIEW1910-A1-A3
- **Stage:** 3-formalized
- **Type:** THEOREMS / SCOPED MODEL RESULT
- **Source:** [review §3](../../../reports/review-1910/astra.md)
- **Statement:** Resolve A1–A3 for an explicit arithmetic family, retaining complete signed channels and costs needed for simultaneous growth.

## Requirements and scope

- [x] **A1:** Complete limiting critical prime form has an explicit negative unit singleton, with margin `4log2/(390π⁴)`.
- [x] **A2:** Finite translated factorial tents have quantitative approximation of the literal prime–Gamma–polar form. An explicit smoothing index permits arbitrary joint growth of finite support, scales, coefficients, and translations.
- [x] **A3:** Same smoothed native family detects an explicit lattice-plus-reflected-pair configuration, with complete diagonal and reflection defect. Native actual-file check passed.
- [x] Complete actual-file, public-declaration axiom, and scoped diff audits; run formal lint and record unrelated failures.
- [x] Audit implications and corpus priority; distinguish model detection from zeta arithmetic compatibility.

A2/A3 select the finite translated span of the existing `factorialSourceRight`
exponential tents. This is an explicit extension of the arithmetic source family.
The direct critical-tail full-form approximation and its lattice-diagonal control
remain separate open problems. No theorem here identifies the model's spectral
form with the actual zeta arithmetic form.

## A1: a negative direction with every harmonic retained

The existing exact common-density formula gives

`factorialCriticalPrimeLimit = (4/π⁴) Σ′_m A_m J_m/m⁴`.

The new proof establishes

`Σ′_m A_m J_m/m⁴ ≤ −log2/390`,

hence `factorialCriticalPrimeLimit ≤ −4log2/(390π⁴) < 0`.
Every translated unit singleton has this same limit. Arbitrary singleton
coefficient `b_j` multiplies it by `b_j²`.

The exact harmonic identity is
`J_m=m[π²/12−∫₀ᵐu⁻²(1−cos(πu/6))du]`.
Global alternating cosine bounds give polynomial lower/upper bounds for the
small harmonics. At `θ=πm/6`, integration by parts also gives
`|J_m−1|≤2/θ` and
`J_m≤1+sinθ/θ+2(1−cosθ)/θ²`.
These imply `J₂≥10/9`, `J₃,J₅≤4/3`, `J₆≤7/6`, the required exact finite-phase
bounds through nineteen, and `J_m≤6/5` for `m≥20`.

The complete finite head is at most
`−(61/7220+1/390)log2`; the entire remaining tail is at most
`(61/7220)log2`. The tail uses `|A_m|≤m logm`, the monotone integral comparison,
and `∫₁₉∞log(x)/x³ dx=(log19+1/2)/722`. All finite comparisons are exact
symbolic inequalities. No independent masses, selected prime subseries, or
numerical experiments enter the sign proof.

The full Weil formula **subtracts** the prime channel. This negative direction
therefore does not assert a negative zeta Weil form or prove RH. It rules out
nonnegativity of the complete critical prime quadratic on all coefficient
patterns; its positive replacements are explicit harmonic control and the
full-form approximation/detection theorems below.

## A2: one source error controls every channel

Write `R_f(t)=∫f(x)f(x+t)dx`, `D=∫|f−g|`. For compact real sources with
value bounds `M_f,M_g` and Lipschitz bounds `K_f,K_g`, the exact identity

`R_f(t)−R_g(t)=∫(f−g)(x)[f(x+t)+g(x−t)]dx`

gives

`|R_f(t)−R_g(t)|≤(M_f+M_g)D`,

`|(R_f(0)−R_f(t))−(R_g(0)−R_g(t))|≤(K_f+K_g)D|t|`.

Let `J=∫₀∞t exp(t/2)/sinh(t)dt`, the corpus's finite nonnegative universal
archimedean moment. Let

`mass(N)=Σ_{1≤m≤N+2} Λ(m)/√m + ∫₀^{log(N+2)}2cosh(t/2)dt`.

When both autocorrelations vanish at and above `log(N+2)`, their literal full
Weil energies `Q` satisfy

`|Q(f)−Q(g)|≤D[(M_f+M_g)(|gammaBracket(0)|+2mass(N))+(K_f+K_g)J]`.

The prime tail vanishes by support, rather than being dropped. The entire
polar density is retained. The Gamma increment identity pays its singular
kernel through the finite first moment; no logarithmic smoothing loss is needed.

For any finite native pattern
`f(x)=Σ_{i∈S} b_i factorialSourceRight(n_i)(x+t_i)`, set

`M=30Σ|b_i|(n_i+1)`, `K=2000Σ|b_i|(n_i+1)²`, `R=1+Σ|t_i|`,

`N=ceil(exp(2(R+1)+1))`,

`C(R,M,K)=(R+1)K[M(|gammaBracket(0)|+2mass(N))+KJ]`.

The corpus mollifier has radius `r_k=1/[4(k+1)]`, preserves value and slope
bounds, and gives `D≤2(R+1)Kr_k`. Consequently

`|Q(smooth_k f)−Q(f)|≤C(R,M,K)/(k+1)`.

Choose `k=ceil((q+1)C(R,M,K))` to obtain error `≤1/(q+1)`. Every finite
pattern parameter may depend on `q`; cardinality, arithmetic scale, translation
aperture, and coefficient moments need not stay bounded. The formula explicitly
pays their growth. It is approximation control, not a uniform bound on `Q(f)`
or a positivity theorem.

## A3: the same admissible test detects the complete model

Fix `L>0`, `0<δ≤1/2`, any integer scale `n≥ceil(32π/L)`, and accuracy index
`q`. The existing `isolatedPairConfig` contains the entire on-line lattice
`1/2+2πik/L`, with multiplicity two, and the reflected pair
`1/2±δ+2πi/L`, with multiplicity one.

Take the native raw difference
`h(x)=factorialSourceRight(n)(x)−factorialSourceRight(n)(x−L)`.
It is precisely the A2 pattern with coefficients `1,−1` and sites `0,−L`.
Its A2 parameters are `M=60(n+1)`, `K=4000(n+1)²`, `R=1+L`.
Choose

`k=max(n,ceil((q+1)C(R,M,K)))`.

The actual test is `f=liftC(smooth_k h)`. Linearity and translation of
convolution give `f(x)=β(x)−β(x−L)`, where
`β=smooth_k(factorialSourceRight n)` is nonnegative, has integral at least one,
and vanishes outside `|x|≤3/(n+1)`. All these properties follow from the
native tent and normalized mollifier. The test is C² and compactly supported.
Its literal arithmetic full-form error is `≤1/(q+1)` by A2.

In the convention `F(z)=∫f(x)exp(izx)dx`, the difference multiplier is
`1−exp(izL)`. Thus every on-line lattice readout vanishes exactly. At
`γ=2π/L`, the off-line multipliers are `1−exp(δL)` and `1−exp(−δL)`.
For a nonnegative seed supported in radius `a`, its tilted readout obeys

`|F_β(γ−iα)−A_α|≤|γ|a A_α`,
`A_α=∫exp(αx)β(x)dx≥exp(−|α|a)`.

Here `γa≤1/4`. The mixed real product of the two seed readouts is at least
`A_δ A_{−δ}/2`. Therefore the complete model Weil value obeys

`Re W_model(f,f)≤−m`,

`m=(exp(δL)−1)(1−exp(−δL))exp(−6δ/(n+1))>0`.

No diagonal term is discarded. With `U=F(γ−iδ)` and `V=F(γ+iδ)`, the full
square diagonal and reflection defect are exactly

`Z=|U|²+|V|²`, `D_reflection=|U−V|²`,

`Z−Re W_model=D_reflection`, hence `D_reflection−Z≥m`.

The infinite on-line contribution is exactly zero in all three sums. Scale `n`
may grow arbitrarily above its threshold; period/aperture `L` and accuracy `q`
may vary simultaneously. `factorialTentDetector_spec` packages admissibility,
literal full-form approximation, positive margin, model negativity, and the
complete diagonal/defect gap for this single test.

## Additional positive result for the unresolved critical-tail route

The public bounded primitive
`G(v)=Σ b_n latticePrimitive_n((n+1)v)/(n+1)` satisfies
`G′=Re factorialPhaseCombination` on `v>0` and
`|G|≤12Σ|b_n|/(n+1)`. It now also replaces the duplicated private primitive
proof in `FactorialCriticalPrimeAdmission` without changing its public results.

The critical polar endpoint is rigorously defined as
`−G(1)+∫₁∞G(v)/v² dv`. Its magnitude is at most `24Σ|b_n|/(n+1)` and its
finite-cutoff error is at most `(24/T)Σ|b_n|/(n+1)` for `T≥1`.
This handles the conditional improper endpoint through an absolutely convergent
primitive integral. It does not complete the direct critical Gamma cutoff or
its model-diagonal analysis; neither route is retired or declared blind.

## Corpus priority and significance

The existing charged-prime kernel/common-density identities, factorial tent
regularity, full Weil jump formula, compact mollification, and explicit off-line
models are reused. Period-difference/two-bump detection already appears in
`ZeroLatticeDepthNyquistLaw` and `IsolatedOffLinePairVisibilityLaw`; this work
calibrates that mechanism to the native arithmetic family and the same joint
full-form accuracy index. It does not claim invention of the detector mechanism.

Documented corpus queries screened all returned candidate lemmas and source
arguments, including critical full-form estimates, quantitative smoothing,
native tent detection, and lattice differences. Inventory coverage was complete;
compiler coverage was mixed source-only/stale/pending. Relevant inputs were
verified through Lean. No matching native combined endpoint was found in those
hits; this is corpus evidence, not external novelty certification.

The research gain is a complete prime sign decision in one explicit direction,
a reusable quantitative full-form stability estimate, and a demonstrably
detecting native subfamily whose approximation cost is explicit as it grows.
The model does not enforce all zeta arithmetic axioms. Full positivity on a
sufficient family, or a contradiction from an actual off-line zeta zero, remains
unproved.

## Installed proof and verification inventory

All leaves are in `formal/GaloisForLFunctions/arithmetic-positivity-theory/` and
imported by `ArithmeticPositivityTheory.lean`:

- A1: `FactorialCriticalHarmonicTaylorBounds`, `FactorialCriticalHarmonicOscillationBounds`, `FactorialCriticalHarmonicFiniteBounds`, `FactorialCriticalPrimeSingletonNegative`.
- A2: `CompactFullWeilQuantitativeSmoothing`, `FactorialTranslatedTentApproximation`.
- A3: `PeriodDifferenceOffLineDetection`, `FactorialTentOffLineDetection`.
- Critical polar survivor: `FactorialCriticalPhasePrimitive`, `FactorialCriticalPolarCutoff`; existing `FactorialCriticalPrimeAdmission` reuses the public primitive.

All eleven touched leaves passed direct actual-file checks with
`lake --old env lean -j 1 <actual-file>`; new dependencies were emitted with
`-o .lake/build/lib/lean/...olean`. Some successful checks contain harmless
tactic-style warnings. No full/umbrella build or heartbeat increase was used.

The final `/tmp` axiom audit checked all **102 public declarations**, including
definitions, support results, and `factorialTentDetector_spec`. Every dependency
is confined to `propext`, `Classical.choice`, and `Quot.sound`; no diagnostics or
additional axioms occur. All eleven import links, forbidden-proof-token checks,
and scoped whitespace/diff checks passed.

`scripts/formal_tools.py lint` returned **1** because two unrelated concurrent
modules are unreachable from `ArithmeticCriticalityTheory.lean`:

- `GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds`
- `GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePotentialBounds`

No owned leaf is named among those failures. The foreign files remain untouched;
there is no repository-wide green claim. Final audit evidence is retained in
`/tmp/apt_review1910_final_axioms.lean`, `/tmp/apt_review1910_final_axioms.log`,
`/tmp/apt_review1910_final_manifest.txt`, and `/tmp/apt_review1910_lint_final.log`.
Stale owned scratch/search artifacts were removed after their reusable findings
were recorded here and in `logs/apt-review1910-knowledge.md`. No numerical
experiments, commits, pushes, or foreign-job interruptions occurred.
