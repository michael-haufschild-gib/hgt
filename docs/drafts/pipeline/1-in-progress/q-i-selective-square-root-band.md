# Q-I: selective cancellation at the square-root band

- **ID:** q-i-selective-square-root-band
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-2410/opus.md, §3 Q-I
- **Statement:** Find and unconditionally formalize a Beurling-selective, single-zeta estimate giving a fixed power saving at the square-root band, including its mathematical consequences and corpus applications.

## Goal

Resolve the fixed-strip question itself. A shrinking Vinogradov–Korobov band, a conditional
transfer theorem, an equivalent formulation, or a restricted no-go does not constitute a full
answer. The report identifies the target with `zetaZeroAbscissa < 1`. Audit that identification
against the actual declarations before applying it. Do not use the `hgtl7` skill or numerical
experiments. Preserve pre-existing worktree changes.

Only results with successful Lean proof checks and transitive axiom audits count
as proved. Paper arguments and unchecked drafts remain open formalization
obligations. Every significant finding below must reach that standard.

## Gates

- [x] Read the complete source report and task attachment; inspect repository instructions.
- [x] Search the Lean corpus before consulting mathlib.
- [ ] Establish a dependency-closed paper proof of an answer to Q-I.
- [ ] Formalize the exact answer and all derived corollaries without unproved analytic inputs.
- [ ] Apply the result in the relevant receiver, short-window, band, and source programmes.
- [ ] Check every new leaf with `lake --old env lean`; audit transitive axioms; wire umbrellas.
- [ ] Completion audit against the full original task, not intermediate milestones.

## Current evidence

- `CompletePronicVaughanCalibration.lean` gives the exact 25-entry signed Gram expansion,
  logarithmic source cancellation, a nonsummable logarithmic majorant, and a uniformly bounded
  difference between the interior and centered-source energies.
- The fifth Vaughan component is independent of both cutoffs and equals the negative pole
  density times the horizon, plus a bounded active correction. Thus individual Gram entries
  contain pole mass before cancellation. Any estimate of their absolute sizes must account for
  this source-defined linear term.
- Existing uncommitted files include work on the balanced statistic and Biarithmetic Geometry;
  those are separate work and must not be overwritten.

## Conjecture loop

**Balanced prime-band audit.** The current corpus sources
`TheCentredPrimeBandIsTheQuasiRiemannHypothesis.lean` and
`TheCentredPrimeBandFromAZeroFreeStrip.lean` have been read in full. They identify
`CentredPrimeBandPowerSaving` with `zetaZeroAbscissa < 1`: the converse recovers a
power rate for the prime reciprocal tail and then `ψ(N)-N`; the forward proof
uses the fixed strip to supply the prime partial-sum rate. This adds an exact
bridge to the same target, not an unconditional producer of that target.


**Source audit of the Guth–Maynard input.**
`ShortWindowDispersionAtSeventeenThirtieths` already applies the `30/13`
zero-density theorem to unbalanced centered-prime dispersion, in the explicit range
`P^(1+δ)≤Q≤P^(30/17-δ)`. That does not include the balanced band `P≈Q`.
`MaynardBufferedPhysicalSelectedCellNoGo` proves that the ordinary unpolarized
Guth–Maynard middle term exceeds the required Route-T receiver exponent throughout
the physical phase. Its positive survivor identifies a need to retain paired
cancellation before taking the large-value count. This is an existing, scoped
obstruction; it neither retires Q-I nor supplies a fixed strip.

1. **Audit the quantitative Class III target.** Determine the unavoidable leading pole part of
   the Vaughan Gram and whether the actual source already forces large negative mixed energy.
   Seek an exact positive decomposition identifying the residual estimate after pole removal.
2. **Test restricted-source estimates.** Use the resulting decomposition to locate a genuinely
   selective estimate, rather than a bound on an entry whose linear growth is forced.
3. **Transfer only proved savings.** Check implications across the receiver, Möbius windows,
   prime windows, and band compression. Record unresolved analytic inputs explicitly.

## No-go closure

No route retired. A failed conjecture requires a strongest non-trivial positive survivor,
paper proof, and Lean proof when dependency-closed. Failure of one estimate is not a negative
answer to Q-I.

## Paper proof: pole mass and normalized mixed cancellation

[PROVED HERE; first Lean leaf check passed] Write `ρ = Re(1/ζ(1+ε)) > 0`, `a_n` for the active
correction, and `I_n` for the interior prefix. For every `ε > 0`, the source mean theorem
gives `I_n/n → 0`, since the centered divisor prefix is `o(n)` and `|a_n| ≤ 1/2`.
Cesàro averaging then gives `E_T^int/T → 0`. This uses absolute convergence at `1+ε`,
not a zero-free strip or even a quantitative PNT.

For every pair of Vaughan cutoffs, the last component is `p_4(n) = -ρn-a_n`. Hence
`G_44/T → ρ²`. More explicitly, `(ρn+a_n)² ≥ ρ²n²/2 - 1/4`, and
`n/(n+1) ≥ 1/2` for `n≥1`, so

`G_44 ≥ ρ²T/4 - 1/4`.

The full diagonal `D_T = Σ_i G_ii` dominates `G_44`, uniformly in cutoffs. Since
`E_T^int = D_T + R_T^mix`, it follows that `R_T^mix/D_T → -1`, uniformly over all
cutoff choices, even choices varying with `T`. Thus arbitrarily high *relative* cancellation
of the uncentered Vaughan diagonal is already unconditional. It does not establish bounded
energy: the unnormalized error is exactly `E_T^int`.

The positive survivor is an explicit scale calibration: the diagonal contains linear pole
mass and only the residual cancellation rate, rather than a fixed relative gap, can carry
the requested zero-free information. This is not a negative answer to Q-I.

### Exact obstruction for individual cross entries

[PROVED HERE; first Lean leaf check passed] The sum of the pole row is the pronic pairing of `p_4`
with `I`. Divided by `T`, that pairing tends to zero by the same Cesàro argument.
Subtracting `G_44` therefore gives

`(G_40 + G_41 + G_42 + G_43)/T → -ρ²`.

This sum is exactly independent of both cutoffs. Hence no cutoff schedule can make every
one of these four entries `o(T)`. This refutes a specific proposed absolute-entry estimate;
it does not refute Q-I or prove that all Class III identities are insufficient. The strongest
positive survivor is the exact negative linear density together with uniform relative
cancellation and the exact residual identity.

The ratio here is `R_mix/D` for the uncentered Vaughan diagonal, whose pole contribution
has order `T`. It is not THIM's long-sawtooth/tail Cauchy–Schwarz ratio at order
`T^(1-2ε)`. The latter's strict gap remains open in the report's interior region.

Draft module: `formal/GaloisForLFunctions/BezoutValuationIncidence/TheVaughanDiagonalContainsLinearPoleMass.lean`.
Main names: `pmPronicVaughanDiagonal_linear_lower`,
`tendsto_pmPronicVaughanGram_pole_div_nat`,
`tendsto_pmPronicVaughanPoleMixed_div_nat`,
`not_all_pmPronicVaughan_pole_cross_entries_sublinear`,
`eventually_pmPronicVaughan_relative_cancellation`, and
`tendsto_pmPronicVaughan_mixed_div_diagonal`.
The complete leaf check passed. A subsequent extension gives a cutoff-uniform finite witness:
eventually at every horizon some `j ≠ 4` satisfies `G_4j ≤ -ρ²T/8`. Its olean-producing check
also passed, needed only because the new fixed-cutoff Gram module imports it. The transitive
axiom audit passed for the principal declarations, with only `propext`, `Classical.choice`,
and `Quot.sound`. The final direct no-olean check also passed for the complete pole module.
It is wired into the BVI umbrella; no umbrella was compiled.

### Next conjecture after pole calibration

Center the individual finite-cutoff small Vaughan legs at their own linear densities. Their
remaining floor errors are bounded and therefore have finite pronic energy. Determine the
remaining large-leg cancellation without dropping its signed cross terms. Search already found
the Type-II short coefficient identity and finite-row receiver calculus; no new selective
residual estimate has yet been established. This is an attack direction, not a claimed theorem.

### Full fixed-cutoff Gram classification

[PROVED HERE; Lean check and transitive-axiom audit passed] For fixed cutoffs `U,V`, set
`A_U = Σ_(d≤U) μ(d)d^(-1-ε)`, `Z = Σ_(k≥1) k^(-1-ε) = 1/ρ`, and

`c = (A_U, A_V, -Z A_U A_V, ρ-A_U-A_V+Z A_U A_V, -ρ)`.

Then `p_i(n)/n → c_i` for all five pieces, and `G_ij(T)/T → c_i c_j`.
For the first two pieces, apply the finite sum of `floor(n/d)/n → 1/d`.
For the third, fix `a,b`, write `N=floor(n/(ab))`, and use

`Σ_(k≤N) (abk)^(-ε) floor(n/(abk)) = (ab)^(-ε) Σ_(k≤N) k^(-ε) floor(N/k)`.

The inner divisor average divided by `N` tends to `Z`, by absolute convergence of
`Σ k^(-1-ε)`; also `N/n → 1/(ab)`. Summing finitely over `a,b` gives the third
coefficient. The exact five-piece identity and the already proved source mean limit give
the fourth coefficient. The fifth is the pole component. Cesàro averaging products gives
the Gram limit. No assertion of uniformity in `U,V` is made for this full matrix limit.

Consequently, for fixed cutoffs, `D/T → Σ c_i² > 0`; bounded residual energy is equivalent
to an `O(1/T)` bound on `1+R_mix/D`. Merely obtaining a positive decay exponent for this
ratio is insufficient to establish the requested estimate. The known VK receiver bound
would give exponent `2ε` in these coordinates; the missing power is `1-2ε`.

This classification is formalized using `pm_tendsto_divisor_average` and the new pronic
Cesàro lemma. It is a positive structural result, not a proof of the missing residual bound.

`TheFixedVaughanGramHasRankOneLeadingTerm.lean` passed its olean-producing leaf check, needed
because the atomic-budget module imports it. Its principal declarations passed the
transitive-axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`; the final
direct no-olean check passed. Its umbrella import is present. Its proof uses finite
floor means, the unsigned divisor average, and the exact five-piece identity. No computation
or analytic estimate beyond absolute convergence enters this first-order classification.

### Secondary unsigned divisor term: existing result found

For `0<ε<1`, the unsigned floor sum admits the exact two-term expansion
`Σ_(d≤n) d^(-ε) floor(n/d) = ζ(1+ε)n + ζ(1-ε)n^(1-ε)/(1-ε) + O_ε(n^((1-ε)/2))`.
Corpus search found the exact theorem `norm_cpowFloorSum_sub_le` in
`TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta.lean`; its real specialization is
`abs_subHalfRemainder_le` in `SubHalfDampingPartialPoleSumsAndLogarithmicMomentIndexLaws.lean`.
The same module proves the stronger uniform atomic estimate
`pronicNorm_subHalfDilationRemainder_le`: the dilated remainder supported on `n≥j` has norm
at most `C_ε j^(-1/2)`. The new task is the exact Vaughan specialization and moving-cutoff
budget, not reproving this unsigned asymptotic.

For the small-small kernel the absolute atomic norm budget has weights
`|μ(a)μ(b)|(ab)^(-ε-1/2)`. Summing these over a rectangle factors into the product of two
critical Wiener partial sums. At square-root cutoffs its trivial norm exponent is again
`1/2-ε`, hence energy exponent `1-2ε`. A selective gain must improve this signed assembly,
rather than the already-paid individual smooth-power remainder. This is the next conjecture
audit; no improved signed assembly estimate has been proved.

### Next exact assembly and sharp budget audit

Let `p=ε+1/2`, `q=1/2-ε>0`, and
`W_ε(U)=Σ_(1≤a≤U)|μ(a)|a^(-p)`. Define the literal signed atomic remainder

`R_(ε,U,V)(n)=Σ_(a≤U,b≤V) μ(a)μ(b)(ab)^(-ε) 1_(ab≤n) R_(ε,ab)(n)`,

where `R_(ε,j)` is the existing `subHalfDilationRemainder`. Finite norm subadditivity
and `pronicNorm_subHalfDilationRemainder_le` give
`‖R_(ε,U,V)‖_T ≤ C_ε W_ε(U)W_ε(V)`, uniformly in `T`.

The exact small-small identity to formalize is

`p_2(n) = -Z L_(ε,U,V)(n) - c_ε n^(1-ε) P_(U,V)(n) - R_(ε,U,V)(n)`,

where `L=Σ μ(a)μ(b)(ab)^(-ε) floor(n/(ab))`,
`P=Σ_(a≤U,b≤V,ab≤n) μ(a)μ(b)/(ab)`, `Z=ζ(1+ε)`, and
`c_ε=Re ζ(1-ε)/(1-ε)`. This retains the floor and partial-pole terms; an estimate on
the atomic remainder alone must not be advertised as controlling the entire source.

For a sharp budget obstruction, the existing squarefree quarter-density bound gives
`W_ε(N)≥N^q/4` for every `N≥1`, whereas the elementary power-sum estimate gives
`W_ε(N)≤C'_ε N^q` for `N≥1`. At the square-root rectangle the squared absolute budget
is `W_ε(N)^4`, of order `N^(2-4ε)=T^(1-2ε)` for `T=N²`. Thus this numerical upper
budget itself admits no fixed power saving. This is an obstruction to that bound, not
a lower bound on the actual signed remainder. Useful corpus inputs:
`tendsto_window_squarefree_density`, `squarefreeDensity_eq`,
`sum_rpow_neg_subcritical_le`, `pronicNorm_sum_le`, and `pronicNorm_smul`.

Draft `TheAbsoluteVaughanRemainderBudgetHasTheTrivialExponent.lean` currently contains the
exact small-small extraction, signed-remainder norm bound, upper/lower bounds for the absolute
mass, squared-budget power bounds, and the explicit no-power-saving corollary. Its first direct
leaf check left two proof-script errors (addition order and an unreduced composition), both
corrected. The source audit passed with only `propext`, `Classical.choice`, and `Quot.sound`
for all ten public theorems. Its umbrella import is present; final direct leaf check passed.
Four further corollaries make the positive atomic constant, the literal remainder's trivial
energy bound, and the no-saving obstruction at horizon `T=N²` explicit. All four additions
passed the olean-producing leaf check after one cast normalization. All fourteen transitive
axiom reports passed with only the standard axioms; final direct leaf audit passed.
Its fixed-Gram dependency is compiled. The paper proof is tracked in
`../3-formalized/vaughan-smooth-remainder-and-absolute-budget.md`.

**Moving-cutoff caution.** The existing `sum_moebius_weight_eq_rectangular` already proves
that the both-large remainder vanishes when `T<(U+1)(V+1)`. In particular, at `T=N²`
and `U=V=N` it is identically zero throughout the energy sum. The fixed-cutoff centering
idea therefore cannot be applied at the square-root horizon without uniform estimates
for the growing small-small piece and its signed cross terms. The new fixed-Gram module
also records this exact vanishing, keeping the two limiting regimes distinct.

The dependency-closed structural result and exact restricted no-go are tracked separately in
`../3-formalized/vaughan-pole-mass-and-fixed-cutoff-gram.md`. This Q-I card remains in progress.

### Stronger conjecture: uniform leading Gram law

[PROVED HERE on paper; Lean draft started] Absolute convergence gives a uniform extension of
the leading matrix approximation: `G_ij(T;U,V)/T-c_i(U,V)c_j(U,V)→0` uniformly over both
cutoffs. For a coefficient family dominated by `b(d)` with `Σ b(d)/d<∞`, the floor-mean
error is uniformly bounded by
`Σ b(d)/d - (1/n)Σ_(d≤n)b(d)floor(n/d)`, which tends to zero. For the small-small piece,
the majorant is `b(d)=d^(-ε)(1*1*1)(d)`; its Dirichlet mass is `ζ(1+ε)^3`.
Uniform boundedness of the five means then converts this error into a uniform Cesàro
bound for all Gram entries.

At square-root cutoffs a simpler proof may suffice: the both-large piece vanishes exactly,
the two small legs differ from the full Möbius floor prefix by at most
`n Σ_(d>N)d^(-1-ε)`, and the five-piece identity determines the small-small leg.
This predicts `G(N²;N,N)/N²→ρ² vvᵀ`, `v=(1,1,-1,0,-1)`, and diagonal density `4ρ²`.
It is a further leading-order classification, not a residual saving. The dependency-closed proof
and internal novelty audit are in `../3-formalized/uniform-vaughan-gram-leading-term.md`.
No external novelty is claimed for this specialization of uniform dominated convergence.

### Fixed-cutoff classification and finite harmonic rigidity

The normal-form paper proof is now dependency-closed in
`../3-formalized/vaughan-finite-cutoff-receiver-normal-form.md`. Every fixed packet is
`w_3 I_ε + L_w n + Q_w n^(1-ε)` plus bounded pronic energy. The existing VK source
estimate and smooth-power norm asymptotic force both explicit coefficients to vanish
for an admitted packet; admission then retains exactly the original receiver direction.
The same proof gives a second rank-one Gram limit after subtracting the linear means.
Both classification and second-scale limit passed the complete Lean scratch check and
all nineteen transitive-axiom audits. Repository production passed; the final direct check passed.

The coefficient `Q_w` simplifies at positive cutoffs because finite Möbius harmonic
sums never vanish. The denominator proof and stronger terminal-prime valuation law are
in `../3-formalized/finite-mobius-harmonic-sums-never-vanish.md`. All eight p-adic and
nonvanishing theorems passed their scratch check and transitive-axiom audit, using only
standard axioms. Their repository leaf is `RHTower/FiniteMobiusHarmonicSumsNeverVanish.lean`,
wired with its producing check passed; the final direct check passed. This forces
`w_2=w_3` in the admitted fixed packets. It gives no polynomial lower bound for the
harmonic sums and no gain for moving cutoffs.

### Product-horizon second scale

A further dependency-closed paper result is in
`../3-formalized/vaughan-product-horizon-centred-gram-has-zero-trivial-density.md`:
at `T=UV`, with both cutoffs divergent and arbitrary aspect ratio, subtracting each
cutoff-dependent linear mean makes every component norm `o(T^(1/2-ε))`, hence every
centered Gram entry `o(T^(1-2ε))`. Small legs cost only `W_ε(U)` and `W_ε(V)`;
the exactly vanishing both-large leg leaves the product of two signed reciprocal tails.
The scaled tail limit follows from the checked mean-zero Möbius theorem and
`abs_tsum_tail_rpow_le_of_linear`. This contrasts with the nonzero second-scale density
at fixed cutoffs. It gives no fixed power saving. The eight scaled-tail declarations include the bounded scaled
tail and the product limit requiring only a divergent product of indices. All eight
scratch axiom audits passed with standard axioms. The checked source is now
`SignedVaughanTailsVanishAtTheirAbsoluteScale.lean`; its producing and final direct checks passed.
The full moving matrix proof, uniform over all factorizations with divergent product,
passed fifteen scratch axiom audits. Its repository module
`ProductHorizonVaughanGramsHaveZeroTrivialDensity.lean` passed its producing and final direct checks.

### The empty large leg already detects the missing power rate

The dependency-closed paper equivalence in
`../3-formalized/vaughan-empty-large-leg-power-gain-and-fixed-strips.md` sharpens the
moving-cutoff obstruction. At square cutoffs the centered both-large diagonal is exactly
`Z²(ρ-A_N)^4 ‖n‖_(N²)^2`. A fixed power gain at its trivial scale is equivalent to a
power rate for the signed reciprocal tail, hence to `zetaZeroAbscissa<1` by finite Abel
inversion and the checked Mertens-rate equivalence. The literal both-large piece is empty;
its centering imports the infinite reciprocal density. No power rate has been proved.
The exact energy identity passed the residual-density audit. Finite Abel inversion,
the power-increment bound, both directions of the tail-rate equivalence, and the
explicit Mertens-to-tail rate passed seven standard-axiom audits in
`VaughanReciprocalTailPowerGainsAreFixedStrips.lean`. Its producing and final direct checks passed.
All four energy-rate targets in `TheEmptyVaughanLegDetectsAFixedStrip.lean` passed
their standard-axiom and final direct audits. The exact equivalence holds for every
fixed `0<ε≤1`, with energy saving measured in `N` and horizon saving half that exponent.

### Verification details

Final direct `lake --old env lean` checks passed for the fixed Gram, absolute budget,
uniform leading Gram, fixed-packet normal form, harmonic nonvanishing, and residual-density
leaves. The pole leaf had already passed. Umbrella imports are present. Their completed
transitive-axiom audits list only the standard axioms. The coefficient-space leaf also
passed its final direct audit. Eight completed cards, including the normal form and its
dimension corollaries, are now in stage 3. Two precisely scoped failed-route cards record the pole-cross and absolute-
budget obstructions with their audited positive survivors.

The residual-density leaf includes all nineteen public statements: source and smooth
scale limits, packet norms and energies, signed pairing and matrix laws, smooth-mean
necessity, complete admission equivalence, and the exact empty-large-leg statistic.
Its olean supports the fully checked coefficient-space importer.
A further theorem extends the classification across half damping:
`../2-fully-proven/vaughan-admission-phase-transition-at-half-damping.md`. Its dependency-closed
paper proof gives dimension three at half damping and four above it, with a uniform
upper-half centered-component bound. Its upper-half claim is uniform
in the cutoffs; no additional lower-half source estimate is asserted.
The coefficient-space, unique-coordinate, and quotient-dimension corollaries are fully
checked in `TheAdmittedVaughanCoefficientSpace.lean`, with ten standard-axiom reports.
The product-horizon paper result has a stronger uniform extension in
`../3-formalized/uniform-product-horizon-vaughan-second-scale.md`: only the product
must diverge. Uniform mean-zero estimates for all truncated Möbius patterns pay the
two small centered legs at the trivial scale. The ten uniform-pattern, energy, and exact
small-leg bridge declarations passed all ten scratch axiom audits with standard axioms.
Their checked source is `UniformTruncatedMobiusReceiversHaveZeroTrivialDensity.lean`;
its producing check passed for the product-horizon importer; its final direct audit passed.
A further scale-contraction conjecture
is tracked in `vaughan-tail-scale-contraction.md`; no composition estimate is proved.
The exact zero-cutoff boundary is proved on paper in
`../2-fully-proven/vaughan-zero-cutoffs-remove-the-smooth-obstruction.md`: the vanished
small-small piece adds one free coefficient direction, giving admitted dimension three
or four below half damping, and four at half damping. These dimension corollaries remain
to formalize.
The dependency-closed rank-set application is in
`../2-fully-proven/vaughan-admitted-rank-filtration-reads-the-zero-abscissa.md`:
for every cutoff pair, the damping set acquiring the extra receiver direction equals
the existing receiver damping set, with lower accumulation boundary `Θ-1/2`.
This is a finite coefficient-space realization of the existing analytic index, not a
finite test for admission. Its Lean proof awaits the dimension and phase extensions.

The uniform second-scale theorem is now proved on paper for all cutoffs independently
of the horizon: `../2-fully-proven/uniform-second-scale-vaughan-gram-at-all-cutoffs.md`.
The undamped small-small convolution has mean `H_U H_V` uniformly with every logarithmic
rate. A generalized finite hyperbola bound transfers this to the damped centered pieces.
Thus the normalized centered Gram is uniformly asymptotic to its smooth rank-one term;
if both the horizon and the cutoff product diverge, that entire Gram tends to zero at
the trivial scale. The error admits every prescribed logarithmic saving. Its Lean
formalization remains pending; this gives no fixed power saving.

An exact extreme-cutoff invariant sharpens this boundary:
`../2-fully-proven/uniform-vaughan-residual-power-rates-are-fixed-strips.md`.
At `U=1,V=T`, the two centered convolution pieces are proportional with factor `ρ-1`.
After subtracting the smooth Gram model, their corresponding error contrast equals
`ρ subHalfZetaCoeff(ε)^2 H_T^2/(1-2ε)>0`. A fixed power rate for the uniform residual
Gram law is therefore equivalent, on paper, to a fixed zero-free strip. Eleven finite
identity, positivity, cofinal-obstruction, and harmonic-rate theorems are drafted in `/tmp/QIExtremeCutoffTools.lean`;
their Lean check remains pending.

## External calibration

Guth–Maynard, [*New large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2405.20552),
states the `30/13` zero-density estimate and `17/30` short-interval consequence. Its stated
density exponent is positive for a fixed `σ<1`; that bound alone does not make the zero count
vanish. The existing corpus already incorporates these results. No external theorem is assumed
in the new pole-calibration proofs.

## Log

- 2026-10-25 — Created after reading the attachment and report, checking the worktree, and
  searching the corpus. Full Q-I remains open.

The endpoint has a stronger paper law in
`../2-fully-proven/uniform-half-damping-vaughan-harmonic-gram.md`: subtracting the explicit
harmonic rank-one term leaves a uniformly bounded matrix error for all cutoffs and horizons.
With both cutoffs divergent, the renormalized Gram tends to the finite Gram of the actual
rows `(A,A,-A,0,P)`, of rank exactly two on paper. At product horizons the harmonic mass vanishes,
and the centered trace has a uniform endpoint budget. These endpoint refinements remain
to formalize and provide no fixed strip below half damping.

The pole's positive finite energy has a separate dependency-closed proof in
`../2-fully-proven/the-centred-vaughan-pole-has-positive-finite-energy.md`.
For every `ε≥0`, its limit lies between `2^(-2ε)/32` and `1/4`, independently of
moving cutoffs. The full normalized residual matrix therefore cannot decay with
power exponent greater than `1-2ε`. Its seven Lean audit targets are drafted but
unverified. The positive energy also proves the endpoint limiting Gram is nonzero.

The two-cell refinement is proved on paper in
`../2-fully-proven/the-endpoint-vaughan-limit-has-rank-two.md`: finite Euler factors
at primes two and three give an explicit positive determinant for the actual prefix
and pole rows. Their endpoint two-by-two Gram determinant is at least `1/62208`.
This proves exact rank two; its Lean formalization remains pending.

The exact decay indices are now proved on paper in
`../2-fully-proven/vaughan-tail-and-energy-decay-indices.md`.
For every fixed `ε>0`, the supremal signed-tail gain is `1-Θ`, independent of
damping; the normalized square empty-leg energy has index `4(1-Θ)` in `N`, or
`2(1-Θ)` in the horizon. The proof combines the checked quartic identity, finite
Abel inversion, and the read Littlewood and absolute-Mertens-moment exponent laws.
The compact-interval power-increment bound removes the earlier restriction `ε≤1`
on paper; its five Lean targets remain unverified. The full rate sets, including
endpoint attainment, are independent of positive damping. Twenty-six Lean targets
for the indices, exact rate sets, and horizon formulations are drafted, uncompiled.
These identities supply no positive lower bound for the width.

## Checked uniform undamped convolution rate

`UniformCancellationInTheUndampedVaughanConvolution.lean` and
`UniformLogarithmicCancellationInTheVaughanConvolution.lean` passed their scratch,
producing, and final direct leaf checks. All eleven transitive axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`; both modules are wired and
their temporary audit files are removed. The completed card is
`../3-formalized/uniform-undamped-vaughan-convolution-cancellation.md`.

The theorem gives `Σ_(d≤n)(μ_≤U*μ_≤V*1)(d)=nH_UH_V+O_q(n/(log n)^q)` for
every integer `q≥0`, uniformly over all cutoffs. The generic divisor-square
hyperbola estimate and damped logarithmic transfer have now passed all six
scratch axiom audits, producing checks, and final direct checks. Their completed
card is `../3-formalized/divisor-bounded-damped-floor-logarithmic-transfer.md`.
The actual fluctuation and exact centered-row decomposition also passed all nine
scratch axiom audits, producing and final direct checks; see
`../3-formalized/vaughan-convolution-mean-and-logarithmic-fluctuation.md`.
The generic prefix-to-energy transfer passed all six standard-axiom audits and
its producing and final direct checks; see
`../3-formalized/uniform-logarithmic-prefix-to-pronic-energy.md`. The five actual
convolution and truncated-Möbius norm targets also passed their standard-axiom
audits, producing check, and final direct check. They are wired as
`UniformLogarithmicEnergyInTheVaughanConvolution.lean`; see
`../3-formalized/uniform-logarithmic-vaughan-convolution-energy.md`.
The four actual Möbius prefix and interior targets also passed standard-axiom
audits, producing and final direct checks. They are wired as
`LogarithmicEnergySavingsForTheMobiusInterior.lean`; see
`../3-formalized/logarithmic-energy-savings-for-the-mobius-interior.md`.
The six all-row remainder targets also passed their scratch, producing, and final
direct checks, with standard axioms only. They give every logarithmic pronic norm
saving uniformly over both cutoffs for all five smooth-subtracted rows, whose
sum is exactly the Bézout interior. They are wired as
`UniformLogarithmicRemaindersInAllVaughanRows.lean`; see
`../3-formalized/uniform-logarithmic-remainders-in-all-vaughan-rows.md`.
The four complete uniform Gram targets also passed scratch, producing, and
final direct checks with standard axioms only. They are wired as
`UniformVaughanGramsFollowTheirSmoothRankOneTerm.lean`; see
`../3-formalized/uniform-vaughan-grams-follow-their-smooth-rank-one-term.md`.
The finite packet identities and seven homogeneous logarithmic packet laws
also passed producing and final direct checks with standard axioms only; see
`../3-formalized/vaughan-packet-gram-identities.md` and
`../3-formalized/uniform-logarithmic-laws-for-vaughan-superpositions.md`.
The fourteen arithmetic amplitude targets also passed producing and final
direct checks with standard axioms only. They are wired as
`TheCompactArithmeticAmplitudesOfVaughanGrams.lean`: compact countable infinitude,
finite-fiber rigidity at positive limits, and exact positive-cutoff escape.
The eight matrix-classification targets passed corrected producing and final
direct checks with standard axioms only, and are wired as
`TheSubcriticalVaughanGramLimitSet.lean`. They include positive-cutoff attainment,
the exact zero-limit converse, the convergence dichotomy, and explicit bounded
moving-packet energy decay. Four scalar-topology targets passed producing and
final direct checks with standard axioms only, and are wired as
`TheOnlyAccumulationOfVaughanAmplitudesIsZero.lean`: positive-amplitude isolation,
unique zero accumulation, and the convergence alternatives' mutual exclusion.
The remaining matrix rank and topology, endpoint,
and power-rate consequences remain
under verification. All fifteen existing paper
cards and their remaining Lean coverage are listed in
`q-i-existing-findings-lean-completion.md`; completing that register has priority
over new conjecture work. Paper arguments and unchecked drafts remain unproved.

The two uniform truncated-Möbius logarithmic targets passed their scratch
axiom audits, producing check, and final direct check. They are wired as
`UniformLogarithmicCancellationInTruncatedMobiusReceivers.lean`; the completed
card is `../3-formalized/uniform-logarithmic-truncated-mobius-receivers.md`.
One threshold works for every truncation cutoff, including at half damping.

The fresh source `TheCofinalSlopeIsTheOneLineEnergyOfOneOverZeta.lean`
expresses the cofinal slope as a weighted integral of
`1/|it ζ(1+it)|²`, with an absolutely convergent Euler-product weight.
Its boundary-value proof uses convergence from `Re s>0` to `Re s=0`
for the Laplace transform, hence only the zeta line `Re s=1`.
This is an exact arithmetic spectral representation, not a bound on a
line to its left. No fixed-strip input was found there. The concurrent
leaf was source-audited, not independently compiled in this work.

The rank-three prime-Gram expansion has a second restriction beyond the
short-window terminal block: its explicit remainder is `(3/4)p³/q²`.
For comparable primes this has the same order as the trivial kernel scale
`p²/q`. Thus the expansion's remainder alone does not save a power in the
balanced band, even if its displayed Kloosterman term is controlled.
Here “rank three” describes the three separable smooth terms of the Gram;
the oscillatory sums are classical Kloosterman sums, not an asserted
rank-three hyper-Kloosterman estimate. The exact reciprocity and Wiener
identities remain available; this observation does not retire that route.

Four further consequences are dependency-closed on paper; their Lean status follows:

- `../2-fully-proven/uniform-vaughan-convolution-stretched-exponential-rate.md`
  uses the read harmonic Möbius stretched-exponential source to strengthen the
  uniform convolution rate and give one threshold for factorial logarithmic bounds.
- `../2-fully-proven/vaughan-endpoint-rates-and-zero-multiplicity.md` proves that
  attained positive tail rates force simple zeros on their boundary line, while
  the maximal tail scale cannot have little-o decay. The quartic comparison gives
  the corresponding unconditional empty-leg energy oscillation.

- `../2-fully-proven/vaughan-subcritical-gram-limit-classification.md` classifies
  all subcritical moving-cutoff Gram limits. Their amplitudes form a countably
  infinite compact set, discrete away from zero. A nonzero limit forces the
  cutoffs eventually into one fixed finite amplitude fiber. Arithmetic and matrix
  classification drafts exist but remain unchecked.
- `../3-formalized/positive-vaughan-cutoff-escape-is-zero-gram-limit.md` proves
  that, for positive cutoffs and a divergent horizon, the zero normalized Gram
  limit is equivalent to cutoff-product escape. Its converse and the resulting
  convergence dichotomy are drafted but unchecked.

None of these statements proves a positive fixed-strip width. Full Q-I remains open.

## Prime reciprocity source audit

The current source `ExactParsevalAndRankThreeKloostermanLawOfThePrimeGram`
isolates a zero-mean periodic reciprocity kernel and proves exact orthogonality
for two distinct primes over a complete product period. Its terminal-block
identity leaves the entire sum unchanged when the observation length is below
that product. Thus complete-period cancellation alone supplies no short-window
estimate in the balanced prime regime. The source also gives a sharp single-prime
Fourier-energy lower bound and a linear Fourier `ℓ¹` bound without the extra
square-root loss. These are concrete inputs for a future signed average over
primes; no such average or fixed-strip producer follows from the read statements.
This audit does not certify the concurrently edited leaf or retire that route.

The physical-residue Kloosterman carrier preserves the signed modulus sum
exactly (`KloostermanPhysicalResidueModulusBilinear`). Its integer-kernel
operator source proves Cauchy and Hilbert–Schmidt reductions and a scalar
cardinality/totient baseline. The missing spectral estimate remains an
estimate on that signed kernel; neither bookkeeping identity supplies it.
The separate `MRFibreReduction` source requires its averaged short-interval
property explicitly, so it cannot be used as an unconditional source bound.
Both sources were read; no new fixed-strip producer follows from them.

The one-prime Mertens transfer is an exact nonnegative discrete tent, but
its double sum retains the signs of both prime-free Möbius coefficients.
`MobiusMertensPrimeRemovalTentLaw` also proves a negative unit-seed lobe
after removing two primes. Thus entrywise positivity of the one-prime
kernel is not a sign bound on its signed quadratic form, and iterated
prime deletion does not preserve that entrywise positivity. This is an
existing local obstruction with an exact tent-law survivor, not a
retirement of the signed averaging route.

The fresh cofactor-module sources give unit transport from Möbius to Liouville
and a joint-multiplicity formula when the actual limit Hilbert space is finite
dimensional. The latter is an explicit hypothesis; the complete result also
allows continuum Hamel index. Neither source excludes actual escape. In
particular, the finite five-row Vaughan Gram at the trivial power scale cannot
be identified with the complete cofactor Gram normalized by actual receiver
energy. The checked interior energy is `o(T^(1-2ε))`, so the trivial-scale
law alone gives no bound after division by that smaller energy. Its rank-one
law therefore supplies no finite-index or hull-support bound for that module.
The concurrent sources were read, not independently certified here.
