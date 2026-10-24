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
and `Quot.sound`. The pole module is wired into the BVI umbrella; no umbrella was compiled.

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
direct no-olean check remains. Its umbrella import is present. Its proof uses finite
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
for all ten public theorems. Its umbrella import is present; final direct leaf check remains.
Its fixed-Gram dependency is compiled. The paper proof is tracked in
`../2-fully-proven/vaughan-smooth-remainder-and-absolute-budget.md`.

**Moving-cutoff caution.** The existing `sum_moebius_weight_eq_rectangular` already proves
that the both-large remainder vanishes when `T<(U+1)(V+1)`. In particular, at `T=N²`
and `U=V=N` it is identically zero throughout the energy sum. The fixed-cutoff centering
idea therefore cannot be applied at the square-root horizon without uniform estimates
for the growing small-small piece and its signed cross terms. The new fixed-Gram module
also records this exact vanishing, keeping the two limiting regimes distinct.

The dependency-closed structural result and exact restricted no-go are tracked separately in
`../2-fully-proven/vaughan-pole-mass-and-fixed-cutoff-gram.md`. This Q-I card remains in progress.

### Stronger conjecture: uniform leading Gram law

[PROVED HERE on paper; Lean not started] Absolute convergence gives a uniform extension of
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
and internal novelty audit are in `../2-fully-proven/uniform-vaughan-gram-leading-term.md`.
No external novelty is claimed for this specialization of uniform dominated convergence.

## External calibration

Guth–Maynard, [*New large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2405.20552),
states the `30/13` zero-density estimate and `17/30` short-interval consequence. Its stated
density exponent is positive for a fixed `σ<1`; that bound alone does not make the zero count
vanish. The existing corpus already incorporates these results. No external theorem is assumed
in the new pole-calibration proofs.

## Log

- 2026-10-25 — Created after reading the attachment and report, checking the worktree, and
  searching the corpus. Full Q-I remains open.
