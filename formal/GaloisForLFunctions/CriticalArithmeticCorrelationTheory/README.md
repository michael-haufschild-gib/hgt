# Critical Arithmetic Correlation Theory

Namespace `GaloisForLFunctions.CriticalArithmeticCorrelationTheory`; umbrella
`CriticalArithmeticCorrelationTheory.lean`.

## Why this programme exists

The explicit formula identifies the arithmetic source of the Riemann zeta function. Existing
programmes identify its negative index, recover its positive collided metric, classify its
arithmetic gauges, and price individual off-line zeros. What remains is an estimate: the signed
prime correlations must be compared with the archimedean and polar contributions at the scale
where a displaced zero is visible.

Critical Arithmetic Correlation Theory studies that comparison. Its subject is the joint use of
addition, multiplication, reflection, and completion to control actual arithmetic correlations.
The central question is how exact arithmetic identities force a quantitative inequality. Source
identification, a positive replacement form, and a conditional receiver do not answer it.

Three principal targets organize the programme:

1. Control the complete low-energy operator through touching and overlapping test atoms.
2. Bound the signed prime-pair functional entering the critical-line census.
3. Bound the annular increment of completed arithmetic source work without assuming finite
   off-line support.

These targets have different logical strengths. A census estimate can tolerate exceptions. A
finite-index estimate can retain finitely many exceptions. Positivity on an exhausting family
must exclude every exception. Constants and quantifiers must reflect the intended conclusion.

## Objects and language

The primary object is the original completed source, with its literal von Mangoldt coefficients,
Gamma contribution, and both pole moments. It is evaluated on finite families of test functions;
the resulting quadratic forms retain mixed terms and the normalization of each test.

An arithmetic correlation carries its additive shift, multiplicative conductor, support, and
scale. A comparison carries the common energy reserve used to pay its error. A limiting statement
carries the invariant it is meant to preserve: sign, negative index, multiplicity, or a counting
proportion. These data cannot be replaced by an unspecified norm or by convergence of selected
matrix entries.

Useful coordinates include:

- **Prime and residue coordinates:** actual integer dilations, successor maps, congruence classes,
  and the centered discrepancy from a parity-compatible Ramanujan model.
- **Spectral coordinates:** conductor modes, pole constraints, and the exact Schur complement left
  after a positive block is eliminated.
- **Microscopic coordinates:** horizontal displacement and ordinate difference in units of
  `1 / log T`, with multiplicities and reflection divided differences retained.
- **Annular coordinates:** differences between two completed source readings at scales `R` and
  `2R`, keeping every exterior field rather than truncating the interaction to the visible zeros.

The language is that of signed quadratic forms, Fourier and Mellin transforms, arithmetic
correspondences, relative spectra, and estimates uniform in explicitly stated parameters.

## Foundational mechanisms

### Signed comparison before absolute estimates

The prime main term cancels a polar contribution. Parity-compatible singular-series terms can
contribute negative repulsion. Estimating their absolute values separately destroys information
that the desired bound needs. A comparison must first identify the exact signed remainder.

### One reserve for interacting directions

If a complete form has block matrix `[[A, B], [B*, D]]` with positive `D`, the unpaid block is
`A - B D⁻¹ B*`. The same reserve cannot also be assigned independently to every mixed term.
Commuting whole-orbit projections provide another exact mechanism: they remove the cross term
before charging the tail. The arithmetic problem is to extend such control to interacting primes
and the original completed form.

### Reflection without a depth gap

An off-line reflected pair can have arbitrarily small displacement. Ordinary value moments can
identify it with two critical points. Divided differences, horizontal jets, and reflected work
retain information that survives this collision. Their arithmetic upper bounds must pay any
normalization cost as displacement tends to zero.

### Annular subtraction

Let `W(R)` denote `ArithmeticElectrostatics.xiDampedSourceWork R`. Its rational height damping is
`h_R(t) = R⁴ / (R² + t²)²`. Subtracting scales before estimating suppresses the constant contribution
of fixed low zeros while preserving a fixed charge at the height of a new quartet. The task is an
upper estimate on the signed source difference, not another proof of its positive zero-side
representation.

### Limits that preserve the intended invariant

Conductor mass can escape while every fixed resolvent reading converges. A finite collection of
generators still has infinitely many translation levels. Convergence must control the full form
domain, its poles, and its tails; it must be uniform in the parameters needed by the receiver.
Explicit escaping profiles may be part of the limit object.

## Pillar theorems supplied by the surrounding corpus

The following are foundations to use, not new claims of this programme.

| Theorem family | Mathematical content | Source programme |
|---|---|---|
| Ordered Weil–Chebyshev identity | Separated mixed entries are exact centered prime-error integrals with completion | ArithmeticIndexDescent |
| Complete bounded spectral counts | Fixed separated profiles have an exhaustive arithmetic description of bounded spectrum | RenormalizedArithmeticPotentialTheory |
| Whole-orbit dyadic tail | One original Gamma reserve pays every power of the dyadic clock | SignedArithmeticHodgeTheory |
| Parity-compatible stabilizer decomposition | Actual coalescent prime pairs equal their Ramanujan model plus a signed centered discrepancy | TransThresholdPairCorrelation |
| Polynomial-prefix collided metric | Finite arithmetic sources uniformly recover the positive metric on growing normalized families | ConjugateDiagonalGeometry |
| Strict annular quartet quantum | Every off-line quartet forces `W(2|γ|) - W(|γ|) > 39/50` | ArithmeticIndexDescent |
| Finite-support classification | Eventual annular bound by `39/50` is finite support; the bound at every scale is RH | ArithmeticIndexDescent |
| Arithmetic index laws | The complete zeta kernel's index counts distinct right zeros, already on two primes | HeckeKreinToeplitz |

New pillar theorems must add a proved comparison, a quantitative rigidity law, a faithful limiting
tool, or a displacement-sensitive estimate. A restatement of one of these foundations is not a
contribution.

## A source-work comparison theorem

Put `L_R = xiLineTwoLogDerivConstant + log(R+4)`. For every `R ≥ 4`, the actual completed work
satisfies

\[
0\le W(R)\le64R L_R(L_R+1).
\]

Every compactly tapered arithmetic source reading satisfies

\[
|W_N(R)|\le128R L_R(L_R+1)
\]

with the same bound for all taper indices `N`. These are
`xiDampedSourceWork_le_logarithmic_ceiling` and
`abs_xiTaperedSourceWork_le_logarithmic_ceiling` in
[TheCompletedSourceWorkHasALogarithmicCeiling](TheCompletedSourceWorkHasALogarithmicCeiling.lean).

The proof uses the arithmetic Lorentzian mass theorem twice. First, reflection compares each
pair with a unit-width Lorentzian row; its sum is logarithmic in the base height. Second, rational
damping absorbs that height cost into a Lorentzian of width `R`, whose total mass is
`O(log R/R)`. Absolute convergence is established before exchanging the rows. The pole and Gamma
information enters through the completed source identity and the actual log-derivative mass
bound.

This improves the quartic product majorant to `O(R (log R)^2)` and controls the finite arithmetic
readings before the outer cutoff is removed. The estimate is not selective enough to prove finite
exceptions: its positive envelope includes critical zeros. The constant annular target requires
additional signed arithmetic information.

## Questions and tools to develop

**Arithmetic overlap analysis.** What new low modes appear when atom supports touch? Derive and
estimate the complete remaining operator, including pole and Gamma terms. A fixed-ratio theorem
must state whether its horizon is uniform as the ratio changes. The ultimate family must exhaust
the source.

**Mixed prime-action estimates.** Which additive–multiplicative relations allow a joint signed
bound with one energy reserve? Quantify projection and commutator errors. Fixed-prime absolute
costs cannot simply be summed over first prime powers.

**Signed short-difference correlations.** Estimate the actual centered stabilizer discrepancy
with the logarithmic weights and end corrections of its census. The concrete milestones are the
`70%` exchange-rate input and the bandwidth-`4/3` surplus of at most `1/18 + o(1)` for `75%` simple
critical zeros. Model correlations alone do not supply these inequalities.

**Confluent reflection calculus.** Construct observables that distinguish reflected pairs through
coalescence and admit arithmetic upper bounds. Explain their cost at arbitrarily small horizontal
depth. A lower charge with no source estimate leaves the main problem open.

**Quantitative source rigidity.** Convert response information that distinguishes prime gauges
into a completed-form estimate. The error must depend explicitly on conductor and aperture;
fixed precision misses sufficiently remote changes in the prime source.

**Annular arithmetic work.** Establish upper bounds for `W(2R) - W(R)` directly from the completed
arithmetic expression, uniformly as the outer taper is removed. An eventual bound by `39/50`
would imply finite exceptions; the same bound at every `R ≥ 4` would imply RH. The known
classification is an input to research, not an assumption that the bound holds.

**Arithmetic count production.** Find a characteristic-zero mechanism that produces a counting
inequality. Integrality already provides base Chebyshev control; a replacement for the useful
flatness of Frobenius must earn its quadratic estimate. A structure with the desired inequality
as a field would only rename the missing theorem.

## Traps and calibration

The maximal prime gap does not identify zeta: remote prime flips share it. Haar-almost-everywhere
cancellation does not select the actual Möbius gauge. A compact negative perturbation need not
have finite negative index when the positive spectrum approaches zero. Density bounds need not
exclude a single zero. Finite heat counts at each positive time need not be uniformly bounded
near zero. Low-profile positivity does not exclude undiscovered modes unless the spectral count
is exhaustive.

Calibration must match the proposed theorem. Liouville, remote prime flips, small weight changes,
and impure geometric models test different assumptions. A theorem deciding RH must use an
assumption that fails on every applicable countermodel. A statistical theorem need not exclude
every finite exceptional configuration.

## Place among the programmes

ArithmeticCastelnuovoSeveri and ArithmeticOrientationGeometry provide the geometric and index
languages. ArithmeticIndexDescent and SignedArithmeticHodgeTheory expose paid blocks and the
remaining complete source. RenormalizedArithmeticPotentialTheory resolves the separated
arithmetic spectrum. TransThresholdPairCorrelation and ShallowCauchyPrimeEnergy provide census
receivers and collision costs. ConjugateDiagonalGeometry supplies source-built positive metrics.
ArithmeticCountingPositivity and ArithmeticCorrelationGeometry explain source selection and its
limits. ArithmeticEffectivityTheory supplies count mechanisms and their current boundary.

This programme connects those tools through quantitative signed comparison. It does not replace
their objects by an abstract positivity axiom. An estimate should carry enough original-source
data to be usable by more than one of these neighbouring languages when a proved transfer exists.

## Success and contribution criteria

A contribution must identify the actual object, prove its estimate or classification without an
unproved analytic premise, preserve the relevant completion and multiplicity, and state all
uniformity and error dependence. It must locate the improvement over existing corpus results.
If a proposed mechanism fails, its sharp boundary or strongest positive survivor must be extracted
and proved.

The programme succeeds through new arithmetic estimates: an overlapping-family sign bound, a
census improvement with its constant, a finite-index bound, or an exclusion estimate that closes
an individual-zero argument. Foundational definitions and exact identities are useful only as
steps toward these tools. The questions above remain research obligations until the corresponding
unconditional theorems have been formalized.
