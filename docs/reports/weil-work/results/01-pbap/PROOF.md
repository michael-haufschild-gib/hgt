# Exact null repair and the scalarization question

## Proved bridge: positive correction at every integer

Write T(f) for the existing `logVector f`, A(f) for `weilArchRe (EF.weilTest f f)`, and

    w(j) = 2 (∫ narrowBump(j,t)² dt) / √j > 0.

The existing pair tests p(j,±) are smooth compactly supported functions and satisfy T(p(j,±)) = ±w(j)e_j. For a real number b define

    R_j(b) = (|b|/w(j)) [p(j,sign(b))],

choosing the positive sign at b=0. These are nonnegative finitely supported mixtures. Directly, T(R_j(b)) = b e_j. Let

    D(j) = max(|A(p(j,+))|, |A(p(j,−))|)/w(j).

Then |A(R_j(b))| ≤ |b| D(j). For finitely supported b put R(b)=Σ_j R_j(b_j). Its coefficients are nonnegative, T(R(b))=b, and

    |A(R(b))| ≤ Σ_j |b_j| D(j).

All sums here are finite, including the integer-indexed defect of every finite mixture. Consequently every nonnegative mixture c has the exact nonnegative repair

    c° = c + R(−T(c)),

with T(c°)=0 at **every** integer ≥2 and

    |A(c°)−A(c)| ≤ Σ_j |T(c)_j| D(j).

Proof: positivity follows termwise; linearity gives T(c°)=T(c)−T(c); linearity and the triangle inequality give the energy bound. No positivity theorem for A is assumed. The correction keeps the full pole terms through the literal A. Thus small weighted total defect, unlike a small unchecked prefix, gives a controlled exact repair.

This is an extraction of the atom-correction mechanism already used in `WeilPositivityPrimeBlindDuality.exists_weilPositiveUpTo_of_primeBlindPositive`. Verdict: **BRIDGE**, not a novel scientific result or PBAP proof.

## Conjecture under audit: no finite-mixture obstruction beyond scalar smooth tests

Proposed precise statement: full C² PBAP is equivalent to nonnegativity of the full functional on every compactly supported smooth complex scalar test whose symmetric autocorrelation vanishes at every integer logarithm.

Reason to investigate: the old L382 note allows a cone-versus-variety gap. On the real line, Boas–Kac–Krein factorization represents each compactly supported positive-definite correlation by one compactly supported L² factor. For a smooth correlation obtained from smooth tests, rapid decay of its nonnegative Fourier transform would make that factor smooth as well: |F|²=H and rapid decay of H imply integrability of t^k F for every k, hence smoothness by Fourier inversion. Equality of correlations preserves every null constraint and both polar evaluations.

### Paper argument for the smooth approximation step

For a fixed finite mixture c, convolve each of its finitely many tests with a nonnegative C∞ approximate identity supported in [−ε,ε], with ε≤1. All approximants have support in one fixed compact interval and converge in C². Their Fourier transforms converge pointwise and obey one common bound C min(1,|t|⁻²), obtained by integrating by parts twice. Thus their squared Fourier transforms times the gamma weight are dominated by an integrable multiple of min(1,|t|⁻⁴)log(2+|t|). Dominated convergence gives convergence of the archimedean energy. Compact support and uniform convergence give convergence of the two exponential pole moments and each logarithmic autocorrelation sample.

Only finitely many integer samples can be nonzero on the common support. Therefore the repair budget of the smoothed mixture tends to zero. Add the positive repair above; its pair tests are C∞, so the repaired mixtures are smooth, remain nonnegative mixtures, satisfy every null constraint exactly, and converge in full energy to c. This proves that positivity on smooth null mixtures implies positivity on C² null mixtures. The reverse inclusion is immediate.

### Paper argument for compression of a smooth mixture

Let Φ be the sum of the autocorrelations of its finitely many smooth tests, including their nonnegative coefficients. It is compactly supported, smooth and positive definite. Boas–Kac–Krein gives a compactly supported complex L² function g with Φ=g*ĝ, where ĝ(x)=conj(g(−x)). On the real Fourier axis, |F(g)|²=F(Φ). The latter is a nonnegative Schwartz function. Hence |t|^k F(g)(t) is integrable for every nonnegative integer k, so inverse Fourier differentiation gives a smooth representative of g. This representative remains compactly supported, since it agrees almost everywhere with the compactly supported L² factor. Equality of autocorrelations is pointwise by continuity. It preserves every symmetric logarithmic sample and the entire pole-plus-archimedean functional. Thus one scalar smooth null test has exactly the same energy as the smooth mixture.

The combined equivalence has a paper proof using the classical one-dimensional factorization theorem and standard smooth approximation/Fourier inversion. **Lean status of this equivalence:** exact finite repair is formalized. Factorization, approximation, and their full-functional bridges remain unformalized here. No Lean scalarization theorem is claimed.

Exhaustive text search subsequently located the single-function reduction already stated in the corpus at `krein-producer-loops.md:4968` (L248). Thus scalarization is **REDISCOVERED**, not a new conjecture beyond the corpus. The smooth exact-repair details above clarify regularity, but do not turn it into new scientific knowledge. The later L382 rank-gap remark must be read against this earlier factorization result. Next research must address the actual scalar energy sign, not rank reduction.

## Other conjecture audits

- Universal positivity from finitely many null nodes: excluded as a source of PBAP by existing sparse-producer obstruction and duality; do not repackage it as new research.
- Polar positivity implies full positivity for arbitrary weights: no closing theorem located. Conditional positivity leaves exponential homogeneous terms; fixing their coefficient is an unpaid issue. No implication is used here.
- Two-cluster Poisson estimate plus a total-mass window bound: existing L390 already identifies the lost frequency resolution. Do not claim the anti-concentration theorem alone closes that sector.

## Proved finite Gram realization

The dependency-closed paper proof is the section “Exact finite realization” in `TORUS-DENSITY.md`. For a PSD matrix A on labels 1..N, factor A as B*B and put conjugated rows of B on translated narrow bumps. Expanding autocorrelations gives matrix entries times shifted bump autocorrelations. At `log a - log b`, every unwanted argument is `log(a*k)-log(b*j)` for unequal positive integers with `b*j <= N*L`; the corpus log-gap bound exceeds the bump autocorrelation radius. Only `a*k=b*j` survives.

If the divisibility traces for integers 2..N vanish, this yields every positive integer null; indices above N have no surviving pair. Hermitian symmetry then yields the negative samples. Unit Finsupp weights on the realized family give the literal WP01 nonnegative mixture, including repeated tests, and the sample at zero gives `packetMass * trace(A)`. These conclusions are compiled in `WeilWorkPBAPGramPackets.lean`; they assume no sign theorem for the Weil energy. The broader measure-level density construction is a separate remaining obligation.

## Proved normalized representing-measure realization

The closed paper argument is in the section “Representing-measure connection” of `TORUS-DENSITY.md`. The corpus's `UnitAddTorus Nat.Primes` and `torusCharacter` supply the continuous integer monomials. For an origin-representing probability measure mu and coefficients d, the matrix is the actual integral Gram of `d_j chi_j`. Existing `complexFeatureGram_posSemidef` proves positivity because continuous products on the compact torus are integrable. Unique prime factorization identifies the character on every rational fibre; nontrivial divisible fibres vanish by the representing identities. The trace is `sum |d_j|^2`.

For a unit coefficient profile, apply the verified null-packet theorem and multiply its Finsupp weights by `packetMass(N,L+1)^{-1}`. Positivity of packet mass preserves nonnegative weights; linearity preserves every integer-null identity; the trace formula gives mass exactly one. Every rational sample is exactly `M_mu(a,b) * packetCoeffCorrelation(d,a,b)`. This full statement is compiled as `exists_normalized_representing_mixture` in `WeilWorkPBAPMomentPackets.lean`. It does not yet assert that the coefficient correlation converges to one or control the full Weil energy.

## Necessary critical gamma coefficient

The separate dependency-closed proof in [CRITICAL-SLOPE.md](CRITICAL-SLOPE.md) establishes: for every `0<=a<b` and every real mass correction `C`, an actual nonnegative smooth finite integer-null mixture has `a Gamma+b Pole+C Mass<0`. Equivalently, its uncorrected energy is unbounded below on the mass-one null cone. Generic algebraic null-cone duality, exact polar resonators, primitive-set summability, translated Gram positivity and signed Abel/Fubini discharge every analytic premise in the final witness. Ten targeted leaf builds, ten final direct-source audits and 22 axiom checks pass; exact outcomes are recorded in `EVIDENCE.md`.

The positive structural survivor is the necessary coefficient boundary `b<=a` for any positive modified completion. The actual PBAP datum `a=b=1,C=0` lies on the unresolved boundary. The proof's residue comparison loses `C`, so it cannot prove its required zero-slack normalization.

## Literal broad-profile energy escape

The full dependency-closed argument is in [JOINT-PHASE-COST.md](JOINT-PHASE-COST.md). The exact paired Fourier density has total normalized mass 2m. Logarithmic submultiplicativity and the corpus gamma lower bound give the pointwise full-mass inequality. Actual gamma integrability dominates the base log moment J, so translation-invariant integration yields Gamma(pair,T)>=2m log(2+|T|)-2m(10+log4)-4J. Opposite exponential L1 weights control both signed poles without replacing their product by the square of the larger weight.

The resulting explicit constant C is nonnegative and independent of modulation T. Summing with actual nonnegative Finsupp weights, including collisions, gives E(c)>=E0+2m sum w log(2+|t|)-C sum w. Two real-active nodes force beta nonzero and supply the already audited actual-real-null logarithmic escape. Shrinking delta below 1 bounds correction mass by 2, giving energy escape. Actual physical mass equals 2m(1+sum w), lies between 2m and 6m, and therefore preserves escape under normalization. The capstones are `joint_actual_null_energy_escape` and `joint_actual_null_normalized_energy_escape` in `WeilWorkPBAPJointEnergyEscape.lean`.

All three analytic leaves pass targeted builds, final direct-source audits and 24 standard-axiom checks. This is a fixed-profile boundary theorem, not full PBAP positivity. The next core remains simultaneous-constraint full-energy control away from mass one and a justified passage to the full null cone.

## Proved negative-seed positive sector

[JOINT-WIDTH-SECTOR.md](JOINT-WIDTH-SECTOR.md) supplies the closed proof for
the actual explicit unit bump at W=kappa*L*exp(-L/2). Its seed energy is
negative, but a nearest-integer all-frequency cosine certificate forces
positive full energy for every actual real-null correction, with margin
L/16 times physical mass. The sector is nonempty at every correction mass
M>1 for each sufficiently large prime half-logarithm. Eight targeted leaf
builds, eight final direct-source audits and 66 standard-axiom checks pass;
see EVIDENCE. This restricted sector does not span the full null cone.

The next completed paper argument is
[JOINT-ONE-NODE-BOUNDARY.md](JOINT-ONE-NODE-BOUNDARY.md). It identifies the
nearest-node critical width and a stronger positive sector below it.
Its four supporting leaves now formally establish the exact-mass upper
bound, quantitative pole remainder, uniform full seed expansion and actual
prime half-log phase scale. All four targeted/final audits and twenty axiom
checks pass. The three-band classification is now formalized in six further
leaves, with 26 public standard-only axiom checks.

The two uniform bridges in `WeilWorkPBAPJointUniformHigh` and
`WeilWorkPBAPJointBoundarySeed` are now formalized and directly audited.
They retain coefficient2 in high-frequency logarithmic energy and bounded
seed error after centering by `-2s+2(d-1)log L`, uniformly in the complete
lag range. The actual-prime seed capstone pays the arithmetic lag bounds.
All fifteen public axiom checks use standard Lean axioms only. The opposite-
phase obstruction and positive three-band capstones are complete. For d<1,
the actual opposite-phase energy sum is negative, ruling out every single
nearest-node cosine coefficient. For d>1, the explicit coefficient gives
margin `(d-1)log L/2` in source-mass units at every real frequency. Actual
nearest-node activity cancels this coefficient in every real integer-null
correction. The resulting full-energy margin is `(d-1)log L/4` times physical
mass; exact corrections make the sector nonempty at every M>1. The seed
itself remains negative. All source signs, width geometry and phase bounds
are derived for the literal unit-bump/prime family. The exact d=1 point,
many-node certificates outside this family, and full PBAP remain open in Lean.

## Many-node extension: paper proof and first formal component

[JOINT-MANY-NODE-CERTIFICATE.md](JOINT-MANY-NODE-CERTIFICATE.md) gives the
dependency-closed MC2/MC3/MC4 arguments. Actual short-prefix length, signed
Abel variation and integer quadrature are essential; the derivative test is
classical and already present in the corpus. Scientific novelty is unestablished.
The continuous component for nonnegative real autocorrelation is now proved
in `WeilWorkPBAPJointContinuousCertificate`. Its positive modulation kernel
dominates the exact leading pole coefficient, while the cosine transform is
the sum of two actual squared source integrals. This proves the continuous
certificate without a positivity input. `JointGammaFloor` and
`JointSignedCertificate` now remove the source-correlation sign condition
from the continuous estimate: exact mass pays the Gamma logarithm and
absolute correlation mass pays the uniform quartic pole error. All four
new leaves, including the explicit short-prefix/Abel bridge, are audited.
The discrete capstones remain unformalized; full PBAP remains OPEN.

The stronger MC6 paper proof is in
[JOINT-UNIFORM-PROFILE-CERTIFICATE.md](JOINT-UNIFORM-PROFILE-CERTIFICATE.md).
Its fixed cutoff moves every derivative onto an auxiliary smooth family,
leaving source-uniform Fourier density and mass bounds. Both source
profiles may vary independently. The same global coefficient system is
indefinite by the corpus semiprime-floor theorem, so only the exact local
restriction and its aggregate-null consequence are positive survivors.
MC6 formalization is the next obligation; its no-go card stays in progress.

`JointSourceBudget` now pays the source-uniform part in Lean: for support
[0,W], `(integral |f|)^2<=W*mass(f)` and `|F_f(t)|^2<=W*mass(f)`.
The integrated fixed log deficit costs at most `mass(f)*integral H`,
giving the explicit Gamma floor with leading term `-mass(f)*log W`.
Eight public theorems are fully audited. Complex quadrature, uniform
growing-order bands and the literal two-source/null capstones remain.
The same paper records MC7, which keeps the extreme pair intact and pays
every shorter pair to allow order D/log D separate narrow windows. Its
derivation is a bridge from MC6; no unrestricted many-window sign follows.

`JointLogQuadrature` now proves the complex quadrature and actual cutoff
Abel variation in Lean, including the logarithmic change of variables.
Seven public theorem audits pass. Remaining steps are actual endpoint/phase
budgets, growing-order band gluing
and literal cross-energy/null identities. MC8 improves the paper's
many-window extension by summing geometric rows instead of multiplying
by window count; its sharper spacing still does not cover general support.

`JointFixedCutoff` now pays the fixed-cutoff obligation, including an actual
even plateau, uniform C1/C2 bounds, its exact leading integral with error
at most `4e W^2`, and inverse-square decay of the complex Fourier integral.
All 28 public theorems pass source/axiom audits. The paper replaces separate
middle-frequency bands by ratio-bounded window landing for `4^k lambda_k`.
The three uniform schedule inequalities and actual cross-energy/null
capstones remain to be formalized. The explicit endpoint budget pays three
rounding/padding units, giving length at most `(4e+3)NW`.

`JointGridGeometry` formalizes those endpoint bounds for the actual width
`b L log log L exp(-L/2)`, for every b>0 and all sufficiently large L.
It also proves that the logarithmic endpoints enclose [-2W,2W]. Its six
public theorem audits pass.

`JointGrowingOrder` now pays all three order-selection inequalities,
including the growing factorial cost, throughout the literal middle band.
Every short prefix has the explicit saving
`exp(-(log L)^(1-c log2)/16)`. Its nine public theorem audits pass. The
all-frequency gluing and cross-energy/null capstones remain open; the phase
theorem itself assumes no numerical budget.

`JointMiddleCutoff` pays the actual cutoff weights and both frequency
signs, bounds the full complex grid-minus-integral error, and supplies an
eventually nonnegative o(L) loss after multiplication by the exact
`2 cosh(L/2)` pole factor. All eleven public source/axiom audits pass.
`JointGridFrequency` also passes all twelve public audits. It pays the full
complex quadrature and low-frequency o(L) loss, preserves the exact Apsi
in the high envelope, and leaves 3L/4 against log|t| above the actual growing
ceiling. Its global finite error bound supports subsequent integration.
`JointSymbolFloor` pays Gamma-deficit gluing and source integration, including
error continuity and integrability. Its nine public audits pass. The exact
corrected symbol leaves L/3 times total physical mass for two independent
sources, with a threshold independent of their shapes. The numerical condition
is discharged for b=1/(8 log2). Source-energy and null identities remain open.
