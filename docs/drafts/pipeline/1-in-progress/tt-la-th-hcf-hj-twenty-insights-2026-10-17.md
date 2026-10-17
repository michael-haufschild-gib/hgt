# Twenty cross-route insights: TT / LA / TH / HCF / HJ

Current scope: the full twenty-insight goal was cleared. The user's subsequent
request to finish the fourth package is complete: four contribution packages,
113 audited declarations, and eleven Lean modules are preserved. No claim of
twenty completed insights is made.

## Contract

User task: attachment `277aa2d6-28d3-4b7c-aca7-800d9e29a1ca/pasted-text-1.txt`.
Find 20 significant insights combining frontier theorems from multiple routes,
each advancing TT, LA, TH, HCF, or HJ directly or indirectly. A new wrapper,
restatement of an RH equivalence, or routine lemma does not earn insight credit.

Use current local Lean sources and corpus search. No external search, numerical
experiments, or external novelty audit. Frontier map is read-only. Prove exact
claims on paper before Lean. No unproved premises, added axioms, heartbeat
increases, full builds, or umbrella builds. Check individual modules in the
foreground, reuse unchanged dependencies with `--old`, wire finished modules,
audit axioms from `/tmp`, run formal lint, and remove owned temporary artifacts.

## Plan

1. Inspect current route interfaces and search the entire indexed Lean corpus.
2. Form falsifiable cross-route conjectures; reject circular and routine claims.
3. Complete dependency-closed proofs, including positive survivors of no-go results.
4. Formalize and audit each significant result; update exact count and evidence.
5. Repeat until all 20 contributions meet the contract.

`update_plan` is unavailable in this tool session; this file tracks the plan.
Serena symbol access rejects the ignored Lean tree; use exact source reads and
patches after that observed failure. `docs/architecture.md` and `docs/testing.md`
were absent from the initial file inventory.

## Current investigation

Question: can the literal Hurwitz reflection residual quantify negative heat
moment directions, rather than merely share their RH-equivalent zero locus?

Inputs inspected:

- `PrimeTailSeedHurwitzReflection.lean`: literal co-Poisson residual and first-prime
  seam have the same open-strip zero locus.
- `XiGaussianHeatRouteCapstone.lean`: exact heat/Hankel receivers at one positive
  time; source orientation remains unproved.
- `XiGaussianHeatRegularKernelProjections.lean`: mutually orthogonal signed
  reproducing block kernels, including singular gaps.

## Conjecture 1: two prime-log heat grids survive arbitrary finite prefixes

For any integers K,L >= 0, put
`s_(h,K)(n) = nu((2K+1+n)h)`, where `nu` is the literal Xi heat trace.
Conjecture: RH iff both complete Hankel forms of `s_(log 2,K)` and
`s_(log 3,L)` are positive semidefinite.

Attack: the direct Hurwitz/heat seam equivalence is already present in
`HeatAperturePrimeSeamReflection.lean`; reject it as a contribution.
A single exponential sampling grid aliases spectral frequencies modulo
`2 pi i / h`; no claim that one grid determines reality. Two prime-log grids
eliminate this exact obstruction. Existing corpus searches did not return this
two-grid heat receiver. No external novelty claim is made.

### Dependency-closed paper proof

Write `w_q = z_q^2` for the actual squared Xi spectral points and
`lambda_q(h) = exp(-h w_q)`. For h>0 these are nonzero, absolutely summable,
and tend to zero off finite sets (`summable_xiGaussianHeatTerm`). Finite
polynomial expansion and absolute convergence identify the Hankel functional
on p^2 with
`Re sum_q lambda_q(h)^(2K+1) p(lambda_q(h))^2`.
This is exactly the trace-Hankel form on the principal ideal `X^K`, since
`lambda^(2K+1) p(lambda)^2 = lambda (lambda^K p(lambda))^2`.

The corpus theorem
`traceHankel_nonnegative_on_principalIdeal_implies_real` applies: `X^K` cannot
vanish at any exponential node. Thus positivity on the h-grid forces every
`exp(-h w_q)` to be real. Equality with its complex conjugate implies
`exp(-2 i h Im(w_q)) = 1`. Applying this at h=log 2 and h=log 3,
`primeLogPhaseClockPair_two_three_injective` forces `Im(w_q)=0`.
The established height gap (`xiSpectralSq_im_ne_zero_of_im_ne_zero`) then
forces every z_q real, hence RH. Conversely, under RH all lambda_q(h) are
strictly positive real, so every term in each polynomial-square form is
nonnegative. This proves the exact equivalence without any sign premise left
unproved in the theorem.

Sources combined: HCF actual heat trace and spectral shell laws; TH/LA
trace-Hankel principal-ideal separation; prime-log phase injectivity. HJ will
receive the exact sampled criterion through its literal reflection residual,
without counting that corollary as a separate insight.

All four modules passed their narrow `:olean` builds and final individual
`lake env lean` audits without warnings in these modules. All 37 public
declarations were audited with `#print axioms` in a temporary file: only
`propext`, `Classical.choice`, and `Quot.sound` occur. All four imports are
wired into `RHTower.lean`; index refresh and `git diff --check` passed.
Repository lint exited 1 on 31 unrelated modules missing umbrella imports
(OddSector, Bernstein, and HTGeometry work from concurrent agents). No lint
error concerns these four modules. This is a repository gate limitation,
not a claim that repository lint passed.
Principal-ideal separation imports a general theorem
with hypotheses; all its hypotheses above are proved for the actual Xi source.

### Arithmetic source strengthening (same contribution)

Let `A(t) = Re(gaussianArchCriticalC(t)-gaussianPrimeChirpC(t))/pi`.
The existing exact source formula gives `A(t)=nu(t)-2 exp(t/4)`.
At grid h with offset 2K+1, set alpha=exp(h/4). For every real polynomial p,
the sampled source functional is the heat functional minus
`2 alpha^(2K+1) p(alpha)`. Therefore their square forms agree on p(alpha)=0.
Applying principal-ideal separation to `X^K (X-alpha)` still excludes every
nonreal exponential node: this generator has only real roots. The two-grid
proof consequently works with source positivity restricted to the two pole
hyperplanes. This gives a derivative-free arithmetic-source criterion and
the exact literal HJ reflection-residual criterion. These are parts of the
same contribution, not extra count.

### Exact one-grid obstruction (same contribution)

For any h>0 choose b=2pi/h, a=1+b^2, and w=a+ib. Then w is nonreal,
`(Im w)^2 < Re w`, and the conjugate-pair heat trace
`T(t)=exp(-tw)+exp(-t conjugate(w))` has
`T(nh)=2 exp(-nha)` for every natural n, including all discarded-prefix
Hankel moments. Thus every sampled Hankel form is nonnegative, exactly as
for a positive real one-atom source. Yet `T(h/2)=-2 exp(-ha/2)<0`.
This kills a universal one-grid replacement even inside the natural parabolic
spectral region. It is an abstract spectral countermodel, not a claim about
actual Xi zeros. The two-grid theorem is its positive survivor.

### Finite-offset conjecture and obstruction (same contribution)

Conjecture: finitely many independently chosen offsets of one grid might
replace two incommensurate grid steps. Verdict: FALSE for the abstract
parabolic spectral class.

For offsets tau_i and grid h, simultaneous integer approximation supplies
arbitrarily large integers n for which each `2 pi n tau_i/h` lies within 1
of an integral multiple of 2pi. Hence all cosines are at least 1/2. Take
the preceding countermodel with smaller step delta=h/n. On every entire
offset grid its trace is exactly
`2 exp(-a tau_i) cos(2 pi n tau_i/h) (exp(-a h))^m`.
Each coefficient is strictly positive, so each complete Hankel form is
positive semidefinite. The same trace remains strictly negative at delta/2.
This preserves arbitrarily high alias frequencies and all ranks at every
finite collection of offsets. The positive survivor remains the exact
two-incommensurate-grid source theorem, rather than more offsets.

Imported recurrence: `exists_fin_simultaneous_integer_approximation_of_lt`
and `one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real` in
`CCMPrimePoleFiniteCoherence.lean`. Full-corpus recurrence search returned
complete retrieval; both candidates were verified in this toolchain and the
finite-offset theorem passed its final Lean audit.

## Verified contribution count

3 / 20. Contributions:

1. Exact two-prime sampled heat/source criterion with sharp single-grid and
   finite-offset obstruction (37 declarations; corollaries not separate credit).
2. Exact marginal-versus-mixed sampling boundary: two separate heat grids
   fail reconstruction even for strict-parabolic four-atom packets; mixed
   prime-log samples determine arbitrary heat-regularized summable countable
   packets on distinct escaping frequencies (18 declarations).
3. FE parity transport preserves the entire Weil form: the Deninger
   orientation isometry moves the Hurwitz witness into the even sector with
   unchanged energy, while the original witness has an exact approximation
   distance from every even vector (24 declarations).

The remaining all-rank arithmetic positivity is open; RH is not proved.

## Contribution 2: marginal ambiguity and mixed recovery

Does equality of all heat-trace values on two prime-log grids reconstruct a
spectral packet? Individual phase pairs are injective, but the two trace
sequences supply unpaired marginals. A rectangle switch between imaginary
frequencies `{0,L1+L2}` and `{L1,L2}`, with `Li=2*pi/hi`, appears to preserve
both grid traces. Audit conjugate closure and the Xi parabola, then extract
the strongest positive recovery theorem from mixed samples. This conjecture
was refuted and replaced by the mixed recovery theorem below.

### Paper proof: marginal ambiguity and finite mixed recovery

For arbitrary positive steps h,k put a=2*pi/h, b=2*pi/k and
A=1+(a+b)^2. Compare the conjugation-closed packets, including multiplicity,
`{A,A,A+i(a+b),A-i(a+b)}` and `{A+ia,A-ia,A+ib,A-ib}`.
Their heat traces are respectively
`F(t)=2 exp(-At)(1+cos((a+b)t))` and
`G(t)=2 exp(-At)(cos(at)+cos(bt))`.
Every frequency satisfies Im(w)^2<Re(w), since a,b>0. On t=nh,
at=2*pi*n, so cosine addition gives F(t)=G(t); on t=nk the same
argument uses bt=2*pi*n. At t*=2*pi/(a+b)>0, however,
F(t*)=4 exp(-At*) while G(t*)=4 exp(-At*)cos(a*t*).
Since 0<a*t*<2*pi, cosine is strictly below one. The packets therefore
have distinct full traces despite agreement on both entire marginal grids.
This works for h=log2,k=log3 and is not a counterexample about actual Xi.

The positive survivor is exact finite spectral recovery from mixed samples
at `t0+m log(p)+n log(q)`, for distinct primes p,q. The paired map
`z -> (exp(-log(p)z),exp(-log(q)z))` is injective: equality first fixes
Re(z) by taking norms; subtracting points gives exponentials equal to one,
and two-prime phase injectivity fixes the imaginary part. For a finite
set S of distinct complex frequencies and coefficient differences c_z,
vanishing mixed samples say
`sum_S c_z exp(-t0*z) x_z^m y_z^n=0` for all m,n>=0.
Linearity extends this to every bivariate complex polynomial. The existing
finite multivariate CRT, with point-ideal powers one, supplies a polynomial
taking value one at any selected paired point and zero at all others.
Testing it gives `c_z exp(-t0*z)=0`; exponential nonvanishing gives c_z=0.
Thus the mixed sampling map is injective for arbitrary complex weights on
every finite support and every real initial offset. Comparing two packets
uses their union support, so their spectra and multiplicities agree.

This proof uses no positivity assumption or unknown source premise.
It combines the prime phase theorem, finite Hermite CRT, and heat packet
encoding. Corpus retrieval was complete but compiler coverage partial;
each imported candidate will be checked by Lean. An infinite packet
extension requires a separate localization argument.

### Stronger survivor: countable mixed-moment determinacy

For sequences x_j,y_j tending to zero, assume the paired points are distinct
and no pair is (0,0). Exclude the countably many complex slopes
`-x_j/y_j` and `(x_l-x_j)/(y_j-y_l)`. Any remaining slope r makes
`z_j=x_j+r*y_j` nonzero and injective; cases with zero denominator are
settled directly by the paired assumptions. The z_j still tend to zero.
For absolutely summable complex weights c_j, all mixed moments converge
because x and y are bounded. If they vanish, binomial expansion and finite
sum interchange show every positive power moment of z vanishes. Apply
`coeff_eq_zero_of_atomicMoments_vanish` from `AtomicMomentDeterminacy.lean`:
all c_j vanish. This upgrades finite recovery to countable recovery without
requiring either marginal coordinate to be injective. The nonconstructive
slope is used only in the proof; the observed data remain the original
nonnegative mixed powers.

For distinct frequencies w_j with Re(w_j) tending to infinity, positive
prime-log heat coordinates tend to zero and are jointly injective. Thus
the theorem applies to every summable coefficient sequence, and to any
heat-regularized packet whose regularized coefficients are summable.
No RH, spectral reality, or sign assumption is needed. This is the positive
survivor, stronger than the finite CRT version above.

### Contribution 2 audit

`HeatGridMarginalAmbiguity.lean` and `HeatMixedMomentDeterminacy.lean` passed
narrow `:olean` builds and final separate `lake env lean` audits without
warnings. All 18 public declarations were checked with `#print axioms`:
only `propext`, `Classical.choice`, and `Quot.sound`. Both imports are wired;
index refresh passed. Latest repository lint exited 1 on 22 unrelated
unreachable OddSector and HTGeometry modules; none belongs to this work.
No external novelty claim is made. The countable scalar projection and
mixed-moment argument provide the new positive recovery mechanism; the
counterexample and its finite specializations remain one contribution.

## Contribution 3: parity transport of the Weil obstruction

The Deninger FE orientation multiplier has modulus one, reverses pure
functional-equation parity, and should commute with critical-line reflection
because the centered spectral real coordinate never vanishes. Therefore it
should give an isometric equivalence of the even and odd FE Weil sectors.
The Hurwitz orientation vector is FE-odd; multiplying by this orientation
should produce an FE-even negative witness with exactly the same energy.
The corpus audit and formal proof are complete below.

### Dependency-closed paper proof of parity transport

Write R for the exact-copy functional-equation permutation, J for the
critical-line permutation, and z_q for the centered spectral point. The
existing source height gap gives |Re z_q|>4. Hence Deninger's orientation
epsilon_q is sign(Re z_q), always real with epsilon_q^2=1. Since
z_(Rq)=-z_q and z_(Jq)=conj(z_q), epsilon_(Rq)=-epsilon_q and
epsilon_(Jq)=epsilon_q. Thus Dv(q)=epsilon_q*v(q) defines an involutive
linear isometry of the complete multiplicity-exact ell2 carrier and
commutes with J. Consequently its full Weil form is invariant:
`<J Dv,Dw>=<D Jv,Dw>=<Jv,w>`.

If v(Rq)=s*v(q), then Dv(Rq)=-s*Dv(q). D therefore identifies the two
functional-equation parity sectors isometrically, preserving every Weil
Gram matrix and its sign, for arbitrary complex coefficients. This is
different from J-parity, whose two sectors already have opposite signs.

The canonical Hurwitz vector u has coordinate
`-sin(2*pi*Re rho)/|rho-1/2|`. Under rho->1-rho its denominator is fixed
and sine changes sign, so Ru=-u. Hence Du is FE-even, has norm squared E
(the Hurwitz orientation energy), and has Weil square exactly -E. Positivity
at this one FE-even vector is equivalent to RH by the existing E=0 criterion.
Thus square folding does not remove the full RH obstruction: orientation
transport relocates it with no energy loss.

For every FE-even v, reindexing the absolutely convergent Hilbert pairing
through R gives `<u,v>=-<u,v>`, hence zero. Pythagoras gives the sharp law
`||u-v||^2=E+||v||^2`. Raw FE-even heat vectors therefore cannot approximate
the original u unless RH holds, despite the existence of the equally strong
even witness Du. This records the precise limitation and its positive repair.

Corpus search returned complete retrieval. Existing graded orientation
equivalence in `DeningerArithmeticRealHodgeFactorization.lean` factors odd
Hodge transport; existing `GaussHodgeWeilFundamentalSymmetry.lean` concerns
J-parity rather than pure FE parity. `XiWeilSpectralFoldIndexConservation`
counts conjugation-fold source orbits and does not assert this FE-sector
unitary equivalence. The new claim is the Hilbert parity transport and its
canonical Hurwitz energy/approximation consequences, not those parent laws.

### Contribution 3 audit

`XiWeilFunctionalEquationParity.lean` and
`XiHurwitzFunctionalEquationEvenWitness.lean` passed both narrow `:olean`
builds and final individual `lake env lean` audits, without warnings in these
modules. All 24 public declarations were audited with `#print axioms`:
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports and
index refresh passed. Latest repository lint exited 1 on 26 unrelated
unreachable modules from concurrent OddSector, EvenSector, and HTGeometry
work. No lint error concerns any of the eight modules in contributions 1–3.
Total audited declarations: 79; contribution count remains three.

## Contribution 4: uniform signed-heat construction of FE orientation

This package counts as one contribution. Prior corpus search found real Hermitian
signed-heat formulas in `RiemannGaussian/Hybrid/SignedHeatInertia.lean`, real
finite-gap formulas in `EtaEnergyFiniteWindowHeatHilbert.lean`, and the
first reciprocal-square Mellin bridge in `XiGaussianMellinBridge.lean`.
The new target is the actual complex Xi spectrum and strong convergence
on its full multiplicity-exact Hilbert carrier, without RH.

### Dependency-closed paper proof

For Re(z^2)>0 let g_z(t)=exp(-z^2*t^2). Complex Gaussian integration gives
`I(z)=integral_R g_z=(pi/z^2)^(1/2)`. When Re(z)>0, the number sqrt(pi)/z
has positive real part and square pi/z^2, so the principal square-root law
gives I(z)=sqrt(pi)/z. When Re(z)<0, apply this to -z and use g_(-z)=g_z.
Thus `z I(z)/sqrt(pi)=sign(Re z)` on both spectral sectors. The actual Xi
source satisfies Re(z_q^2)>0 and |Re z_q|>4, so this is exactly Deninger's
orientation epsilon_q.

For any measurable window S define
`a_S(z)=z/sqrt(pi) * integral_S g_z`.
The norm integral bound and the real Gaussian integral yield
`|a_S(z)| <= |z|/sqrt(Re(z^2))`. The already proved Xi sector inequality
`|z_q|^2 < 2 Re(z_q^2)` gives the uniform bound |a_S(z_q)|<=2,
independent of the window and spectral copy. For S_N=[-N,N], integrability
and increasing exhaustion give a_N(z_q)->epsilon_q.

For each v in ell2 define A_N v(q)=a_N(z_q)v(q). The uniform bound makes
this a bounded diagonal map with norm at most two. Every coordinate of
`A_N v-Dv` tends to zero, and its squared norm is dominated by
`9 |v(q)|^2`. Tannery's theorem and the exact lp norm-square identity give
`||A_N v-Dv||^2->0`, hence strong convergence on the whole carrier.

The multiplier a_N is odd in z, so every A_N maps FE-odd vectors to FE-even
vectors. In particular A_N u is an explicit even signed-heat approximation
to the canonical even witness Du. Continuity of the Weil form gives
`Q(A_N u)->-E`; off RH these energies are eventually strictly negative,
while under RH u=0. This does not infer arithmetic positivity: it constructs
the precise even witness by signed heat and retains the unsquared factor z.
Pure square-heat multipliers alone remain FE-even and cannot implement D.

### Stronger conjecture exposed by the time-window proof, now proved on paper

The upper cutoff actually converges in operator norm with a uniform Gaussian
rate. Write A=Re(z_q^2). The actual height gap and strip bound give A>=2,
and the existing sector law gives |z_q|^2<=2A. Outside [-N,N], t^2>=N^2,
so `exp(-A t^2)<=exp(-N^2) exp(-(A/2)t^2)`. The remainder integral is thus
bounded by
`exp(-N^2) |z_q|/sqrt(A/2) <= 2 exp(-N^2)`.
Consequently
`||A_N v-Dv|| <= 2 exp(-N^2) ||v||`
for every Hilbert vector, uniformly over the complete spectrum. This improves
the strong-limit argument; it uses the proved uniform height gap, not RH.
The cutoff contains t=0 throughout, so this claim does not assert norm
convergence for windows whose lower endpoint stays positive.

## Completion scope after goal clearance

The user cleared the twenty-insight goal, then requested completion of the
unfinished work. The active scope is contribution 4: finish the signed-heat
construction, its uniform Gaussian convergence rate, and the even Hurwitz
witness consequences. Contributions 1–3 remain complete. This does not
restart the twenty-insight target.

Completion plan:
1. Formalise the uniform scalar tail bound and its actual Xi specialisation.
2. Package bounded Hilbert operators, prove operator-norm convergence, and
   derive finite-window even witness and Weil-energy convergence theorems.
3. Run narrow builds, final per-file checks and axiom audits; wire imports,
   refresh the index, run lint, and record exact results.

### Contribution 4 result and audit

The stronger operator-norm result is formalised, together with the original
strong convergence target and its canonical even-witness consequences:

- `ComplexSignedGaussianHeat.lean` (8 declarations): exact signed complex
  Gaussian formula, finite symmetric cutoffs, uniform bounds, and Gaussian
  tail estimate.
- `XiSignedHeatOrientation.lean` (11 declarations): exact actual Xi
  orientation formula, uniform spectral gap and cutoff error, Hilbert
  cutoff construction, and FE parity reversal.
- `XiSignedHeatOrientationConvergence.lean` (15 declarations): bounded
  complex-linear operators with
  `||A_N-D|| <= 2 exp(-N^2)`, operator-norm and strong convergence, FE-even
  signed-heat witnesses, and convergence of their Weil energies to `-E`.

Off RH, all sufficiently large finite-time witnesses have strictly negative
Weil energy. Eventual nonnegativity on this explicit sequence is equivalent
to RH. These corollaries are counted within the heat-construction package,
not as additional insights. The construction does not prove arithmetic
source positivity or realise an arithmetic test-function operation.

All three narrow `:olean` builds and final individual `lake env lean`
checks passed without warnings in these modules. All 34 declarations were
audited with `#print axioms`; each uses only `propext`, `Classical.choice`,
and `Quot.sound`. Each module is imported exactly once by the RHTower
umbrella. Index generation and `git diff --check` passed. Final
`scripts/formal_tools.py lint` exited 1 with 17 unrelated import-reachability
errors: `OddSectorImaginaryZeroMorseBound` and 16 HTGeometry modules, including
`SymbolicTransferOperator`. None of the eleven modules in contributions 1–4
has a lint error. Concurrent work was preserved; no unrelated imports were
changed to suppress that result.

Completed requested scope: contribution 4. Total preserved: 4 contribution
packages, 113 audited declarations, 11 modules. The original twenty-package
goal remains cleared.

## Workspace preservation

Initial unrelated changes: `docs/prompts.md`,
`HTGeometry/SymbolicTransferOperator.lean`,
`RHTower/PrimeArchSignedCompactCompletionCollapse.lean`, and untracked
`RHTower/OddSectorGroundDivisionOperator.lean`. Preserve them.
