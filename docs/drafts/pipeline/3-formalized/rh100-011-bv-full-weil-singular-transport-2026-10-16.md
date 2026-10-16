# Contribution 011 — BV admission and singular transport of the full Weil form

Baseline: **10/100**. Previous turn was verified progress: actual-source
closed full-Jordan generator, compact Hilbert–Schmidt inverse, entire Xi
determinant, and RN gluing-rank interpretation. Seven direct leaf audits,
61 standard-axiom audits and global lint passed; cleanup complete.

Plan:
1. Recheck current map and use documented corpus searches across source Euler
   division, singular native currents, and arithmetic trace/cup mechanisms.
2. Test conjectures against exact source spaces. Record failures and positive
   survivors. Select only a distinct structural obstacle with a closed paper
   proof, not an estimate, RH receiver, or routine consequence of 010.
3. Formalize, direct-audit leaves with `lake --old env lean`, audit axioms in
   `/tmp`, wire umbrellas, lint, clean scratch, then count and persist.

Constraints: no web, external novelty check, old reports, numerical experiments,
subagents, commits, full/umbrella builds, or heartbeat overrides. Main result
unconditional. One owned foreground Lean process at a time.

Initial candidate, not yet a theorem: literal Euler inversion. The actual cap
is even Schwartz with only the value and Fourier value at zero killed. Thus
annular compact sources may realize smooth periodic Mellin data. An imaginary-
lattice inverse of the genuine zeta multiplier, with polynomial growth, could
pay boundary periodization surjectivity and remove the one-sided Green defect.
Pointwise Xi-jet division and Floquet Hilbert closure alone do not pay this.

Initial independent checks explored full nonlinear/prime–Gamma transport and
actual-source arithmetic trace/cup realization before the selection below.

Selected and formalized conjecture: singular compactification of the complete signed Weil form.
Combine RN's unconditional all-parameter BV cut jets with CHMD's literal full
arithmetic difference graph and dense compact C2 core. Every globally BV real
profile enters that graph; the theta quantile transports its entire quadratic
form, every prime-power edge, Gamma continuum and polar term. Apply to every
real polynomial response of every real-linear projection of every cut parameter
jet. No spectral sign is asserted.

Paper mechanism, dependency closed at the mathematical level:
1. Signed variation w(x)=Var(f;0,x) is bounded and monotone and dominates
   |f(x+h)-f(x)|. Its translation integral is at most 2 Var(f) h, by finite
   interval telescoping and exhaustion. Boundedness of f upgrades this to the
   squared-increment integral. This includes jumps and singular continuous BV.
2. The actual Gamma density exp(-h/2)/(1-exp(-2h)) has finite first moment:
   h/(1-exp(-2h)) <= h+1/2 follows from exp(2h)>=1+2h. The theta factors are
   bounded. Thus the Gamma graph energy is finite. CHMD's proved finite total
   prime-edge mass pays all primes for bounded f; its finite theta-cosh mass
   pays the source coordinate. No smoothing or continuity premise on f.
3. The graph norm controls its signed energy. Polar moments are continuous
   source-coordinate functionals by Cauchy--Schwarz against the finite mass.
   Their exact rank-two correction gives the unique continuous full Weil
   quadratic form extending literal compact C2 tests. Dense C2 approximation
   retains every mixed term by polarization.
4. For p=theta CDF and Q its inverse, Q(p(x))=x. At a positive shift h,
   p(Q(t)+h) is the exact compactified edge. Change of variables divides the
   original mass/edge densities by theta's normalized density at Q(t).
   The integral identity is valid with no endpoint derivative bound. Applying
   it separately to every prime term and to the Gamma continuum yields the
   entire signed transported form, not merely the linear theta current.
5. RN supplies unconditional BV of every cut jet, including nonzero terminal
   charges; hence these are concrete admitted vectors of the full form and
   smooth-core limits. Finite polynomial/nonlinear BV operations remain in
   the same arithmetic domain.

Failed shortcuts / deferred candidates:
- Existing full-graph closure is already proved by CHMD and is not a new result.
- A coordinate trace identity is insufficient for actual-source flow calculus;
  the needed group extension remains separate. Not selected here.
- Literal Euler inversion still needs periodic Poisson-range surjectivity;
  finite rational inverses and Hilbert resolvents do not imply it. Deferred,
  not declared false or counted.

## Exact result and structural change

Write `r = thetaSource.normalized`, `Q = thetaSource.quantileFun`,
`p = thetaSource.cdfFun`. The actual compact shift is
`T_h(t) = p(Q(t)+h)`, which always lies in `(0,1)`. Original mass and edge
densities become their values at `Q(t)` divided by `r(Q(t))`. No derivative
bound on `Q` is assumed.

The canonical real full form on the CHMD source graph is

`W(u,v) = sourcePair(u,v) + 2 C(u) C(v) - 2 S(u) S(v)`,

where `C` is the mass-coordinate inner product with `1`, and `S` is the
mass-coordinate inner product with `tanh(x/2)`. On original compact C² tests
this is exactly the original full Weil quadratic form. Its continuity and
uniqueness are proved, and polarization retains mixed terms.

For every globally BV real `v`, the literal function lifts to the actual source
graph; the compactified complete form of `v ∘ Q` equals `W(v,v)`. This includes
jumps and singular continuous BV. Gamma product integrability, individual prime
integrability and full prime summability are explicit theorems, so the identity
does not rely on default values of nonintegrable Bochner integrals. Every BV
profile on `[0,1]` and every polynomial response has the same full transport.

For arbitrary `n : ℕ`, `z : ℂ`, interior cut `c`, real continuous-linear
`ell : ℂ →L[ℝ] ℝ` and `P : Polynomial ℝ`, there is no admission premise:

`compactFullWeil(P ∘ ell ∘ cutQuantileParameterJet n z c)`
`  = sourceWeilEnergy(cutJetArithmeticSource n z (Q c) ell P)`.

The right side retains the literal Gamma continuum, every prime power, negative
cosh mass and both polar terms. It is the limit of the literal full Weil values
of original compact C² tests converging in the source graph. At the actual
Meyer/Fredholm spectral rank, an explicit choice between real and imaginary
projection supplies a genuinely discontinuous response that still enters this
graph. Thus this construction does not require the terminal charge to vanish.

The obstacle removed is full arithmetic-domain admission and exact singular
quadratic-form transport for a class previously available only as native BV
currents. RN supplies all parameter jets; CHMD supplies the original complete
prime–Gamma graph/core; HF supplies the actual spectral-rank interpretation of
the terminal charged order. This opens arithmetic variational and mixed-form
arguments on every such nonlinear response without a continuity restriction.

## Lean implementation and audits

- `HTGeometry/BoundedVariationTranslationIntegral.lean`: measurable/bounded BV,
  monotone translation exhaustion and whole-line squared-increment integrability.
- `RHTower/ThetaBVArithmeticAdmission.lean`: actual Gamma first moment, full
  arithmetic graph admission of every BV profile, exact source energy,
  C¹ and polynomial composition.
- `RHTower/ThetaBVWeilForm.lean`: both continuous polar moments, canonical full
  signed form, exact original compact-test identification, uniqueness,
  polarization and original compact C² approximation with full Weil convergence.
- `RHTower/ThetaQuantileArithmeticForm.lean`: exact compact arithmetic shifts,
  weighted integral transport, absolute Gamma/prime admission, complete form
  transport for all BV profiles and polynomial responses.
- `RHTower/PaperThetaConfluentArithmeticWork.lean`: unconditional all-order,
  all-parameter polynomial cut-jet transport and source construction; original
  compact-test approximation; terminal-rank discontinuous response admission.

All five leaves passed direct foreground `lake --old env lean -o ... <leaf>`
audits. The `/tmp` mathlib API check passed. All **81 public declarations** passed
`#print axioms`; only `propext`, `Classical.choice`, `Quot.sound` occur. All five
umbrella imports occur exactly once. Freshness checks passed for the five leaves
and seven direct local prerequisites. No full or umbrella build, numerical
experiment, added axiom, proof hole or heartbeat override was used.

Repository-wide `scripts/formal_tools.py lint` was run. Its sole error was the
separate concurrently created `CHMDKleinGordonBoundarySingularity` module being
unreachable from `RHTower.lean`; it had no compiled artifact. None of the five
owned leaves triggered a lint error. That separate work was left untouched.
All owned `/tmp/hgt_rh011*` search, scratch and audit files were removed after
recording their results. The ledger records this as **11/100**; the overall
goal remains active.

## Scope and next conjectures

This is the continuous full-form extension identified with original compact C²
Weil values and their limits. No literal spectral/Fourier formula evaluated
directly on discontinuous complex BV data is asserted. The theorem concerns
real profiles and polynomial real responses; it does not assert a complex
spatial Jordan equation or BV-norm holomorphy.

The full form retains its signs. Positivity, directed/causal nonlinear boundary
current identities, orientation of reflected normal charges, and signed
prime–continuous cancellation remain open. Quantile transport does not solve
them. Euler periodic Poisson-range surjectivity and actual-source flow calculus
also remain separate. Future conjectures must address one of these genuinely
unpaid structures; routine consequences of this transport do not count again.
