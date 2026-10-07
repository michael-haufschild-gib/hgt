# Actual Xi cubic lift versus strip decay

- **ID:** RH-XICLSD-20261007
- **Stage:** 3-formalized; actual no-lift and full positive S3 survivor audited
- **Current checkpoint:** eight targeted builds and final actual-source checks pass;
  all 38 public axiom closures use standard foundations only; obsolete proof scratches removed.
- **Parent:** `../1-in-progress/xi-marked-joint-monodromy.md`, first actual cubic no-lift core
- **Exact target:** for each integer n at least two, there is no entire h with
  `(h(s)^3-3h(s)-2)/4 = Xi(s) exp(-s log n)` for every complex s.
- **Competing possibility:** an actual entire lift exists; the proposed decay
  argument must then fail at real descent, finite order, or finite-zero control.

## Candidate mechanism and simplifications

Write d=Xi exp(-s log n), P(x)=(x-2)(x+1)^2/4. The actual d has all zeros in
the critical strip and tends to zero uniformly there as imaginary part tends
to either infinity. A hypothetical entire h with P(h)=d has finite order at
most one, because a polynomial bounds its roots in terms of its value.

1. Establish real descent. Conjugate reflection h*(s)=conj(h(conj(s))) is also
   a lift. If h* differs from h, the third root -h-h* is entire, so the cubic
   discriminant is an entire square. But d(d+1) has an odd zero at an actual
   odd Xi zero, excluding that square. Thus h*=h.
2. In the connected upper tail of the critical strip, sufficiently small d
   confines h to disjoint small neighborhoods of the two roots 2 and -1.
   Connectedness selects one neighborhood throughout that tail. Real descent
   selects the same real root in the lower tail.
3. The other root b has only finitely many preimages under h: all such points
   are zeros of d and hence lie in the critical strip, while both tails are
   excluded. An infinite subset of the remaining compact rectangle would force
   h=b identically, contradicting nonconstant d.
4. Finite-order Hadamard factorization with finitely many zeros gives
   h-b=q exp(as+c), where q is a polynomial. Hence P(h), and then Xi, have finite
   exponential type. Actual positive-real Gamma growth makes Xi infinite type.

Every step above remains under exact internal and external audit. In particular
one must prove the actual uniform strip decay, the needed growth/factorization
theorems, nonconstancy, existence of an odd Xi zero, and the discriminant identity.
No simple-zero assumption or RH assumption is permitted. Multiplication by the
nonvanishing exponential preserves every zero order. At an Xi zero, d+1 is one.

### Simpler uniqueness route under audit

An odd zero rho of d forces every entire cubic lift to take value 2 there:
value -1 would give even vanishing order through the factor (h+1)^2. Any two
lifts agree at rho, where P'(2)=9/4 is nonzero. The subtraction identity
`(h-g)(h^2+hg+g^2-3)=0` then gives equality of the entire functions, since the
second factor equals 9 at rho and hence is not identically zero. This proves
uniqueness and real descent without introducing a discriminant square root.
It needs only one actual odd Xi zero, not simplicity of any zero or of a fiber.

## Initial literature audit

[Dundulis–Garunkstis–Karikovas–Simenas (2023)](https://www.mdpi.com/2227-7390/11/5/1150)
proves compositional primeness of the Hurwitz zeta function and cites the
Gamma/Riemann-zeta primeness theorem of Liao–Yang (2003). This does not directly
apply to the completed and exponentially twisted Xi function: multiplication
by Gamma and exponential factors does not preserve compositional primeness.

[Garunkstis–Steuding (2019/2020)](https://arxiv.org/pdf/1908.03108)
separates pseudo-prime, left-prime and right-prime statements. Its Selberg
result initially still permits polynomial left factors. Such a weaker result
would not close this exact cubic problem. The proposed strip-decay mechanism
must be audited on its own hypotheses; no generic primeness theorem is imported.

## Corpus search evidence

- Deep query `Riemann xi entire polynomial composition cubic lift indecomposable
  growth`: complete, partial=false, output
  `/tmp/rh-xi-cubic-indecomposability-search-20261007.json`.
- Deep query `entire finite order finitely many zeros polynomial exponential xi
  critical strip vertical decay cubic lift conjugate discriminant`: complete, partial=true,
  output `/tmp/rh-xi-cubic-strip-decay-search-20261007.json`.
- Both inventories are complete (68140/68141 files), but compiler coverage has
  many pending/stale entries. Candidate applicability was checked in source:
  `R:RiemannXiZerosInfinite` supplies unconditional `OrderOneEnvelope` and
  `riemannXi_ray_growth`; `R:FiniteZeroSubquadraticRigidity` supplies finite-zero
  factorization and `zeroSet_infinite_of_subquadratic_superlinear_ray`;
  `R:XiStripInverseDecay` supplies uniform strip decay;
  `R:GlobalParityWall` supplies odd critical-line zeros above every height.
  `R:RiemannXiRealAxisNonvanishing` contains the bridge `xi_eq_riemannXi`.
  Exact API scratch verification and dependency audits remain required.

## Dependency-closed paper proof

The direct argument below removes real descent and discriminants from the
critical path. Fix n>=2 and suppose h is entire with P(h)=d_n. Put f=h+1, so

    4 d_n = (f-3) f^2.

**Growth upper bound.** If r=|f|>=6 then |f-3|>=r/2, whence r^3<=8|d_n|;
in particular r<=8|d_n| since r>=1. Otherwise r<6. Thus
|f|<=6+8|d_n| everywhere. Xi's actual order-one envelope and the exponential
mark give an order-one envelope for f, hence a subquadratic exponential bound
with exponent 3/2.

**Growth lower bound on a real ray.** For any real A, put B=max(1,A).
If |f(sigma)|<=exp(B sigma), sigma>=1, then
|d_n(sigma)|<=exp(3 B sigma), because |f-3|<=|f|+3<=4 exp(B sigma).
Consequently |Xi(sigma)|<=exp((3 B+log n) sigma). The established Xi ray-growth
theorem supplies a sigma>=1 contradicting this bound. Hence f beats every
linear logarithmic slope. Finite-zero subquadratic rigidity implies that f
has infinitely many distinct zeros.

**Odd zeros select the simple cubic branch.** At any odd zero rho of d_n,
h(rho) is 2 or -1. If it were -1, the factor h-2 would be nonzero there and
the order of d_n would be twice the order of h+1. This is even, a contradiction.
All relevant orders are finite: d_n is nonzero as an entire function and the
exponential mark never vanishes. Thus h(rho)=2 and f(rho)=3.

**Both strip tails contain such points.** Hardy's proven odd-order theorem
gives critical-line odd Xi zeros above every height. Conjugation of Xi preserves
orders and gives corresponding zeros below every negative height. The entire
exponential mark preserves these orders, so f takes value 3 in each arbitrarily
high upper and lower strip tail. No conjugation property of h is required.

**Tail exclusion of f=0.** Uniform Xi decay on 0<=Re(s)<=1, combined with
|exp(-s log n)|<=1 on that strip, gives T>0 such that |d_n(s)|<1 for
|Im(s)|>=T. Each closed tail is convex. If f vanished at a point in that tail,
join it by a straight segment to an odd-zero point where f=3. The continuous
real function |f| takes value 1 somewhere on the segment. There |f-3|>=2,
which gives only |d_n|>=1/2. Choose the decay threshold **1/2**, rather than 1:
then |d_n|<1/2 contradicts |(f-3)f^2|>=2. Thus neither tail contains a zero of f.

**Compact remainder.** Every zero of f is a zero of d_n and hence of Xi, so
it lies in the critical strip. Tail exclusion puts the entire zero set of f
inside a compact rectangle. The nonzero entire function f has finitely many
zeros there by isolation/identity, contradicting the infinitude proved above.
Therefore no entire cubic lift exists. This uses neither RH nor a simple-zero
hypothesis, and every arithmetic input is already unconditional in the corpus.

The inequality threshold correction above is retained explicitly in the audit:
the formal proof must use 1/2. The argument only needs subquadratic growth,
superlinear real-ray growth, confinement and decay on a strip, and odd zeros
in both tails. It fails for prior reflected cubic countermodels because their
zeros are not confined to one fixed strip with the actual decay/growth package.

## Hostile and significance audit

Verdict: **BRIDGE**. This combines classical finite-zero Hadamard rigidity with
the actual Hardy/strip-decay source; no scientific novelty is certified.
The [Liao–Yang primary abstract](https://onlinelibrary.wiley.com/doi/pdf/10.1002/mana.200310078)
confirms Gamma/zeta compositional primeness, but does not state this completed,
exponentially twisted Xi conclusion. Search non-hits are not an absence proof.
Unlike the finite rational law, the present claim directly addresses the
parent's actual cubic no-lift premise. It still does not prove C1 or RH.

The positive closure to audit after formalization is the actual irreducible
cubic over the meromorphic plane, with a degree-three extension (and ultimately
the S3 splitting field). A meromorphic root of a monic cubic with entire
coefficients cannot have a pole, so no-lift should imply irreducibility. Do not
mark that stronger statement verified until its exact transport is completed.

### Positive closure: dependency-closed algebraic paper argument

Over K, the field of globally meromorphic functions on C, put
delta_n=Xi exp(-s log n) and Q_n(X)=X^3-3X-(2+4 delta_n).
At a pole of a meromorphic candidate root r of order m<0, the cubic term has
order 3m while the linear term has order m and the entire constant term has
nonnegative order. The unique smallest order cannot cancel, a contradiction.
After filling removable values, r is an entire lift already excluded above.
A cubic over a field is reducible exactly when it has a root. Thus Q_n is
irreducible and adjoining any root gives an actual degree-three extension.

Its discriminant is -432 delta_n(delta_n+1). At an odd Xi zero, the exponential
mark is a unit and delta_n+1 is one, so the discriminant has odd order and is
not a square in K. The characteristic-zero cubic is separable. Its splitting
group is a transitive subgroup of S3, and nonsquare discriminant excludes A3;
therefore the group is S3 and the splitting field has degree six. This is the
strong positive survivor to formalize, not a claim that the full free-group
monodromy conjecture C1 or RH follows.

The local no-pole argument can follow the existing normal-form transport in
`H:MeromorphicPlaneSquareRoot`, read in full. The generic root search completed
in `/tmp/rh-xi-cubic-meromorphic-root-search-20261007.json` with partial=false.
No generic monic-root result was accepted from its hits. Local removal,
actual irreducibility and root-algebra dimension now pass Lean; S3 remains
under formalization.

The formal S3 proof uses a direct degree argument. The explicit product of
three root differences squares to the cubic discriminant in its splitting
field. Its nonsquareness over K makes X^2-discriminant irreducible, forcing
degree divisible by two. Cubic irreducibility forces divisibility by three.
The faithful action on the three distinct roots bounds the group order by
six, hence it is six and the action is all S3. This avoids assuming a generic
discriminant/Galois criterion as an unproved premise.

Primary parent check: Keith Conrad's
[Galois Groups of Cubics and Quartics in All Characteristics](https://kconrad.math.uconn.edu/blurbs/galoistheory/cubicquarticallchar.pdf),
Theorem 1.1 and Section 2, states the classical irreducible cubic/discriminant
criterion and explains the sign action on the root-difference product. This
confirms the algebraic survivor is a classical bridge applied to the actual
Xi source, not a new abstract Galois theorem.

## Obligations

### Formalization log

- Generic connected-region exclusion and odd-order simple-branch selection now
  pass in `/tmp/rh-cubic-strip-separation.lean`, with exact API verification.
  The odd-order lemma works directly with ENat.toNat and needs no added
  finiteness-of-order hypothesis.
- The cubic root bound, inherited order-one envelope and actual Xi real-ray
  growth transport pass scratch, including the exponential reassociation.
- Actual Xi growth transport and the infinite-zero consequence now pass scratch
  with empty logs. The generic branch/tail lemmas, including convexity of both
  strip orientations, also pass. Promoted/wired `H:CubicStripSeparation` and
  `R:XiCubicLiftGrowth`; targeted build is queued after the actual-source API
  check. The full actual no-lift proof is prepared in
  `/tmp/rh-xi-cubic-strip-no-lift.lean` and will run after those builds.
- Compactness can use the existing `xi_zeros_finite_ball` directly, since every
  zero of the lift factor is an actual Xi zero. No duplicate generic finite-zero
  infrastructure is needed. `EMAnnulusSupply` supplies `xi_zero_re_pos` and
  `xi_zero_re_lt_one`; `Reflection` supplies `xi_orderAt_conj`.
- The full actual no-lift scratch passes after fixing the exponential analytic
  proof, qualifying `Complex.I`, and normalizing a negative product. Promoted
  and wired `R:XiCubicStripNoLift`; targeted build is in progress. One redundant
  `ring` tactic will be removed before final actual-source audit.
- The search for cubic/S3 infrastructure completed with partial=false, full
  inventory 68149, but substantial pending/stale compiler coverage. Output:
  `/tmp/rh-xi-cubic-s3-search-20261007.json`. Generic rational-field S_n results
  are not accepted as a substitute for this actual cubic's Galois group.
- Local no-pole and normal-form extension proofs are prepared in
  `/tmp/rh-cubic-meromorphic-root.lean`. They compare the order of f-3 with f
  at a hypothetical pole, making the cubic value have order three times that
  pole order. API verification and compilation are next in the single Lean chain.
- Local no-pole, entire-extension and field-equation transport now pass Lean;
  promoted/wired `H:MeromorphicPlaneCubicRoot`, targeted build passes.
- `R:XiCubicStripNoLift` rebuilds without owned warnings after removing the
  unused tactic. The exact source closure remains unconditional for nonnegative
  real tilt; no simplicity, RH, or monodromy premise is added.
- Actual field no-root, irreducibility and dimension-three root algebra all
  pass `/tmp/rh-xi-cubic-meromorphic.lean` with empty log. Promoted/wired
  `R:XiCubicMeromorphic`; targeted build is running.
- Prepared generic S3 proof in `/tmp/rh-cubic-galois.lean` and actual nonsquare
  discriminant in `/tmp/rh-xi-cubic-discriminant.lean`; these remain unverified.
- Generic cubic S3/degree-six proof and actual nonsquare-discriminant theorem
  now pass Lean and targeted builds. Promoted/wired `H:CubicGaloisGroup` and
  `R:XiCubicDiscriminant`. Exact mathlib API checks pass.
- The full actual wrapper passes `/tmp/rh-xi-cubic-galois.lean` with empty log:
  the root algebra is a field, its distinguished root satisfies the cubic,
  `xiCubicGaloisEquiv` gives actual S3, and splitting degree is six. Integer
  wrappers are premise-free, indexed by n+2. Promoted/wired `R:XiCubicGalois`.
- Final audit preparation finds 38 public declarations in eight uniquely
  wired leaves. `/tmp/rh-xi-cubic-final.sh` runs targeted `--old` builds,
  all named `#print axioms` checks, then `lake env lean` on every actual source.
  Index/lint, card closure and proof-scratch cleanup follow only on success.

- [x] Corpus and primary parent/hostile audits; assign an honest verdict.
- [x] Dependency-closed paper proof of the actual no-lift statement.
- [x] Exact Lean formalization with all actual Xi hypotheses discharged.
- [x] Public axiom audit, target builds, actual-source checks and unique wiring.
- [x] Run authoritative index/lint and record its exact scope below.
- [x] State the precise monodromy consequence without claiming RH.

## Final evidence and scope boundary

All eight leaves build with `lake --old build +Module`. Every actual source
passes final `lake env lean path/to/Module.lean` with an empty log. All 38 named
public declarations pass `#print axioms`: only `propext`, `Classical.choice`
and `Quot.sound` occur. Every umbrella import is present exactly once.

Evidence: `/tmp/rh-xi-cubic-final-build.log`,
`/tmp/rh-xi-cubic-axioms.log`, `/tmp/rh-xi-cubic-audit-names.txt`,
`/tmp/rh-xi-cubic-final-modules.txt`, and eight
`/tmp/rh-<Leaf>-xi-cubic-final-20261007.log` files.
All eight obsolete proof scratches were removed only after exact comparison
against their promoted sources, ignoring added module docstrings. API/audit
scratch files and logs remain as evidence.

`scripts/formal_tools.py index` passes. Authoritative lint exits 1 for six
unrelated unwired leaves: `R:FreeLagSymbolBoundaryLayer`,
`H:ApertureConeCalculus`, `H:ApertureConeWinding`, `H:ApertureLogTranslation`,
`H:ApertureOpenHistoryIdeal`, `H:BoundaryCoronaCStarAlgebra`. No owned leaf
fails. This is not a global lint pass; unrelated source was not changed.
Logs: `/tmp/rh-xi-cubic-index-20261007.log`,
`/tmp/rh-xi-cubic-lint-20261007.log`.

Exact achievement: actual entire and meromorphic cubic lifts are excluded,
the source cubic is irreducible, its root field has degree three, and its
splitting field has actual Galois group S3 and degree six. The integer wrappers
are unconditional. This closes the parent's first fixed-cubic obstruction.
It does not prove the joint free-group image C1, construct a distinguished
normalized-cover loop, or imply RH. Verdict remains BRIDGE.

Next candidate: `../1-in-progress/xi-joint-cubic-galois.md`, testing the full product
S3^S for finite families of distinct actual marked channels.
