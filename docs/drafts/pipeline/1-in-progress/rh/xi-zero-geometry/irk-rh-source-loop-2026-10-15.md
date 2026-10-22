# IRK: source construction research loop

Objective: unconditional formal Lean proof of RH through IRK. Active; no RH proof claimed.

## Rules and plan

- Follow hgtl7 each cycle; user's corpus-only instruction overrides external literature checks.
- Read Lean sources; use documented research search; no numerical experiments.
- Identify exact source construction, attack it, finish a dependency-closed paper proof before Lean.
- Audit any new Lean leaves with `lake --old env lean`, print axioms in `/tmp`, wire umbrellas, run formal lint; no full builds.
- Continue conjecturing after failures. Do not equate a bridge or obstruction with RH completion.
- `update_plan` is unavailable in this session; this file records plan and checkpoints.

## Authoritative starting evidence

- `PrimeIrrationalRotationKZeroRH.lean`: integer trace `rank + theta*chern` forces Chern coordinate zero. `PrimeRotationKZeroIndexDatum` exists iff local order is zero. Its Xi construction is explicitly absent.
- `PaperPrimeRotationCoherentLimit.lean`: finite coherent packets tend to zero in operator norm, have ordinary Fredholm determinant one, and have Gram determinant tending to `exp(E)`; `E` is strictly positive exactly for nonzero packet coefficients.
- `PaperPrimeRotationCoherentKernel.lean`: `E` is finite prime logarithmic exponential-sum Gram energy.
- Existing finite Gram positivity alone supplies no Xi multiplicity, Chern class, or integer trace.

## Cycle 1: source landing audit

Candidate: the native coherent Gram completion supplies an integer analytic index and nonzero off-line Chern charge without an additional arithmetic construction.

Attack in progress: inspect source dependencies and scaling/degeneration. The packet construction currently takes only primes and arbitrary complex coefficients; the missing Xi dependence must be specified, not assumed.

[OPEN CORE] Construct actual Xi-dependent projective data with both trace and Chern identifications. Existing coordinate equivalence is a receiver, not such a construction.

User steering: remain on IRK's unanswered mathematical source problem. Do not replace it with improved constants, asymptotic estimates, or adjacent Gram results. Candidate tests must address construction of the actual module and its two pairings.

Next source mechanism under examination: induce the local Xi divisor along its spectral translation orbit, then descend to the prime rotation algebra. Audit whether orbit induction produces a finite projective module, whether it retains local multiplicity, and which pairing it actually carries. If direct descent fails, repair that precise failure; do not abandon IRK.

### Exact scalar correction conjecture and paper proof

Candidate C1: for sufficiently small nonzero prime clock step `t`, a holomorphic scalar weight `w` can correct `T_t f(s)=f(s+t)` so it preserves the Xi ideal and acts invertibly on the local Xi quotient at an assumed zero `rho`.

Verdict: **FALSE**, by the following exact conductor classification. This is a local analytic obstruction within IRK, not a retirement of IRK and not a new scientific-knowledge claim.

Write `I_rho=(xi)` in holomorphic germs at `rho`. Choose `t` small and nonzero so `xi(rho+t) != 0`, possible because xi is entire, nonzero, and its zeros are isolated. Then `xi(s+t)` is a unit germ. Consequently

`w(s) xi(s+t) in I_rho` iff `w in I_rho`.

Proof: the reverse direction is multiplication by a holomorphic germ; the forward direction divides the witness by the unit `xi(s+t)`. If `w=xi*h`, every holomorphic `f` at `rho+t` satisfies `w(s) f(s+t)=xi(s)[h(s)f(s+t)]`. Thus every corrected translation preserving even the ideal generator induces the ZERO map on the whole local quotient. At a Xi zero the quotient is nonzero, so this map is not invertible. This audits all holomorphic scalar corrections, not one chosen weight.

Positive survivor: exact conductor ideal `(I_rho : xi(.-+t))=I_rho`, including its complete induced-action classification. The meromorphic correction `xi(s)/xi(s+t)` remains a genuine moving-fiber transport; its order at `s` is `ord_s xi - ord_(s+t) xi`. Near an isolated zero it retains a zero/pole dipole of multiplicity `d`, not a holomorphic automorphism of the fixed quotient. Formalize these exact statements next.

Next conjecture C2, still IRK: retain the meromorphic transition and its divisor as relative gluing data instead of clearing its poles. Construct the projective class from that gluing, calculate its actual canonical trace and Chern pairing, and then attack the Xi-specific identity equating the trace to the analytic count. No such identity has been proved.

### Positive transport law, dependency-closed proof

Set `G_t(s)=xi(s)/xi(s+t)` and `U_t f(s)=G_t(s) f(s+t)`. Since every shifted Xi function has isolated zeros, the cancellation identities below hold as punctured germs at every point:

- `G_t(s) G_u(s+t)=G_(t+u)(s)`; cancel the nonzero intermediate factor `xi(s+t)`.
- `U_t(xi*f)=xi*T_t(f)`; cancel the same factor.
- `U_t U_u=U_(t+u)`; combine the cocycle with associativity of translation.
- `U_t M_p=exp(-log(p)t) M_p U_t`; the scalar correction commutes with multiplication and the already-proved global Weyl relation applies.

The meromorphic order identity follows from order of a quotient and translation's derivative one. At an isolated zero `rho` of multiplicity `d`, both `xi(rho+t)` and `xi(rho-t)` are nonzero for all sufficiently small nonzero `t`. Hence `ord_rho G_t=d` and `ord_(rho-t) G_t=-d`. Since `d>0`, a holomorphic extension at the second point would have both nonnegative and negative order, a contradiction. This gives an exact reversible meromorphic transport with retained divisor charge. It does not yet give a finite projective module over the norm-closed prime rotation algebra.

Cycle assessment: C1 is killed by a complete local conductor proof. C2 remains the actual unanswered IRK construction. Formalizing C1 and the retained transport checks the proposed repair and records the exact object available for C2; no improved estimates or substitute RH route are involved. These are classical analytic consequences applied to the native source; beyond-literature novelty is not claimed.

### C2 construction attempt: meromorphic conjugacy and the missing lattice

The explicit transport is `M_xi T_t M_xi^-1` on meromorphic germs. Thus forgetting the holomorphic lattice makes it conjugate to the original translation representation. Such a construction alone cannot supply a source-sensitive class: the conjugation makes the Xi factor invertible.

Retain instead the embedded lattice pair `(O, xi O)`. Its quotient retains the analytic multiplicity. The attempted equivariant square uses the ordinary translation on the ambient term and the corrected translation on the Xi term. Their difference is the actual defect of the embedding, not a removable choice of scalar frame. C1 proves that a holomorphic scalar completion of this square on the fixed local quotient is impossible at a separated zero. This is the same IRK source descent problem, now with explicit transition and lattice data.

The next unresolved construction is a relative projective extension retaining this lattice defect. It must supply an actual idempotent or projective module over the native prime rotation algebra, then derive its trace and Chern pairings from the source. Assigning the two coordinates by their desired values is forbidden. Meromorphic conjugacy, finite-dimensional rank, the Weyl multiplier, and a Chern coordinate are distinct data; no equality between them has been proved here.

## Current formal artifact

`formal/GaloisForLFunctions/RHTower/PrimeRotationXiSourceTransport.lean`:
exact conductor and induced-action classification, no local right inverse, meromorphic source transport, prime Weyl relation, cocycle/composition laws, exact divisor orders and nonremovable poles, and specialization to a positive native rational-imaginary clock denominator.

Scratch development passed `lake --old env lean /tmp/irk-source-draft.lean` without warnings. Actual-path final audit passed without warnings:

`lake --old env lean GaloisForLFunctions/RHTower/PrimeRotationXiSourceTransport.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeRotationXiSourceTransport.olean -i .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeRotationXiSourceTransport.ilean`

Owned object is newer than source. Module has 17 public declarations (14 theorems, 3 definitions), 239 lines. Umbrella import is present exactly once. `scripts/formal_tools.py index` completed. `lake --old env lean /tmp/irk-source-axioms.lean` exited 0: all 17 public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. No added axioms, `sorryAx`, or computational reflection axiom appears.

`scripts/formal_tools.py lint` exited 1: four concurrent even-sector modules are unreachable from their umbrella (`EvenSectorAbelAveraging`, `EvenSectorAbelLaplace`, `EvenSectorAbelPinning`, `EvenSectorFarBumpPoleFreeCombination`). Existing large-file warnings also emitted. No reported error concerns the new IRK module. Preserve those concurrent files; do not claim a repository-wide lint pass.

Completion audit: no unconditional theorem of `RiemannHypothesis` has been constructed. The required projective module and its source-derived trace/Chern pairings remain missing. Therefore goal remains active. This turn made progress by disproving one concrete source correction and formalizing its exact surviving transport; it did not solve the research objective.

## Verification log

- Initial worktree contains concurrent RHTower even-sector changes. Preserve them.
- Corpus search `IRK`: complete request, source-only candidates; coverage warns older snapshot and unmeasured semantic coverage. Refined source and Gram searches initiated.

## Cycle 2: can the induced divisor enter a projective module?

The meromorphic-gluing and orbit-module searches completed without finding the missing source
construction. Their coverage reports warn that semantic coverage is unmeasured and some compiler
snapshots are stale. Read Lean evidence includes the concrete bilateral rotation representation,
its full norm-closed algebra, and its proven zero intersection with compact operators.

Candidate C2a: retain the local divisor by orbit induction, then realize the resulting generalized
eigenvectors inside a projective module over the native closed rotation algebra.

Dependency-closed paper attack:

1. Let `A` be that concrete algebra on `H = l2(Z)`, and let `V` be its diagonal prime modulation.
   At every positive clock denominator, its diagonal values are pairwise distinct: equality of
   values at `m,n` would make the prime phase at integer `m-n` equal one, which the existing
   irrationality theorem excludes unless `m=n`.
2. If `(V-lambda) a = 0` for `a in A`, every vector in the range of `a` is supported on at most
   one coordinate. Thus `a` has rank at most one and is compact. The existing Calkin-faithfulness
   theorem gives `a=0`. This holds for every complex `lambda`, including unit-circle values.
3. Consequently left multiplication by every power `(V-lambda)^d` is injective on `A`, and
   coordinatewise on every free left `A`-module. A projective module embeds in a free module,
   so it contains no nonzero generalized `V`-eigenvector.
4. In contrast, the natural Hilbert-space representation contains the nonzero coordinate vector
   at zero, with `V e_0 = e_0`. Therefore this actual rotation representation is not a projective
   module over `A`. Positivity and a faithful operator representation do not supply projectivity.

Verdict: C2a is false for equivariant inclusions retaining the finite local generalized-eigenvector
data. This is stronger than the fixed-germ scalar obstruction and applies after arbitrary
projective stabilization. It does not rule out a relative index construction whose source is a
complex rather than an embedded eigenspace.

Positive survivor proved on paper: the complete absence of generalized modulation
eigenvectors in projective modules over the native closed algebra, together with the concrete
nonprojective Hilbert representation. This is a structural source-construction audit; no claim of
beyond-literature novelty or progress on RH's truth follows from it alone. This auxiliary result
was not formalized: the user's subsequent steering explicitly prioritizes the source canonical
trace integrality problem.

Next hard construction remains IRK: a relative index must convert the divisor complex into a
projective class without claiming that its torsion vectors embed in that class. Its trace and
Chern identities still require source proofs. Do not replace this task with norm estimates.

## Cycle 3: integral trace through simultaneous prime descent

User's precise target: irrational trace integrality must kill off-line multiplicity through
noncommutative topology. Keep the actual canonical trace, the projective class, and its Chern
pairing central. Conventional spectral counting is not the proposed proof mechanism.

Candidate integrality mechanism: a single Xi relative-index class descends to two distinct
single-prime rotation algebras, and both inclusions into the common two-prime algebra preserve
the canonical trace. Equality of the two ambient classes then gives equality of their traces.
No common-source descent or equality of classes has yet been constructed.

Arithmetic part, dependency-closed paper proof: for distinct primes `p,r` and nonzero natural
clock denominators `q,s`, the lattices

`Z + log(p)/(2*pi*q) Z` and `Z + log(r)/(2*pi*s) Z`

intersect exactly in `Z`. Indeed, equality of two such coordinates gives

`s*c_p*log(p) - q*c_r*log(r) = 2*pi*q*s*(rank_r-rank_p)`.

Exponentiating makes the left side an algebraic number (an integer power ratio of primes).
If the integer coefficient of `2*pi` on the right were nonzero, Gelfond--Schneider applied to
base `-1` and nonzero purely imaginary algebraic exponent would make its exponential
transcendental. Hence the ranks agree. Unique factorization / the existing independence of two
prime logarithms then forces both Chern coordinates to vanish. The reverse lattice inclusion
uses Chern coordinate zero.

This derives integrality from cross-prime topological compatibility, without assuming that the
trace already equals an ordinary finite-dimensional count. Formalize the exact lattice theorem;
then return to constructing simultaneous descent of the Xi source class. The arithmetic theorem
alone is not that construction, and is not an RH proof.

Stronger construction target C3b: Euler-tail descent. A finite Euler factor `1-p^(-s)` is a
holomorphic unit where `Re(s)>0`; deleting any finite set of primes preserves the Xi divisor
there. Seek one projective relative-index class whose deletion equivalences are realized in the
corresponding remaining-prime rotation algebras. The missing implication is from holomorphic
unit equivalence to actual descent of a projective class. It must be constructed, not assumed.

The arithmetic survivor extends to arbitrary finite prime support: if
`sum m_p log p = 2*pi*k` with integral coefficients, exponentiation and Gelfond--Schneider force
`k=0`, and unique factorization forces `m=0`. Thus coordinates
`rank + (sum m_p log p)/(2*pi*q)` are unique at a nonzero clock. If a fixed trace admits such a
coordinate avoiding every finite set of primes, choose the excluded set to be the support of
one coordinate. Uniqueness forces that support to be empty, proving the trace is an integer.
This is an exact tail-intersection argument, with no estimates or limiting spectral counts.

Do not identify the arithmetic trace lattice with the range of an all-prime canonical `K0`
trace without a proof of that operator-algebra theorem. The single-prime coordinate receiver
and its missing source construction remain distinct from a genuine simultaneous-descent theorem.

Source audit for C3b: the corpus already proves finite Euler gauges are holomorphic units and
finite-modification-invariant divisor charges have dense fibers (`FiniteGaugeTailCharge.lean`).
Thus finite-gauge invariance alone does not give a continuous projective-class-valued readout.
The proposed IRK proof must construct the source index and its topology, rather than silently
promote the divisor invariant to a continuous `K0` class.

Concrete missing map: the ordinary analytic crossed-product quotient by Xi has a relative
principal-divisor class, and multiplying Xi by a finite Euler unit preserves that class.
There is currently no constructed functor sending this relative analytic class to finite
projective classes in each prime/tail rotation algebra while preserving the local Chern charge.
Meromorphic conjugacy, holomorphic unit equivalence, and bounded rotation-algebra descent are
separate steps. The next cycle must attack this map directly.

Cycle 3 assessment: targeted corpus searches supplied Gelfond--Schneider and prime-logarithm
independence, but did not return the exact two-prime/tail trace-intersection theorem. These
arithmetic consequences are not claimed to be new mathematical knowledge beyond the literature;
the user's instruction excludes an external novelty search. The hard, potentially new source
result remains the construction of simultaneous/tail descent with its local Chern identification.
The Lean artifact below verifies the integrality mechanism without assuming RH or that source
construction.

Formal artifact: `formal/GaloisForLFunctions/RHTower/PrimeRotationTraceTailIntegrality.lean`,
225 lines, eight public theorems and one definition. Every scratch statement compiled. The final
actual-path `lake --old env lean` build passed without warnings and wrote fresh `.olean` and
`.ilean` files. Umbrella import appears exactly once next to the existing IRK leaves. The API
index refreshed successfully. `/tmp/irk-trace-tail-axioms.lean` passed: all nine public declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`. No added axioms, `sorryAx`, or
computational-reflection axiom appears. No projective-source existence theorem is claimed.

Current global lint exited 1 with two unrelated unreachable concurrent modules,
`SoninPrimePolarHeadMellin` and `SoninPrimePolarResidueExclusion`, plus existing large-file warnings.
No reported lint error concerns either owned IRK module. Preserve concurrent files; do not claim
a repository-wide lint pass. The four even-sector import errors recorded earlier are no longer
the current lint result.

Checkpoint: owned draft/API/search scratch files were removed; axiom scripts and the current lint
log remain in `/tmp`. Goal stays active. The next task is the actual Xi relative-index-to-projective
descent construction described above, including canonical trace compatibility and the Chern
identification with off-line multiplicity. Do not spend the next cycle refining this arithmetic
lemma or replacing that construction with estimates or ordinary eigenvalue counting.

## Cycle 4 — source audit and algebraic trace integrality

User's target remains irrational canonical-trace integrality for an actual Xi index,
with local Chern charge equal to off-line multiplicity. IRK is not retired. No numerical
experiment, external novelty claim, or RH proof is made in this cycle.

### Literal arithmetic source audited

`DeningerMeyerXiSpectralInclusion.lean` constructs a genuine map from the all-weight
Poisson quotient to compact-open Xi cohomology. It proves that every actual Xi divisor,
with all its multiplicity jets, occurs in the dual flow. Its comparison map is injective
if and only if `DeningerMeyerXiSpectralSynthesis`; that synthesis is a definition, not a
proved source property. No rotation-algebra projective structure is supplied there.

`CCMArithmeticPrimeFredholmOrientation.lean` defines its source cycle using a prime and
a nonzero integer grade. `CCMArithmeticPrimeFredholmTrace.lean` identifies its downstream
Xi label with a real horizontal orientation. This is a source-first critical-line
receiver, not a construction attaching a projective class to an arbitrary off-line
Xi divisor. Do not use either file to silently supply the missing IRK class.

### Exact algebraic integrality theorem — paper proof

Let lambda be any nonzero complex number. Let R_lambda be the finite quantum Laurent
algebra with basis v^b u^a, a,b in Z, and relation u v = lambda v u. For a matrix E over
R_lambda satisfying E^2=E, its unnormalized coefficient trace

    tau_n(E) = sum_i coefficient_(u^0 v^0)(E_ii)

is an integer r with 0 <= r <= n. This is an algebraic theorem; no positivity,
irrationality, finite-dimensional Hilbert-space representation, or spectral counting
is used.

Dependency-closed construction and proof:

1. Set K=C((v)), the field of formal Laurent series with exponents bounded below.
   Define sigma(sum_b c_b v^b)=sum_b c_b lambda^b v^b. Nonzero lambda makes sigma a
   field automorphism, with inverse obtained using lambda^(-1). The coefficient
   functional epsilon(f)=coefficient_v^0(f) satisfies epsilon(sigma^a(f))=epsilon(f)
   for every integer a. It is C-linear, but is not a ring homomorphism.

2. Form D=K((u;sigma)): expressions sum_{a>=A} f_a u^a with multiplication
   (f_a u^a)(g_b u^b)=f_a sigma^a(g_b) u^(a+b). Each coefficient of a product is a
   finite sum because both outer supports are bounded below. Associativity follows
   from sigma^(a+b)=sigma^a sigma^b and the finite triple-sum identity. The finite
   quantum Laurent algebra embeds by its explicit coefficient expansion.

3. D is a division ring. For nonzero f with leading outer exponent A and coefficient
   f_A, the monomial L=f_A u^A is invertible, with inverse
   sigma^(-A)(f_A^(-1)) u^(-A). Write L^(-1) f=1+h, where every outer exponent of h
   is at least one. The formal geometric series sum_{k>=0}(-h)^k is defined
   coefficientwise: only finitely many k contribute to each outer exponent.
   Finite telescoping proves that it is both a left and a right inverse of 1+h.
   Consequently (sum_k(-h)^k)L^(-1) is a two-sided inverse of f. There is no
   analytic convergence or bounded-operator assertion in this construction.

4. Define T(f)=epsilon(f_0). Then T(1)=1 and T is C-linear and cyclic. In detail,

       T(fg)=sum_a epsilon(f_a sigma^a(g_(-a)))
             =sum_a epsilon(g_(-a) sigma^(-a)(f_a))=T(gf).

   Both sums are finite: a is bounded below by the lower support bound of f and
   above by minus the lower support bound of g. The middle equality applies
   sigma^(-a), uses epsilon's invariance, and then commutativity of K. This is the
   crucial trace-extension step; no continuity of T is claimed.

5. Extend T to square matrices by summing diagonal entries. The same finite-sum
   argument gives T_n(AB)=T_n(BA), hence invariance under conjugation by every
   invertible matrix over D. An idempotent E on the finite right D-vector space
   D^n splits it as im(E) direct-sum ker(E): x=Ex+(x-Ex), with zero intersection.
   Choose bases of those two spaces. Their union is a basis of D^n, in which E
   is diag(I_r,0). Therefore tau_n(E)=T_n(E)=r. This proves the stated theorem.

This theorem supplies a concrete possible integrality mechanism, stronger than an
assumed integer-valued trace coordinate. It does not construct Xi's class, identify
the canonical C*-trace, or prove that the Xi class comes from R_lambda. The paper
argument is complete as written; Lean formalization of the skew Laurent division
ring and the theorem is NOT yet done. No beyond-corpus novelty is asserted.

### Source obligation exposed by the theorem

For the native prime rotation, the needed construction would send the local Xi
relative index to the image of algebraic K0(R_lambda) in the completed rotation
algebra while preserving the local Chern pairing. Matching the coefficient trace
above with the completed canonical trace must also be proved. Homotopy invariance
would then transfer the integer trace from an algebraic representative.

It is invalid to tensor the principal quotient O/(xi) directly into a meromorphic
field and call the result its divisor class: xi becomes invertible and that quotient
vanishes. Likewise its two-term rank-one free resolution has zero absolute Euler
class before any local multiplicity has been recovered. The source construction
must retain the relative boundary/clutching datum first. Algebraization of that
actual boundary class remains the hard open construction, not a new hypothesis
that has been discharged by the division-ring argument.

### Euler-phase homotopy attack — open, with a concrete obstruction

Deleting finitely many Euler factors preserves the local divisor. The all-minus
prime phase has Dirichlet series zeta(2s)/zeta(s), as the corpus proves on Re(s)>1.
Its meromorphic quotient continuation reverses zeta's local order on Re(s)>1/2,
away from s=1, since zeta(2s) is holomorphic and nonzero there. A source-level
projective homotopy connecting the two endpoints, preserving a local Chern readout,
would thus be powerful. Such a homotopy has NOT been constructed.

In particular, arbitrary intermediate phase twists must not be assumed meromorphic.
If a proposed local scalar deformation has logarithmic derivative

    z * (xi'/xi) + H_z, with H_z holomorphic near rho,

its residue is z*d, where d is xi's local order. The corpus theorem
`logDeriv_residue_of_meromorphicOrder` proves that a nonzero meromorphic germ has
integer logarithmic residue. Thus an irrational real z and d>0 obstruct precisely
that scalar meromorphic deformation. A projective construction would have to handle
this monodromy explicitly; calling the deformation meromorphic would assume away
the problem. This is a local diagnosis, not a proof that every Euler-phase path
has the displayed logarithmic derivative.

The existing Helson finite-prefix divisor theorem independently prevents upgrading
finite-prime agreement into a universal divisor-preserving continuous source map.
Xi's Poisson/Gamma/duality structure must enter the actual construction.

### Cycle 4 checkpoint

Corpus deep searches completed without partial-result flags. Their semantic matches
were mostly unrelated; exact Lean source inspection supplied the facts above. The
installed Hahn-series field construction is commutative, and the inspected skew
monoid/polynomial APIs do not already supply the required skew Laurent division
ring and trace. No new Lean declaration or placeholder was added in this cycle.
The previous two IRK leaves retain their earlier verified status; they were not
rebuilt because no source changed. The next substantive tasks are the relative
Xi boundary construction and the concrete skew-series trace formalization, with
source charge preservation audited at every completion/localization step.

## Cycle 5 — concrete skew-series construction

Implementation plan for the proved algebraic trace mechanism: realize K((u;sigma))
as a subring of ordinary Hahn series over additive endomorphisms of K. At degree n,
allow exactly coefficient operators x |-> a*sigma^n(x). Ordinary composition gives
the required skew product, and the existing Hahn support/convolution machinery
then supplies associativity. A formal geometric inverse stays in the same graded
coefficient groups. Nonzero leading coefficient operators are units, giving a
division ring. This avoids adding a division-ring existence assumption. Next,
specialize K=C((v)), construct the scaling automorphism, and prove the iterated
coefficient trace cyclic before using idempotent splitting. The independent Xi
relative-boundary construction remains open and must preserve divisor charge;
this foundation alone is not an RH proof.

Source compatibility check during construction: the coefficient field cannot be
the full meromorphic Mellin field with its additive translation automorphism.
If sigma(x)=x+1, an invariant additive functional epsilon satisfies
epsilon(x)=epsilon(sigma(x))=epsilon(x)+epsilon(1), forcing epsilon(1)=0.
Equivalently, in the skew ring, [u,x*u^(-1)]=1, so every cyclic trace kills 1.
This rules out extending a normalized trace across that full local-coordinate
field. The periodic scaling field C((v)), sigma(v)=lambda*v, has the explicit
invariant coefficient functional from Cycle 4 and avoids this obstruction.
Thus the necessary source map is a relative boundary/clutching construction
into the periodic algebra, not a trace-preserving embedding of all meromorphic
Mellin functions. IRK remains active; this diagnoses a specific invalid source
implementation without supplying the missing boundary map.

The concrete division-ring construction and coefficient trace now pass Lean in
their own actual-path leaf builds. The remaining idempotent argument is being
formalized through a rectangular factorization: E=A*B and B*A=I_r, obtained by
choosing a basis of the algebraic range of E. Cyclicity then gives
tau_n(E)=tau_r(I_r)=r. This is a finite free-module argument over the constructed
division ring, not a spectral counting estimate or a finite Hilbert-space model
for the irrational rotation algebra.

Cycle 5 completed the paper integrality mechanism in Lean:

- `HTGeometry/SkewLaurentOperatorDivision.lean`: 352 lines, 28 public declarations;
  explicit skew Laurent division ring, geometric inverse, and additive-translation
  unit-commutator obstruction.
- `HTGeometry/SkewLaurentCoefficientTrace.lean`: 225 lines, 22 public declarations;
  actual scaling automorphism, actual normalized cyclic iterated coefficient trace,
  and its exact constant-coefficient value on Laurent words.
- `HTGeometry/QuantumLaurentTraceIntegrality.lean`: 116 lines, five public declarations;
  rectangular idempotent splitting and the closed endpoint
  `quantumLaurentTrace_idempotent_eq_nat`.

The endpoint proves, for every unit parameter c over a field and every matrix
idempotent E over the constructed quantum Laurent division ring,

    exists r : Nat, sum_i quantumLaurentTrace c (E i i) = r.

There is no division-ring-existence, normalized-trace-existence, or spectral-model
premise. The equation E*E=E specifies the input idempotent. Thus the result applies
in particular to idempotents made from finite quantum Laurent expressions. The
paper argument from Cycle 4 now has a concrete formal algebraic realization.

All three actual-path `lake --old env lean` builds passed without warnings and
wrote fresh `.olean` and `.ilean` files. Each leaf is wired once into HTGeometry's
umbrella; no umbrella build was run. The `/tmp/irk-skew-axioms.lean` audit checked
all 55 public declarations and passed, with only `propext`, `Classical.choice`, and
`Quot.sound`. The exact endpoint is present in the refreshed research index.

Current global lint exited 1 solely on an unrelated unreachable module,
`GaloisForLFunctions.Hurwitz.JointAnchorContinuity`, plus existing large-file warnings.
No lint error concerns these three leaves. This supersedes the previous cycle's
Sonin import-error observation; it is not a claim of a repository-wide lint pass.

Scope audit: the trace constructed here is a formal-series coefficient trace. Its
agreement with a completed rotation algebra's canonical trace has not been
formalized, and no C*-projective Xi class or local Chern identification is supplied.
Most importantly, Xi's actual relative boundary has not been shown to algebraize.
RH remains unproved. No external novelty check or beyond-literature novelty claim
was made; this is a rigorous implementation of the stated algebraic mechanism.

Next source task: construct a boundary/clutching map retaining the local Xi divisor
while landing in the periodic rotation algebra. Direct extension across the full
additive meromorphic coordinate is ruled out by the new commutator theorem; its
positive survivor is the scaling-field trace and integrality theorem above. Do not
replace this remaining source construction with another arithmetic receiver,
spectral counting, or refinements of the already closed algebraic trace theorem.

## Cycle 6 — actual relative K2 boundary of the Xi transport

Source audit: `CircleArgumentPhaseRelativeIndex` constructs an actual scalar Hardy
boundary index and preserves the local multiplicity. Its winding is K1 data; no
identification with rotation Chern charge follows from that construction. The
literal Meyer quotient has full independent Xi jets and triangular prime dilation,
but no fixed-quotient imaginary-translation action has been constructed. A moving
quotient or determinant character alone would still leave the descent unproved.

The next concrete conjecture is a relative K2 source boundary, using the existing
`MeromorphicGermField` and `MilnorKTameSymbol` constructions. For a meromorphic
germ f and a holomorphic unit v, the tame boundary of {v,f} is v(rho)^ord(f).
Apply this to f(s)=Xi(s)/Xi(s+t) and v(s)=exp(-s log p). At an isolated Xi zero
rho of order d and a sufficiently small nonzero t, the two boundary factors at
rho and rho-t multiply to exp(-t log(p)*d). At the native rational imaginary
clock, this is the previously verified prime Weyl phase. This constructs a
boundary of an actual K2 class, rather than declaring a rank/Chern coordinate.

Paper proof of the needed germ tame data: meromorphic order descends to germs
and is additive on nonzero products. A germ of order zero has a unique nonzero
punctured limit; that limit is a multiplicative residue on the order-zero unit
group. If ord(a)>0, 1-a tends to 1. If ord(a)=0, 1-a has finite limit and hence
nonnegative order; positive order forces residue(a)=1. If ord(a)<0, a^-1 tends
to zero, so (1-a)/a tends to -1. This proves equal negative orders and residue
a/(1-a)=-1. These are exactly the three Steinberg obligations of `TameData`,
so its existing theorem gives an actual homomorphism K2^M(MeroGerm)->C^*.

Implementation plan: (1) construct this tame datum without existence premises;
(2) construct the two local Xi/prime symbols and identify their boundary phase;
(3) audit whether it has a legitimate periodic rotation descent. The phase is
not assumed trivial or algebraic. Global reciprocity cannot be invoked without
controlling the omitted boundary, especially the exponential prime unit at
infinity. No RH, off-line zero exclusion, or completed rotation class is claimed.

The concrete germ tame datum passed Lean. The Xi specialization retains the
complete signed divisor and its two-point prime phase. The next gluing obligation
is already visible on paper: these relative K2 symbols do not obey the ordinary
additive translation cocycle. Write v_rho(z)=exp(-log(p)*(rho+z)),
f_t,rho(z)=Xi(rho+z)/Xi(rho+z+t), and c_t=exp(-t log(p)). Then

    kappa(t+u,rho) + {c_t, f_u,rho+t}
      = kappa(t,rho) + kappa(u,rho+t).

Proof: f_(t+u),rho=f_t,rho*f_u,rho+t and v_(rho+t)=c_t*v_rho;
bilinearity of Milnor symbols gives the displayed equality. The correction's
tame boundary is c_t^(ord Xi(rho+t)-ord Xi(rho+t+u)). This is an exact
source-defined correction to composition, not an assumed projective module.
It must be retained by any periodic clutching construction.

A separate paper audit identifies the next risk: a finite polynomial in the
prime coordinate v=exp(-s log p) can reproduce a local divisor and the same
relative tame phase. Thus relative algebraization alone does not give a matrix
idempotent with nonzero Chern charge. The trace-integrality theorem applies to
K0 idempotents; the source just constructed lies in K2. Constructing and auditing
the map between those groups remains essential. No such map is presumed here.

An exact source decomposition sharpens that obligation. Let
Phi(rho)={v_rho,Xi_rho} and a(t,rho)={c_t,Xi_(rho+t)}. Bilinearity gives
kappa(t,rho)=Phi(rho)-Phi(rho+t)+a(t,rho). Consequently kappa-a is a strict
translation cocycle. On an isolated two-point Xi dipole its tame boundary is
one: the intermediate Phi(rho) cancels, and both outer Xi germs are units of
order zero. The nontrivial prime phase therefore resides exactly in a, the
clock correction. This is a constructive decomposition, not an argument that
the charge is zero. Any successful noncommutative clutching must carry the
clock correction into the rotation class; ordinary untwisting erases the
desired charge. Formalizing this decomposition is part of Cycle 6.

### Cycle 6 verified checkpoint

Both new leaves are fully checked at their actual paths:

- `HTGeometry/MeromorphicGermTameSymbol.lean`: 277 lines, 34 public declarations.
  Concrete integer germ order, multiplicative complex residue, all Steinberg
  clauses, actual Milnor K2 boundary, and its unit/divisor evaluation formula.
- `RHTower/PrimeRotationXiRelativeKTwo.lean`: 325 lines, 28 public declarations.
  Actual Xi/prime K2 symbols, exact signed multiplicity boundary, nonzero native
  clock class, exact composition correction, and the charge-transfer theorem
  `xiPrimeK2_dipole_charge_transfer` (line 298).

For the source class kappa, a sufficiently small nonzero t gives

    boundary(kappa(t,rho) + kappa(t,rho-t)) = exp(-t log(p))^d.

At the rational imaginary clock the boundary is the exact prime Weyl phase,
transcendental for every actual Xi zero. The new construction does not assert
that this phase is algebraic. The canonical untwisting kappa-a has boundary one
on the dipole, while a retains precisely exp(-t log(p))^d. The statement concerns
this explicit normalization; it is not a classification of every possible
noncommutative source construction.

Final actual-path `lake --old env lean` builds passed without warnings and wrote
fresh `.olean`/`.ilean` files for both leaves. Each is imported once by its area
umbrella. No umbrella/full build was run. `/tmp/irk-tame-axioms.lean` audited all
62 public declarations; the log contains exactly 62 reports and only `propext`,
`Classical.choice`, and `Quot.sound`. The exact endpoint is found by the lexical
research command. Deep source searches earlier in the cycle completed without
partial flags; their mostly unrelated semantic hits were checked against Lean
source rather than treated as applicability proofs.

Global lint currently exits 1 on three unrelated unreachable RHTower modules:
`CHMDStage1MultiplicativeResolventAndClampedBeam`, `LogSineClockTransform`, and
`LogSineQuantileClock`, plus existing large-file warnings. No lint error names
either new leaf. This supersedes Cycle 5's unrelated Hurwitz reachability error;
repository-wide lint is not reported as passing.

IRK remains active. RH is unproved. The remaining source theorem must carry the
actual clock correction into a completed rotation K0 class while establishing
integer canonical trace and the multiplicity Chern identification. The existing
formal-series idempotent trace theorem cannot be applied directly to this K2
class. The construction above works at critical-line zeros too, so an off-line
source hypothesis must come from a genuine relative construction, not a claim
that all these local K2 boundaries vanish.

Next audit candidate: the periodic-coordinate model F(v)=(v-v_rho)^d with
v=exp(-s log p), comparing F(v)/F(c_t v) against the actual Xi cocycle. Its
local tame boundary should agree while the omitted global boundary can differ.
This model comparison has not been formalized in Cycle 6 and is not used in
the verified results. The key task remains the K2-to-K0 source construction
with the clock correction retained. No route is retired and no beyond-literature
novelty claim is made.

## Cycle 7 — retaining the clock in the K2 source category

The ambient-to-K0 proposal has a concrete algebraic obstruction. For any
c in C^* and any meromorphic unit f, {c,f} in Milnor K2 is divisible by every
positive integer: choose an nth root b of c and use {c,f}=n{b,f}. Therefore
every additive integer-valued map on the full ambient K2 kills every clock
correction. In particular an additive Chern map on the full ambient group
cannot recover the required positive local multiplicity. This is a specific
failure of forgetting the fixed clock, not a retirement of IRK.

Positive replacement with a closed paper proof: fix the non-torsion native
clock multiplier c. In K2(MeroGerm), take the actual subgroup whose tame
boundary lies in c^Z. Boundary exponents are unique, so this subgroup has an
integer degree homomorphism. The symbol {c,z} has degree one. The degree map
is onto, its kernel is exactly the tame kernel inside the subgroup, and the
primitive symbol splits it. The actual Xi clock correction has degree equal
to analytic Xi order at the transported point; the isolated Xi dipole has
degree d. Dividing the clock in the ambient field generally leaves this
subgroup. This source retains the clock before any map to rotation K0.

Plan: formalize (1) ambient divisibility and integer blindness, (2) this
marked tame subgroup and its exact integer degree, (3) actual Xi membership
and multiplicity. Then seek projective realization from the marked source,
without assuming an impossible degree-preserving homomorphism on all ambient
Milnor K2. No completed rotation class or RH proof is claimed by this plan.

The positive replacement also has a coherent clock-refinement law. If c=d^k,
the same ambient class with c-degree n has d-degree k*n. For the native clocks,
c_(kq)^k=c_q. Thus forgetting the clock destroys the integer grading, while
retaining the clock family gives an exact integer degree in each fiber and
the appropriate scaling under refinement. An ambient half of the primitive
{c,z} class lies outside its fixed-clock subgroup; this proves that the
restriction is substantive. These statements have paper proofs from the
explicit root and tame identities and are included in the formalization.

Corpus bridge search completed with partial=false; it located the closed
rotation algebra and compactness results, but no applicable K2-to-K0 map.
The divisibility deep search returned useful hits with partial=true because
the decomposition model returned malformed JSON. Its inventory was complete
(72344/72344 files, no pending files). Available hits, direct Lean source,
and actual leaf checks are used; no missing decomposition output is presumed.

### Cycle 7 verified checkpoint

The ambient integer-map obstruction and its positive replacement are both
formalized without adding existence assumptions:

- `HTGeometry/MarkedMeromorphicKTwo.lean`: 226 lines, 24 public declarations.
  Explicit complex unit roots prove divisibility of every constant/germ
  symbol. `constantMeroSymbol_integerHom_zero` (line 54) proves every ambient
  additive integer map kills such symbols. `markedTameK2` is the actual
  preimage of the clock's integer powers under the concrete tame boundary.
  Its unique exponent is an additive degree, onto Z, with kernel exactly
  the tame kernel. `{c,z}` supplies degree one and splits the quotient.
  `markedTameDegree_not_extend` proves no ambient integer extension exists.
  `markedTameCoordinate_half_outside` gives an explicit divisibility failure
  of the marked subgroup. Clock changes preserve the ambient class and scale
  degree by the integer exponent.
- `RHTower/PrimeRotationMarkedXiSource.lean`: 145 lines, 15 public declarations
  including the source abbreviation. Native clock infinite order is proved
  from the established prime-phase transcendence theorem. The actual Xi
  clock correction has marked degree equal to full analytic multiplicity.
  `xiPrimeDipole_marked_source` (line 79) constructs, for every rho, a nonzero
  clock denominator and a marked representative whose underlying class is
  the literal Xi dipole and whose degree is its analytic order. No scalar
  coordinate is inserted as a substitute for that source class.
  Native refinement c_(kq)^k=c_q and its exact degree scaling are proved.

Final actual-path `lake --old env lean` builds passed warningfree and wrote
fresh `.olean`/`.ilean` files. Each leaf is wired once into its area umbrella;
no umbrella/full build was run. `/tmp/irk-marked-axioms.lean` checked all
39 public declarations; exactly 39 reports, only `propext`, `Classical.choice`,
and `Quot.sound`. The exact source endpoint is present in the lexical research
index. Global lint currently exits 1 solely on the unrelated unreachable
RHTower module `CHMDStage2KleinGordonTransmutationAndTContourBochner`, plus
existing large-file warnings. This supersedes Cycle 6's three reachability
errors; repository-wide lint is not reported as passing.

The failed ambient-domain proposal has a positive survivor with both a paper
proof and complete Lean proof. IRK itself is not retired. The construction
still works at every Xi point, including critical-line zeros. It supplies a
clock-dependent integer degree on a genuine subgroup of the source K2; it
does not prove canonical rotation trace integrality or identify this degree
with an actual rotation Chern pairing. The next projective realization must
use this marked domain, retain its refinement law, and obtain its off-line
input from the arithmetic source. Extending an integer Chern map to all
ambient complex K2 is now disproved and should not be retried.

Next conjecture: construct the rotation-projective realization of the marked
Xi source with its clock correction retained, and isolate the arithmetic
condition forcing its canonical trace to be integral on off-line source
classes. A generic degree-preserving realization on the whole marked group
cannot itself establish integral trace, since the degree-one primitive is
already present. RH remains unproved; the goal remains active.

## Cycle 8 — canonical trace on the concrete completed rotation algebra

The formal-series integrality theorem uses a genuine division ring, but its
coefficient trace has not yet been compared with a trace on the concrete
norm-closed rotation algebra. That missing comparison is a bridge in IRK.
The marked Xi K2 source still needs projective realization; constructing the
trace does not supply that realization.

Paper plan: average diagonal matrix coefficients on basis vectors e_n,
0 <= n < N. Every average is complex linear and bounded by operator norm.
A fixed ultrafilter refining atTop gives a limit for every bounded operator,
since closed bounded subsets of C are compact. Limits form a continuous
linear functional, normalized at identity and positive on A* A. On a Weyl
word its value is zero unless the shift exponent vanishes; then it is the
Cesaro limit of exp(i b t n). For an infinite-order clock this is precisely
the constant-coefficient functional.

Finite Weyl spans form a star algebra by exact multiplication and inverse
formulas. Its norm closure is the existing concrete rotation algebra. Word
trace values give cyclicity, then bilinearity and continuity extend it to
the whole closure. Density gives uniqueness with these word values. Next
compare finite Weyl sums with formal quantum Laurent words; faithful
coefficient identification is needed before transporting idempotent
integrality. No trace-range or Xi projectivity premise is added.

Both initial deep corpus searches completed with partial=false and no
reported errors. Hits include compact-ideal trace cost and scalar trace
coordinates; neither is the needed canonical tracial state. Claims are
checked against actual Lean source and the active toolchain.

Cycle 8 intermediate check: canonical trace, positivity, word values,
cyclicity on the completed algebra, and uniqueness with those word values
have passed Lean. The finite Weyl span is a star algebra with the required
closure. The next bridge has a dependency-closed paper proof: prove word
linear independence by the trace pairing tau(W_i^* W_j)=delta_ij; use its
coefficient representation to map the finite operator algebra into the
quantum Laurent division ring at c=exp(-it). Exact multiplication agrees
in both representations. The ground field acts centrally on the division
ring, and its coefficient trace is linear. Consequently this map preserves
trace and sends actual matrix idempotents to formal matrix idempotents.
The existing division-ring factorization then yields integer canonical
trace for actual finite Weyl matrix idempotents. Infinite norm completion
alone does not supply finite Laurent idempotent representatives; that
remains a substantive arithmetic requirement on the Xi source.

The complete finite-operator transfer, including injectivity of its algebra
map and integer canonical trace of matrix idempotents, passed its scratch
Lean check. The actual-path leaf audit and native-prime specialization are
next. Sign convention is explicit: concrete word is V^b U^a, with product
phase exp(-i*a*d*t); the formal parameter is exp(-it). At native frequency
t=-log(p)/q this formal parameter is the inverse of the marked tame clock.
Any future Chern identification must respect this orientation; no such
identification is silently inferred from the trace comparison.

### Cycle 8 verified leaf checkpoint

All four actual-path leaves passed warningfree, with fresh olean/ilean:

- `HTGeometry/PaperRotationCanonicalTrace.lean` (390 lines, 19 public
  declarations): actual normalized positive continuous trace, cyclic on
  the concrete norm-closed rotation algebra. Finite Weyl star algebra,
  closure identification, trace orthogonality, and word independence.
- `HTGeometry/QuantumLaurentScalarAlgebra.lean` (96 lines, 9 public
  declarations): actual central ground-field algebra structure, exact word
  multiplication, and scalar linearity of the formal coefficient trace.
- `HTGeometry/PaperRotationPolynomialTraceIntegrality.lean` (185 lines,
  11 public declarations): actual faithful algebra map from finite concrete
  Weyl operators to the division ring; exact canonical/coefficient trace
  comparison; natural-number trace of every matrix idempotent.
- `RHTower/PrimeRotationCanonicalTraceIntegrality.lean` (71 lines,
  5 public declarations): native prime specialization, with all positive
  clocks parameterized as q+1 and irrationality proved internally. Line 46
  is the actual-idempotent integer-trace endpoint. Differences of actual
  idempotents have integer trace too.

Each leaf is imported once by its area umbrella. No full or umbrella build
was run. The lexical corpus search finds the native endpoint at its actual
path. Global lint exits 1 on three unrelated unreachable RHTower modules:
`EvenSectorPolarRigidity`, `EvenSectorPolarStripCeiling`, and
`EvenSectorPoleFreeNodeTests`, plus 381 existing large-file warnings.
No owned leaf has a lint error. Axiom audit is recorded below when finished.

The formal-series/canonical-trace comparison is now closed for the actual
finite Weyl algebra. It is not an assertion of integer trace for every
completed rotation projection. No off-line multiplicity was eliminated:
there is still no constructed projective class from the marked Xi source,
no actual Chern/multiplicity identification, and no arithmetic proof that
such a class has a finite Weyl representative. RH remains unproved.

Next conjecture stays at this obstruction: build the marked Xi source's
rotation-projective realization while retaining its clock correction, then
use actual Poisson/Mellin arithmetic structure to place its off-line class
in the image of the finite Weyl algebra (or prove an equally strong source
trace theorem). The degree-one primitive in the generic marked source
prevents a uniform finite-algebra realization preserving degree. The
construction must use Xi's global arithmetic input and the off-line
condition. Do not replace this missing producer by a structure field or an
assumed Chern equality. The established orientation convention must be
retained in that construction.

Final dependency audit: `/tmp/irk-canonical-axioms.lean` generated exactly
44 public-declaration reports; all use only `propext`, `Classical.choice`,
and `Quot.sound`. No errors. Evidence retained in
`/tmp/irk-canonical-axioms.log`; lint evidence retained separately. All four
olean and ilean timestamps are newer than their sources. Cross-session
checkpoint saved as `research/irk-canonical-trace-integrality-2026-10-15`.
Owned exploratory source and search files are cleaned after all processes
finish. IRK goal remains active and RH remains unproved.

## Cycle 9 — an actual arithmetic module for the rotation algebra

Current source audit: finite canonical trace integrality is proved, while
no actual rotation-projective Xi source or Chern pairing is available in
the retrieved Lean sources. The literal Meyer target/Poisson quotient has
an exact centered real dilation flow and surjects onto every finite full
Xi jet packet. Sparse prime sampling is insufficient to recover the global
Poisson boundary; the existing global Calderon defect proves that gap.
No sparse replacement is used here.

Construction with a closed paper proof: for a complex vector space M with
an integer flow T_b, use the actual finite-support clock family Z ->_0 M.
The ordered word W_(a,b) sends delta_n(m) to
  delta_(n+a)(exp(i*b*t*(n+a)) T_b(m)).
The exact composition is
  W_(a,b) W_(d,e) = exp(-i*a*e*t) W_(a+d,b+e).
Therefore the independent finite Weyl basis extends these operators to a
literal representation of the concrete finite rotation algebra. At the
native prime frequency, take T_b to be centered Meyer dilation at
-b*log(p). This constructs the action from the actual arithmetic quotient;
no fixed finite spectral packet is required to carry an impossible Weyl
pair.

Full Xi jet evaluation intertwines centered dilation. Its coefficientwise
extension gives a surjective equivariant map from the integer Meyer family
onto the integer family of every finite full Xi jet packet. The latter has
an explicit finite free cover: its generators are the packet basis vectors
at clock zero, and W_(n,0) produces every clock translate. Thus the retained
multiplicity is carried by a genuine finitely generated rotation module,
rather than a declared rank/Chern coordinate. Construct the operators,
representation, equivariant quotient, and finite free cover in Lean. This
does not assert projectivity; the relation module and relative K-class must
be audited next.

The projectivity search was partial=true due to malformed local-model JSON;
no missing answer is assumed. Other source, Chern, and induced-Weyl searches
finished with partial=false. No numerical experiment or external search.

Cycle 9 intermediate proof checkpoint: the generic induced word law,
representation, naturality, and equivariant finite free cover passed a
warningfree scratch Lean check. The arithmetic specialization also records
its exact relationship to the original source complex: integer families of
the all-weight target map onto the integer Meyer quotient, with kernel
exactly the coefficientwise literal Poisson boundary. The target rotation
action will be shown to preserve that exact boundary, not a prime-sampled
surrogate. Neither spectral synthesis nor an off-line vanishing assumption
is used.

The finite free cover is deliberately not called a projective realization.
Its relation matrix is the next specific algebraic problem: in a packet
basis B it should be V*I - [T_1]_B, acting in the finite free module. An exact
kernel proof would produce a genuine finite free resolution and permit a
relative K-class/tame-boundary comparison with the marked Xi source. That
comparison and conversion to the required completed projective class are
still unproved.

Cycle 9 relation proof, before formalization: for any invertible integer
flow T on M, let E(delta_b m)=T_b m and
D(delta_b m)=delta_(b+1)m-delta_b(T_1 m). Then ED=0 by the group
law. Each delta_b m-delta_0(T_b m) lies in range(D), by upward
induction using D(delta_b m), and downward induction using T_(-1).
Finite linearity gives x-delta_0(E x) in range(D), hence ker(E)=range(D).
D is injective: at the smallest support index k, (Dx)_k=-T_1 x_k,
which is nonzero whenever x_k is, since T_1 is invertible. E is onto
via delta_0. Thus this is an exact length-one sequence, for the whole
flow, retaining every Jordan jet. At fixed outer Weyl index a, scalar
rescaling replaces T_1 by exp(i*a*t)T_1. This is the coefficient-level
identity needed for the actual noncommutative finite presentation.
The latest deep resolution search is partial=false, with all inventoried
files indexed; compiler freshness is mixed. Retrieved Barnes resolution
handles a commutative principal quotient, not this vector-valued quantum
relation. No applicable kernel theorem found among the retrieved hits.

Cycle 9 continued: the actual Meyer specialization passed a warningfree
actual-path Lean check and is installed as
`RHTower/Deninger/DeningerMeyerPrimeRotationModule.lean`. The generic Laurent
resolution also passed its final actual-path check in
`HTGeometry/IntegerFlowLaurentResolution.lean`.

Full noncommutative presentation proof: the independent Weyl basis and a
finite packet basis identify A^m with outer/inner finite Laurent families.
At outer index a the flow is twisted by exp(i*a*t). The coefficient
relation is shift-exp(i*a*t)T_1. Precomposing by the invertible row phase
exp(-i*a*t) turns it into the actual right matrix V I-[T_1]_B.
This phase is necessary because words are V^b U^a. Thus its injectivity
and exact kernel follow from the already proved Laurent resolution,
while the displayed right matrix proves left A-equivariance. This gives
0 -> A^m -> A^m -> induced packet -> 0, not a projective identification
of the quotient. Formal transfer is in progress in owned scratch.

Topological consequence to investigate, not a proved Lean claim: the
ordinary Euler K0 class of this equal-rank free resolution is zero. A
multiplicity invariant must retain its differential/relative class and
compare that class with the marked Xi K2 source. Merely discarding the
differential and assigning a rank cannot supply the missing Chern pairing.
The arithmetic Poisson complex must provide the additional comparison;
it has not been inferred from finite packet data alone.

Next explicit conjecture, after the finite presentation: for one actual
zero rho with full jet multiplicity d, let D be its centered prime-flow
matrix. The proved binomial formula is triangular with constant diagonal
lambda=exp(-log(p)*(rho-1/2)), so det(X I-D)=(X-lambda)^d. Its meromorphic
germ at lambda gives a literal K2 symbol {nativeClock, det(X I-D)} with
marked tame degree d. Compare this with the actual Xi marked class in the
marked quotient (equality of tame degrees gives quotient equality, not
ambient K2 equality). Then construct and prove the required topological
transgression from the differential, rather than define its Chern value
to be d. Native clock is inverse of the concrete quantum multiplier, so
orientation must be checked explicitly.

Search checkpoint: deep relative-K/Chern query returned partial=false but
no applicable relative rotation boundary construction among its retrieved
hits. A lexical query also found no such construction. Deep Xi determinant
query returned partial=false and useful triangular determinant machinery
(`Matrix.det_of_upperTriangular` in the retrieved proof); no ready theorem
for this actual centered Xi packet determinant was found. The existing
regularized Xi determinant identity is a different global object and is
not used as the finite relation determinant without a proof.

The complete generic finite-free resolution, including left equivariance,
explicit relation matrix, injectivity, and exact kernel, passed warningfree
scratch and final actual-path Lean checks. Installed in
`HTGeometry/RotationInducedFiniteFreeResolution.lean`. The phase correction
is proved, not dropped. Native specialization is being checked at
`RHTower/Deninger/DeningerMeyerPrimeRotationResolution.lean`.

Global lint ran and exited 1: an unrelated in-progress module
`RHTower.EvenSectorPoleFreeTwoSidedGrowth` is unreachable from its umbrella;
large-file warnings also remain. All five owned IRK leaves each have one
umbrella import. The observed lint result is retained in
`/tmp/irk-arithmetic-lint.log` (summary, not full stderr capture).

Native specialization passed its warningfree final actual-path Lean check;
all five new leaves have fresh olean/ilean artifacts. The dependency audit
covers exactly 77 public declarations; its process is still running.

Refinement of the next determinant comparison: pull the relation pencil
back to the original Mellin coordinate, F_rho(s) =
det(exp(-log(p)*(s-1/2)) I - D_rho). For a singleton full jet block,
F_rho has order d at rho because the exponential coordinate has nonzero
derivative there. Hence F_rho/Xi is a local meromorphic unit and
{clock,F_rho}-{clock,Xi} lies in the actual tame kernel. This is a concrete
source comparison in the marked quotient, with a locally invertible
coordinate change, rather than matching declared integer coordinates.
It still does not construct the required topological Chern transgression.

Cycle 9 final dependency audit passed: 77/77 public declarations, exact
coverage, with only propext, Classical.choice, and Quot.sound. No errors or
warnings. Evidence: `/tmp/irk-arithmetic-axioms.lean` and
`/tmp/irk-arithmetic-axioms.log`; expected names retained separately.
All five actual-path leaf checks passed warningfree, every leaf is imported
once, and all olean/ilean artifacts are fresh. Completed owned exploratory
sources and old searches are cleaned after their processes exited. The
next useful search is retained as `/tmp/irk-xi-characteristic-search.json`.
IRK and the unconditional RH goal remain active. The topological
transgression and its Chern/multiplicity identity are not proved.

## Cycle 10 — relation determinant to the marked arithmetic source

Previous cycle is verified progress. Mission remains unconditional fully
Lean RH via IRK. Current conjecture verdict: BRIDGE. The finite determinant
comparison is a concrete missing source identification, not a claim of a
new general determinant theorem or a completed topological solution.
External novelty audit is omitted under the user's explicit corpus-only
instruction. The hard target remains a source-produced topological
transgression, with its Chern pairing proved from the Poisson complex.

Exact bridge proof: select one actual Xi support point rho, multiplicity
d, and restrict the actual full-packet centered flow to its d jet slots.
The displayed binomial action is lower triangular: row k uses only rows
k-i <= k; its diagonal is exp(c*(rho-1/2)). Hence the actual relation
pencil det(z I-D(c)) equals (z-exp(c*(rho-1/2)))^d. This holds for every
c and includes all nilpotent jet terms. With c=-log p, pull z back by
s -> exp(-log p*(s-1/2)). Its derivative is -log p times a nonzero
exponential, hence nonzero since p>=2. The determinant germ has order d.
Xi at rho has order d by the actual divisor multiplicity definition, so
their ratio is a meromorphic unit of order zero. Pairing the two germs
with the same native clock gives equal actual tame boundaries and the
same class in the marked quotient. All definitions will use the proved
actual packet matrix, not a surrogate diagonal matrix.

Attack: this comparison alone cannot prove RH. The marked quotient has
primitive degree-one elements independently of Xi; matching tame degrees
does not produce a finite rotation idempotent or its Chern class. No such
projective realization is inserted as a hypothesis. [OPEN CORE] remains
the arithmetic topological transgression and trace-integrality mechanism
for its image. Continue attacking that core after the source comparison.

Cycle 10 source comparison passed scratch Lean: the literal actual flow
matrix, its equality with the finite-free relation coefficients, the full
pencil determinant, its Mellin pullback order, the order-zero ratio and
nonzero limit, equality with the Xi clock correction in the marked tame
quotient, and comparison with an actual isolated Xi dipole. No off-line
assumption was needed for this source identification. Native clock versus
quantum multiplier orientation is included in the final actual-path check
of `RHTower/PrimeRotationXiDeterminantSource.lean`.

Direct topological audit: assigning the ordinary Euler class to this
resolution loses the differential and gives zero before any Chern pairing.
The positive replacement is the now-proved determinant/tame comparison.
A genuine next construction must retain both derivations of the rotation
algebra and its actual canonical trace, so that the Chern value is a cyclic
pairing computed from an idempotent. The available generic source currently
provides a cyclic one-cocycle, not the required rotation two-cocycle.
Do not substitute the marked degree itself for that Chern pairing.

## Cycle 11 — actual cyclic pairing required by the transgression

Conjecture/bridge target: construct the two coordinate derivations on the
concrete finite Weyl algebra, and its actual canonical-trace cyclic
2-cocycle phi(A,B,C)=tau(A*(D1(B)*D2(C)-D2(B)*D1(C))). This is an
operative pairing to be evaluated on an eventual source idempotent; it
is not a declared integer Chern coordinate. Generic cyclic one-cocycle
machinery exists. Search for a ready commuting-derivation two-cocycle is
running; no matching actual rotation construction found in the audit.
Verdict BRIDGE: standard derivation/cyclic theory, required here to remove
an unconstructed Chern interface. No novelty claim for the generic law.

Dependency-closed paper proof: set D_(u,v)(W_(a,b))=(a*u+b*v)W_(a,b).
Finite Weyl independence defines the linear operator; additivity of the
integer word indices proves Leibniz with the exact quantum multiplier.
All such directional derivations commute. The canonical trace annihilates
them since its only surviving word is W_(0,0), whose derivative is zero.
For commuting derivations D,E and trace tau annihilating both,
D(b*E(c))-E(b*D(c))=D(b)*E(c)-E(b)*D(c).
Integration by parts gives phi(a,b,c)=phi(b,c,a). Expanding the three
Leibniz terms in the Hochschild boundary leaves tau(a*(D(b)*E(c)-
E(b)*D(c))*d)-tau(d*a*(D(b)*E(c)-E(b)*D(c)))=0 by trace cyclicity.
Trilinearity follows from linearity of the operators and tau. These are
actual cyclic cocycle identities; homotopy invariance of an idempotent
pairing and the arithmetic source transgression remain separate tasks.

Cycle 10 actual-path source leaf passed warningfree, including the inverse
native-clock orientation. Cycle 11 generic cyclic/Hochschild identities
and actual Euler derivations passed the first scratch check; proof-binder
plumbing for the trace is being corrected without heartbeat changes.

Stronger positive pairing test, paper proof: set X=V^(-1)U^(-1), Y=U,
Z=V and q=exp(-it). In the actual tensor Hochschild boundary
b(a,b,c)=ab tensor c-a tensor bc+ca tensor b,
b(X,Y,Z)=q*b(X,Z,Y), using XY=q*YX, YZ=q*ZY, ZX=q*XZ.
The constructed cocycle has values phi(X,Y,Z)=1 and
phi(X,Z,Y)=-q^(-1). Therefore its value on this quantum cycle is 2.
It cannot be a Hochschild coboundary: any linear functional on the
boundary tensor module would give 1=q*(-q^(-1))=-1. This proves genuine
nontriviality of the actual cochain, without postulating a Chern coordinate.
The map from the arithmetic marked source to this pairing is still open.

Cycle 11 actual-path final check passed warningfree, including scalar
normalization in all three slots. Both new leaves are wired into their
umbrellas. Global formal lint passed. The 51-public-declaration axiom audit
is running. No projective realization, integer Chern normalization, or RH
conclusion has been inserted.

Anti-theatre/anti-laziness audit: these cycles close concrete source and
pairing bridges; no scientific novelty claim follows from Lean coverage.
The arithmetic source-to-projective-class theorem remains the hardest
open problem. Scalar-clock substitution fails; its positive survivor is
the proved nontrivial quantum commutator cycle. Ordinary Euler K0 erases
the resolution differential. Next retain that differential on a circle:
for rho to the right of the critical line, the actual full relation pencil
has a nonvanishing homotopy to z I, hence determinant to z^d. On the left,
it contracts to its constant flow term. This supplies a genuine source
boundary class before a proposed quantum secondary transgression. It does
not provide an integral-trace arithmetic lift. No pivot from IRK.

## Cycle 12 — actual relation boundary homotopy

Exact conjecture: write D for the actual full centered prime-flow matrix
and lambda=exp(-log(p)*(rho-1/2)). Its lower-triangular diagonal is lambda.
For Re(rho)>1/2 and z on the unit circle, zI-sD has determinant
(z-s*lambda)^d, nonzero for every 0<=s<=1. At s=0 it is zI and at s=1
it is the literal relation matrix. For Re(rho)<1/2, s*zI-D has determinant
(s*z-lambda)^d, nonzero for 0<=s<=1, joining constant -D to the relation.
These are explicit continuous homotopies of invertible matrices. The
finite nilpotent jet terms are retained. The corresponding determinant
boundary maps therefore have the homotopy classes z^d on the right and
constant (-lambda)^d on the left.

Paper proof: norm(lambda)=exp(-log(p)*(Re(rho)-1/2)); log(p)>0. Thus it is
strictly below one on the right and strictly above one on the left.
Multiplying the actual triangular flow by s multiplies every diagonal by
s, so triangular determinant yields the displayed formulas. If a right
pencil determinant vanishes, z=s*lambda, contradicting norm z=1 and
norm(s*lambda)<=norm(lambda)<1. The left case would force
norm(lambda)=s*norm(z)<=1, also impossible. Entrywise continuity is
polynomial in s,z. This is a BRIDGE in topology, not new general winding
theory; its role is identifying the actual source boundary. The missing
quantum transgression and global Poisson integrality remain OPEN CORE.

Cycle 12 scratch found only elaboration/rewriting issues, not a failed
mathematical claim. The source coordinate uses the REAL logarithm; an
unrestricted simp converted its cast to a complex logarithm, so the proof
now uses only the explicit real/imaginary-part rules. Matrix continuity
requires an explicitly supplied parameter map. The Cycle 10/11 axiom
script initially used the path namespace GaloisForLFunctions.RHTower;
actual declarations live in RHTower. That audit script has been corrected;
the failed run already confirmed the 31 cyclic declarations use only
propext, Classical.choice, Quot.sound.

Hard-obstacle attack while checking: the full global Poisson source has
actual finite Xi quotient packets, but the canonical half-density
completion makes every off-line packet entirely vertical (existing
DeningerMeyerHalfDensityFiniteXiJetVerticalDefect, lines 333-407). Hence a
bounded extension of those packet observations cannot be silently used
to construct the projective class. The finite Weyl integral-trace theorem
also cannot be silently extended to the C* completion. A resolvent
already exposes the comparison issue: for V on the unit circle, the
canonical constant term of V/(V-lambda) is 1 when |lambda|<1 and 0 when
|lambda|>1, whereas a fixed formal expansion at V=0 gives 0 for every
nonzero lambda. The difference is the boundary winding. This is a paper
observation, NOT yet a Lean theorem, and does not prove a source lift.
A successful arithmetic transgression must control that discrepancy
using the literal global Poisson boundary. Generic finite-flow data
alone admit arbitrary complex characters and cannot enforce RH.

Cycle 12 scratch now passes warningfree. The leaf
RHTower/PrimeRotationXiBoundaryHomotopy.lean is installed and wired;
actual-path final check is running. It proves continuity, invertibility,
endpoints, and both actual determinant boundary winding identities.

## Cycle 13 — trace discrepancy at the resolvent transition

Conjecture to attack the completion step: the finite Weyl formal lift
continues to identify the canonical operator trace after adjoining an
off-circle resolvent. Verdict FALSE, with an exact positive survivor.
For 0<|lambda|<1 and an infinite-order rotation clock V, set
S=sum_{n>=0} lambda^n V^(-n). This is norm convergent. Then
(1-lambda V^(-1))S=S(1-lambda V^(-1))=1. The actual resolvent is
R=SV^(-1), and V R=S, with canonical trace 1 because every nonconstant
rotation word has zero trace. Meanwhile in the fixed formal Laurent field
at v=0, v/(v-lambda) has order 1, so its constant coefficient is zero.
Thus the finite-word trace comparison cannot extend across this rational
inverse. The discrepancy is exactly the positive boundary degree. For
|lambda|>1 the analytic expansion at v=0 is valid and the discrepancy is
zero. The full Xi jet determinant multiplies the boundary degree by its
actual multiplicity as proved in Cycle 12.

The paper proof is the geometric series identity, canonical trace
continuity and the formal valuation law. This is a BRIDGE/obstruction,
not a novelty claim or retirement of IRK. Positive salvage is an explicit
integer-valued relative trace discrepancy. The next hard conjecture must
control this discrepancy using the global arithmetic Poisson complex;
assuming a trace-preserving extension would conceal the desired result.

Cycles 10-12 verified: all three actual source leaves passed warningfree
with fresh olean/ilean, each imported once by its umbrella. Combined audit
checked all 71 public declarations: only propext, Classical.choice,
Quot.sound; no missing declarations, errors, or sorryAx. Evidence:
/tmp/irk-determinant-cyclic-axioms.lean, .log, and
/tmp/irk-determinant-cyclic-public.txt. The initial failed audit was a
namespace error in the scratch audit, now corrected and rerun successfully.

Cycle 13 first scratch proved the actual geometric inverse, both inverse
identities, and the canonical logarithmic trace=1. The formal Laurent
valuation proof had one remaining coercion equality 0=(0:WithTop Z), now
fixed. The quantum division-ring comparison and the outside-circle
inverse/zero-trace classification have been added to the next scratch run.

Cycle 13 extended scratch passed warningfree: actual bounded inverses on
both components, their logarithmic canonical traces (inside 1, outside 0),
fixed formal Laurent constant term zero for every nonzero parameter,
actual quantum-division-ring formal trace zero, and the exact discrepancy
classification. No heartbeat or recursion limits were raised. A uniform
statement using Ring.inverse and a native full-Xi-diagonal specialization
are being checked next.

Global lint rerun currently fails only at unrelated
RHTower.ThetaRenewalReflectedArithmetic, absent from its umbrella. Owned
leaves have no reported lint failures. Do not claim the global gate passed
at this later snapshot merely because an earlier snapshot passed.

Native specialization paper proof: substitute the actual prime-flow
matrix diagonal lambda into the uniform rational discrepancy. On the
right each diagonal contributes 1; on the left each contributes 0. Sum
over all actual jet slots, retaining full multiplicity d. Cycle 12 proves
the same integer is the boundary winding of the full relation matrix,
including its nilpotent entries. Thus the actual relative trace defect
is precisely that winding. This DOES NOT identify the defect with the
canonical trace of a rotation K0 class: that would be a new, unproved
arithmetic trace identity. Generic complex characters have the same
relative defect and cannot force RH by this calculation alone.

Cycle 13 actual-path check of
HTGeometry/PaperRotationRationalTraceDefect.lean passed warningfree with
fresh olean/ilean, including uniform Ring.inverse statements. It is wired
once into HTGeometry.lean. Native Xi specialization scratch is now running.

Anti-theatre answers: (1) scientific novelty unestablished; completed
results are exact bridges and an obstruction to the proposed trace
extension, (2) standard homotopy/geometric-series machinery was necessary
but not new mathematics, (3) no claim that formalization or this routine
machinery itself solves the research problem, (4) formal source frontier
moved from a marked degree to actual boundary topology and an explicit
analytic/formal trace discrepancy, (5) stay on IRK and zoom into the
global arithmetic regulator. Anti-laziness: (1) proved new corpus links,
not yet new external scientific knowledge; (2) no effort barrier was used;
(3) the still-unsolved core is global Poisson descent to a projective
class with the required trace identity; local generic-flow bridges do
not settle it; (4) corpus deep searches were run and source applicability
checked. Next cycle must use literal global Poisson range relations.

Structural constraint on the next conjecture: arbitrary complex
characters already admit the finite-flow resolution, boundary class and
integer relative trace defect. Therefore no theorem using only that
local data can rule out off-line Xi multiplicity. It must use a property
of the global arithmetic Poisson source absent from generic characters.
Nor does the integer relative trace defect equal a rotation-projective
canonical trace by definition. That equality or a suitable replacement
requires a constructed arithmetic regulator and an actual proof.

The rational resolvent leaf now also proves both explicit inverses belong
to the actual norm-closed rotation algebra, via its closedness and finite
Weyl power sums. Its final actual-path check including these four
membership theorems passed warningfree. Native Xi actual-path check is
running; combined audit will include 107 public declarations.

Next exact construction under consideration (BRIDGE, no novelty claim):
build an actual nontrivial rotation projection and its trace/Chern values
from explicit periodic coefficient functions, to expose the trace change
in a genuine secondary class rather than coordinates. For 0<alpha<1/2,
0<epsilon<alpha and alpha+epsilon<1, take a continuous ramp h from 0 to 1
on [0,epsilon], f=h there, f=1 on [epsilon,alpha], f=1-h(x-alpha) on
[alpha,alpha+epsilon], zero elsewhere modulo one; let g=sqrt(h(1-h)) on
the descending interval and zero elsewhere. On the actual clock lattice,
P=f(x)+g(x)U+U^(-1)g(x) is a projection because g(x)g(x-alpha)=0,
g(x)(f(x)+f(x-alpha)-1)=0, and
f(x)^2+g(x)^2+g(x+alpha)^2=f(x). Its canonical trace should be alpha,
using the already-proved word trace and continuous functional calculus.
An endpoint-flat rational ramp h(u)=u^4/(u^4+(epsilon-u)^4) makes g
explicit and differentiable enough for the cyclic pairing. Orientation
must be checked against the already-proved inverse native-clock law.
This projection exists for generic characters, so it would not itself be
an arithmetic integral-trace source lift. It would make the exact
canonical-trace change under the proposed transgression reviewable.
Search evidence: /tmp/irk-explicit-projective-source-search.json (running).

The true open conjecture remains a regulator constructed from literal
global Poisson range relations that imposes the requisite arithmetic
trace constraint on the off-line source class. No finite-flow theorem,
marked-degree assignment, ordinary Euler class, or generic rotation
projection may be substituted for that construction.

Cycle 13 native Xi leaf actual-path check passed warningfree. Each of the
five finished leaves is wired once into its umbrella. The final 107-name
axiom audit is running. The latest full lint remains blocked by the
single unrelated ThetaRenewalReflectedArithmetic umbrella error.

Next source audit: the global induced Poisson module currently has an
actual polynomial rotation action and exact boundary invariance. An
analytic inverse of V-lambda exists off the unit circle, but its action
on the arithmetic module cannot be assumed: the actual finite Xi quotient
has exactly that resonance. Analytic localization kills such torsion;
relative torsion/secondary topology must retain it. Thus neither an
extension of the module action to C* nor preservation of the Poisson
boundary by analytic resolvents is an available premise. These are
precisely source claims requiring proof. The explicit generic projection
is only a possible calibration, not a replacement research objective.
The next main objective stays the literal global arithmetic regulator.

Corpus search for actual rotation projectors returned no applicable
construction among its hits (partial=false; compiler coverage largely
source-only). A relevant existing exact obstruction is
GaloisForLFunctions.not_dilationTelescoped_of_unique_multOrbit_pole in
HTGeometry/MultiplicativeOrbitNonSummability.lean: a unique rational pole
on a non-torsion rotation orbit cannot be a rational q-difference. Its
source proof was inspected (lines 207-268). This constrains any attempted
rational cancellation of the new trace defect. Do not infer absence of
all projectors from incomplete semantic retrieval.

Final Cycle 10-13 verification: 107/107 public declarations audited with
only propext, Classical.choice and Quot.sound; no errors or sorryAx.
All five actual-path final Lean checks passed warningfree. Current owned
scratch Lean/part files and completed old search files are removed; audit
scripts/log/names and the two next-source searches are retained. Latest
full lint has only the unrelated ThetaRenewalReflectedArithmetic umbrella
failure. The unconditional RH goal is active and not complete.

## Cycle 14 — actual Poisson boundary clock defect

Target stays the global IRK source-to-topology construction. The induced
integer clock in PrimeRotationModule is external; it is not log-variable
modulation. A literal Mellin translation need not preserve Poisson range.
The secondary two-collar regulator has no proved identification with this
IRK source, so its boundary annihilation cannot be imported as that claim.

Exact source conjecture: let B(s) be the entire Mellin transform of the
Poisson image of the fixed meyerPoissonTestSource. For every finite array
of distinct points in 0 < Re(s) < 1 and every finite jet depth m, there is
a positive native clock denominator q such that the map taking an actual
cap source f to the derivatives through order m-1 of M(Zf) at rho_i+i/q
is onto the full finite jet space. All sources can be chosen from the
finite span of negative Euler iterates of the same fixed cap test.
Thus this is a concrete relative boundary defect, not an assumed quotient
clock action. In particular every full finite Xi multiplicity packet is
hit. This does not construct a K0 class or prove trace integrality.

Attack verdict: BRIDGE. The underlying interpolation is classical
Hermite interpolation and multiplication by an analytic unit. It is not
claimed novel. The improvement required here is actual Poisson-source
provenance with all jets, rather than an abstract target or diagonal count.
No external audit, per user instruction. Corpus searches:
irk-global-modulation-search, irk-boundary-jet-transgression-search,
irk-euler-source-search (all /tmp JSON files). No numerical experiments.

Dependency-closed paper proof:
1. For strong log g, exp(s t)g(t), exp(s t)g'(t), and
   s exp(s t)g(t) are integrable by all-weight decay. Whole-line integration
   by parts gives M(g')=-s M(g). Cap is Euler-stable and differentiation
   commutes with its actual Poisson map. Therefore the negative Euler
   iterate E^n f has boundary transform s^n M(Zf).
2. Consequently the finite source sum sum c_n E^n f has transform P(s)B(s)
   for P(s)=sum c_n s^n. This is an actual cap source, with no lift premise.
3. B is entire and nonzero: at s=2 its exact zeta-times-source factorization
   has two nonzero factors. Hence its zeros are isolated. For each of the
   finitely many rho_i, B(rho_i+t) is nonzero for all sufficiently small
   nonzero t. Take a common radius and a native t=i/q inside it. Translation
   preserves distinctness and the positive real parts of the nodes.
4. On jets at the translated nodes, multiplication by B is invertible:
   analytic order of P B equals that of P since B(node) != 0. Thus zero
   product jets force zero polynomial jets. Hermite interpolation makes
   the degree < K*m polynomial jet map bijective; composing with this
   unit multiplication is bijective. Step 2 realizes it on actual sources.
5. For variable multiplicities choose m at least their maximum and project
   the uniform packet. This retains every requested derivative. For the
   unshifted actual Xi nodes, all these boundary jets vanish by the existing
   full-multiplicity Poisson annihilation theorem. The shifted map is
   therefore a genuine nontrivial failure of descent of the physical clock.

Open core after this bridge: construct the relative noncommutative
projective/transgression class from these literal boundary relations and
prove its arithmetic trace constraint. Surjectivity alone cannot impose
critical-line placement and must not be advertised as doing so.

Cycle 14 first leaf verified warningfree on its actual path:
DeningerMeyerBoundaryEulerSource.lean. Actual integration-by-parts and
cap negative Euler polynomial synthesis now compile. Fresh olean/ilean
written. Full-jet and native-clock leaves remain under verification.

Possible next topological construction to attack, not a proved result:
compactify the meromorphic Xi gauge as a graph projection. Graph
projections have integer canonical trace when their entries lie in the
rotation algebra, while local poles can create a Chern obstruction.
The serious issue is membership/covariance: a general Xi gauge on the
vertical spectral line is not automatically periodic in the prime phase,
nor an element of the rotation C* algebra. Bounded entries alone prove
nothing about that membership. A measurable factor completion would also
lose discrete trace range. Thus graph completion may give a concrete place
to attack arithmetic descent, but cannot be asserted as the missing lift.
No graph projection is being substituted for a source theorem.

Cycle 14 physical-clock identification added to native leaf draft: the raw
log modulation exp(a*t)g(t) has Mellin transform M(g)(s+a), including every
spectral derivative. Surjective full Xi defects therefore give actual cap
boundaries whose modulation has no literal cap-boundary preimage. This is
stronger source provenance than the earlier local-principal-ideal no-go.
All-weight admission of modulation is not yet asserted by this raw identity.

Hard-obstacle analysis to retain:
- Euler interpolation uses the additive Mellin coordinate. Earlier Cycle 5
  already proved that adjoining that coordinate to the clock algebra gives
  a commutator equal to 1 and destroys a normalized cyclic trace. Source
  generation by Euler iterates is not permission to extend the trace to all
  source operators.
- The physical clock fails boundary descent; the induced external integer
  clock has exact boundary invariance but is a different module. Identifying
  external clock shifts with physical modulation changes the boundary
  complex. The new full-jet defect must be retained in that change, rather
  than quotiented away.
- One possible genuine next construction is a relative derived periodization
  of that induced complex, with the clock-defect object surviving in its
  index class. A declaration that the ordinary quotient already admits the
  physical clock is now explicitly ruled out at the actual source level.
- Global two-shift Bezout/synthesis is not available: avoiding finitely many
  zeros at a native rational-imaginary step does not avoid all Xi zeros at
  once, nor prove growth-controlled Mellin division. No such implication is
  used in Cycle 14.

## Cycle 15 — exact global Xi cap generator

The explicit Mellin formula for meyerPoissonTestSource implies the stronger
source identity B(s)=xi(s)/(4*pi^2). This identifies the fixed source in
Cycle 14 with the exact global Xi factor, not merely a function sharing
local nonvanishing properties. Verdict: BRIDGE; the identity is a theta/
Mellin calculation and is not claimed novel scientific knowledge.
Corpus search /tmp/irk-fixed-boundary-xi-search.json is partial=false and
returned no applicable ready-made identity among its hits. Exhaustive
source-text search found no direct meyerPoissonTest/xi named comparison.

Closed paper proof: on Re(s)>1, Poisson Mellin factorization gives zeta(s)
times (s-1)/4 * pi^(-(s+4)/2) * Gamma((s+2)/2). The Gamma recurrence changes
the final factor into (s/2)Gamma(s/2). Multiply by 4*pi^2 and combine powers
of the positive number pi; the result is exactly
s(s-1)/2 * Gamma_R(s) * zeta(s) = xi(s). Both boundary transform and xi are
entire, so equality holds globally by the identity theorem. Therefore the
scaled actual cap source 4*pi^2 * meyerPoissonTestSource has boundary Mellin
transform exactly xi. Negative Euler polynomial synthesis gives P(s)xi(s)
from actual cap sources. The ratio of the source boundary transform at s
and its physical-clock translate at s+a is exactly xi(s)/xi(s+a), including
Lean's totalized values at poles; all previous meromorphic gauge theorems
therefore attach to this actual global cap source.

Cycle 14 final native leaf passed actual-path Lean warningfree, including
all-multiplicity surjectivity, zero unshifted map, exact physical Mellin
translation on every derivative, and actual failure of Poisson-boundary
invariance. All three Cycle 14 leaves are wired once into RHTower.lean.
Cycle 15 exact Xi cap-source leaf subsequently passed its actual-path check.

## Cycle 16 — paper trace integrality beyond finite Weyl polynomials

User steering: stop bridge formalization and obstruction busywork. Solve the
projective construction or actual trace integrality. No Lean files were
written in this cycle. The subsequent explicit instruction is to construct
the rational idempotent from the Poisson source while retaining Xi
multiplicity. Retaining means the canonical Chern pairing, not merely the
dimension of an auxiliary vector space.

### Closed paper argument: rational idempotent trace

Let R be the finite twisted Laurent algebra of the two native Weyl
generators. Let A be its rotation C* closure with its canonical trace tau,
and M the finite von Neumann algebra in the trace GNS representation. Write
tau_n for the unnormalized matrix trace. Let D be the Ore division ring
of R. The following argument establishes two exact statements:

1. For T in M_{m,n}(R),
   tau_m(proj closure(range T)) = rank_D(T), and
   tau_n(proj ker T) = n - rank_D(T).
2. If E in M_n(A) is idempotent, b is a nonzero element of R, and
   E(b I_n) = B for B in M_n(R), then
   tau_n(E) = rank_D(B), an integer between 0 and n.

These are paper results, not Lean-verified results. They require no
spectral gap, no bounded inverse for b, and no assumed agreement of the
formal and analytic traces on arbitrary rational elements.

Proof of the algebraic preliminaries. A nonzero finite Laurent polynomial
has a lexicographically largest exponent in Z^2. The largest exponent in
a product has a unique nonzero coefficient, multiplied by a nonzero Weyl
phase. Thus R is a domain. For nonzero a,b in R, take square boxes F_N in
Z^2 and a finite square K containing both supports and 0. Both a R_{F_N}
and b R_{F_N} have complex dimension |F_N| and lie in R_{F_N+K}.
Since |F_N+K|/|F_N| tends to 1, their intersection is nonzero for large N.
This gives a common nonzero right multiple. The identical argument with
right multiplication gives a common nonzero left multiple. Thus R is an
Ore domain, and finitely many fractions admit common right denominators.

Proof of analytic rank for algebraically injective matrices. Suppose
S: R^r -> R^m is injective. In the GNS space l2(Z^2), its restriction to
vectors supported in F_N has image of dimension r|F_N|, supported in
F_N+K. Let Q be its closed-range projection and Q_N the orthogonal
projection onto that finite-dimensional image. Then Q_N <= Q and
Q_N <= chi_{F_N+K}. Twisted right translations commute with Q, so the
sum of its m diagonal coefficients is constant at every lattice point.
Consequently

  r |F_N| <= Tr(chi_{F_N+K} Q chi_{F_N+K})
            = |F_N+K| tau_m(Q).

Passing to the limit gives tau_m(Q) >= r. Polar decomposition gives the
opposite inequality and
tau_m(Q) = r - tau_r(proj ker S). Thus tau_m(Q)=r and ker S=0.
Applying this to a scalar a and its adjoint shows that each nonzero
element of R is injective with dense range.

Proof for an arbitrary T. Put r=rank_D(T). Choose r D-independent
columns of T. Their polynomial column matrix is algebraically injective,
so the closed range of T has trace at least r. Choose a D-basis of ker_D T
and clear the denominators of each column on the right. This gives a
polynomial matrix K with n-r D-independent columns and T K=0. The preceding
argument shows that its closed range has trace n-r and lies in ker T.
Polar decomposition of T now bounds its range trace above by r. Both
inequalities are equalities. This proves statement 1.

Proof for E. The operator b I_n has dense range. Therefore the closure of
range B = range(E b I_n) is the closed range of E. If P is the orthogonal
projection onto that range, P E=E and E P=P. Cyclicity gives
tau_n(E)=tau_n(P). Statement 1 applied to B gives statement 2.

Every bounded element of the Ore rational envelope has such a common
denominator. One way to justify the identification is that each nonzero
element of R has a densely defined affiliated inverse, so the Ore field
embeds in affiliated operators. The bounded rational envelope means the
intersection of this embedded Ore field with M; it does NOT mean all of
M or all of A. The statement with the explicit witness E b=B avoids
requiring affiliated-operator machinery in the theorem's hypotheses.

The Ore field also embeds in the already constructed formal quantum
Laurent division ring. Matrix rank is unchanged by this division-ring
extension. Diagonalizing an idempotent over that field proves that its
formal trace is the same rank. Hence the analytic/formal trace discrepancy
vanishes on bounded rational idempotents even though it does not vanish
on individual rational resolvents. This repairs that particular trace
comparison; it does not show that an arithmetic transgression is rational.

### Attacks and applicability

- The proof uses the trace GNS representation on l2(Z^2), not the concrete
  l2(Z) representation without justification. Their traces agree on the
  finite Weyl algebra and hence on its norm closure. Faithfulness of the
  latter representation is not needed for the displayed trace equality.
- Matrix traces are unnormalized. No factor 1/n is suppressed.
- Right denominators match the right D-vector-space convention for column
  matrices. The opposite-algebra statement handles the source's left
  module/right multiplication presentation.
- A gapped spectral-band projection of a polynomial Hamiltonian is not
  a kernel projection of a polynomial matrix merely because it comes
  from continuous functional calculus. The theorem does not assert that.
- Nontrivial smooth rotation projections are not counterexamples: common
  finite-Weyl denominators for them have not been supplied and cannot be
  inferred from smoothness or boundedness.
- No numerical experiment or spectral zero count enters this argument.

Corpus search /tmp/irk-ore-projection-integrality-search.json completed
with partial=false. It found the existing division-ring idempotent trace
and finite-Weyl trace comparison, but no applicable analytic Ore-rank
comparison among its hits. An exhaustive project Lean text search for
the relevant combinations did not locate one. This is not an external
novelty claim. Verdict: BRIDGE with a closed paper proof of the broader
trace comparison; actual Poisson projective construction remains OPEN.

### Direct construction attempts: keep the required Chern coordinate

The exact cap source has boundary transform F(s)=Xi(s). Its physical
clock gives G(s)=Xi(s+a). On a neighborhood of a zero rho at which G(rho)
is nonzero, the normalized column (F,G) gives an honest smooth rank-one
graph projection. This does not solve the requested construction:
the column is a global nonvanishing frame on that neighborhood, so its
line bundle is trivial. The order d of F/G is a marked transition order,
not an absolute Chern number of this graph projection. As the disk shrinks
to rho, its smooth curvature integral tends to zero. Attaching a cap with
degree d is an additional transgression, not a property of the graph.

For the actual full Xi jet relation R_rho(V)=V I-D_rho, the eigenvalue is
lambda=p^{-(rho-1/2)}. Off the critical line, |lambda| differs from 1.
The relation is then invertible in the rotation C* algebra: the scalar
factor V-lambda is invertible, and the remaining triangular nilpotent
part is inverted by a finite series. Its completed kernel/cokernel
projection is therefore zero. This direct rational construction loses
the entire source torsion and is rejected. It is not called a
multiplicity-preserving projectivization.

The alternative local Hardy/Toeplitz defect has finite rank d and keeps
the full local quotient. Its compact projection maps to zero in the
rotation Calkin quotient. Tensoring it with a prescribed rotation
projection would insert a chosen K-class; it would not prove arithmetic
trace integrality. This construction is also not accepted as the answer.

The exact outstanding construction now has a concrete algebraic witness
target: from the actual relative Poisson source, produce E_rho, b_rho,
and B_rho with E_rho^2=E_rho, E_rho b_rho=B_rho, nonzero finite-Weyl
b_rho, finite-Weyl B_rho, and canonical Chern pairing equal to the full
off-line multiplicity. The trace result above then supplies integrality
without any additional trace-comparison premise. No such E_rho or source
transgression has yet been constructed. Merely assuming its existence
would leave the central IRK problem untouched.

The actual Möbius inverse was checked as a possible source retraction in
DeningerMobiusPoissonRangeClassification.lean. It is continuous on the
literal Poisson range. Its regularity at the radial origin is an explicit
domain restriction; the file does not provide a retraction from the full
target onto that range. Therefore it cannot yet supply the needed bounded
idempotent. The next attack must use additional global source structure,
not silently extend this inverse to every cochain.

## Cycle 17 — attempted adelic construction through a finite-place corner

Previous goal turn classification: progress, specifically the closed paper
rank/trace argument in Cycle 16. It did not construct the required source
idempotent. Current target remains that construction, with full multiplicity
in its canonical Chern pairing. No additional Lean code was written.

### Candidate and actual source evidence

Candidate: cancel the real native Weyl phase with an opposite finite-place
clock in the global Poisson source; then remove the finite-place factor
through its unramified corner. If that passage were multiplicative on the
source projection and preserved the relevant trace, global ordinary trace
integrality could give the missing real rotation trace condition.

The corpus provides considerably more than a formal product formula:

- CCMRationalAdelicMoritaTraceFormula.lean constructs the ordinary
  trace-class representation of the actual algebraic adelic crossed product
  and proves its trace equals the rational orbit sum of the identity
  coefficient.
- CCMRationalAdelicSourceContinuousTraceNormField.lean constructs an actual
  algebra homomorphism from the unitized cyclic source to continuous fields
  of unitized trace-norm operators.
- CCMRationalAdelicTensorHaarMobiusCompression.lean constructs, for every
  actual algebraic Bruhat tensor, an even Schwartz source whose Meyer sum
  equals its profinite Haar-averaged rational trace after removing the
  zero mode. Vanishing of both Tate endpoints puts this source in the
  actual Meyer cap. This is a linear compression identity, not a proved
  homomorphism taking idempotents to idempotents.
- FieldOnePadicUnitBallNormalizedHaar.lean fixes the additive local Haar
  normalization mu(Z_p)=1. FieldOnePadicBruhatFourierL2.lean embeds actual
  Bruhat vectors in that Haar L2. FieldOnePadicUnitInvariantL2.lean averages
  over compact units; its range retains the entire valuation direction.
- The existing strict adelic prime-isotropy comparison is not a hidden
  answer: CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean explicitly
  proves its retained class maps to a resolved Xi boundary, and hence to
  zero in target H1. Its Stokes regulator does not repair that loss.

The corpus search /tmp/irk-global-clock-corner-search.json completed with
partial=false and no errors; session 36014 exited 0. The sources above were
read directly. No external search or numerical experiment was used.

### Exact test on the unramified local source

Put r=1/p and use additive Haar measure mu(Z_p)=1. The valuation shells
A_n=p^n Z_p^* have measure (1-r) r^n. This follows from the p equal additive
cosets in Z_p and Haar scaling, for all integer n. Their normalized
indicators e_n=((1-r)r^n)^(-1/2) 1_{A_n} form the orthonormal shell basis
of the unit-invariant subspace. The actual unramified vector v=1_{Z_p}
has norm one and expansion

  v = sqrt(1-r) sum_{n>=0} r^(n/2) e_n.

The point 0 has Haar measure zero, so it contributes no additional term.
The native local clock C acts by C e_n=omega^n e_n, where
omega=exp(-i log(p)/q) for the positive native clock denominator q. Its
phase is of infinite order by the native prime irrationality already
proved in the corpus. Let e=|v><v|. The exact geometric series gives

  <v,Cv> = c = (1-r)/(1-r omega),
  e C e = c e,
  1-|c|^2 = 2 r (1-Re(omega)) / |1-r omega|^2 > 0.

Thus the actual unramified rank-one corner turns the unitary native clock
into a strict contraction. For a real-place unitary U, compressing U tensor
C to H_real tensor Cv gives c U, which is not unitary. Opposite-phase
cancellation in a larger tensor algebra therefore does not itself produce
a unital star homomorphism to the real rotation algebra through this
corner. The failure is present on the actual unramified source vector;
it is not a generic auxiliary counterexample.

For any orthogonal projection P and any orthogonal corner e, put X=ePe.
Then

  X-X^2 = eP(1-e)Pe = ((1-e)Pe)^*((1-e)Pe).

Hence X is a projection precisely when (1-e)Pe=0, equivalently when P
commutes with e. The Haar/Mobius linear trace formula above does not prove
this condition for a proposed arithmetic P. No arithmetic P was produced
here; the calculation rejects the claim that compression alone would
provide the missing idempotence and trace comparison.

Verdict for the automatic finite-corner construction: FALSE.

### Positive survivor: the source forces its valuation completion

There is an exact minimal-completion statement, not only a negative test.
The closed C-invariant span of the actual v is all l2 of the nonnegative
valuation shells. For a fixed n>=0, the finite means

  (1/N) sum_{k=0}^{N-1} omega^(-nk) C^k v

converge in norm to sqrt(1-r) r^(n/2) e_n. On the m-th coordinate this is
the ordinary geometric mean of omega^(m-n); infinite order gives limit
zero for m!=n and one for m=n. Domination by the summable squared
coefficients of v proves norm convergence. Every shell therefore belongs
to the generated closed subspace, and the reverse inclusion follows from
support. In particular no finite-dimensional clock-invariant subspace
contains v.

Normalized prime dilation S f(x)=sqrt(p) f(x/p) satisfies S e_n=e_(n+1)
and C S=omega S C. Adding S and S^{-1} to the generated orbit gives every
integer shell, hence the complete bilateral rotation representation on
l2(Z). Retaining covariance is possible, but the finite-place factor is
then another infinite rotation representation. Its ordinary identity
trace is infinite; an integer finite-dimensional trace cannot be carried
through this replacement. Compact-unit averaging retains this valuation
space rather than replacing it by the one-dimensional span of v.

This positive survivor is proved on paper only. Per the user's instruction,
it is not being formalized as another obstruction leaf. It does not retire
IRK, nor does it rule out a source-specific projection satisfying the exact
multiplicative-domain condition. It rules out obtaining that condition
merely from the global linear Haar/Mobius trace formula or from phase
cancellation.

### Continuation target

Keep the full valuation orbit in any further global-source construction.
Do not reuse the finite unramified corner as a trace-preserving algebra
map. The concrete remaining target is a source-specific projective
transgression with the full Xi divisor Chern pairing and a proved trace
comparison. Global trace-class source representations are available;
their connection to such an idempotent is still open. No RH conclusion,
new scientific novelty, or successful projective construction is claimed.
