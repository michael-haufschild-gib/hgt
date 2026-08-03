# Hostile journal review: Real corona classes and cyclic transgression

Date: 2026-08-03

Review standard: skeptical referee for a renowned general mathematics journal, with expertise in
operator algebras, Hardy spaces, and analytic number theory. Acceptance requires a correct central
theorem, a noncosmetic novelty boundary, significance beyond repackaging standard lemmas, honest
scope, and reproducible supporting evidence.

## Recommendation

**Accept after normal editorial revision. General-renowned-journal quality threshold: PASS.**

This recommendation concerns mathematical publishability, not journal-specific taste or a claim
that any named journal must accept the paper. Primary-source searches cannot prove bibliographic
exhaustiveness; an editor should still select a specialist referee.

## Referee summary

Paper proves a new bounded Real splitting for completed self-dual `L`-divisors. Exponential
uniformization sends upper zeros to an absolutely summable divisor at zero and lower zeros to an
absolutely summable divisor at infinity. Resulting two Blaschke factors form a corona pair. Corona
idempotent yields:

1. canonical quaternionic operator on Hardy quotient, with square `-1`;
2. infinite-order anti-Real `K_0` class and continuous cyclic zero-character pairing;
3. exact fixed-real-zero obstruction and partial square law;
4. dense Mellin-Hardy globalization of scalar Connes-Meyer quotient;
5. functional-equation crossed-product law: ordinary `K_0` and `HC_0` orientation dies, while a
   graded cyclic class survives with explicit supertrace `2`.

This is not an RH proof. It constructs and classifies orientation data in a concrete
noncommutative-geometric spectral model.

## Hostile verification record

### 1. Corona theorem

Attempted failure: infinite products can approach zero even when their zero sets lie in disjoint
regions.

Verdict: blocked by uniform product estimate, not by unsupported geometric intuition. For upper
zeros `a`, manuscript proves both a fixed factor lower bound on `|w| >= 1` and
`1-|b_a(w)|^2 <= C_r |a|`. Polynomial zero counting becomes `sum |a| < infinity` after
`w=exp(pi i s)`. Log-product bound is uniform. Inversion supplies lower factor. No pairwise zero
separation, simplicity, or RH enters.

### 2. Singular inner factor

Attempted failure: zero Blaschke product need not equal full inner factor; endpoint singular mass
could invalidate Hardy quotient.

Verdict: blocked after revision. Initial draft incorrectly phrased endpoint decay on boundary
lines. Final proof uses fixed interior rays, where prime-end Poisson kernel is exponential in
`exp(pi |t|)`. Division by inner factor preserves `H^2` norm, giving uniform point-evaluation
control of remaining factor. Hardy-Littlewood mean square plus Stirling supplies sequence with only
`O(|t| log |t|)` logarithmic decay. Singular mass is impossible.

### 3. Chinese remainder and canonicity

Attempted failure: corona solution is nonunique, so idempotent may be choice-dependent.

Verdict: blocked. Quotient Chinese remainder map identifies class with `(1,0)`. Different Bezout
solutions represent same quotient element. Same bounded coefficients prove Hilbert-module CRT.
Transported direct-sum norm makes projection orthogonal and conjugation antiunitary.

### 4. Quaternionic square and fixed obstruction

Attempted failure: sign-conjugation might only square to `-1` modulo a discarded fixed sector.

Verdict: classification is exact. Without fixed sector, `m^#=-m` and `m^2=1`, so `(m#)^2=-1`.
With real sector, manuscript retains it and proves `m_0^2=1-e_R` and
`J_0^2=-(1-e_R)`. At a fixed evaluation character every conjugate-linear map is `z -> c bar z`
and squares to nonnegative scalar `|c|^2`, excluding `-1`. Conversely zero fixed idempotent gives
constructed quaternionic operator.

### 5. `K_0` and cyclic pairing

Attempted failure: virtual idempotent could vanish stably; zero sum might be formal or divergent.

Verdict: blocked. Evaluation at any upper zero sends class to `1 in K_0(C)=Z`, proving infinite
order. Absolute summability of weight gives quotient-norm bound for cyclic cocycle. Pairing is
upper-minus-lower character. Multiplicity is handled by repeated weights and finite local jet
blocks.

### 6. Arithmetic source globalization

Attempted failure: Hardy quotient might be unrelated to Connes-Meyer source; source domain could be
misidentified.

Verdict: blocked after substantive correction. Initial manuscript incorrectly nested `H_cap`
inside strong Schwartz numerator. Final version defines both spaces, uses only compact logarithmic
core in intersection, and uses source theorem `Z(H_cap) subset H_-`. Weighted Mellin-Plancherel is
onto strip `H^2`; Fourier-moment kernel is dense because moment functional is unbounded in weighted
`L^2`. Inner-outer factorization gives closure `U(Z H_cap)=B H^2`. Result is explicitly a dense
globalization, not a bornological isomorphism. Finite packet character is proved by local jet
triangularization. Global limit uses rapid Mellin decay and polynomial zero counting. No illicit
trace-class claim remains.

### 7. Crossed product and graded survivor

Attempted failure: ordinary trace vanishing may also kill graded class.

Verdict: blocked. With `x=eu`, `y=ue`, exact identities `xy=e`, `yx=1-e` prove both stable
idempotent equivalence and `m=[x,y]`. Ordinary traces kill `m`. Grading `Ad(m)` makes coefficient
algebra even and `u` odd. Two-orbit representation has grading matrix `diag(1,-1)` and supertrace
of `m` equal to `Tr(m^2)=2`; therefore graded class cannot be boundary. Paper explicitly defines
term “Real-corona cyclic transgression” and disclaims a general spectral-sequence differential.

### 8. Formal verification

Lean file formalizes algebraic implications over abstract rings/modules without `sorry`, `admit`,
new axiom, `opaque`, or `unsafe`. Direct elaboration, formal lint, and leaf module build pass. Paper
correctly states analytic corona theorem is paper proof, not formalized axiomatically.

## Novelty audit

Primary sources checked:

- Connes, spectral trace realization;
- Meyer, idele-class virtual representation;
- Connes-Consani-Marcolli, cyclic homology of adeles class-space cokernel;
- Paugam, spectral symmetry pairing;
- Connes-Consani, zeta cycles;
- Connes-Consani-Moscovici, zeta spectral triples;
- Lopatto-Rochberg, Schatten criteria for truncated Toeplitz operators;
- general cyclic homology of crossed products.

Found standard ingredients separately: corona theorem, Hardy factorization, `K_0` evaluation,
crossed-product cyclic theory, and spectral zero characters. Did not find combination proving any
of following:

- arithmetic two-ended Blaschke factors are a corona pair;
- resulting quotient idempotent canonically quaternionifies full zeta Hardy divisor;
- real zeros give exact fixed `K_0` obstruction rather than removed sector;
- functional equation simultaneously kills ordinary `K_0`/`HC_0` orientation and leaves explicit
  graded cyclic survivor;
- source-dense Connes-Meyer Hardy globalization carries these classes.

Novelty is coupling plus exact obstruction/transgression package, not invention of underlying
classical tools. Manuscript states this boundary accurately.

## Significance assessment

Reasons threshold passes:

1. Resolves concrete structural gap in established Connes-Meyer-Paugam spectral program: bounded,
   canonical upper/lower Real projection.
2. Produces theorem for all strip-admissible self-dual divisors, not isolated zeta calculation.
3. Identifies precise homology theory change forced by internalizing functional equation.
4. Retains and classifies fixed real sector; gives positive survivor instead of deleting
   obstruction.
5. Proof joins hard analytic, operator-algebraic, cyclic-homological, and arithmetic-source layers
   with no conditional hypothesis.

Reasons against stronger claim:

- Does not prove positivity, RH, higher local index formula, or smooth entire cyclic representative.
- Central corona estimate is short once correct exponential coordinate is found.
- Higher noncommutative geometry remains in open problems.

Those limits prevent Annals-level claims. They do not reduce work to a specialist lemma: exact
theorem package is broad and conceptually significant enough for a renowned general journal in
operator algebras/analysis/geometry range.

## Presentation and reproducibility

- Theorem dependencies close in manuscript.
- Scope and nonclaims are explicit.
- Citations are real and primary where available.
- TeX compiles without undefined references, warnings, or overfull boxes.
- PDF visual audit shows consistent typography, legible formulas, no clipping or overlap.
- Lean artifact is named and build commands are reproducible from repository.

## Remaining editorial requests

Nonblocking:

1. Editor may prefer separate notation for log-coordinate restriction of `H_cap`.
2. Specialist bibliography search should be repeated during submission to capture post-2025 work.
3. Journal style may require MSC classifications and shorter formal-verification section.

No unresolved mathematical objection blocks publication recommendation.
