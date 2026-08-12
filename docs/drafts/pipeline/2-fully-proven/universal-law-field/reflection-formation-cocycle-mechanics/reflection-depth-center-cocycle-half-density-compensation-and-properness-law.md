# Reflection--depth center cocycle, half-density compensation, and properness law

- **ID:** ULF-RFCM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / GLOBAL FORMATION-PROPERNESS SURVIVOR
- **Source:** `../../../1-in-progress/universal-law-field/witt-formation-mechanics/full-frontier-intervention-generation-grammar.md` and `../packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md`
- **Statement:** Every one-dimensional affine multiplicative formation law has one common center; its exchange with a marked reflection is a translation measuring center mismatch, and functional-equation compatibility uniquely forces the half-density-compensated depth action. A nonzero mismatch either exits every bounded admission chamber or has unbounded proper work, while common recovery preserves it information-isometrically.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [GLOBAL ADMISSION/PROPERNESS] [COMMON-RECOVERY CONSERVATIVE]
  [ONE-DIMENSIONAL AFFINE CORE FALSIFIED] [NOT RH] [LEAN OPEN]

## Goal

Combine three mechanisms already proved separately in the corpus:

1. functional-equation reflection;
2. multiplicative formation depth;
3. common-kernel information-neutral packet formation.

The question is whether their interaction generates a genuine selector. The answer is exact:
ordinary depth and reflection generate an affine translation, while the unique way to remove that
translation is the centered half-density correction. Consequently a one-dimensional affine law
cannot be the missing field core. Its strongest survivor is a formation-center classification and
a global admission/properness theorem.

## Gates

- [x] 0 -> 1: source operations fixed before target specialization; exact exchange word and hostile attack supplied
- [x] 1 -> 2: complete unconditional paper proof; no analytic or RH premise
- [ ] 2 -> 3: formalize exact affine, admission, and properness core in Lean under `UniversalLawField`
- [ ] 3 -> 4: standalone publication treatment

## 1. Affine formation semigroup

Let (M\subset \mathbb R_{>0}) be a commutative multiplicative monoid containing (1) and at
least one element different from (1). Suppose

\[
 F_\lambda(x)=\lambda x+b_\lambda
 \qquad(\lambda\in M)
 \tag{RFC.1}
\]

is a strict monoid action on the real formation line:

\[
 F_1=\operatorname{id},\qquad F_\lambda F_\mu=F_{\lambda\mu}.
 \tag{RFC.2}
\]

The translation terms obey

\[
 b_{\lambda\mu}=\lambda b_\mu+b_\lambda.
 \tag{RFC.3}
\]

### Theorem 1.1 -- common-center classification

There is a unique (d\in\mathbb R) such that

\[
 \boxed{b_\lambda=(1-\lambda)d,
 \qquad F_\lambda(x)=d+\lambda(x-d)}
 \tag{RFC.4}
\]

for every (lambda\in M). Thus every strict one-dimensional affine multiplicative formation law
is a dilation about one common center. Its apparent translation cocycle is a coboundary.

#### Proof

Commutativity and `(RFC.3)` give

\[
 \lambda b_\mu+b_\lambda
 =b_{\lambda\mu}=b_{\mu\lambda}
 =\mu b_\lambda+b_\mu,
\]

hence

\[
 (\lambda-1)b_\mu=(\mu-1)b_\lambda.
 \tag{RFC.5}
\]

Choose (ho\in M) with (ho\ne1), and put

\[
 d={b_\rho\over1-\rho}.
\]

Equation `(RFC.5)` with (mu=\rho) gives (b_\lambda=(1-\lambda)d). Uniqueness follows from
any (lambda\ne1). Conversely `(RFC.4)` plainly satisfies `(RFC.2)`. ∎

## 2. Reflection exchange and the center defect

For a marked reflection center (c\in\mathbb R), define

\[
 R_c(x)=2c-x,
 \qquad T_h(x)=x+h.
 \tag{RFC.6}
\]

### Theorem 2.1 -- exact schedule exchange

For every (lambda\in M),

\[
 \boxed{
 F_\lambda R_c
 =T_{h_\lambda}R_cF_\lambda,
 \qquad
 h_\lambda=2(\lambda-1)(c-d).}
 \tag{RFC.7}
\]

Because (F_\lambda) is invertible on the real line,

\[
 \boxed{F_\lambda R_cF_\lambda^{-1}R_c=T_{h_\lambda}.}
 \tag{RFC.8}
\]

For every (lambda\ne1), the following are equivalent:

1. (F_\lambda R_c=R_cF_\lambda);
2. the exchange translation vanishes;
3. (d=c).

#### Proof

Using `(RFC.4)`, direct expansion gives

\[
 F_\lambda(R_cx)-R_c(F_\lambda x)
 =2(\lambda-1)(c-d).
\]

This is `(RFC.7)`. Right composition by (F_\lambda^{-1}R_c) gives `(RFC.8)`. The equivalence
follows because (lambda\ne1). ∎

The exchange defect is therefore not an intrinsic curvature class. It is the coboundary measuring
the distance between two marked centers. Repeated commutator execution produces

\[
 (F_\lambda R_cF_\lambda^{-1}R_c)^n(x)
 =x+n h_\lambda.
 \tag{RFC.9}
\]

## 3. Unique reflection-compatible compensation

### Corollary 3.1 -- unique centered dilation

Fix a slope (lambda>0). Among all affine maps (A(x)=\lambda x+b), the unique map commuting with
(R_c) is

\[
 \boxed{C_{\lambda,c}(x)=c+\lambda(x-c)
 =\lambda x+(1-\lambda)c.}
 \tag{RFC.10}
\]

The family (C_{\lambda,c}) is itself a strict multiplicative action:

\[
 C_{\lambda,c}C_{\mu,c}=C_{\lambda\mu,c},
 \qquad C_{\lambda,c}R_c=R_cC_{\lambda,c}.
 \tag{RFC.11}
\]

This is immediate from Theorems 1.1 and 2.1.

### Functional-equation specialization

Take the usual Dirichlet coordinate (sigma), functional reflection

\[
 R(\sigma)=1-\sigma=R_{1/2}(\sigma),
 \tag{RFC.12}
\]

and raw depth formation (D_m(\sigma)=m\sigma), (m\ge2). Then

\[
 \boxed{
 D_mR=T_{m-1}RD_m,
 \qquad D_mRD_m^{-1}R=T_{m-1}.}
 \tag{RFC.13}
\]

Hence raw depth and functional reflection do not commute. The unique slope-(m) correction that
does commute is

\[
 \boxed{
 C_m(\sigma)={1\over2}+m\left(\sigma-{1\over2}\right)
 =m\sigma-{m-1\over2}.}
 \tag{RFC.14}
\]

For the Dirichlet weight (w_\sigma(n)=n^{-\sigma}), this gives the exact coefficient law

\[
 \boxed{
 w_{C_m(\sigma)}(n)
 =n^{(m-1)/2}\,w_\sigma(n)^m.}
 \tag{RFC.15}
\]

Thus the half-density factor (n^{(m-1)/2}) is not an optional normalization inside the affine
formation class. It is uniquely forced by strict depth composition and functional-equation
reflection.

## 4. Bounded-admission escape

Let (A\subset\mathbb R) have finite diameter (L). If

\[
 x,x+h,\ldots,x+Nh\in A,
\]

then

\[
 \boxed{N|h|\le L.}
 \tag{RFC.16}
\]

Indeed the first and last points lie in (A), and their distance is (N|h|). Consequently, if
(h\ne0), no bounded admission chamber is invariant under the exchange word. In particular, a
bounded analytic strip cannot admit both raw depth and functional reflection as globally closed
source operations.

This yields a strict alternative:

1. use the unique compensated action `(RFC.14)`;
2. let the schedule leave the admitted source domain after finitely many iterations; or
3. enlarge the source to retain an unbounded history coordinate.

## 5. Proper-work escape

Let (mathcal C:\mathbb R\to[0,\infty]) have compact sublevel sets. If (h\ne0), then

\[
 \boxed{\mathcal C(x+nh)\longrightarrow\infty.}
 \tag{RFC.17}
\]

#### Proof

If `(RFC.17)` failed, some finite sublevel set would contain an unbounded subsequence of
(x+nh), contradicting compactness. ∎

Applied to `(RFC.9)`, every nonzero center mismatch has unbounded cost under any predeclared proper
source work. Therefore bounded work on the complete exchange orbit forces (d=c). This is a
global selection law for formation centers, but it is not yet an RH theorem: a source-specific
comparison must prove that the physical orbit is admitted and has bounded work.

## 6. Common recovery is information-neutral, not defect-neutral

Let (x\mapsto\mu_x) be probability laws on a standard Borel observer space and let (K) be one
parameter-independent Markov recovery kernel. Put

\[
 E_K(\mu_x)=\mu_x\otimes K.
 \tag{RFC.18}
\]

The split relative-entropy chain rule gives, with extended values allowed,

\[
 D_{\rm KL}(E_K\mu_x\Vert E_K\mu_y)
 =D_{\rm KL}(\mu_x\Vert\mu_y).
 \tag{RFC.19}
\]

Consequently Jeffreys work also satisfies

\[
 \boxed{
 J(E_K\mu_x,E_K\mu_{x+nh})
 =J(\mu_x,\mu_{x+nh}).}
 \tag{RFC.20}
\]

Thus common recovery cannot erase the center defect. If base Jeffreys work is proper along the
translation orbit, formed-packet work is proper with exactly the same growth. This is the precise
fusion with `ConstitutiveFunctionalEquationPacketLift`: information-neutral formation transports
the exchange defect isometrically rather than annihilating it.

## 7. Recurrent observation and open exchange history

For (ell>0), project the exchange orbit to the circle

\[
 \pi_\ell:\mathbb R\longrightarrow\mathbb R/\ell\mathbb Z.
 \tag{RFC.21}
\]

If (h/\ell\in\mathbb Q), the projected orbit is periodic. If (h/\ell\notin\mathbb Q), it is
dense and recurrent. In both cases the observer has recurrent compact closure, while for (h\ne0)
the marked lift (x+nh) is unbounded. Hence

\[
 \boxed{
 \text{closed/recurrent exchange observer}
 \quad\not\Rightarrow\quad
 \text{closed formation history}.}
 \tag{RFC.22}
\]

The proof is the elementary classification of rotations of the circle. The point here is not that
classification, but that the rotation increment is generated by the source exchange word
`(RFC.8)` rather than appended as an unrelated history counter.

## 8. Five-frontier-class consequence

This theorem supplies one exact mechanism across all five obstruction classes without claiming to
solve them:

| frontier class | exact consequence of ULF-RFCM-1 |
|---|---|
| singular source descent | common recovery preserves the defect; an information-neutral lift is not an annihilator |
| all-prime oscillatory transport | compact recurrent quotient can hide an open generated translation history |
| adaptive spectral orientation | reflection center (c) and formation center (d) must be source-marked independently |
| whole-space coercivity | proper work turns every nonzero center mismatch into unavoidable escape |
| positive carrier existence | positive packet formation does not remove exchange; it carries the same Jeffreys work |

This is unconditional leverage because it rules out one complete class of proposed selectors:
one-dimensional affine reflection/depth geometry cannot manufacture a new law. It either aligns
centers by the unique half-density correction or produces an escaping coboundary.

## 9. Hostile conjecture loops

1. **The reflection--depth commutator selects (sigma=1/2). -- False.** Its translation
   (m-1) is independent of (sigma). It detects incompatible centers, not a distinguished point.
2. **Information-neutral recovery kills the exchange defect. -- False.** Equation `(RFC.20)`
   preserves its full Jeffreys work.
3. **The half-density correction is a convenient gauge. -- Too weak.** It is the unique affine
   compensation compatible with strict multiplicative depth and reflection.
4. **The center defect is nontrivial curvature. -- False.** Theorem 1.1 makes every such affine
   cocycle a coboundary determined by one common center.
5. **Properness proves RH. -- False.** Properness proves center equality only after a literal source
   theorem admits the complete orbit and bounds its physical work.
6. **Raw depth and functional reflection coexist on one bounded analytic family. -- False.** Their
   exchange translation exits every bounded chamber.

## 10. Literature and significance boundary

Affine actions, group/semigroup cocycles, proper affine actions, circle rotations, relative-entropy
chain rules, and half-density normalizations are established mathematics. Nearby parent theories
include proper affine cocycles and affine group actions, Markov recovery/equality in data
processing, and renormalization semigroups. No priority claim is made for those ingredients.

The corpus-level advance is the exact fusion and kill boundary:

- functional reflection and raw depth generate a source-marked translation;
- common recovery conserves it exactly;
- admission and proper work make its global consequence unavoidable;
- the only affine repair is the half-density-centered action;
- therefore the next field mechanism must be nonlinear, higher-rank, noncommutative, or
  admission-singular enough to carry a genuinely non-coboundary formation class.

## No-go closure

- **Exact killing theorem/mechanism:** Theorem 1.1 proves every one-dimensional affine formation
  cocycle is a common-center coboundary; Theorem 2.1 identifies its whole reflection defect with
  center mismatch.
- **Strongest positive survivor:** unique reflection-compatible half-density compensation plus
  bounded-admission and proper-work escape, conserved through common recovery.
- **New insight:** source selection cannot come from another affine reflection/depth scalar. It
  must enter through a genuinely nontrivial formation cocycle, a non-affine action, or a singular
  admission comparison.
- **Status:** dependency-closed paper proof; Lean formalization deliberately deferred during the
  current read-only research phase.

## Log

- 2026-08-12 -- extracted after the functional-equation packet lift proved information neutrality
  is isometry rather than work annihilation.
- 2026-08-12 -- hostile audit killed the affine-Weyl selector interpretation and retained the
  unique half-density compensation/properness theorem.
