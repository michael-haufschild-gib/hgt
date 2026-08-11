# Laminar static dimension one, unbounded adaptive stress, and convex-loss law

- **ID:** ULF-ALG-2
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / SUBORDINATE BRIDGE FOR ADVERSARIAL LAW GENESIS
- **Source:** `../../1-in-progress/universal-law-field/adversarial-law-genesis-and-sequential-stress-mechanics.md`
- **Statement:** A laminar family of prefix tests has static shattering dimension one but exact
  adaptive mistake depth \(d\); convex prediction changes the exact minimax loss from \(d\) to
  \(d/2\) without removing source-consistent adaptive stress.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [CLASSICAL ONLINE-LEARNING PARENT] [LEAN-FORMALIZED] [NOT RH]
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveAdversarialLawStress`

## 1. Source laws and legal tests

Let \(\Sigma=\{0,1\}\).  For \(d\geq1\), the source-law space is the set of binary branches

\[
  H_d=\Sigma^d.
\tag{AS.1}
\]

For every nonempty word \(p\in\Sigma^{\leq d}\), define its prefix cylinder

\[
  C_p=\{b\in H_d:p\preceq b\}.
\tag{AS.2}
\]

A branch \(b\) evaluates the test \(p\) by

\[
  \chi_b(p)=\mathbf1_{C_p}(b).
\tag{AS.3}
\]

The test family is source-native: tests are finite initial commitments, and a source law is a
complete continuation.

## 2. Static test complexity

Call a finite prefix family \(Q\) **statically shattered** when every labelling
\(Q\to\Sigma\) is the restriction of \(\chi_b\) for some \(b\in H_d\).

### Theorem 2.1 -- exact static shattering dimension

For every \(d\geq1\):

1. some singleton prefix family is shattered;
2. no two distinct prefixes are shattered.

Hence the static VC/shattering dimension of the prefix-cylinder doctrine is exactly one.

### Proof

The singleton \(\{(0)\}\) is shattered: a branch beginning in \(0\) gives label one, while a branch
beginning in \(1\) gives label zero.

Let \(p\neq q\).  If \(C_p\cap C_q=\varnothing\), the labelling \((1,1)\) is impossible.  Otherwise
some branch has both \(p\) and \(q\) as prefixes.  Two prefixes of one word are comparable, so either
\(p\preceq q\) or \(q\preceq p\).  In the first case \(C_q\subseteq C_p\), and the labelling
\((0,1)\) on \((p,q)\) is impossible.  In the second case \(C_p\subseteq C_q\), and \((1,0)\) is
impossible.  Thus no pair is shattered. `QED`

## 3. Exact adaptive stress

A deterministic response policy is any function

\[
  A:\Sigma^{<d}\longrightarrow\Sigma.
\tag{AS.4}
\]

At stage \(k\), the current source-consistent prefix is \(p_k\).  The policy is challenged on the
left-child cylinder

\[
  q_k=p_k0
\tag{AS.5}
\]

and predicts \(\widehat y_k=A(p_k)\).  The source then appends that predicted bit,

\[
  p_{k+1}=p_k\widehat y_k,
\tag{AS.6}
\]

and returns the opposite membership label

\[
  y_k=1-\widehat y_k.
\tag{AS.7}
\]

### Theorem 3.1 -- realizable all-round mistake forcing

For every deterministic policy \(A\) and every \(d\geq1\), the recursion above has a final branch
\(b=p_d\in H_d\) such that

\[
  \chi_b(q_k)=y_k\neq\widehat y_k
  \qquad(0\leq k<d).
\tag{AS.8}
\]

After the first \(k\) answers, the complete version space is exactly \(C_{p_k}\), of cardinality
\(2^{d-k}\).  Thus every answer history is source-consistent and every deterministic policy makes
exactly \(d\) forced mistakes.

### Proof

The final branch extends every \(p_k\).  The query \(q_k=p_k0\) is a prefix of \(b\) exactly when
the next bit of \(b\) is zero.  By `(AS.6)` that bit is \(\widehat y_k\).  Therefore

\[
  \chi_b(q_k)=1
  \Longleftrightarrow \widehat y_k=0,
\]

which is `(AS.7)`--`(AS.8)`.

For the version-space statement, use induction on \(k\).  Before any query the version space is
\(C_{p_0}=H_d\).  Inside \(C_{p_k}\), label one on \(q_k=p_k0\) leaves precisely
\(C_{p_k0}\), while label zero leaves precisely \(C_{p_k1}\).  Equation `(AS.6)` chooses the
corresponding child.  A length-\(k\) cylinder has \(2^{d-k}\) completions. `QED`

### Corollary 3.2 -- exact sequential dimension

The Littlestone/sequential shattering dimension of this doctrine is exactly \(d\).

### Proof

Theorem 3.1 gives a complete shattered challenge tree of depth \(d\).  Conversely, a shattered
binary tree of depth \(r\) needs a distinct source law for each of its \(2^r\) root-to-leaf label
histories: two different histories disagree at their first divergent node and cannot be realized by
the same law.  Since \(|H_d|=2^d\), one has \(2^r\leq2^d\), hence \(r\leq d\). `QED`

This is the sharp separation:

\[
  \boxed{\operatorname{static\text{-}dim}(H_d)=1,
  \qquad \operatorname{sequential\text{-}dim}(H_d)=d.}
\tag{AS.9}
\]

## 4. Convex response does not close the horizon

A fractional policy assigns

\[
  u:\Sigma^{<d}\longrightarrow[0,1],
\tag{AS.10}
\]

interpreted as weight on label one.  For \(y\in\{0,1\}\), use linear loss

\[
  \ell(u,y)=y(1-u)+(1-y)u.
\tag{AS.11}
\]

At prefix \(p\), the source returns label zero if \(u(p)\geq1/2\) and label one otherwise.  It
appends bit one in the first case and bit zero in the second, so the same prefix-cylinder argument
retains a realizable final branch.

### Theorem 4.1 -- exact convex minimax loss

Every fractional policy admits a source-consistent depth-\(d\) transcript with

\[
  \sum_{k<d}\ell(u(p_k),y_k)\geq \frac d2.
\tag{AS.12}
\]

The constant policy \(u\equiv1/2\) has loss exactly \(d/2\) against every transcript.  Therefore the
fractional minimax loss is exactly \(d/2\).

### Proof

If \(u(p_k)\geq1/2\), label zero gives loss \(u(p_k)\geq1/2\).  Otherwise label one gives loss
\(1-u(p_k)>1/2\).  The chosen next bit makes that label equal to membership in the queried left
child, so all answers are realized by the final branch as in Theorem 3.1.  Summing gives `(AS.12)`.
The constant half policy makes each summand exactly \(1/2\). `QED`

Thus convexification changes exact damage but not the existence of an arbitrarily deep legal
counterchallenge.

## 5. Infinite horizon

Let \(H_\infty=\Sigma^{\mathbb N}\) and retain every finite nonempty prefix cylinder.  Every finite
prefix family still has static dimension one by Theorem 2.1.  For every \(d\), restriction to the
first \(d\) coordinates contains the depth-\(d\) game above.  Consequently:

\[
  \boxed{\operatorname{static\text{-}dim}(H_\infty)=1,
  \qquad \operatorname{sequential\text{-}dim}(H_\infty)=\infty.}
\tag{AS.13}
\]

No deterministic policy has a finite universal mistake bound, and no fractional policy has a
finite universal cumulative-loss bound.

## 6. Mechanism consequences

1. Fixed-face simplicity does not bound adaptive stress.  Static dimension can remain one while
   source-consistent challenge depth diverges.
2. The adversary does not falsify realizability.  It preserves a nonempty version cylinder at every
   stage and selects one complete source law only after the transcript is formed.
3. Convex/positive relaxation changes the minimax rate but does not manufacture closure.
4. A source theorem quantified over self-selected tests cannot be replaced by any bound proved only
   for fixed test families without an independent sequential-rank theorem.
5. Hypertranscendence is not proved here.  The exact survivor is narrower: unbounded adaptive law
   stress can occur in a combinatorially elementary, statically one-dimensional family.

This closes one bridge in `ULF-ALG-1`; it does not prove that all law genesis is online learning.

## 7. Hostile boundaries

1. The source sees the current response before choosing the next branch bit.  Reversing this move
   order changes the game.
2. The final target is selected consistently in hindsight.  This is standard realizable online
   semantics, not a claim that a physical hidden variable may depend causally on a later choice.
3. Prefix labels and lineage are retained.  An observer erasing them may contract the challenge
   tree, but this theorem does not yet prove a general data-processing law.
4. The convex theorem concerns fractional predictions exposed to the source before label choice.
   Private random samples require a separate probabilistic game.
5. The result is classical threshold/tree online-learning mathematics.  Parent machinery includes
   Littlestone dimension and model-theoretic stability.  No priority claim is made.
6. No computable-strategy theorem follows.  Effective Littlestone theory proves that abstract
   finite rank and executable online learning can separate.
7. No RH route, zero criterion, positivity theorem, physical clock, or Hypertranscendence theorem is
   used or obtained.

## 8. No-go closure and positive survivor

The conjecture that small static/fixed-face complexity bounds adaptive law stress is false.

- **Exact killing mechanism:** the laminar prefix-cylinder family has static dimension one but
  sequential dimension \(d\), for arbitrary \(d\).
- **Strongest positive survivor:** sequential stress is exactly challenge-tree depth; deterministic
  and convex minimax losses are exactly \(d\) and \(d/2\) in this source-native family.
- **New insight:** adaptivity is an independent constitutive resource.  It cannot be inferred from
  the complexity of every fixed test face.
- **Formal status:** Lean-certified.  Static laminarity, arbitrary-depth deterministic stress,
  source-consistent final-branch realization, the exact version-space count `2^(d-k)`, the
  sequential-dimension upper bound `r <= d` for every shattered challenge tree, the per-round convex
  lower bound, and the exact cumulative value (d/2) are unconditional declarations in
  `ConstitutiveAdversarialLawStress.lean`.

## Log

- 2026-08-10 -- theorem and hostile scope closed on paper after internal corpus and current parent
  audit.  Sent to Lean gate.
- 2026-08-10 -- Lean gate passed; module wired into the Universal Law Field umbrella.  Axiom audit
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-11 -- version-space count and sequential-dimension upper bound certified; card promoted to stage 3.
