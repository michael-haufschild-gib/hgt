# First-Entrance Gate Renewal and Prefix Law

Status: `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN DEFERRED DURING REFACTOR]`

Date: 2026-08-10

## Scope and scientific label

This card proves an exact decomposition that separates two effects conflated by
ordinary endpoint Green mass:

1. reaching a target for the first time;
2. returning to the target after it has already been reached.

The Markov renewal identity, prefix-free coding, Kraft inequality, and
information projection used below are classical mathematical mechanisms. No
novelty is claimed for those ingredients. Possible novelty is restricted to
their joint use as a loop-free circuit-complexity observable and to any future
quenched theorem for ordinary static local-Hamiltonian trajectories. External
priority remains unverified.

No Brown--Susskind ramp, plateau, or static-local ensemble estimate is claimed
here. No physics claim is made.

## 1. Markov-chain setup

Let \((Z_j)_{j\ge 0}\) be a time-homogeneous Markov chain on a finite or
countable state space \(S\). Fix a nonempty target set \(A\subseteq S\) and a
discount \(a\in(0,1)\). Define the first entrance and first positive return
times

\[
 \tau_A:=\inf\{j\ge 0:Z_j\in A\},
 \qquad
 \tau_A^+:=\inf\{j\ge 1:Z_j\in A\}.
\]

As usual, \(a^\infty\mathbf 1_{\{\infty<\infty\}}\) is interpreted as zero.
For \(x\in S\), define the discounted entrance measure on \(A\)

\[
 \nu_{x,a}(B)
 :=\mathbb E_x\!\left[
      a^{\tau_A}\mathbf 1_{\{\tau_A<\infty\}}
      \mathbf 1_{\{Z_{\tau_A}\in B\}}
    \right],
 \qquad B\subseteq A,
\]

and its total mass

\[
 F_a(x,A):=\nu_{x,a}(A)
 =\mathbb E_x\!\left[a^{\tau_A}\mathbf 1_{\{\tau_A<\infty\}}\right].
\]

Define the discounted positive-return kernel on \(A\) by

\[
 K_{A,a}(z,B)
 :=\mathbb E_z\!\left[
      a^{\tau_A^+}\mathbf 1_{\{\tau_A^+<\infty\}}
      \mathbf 1_{\{Z_{\tau_A^+}\in B\}}
    \right],
 \qquad z\in A,\ B\subseteq A.
\]

Finally define the discounted occupation measure restricted to \(A\):

\[
 \mu_{x,a}^{A}(B)
 :=\sum_{j\ge 0}a^j\mathbb P_x(Z_j\in B),
 \qquad B\subseteq A.
\]

All sums are absolutely convergent because \(a\in(0,1)\).

## 2. The exact entrance--return resolvent law

### Theorem 2.1 (entrance--return factorization)

For every \(x\in S\),

\[
 \boxed{
 \mu_{x,a}^{A}
 =\nu_{x,a}\sum_{k\ge 0}K_{A,a}^{,k}
 =\nu_{x,a}(I-K_{A,a})^{-1}.}
 \tag{ER}
\]

The inverse is the convergent Neumann resolvent. Indeed,

\[
 \sup_{z\in A}K_{A,a}(z,A)\le a<1.
 \tag{2.1}
\]

Thus discounted target occupation is exactly first entrance followed by all
possible target returns. First entrance carries preparation; the return
resolvent carries recurrence.

#### Proof

Let

\[
 \sigma_0:=\tau_A,
 \qquad
 \sigma_{k+1}:=\inf\{j>\sigma_k:Z_j\in A\}.
\]

On every sample path, the finite values among \(\sigma_0,\sigma_1,\ldots\)
are exactly the times \(j\ge0\) for which \(Z_j\in A\), including consecutive
visits. Hence, for \(B\subseteq A\),

\[
 \sum_{j\ge0}a^j\mathbf 1_{\{Z_j\in B\}}
 =\sum_{k\ge0}
   a^{\sigma_k}
   \mathbf 1_{\{\sigma_k<\infty\}}
   \mathbf 1_{\{Z_{\sigma_k}\in B\}}.
 \tag{2.2}
\]

Nonnegative Tonelli and the strong Markov property at successive \(\sigma_k\)
give

\[
 \mathbb E_x\!\left[
   a^{\sigma_k}
   \mathbf 1_{\{\sigma_k<\infty\}}
   \mathbf 1_{\{Z_{\sigma_k}\in B\}}
 \right]
 =\bigl(\nu_{x,a}K_{A,a}^{,k}\bigr)(B).
 \tag{2.3}
\]

Summing (2.3) proves the first equality in (ER). Since
\(\tau_A^+\ge1\) on \(\{\tau_A^+<\infty\}\),

\[
 K_{A,a}(z,A)
 \le a\,\mathbb P_z(\tau_A^+<\infty)
 \le a.
\]

Therefore the kernel has total-mass operator norm at most \(a<1\), its Neumann
series converges, and the second equality follows. \(\square\)

### Corollary 2.2 (stopped Green decomposition)

Define the unnormalised endpoint Green occupation

\[
 G_a(x,A):=\sum_{j\ge0}a^j\mathbb P_x(Z_j\in A).
\]

Also let

\[
 G_a(z,A):=\sum_{j\ge0}a^j\mathbb P_z(Z_j\in A),
 \qquad z\in A.
\]

Then

\[
 \boxed{
 G_a(x,A)
 =\mathbb E_x\!\left[
     a^{\tau_A}\mathbf 1_{\{\tau_A<\infty\}}
     G_a(Z_{\tau_A},A)
   \right].}
 \tag{SG}
\]

Consequently, if

\[
 g_-\le G_a(z,A)\le g_+
 \qquad(z\in A),
\]

then

\[
 g_-F_a(x,A)\le G_a(x,A)\le g_+F_a(x,A).
 \tag{2.4}
\]

#### Proof

Before \(\tau_A\), the occupation sum is zero. On
\(\{\tau_A<\infty\}\), shift the remaining sum by \(\tau_A\):

\[
 \sum_{j\ge0}a^j\mathbf 1_A(Z_j)
 =a^{\tau_A}
  \sum_{k\ge0}a^k\mathbf 1_A(Z_{\tau_A+k}).
\]

Take expectation and apply the strong Markov property. The bounds follow by
integrating \(g_-\le G_a(Z_{\tau_A},A)\le g_+\) against the entrance measure.
\(\square\)

### Corollary 2.3 (singleton preparation--recurrence product)

For \(A=\{y\}\), put

\[
 R_a(y):=\mathbb E_y\!\left[
   a^{\tau_y^+}\mathbf 1_{\{\tau_y^+<\infty\}}
 \right].
\]

Then \(R_a(y)\le a<1\) and

\[
 \boxed{
 G_a(x,y)
 =F_a(x,y)G_a(y,y)
 =\frac{F_a(x,y)}{1-R_a(y)}.}
 \tag{PR}
\]

#### Proof

Equation (SG) gives \(G_a(x,y)=F_a(x,y)G_a(y,y)\). Starting at \(y\),
the time-zero visit contributes one. Applying the strong Markov property at
\(\tau_y^+\) to all later visits gives

\[
 G_a(y,y)=1+R_a(y)G_a(y,y).
\]

Solve using \(R_a(y)<1\). \(\square\)

This identity exposes the defect in treating endpoint Green mass as pure
preparation cost: \(F_a\) measures first arrival, whereas
\((1-R_a)^{-1}\) measures repeated return after arrival.

### Corollary 2.4 (fixed-fugacity Green--entrance equivalence)

For every target set \(A\), define normalized endpoint occupation

\[
 \overline G_a(x,A):=(1-a)G_a(x,A).
\]

Then

\[
 \boxed{
 (1-a)F_a(x,A)
 \le\overline G_a(x,A)
 \le F_a(x,A).}
 \tag{GEQ}
\]

Whenever \(F_a(x,A)>0\),

\[
 \boxed{
 0\le
 -\log\overline G_a(x,A)+\log F_a(x,A)
 \le-\log(1-a).}
 \tag{SEQ}
\]

#### Proof

For every \(z\in A\), the time-zero visit and the geometric-series ceiling
give

\[
 1\le G_a(z,A)\le\frac1{1-a}.
\]

Apply Corollary 2.2 with \(g_-=1\), \(g_+=(1-a)^{-1}\), then multiply by
\(1-a\). Taking logarithms proves (SEQ). \(\square\)

Thus return contamination is exact and conceptually important, but at fixed
positive fugacity it changes surprisal by only an additive constant. It cannot
by itself improve or destroy a Brown-scale exponential rate.

## 3. Gate-word specialization

Let \(\Gamma\) be a finite gate alphabet with \(|\Gamma|=M\ge1\). Let letters
act on a state space and fix a seed \(\chi\). On the transformation semigroup
generated by \(\Gamma\), run the right random walk

\[
 W_0=1,
 \qquad
 W_{\ell+1}=W_\ell g_{\ell+1},
\]

where the letters are independent and uniform. For a word
\(w=(g_1,\ldots,g_\ell)\), write

\[
 w\chi:=g_1\cdots g_\ell\chi,
 \qquad |w|=\ell.
\]

Thus words are built by right extension. This is a reversal of ordinary
chronological circuit labels: it preserves every length-\(\ell\) circuit, the
uniform prior on descriptions, and minimum circuit length, but it need not
have the same joint path law as physically appending gates at the output end
when gates do not commute. The observable is a synthesis-word first-entrance
process, not a claim about physical random-circuit time.

For a state target \(A\), put

\[
 \widetilde A:=\{W:W\chi\in A\}
\]

in the transformation semigroup. The first-hit time below is the Markov-chain
entrance time of \(W_\ell\) into \(\widetilde A\). We abbreviate

\[
 F_a(\chi,A):=F_a(1,\widetilde A).
\]

Thus the renewal law of Section 2 applies without requiring the evaluated
state process \(W_\ell\chi\) itself to be Markov.

Fix a target set \(A\). Define the first-hit language

\[
 \mathcal H_A
 :=\left\{
 w:\ w\chi\in A
 \text{ and }u\chi\notin A
 \text{ for every proper prefix }u\prec w
 \right\}.
\]

If \(\chi\in A\), then \(\mathcal H_A\) consists only of the empty word.

### Theorem 3.1 (prefix-free first-hit partition function)

The language \(\mathcal H_A\) is prefix-free and

\[
 \boxed{
 F_a(\chi,A)
 =\sum_{w\in\mathcal H_A}\left(\frac aM\right)^{|w|}.}
 \tag{FH}
\]

Moreover,

\[
 \boxed{
 \sum_{w\in\mathcal H_A}M^{-|w|}\le1.}
 \tag{Kraft}
\]

#### Proof

If distinct \(u,v\in\mathcal H_A\) and \(u\) were a proper prefix of \(v\),
the path associated with \(v\) would already enter \(A\) at time \(|u|\),
contradicting first entrance at time \(|v|\). Thus \(\mathcal H_A\) is
prefix-free.

For every \(\ell\), first entrance at time \(\ell\) partitions into the
disjoint length-\(\ell\) word cylinders indexed by
\(\mathcal H_A\cap\Gamma^\ell\). Each cylinder has probability \(M^{-\ell}\).
Therefore

\[
 \mathbb P_\chi(\tau_A=\ell)
 =\frac{|\mathcal H_A\cap\Gamma^\ell|}{M^\ell}.
\]

Multiplying by \(a^\ell\) and summing proves (FH). Prefix-free cylinders are
disjoint in the infinite product space, so their total probability is at most
one, proving (Kraft). \(\square\)

No faithfulness or freeness of the gate action is required. Different words
may have the same endpoint.

## 4. Exact circuit-complexity bounds and tropical recovery

Define target-set word complexity

\[
 C_A(\chi):=\inf\{|w|:w\chi\in A\}\in\mathbb N\cup\{\infty\}.
\]

For an \(\varepsilon\)-tube \(A=B_\varepsilon(v)\), this is robust circuit
complexity \(C_\varepsilon(v)\) relative to \(\chi\) and \(\Gamma\).

### Theorem 4.1 (loop-free complexity sandwich)

If \(c:=C_A(\chi)<\infty\), then

\[
 \boxed{
 \left(\frac aM\right)^c
 \le F_a(\chi,A)
 \le a^c.}
 \tag{CS}
\]

If \(C_A(\chi)=\infty\), then \(F_a(\chi,A)=0\).

#### Proof

A shortest hitting word has no hitting proper prefix, so it belongs to
\(\mathcal H_A\) and contributes \((a/M)^c\) to (FH). This proves the lower
bound. On every hitting path, \(\tau_A\ge c\); hence

\[
 F_a(\chi,A)
 =\mathbb E_\chi[a^{\tau_A}\mathbf 1_{\{\tau_A<\infty\}}]
 \le a^c.
\]

Unreachability is equivalent to \(\tau_A=\infty\) almost surely because every
finite gate word has positive cylinder probability. \(\square\)

### Corollary 4.2 (exact zero-fugacity exponent)

For finite \(C_A(\chi)\),

\[
 \boxed{
 C_A(\chi)
 =\lim_{a\downarrow0}
   \frac{-\log F_a(\chi,A)}{\log(1/a)}.}
 \tag{TR}
\]

#### Proof

Taking negative logarithms in (CS) gives

\[
 c\log(1/a)
 \le-\log F_a(\chi,A)
 \le c\log(M/a).
\]

Divide by \(\log(1/a)\). Since
\(\log(M/a)/\log(1/a)\to1\), squeeze. \(\square\)

This recovery is immune to every circuit suffix appended after the first hit.

## 5. Exact information projection on first-hit words

Put the geometric gate prior on all finite words:

\[
 \pi_a(w):=(1-a)\left(\frac aM\right)^{|w|}.
\]

It is a probability distribution because there are \(M^\ell\) words of
length \(\ell\). Equation (FH) gives

\[
 \pi_a(\mathcal H_A)=(1-a)F_a(\chi,A).
 \tag{5.1}
\]

### Theorem 5.1 (loop-free synthesis divergence)

Among all probability distributions \(Q\) supported on \(\mathcal H_A\),

\[
 \boxed{
 \inf_{Q:\,Q(\mathcal H_A)=1}D(Q\Vert\pi_a)
 =-\log\bigl((1-a)F_a(\chi,A)\bigr).}
 \tag{IP}
\]

The unique minimizer on positive-prior words is the conditioned prior

\[
 Q_A^*(w)
 =\frac{(a/M)^{|w|}}{F_a(\chi,A)},
 \qquad w\in\mathcal H_A.
\]

#### Proof

Let \(\pi_a^A:=\pi_a(\,\cdot\mid\mathcal H_A)\). For every admissible \(Q\),

\[
 D(Q\Vert\pi_a)
 =D(Q\Vert\pi_a^A)-\log\pi_a(\mathcal H_A).
\]

The first term is nonnegative and vanishes exactly at \(Q=\pi_a^A\). Apply
(5.1). \(\square\)

### Corollary 5.2 (energy--multiplicity identity)

For \(W\sim Q_A^*\),

\[
 \boxed{
 -\log F_a(\chi,A)
 =\log(M/a)\,\mathbb E|W|-H(W).}
 \tag{EM}
\]

#### Proof

Directly expand

\[
 D(Q_A^*\Vert\pi_a)
 =-H(W)-\log(1-a)+\log(M/a)\mathbb E|W|
\]

and compare with (IP). \(\square\)

Thus first-hit free energy is exact mean synthesis length minus the entropy of
distinct successful first-entry routes. It does not count post-success loops.

## 6. Complete circuit union in one first-hit moment

Let \(V\) be any random target, let \(A(V)\) be its target tube, and let
\(\mathcal R\) be any retained event. Put

\[
 C(V):=C_{A(V)}(\chi),
 \qquad
 F_a(V):=F_a(\chi,A(V)).
\]

### Theorem 6.1 (first-hit complete-union bound)

For every integer \(s\ge0\),

\[
 \boxed{
 \mathbb P\bigl(\mathcal R\cap\{C(V)\le s\}\bigr)
 \le\left(\frac Ma\right)^s
    \mathbb E\!\left[
      \mathbf 1_{\mathcal R}F_a(V)
    \right].}
 \tag{CU}
\]

#### Proof

On \(\{C(V)\le s\}\), Theorem 4.1 and \(a/M<1\) imply

\[
 F_a(V)\ge(a/M)^{C(V)}\ge(a/M)^s.
\]

Therefore

\[
 \mathbf 1_{\mathcal R\cap\{C(V)\le s\}}
 \le(M/a)^s\mathbf 1_{\mathcal R}F_a(V).
\]

Take expectation. \(\square\)

This absorbs the union over every circuit of length at most \(s\), while
discarding all word suffixes after first success.

## 7. Exact recurrence collapse

If the target tube contains the seed \(\chi\), then \(\tau_A=0\),
\(\mathcal H_A=\{\varnothing\}\), and

\[
 \boxed{F_a(\chi,A)=1.}
 \tag{RC}
\]

Hence the first-hit surprisal \(-\log F_a\) collapses exactly to zero at every
exact or tolerance-level recurrence to the seed. In contrast, endpoint Green
occupation generally retains the return multiplier in (ER) or (PR).

## 8. Conjecture tournament and failures

### C1. Raw endpoint Green mass is pure preparation cost

Label: `[FALSIFIED AS AN EXACT INTERPRETATION; RATE-EQUIVALENT]`.

Reason: (PR) gives

\[
 G_a(x,y)=F_a(x,y)/(1-R_a(y)).
\]

The factor \((1-R_a(y))^{-1}\) counts visits after preparation has already
succeeded. For target tubes, (ER) replaces this scalar by the full return
resolvent. Raw endpoint mass therefore mixes synthesis and recurrence.
However, Corollary 2.4 proves that normalized Green and first-entrance
surprisals differ by at most \(-\log(1-a)\). Raw Green remains quantitatively
valid for fixed-fugacity exponential-rate estimates.

### C2. Removing post-hit suffixes destroys the complete circuit union

Label: `[FALSIFIED]`.

Reason: every successful word has a unique shortest prefix that first enters
the target. Theorem 6.1 retains the complete short-circuit union using only
those first-entry prefixes.

### C3. First-hit words may still have uncontrolled prefix multiplicity

Label: `[FALSIFIED]`.

Reason: Theorem 3.1 proves exact prefix-freeness and Kraft mass at most one.
Endpoint collisions between distinct first-hit words remain possible, but are
represented honestly by the entropy term in (EM).

### C4. Fixed positive fugacity is equivalent to shortest-word complexity

Label: `[FALSIFIED]`.

At fixed \(a\), \(-\log F_a\) is a free energy over every first-entry path,
not the minimum length. Only the zero-fugacity exponent recovers complexity
exactly. A Brown-scale fixed-\(a\) theorem must control first-entry path
multiplicity, not silently identify free energy with minimum complexity.

### C5. First entrance supplies the missing static-local estimate

Label: `[OPEN]`.

No theorem here bounds \(F_a\) for endpoints of an ordinary time-independent
local Hamiltonian. The exact open core is a quenched lower-tail or expectation
bound for

\[
 F_a\bigl(\chi,B_\varepsilon(e^{-itH}\chi)\bigr)
\]

at the geometric Brown skeleton times, after a common recurrence or
fast-forwardable-carrier removal, strong enough for (CU).

## 9. Consequence for the Brown--Susskind programme

This card changes the correct object but does not close the programme.

The raw killed gate-walk Green observable has two independent sources of mass:

\[
 \boxed{
 \text{endpoint occupation}
 =\text{first preparation}
 \times\text{return resolvent}.}
\]

For circuit-complexity growth, the first factor is the relevant one. For
recurrence, the second factor is itself physical mathematical data. Conflating
them can make a highly recurrent easy target look artificially easy to prepare
from an unrelated seed.

The next admissible frontier statement must therefore be formulated in terms
of first-entrance mass or entrance measure. It must not infer a Brown ramp from
raw Green occupation.

## 10. Hostile audit

1. **Is the theorem new?** The general renewal, Kraft, and information
   projection mechanisms are classical. The card makes no theorem-level
   novelty claim.
2. **Does it prove static-local circuit growth?** No.
3. **Does it prove a black-hole statement?** No.
4. **Does it hide post-hit padding?** No; all successful suffixes are removed
   by first entrance.
5. **Does it hide pre-hit route multiplicity?** No; it appears exactly as
   \(H(W)\) in (EM).
6. **Does it require a faithful gate action?** No.
7. **Does it recover robust complexity?** Yes, when \(A\) is the chosen robust
   target tube, through (TR).
8. **What remains hardest?** A quenched anti-shadowing estimate for
   first-entry gate paths against ordinary static local-Hamiltonian endpoints.
9. **Why is this progress?** It corrects the interpretation, separates the
   preparation lower-tail problem from return amplification exactly, and
   proves that this correction changes no fixed-fugacity Brown exponent.
10. **Why not publication-ready?** It is a bridge, not the missing
    static-local theorem, and external priority is not established.

## 11. Formalization plan

Lean formalization is intentionally deferred while the corpus is being
refactored, per user instruction. A later dependency-light formalization can be
split into:

1. finite-word first-hit predicate and prefix-freeness;
2. finite-depth Kraft inequality;
3. finite-depth first-hit partition identity;
4. complexity sandwich and finite-depth complete-union bound;
5. finite-state discounted entrance/return matrix identity;
6. KL information projection on a finite first-hit support;
7. passage to infinite depth by monotone convergence, if the analytic
   infrastructure is ready.

No Lean process was started for this card.

## 12. Dependencies and child frontier

Parents:

- `gate-walk-green-bellman-tropicalization-law.md`
- `circuit-complexity-selection-synthesis-divergence-law.md`
- `geometric-skeleton-brown-ramp-transfer-law.md`

Child frontier:

- `synthesis-divergence-brown-law.md`, to be reformulated with first-entrance
  mass rather than raw endpoint Green occupation.
