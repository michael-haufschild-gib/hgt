# First-Entrance Gate Capacity and Discrepancy Law

Status: `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN DEFERRED DURING REFACTOR]`

Date: 2026-08-10

## Scope and scientific label

This card identifies the exact potential-theoretic invariant behind the
first-entrance circuit observable. For a reversible local-gate walk,
discounted first-hit probability is the equilibrium potential of the target,
its Dirichlet energy is discounted capacity, and its stationary mean is
capacity divided by killing rate.

Dirichlet principles, equilibrium potentials, capacity, and dual-energy
estimates are classical. No novelty is claimed for those ingredients. The
candidate research advance is the exact composition with robust gate-word
complexity, complete circuit union, and permanently non-Haar static endpoint
laws. External priority for that composition is unverified.

No static-local Brown estimate is proved here.

## 1. Reversible killed gate walk

Let \(S\) be a finite state space, let \(P\) be a Markov kernel on \(S\), and
let \(\pi\) be a strictly positive reversible stationary law:

\[
 \pi(x)P(x,y)=\pi(y)P(y,x).
\]

Fix \(a\in(0,1)\) and define the positive killed operator

\[
 L_a:=I-aP.
\]

On real functions with
\(\langle f,g\rangle_\pi=\sum_x\pi(x)f(x)g(x)\), reversibility makes
\(P\) and \(L_a\) self-adjoint. Since the spectrum of \(P\) lies in
\([-1,1]\),

\[
 \langle f,L_af\rangle_\pi\ge(1-a)\|f\|_{L^2(\pi)}^2.
 \tag{1.1}
\]

Let \(A\subseteq S\) be nonempty and define

\[
 h_A(x):=\mathbb E_x\!\left[
   a^{\tau_A}\mathbf 1_{\{\tau_A<\infty\}}
 \right].
 \tag{1.2}
\]

This is the first-entrance mass from the parent card.

## 2. Bellman--Dirichlet equivalence

### Theorem 2.1 (equilibrium-potential law)

The function \(h_A\) is the unique solution of

\[
 \boxed{
 h_A=1\text{ on }A,
 \qquad
 h_A=aPh_A\text{ on }A^c.}
 \tag{BD}
\]

It is also the unique minimizer of

\[
 \mathcal E_a(f):=\langle f,L_af\rangle_\pi
 \tag{2.1}
\]

over all real \(f\) satisfying \(f=1\) on \(A\).

#### Proof

If \(x\in A\), then \(\tau_A=0\), so \(h_A(x)=1\). If \(x\notin A\),
condition on the first step and use the Markov property:

\[
 h_A(x)=a\sum_yP(x,y)h_A(y)=aPh_A(x).
\]

Uniqueness follows because the difference \(u\) of two solutions vanishes on
\(A\), obeys \(u=aPu\) on \(A^c\), and at a point of maximal \(|u|\) satisfies
\(\|u\|_\infty\le a\|u\|_\infty\). Thus \(u=0\).

For the variational statement, write any admissible \(f=h_A+g\), where
\(g=0\) on \(A\). Equation (BD) says \(L_ah_A=0\) on \(A^c\). Hence

\[
 \langle g,L_ah_A\rangle_\pi=0
\]

and self-adjointness gives

\[
 \mathcal E_a(f)
 =\mathcal E_a(h_A)+\mathcal E_a(g).
\]

Strict positivity (1.1) makes the second term nonnegative, with equality only
for \(g=0\). \(\square\)

### Corollary 2.2 (exact gate-gradient energy)

For every real \(f\),

\[
 \boxed{
 \mathcal E_a(f)
 =(1-a)\sum_x\pi(x)f(x)^2
 +\frac a2\sum_{x,y}\pi(x)P(x,y)(f(x)-f(y))^2.}
 \tag{GE}
\]

#### Proof

Use

\[
 I-aP=(1-a)I+a(I-P)
\]

and the standard reversible identity

\[
 \langle f,(I-P)f\rangle_\pi
 =\frac12\sum_{x,y}\pi(x)P(x,y)(f(x)-f(y))^2.
\]

\(\square\)

Unlike a smooth threshold polynomial evaluated at an exact hit, the
first-entrance reporter has a Dirichlet boundary value. Its relevant one-step
quantity is the nonzero energy (GE), not a derivative of a flat fidelity
reporter.

## 3. Discounted capacity and charge

Define the discounted capacity of \(A\) by

\[
 \operatorname{cap}_a(A)
 :=\mathcal E_a(h_A).
 \tag{3.1}
\]

Define equilibrium charge

\[
 q_A:=L_ah_A.
\]

### Theorem 3.1 (charge support and stationary mean)

The charge is supported on \(A\), satisfies \(q_A\ge0\), and

\[
 \boxed{
 \operatorname{cap}_a(A)
 =\sum_{x\in A}\pi(x)q_A(x)
 =(1-a)\sum_x\pi(x)h_A(x).}
 \tag{CM}
\]

Equivalently,

\[
 \boxed{
 \mathbb E_{X\sim\pi}
 \mathbb E_X\!\left[
   a^{\tau_A}\mathbf 1_{\{\tau_A<\infty\}}
 \right]
 =\frac{\operatorname{cap}_a(A)}{1-a}.}
 \tag{SM}
\]

#### Proof

Equation (BD) gives \(q_A=0\) on \(A^c\). Since \(0\le h_A\le1\), for
\(x\in A\),

\[
 q_A(x)=1-aPh_A(x)\ge1-a>0.
\]

Because \(h_A=1\) on the support of \(q_A\),

\[
 \operatorname{cap}_a(A)
 =\langle h_A,q_A\rangle_\pi
 =\sum_{x\in A}\pi(x)q_A(x).
\]

Self-adjointness and \(L_a1=(1-a)1\) give

\[
 \sum_x\pi(x)q_A(x)
 =\langle1,L_ah_A\rangle_\pi
 =\langle L_a1,h_A\rangle_\pi
 =(1-a)\sum_x\pi(x)h_A(x).
\]

Apply (1.2). \(\square\)

### Corollary 3.2 (sharp elementary capacity window)

\[
 \boxed{
 (1-a)\pi(A)
 \le\operatorname{cap}_a(A)
 \le\min\{\pi(A),1-a\}.}
 \tag{CW}
\]

#### Proof

The lower bound follows from (CM), \(h_A=1\) on \(A\), and \(h_A\ge0\).
For the upper bounds, use the Dirichlet principle with the admissible test
functions \(1_A\) and \(1\):

\[
 \operatorname{cap}_a(A)
 \le\langle1_A,L_a1_A\rangle_\pi
 =\pi(A)-a\langle1_A,P1_A\rangle_\pi
 \le\pi(A),
\]

and

\[
 \operatorname{cap}_a(A)\le\langle1,L_a1\rangle_\pi=1-a.
\]

\(\square\)

Thus stationary first-entrance mass differs from target volume by at most the
fixed factor \((1-a)^{-1}\):

\[
 \pi(A)
 \le\mathbb E_\pi h_A
 \le\frac{\pi(A)}{1-a}.
 \tag{3.2}
\]

## 4. Exact non-Haar discrepancy transfer

Let \(\nu\) be any probability law on \(S\), write

\[
 r:=\frac{d\nu}{d\pi},
 \qquad
 g:=r-1,
\]

and define the directional capacity discrepancy

\[
 \delta_{A,a}(\nu)
 :=\langle g,h_A\rangle_\pi.
 \tag{4.1}
\]

Also define the global killed negative-energy discrepancy

\[
 \|\nu-\pi\|_{-1,a}
 :=\sqrt{\langle g,L_a^{-1}g\rangle_\pi}.
 \tag{4.2}
\]

### Theorem 4.1 (capacity-discrepancy law)

For every nonempty target \(A\),

\[
\boxed{
 \mathbb E_{X\sim\nu}h_A(X)
 =\frac{\operatorname{cap}_a(A)}{1-a}
  +\delta_{A,a}(\nu),}
 \tag{CD0}
\]

and

\[
 \boxed{
 |\delta_{A,a}(\nu)|
 \le
 \sqrt{\operatorname{cap}_a(A)}
 \|\nu-\pi\|_{-1,a}.}
 \tag{CD}
\]

#### Proof

By (SM),

\[
 \mathbb E_\nu h_A-\frac{\operatorname{cap}_a(A)}{1-a}
 =\langle g,h_A\rangle_\pi.
\]

Since \(L_a\) is positive definite, Cauchy--Schwarz after inserting
\(L_a^{-1/2}L_a^{1/2}\) gives

\[
 |\langle g,h_A\rangle_\pi|
 \le
 \sqrt{\langle g,L_a^{-1}g\rangle_\pi}
 \sqrt{\langle h_A,L_ah_A\rangle_\pi}.
\]

The second square root is \(\sqrt{\operatorname{cap}_a(A)}\). \(\square\)

The exact identity (CD0) tests only the equilibrium potential associated with
the chosen target. The norm estimate (CD) is only a sufficient bound, and the
next theorem shows that it is generally too strong for the intended static
ensemble.

### Theorem 4.2 (global discrepancy obstruction)

For every \(\nu\),

\[
 \boxed{
 \|\nu-\pi\|_{-1,a}^2
 \ge\frac{\chi^2(\nu\Vert\pi)}{1+a}.}
 \tag{GO}
\]

If \(\nu\) is supported on \(B\subseteq S\) with \(\pi(B)=\beta\), then

\[
 \boxed{
 \|\nu-\pi\|_{-1,a}^2
 \ge\frac{\beta^{-1}-1}{1+a}.}
 \tag{GS}
\]

#### Proof

The spectrum of \(L_a=I-aP\) is contained in
\([1-a,1+a]\). Hence

\[
 L_a^{-1}\succeq\frac1{1+a}I
\]

and

\[
 \|\nu-\pi\|_{-1,a}^2
 \ge\frac{\|g\|_{L^2(\pi)}^2}{1+a}
 =\frac{\chi^2(\nu\Vert\pi)}{1+a}.
\]

If \(r=d\nu/d\pi\) vanishes outside \(B\), Cauchy--Schwarz gives

\[
 1=\left(\sum_{x\in B}\pi(x)r(x)\right)^2
 \le\beta\sum_{x\in B}\pi(x)r(x)^2.
\]

Thus \(\chi^2(\nu\Vert\pi)=\sum_x\pi(x)r(x)^2-1\ge\beta^{-1}-1\).
\(\square\)

### Corollary 4.3 (directional matching without Haar convergence)

If the real function space on \(S\) has a nonzero vector \(g\) orthogonal to
both \(1\) and \(h_A\), then for all sufficiently small nonzero real
\(\eta\),

\[
 \nu_\eta(x):=\pi(x)(1+\eta g(x))
\]

is a probability law distinct from \(\pi\) with

\[
 \boxed{\delta_{A,a}(\nu_\eta)=0.}
 \tag{DM}
\]

#### Proof

Orthogonality to \(1\) gives total mass one; small \(|\eta|\) gives
nonnegativity; orthogonality to \(h_A\) gives (DM). \(\square\)

Therefore a distribution can remain non-Haar in many observable directions
while agreeing exactly with Haar on the first-entrance observer. The correct
Brown target is directional \(\delta_{A,a}\), not global
\(\|\nu-\pi\|_{-1,a}\).

## 5. Inverse-word conversion for circuit targets

Let a finite inverse-closed gate alphabet \(\Gamma\), \(|\Gamma|=M\), act by
isometries on a metric state space. Fix a seed \(\chi\). Enumerate circuit
words by right extension,

\[
 W_\ell=g_1\cdots g_\ell.
\]

This is only a reversal of the ordinary chronological word labels; it
preserves the set of length-\(\ell\) circuits, the uniform word prior, and
minimum word length.

For a target \(v\), define the backward path

\[
 X_0=v,
 \qquad
 X_{\ell+1}=g_{\ell+1}^{-1}X_\ell.
\]

Then \(X_\ell=W_\ell^{-1}v\), and isometry gives

\[
 \boxed{
 d(W_\ell\chi,v)=d(\chi,X_\ell).}
 \tag{IW}
\]

Because inversion permutes \(\Gamma\), the backward process uses the same
uniform gate law. Hence the first time a word-built circuit enters
\(B_\varepsilon(v)\) is exactly the first time the backward gate walk from
\(v\) enters the fixed seed tube

\[
 A_\varepsilon:=B_\varepsilon(\chi).
\]

Consequently,

\[
 \boxed{
 \mathcal F_{a,\varepsilon}(v)
 =h_{A_\varepsilon}(v).}
 \tag{IF}
\]

No target translation symmetry is needed. The only requirements are
inverse-closed uniform word prior and isometric gate action.

## 6. Capacity form of the complete circuit union

Assume the backward gate walk in Section 5 descends to the finite reversible
chain of Section 1. Let \(V\) be a random circuit target with law \(\nu\), and
write \(C_\varepsilon(V)\) for its robust circuit complexity from \(\chi\).
The parent first-entrance union law, (IF), and (SM) give:

### Theorem 6.1 (stationary capacity union bound)

If \(V\sim\pi\), then for every integer \(s\ge0\),

\[
 \boxed{
 \mathbb P_\pi\{C_\varepsilon(V)\le s\}
 \le
 \left(\frac Ma\right)^s
 \frac{\operatorname{cap}_a(A_\varepsilon)}{1-a}.}
 \tag{CUC}
\]

By (CW),

\[
 \mathbb P_\pi\{C_\varepsilon(V)\le s\}
 \le
 \left(\frac Ma\right)^s
 \frac{\pi(A_\varepsilon)}{1-a}.
 \tag{6.1}
\]

Thus first entrance does not make the stationary circuit entropy disappear;
it recovers the expected target-volume competition within a fixed killing
factor.

### Theorem 6.2 (nonstationary capacity union bound)

For an arbitrary target law \(\nu\),

\[
\boxed{
 \mathbb P_\nu\{C_\varepsilon(V)\le s\}
 \le\left(\frac Ma\right)^s
 \left[
  \frac{\operatorname{cap}_a(A_\varepsilon)}{1-a}
  +\delta_{A_\varepsilon,a}(\nu)
 \right].}
 \tag{NCU0}
\]

Consequently,

\[
 \boxed{
 \mathbb P_\nu\{C_\varepsilon(V)\le s\}
 \le\left(\frac Ma\right)^s
 \left[
  \frac{\operatorname{cap}_a(A_\varepsilon)}{1-a}
  +\sqrt{\operatorname{cap}_a(A_\varepsilon)}
   \|\nu-\pi\|_{-1,a}
 \right].}
 \tag{NCU}
\]

#### Proof

Apply the first-entrance complete-union inequality. Equation (IF) identifies
the expected first-hit mass with
\(\mathbb E_\nu h_{A_\varepsilon}\); (CD0) proves (NCU0), and (CD) proves
(NCU). \(\square\)

## 7. Conjecture tournament

### C0. A smooth bounded-threshold reporter supplies first-order dissipation

Label: `[FALSIFIED BY PARENT]`.

At an exact occupied target, the reporter has high contact-order flatness, so
ordinary carré du champ vanishes despite transverse local-word leakage.

### C1. Replace threshold derivatives by first-entrance equilibrium potential

Label: `[PAPER-PROVED]`.

Theorems 2.1--3.1 show that the correct Bellman reporter has exact Dirichlet
energy equal to capacity and a charge supported on the target.

### C2. Discounted capacity alone beats the complete circuit union

Label: `[FALSIFIED]`.

For homogeneous stationary targets, (SM), (CW), and (CUC) show that capacity
reduces to target volume up to a constant depending only on \(a\). The full
gate-word entropy remains. Capacity is the correct invariant, not an automatic
Brown estimate.

### C3. Full approach to Haar is required

Label: `[FALSIFIED AS A LOGICAL REQUIREMENT]`.

Equations (CD0) and (DM) show that only one directional
equilibrium-potential discrepancy is relevant to this test. A law may remain
distinguishable from Haar by other observables while matching Haar exactly on
the first-entrance potential.

### C4. Control the global negative-energy norm

Label: `[FALSIFIED AS THE FRONTIER TARGET]`.

Theorem 4.2 shows that this norm lower-bounds \(\chi^2\)-distance. Low-support
or singular static endpoint laws cannot converge in it at the required scale.
Using (CD) as the final estimate would reintroduce an unnecessary global-Haar
requirement and conflict with the programme's permanent locality witness.

### C5. Static-local directional capacity discrepancy closes Brown growth

Label: `[OPEN]`.

For ordinary time-independent local-Hamiltonian endpoints, prove a quenched or
annealed bound directly on the translated analogue of
\(\delta_{A,a}(\nu_{n,t})\), whose exponent survives (NCU0) at Brown depth.
No global norm is requested.

## 8. Frontier consequence

The contact-order problem has a precise replacement:

\[
 \boxed{
 \text{threshold jet}
 \longrightarrow
 \text{first-entrance equilibrium potential}
 \longrightarrow
 \text{gate Dirichlet capacity}.}
\]

The remaining static-Hamiltonian problem is no longer an unspecified
"anti-concentration" statement. It is a signed directional
capacity-discrepancy estimate against one Bellman-generated observer class.
Theorems 4.2 and Corollary 4.3 prove why global Haar convergence is both too
strong and unnecessary.

What remains unproved is the hard transfer from static-shell coefficient
geometry or growing replicas to this gate-Dirichlet observer. The local-word
leakage theorem controls gate directions sheetwise, but no theorem yet carries
that leakage through the equilibrium potential under the quenched static
ensemble.

## 9. Hostile audit

1. **Classical engine.** The reversible Dirichlet principle is standard
   potential theory. It is not a novelty claim.
2. **Finite state.** The proof is finite-dimensional. Compact-state extension
   requires analytic domain and regularity work.
3. **No static density.** A fixed-time static endpoint law may be singular
   relative to Haar. The exact directional pairing still makes sense for
   measures, but the density-norm estimate (CD) then requires a finite-state
   discretization or a measure-energy extension.
4. **No Brown ramp.** Neither (CD) nor (NCU) proves the needed discrepancy
   exponent.
5. **No automatic circuit-entropy gain.** (CUC) explicitly retains it.
6. **Contact order only repaired on gate graph.** A transfer from static
   coefficient derivatives to gate-graph energy is still missing.
7. **Why this is progress.** It replaces a false high-order-jet target by an
   exact variational observable, proves that global resolvent convergence is
   the wrong invariant, and isolates the single signed directional discrepancy
   that must beat the circuit union.

## 10. External comparison

Classical potential theory for Markov chains treats equilibrium potentials,
capacities, Green functions, and Dirichlet principles; for example,
Gaudilliere--Landim, *A Dirichlet principle for non reversible Markov chains
and some recurrence theorems*, arXiv:1111.2445, develops more general
nonreversible formulas. The present card makes no claim to those mechanisms.

The audited circuit-complexity literature establishes random-circuit growth
or studies gate-walk mixing/designs. It was not found to formulate the
ordinary static-local Brown problem as the capacity-discrepancy bound (NCU).
That negative search is not proof of priority.

## 11. Formalization plan

Lean is intentionally deferred during corpus refactor. Later finite-state
formalization can use matrices and weighted Euclidean inner products:

1. reversible self-adjointness of \(P\);
2. positivity of \(I-aP\);
3. finite hitting-time dynamic programming;
4. Dirichlet minimization by orthogonal energy decomposition;
5. charge and stationary-mean identity;
6. capacity window;
7. inverse-energy Cauchy--Schwarz;
8. composition with finite first-hit complete-union law.

No Lean process was started.

## 12. Dependencies

Parents:

- `first-entrance-gate-renewal-prefix-law.md`
- `all-replica-incidence-normalized-local-word-leakage-law.md`
- `gate-walk-green-bellman-tropicalization-law.md`

Child frontier:

- `synthesis-divergence-brown-law.md`
