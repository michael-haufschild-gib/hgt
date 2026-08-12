# Superposition--thinning Poisson formation, recovery isometry, and Gamma-six polarity law

**ID:** ULF-SRFM-1  
**Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [NOVELTY UNVERIFIED] [LEAN PENDING] [NOT RH]`

## 1. Purpose

This card treats a formation law, not a proof-route endpoint. It proves that three native operations—independent superposition, Bernoulli thinning, and mean calibration—determine the Poisson formation species. It then proves that common stochastic recovery is exactly information-neutral at the intensity level and applies the result to the literal Gamma-six packet.

The result supplies one exact chamber of a species-relative formation theory. It does not show that every corpus organ is Poissonian and does not derive a source theorem selecting the critical line.

## 2. Poisson formation is forced by native laws

### Theorem 2.1 (superposition--thinning characterization)

Let \((\nu_\lambda)_{\lambda\ge 0}\) be probability laws on \(\mathbb N\). Assume:

1. **vacuum:** \(\nu_0=\delta_0\);
2. **independent superposition:** \(\nu_{\lambda+\mu}=\nu_\lambda*\nu_\mu\);
3. **Bernoulli thinning:** if \(N\sim\nu_\lambda\) and each of its \(N\) particles is retained independently with probability \(p\in[0,1]\), then the retained count has law \(\nu_{p\lambda}\);
4. **mean calibration:** \(\mathbb E_{\nu_\lambda}N=\lambda<\infty\).

Then

\[
\nu_\lambda=\operatorname{Pois}(\lambda)
\qquad(\lambda\ge0).
\]

#### Proof

For \(z\in[0,1]\), let

\[
G_\lambda(z)=\mathbb E_{\nu_\lambda}z^N.
\]

Superposition gives

\[
G_{\lambda+\mu}(z)=G_\lambda(z)G_\mu(z),
\qquad G_0(z)=1.
\tag{2.1}
\]

For \(z\in(0,1]\), \(G_\lambda(z)>0\). Moreover

\[
0\le 1-G_\lambda(z)
=\mathbb E(1-z^N)
\le (1-z)\mathbb E N
=(1-z)\lambda.
\tag{2.2}
\]

Thus \(\lambda\mapsto G_\lambda(z)\) is continuous at \(0\). The continuous multiplicative Cauchy equation (2.1) therefore has the form

\[
G_\lambda(z)=e^{-\lambda c(z)}
\tag{2.3}
\]

for some \(c(z)\ge0\).

Thinning replaces \(z\) by \(1-p+pz\), hence

\[
G_\lambda(1-p+pz)=G_{p\lambda}(z).
\]

Using (2.3),

\[
c(1-p+pz)=p,c(z).
\tag{2.4}
\]

Fix \(0<z<u<1\) and choose

\[
p=\frac{1-u}{1-z}\in(0,1).
\]

Then \(1-p+pz=u\), so (2.4) gives

\[
\frac{c(u)}{1-u}=\frac{c(z)}{1-z}.
\]

Hence there is a constant \(C\ge0\) such that \(c(z)=C(1-z)\) for every \(z\in(0,1)\). Since \(\mathbb E N=\lambda\),

\[
\lambda
=\lim_{z\uparrow1}\frac{1-G_\lambda(z)}{1-z}
=\lim_{z\uparrow1}\frac{1-e^{-\lambda C(1-z)}}{1-z}
=\lambda C.
\]

For \(\lambda>0\), \(C=1\). Consequently

\[
G_\lambda(z)=e^{\lambda(z-1)},
\]

the probability generating function of \(\operatorname{Pois}(\lambda)\). Probability generating functions determine laws on \(\mathbb N\). ∎

### Interpretation

Poisson formation is not chosen because it is convenient or positive. It is forced once the source declares additive mass, independent superposition, Bernoulli restriction, and the normalization of the first moment. A different source algebra may force a different formation species.

## 3. Recovery preserves the complete intensity information

Let \(I\) be a finite source-label set. For positive intensity vectors \(a,b\in(0,\infty)^I\), define

\[
D_+(a\Vert b)
=\sum_{i\in I}
\left(a_i\log\frac{a_i}{b_i}-a_i+b_i\right).
\tag{3.1}
\]

Let \(P_a=\bigotimes_{i\in I}\operatorname{Pois}(a_i)\).

### Theorem 3.1 (Poisson information and common-recovery isometry)

1. The Kullback--Leibler divergence of the independent Poisson packet is

   \[
   D(P_a\Vert P_b)=D_+(a\Vert b).
   \tag{3.2}
   \]

2. Let \(K=(K_{ij})\) be a row-stochastic matrix from \(I\) to a finite mark set \(J\). Mark each source particle independently using row \(K_i\). The marked intensities are

   \[
   \widetilde a_{ij}=a_iK_{ij},
   \qquad
   \widetilde b_{ij}=b_iK_{ij}.
   \]

   Then

   \[
   D_+(\widetilde a\Vert\widetilde b)=D_+(a\Vert b).
   \tag{3.3}
   \]

3. Projection \((i,j)\mapsto i\) recovers the original packet: the sum of the marked counts over \(j\) is \(\operatorname{Pois}(a_i)\), independently in \(i\). Hence common marking is an exact lift through a common recovery kernel, not merely a data-processing inequality.

#### Proof

For one coordinate, direct summation of the Poisson log-likelihood ratio gives

\[
D(\operatorname{Pois}(a_i)\Vert\operatorname{Pois}(b_i))
=a_i\log(a_i/b_i)-a_i+b_i.
\]

Additivity of relative entropy under finite products proves (3.2).

For (3.3), terms with \(K_{ij}=0\) contribute zero, while for \(K_{ij}>0\),

\[
a_iK_{ij}\log\frac{a_iK_{ij}}{b_iK_{ij}}
-a_iK_{ij}+b_iK_{ij}
=K_{ij}
\left(a_i\log\frac{a_i}{b_i}-a_i+b_i\right).
\]

Sum over \(j\) and use \(\sum_jK_{ij}=1\). The recovery statement is the elementary Poisson splitting/superposition law. ∎

### Corollary 3.2 (mass--shape decomposition)

Put

\[
A=\sum_i a_i,
\quad B=\sum_i b_i,
\quad p_i=a_i/A,
\quad q_i=b_i/B.
\]

Then

\[
D_+(a\Vert b)
=A D(p\Vert q)+A\log(A/B)-A+B.
\tag{3.4}
\]

Thus probability normalization retains the shape term and erases the extensive mass coordinate. For the symmetrized divergence

\[
J_+(a,b)=D_+(a\Vert b)+D_+(b\Vert a),
\]

one has

\[
J_+(a,b)
=A D(p\Vert q)+B D(q\Vert p)
+(A-B)\log(A/B).
\tag{3.5}
\]

#### Proof

Substitute \(a_i=Ap_i\), \(b_i=Bq_i\) into (3.1) and sum. ∎

## 4. Literal Gamma-six packet

Fix shell \(m\ge3\). The Gamma-six packet has

\[
N_m=5\cdot6^m
\]

labelled coordinates and base eigenvalue

\[
\lambda_m=6^{-m}.
\]

Let \(\delta\in\mathbb R\) denote the displacement from the functional-equation centre and put

\[
x_m=m(\log6)\delta.
\]

Define forward and reflected coordinate intensities

\[
a_{m,i}=\lambda_m^{1-\delta},
\qquad
b_{m,i}=\lambda_m^{1+\delta}
\qquad(1\le i\le N_m).
\tag{4.1}
\]

Their total intensities are

\[
A_m=5e^{x_m},
\qquad B_m=5e^{-x_m}.
\tag{4.2}
\]

Both normalized shapes are uniform on the shell. Therefore projectivization erases \(\delta\) completely, while intensity formation retains it.

### Theorem 4.1 (exact functional-equation polarity)

Let \(P_m^+\) and \(P_m^-\) be the independent labelled Poisson packets with intensities (4.1). Then

\[
D(P_m^+\Vert P_m^-)
=2x_mA_m-A_m+B_m,
\tag{4.3}
\]

\[
D(P_m^-\Vert P_m^+)
=-2x_mB_m-B_m+A_m,
\tag{4.4}
\]

\[
J(P_m^+,P_m^-)=20x_m\sinh x_m,
\tag{4.5}
\]

and the directed chirality is

\[
\begin{aligned}
\chi_m(\delta)
&=D(P_m^+\Vert P_m^-)-D(P_m^-\Vert P_m^+)\\
&=20\bigl(x_m\cosh x_m-\sinh x_m\bigr).
\end{aligned}
\tag{4.6}
\]

The intensity Hellinger square and Poisson Hellinger affinity are

\[
H^2_{\mathrm{int},m}
=\sum_i(\sqrt{a_{m,i}}-\sqrt{b_{m,i}})^2
=10(\cosh x_m-1),
\tag{4.7}
\]

\[
\operatorname{Aff}(P_m^+,P_m^-)
=\exp[-5(\cosh x_m-1)].
\tag{4.8}
\]

The functional equation \(\delta\mapsto-\delta\) exchanges \(P_m^+\) and \(P_m^-\), preserves (4.5), and reverses (4.6).

#### Proof

The shell shapes coincide, so (3.4) reduces to the scalar mass term. Since \(\log(A_m/B_m)=2x_m\), equations (4.3)--(4.6) follow by elementary algebra. Equations (4.7)--(4.8) are the standard Hellinger formulas for Poisson laws, applied to equal coordinate intensities. ∎

The function

\[
V(x)=x\cosh x-\sinh x
\]

is already a corpus object (the hyperbolic virial). Equation (4.6) is therefore a bridge to an existing invariant, not a novelty claim.

## 5. Infinite formation and fixed-label selection consumer

Let

\[
P_\delta^+=\bigotimes_{m\ge3}P_m^+,
\qquad
P_\delta^-=\bigotimes_{m\ge3}P_m^-
\tag{5.1}
\]

on the fixed labelled shell-count space. The phrase fixed labelled is load-bearing: arbitrary abstract standard probability spaces are not the observer doctrine in question.

### Theorem 5.1 (global polarity)

\[
P_\delta^+\sim P_\delta^-
\quad\Longleftrightarrow\quad
\delta=0.
\tag{5.2}
\]

Indeed, at \(\delta=0\) the laws are identical. At every \(\delta\ne0\) they are mutually singular.

#### Proof

Assume \(\delta>0\); the negative case follows by exchanging signs. Let \(E_m\) be the event that shell \(m\) is nonempty. Under \(P_\delta^+\),

\[
P_\delta^+(E_m^c)=e^{-A_m}
=\exp[-5e^{m(\log6)\delta}],
\]

whose sum over \(m\) converges. Hence almost surely only finitely many shells are empty.

Under \(P_\delta^-\),

\[
P_\delta^-(E_m)=1-e^{-B_m}\le B_m
=5e^{-m(\log6)\delta},
\]

whose sum converges. Hence almost surely only finitely many shells are nonempty. These two eventual properties are disjoint. The first Borel--Cantelli lemma proves mutual singularity. ∎

### Corollary 5.2 (selection consumer, not producer)

Any independently proved source theorem asserting fixed-label functional-equation quasi-invariance

\[
P_\delta^+\sim P_\delta^-
\]

for the canonical Poisson formation forces \(\delta=0\).

This is not an RH proof. The missing theorem is precisely the source-side production of the Poisson formation laws and their fixed-label quasi-invariance before zero specialization.

## 6. What is proved and what is not

### Proved

- additive superposition + Bernoulli thinning + mean calibration uniquely determine Poisson formation;
- common marking and recovery preserve full Poisson relative information exactly;
- normalization is an explicit quotient from extensive intensity to probability shape;
- the literal Gamma-six packet has exact divergence, Hellinger, chirality, and functional-equation formulas;
- the global forward/reflected labelled formations are mutually singular off-centre and equal at the centre.

### Not proved

- that the rational-adelic source satisfies the independent-superposition and thinning hypotheses;
- that all corpus organs use Poisson formation;
- any comparison to exterior, Bose/Witt, phase-history, or hypertranscendental formation species;
- a source-native quasi-invariance theorem;
- RH.

## 7. Parent mathematics and collision audit

Poisson point-process divergence formulas and their absolute-continuity/singularity theory are established; see L. Leskelä, *Information divergences and likelihood ratios of Poisson processes and point patterns*, IEEE Transactions on Information Theory 70 (2024), [arXiv:2404.00294](https://arxiv.org/abs/2404.00294). The Poisson Hellinger/Bhattacharyya formula is also explicit in B.-N. Vo et al., *Cauchy--Schwarz divergence for Poisson point processes*, [arXiv:1312.6224](https://arxiv.org/abs/1312.6224). Positive-measure cone and unbalanced-transport geometry are established parent machinery; see T. Gallouët, R. Ghezzi, and F.-X. Vialard, *Regularity theory and geometry of unbalanced optimal transport*, [arXiv:2112.11056](https://arxiv.org/abs/2112.11056).

Internally, compound-Poisson chirality and the hyperbolic virial already exist. The new-to-this-card content is the exact source-law characterization, its common-recovery isometry, and the Gamma-six global fixed-label polarity synthesis. No external priority claim is made.

## 8. Lean boundary

No Lean theorem is claimed by this card. Required formal modules are:

1. a finite-law PGF characterization of Poisson formation from the four axioms;
2. finite-vector \(D_+\) marking isometry and mass--shape split;
3. Gamma-six scalar identities;
4. a formal finite-shell polarity theorem;
5. a separate measure-theoretic formalization of the infinite Borel--Cantelli singularity theorem.

Until those exist and are wired under `HTGeometry/UniversalLawField.lean`, this card remains Stage 2.
