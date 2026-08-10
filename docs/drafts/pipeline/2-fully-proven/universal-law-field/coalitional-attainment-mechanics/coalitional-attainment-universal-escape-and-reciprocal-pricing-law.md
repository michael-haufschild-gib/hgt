# Coalitional attainment, universal escape, and reciprocal pricing law

- **ID:** ULF-CAM-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** An actual positive law carrier exists exactly when zero residual is approximated by
  tight finite coalitions, equivalently by finite coalitions bounded in some proper source price.
  Without an actual carrier, every approximate history has diverging cost in every proper price.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [ATTAINMENT--ESCAPE LAW] [SHARP COUNTERMODEL] [LEAN PENDING] [NOT RH]

## 1. Setup

Let \(V\) be a real or complex Banach space and let

\[
  a:\mathbb N\longrightarrow V,
  \qquad B:=\sup_i\|a_i\|<\infty,
\tag{CAM.1}
\]

be a bounded family of **rule defects**.  A finite coalition is a finitely supported sequence
\(\mu=(\mu_i)_{i\geq0}\) satisfying

\[
  \mu_i\geq0,
  \qquad \sum_i\mu_i=1.
\tag{CAM.2}
\]

Its collective defect and residual are

\[
  A\mu:=\sum_i\mu_i a_i,
  \qquad R(\mu):=\|A\mu\|.
\tag{CAM.3}
\]

An **actual carrier** is a probability vector \(p\in\ell^1(\mathbb N)\), \(p_i\geq0\), with

\[
  Ap:=\sum_i p_i a_i=0.
\tag{CAM.4}
\]

An **approximate history** is a sequence of finite coalitions \((\mu^{(n)})\) with

\[
  R(\mu^{(n)})\longrightarrow0.
\tag{CAM.5}
\]

It is **uniformly tight** when, for every \(\varepsilon>0\), some \(N\) satisfies

\[
  \sup_n\sum_{i>N}\mu_i^{(n)}<\varepsilon.
\tag{CAM.6}
\]

A **proper source price** is a sequence \(W_i\geq0\) with \(W_i\to\infty\).  Its cost is

\[
  \mathcal A_W(\mu)=\sum_i\mu_iW_i.
\tag{CAM.7}
\]

The terminology is interpretive; all theorems below are statements about bounded Banach-valued
sequences and countable probability vectors.

## 2. Coalitional attainment theorem

### Theorem 2.1 -- exact carrier, tight approximation, and proper pricing

The following are equivalent.

1. There exists an actual carrier \(p\).
2. There exists a uniformly tight approximate history of finite coalitions.
3. There exist a proper source price \(W\), a constant \(C<\infty\), and an approximate history
   satisfying

   \[
     \mathcal A_W(\mu^{(n)})\leq C
     \qquad(n\geq0).
   \tag{CAM.8}
   \]

Moreover, every uniformly tight family of probability vectors admits some proper price whose
expectation is uniformly bounded.

### Proof: actual carrier implies tight finite approximation

Let \(p\) be an actual carrier.  Choose prefixes on which

\[
  s_N:=\sum_{i\leq N}p_i>0
\]

and define the normalized truncation

\[
  \mu_i^{(N)}=
  \begin{cases}
  p_i/s_N,&i\leq N,\\
  0,&i>N.
  \end{cases}
\tag{CAM.9}
\]

Since \(s_N\to1\), direct calculation gives

\[
  \|\mu^{(N)}-p\|_1=2(1-s_N)\longrightarrow0.
\tag{CAM.10}
\]

The bounded rule map is Lipschitz:

\[
  \|Aq-Ar\|
  \leq B\|q-r\|_1.
\tag{CAM.11}
\]

Thus \(A\mu^{(N)}\to Ap=0\).  The sequence is uniformly tight because it converges in
\(\ell^1\) to the probability vector \(p\).  This proves \(1\Rightarrow2\).

### Proof: tight approximation attains a carrier

Let \((\mu^{(n)})\) be uniformly tight.  Every coordinate lies in \([0,1]\).  Successive
Bolzano--Weierstrass extraction and diagonalization give a subsequence, still denoted
\((\mu^{(n)})\), and numbers \(p_i\in[0,1]\) such that

\[
  \mu_i^{(n)}\longrightarrow p_i
  \qquad\text{for every }i.
\tag{CAM.12}
\]

Fix \(\varepsilon>0\) and choose \(N\) from tightness.  Passing to the limit in the finite head
gives

\[
  \sum_{i\leq N}p_i
  =\lim_n\sum_{i\leq N}\mu_i^{(n)}
  \geq1-\varepsilon.
\tag{CAM.13}
\]

Because \(\varepsilon\) is arbitrary and finite partial sums are at most one,
\(\sum_i p_i=1\).  The same finite-head/tail split proves \(\ell^1\)-convergence: for the chosen
\(N\),

\[
\begin{aligned}
  \|\mu^{(n)}-p\|_1
  &\leq \sum_{i\leq N}|\mu_i^{(n)}-p_i|
       +\sum_{i>N}\mu_i^{(n)}+\sum_{i>N}p_i\\
  &\leq \sum_{i\leq N}|\mu_i^{(n)}-p_i|+2\varepsilon.
\end{aligned}
\tag{CAM.14}
\]

The finite sum tends to zero.  Equation `(CAM.11)` now gives

\[
  Ap=\lim_nA\mu^{(n)}=0.
\]

Hence \(p\) is an actual carrier.  This proves \(2\Rightarrow1\).

### Proof: proper moment bounds are exactly tightness witnesses

Assume `(CAM.8)`.  Since \(W_i\to\infty\), for every \(M>0\) there is \(N\) such that
\(W_i\geq M\) for \(i>N\).  Therefore

\[
  M\sum_{i>N}\mu_i^{(n)}
  \leq\sum_{i>N}\mu_i^{(n)}W_i
  \leq C.
\tag{CAM.15}
\]

Choosing \(M>C/\varepsilon\) proves uniform tightness.  Hence \(3\Rightarrow2\).

Conversely, let a family \(\mathcal M\) be uniformly tight.  Choose a strictly increasing sequence
\(N_k\to\infty\) such that

\[
  \sup_{\mu\in\mathcal M}\sum_{i>N_k}\mu_i\leq2^{-k}
  \qquad(k\geq1).
\tag{CAM.16}
\]

Define

\[
  W_i:=\#\{k\geq1:N_k<i\}.
\tag{CAM.17}
\]

The count is finite for every \(i\), and \(W_i\to\infty\).  Using the layer-cake identity for this
integer-valued price,

\[
\begin{aligned}
  \sum_i\mu_iW_i
  &=\sum_{k\geq1}\sum_{i>N_k}\mu_i\\
  &\leq\sum_{k\geq1}2^{-k}=1
  \qquad(\mu\in\mathcal M).
\end{aligned}
\tag{CAM.18}
\]

Thus tightness constructs a proper source price with uniformly bounded cost.  Applied to the tight
approximate history from item 2, this proves \(2\Rightarrow3\) and closes the equivalence.
\(\square\)

## 3. Universal escape theorem

### Theorem 3.1 -- every proper resource diverges in the mirage phase

Assume approximate histories exist but no actual carrier exists.  Let \(W\) be any proper source
price and let \((\mu^{(n)})\) be any approximate history.  Then

\[
  \boxed{\mathcal A_W(\mu^{(n)})\longrightarrow\infty.}
\tag{CAM.19}
\]

### Proof

If the nonnegative costs did not tend to infinity, some constant \(C\) and subsequence would satisfy

\[
  \mathcal A_W(\mu^{(n_j)})\leq C.
\]

The residuals along that subsequence still tend to zero.  Theorem 2.1 would then produce an actual
carrier, contrary to hypothesis.  \(\square\)

The quantifier order is essential:

\[
  \boxed{
  \text{no actual carrier}
  \Longrightarrow
  \forall W\text{ proper}\ \forall\text{ approximate histories}\quad
  \mathcal A_W\to\infty.}
\tag{CAM.20}
\]

This is not divergence in one selected norm.  Every proper source gauge sees open lifted history.

## 4. Reciprocal separator pricing

### Theorem 4.1 -- residual--resource uncertainty law

Let \(\varphi\in V^*\) and suppose

\[
  s_i:=\varphi(a_i)>0,
  \qquad s_iW_i\geq\kappa>0
\tag{CAM.21}
\]

for every \(i\).  Then every finite coalition satisfies

\[
  \boxed{
  R(\mu)\,\mathcal A_W(\mu)
  \geq\frac{\kappa}{\|\varphi\|}.}
\tag{CAM.22}
\]

### Proof

Cauchy--Schwarz applied to
\(\sqrt{\mu_i s_i}\) and \(\sqrt{\mu_iW_i}\) gives

\[
  \left(\sum_i\mu_i s_i\right)
  \left(\sum_i\mu_iW_i\right)
  \geq
  \left(\sum_i\mu_i\sqrt{s_iW_i}\right)^2
  \geq\kappa.
\tag{CAM.23}
\]

On the other hand,

\[
  \sum_i\mu_i s_i
  =\varphi(A\mu)
  \leq\|\varphi\|\,R(\mu).
\tag{CAM.24}
\]

Combine `(CAM.23)` and `(CAM.24)`.  The assumptions force \(\varphi\ne0\), so division by its norm
is legitimate.  \(\square\)

This law supplies a quantitative mechanism whenever the source price is reciprocal to a strict but
vanishing separator.  A uniform separator margin forbids approximation; a vanishing separator
permits approximation only by paying reciprocal history.

## 5. Sharp escape countermodel

Take \(V=\mathbb R\) and

\[
  a_i=\frac1{i+1},
  \qquad \mu^{(n)}=\delta_n.
\tag{CAM.25}
\]

Then \(R(\mu^{(n)})=1/(n+1)\to0\).  No actual carrier exists: if \(p\) is any probability vector,
some \(p_j>0\), and hence

\[
  \sum_i\frac{p_i}{i+1}
  \geq\frac{p_j}{j+1}>0.
\tag{CAM.26}
\]

The history is not tight.  For every proper \(W\), its cost is \(W_n\to\infty\), exactly as
Theorem 3.1 predicts.  With \(\varphi=\operatorname{id}_{\mathbb R}\),
\(W_i=i+1\), and \(\kappa=1\), equality holds:

\[
  R(\delta_n)\,\mathcal A_W(\delta_n)=1.
\tag{CAM.27}
\]

Thus the reciprocal lower bound and universal escape conclusion are sharp.

## 6. Three law phases and mechanism

The combined theorem refines the existing exact/mirage/separated trichotomy.

| Phase | Finite residuals | Positive carrier | Source-history signature |
|---|---:|---:|---|
| separated | bounded away from zero | none | no approximate history |
| attained | tend to zero | exists | some proper price remains bounded |
| escaping mirage | tend to zero | none | every proper price diverges |

The new information is not another quotient class.  It is the exact operational distinction
between the last two rows.

The mechanism can be stated as five laws.

1. **Formation law:** only positive normalized coalitions count as candidate carriers.
2. **Residual law:** law compatibility is collective cancellation, not individual rule validity.
3. **Properness law:** bounded source-resource sublevels are precompact at the level of coalition
   mass.
4. **Attainment law:** residual decay plus properness creates an actual carrier.
5. **Escape law:** without a carrier, every proper resource becomes infinite; reciprocal prices
   quantify the divergence.

This is a Frankenstein synthesis of convex alternatives, discrete Prokhorov compactness,
concentration compactness, Lyapunov/proper-moment coercion, and autocatalytic positive kernels.  Its
claim is the coupled law mechanism, not novelty of the ingredients.

## 7. Corpus compression and limits

### 7.1 Exact compression

- **Kernel--cokernel--closure mechanics:** Theorem 3.1 supplies the sequence/rate/cost information
  explicitly absent from the closure-only phase, whenever witnesses admit positive normalization.
- **Genesis--termination mechanics:** the required “compactness/effectivity theorem” is now exact:
  proper source cost turns finitary approximations into a cofinal carrier.
- **Autopoietic law mechanics:** on a finite repair set tightness is automatic, explaining why the
  spectral threshold creates an actual positive carrier rather than a mirage.
- **Adaptive mimic/open history:** exhaustive finite mimics are an escape phenomenon when their
  constitutive support cost is proper; CAM explains why no bounded subsequence can close the lift.
- **Positive-overlap defect calculus:** any future infinite positive defect measure must prove
  precisely the tightness/uniform-integrability premise isolated here.

### 7.2 What is not compressed

CAM does not produce:

1. the rule defects \(a_i\) from the rational-adelic source;
2. an all-prime phase-coherent residual;
3. the adaptive separator/orientation used by a spectral route;
4. a Stokes contact or physical positive carrier;
5. RH or any route endpoint.

It is a law-production mechanism once a source supplies rules and a price, not a claim that every
route has already been realized in one chart.

## 8. Hostile boundaries

1. **Bounded rules are load-bearing.**  Tight coefficient mass need not control unbounded
   Banach-valued barycentres.  A later extension requires uniform integrability or price domination.
2. **Countable carrier labels are load-bearing for the explicit proper-price construction.**
   General Polish carrier spaces require a genuine coercive function theorem.
3. **Positivity is load-bearing.**  Signed coalitions can cancel through unbounded total variation
   while their net mass looks tight.
4. **Properness is doctrine-relative.**  A bounded or noncoercive cost can hide escape.
5. **Actual carrier means countably additive \(\ell^1\) carrier.**  Finitely additive boundary laws
   live in a different completion and do not contradict the theorem.
6. **A carrier need not be unique, ergodic, or source-canonical.**  Attainment proves existence, not
   selection.
7. **Reciprocal pricing is additional structure.**  The qualitative universal escape theorem does
   not construct \(W\); Theorem 2.1 only proves that some proper bounded price exists in the attained
   phase.

## 9. Literature boundary

Prokhorov compactness and concentration compactness are classical parents.  Pouchol--Trelat--Zhang
separate membership from closure membership for nonclosed image cones and give constructive Farkas
conditions ([arXiv:2603.11859](https://arxiv.org/abs/2603.11859)).
Bowler--Hochstaettler--Kaspar show that different infinite oriented-matroid axiom lifts do not
collapse to one cryptomorphic theory ([arXiv:2603.15843](https://arxiv.org/abs/2603.15843)).  These
collisions support, rather than remove, the need to retain source admission and tightness.

No priority claim is made for diagonal compactness, Markov, or Cauchy--Schwarz.  Field-level residue
is the exact equivalence and universal quantifier in `(CAM.20)`, interpreted as formation versus
escape of positive laws.

## 10. Formalization gate

This theorem is dependency-closed on paper.  Required Lean certification must include at least:

1. proper-price tail coercion;
2. residual--resource uncertainty and its equality model;
3. the scalar escape countermodel;
4. a closed finite-support or countable-attainment capstone sufficient to certify the headline
   mechanism;
5. no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations;
6. direct foreground elaboration, source axiom audit, umbrella wiring, and one final module build.

Until that gate passes, project policy does not count this theorem as truly proven.

## Log

- 2026-08-10 -- conjecture frozen after internal closure-trichotomy collision.
- 2026-08-10 -- Conjectures A--C proved; sharp scalar escape/equality model closed; promoted to
  Stage 2 pending Lean certification.
