# Beurling cross-system blindness of multiplicative regularization

- **ID:** ULF-INV-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FIRST NECESSITY AXIOM OF THE INVERSE THEORY
- **Source:** inversion of the corpus blindness theorem (`rh-producer-map-corpus.md` §17,
  `HTGeometry/MultiplicativeRegularizationBlind.lean`) from an internal limit statement into a
  cross-system statement about what the method can ever see
- **Statement:** Over the class of Mertens-normal Beurling systems, every convergent
  multiplicatively regularized limit of the prime log-jet Grams is a function of the normalizer
  alone — constant across systems — and therefore determines neither the zero set nor the system.
  Any finite pairing that detects zeros must consume input beyond Mertens-normal moment data.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [NECESSITY AXIOM N1] [CORPUS PARENT CITED]
  [NOT RH] [NO LEAN]

## 1. Setting

A **Beurling system** \(\mathcal P\) is a sequence of generalized primes
\(1<p_1\le p_2\le\cdots\to\infty\); its generalized integers are the multiplicative semigroup they
generate (with multiplicity), \(\Lambda_{\mathcal P}\) its von Mangoldt function
(\(\Lambda_{\mathcal P}(n)=\log p\) on generalized prime powers \(n=p^k\), extended by \(0\)),
and \(\zeta_{\mathcal P}(s)=\prod_i(1-p_i^{-s})^{-1}\) where convergent.

Call \(\mathcal P\) **Mertens-normal** if

\[
S_{\mathcal P}(N):=\sum_{n\le N}\frac{\Lambda_{\mathcal P}(n)}{n}
=\log N+C_{\mathcal P}+o(1)
\qquad(N\to\infty).
\tag{INV.1}
\]

The rational primes are Mertens-normal (classical Mertens). The **prime log-jet Gram** of
\(\mathcal P\) at aperture \(N\) is the corpus's object

\[
H^{\mathcal P}_{k}(N)=\sum_{n\le N}\frac{\Lambda_{\mathcal P}(n)}{n}\,(\log n)^{k},
\qquad
H^{\mathcal P}(N)_{ij}=H^{\mathcal P}_{i+j}(N).
\tag{INV.2}
\]

A **multiplicative regularization** is a family \(c^{(N)}_k\in\mathbb R\) (arbitrary dependence on
\(k\) and the aperture) applied entrywise, \(H_{ij}\mapsto c^{(N)}_{i+j}H_{i+j}(N)\).

## 2. Leading structure

### Lemma 2.1

If \(\mathcal P\) is Mertens-normal then, with \(L=\log N\),

\[
H^{\mathcal P}_k(N)=\frac{L^{k+1}}{k+1}+O_k\bigl(L^{k}\bigr).
\tag{INV.3}
\]

#### Proof

Riemann–Stieltjes partial summation against (INV.1): writing
\(S(x)=\log x+C+\varepsilon(x)\) with \(\varepsilon(x)=o(1)\) and \(\varepsilon\) bounded,

\[
H_k(N)=\int_{1^-}^{N}(\log x)^k\,dS(x)
=\int_1^N\frac{(\log x)^k}{x}\,dx+\int_{1^-}^N(\log x)^k\,d(C+\varepsilon(x)).
\]

The first integral is \(L^{k+1}/(k+1)\). The second is, after integration by parts,
\((\log N)^k\varepsilon(N)-k\int_1^N(\log x)^{k-1}\varepsilon(x)\,dx/x
=o(L^k)+O_k(L^{k})\), using boundedness of \(\varepsilon\). QED.

## 3. Cross-system blindness

### Theorem 3.1 — the limit is a function of the normalizer alone

Let \(\mathcal P\) be Mertens-normal and let \(c^{(N)}\) be any multiplicative regularization such
that \(c^{(N)}_kH^{\mathcal P}_k(N)\) converges as \(N\to\infty\) for each \(k\), with some limit
nonzero. Then \(c^{(N)}_kL^{k+1}\) converges, say to \(\delta_k\), and

\[
\lim_{N\to\infty}c^{(N)}_kH^{\mathcal P}_k(N)=\frac{\delta_k}{k+1}.
\tag{INV.4}
\]

Consequently, for any two Mertens-normal systems \(\mathcal P,\mathcal P'\) and any regularization
under which both converge, the limit matrices are **equal**:

\[
\lim c^{(N)}\!\cdot H^{\mathcal P}(N)=\lim c^{(N)}\!\cdot H^{\mathcal P'}(N).
\tag{INV.5}
\]

#### Proof

By (INV.3), \(H_k(N)=L^{k+1}(1/(k+1)+O(1/L))\). If \(c^{(N)}_kH_k(N)\to\ell_k\) then
\(c^{(N)}_kL^{k+1}=c^{(N)}_kH_k(N)\cdot\bigl(1/(k+1)+O(1/L)\bigr)^{-1}\to(k+1)\ell_k=:\delta_k\),
and conversely \(c^{(N)}_kH_k(N)=c^{(N)}_kL^{k+1}\cdot(1/(k+1)+O(1/L))\to\delta_k/(k+1)\).
Both limits are functions of \((\delta_k)\) alone; (INV.5) follows since the same \(c^{(N)}\) fixes
the same \((\delta_k)\). (This is the cross-system form of the corpus's
`tendsto_mul_regularized`; the aperture calibration \(L=\log N\) is shared because both systems
satisfy (INV.1) with leading coefficient \(1\).) QED.

### Theorem 3.2 — the limit determines neither the zeros nor the system

There exist Mertens-normal Beurling systems \(\mathcal P\ne\mathcal P'\) with
\(\zeta_{\mathcal P}\ne\zeta_{\mathcal P'}\) and different zero sets, on which every convergent
multiplicative regularization takes identical limits. Concretely: let \(\mathcal P\) be the
rational primes and \(\mathcal P'\) the rational primes with the generator \(2\) replaced by any
\(\beta\in(1,\infty)\), \(\beta\ne2\). Then:

1. \(\mathcal P'\) is Mertens-normal.
2. On the common half-plane of convergence,

   \[
   \zeta_{\mathcal P'}(s)=\zeta(s)\,\frac{1-2^{-s}}{1-\beta^{-s}},
   \tag{INV.6}
   \]

   which extends meromorphically wherever \(\zeta\) does; the point \(s_0=2\pi i/\log 2\) is a
   zero of the factor \(1-2^{-s}\) and not a pole of \(1/(1-\beta^{-s})\) for
   \(\log 2/\log\beta\notin\mathbb Q\), while \(\zeta(s_0)\ne0\) (all zeros of \(\zeta\) lie in
   the critical strip or at negative even integers, and \(s_0\) is purely imaginary, nonzero).
   Hence \(s_0\) is a zero of \(\zeta_{\mathcal P'}\) and not of \(\zeta\): the zero sets differ.
3. Every convergent multiplicative regularization has the same limit on \(\mathcal P\) and
   \(\mathcal P'\) (Theorem 3.1).

#### Proof

Item 1: \(\Lambda_{\mathcal P'}=\Lambda-\log2\sum_k\delta_{2^k}+\log\beta\sum_k\delta_{\beta^k}\)
as measures on \((1,\infty)\), so

\[
S_{\mathcal P'}(N)=S_{\mathcal P}(N)
-\log2\!\!\sum_{2^k\le N}\!2^{-k}
+\log\beta\!\!\sum_{\beta^k\le N}\!\beta^{-k},
\]

and both corrections converge as \(N\to\infty\) (geometric series), so (INV.1) holds with a
shifted constant. Item 2: (INV.6) is the Euler-product manipulation on
\(\operatorname{Re}s>1\), and both sides continue; the factor's zeros are
\(s=2\pi ik/\log2\), its poles \(s=2\pi ik/\log\beta\); choosing \(\beta\) with
\(\log2/\log\beta\) irrational makes zeros and poles disjoint away from \(s=0\); \(\zeta\) is
zero-free and pole-free at \(s_0\). Item 3 is Theorem 3.1. QED.

### Corollary 3.3 — necessity axiom N1

Any finite pairing built from the prime log-jet source by entrywise (multiplicative)
regularization is constant on the Mertens-normal class and therefore carries no information about
the zero set of the underlying zeta function. Hence: **any theory whose pairing is finite,
positive, and zero-sensitive must consume structural input beyond Mertens-normal moment data** —
the pairing cannot factor through the multiplicative-regularization functor.

## 4. Hostile scope

- The internal blindness mechanism is the corpus's (`tendsto_mul_regularized`); Lemma 2.1 and the
  cross-system/Beurling formulation, the explicit comparison pair, and Corollary 3.3's necessity
  reading are what this card adds. If a corpus or literature source already states the
  cross-system form, this card demotes to BRIDGE — a search of the corpus docs found the internal
  form only (§17), and Beurling comparison arguments in the literature (Diamond; Zhang;
  Diamond–Montgomery–Vorhauer, who build far deeper oscillation examples than needed here) are
  cited as parents for the technique of varying the system.
- The theorem does not touch subtractive or nonlinear regularizations (closed separately by the
  corpus's §§20–22 within their families), and creates no positivity. Its role is axiomatic: it
  is the first entry of the specification the missing object must satisfy.
- \(\beta\) with \(\log2/\log\beta\) irrational exists trivially (any transcendental \(\beta\),
  or \(\beta=3\): \(\log2/\log3\) irrational since \(2^a=3^b\) has no nontrivial integer
  solutions — with \(\beta=3\) the system has a doubled prime \(3\), which Beurling systems
  permit (multiplicity is allowed); item 2's disjointness at \(s_0\) needs only
  \(2^{-s_0}=1\ne\beta^{-s_0}\), i.e. \(\log\beta/\log2\notin\mathbb Z\) at \(k=1\), true for
  \(\beta=3\).)

## Log

- 2026-08-09 — created as the first executed step of the inverse theory: corpus no-go inverted
  into a cross-system impossibility with explicit comparison pair, and read as necessity axiom N1.
