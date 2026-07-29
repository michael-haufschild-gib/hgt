# Prime-sieve Wold--Gamma/BV relative character and atomic cofinal limit

- **ID:** `prime-sieve-wold-gamma-bv-relative-character`
- **Stage:** 2-fully-proven
- **Type:** SOURCE-COFINAL OPERATOR/CONORMAL THEOREM
- **Scientific status:** `[PAPER PROOF COMPLETE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:**
  - `../1-in-progress/multiplicative-wold-gamma-anomaly-purity-rh.md`;
  - `not_new_scientific_knowledge/bv-prime-window-polar-coefficient-decimation-law.md`;
  - `../1-in-progress/source-effective-polar-kummer-conormal-purity.md`;
  - `../1-in-progress/source-curved-prime-torus-conormal-temperedness.md`.
- **Statement:** Independent one-prime Wold defects do not form a cofinal character.  Their
  commuting prime-sieve intersection does.  Its regular polarized determinant has absolutely
  summable prime-enlargement increments and converges to the one-dimensional vacuum determinant;
  its singular first-trace density is exactly the BV principal-conormal coefficient, has total
  cofinal variation one, and tends to zero.  The principal conormal therefore survives only in the
  source-normal blow-up of this convergent relative character.

## 1. Commuting arithmetic sieve

Let
\[
 H=\ell^2(\mathbb N_{>0}),\qquad
 Qe_n=n^{-1}e_n,\qquad
 S_pe_n=e_{pn},\qquad
 E_p=I-S_pS_p^*.
\]
For a finite set \(P\) of rational primes put
\[
 M_P=\prod_{p\in P}p,\qquad
 E_P=\prod_{p\in P}E_p,\qquad
 Q_P=E_PQ.                                                     \tag{1}
\]
The projections \(E_p\) commute, and \(E_P\) is the coordinate projection onto
\[
 \{n\geq1:(n,M_P)=1\}.                                        \tag{2}
\]
If \(p\notin P\), there is an orthogonal \(Q_P\)-reducing decomposition
\[
 E_PH=E_{P\cup\{p\}}H\ \widehat\oplus\ S_pE_PH,                \tag{3}
\]
and \(S_p:E_PH\to S_pE_PH\) identifies the second restriction of \(Q_P\) with
\(p^{-1}Q_P\).

Indeed, every integer coprime to \(M_P\) is uniquely either prime to \(p\) or \(p\) times an
integer coprime to \(M_P\).  Also \(QS_p=p^{-1}S_pQ\).  This proves `(1)`--`(3)` without analytic
continuation or divisor data.

## 2. Regular determinant layer

For \(|t|<1\), define
\[
 \Phi_P(t)
 =
 \frac{\det_2(I-tQ_P)}{\det_2(I+tQ_P)}.                         \tag{4}
\]
Since \(Q_P\) is Hilbert--Schmidt, `(4)` is defined and nonzero on the open unit disk.  Orthogonal
determinant multiplicativity in `(3)` gives the exact prime-enlargement law
\[
 \boxed{\quad
 \Phi_{P\cup\{p\}}(t)=\frac{\Phi_P(t)}{\Phi_P(t/p)}.
 \quad}                                                        \tag{5}
\]
This is not the independent one-prime defect
\(\Phi_\varnothing(t)/\Phi_\varnothing(t/p)\) repeated at every prime.  The numerator in `(5)`
changes with the already-sieved packet.

The logarithmic expansion is
\[
 \log\Phi_P(t)
 =
 -2\sum_{j\geq1}
 \frac{t^{2j+1}}{2j+1}
 \zeta(2j+1)
 \prod_{p\in P}(1-p^{-(2j+1)}).                                \tag{6}
\]
For every \(0<r<1\), there is \(C_r<\infty\), independent of \(P\) and \(p\notin P\), such that
\[
 \sup_{|t|\leq r}
 \left|
 \log\Phi_{P\cup\{p\}}(t)-\log\Phi_P(t)
 \right|
 \leq \frac{C_r}{p^3}.                                        \tag{7}
\]
To prove `(7)`, use `(5)` and `(6)` at \(t/p\), together with
\[
 \operatorname{Tr}(Q_P^k)
 \leq\zeta(k)\leq\zeta(3)
 \qquad(k\geq3).
\]
The remaining odd power series is bounded by a constant times \(p^{-3}\).  Hence the increments
in `(7)` are absolutely summable over all primes.

As \(P\) increases through the finite prime sets,
\[
 Q_P\longrightarrow P_{\{1\}}
 \quad\text{in Hilbert--Schmidt norm},                          \tag{8}
\]
because
\[
 \|Q_P-P_{\{1\}}\|_2^2
 =
 \sum_{\substack{n>1\\(n,M_P)=1}}\frac1{n^2}
 \longrightarrow0
\]
by dominated convergence.  Therefore `(4)` converges locally uniformly on \(|t|<1\) to
\[
 \Phi_{\rm vac}(t)
 =
 \frac{\det_2(I-tP_{\{1\}})}{\det_2(I+tP_{\{1\}})}
 =
 e^{2t}\frac{1-t}{1+t}.                                       \tag{9}
\]
Equivalently, the Euler factors in `(6)` cancel \(\zeta(2j+1)\) in the cofinal limit, leaving
the single vacuum eigenvalue.

## 3. Singular first-trace layer

For a cutoff \(N\), put
\[
 T_P(N)
 =
 \operatorname{Tr}_{n\leq N}(Q_P)
 =
 \sum_{\substack{n\leq N\\(n,M_P)=1}}\frac1n.                  \tag{10}
\]
Finite inclusion--exclusion gives
\[
 T_P(N)
 =
 \sum_{d\mid M_P}\frac{\mu(d)}d H_{\lfloor N/d\rfloor}.
\]
Consequently
\[
 T_P(N)=a_P\log N+\kappa_P+o(1),                               \tag{11}
\]
where
\[
 a_P=\prod_{p\in P}(1-p^{-1}),\qquad
 \kappa_P
 =
 a_P\left(
 \gamma+\sum_{p\in P}\frac{\log p}{p-1}
 \right).                                                     \tag{12}
\]
The singular trace density has the exact transition
\[
 a_{P\cup\{p\}}=a_P(1-p^{-1}),\qquad
 a_P-a_{P\cup\{p\}}=\frac{a_P}{p}.                            \tag{13}
\]

For any enumeration \(p_1,p_2,\ldots\) of all primes, let
\(P_n=\{p_1,\ldots,p_n\}\).  Euler's divergence of
\(\sum_p1/p\) gives \(a_{P_n}\to0\), and `(13)` telescopes:
\[
 \boxed{\quad
 \sum_{n\geq1}\frac{a_{P_{n-1}}}{p_n}=1.
 \quad}                                                        \tag{14}
\]
Thus the singular density has finite total cofinal variation, even though the independent
one-prime densities \(1-p^{-1}\) are not summable.

The finite part \(\kappa_P\) is retained in `(11)` but is not used to manufacture convergence.
The regular/singular relative character is the pair consisting of the \(\det_2\) layer and the
coefficient \(a_P\) of the trace term removed by \(\det_2\).

## 4. Exact BV principal-conormal reading

Let \(W\) be a compactly supported BV window.  For every scale \(a>0\), put
\[
 W_a(x)=W(ax)
\]
and let \(p_a\) be its canonical prime--polar coefficient sequence.  For every integer \(q\geq2\),
the proof of the BV decimation law gives, without requiring \(\sqrt q\) to be an integer,
\[
 D_qp_a=p_{aq},\qquad
 (D_qb)(N)=b(qN).                                            \tag{15}
\]
Indeed, the prime term is reindexed directly, while
\(M_{W_a}(3/2)=a^{1/2}M_W(3/2)\).

Let \(J\) denote the pole-cancelled BV/co-Poisson principal-normal class before choosing a zero.
The source laws are
\[
 J(D_qp_a)=q^{s-1}J(p_a),\qquad
 J(S_qb)=q^{-s}J(b).                                         \tag{16}
\]
With \(E_q=I-S_qD_q\), equations `(15)`--`(16)` cancel the spectral variable:
\[
 J(E_qp_a)=(1-q^{-1})J(p_a).                               \tag{17}
\]
For distinct primes the decimation, inflation, and off-multiple projections commute.  Induction
therefore gives the finite-prime identity
\[
 \boxed{\quad
 J(E_Pp_a)=a_PJ(p_a).
 \quad}                                                       \tag{18}
\]
At every uncensored divisor fibre, `(18)` is the corresponding identity for the complete
principal Laurent residue, including its multiplicity scalar.  Thus the coefficient \(a_P\) in
the singular trace asymptotic `(11)` is literally the coefficient of the same sieved BV
principal conormal.

## 5. Cofinal relative character and normal-cone fracture

Equations `(5)`, `(13)`, and `(18)` define one finite-packet relative source character:
\[
 \mathfrak C_P
 =
 \bigl(Q_P,\Phi_P,a_PJ(p_a)\bigr).                            \tag{19}
\]
Its regular increments have total variation bounded by
\(\sum_pC_rp^{-3}\); its singular scalar increments have total variation one.  Its endpoint is
\[
 \mathfrak C_\infty
 =
 \bigl(P_{\{1\}},\Phi_{\rm vac},0\bigr)                       \tag{20}
\]
in the coarse Hilbert/determinant/conormal topology.

The zero in `(20)` does not mean that the distinguished conormal was absent.  For every finite
\(P\),
\[
 a_P^{-1}J(E_Pp_a)=J(p_a).                                  \tag{21}
\]
Therefore the source-normal blow-up of `(19)` along \(a_P=0\) retains one constant nonzero
principal-conormal direction while the coarse realization loses it.  This is an exact instance
of the required third-completion fracture:

```text
coarse all-prime limit:
  regular vacuum survives, principal conormal vanishes;

source-normal blow-up:
  regular vacuum and calibrated principal conormal both survive.
```

The blow-up is source-defined: \(E_P\), \(a_P\), and \(J(E_Pp_a)\) exist before a zero or a divisor
fibre is selected.

## 6. Naive differential-character no-go

The one-prime pair
\[
 \left(
 \frac{\Phi_\varnothing(t)}{\Phi_\varnothing(t/p)},
 1-p^{-1}
 \right)
\]
tends to \((\Phi_\varnothing(t),1)\), not to the identity.  Taking its direct product over primes
therefore diverges in both regular and singular channels.  Calling those independent scalar
reporters one differential character does not construct an all-prime source object.

The nested sieve `(19)` is the positive replacement.  Previously adjoined primes change the next
defect: the regular increment becomes \(O(p^{-3})\), while the singular increment becomes
\(a_P/p\) and telescopes.  Higher-prime interaction is therefore load-bearing, not an optional
repackaging of the one-prime Wold law.

There is still no RH conclusion.  Blowing up by \(a_P^{-1}\) is singular.  Differential
cohomology, determinant curvature, and the integral characteristic class do not by themselves
bound the nonunitary flat holonomy of the normalized conormal line.  A Hermitian comparison must
be constructed from the source and proved continuous in the blow-up topology.

## 7. Exact next theorem: contractive polar transgression

Fix \(0<r<1\) and define the source transition size
\[
 \delta_r(P,p)
 =
 \frac{a_P}{p}
 +
 \sup_{|t|\leq r}|\log\Phi_P(t/p)|.                       \tag{22}
\]
Equations `(7)` and `(14)` prove, for every prime exhaustion,
\[
 \sum_n\delta_r(P_{n-1},p_n)<\infty.                     \tag{23}
\]

The RH-bearing comparison is now one quantitative statement, rather than the assertion that a
determinant character exists:

> **[CONJECTURE -- SOURCE-NORMAL CONTRACTIVE POLAR TRANSGRESSION.]**
> The source-calibrated normal blow-up of `(19)` has finite-packet Kummer--Arakelov regulators
> \(h_P\) whose prime transport is the centered principal-conormal transport, and there are
> source constants \(C,r\), independent of \(P\) and \(p\notin P\), such that
> \[
> \|h_{P\cup\{p\}}-h_P\|_{L^1+L^2}
> \leq C\,\delta_r(P,p).                                    \tag{24}
> \]
> The regulator and `(24)` are constructed before divisor specialization and preserve every
> normalized principal-conormal multiplicity jet.

By `(23)`, equation `(24)` makes \((h_P)\) mixed-Cauchy.  At a divisor fibre \(\rho\), exact
prime transport gives
\[
 \langle h_\rho,f_p\rangle
 =
 (\tfrac12-\operatorname{Re}\rho)\log p.
\]
The mixed Kummer coherent-power selector then forces
\(\operatorname{Re}\rho=\tfrac12\).  Hence `(24)` plus the source comparison proves RH.

This consequence also makes `(24)` hostilely testable.  For a coherent off-critical exponent
\(c\neq0\), the unique component-constant finite Kummer regulators have harmonic-size transition
defects and are not mixed-Cauchy, whereas the right side of `(24)` is summable.  Thus an off-line
generalized-prime model can satisfy `(24)` only if it carries the literal nested ordinary-prime
source character and a false contractive comparison; positivity, functional equation, entire
completion, and hypertranscendence alone do not approach it.

## Novelty and literature boundary

Parent ingredients are not claimed as new:

- Wold decompositions for commuting isometries;
- Hilbert--Schmidt regularized determinants and their product laws;
- Eratosthenes inclusion--exclusion and Euler's divergence of reciprocal primes;
- BV coefficient decimation and the co-Poisson principal-normal class.

Targeted searches found tuple-Wold theory, regularized determinant product formulas, Bost--Connes
finite-prime semigroup systems, and classical sieve asymptotics.  They did not locate the exact
conjunction `(5)`, `(14)`, `(18)`, and `(21)`: a coprime Wold sieve whose polarized Gamma
determinant and BV principal conormal form one finite-variation cofinal relative character with an
atomic coarse limit and a nonzero source-normal conormal blow-up.  This is a provisional
noncollision report, not a priority claim.

Closest external parents include:

- Satyabrata Majee and Amit Maji, *Wold decomposition for isometries with equal range*,
  https://arxiv.org/abs/2309.04445;
- Thomas Britz, Alan Carey, Fritz Gesztesy, Roger Nichols, Fedor Sukochev, and Dmitriy Zanin,
  *The product formula for regularized Fredholm determinants*,
  https://arxiv.org/abs/2007.12834;
- Nathan Brownlowe, Nadia Larsen, Ian Putnam, and Iain Raeburn,
  *Subquotients of Hecke \(C^*\)-algebras*,
  https://arxiv.org/abs/math/0309429.

## Gates

- [x] finite commuting prime-sieve operator constructed
- [x] exact nested polarized-determinant transition proved
- [x] absolute cofinal convergence to the vacuum determinant proved
- [x] singular first-trace density and total variation proved
- [x] arbitrary-integer BV scale-decimation extension proved
- [x] multi-prime BV principal-conormal coefficient proved
- [x] coarse-limit/normal-blow-up fracture classified
- [x] naive independent-defect differential character killed
- [x] exact contractive transgression inequality isolated
- [ ] independent specialist novelty audit
- [ ] Lean formalization
- [ ] source-normal contractive polar transgression `(24)`
- [ ] RH

## Log

- 2026-07-29 — Replaced the divergent product of independent one-prime Wold defects by the
  commuting coprime sieve.  Proved absolute convergence of its regular determinant increments,
  total-variation convergence of its singular trace/BV coefficient, and the atomic coarse
  limit with nonzero normalized conormal blow-up.  Isolated `(24)` as the exact remaining
  source-to-Kummer estimate.
- 2026-07-29 — Normalization-amplification audit:
  `prime-valuation-conditioning-normalization-amplification-no-go.md` proves that the
  unnormalized loss \(a_P/p\) becomes the nonsummable conditional-state distance \(1/p\) after
  division by \(a_P\), and every finite conditioned state is at total-variation distance one
  from the weak atomic endpoint.  Equation `(24)` remains an RH-bearing cancellation statement,
  but it no longer follows from or is made plausible by `(23)`; deriving normalized strong
  convergence from the telescoping unnormalized character is retired.
