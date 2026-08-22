# Prime-square Möbius--Fourier complementary-record law

- **ID:** `prime-square-mobius-fourier-complementary-record-law`
- **Stage:** 2-fully-proven
- **Type:** EXACT LOCAL ADDITIVE--MULTIPLICATIVE COMPARISON / INFINITE-SECTOR FRACTURE
- **Scientific status:** `[PAPER-PROVED] [NEW TO CORPUS] [PARENT FINITE FOURIER/CRT]`
  `[BUILDING BLOCK] [NOT RH] [NO COMPUTATION]`
- **Parents:**
  - `../new_scientific_knowledge/projective-prime-weyl-leakage-fock-normal-cone.md`;
  - `poisson-euler-sobolev-natural-cone-bipolarity.md`;
  - `../../1-in-progress/squarefree-fourier-torsion-counterface-completion.md`;
  - `noninvertible-event-complementary-record-boundary.md`;
  - `involution-selects-minimal-event-record.md`.

## 1. The finite clock that contains the actual Möbius atom

Fix a prime \(p\), put \(G_p=\mathbb Z/p^2\mathbb Z\), and define
\[
 m_p(x)=
 \begin{cases}
  1,&p\nmid x,\\
  -1,&p\parallel x,\\
  0,&p^2\mid x.
 \end{cases}                                                   \tag{1}
\]
This is not a fitted Bernoulli model.  It is the literal local factor of the Möbius function.
For every finite prime set \(P\),
\[
 m_P(n)=\prod_{p\in P}m_p(n\bmod p^2)                           \tag{2}
\]
is periodic modulo
\[
 M_P=\prod_{p\in P}p^2,                                        \tag{3}
\]
and, as \(P\) exhausts the primes,
\[
 m_P(n)\longrightarrow\mu(n)                                  \tag{4}
\]
for every fixed positive integer \(n\).

Let \(U_p\) be the unit residues and let
\[
 V_p=pG_p\setminus\{0\}.
\]
In \(\ell^2(G_p)\) with counting inner product, put
\[
 u_p={\mathbf1_{U_p}\over\sqrt{p(p-1)}},
 \qquad
 v_p={\mathbf1_{V_p}\over\sqrt{p-1}},
 \qquad
 w_p=\delta_0.                                                \tag{5}
\]
These vectors are orthonormal.  Let \(E_p=\operatorname{span}\{u_p,v_p\}\).

Use the unitary additive Fourier transform
\[
 (\mathcal F_pf)(a)
 ={1\over p}\sum_{x\bmod p^2}f(x)e^{-2\pi iax/p^2}.            \tag{6}
\]

## 2. Exact additive Fourier compression

> **[THEOREM -- PRIME-SQUARE FOURIER POLARIZATION.]**
> On the vectors `(5)`,
> \[
> \begin{aligned}
> \mathcal F_pu_p
>  &=\sqrt{{p-1\over p}}\,w_p-{1\over\sqrt p}v_p,\\
> \mathcal F_pv_p
>  &=-{1\over\sqrt p}u_p+{p-1\over p}v_p
>    +{\sqrt{p-1}\over p}w_p.                                \tag{7}
> \end{aligned}
> \]
> Consequently the producer--reporter cross-Gram compression is
> \[
> C_p=P_{E_p}\mathcal F_p|_{E_p}
> =
> \begin{pmatrix}
> 0&-p^{-1/2}\\
> -p^{-1/2}&1-p^{-1}
> \end{pmatrix}_{(u_p,v_p)},                                  \tag{8}
> \]
> with eigenvalues
> \[
> 1,\qquad-{1\over p}.                                        \tag{9}
> \]
> The corresponding unit eigenvectors are
> \[
> c_p={u_p-\sqrt p\,v_p\over\sqrt{p+1}},
> \qquad
> t_p={\sqrt p\,u_p+v_p\over\sqrt{p+1}}.                      \tag{10}
> \]
> Thus
> \[
> \mathcal F_pc_p=c_p,\qquad
> P_{E_p}\mathcal F_pt_p=-p^{-1}t_p,\qquad
> \|(1-P_{E_p})\mathcal F_pt_p\|^2=1-p^{-2}.                 \tag{11}
> \]

### Proof

The sum of the additive character over the unit residues modulo \(p^2\) is
\[
 c_{p^2}(a)=
 \begin{cases}
 p(p-1),&p^2\mid a,\\
 -p,&p\parallel a,\\
 0,&p\nmid a.
 \end{cases}                                                   \tag{12}
\]
The sum over the nonzero multiples of \(p\) is
\[
 \sum_{y=1}^{p-1}e^{-2\pi iay/p}
 =
 \begin{cases}
 p-1,&p\mid a,\\
 -1,&p\nmid a.
 \end{cases}                                                   \tag{13}
\]
Substitution into `(6)` and collection in the orthonormal strata `(5)` gives `(7)`.
Projection to \(E_p\) gives `(8)`.  Its characteristic polynomial has roots
\[
 {p-1\pm(p+1)\over2p}=1,-p^{-1},
\]
with eigenvectors `(10)`.  Since \(\mathcal F_p\) is unitary, equality of the compressed norm on
the \(1\)-eigenline forces \(\mathcal F_pc_p=c_p\); Pythagoras gives the leakage in `(11)`.
\(\square\)

Equation `(9)` is the actual additive-Fourier realization of the projective transverse overlap
\(-1/p\).  Equation `(11)` is its Gram determinant \(1-p^{-2}\).  The projective
\(\mathbb P^1(\mathbb F_p)\) plane pair is therefore a minimal principal-angle model of the
literal valuation/Fourier plane pair inside \(\ell^2(\mathbb Z/p^2\mathbb Z)\).

## 3. Möbius parity is the complementary record

The normalized positive squarefree and signed Möbius local vectors are
\[
 q_p={|m_p|\over\|m_p\|}
 ={ \sqrt p\,u_p+v_p\over\sqrt{p+1}}
 =t_p,                                                        \tag{14}
\]
\[
 \widetilde m_p={m_p\over\|m_p\|}
 ={ \sqrt p\,u_p-v_p\over\sqrt{p+1}}.                         \tag{15}
\]
Let \(S_p\) be the involution on \(E_p\) which fixes \(u_p\) and negates \(v_p\).  Then
\[
 S_pq_p=\widetilde m_p.                                      \tag{16}
\]
In the Fourier principal basis \((c_p,t_p)\),
\[
 \boxed{
 S_p=
 \begin{pmatrix}
 -\tau_p&\sigma_p\\
 \sigma_p&\tau_p
 \end{pmatrix},
 \qquad
 \sigma_p={2\sqrt p\over p+1},
 \qquad
 \tau_p={p-1\over p+1}.
 }                                                            \tag{17}
\]
In particular,
\[
 \widetilde m_p=\sigma_pc_p+\tau_pt_p,\qquad
 \sigma_p^2+\tau_p^2=1.                                      \tag{18}
\]

The two amplitudes were previously found in different parts of the corpus:
\[
 \sigma_p={2\sqrt p\over p+1}
 \quad\text{is the critical fixed-source \(p\)-adic spherical moment},          \tag{19}
\]
\[
 \tau_p={p-1\over p+1}
 \quad\text{is the projective Möbius/Pluecker overlap}.                         \tag{20}
\]
Equations `(17)`--`(18)` prove that they are complementary entries of one source involution.
The additive-Fourier common mode is the continuation channel; the transverse mode is the
Möbius record channel.  The identity
\[
 \operatorname{sech}^2\!\left({\log p\over2}\right)
 +
 \operatorname{tanh}^2\!\left({\log p\over2}\right)=1          \tag{21}
\]
is therefore a local information-conservation law, not a coincidental hyperbolic identity.

### Proof

Equations `(14)`--`(16)` follow by counting
\[
 |U_p|=p(p-1),\qquad |V_p|=p-1.
\]
Taking the four matrix coefficients of \(S_p\) in the orthonormal basis `(10)` gives `(17)`.
Equation `(18)` is the second column of that matrix, and \(S_p^2=1\) gives the Pythagorean
identity. \(\square\)

## 4. The exact local Fourier spectrum

With probability-normalized Fourier coefficients
\[
 \widehat m_p(a)={1\over p^2}
 \sum_{x\bmod p^2}m_p(x)e^{-2\pi iax/p^2},                    \tag{22}
\]
one has
\[
 \widehat m_p(a)=
 \begin{cases}
 (p-1)^2/p^2,&a=0,\\
 -(2p-1)/p^2,&p\parallel a,\\
 1/p^2,&p\nmid a.
 \end{cases}                                                   \tag{23}
\]
Indeed
\[
 m_p=1-2\mathbf1_{p\mid x}+\delta_0,                          \tag{24}
\]
and `(23)` follows by summing each term.

Plancherel gives
\[
 \sum_{a\bmod p^2}|\widehat m_p(a)|^2
 ={1\over p^2}\sum_{x\bmod p^2}|m_p(x)|^2
 =1-p^{-2}.                                                   \tag{25}
\]
The normalized zero-frequency survival probability factors exactly as
\[
 \boxed{
 {|\widehat m_p(0)|^2\over1-p^{-2}}
 =
 (1-p^{-2})
 \left({p-1\over p+1}\right)^2.
 }                                                            \tag{26}
\]
Thus the local additive zero mode is the product of:

```text
safe squarefree Fourier mass       1-p^(-2);
singular Möbius projective record  ((p-1)/(p+1))^2.
```

The first product over primes converges to \(1/\zeta(2)\); the second vanishes at the divergent
first-trace scale.  The regular determinant and singular boundary record are two factors of one
literal local Fourier coefficient.

## 5. Exact natural-cone identification

For real \(c\), deform only the valuation-one amplitude:
\[
 m_{p,c}(x)=
 \begin{cases}
 1,&p\nmid x,\\
 -p^c,&p\parallel x,\\
 0,&p^2\mid x.
 \end{cases}                                                   \tag{27}
\]
Then
\[
 {m_{p,c}\over\|m_{p,c}\|}
 ={ \sqrt p\,u_p-p^c v_p\over\sqrt{p+p^{2c}}}.                 \tag{28}
\]
For real \(c,d\),
\[
 \boxed{
 \left\langle
 {m_{p,c}\over\|m_{p,c}\|},
 {m_{p,d}\over\|m_{p,d}\|}
 \right\rangle
 =
 {p+p^{c+d}\over
  \sqrt{(p+p^{2c})(p+p^{2d})}}.
 }                                                            \tag{29}
\]
This is exactly the projective-prime Hellinger Gram coefficient with
\[
 z=c\log p,\qquad y=d\log p,                                  \tag{30}
\]
up to the source-fixed Möbius sign on the marked coordinate.  Hence the projective natural cone
is not merely calibrated to the valuation law: it is the normalized two-stratum compression of
the actual prime-square Möbius clock.

## 6. CRT tensorization and the infinite-sector fracture

Under the Chinese remainder isomorphism
\[
 \mathbb Z/M_P\mathbb Z
 \cong\prod_{p\in P}\mathbb Z/p^2\mathbb Z,                    \tag{31}
\]
both `(2)` and its additive Fourier transform are tensor products of their local factors.
Consequently
\[
 {1\over M_P}\sum_{n\bmod M_P}|m_P(n)|^2
 =\prod_{p\in P}(1-p^{-2}).                                   \tag{32}
\]

Pointwise convergence `(4)` does **not** extend to the natural density Hilbert completion.
For every fixed finite \(P\), Davenport's uniform exponential-sum theorem for Möbius gives
\[
 \lim_{X\to\infty}{1\over X}
 \sum_{n\le X}\mu(n)\overline{m_P(n)}=0,                       \tag{33}
\]
because \(m_P\) is a finite Fourier series of rational additive characters.  The squarefree
density and periodic mean give
\[
 \lim_{X\to\infty}{1\over X}\sum_{n\le X}|\mu(n)|^2
 ={1\over\zeta(2)},                                            \tag{34}
\]
\[
 \lim_{X\to\infty}{1\over X}\sum_{n\le X}|m_P(n)|^2
 =\prod_{p\in P}(1-p^{-2}).                                   \tag{35}
\]
Therefore
\[
 \boxed{
 \lim_{X\to\infty}{1\over X}
 \sum_{n\le X}|\mu(n)-m_P(n)|^2
 =
 {1\over\zeta(2)}
 +\prod_{p\in P}(1-p^{-2}).
 }                                                            \tag{36}
\]
As \(P\) exhausts the primes, the right side tends to
\[
 {2\over\zeta(2)}.                                             \tag{37}
\]

Thus the finite local clocks converge to Möbius at every fixed integer while becoming
asymptotically orthogonal to Möbius in density.  The finite and infinite limits do not merely
fail to commute by a small tail: the entire limiting Hilbert sector changes.

The same fracture is visible on the Fourier side.  The proportion of local Plancherel mass in
the zero frequency is
\[
 r_p
 ={(p-1)^3\over p^2(p+1)}
 =(1-p^{-2})\tau_p^2
 =1-{4\over p}+O(p^{-2}),                                     \tag{38}
\]
so \(\prod_pr_p=0\).  Fourier mass escapes every fixed finite-excitation cylinder even though
the total mass converges to \(1/\zeta(2)\).

### Profinite tail-sector theorem

There is a stronger source statement which does not use Davenport.  On
\[
 \widehat{\mathbb Z}\cong\prod_p\mathbb Z_p
\]
with Haar probability, regard \(m_p\) as the cylinder function `(1)`.  Independence of the prime
coordinates gives
\[
 \mathbb E(m_p)=(1-p^{-1})^2,\qquad
 \mathbb E(m_p^2)=1-p^{-2}.                                  \tag{39}
\]
For finite prime sets \(P\subset Q\),
\[
 \boxed{
 \langle m_P,m_Q\rangle_{L^2(\widehat{\mathbb Z})}
 =
 \prod_{p\in P}(1-p^{-2})
 \prod_{q\in Q\setminus P}(1-q^{-1})^2.
 }                                                            \tag{40}
\]
Consequently, along every prime exhaustion:

1. \(\|m_P\|_2^2\to1/\zeta(2)\);
2. \(m_P\rightharpoonup0\) weakly in \(L^2(\widehat{\mathbb Z})\);
3. for every fixed \(P\), \(\langle m_P,m_Q\rangle\to0\);
4. the net is not \(L^2\)-Cauchy, and
   \[
   \lim_{P\uparrow\mathbb P}
   \ \lim_{\substack{Q\uparrow\mathbb P\\Q\supset P}}
   \|m_P-m_Q\|_2^2={2\over\zeta(2)}.                         \tag{41}
   \]

For weak convergence, first test against a cylinder function depending on a fixed finite set
\(P_0\).  Independence factors out
\[
 \prod_{q\in P\setminus P_0}(1-q^{-1})^2\longrightarrow0.
\]
Cylinder functions are dense and the \(m_P\) are uniformly \(L^2\)-bounded, so the conclusion
extends to every \(L^2\) test.

The pointwise behavior identifies the missing sector.  The independent events
\[
 A_p=\{p^2\mid x\}
\]
have summable probabilities \(p^{-2}\).  Their complement over every prime, the profinite
squarefree locus, has Haar mass
\[
 \prod_p(1-p^{-2})={1\over\zeta(2)}.                         \tag{42}
\]
If some \(A_p\) occurs, the product \(m_P(x)\) is eventually zero.  Conditional on the squarefree
locus, the events
\[
 B_p=\{p\parallel x\}
\]
remain independent and have conditional probabilities \(1/(p+1)\).  Their sum diverges, so
Borel--Cantelli gives infinitely many \(B_p\) almost surely on that locus.  The sign of \(m_P(x)\)
therefore flips infinitely often.  Hence the canonical finite-prime products converge to zero on
the nonsquarefree part and fail to converge on a set of measure \(1/\zeta(2)\).

Möbius parity is thus not obtained as a Haar-measurable limit of its finite Euler clocks.  It is a
tail-sector charge defined on ordinary finite factorizations whose canonical product limit leaves
the Haar representation.  This is the exact reason scalar adelic \(L^2\) restores prime
covariance while erasing the Möbius phase.

## 7. What this means

The corpus had treated five quantities as adjacent:

```text
actual Möbius parity;
squarefree safe factor 1-p^(-2);
projective transverse overlap -1/p;
Möbius/Pluecker record (p-1)/(p+1);
critical p-adic moment 2 sqrt(p)/(p+1).
```

Equations `(7)`--`(29)` show that they are five matrix coefficients of one prime-square additive
Fourier clock.  The \(p+1\)-point projective model is its minimal principal-angle compression.

The infinite obstruction is now equally exact.  Ordinary finite tensor products live in one
Hilbert sector.  Möbius is obtained only by a pointwise limit that leaves that sector completely.
Scalar \(L^2\) completion therefore cannot retain the inter-sector source morphism.  A valid third
completion must contain:

1. both inequivalent incomplete tensor-product sectors;
2. the Fourier/projective correspondence between them;
3. the determinant/Fock record of the vanishing product overlap;
4. the archimedean additive ordering needed by the Laplace/Gamma reporter; and
5. distributional point conormals of the resulting correspondence.

This is a concrete **singular correspondence** problem, not a request for another scalar norm.

## 8. Hostile audit

1. **No RH estimate.**  Equations `(33)`--`(37)` use known Möbius cancellation against each
   fixed periodic sequence.  They give no uniformity when \(M_P\) grows with the Laplace scale.
   That moving-modulus estimate contains the open arithmetic difficulty.
2. **CRT does not preserve archimedean locality.**  The interval or Laplace window
   \(n\lesssim x^{-1}\) is not a product set under `(31)`.  Local Fourier tensorization alone
   cannot bound \(\sum\mu(n)e^{-nx}\).
3. **Pointwise convergence is misleading.**  Equation `(36)` rules out passing from finite clocks
   to Möbius in density \(L^2\).
4. **A measurable extension is not the issue.**  Since the embedded ordinary integers are Haar
   null, arbitrary measurable functions can be assigned their values.  The theorem says that the
   canonical Euler-local product has no Haar limit and its phase belongs to a different sector.
5. **The projective comparison is now source-derived only locally.**  Principal-angle equivalence
   does not yet identify the restricted adelic all-prime correspondence with the global Poisson
   intertwiner or land a Xi conormal.
6. **No novelty over finite Fourier theory is claimed.**  Ramanujan sums, CRT factorization,
   Plancherel, Davenport's estimate, and involution decompositions are parent mathematics.  The
   value is their exact source-specific joint identification and the new infinite-completion
   target it forces.

## 9. Positive survivor

The next RH-bearing theorem is not another local identity.  It is a moving-aperture
archimedean--profinite comparison:

> Construct the renormalized inter-sector Fourier correspondence of the clocks `(1)` before
> scalarization, prove that its archimedean Laplace/Gamma boundary has finite-order prime-angle
> record, and identify its scalar heat supertrace with
> \(\Phi(x)=\sum_n\mu(n)e^{-nx}\).  A source-local finite-order theorem for that record would imply
> the cofinal Gamma--Hankel energy bound already formalized in the corpus and hence RH.

The theorem must gain uniformity as \(P\) grows with the archimedean window.  Fixed-modulus
Davenport cancellation is insufficient.

## Literature boundary

Parent inputs are finite Fourier analysis on cyclic groups, the Ramanujan-sum formula,
Good--Thomas/CRT Fourier factorization, the prime number theorem for Möbius against fixed rational
additive characters, and infinite-product sector theory.  Targeted searches found no source
stating the joint formulas `(7)`--`(29)` as an actual prime-square realization of the projective
Möbius/half-density clock.  No priority claim is made; this card is classified as a building
block unless a specialist audit shows otherwise.

## Gates

- [x] literal prime-square Möbius clock constructed
- [x] exact additive Fourier images of valuation strata computed
- [x] cross-Gram spectrum \(1,-1/p\) proved
- [x] leakage determinant \(1-p^{-2}\) recovered
- [x] Möbius involution decomposed into continuation and record amplitudes
- [x] critical \(p\)-adic spherical moment and projective Möbius overlap unified
- [x] normalized zero-frequency factorization proved
- [x] projective Hellinger natural cone identified with deformed local Möbius clocks
- [x] CRT tensorization proved
- [x] pointwise-versus-density sector fracture proved
- [x] profinite weak-zero and tail-sign nonconvergence proved
- [x] hostile fixed-modulus/moving-aperture distinction recorded
- [ ] construct renormalized all-prime inter-sector correspondence
- [ ] prove moving-aperture archimedean--profinite locality
- [ ] land Meyer/Xi conormal in finite-order record
- [ ] derive cofinal Möbius--Laplace energy bound
- [ ] RH

## Lean status (2026-08-22)

Unconditional Lean modules (wired into `GaloisForLFunctions.RHTower`, `lake build`-green, axiom
audit `[propext, Classical.choice, Quot.sound]`):

- `formal/GaloisForLFunctions/RHTower/PrimeSquareMobiusComplementaryRecord.lean` — §2–§5.
  `countInner_strataVec`; `primeSquareFourier_unitVec`, `primeSquareFourier_valOneVec'` `(7)`;
  `compression_unit_unit`, `compression_valOne_unit`, `compression_unit_valOne`,
  `compression_valOne_valOne` `(8)`; `primeSquareFourier_fourierFixedVec`,
  `countInner_fourierFixedVec_fourier_recordVec`, `countInner_recordVec_fourier_recordVec`,
  `countInner_recordLeak_self` `(9)`--`(11)`; `primeSquareOccupationVec_eq_recordVec` `(14)`;
  `primeSquareSourceInvolution_occupationVec` `(16)`;
  `primeSquareSourceInvolution_fourierFixedVec`, `primeSquareSourceInvolution_recordVec` `(17)`;
  `primeSquareMobiusVec_eq`, `primeRecordSigma_sq_add_tau_sq` `(18)`;
  `primeRecordSigma_eq_sech`, `primeRecordTau_eq_tanh` `(19)`--`(21)`;
  `primeSquareMobiusDFT_strata` and its three case values `(22)`--`(24)`;
  `countInner_mobiusDFT_self` `(25)`; `primeSquare_zeroFrequency_factorization` `(26)`;
  `primeSquare_zeroFrequency_share` `(38)`; `countInner_deformedMobius`,
  `countInner_deformedLine` `(27)`--`(29)`; capstone
  `primeSquare_complementary_record_law` for `p.Prime`.
- `formal/GaloisForLFunctions/RHTower/PrimeSquareMobiusSectorFracture.lean` — §6, profinite half.
  `eulerClockNat_eq_moebius` `(4)`; `sum_primeSquareLocalMobius`,
  `sum_primeSquareLocalMobius_sq` `(39)`; `eulerClockCRT` `(31)`;
  `sum_eulerClockProd_mul`, `eulerClockProd_gram`, `eulerClockProd_gram_univ` `(40)`;
  `eulerClockProd_normSq` `(32)`; `eulerClockProd_dist_sq`, `tendsto_sectorFracture`,
  `tendsto_sectorFracture_iterated` `(41)`; `tendsto_squarefreeSafeProduct` `(42)`;
  `tendsto_primeRecordProduct_zero`.

Still to formalize: the *density* half `(33)`--`(37)`.  Davenport is **not** needed; the corpus
already owns `M(N) = o(N)` as `RHTower.Sieve.tendsto_abs_mertensM_div`.  The remaining bricks are
`μ·m_P = w_P ⍟ μ` with `w_P` the multiplicative `P`-smooth weight `2^{ω(d)}`, the summability
`∑_d w_P(d)/d < ∞`, and the dominated-convergence transfer through
`RHTower.Sieve.sum_Icc_convolution_apply`; plus `∑_{n≤X} μ(n)²/X → 6/π²` from
`RHTower.Sieve.abs_window_squarefree_sub_le` and the inclusion–exclusion mean of `m_P²`.
