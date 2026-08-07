# Essential inverse-flow tomography of the Hedenmalm theta source

- **ID:** `hedenmalm-essential-inverse-flow-prime-tomography`
- **Stage:** 2-fully-proven / needs literature and Lean audit
- **Type:** THEOREM / SOURCE-DERIVED SINGULAR SPECTRAL CALCULUS
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  `hedenmalm-theta-source-compressed-inverse-determinant.md`;
  `../../4-publication-ready/fixed-width-two-edge-weil-source-spectrum/main.tex`;
  `../../3-formalized/prime-valuation-reflection-type-conservation-law.md`.

## Result

Let `k` be the normalized positive even Hedenmalm theta source, and let

\[
 B=A^{-1}P\quad\text{on}\quad
 \mathcal H_k=L^2(\mathbb R,k^{-1}dx)
 \tag{1}
\]

be the source-derived Hilbert--Schmidt operator of the parent theorem.  Its nonzero eigenvalues,
with algebraic multiplicity, are

\[
 \mu=-\frac1z=-\frac{i}{w},
 \qquad
 \Xi_C(z)=0,
 \qquad
 \Xi\!\left(\frac12+w\right)=0,
 \qquad w=iz.
 \tag{2}
\]

For `L>0` and `a>=L`, define on the punctured plane

\[
 \Phi_{a,L}(\mu)
 =2\mu\left[
   \sin\!\left(\frac a\mu\right)
  -\sin\!\left(\frac{a-L}\mu\right)
 \right].
 \tag{3}
\]

For `epsilon>0` avoiding the moduli of the nonzero spectrum, let `P_epsilon` be the finite-rank
Riesz projection of `B` onto all generalized eigenspaces with `|mu|>epsilon`.  Since
`Phi_(a,L)` is holomorphic near that finite spectrum, ordinary finite-dimensional holomorphic
functional calculus defines `Phi_(a,L)(B|ran P_epsilon)`.  Put

\[
 \tau^{\mathrm{ess}}_{B,a,L}
 =\lim_{\epsilon\downarrow0}
   \operatorname{tr}_{\operatorname{ran}P_\epsilon}
   \left(\Phi_{a,L}(B|\operatorname{ran}P_\epsilon)^2\right).
 \tag{4}
\]

Then:

1. The limit `(4)` exists absolutely and is independent of the admissible cofinal sequence of
   cutoffs.
2. It equals the fixed-width Xi--Weil observable
   \[
   \tau^{\mathrm{ess}}_{B,a,L}
    =Q_L(a)
    =\sum_w m(w)F_{a,L}(w)^2,
   \tag{5}
   \]
   where
   \[
   A_L(w)=\frac{1-e^{-Lw}}w,
   \qquad
   F_{a,L}(w)=e^{aw}A_L(w)+e^{-aw}A_L(-w).
   \]
3. On the ordinary-integer logarithmic orbit `a=(1/2) log n`, every admissible sample is the
   literal finite prime--Gamma source coefficient from the fixed-width theorem:
   \[
   \tau^{\mathrm{ess}}_{B,\frac12\log n,L}=q_L(n)=g_L(n).
   \tag{6}
   \]
   In particular, this single aggregate source sequence reconstructs every off-critical
   eigenvalue of `B` and its algebraic multiplicity through the poles and normalized residues of
   its ordinary Dirichlet series.  This is global tomography; it does not attach a separate prime
   incidence record to each individual Riesz fibre.
4. `Phi_(a,L)` is even and has an essential singularity at `mu=0` for every `L>0`, `a>=L`.
   Hence reflection is internal,
   \[
   RBR=-B,
   \qquad
   \Phi_{a,L}(-\mu)=\Phi_{a,L}(\mu),
   \tag{7}
   \]
   but the observer lies outside every finite-pole-order functional calculus at the compact
   boundary.
5. The Riemann hypothesis is exactly boundedness of this one source-defined inverse-flow trace on
   its integer orbit:
   \[
   \mathrm{RH}
   \quad\Longleftrightarrow\quad
   \sup_{\substack{n\ge1\\ \frac12\log n\ge L}}
   \left|\tau^{\mathrm{ess}}_{B,\frac12\log n,L}\right|<\infty.
   \tag{8}
   \]

Statement `(8)` is a terminal equivalence, not an RH proof.  New content is the exact
source-operator/prime-source identification `(3)`--`(6)` and the classification of its required
boundary operation as an essential inverse flow.

## Proof

### 1. Reciprocal coordinate and inverse-flow window

The Hedenmalm compact operator has eigenvalue `mu=-1/z` at a zero `z` of `XiC`.  In the centered
`s`-coordinate, `w=iz`, so

\[
 \mu=-\frac{i}{w},
 \qquad
 w=-\frac{i}{\mu}.
 \tag{9}
\]

Substitution into the two-edge transform gives

\[
\begin{aligned}
 F_{a,L}\!\left(-\frac{i}{\mu}\right)
 &=e^{-ia/\mu}
   \frac{1-e^{iL/\mu}}{-i/\mu}
   +e^{ia/\mu}
   \frac{1-e^{-iL/\mu}}{i/\mu}\\
 &=2\mu\left[
   \sin\!\left(\frac a\mu\right)
  -\sin\!\left(\frac{a-L}\mu\right)
  \right]\\
 &=\Phi_{a,L}(\mu).
\end{aligned}
\tag{10}
\]

Thus translation of a fixed physical window is not finite order after compactification: it is the
inverse flow `exp(+/- ia/mu)` at the accumulation point of the compact spectrum.

### 2. Absolute punctured Riesz trace

Every nonzero spectral point of a compact operator is isolated, has finite algebraic
multiplicity, and only finitely many have modulus above a fixed positive cutoff.  On each
generalized eigenspace at `mu`, finite-dimensional holomorphic functional calculus and nilpotent
Jordan decomposition give

\[
 \operatorname{tr}\left(\Phi_{a,L}(B)^2\right)
 =m_B(\mu)\Phi_{a,L}(\mu)^2;
 \tag{11}
\]

all derivative terms multiply positive powers of the nilpotent part and have zero trace.

The centered Xi divisor lies in `|Re w|<1/2`, and the classical zero count gives

\[
 \sum_w\frac{m(w)}{|w|^2}<\infty.
 \tag{12}
\]

For fixed `a>=L`, edge factorization gives

\[
 F_{a,L}(w)
 =A_L(w)\left(e^{aw}+e^{-(a-L)w}\right),
 \tag{13}
\]

and therefore

\[
 |F_{a,L}(w)|
 \le
 \frac{1+e^{L/2}}{|w|}
 \left(e^{a/2}+e^{(a-L)/2}\right).
 \tag{14}
\]

Equations `(10)`, `(12)`, and `(14)` prove

\[
 \sum_{\mu\in\sigma(B)\setminus\{0\}}
 m_B(\mu)|\Phi_{a,L}(\mu)|^2<\infty.
 \tag{15}
\]

Consequently the Riesz traces converge absolutely and independently of cutoff order.  The exact
spectral-divisor and multiplicity theorem for `B`, followed by `(10)`, proves `(5)`.

### 3. Arithmetic source weld

The fixed-width explicit formula proves, for every admissible integer `n`,

\[
 Q_L\!\left(\frac12\log n\right)
 =-2\sum_{2\le k\le n}\frac{\Lambda(k)}{\sqrt k}
     R_{L,\frac12\log n}(\log k)
  +\operatorname{Re}\mathcal A_{\infty,L,\frac12\log n}
 =g_L(n).
 \tag{16}
\]

Combining `(5)` and `(16)` proves `(6)`.  The same parent theorem proves that the meromorphic
continuation of `sum g_L(n)n^(-s)` has exactly the poles `1+w` with `Re w>0`, residue
`2m(w)A_L(w)^2`, and no cancellation.  Equation `(9)` transports that recovered divisor and
multiplicity to the nonreal part of the compact spectrum of `B`.

### 4. Essentiality and reflection

Expanding `(3)` at the puncture yields

\[
 \Phi_{a,L}(\mu)
 =2\sum_{r\ge0}\frac{(-1)^r
   \left(a^{2r+1}-(a-L)^{2r+1}\right)}{(2r+1)!}
   \mu^{-2r}.
 \tag{17}
\]

Because `L>0` and `a>=L`, every coefficient in parentheses is strictly positive.  Infinitely many
negative Laurent powers occur, so `mu=0` is essential.  Formula `(3)` also gives
`Phi_(a,L)(-mu)=Phi_(a,L)(mu)`.  Since evenness of the theta source gives `RBR=-B`, `(7)` follows.

Finally, the fixed-width tomography theorem proves

\[
 \mathrm{RH}
 \Longleftrightarrow
 \sup_{n\text{ admissible}}|q_L(n)|<\infty.
 \tag{18}
\]

Substitution of `(6)` proves `(8)`.

## Meaning

This identifies the previously unnamed `third completion` more sharply.

- `B` compactifies the complete theta divisor into a source-derived Hilbert--Schmidt operator;
  high zeros accumulate only at `mu=0`.
- Physical translation in the unbounded zero coordinate becomes the essential inverse flow
  `exp(+/- ia/mu)` at that single compact boundary point.
- The punctured Riesz trace retains every generalized eigenspace and algebraic multiplicity.
- Restriction to the logarithmic integer orbit is not an abstract divisor observable: its
  aggregate trace is the literal finite von Mangoldt plus Gamma source sequence `g_L`.
- The corpus's finite-Rees no-sewing law is therefore sharp for this construction.  Infinite rank
  is insufficient, while the first source mechanism that carries the complete divisor indeed has
  an essential singularity beyond every finite Rees order.

The operation is not an ordinary bounded holomorphic functional calculus of `B`.  It is a
cofinal, punctured spectral trace of the inverse generator.  This explains at once why finite
truncations can retain individual modes but lose uniform covariance, why the ordinary infinite
Hilbert completion loses point fibres, and why a finite-order repair cannot restore both.

## What remains between this theorem and RH

The theta-source-to-divisor carrier is now explicit, reflection-internal, multiplicity-faithful,
and aggregate-prime faithful.  Missing theorem is no longer construction of a global theta mode.
Two obligations remain distinct: a fibrewise ordinary-prime incidence landing, and an independent
arithmetic law controlling the inverse flow:

> Prove directly from the Euler--Poisson--Gamma source that the punctured inverse-flow traces in
> `(6)` are bounded on the full admissible logarithmic integer orbit (equivalently, are
> nonnegative, or have no negative Dirichlet mass).

The fixed-width theorem proves that any one of these conclusions is exactly RH.  Calling the
required law `unitarity`, `purity`, `same-fibre dagger`, `conservativity`, or `almost periodicity`
does not weaken it.  A useful provider must expose a source identity or estimate not already
equivalent by definition.

The Hedenmalm positive-self-adjoint question is also sharply delimited.  The source-core
classification proves that no nonzero positive-definite metric with Schwartz-continuous pullback
exists on the full algebraic range, and no such semidefinite form is closable in ordinary `L2`.
Any successful self-adjoint realization must therefore live on the essential inverse-flow
completion above, or on an equally singular rigging, and must prove its positivity without first
selecting the real divisor.

## Hostile audit

1. **No positivity gain.**  The trace in `(4)` is algebraic, not a Hilbert norm.  For a hypothetical
   off-line zero it has the compulsory two-sided excursions of the fixed-width theorem.
2. **No bounded operator `Phi(B)`.**  Essentiality at zero prevents ordinary holomorphic functional
   calculus on all of `sigma(B)`.  Only finite punctured Riesz calculi and their absolutely
   convergent scalar traces are asserted.
3. **No hidden zero choice.**  Operator `B` is defined from `k`, `A`, and `P`.  Riesz cutoffs are
   spectral operations on that fixed operator.  Zeros enter the proof of the trace identity, not
   its operator-side definition.
4. **Prime incidence is not inferred from `det_2`.**  It enters only through the independent exact
   Guinand--Weil source formula `(16)`.  This is why `(6)`, rather than `(5)` alone, is load-bearing.
   Formula `(6)` identifies the total trace, not a prime-labelled decomposition of each Riesz
   fibre.
5. **Multiplicity survives.**  Riesz trace counts algebraic dimension, and the Grushin theorem
   identifies it with analytic zero order.  No simplicity assumption occurs.
6. **Essentiality is necessary, not sufficient.**  Generic positive even sources can produce the
   same compact/inverse-flow architecture with nonreal Fourier zeros.  Theta arithmetic must still
   supply the missing boundedness law.
7. **No self-adjoint realization claimed.**  Spectral reality in `(8)` remains unproved.

## Preliminary literature audit

Hedenmalm's June 2026 preprint constructs the theta differential pencil and formulates
self-adjointness of the pair `(LD,L)`, but does not compactify the pencil by `B`, define the
punctured inverse-flow trace, or identify a fixed-width prime--Gamma sequence with that trace:
<https://arxiv.org/abs/2606.17494>.

Livsic colligation theory, triangular integration-operator models, Riesz projections, and
finite-dimensional holomorphic calculus are parent operator theory.  The closest surveyed
sources construct characteristic functions and triangular models, not the theta-specific
identity `(3)`--`(6)`:

- <https://arxiv.org/abs/2312.17333>
- <https://arxiv.org/abs/2104.12694>

Targeted searches for `punctured Riesz trace`, `essential inverse flow`, compact-operator
essential-singular traces, and Xi inverse Fredholm models found no direct match.  This is only a
preliminary noncollision result; `[NOVELTY UNVERIFIED]` remains mandatory.

## Lean status

`[PARTIAL]`  `formal/GaloisForLFunctions/RHTower/HedenmalmEssentialFlowSymbol.lean`
(namespace `RHTower.HedenmalmThetaSource`).  All declarations are `#print axioms`-clean.

| # | statement | Lean declaration |
|---|---|---|
| `(3)` | the fixed-width tomography symbol in the compact reciprocal coordinate | `essentialFlowSymbol` |
| `(5)` | the fixed-width amplitude `A_L` and the Weil sample `F_(a,L)` | `weilWidthAmplitude`, `weilFixedWidthSample` |
| `(3)`,`(5)` | the common closed form of both on a root block | `rootBlockForm`, `essentialFlowSymbol_eq_rootBlockForm`, `weilFixedWidthSample_eq_rootBlockForm` |
| `(3)`,`(5)` | **`Phi_(a,L)(-1/z) = F_(a,L)(i z)`**: the symbol reproduces the Weil sample on every root block | `essentialFlowSymbol_root` |
| `(2)` | the compact eigenvalue in both spectral coordinates, `mu = -1/z = -i/w` at `w = i z` | `compactEigenvalue_eq_of_spectralParameter` |
| `(2)` | `Xi_C(z) = 0` is `Xi(1/2 + w) = 0` at `w = i z` | `xiC_eq_xi_shift`, `xiC_eq_zero_iff_xi_shift` |

This is the spectral-sample matching of the card at the level of the symbols, which is what `(5)`
compares term by term; it needs no operator theory.  The parent compact reciprocal coordinate is
`RHTower.HedenmalmThetaSource.compactNormalMultiplier` of the two-prime frame card, whose special
case `a = L/2` is `essentialFlowSymbol` up to the prime normalization.

Still missing, and all of it inherited from the unformalized part of the parent card
`hedenmalm-theta-source-compressed-inverse-determinant.md`: the Riesz projections `P_epsilon`, the
finite-dimensional holomorphic functional calculus on their ranges, the trace `(4)` and its
cutoff-independent limit `(1)`, the divisor sum `(5)` itself, and the prime--Gamma sampling `(6)`.
None of these can be built before the multiplicity clause and the trace layer of the parent.

## Gates

- [x] source-derived compact carrier
- [x] exact reciprocal centered-coordinate conversion
- [x] essential inverse-flow window computed
- [x] punctured Riesz trace defined without enumerating zeros
- [x] absolute convergence and cutoff independence
- [x] Xi fixed-width trace identity
- [x] literal ordinary-prime--Gamma source weld
- [x] reflection internal and multiplicity faithful
- [x] terminal boundedness/RH equivalence identified honestly
- [x] preliminary focused literature audit of essential inverse-flow/Riesz-trace formulation
- [ ] independent operator-theory priority audit
- [x] fibrewise prime-incidence conormal and root-block landing in
      `hedenmalm-prime-translation-rank-one-anomaly.md`
- [ ] formalize concrete weighted-`L2` operator and punctured trace
- [ ] prove independent Euler--Poisson--Gamma inverse-flow boundedness law
- [ ] RH
