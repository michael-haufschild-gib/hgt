# Ramified top-conormal ambidexterity and coherent power-sector classification

- **ID:** `deninger-ramified-top-conormal-ambidexterity`
- **Stage:** 2-fully-proven
- **Type:** NEW STRUCTURAL THEOREM / ROUTE-L PRODUCER REFINEMENT
- **Label:** `DAC_RAMIFIED_TOP_CONORMAL_AMBIDEXTERITY`
- **Parent:** `source-reporter-ambidexterity-categorical-half-density-law`
- **Status:** dependency-closed paper proof; Lean pending

## Frontier statement

The raw ramified power pullback and its Grothendieck-residue transpose do not form a positive
dagger pair. The correct local ramified source block is forced: move pullback into last residue
class, equivalently multiply by relative top-conormal monomial before Hilbert completion.

For every positive power degree `n`, this gives

\[
  C_n:g(X)\longmapsto X^{n-1}g(X^n).
\]

The maps `C_n` compose strictly, their residue extractions compose contravariantly, and after the
rank half-density normalization they satisfy the degree-`n` source relation with literal Hilbert
adjunction.  Moreover, among all monomial residue-class corrections compatible with the
commutative power semigroup, only two exist: raw pullback and this top-conormal pullback.

This is finite ramified local block that Route L had not previously isolated. It does not by
itself construct actual unit-group rational-Witt source stage or cofinal Xi/Gamma realization.

## 1. Ramified block algebra

Fix `k,n >= 1` and put

\[
 A_k=\mathbb C[y]/(y^k),\qquad
 B_{k,n}=\mathbb C[x]/(x^{kn}),\qquad y\longmapsto x^n.
\tag{1}
\]

Write `e_j=x^j`.  Give both algebras the positive Hermitian form for which their displayed
monomial bases are orthonormal.  For `0 <= r < n`, define the residue-class embedding and
extraction

\[
 \begin{aligned}
 E_{n,r}:A_k&\longrightarrow B_{k,n},
 &E_{n,r}(e_j)&=e_{nj+r},\\
 R_{n,r}:B_{k,n}&\longrightarrow A_k,
 &R_{n,r}(e_\ell)&=
 \begin{cases}
 e_j,&\ell=nj+r,\\
 0,&\ell\not\equiv r\pmod n.
 \end{cases}
 \end{aligned}
\tag{2}
\]

Thus `E_(n,0)` is ordinary power pullback and

\[
 C_n:=E_{n,n-1},\qquad C_n(g)=x^{n-1}g(x^n)
\tag{3}
\]

is top-conormal pullback.

## 2. Exact dagger and projection laws

### Theorem 2.1 (residue-class dagger law)

For every `0 <= r < n`,

\[
 E_{n,r}^{\dagger}=R_{n,r},\qquad
 R_{n,r}E_{n,r}=\operatorname{id}_{A_k},
\tag{4}
\]

and `E_(n,r) R_(n,r)` is the orthogonal projection of `B_(k,n)` onto the `r`-th residue-class
sector.  In particular every `E_(n,r)` is an isometry.

#### Proof

For basis vectors,

\[
 \langle E_{n,r}e_j,e_\ell\rangle
 =\delta_{nj+r,\ell}
 =\langle e_j,R_{n,r}e_\ell\rangle.
\]

Sesquilinearity proves the adjoint identity.  Applying `R_(n,r)` to `e_(nj+r)` gives `e_j`, which
proves the left-inverse law.  On a basis vector of `B_(k,n)`, the other composite is the identity
exactly in residue class `r` and zero otherwise.  Hence it is the stated orthogonal projection.

### Corollary 2.2 (rank-normalized source relation)

Put

\[
 V_n^{\mathrm{con}}=\sqrt n\,C_n,
 \qquad
 F_n^{\mathrm{res}}=\sqrt n\,R_{n,n-1}.
\tag{5}
\]

Then

\[
 (V_n^{\mathrm{con}})^\dagger=F_n^{\mathrm{res}},
 \qquad
 F_n^{\mathrm{res}}V_n^{\mathrm{con}}=n\,\operatorname{id}_{A_k}.
\tag{6}
\]

This is strict ramified source/reporter ambidexterity.  No separability or unramified reduction is
used.

## 3. Grothendieck residue selects the top-conormal sector

Let

\[
 \epsilon_j:A_j\longrightarrow\mathbb C
\]

extract the coefficient of the top monomial.  Thus

\[
 \epsilon_k(e_i e_j)=\delta_{i+j,k-1},\qquad
 \epsilon_{kn}(e_a e_b)=\delta_{a+b,kn-1}.
\tag{7}
\]

### Theorem 3.1 (residue transpose of raw power pullback)

For every `a in A_k` and `b in B_(k,n)`,

\[
 \epsilon_{kn}\!\left(E_{n,0}(a)b\right)
 =\epsilon_k\!\left(aR_{n,n-1}(b)\right).
\tag{8}
\]

Consequently the Grothendieck-residue transpose of raw power pullback is `R_(n,n-1)`, while its
positive Hilbert adjoint is `R_(n,0)`.  For `n>1` these reporters have disjoint residue support.
The residue transpose becomes the positive dagger precisely after replacing raw pullback by the
top-conormal pullback `C_n`.

#### Proof

It is enough to take `a=e_j` and `b=e_l`.  The left side is nonzero exactly when

\[
 nj+\ell=kn-1,
\]

equivalently

\[
 \ell=n(k-1-j)+(n-1).
\]

This is exactly the condition that `R_(n,n-1)(e_l)=e_(k-1-j)`, which makes the right side one.
Both sides vanish otherwise.  The Hilbert-adjoint assertions follow from Theorem 2.1.  Residue
classes `0` and `n-1` are distinct when `n>1`.

### Corollary 3.2 (trace/different separation)

The relative module trace and residue functional are

\[
 \operatorname{Tr}_{B_{k,n}/A_k}=nR_{n,0},
 \qquad
 \operatorname{Res}_{B_{k,n}/A_k}=R_{n,n-1}.
\tag{9}
\]

Under the Frobenius identification

\[
 B_{k,n}\simeq\operatorname{Hom}_{A_k}(B_{k,n},A_k),
 \qquad
 u\longmapsto\bigl[b\mapsto\operatorname{Res}(ub)\bigr],
\]

the trace is represented by the relative different

\[
                         n x^{n-1}.
\tag{10}
\]

At the ramified fibre this element is not a unit for `n>1`.  Therefore raw residue orientation
cannot be identified with the trace/Hilbert reporter by a change of generator equal to the
different.  The conormal-shifted source `(3)`, not a raw change of scalar normalization, is the
required correction.

#### Proof

Multiplication by `x^a` permutes the monomial basis only when the exponent remains in range.  Its
diagonal is empty unless `a` is divisible by `n`; for `a=nj` it consists of `n` equal copies of
multiplication by `y^j`.  Hence the relative trace is `nR_(n,0)`.  Also

\[
 R_{n,n-1}(n x^{n-1}b)=nR_{n,0}(b),
\]

which proves `(10)` by perfection of the residue pairing.  The class of `x` is nilpotent in
`B_(k,n)`, so `n x^(n-1)` is a nonunit when `n>1`.

## 4. Strict power-semigroup coherence

For a second power degree `m` and shift `0 <= s < m`, direct substitution gives

\[
 E_{m,s}E_{n,r}=E_{mn,mr+s},
 \qquad
 R_{n,r}R_{m,s}=R_{mn,mr+s},
\tag{11}
\]

where the intermediate and target truncation lengths are the evident ones.

In particular,

\[
 C_mC_n=C_{mn},\qquad
 R_{n,n-1}R_{m,m-1}=R_{mn,mn-1},
\tag{12}
\]

because

\[
                         m(n-1)+(m-1)=mn-1.
\]

### Theorem 4.1 (classification of coherent monomial power sectors)

Suppose integers `r_n` are given for every `n>=1`, with

\[
 0\le r_n<n,qquad r_1=0,qquad
 r_{mn}=mr_n+r_m\quad(m,n\ge1).
\tag{13}
\]

Then exactly one of the following holds for every `n`:

\[
 r_n=0,
 \qquad\text{or}\qquad
 r_n=n-1.
\tag{14}
\]

Both families satisfy `(13)`.  Hence raw pullback and top-conormal pullback are the only strict
monomial sectors compatible with the full commutative power semigroup.

#### Proof

Compute `r_(mn)` in the two orders.  Commutativity of multiplication and `(13)` give

\[
 mr_n+r_m=nr_m+r_n,
 \qquad
 (m-1)r_n=(n-1)r_m.
\tag{15}
\]

Set `m=2`.  Then

\[
                         r_n=(n-1)r_2.
\]

Since `0 <= r_2 < 2`, either `r_2=0` or `r_2=1`, producing the two families in `(14)`.
Their coherence is immediate from `m(n-1)+(m-1)=mn-1` and `m*0+0=0`.

## 5. Impact of updated Hellinger--Hodge--Green descent

The updated paper proves that the full prime--valuation biorthogonal common test retains source
labels but functional-equation diagonal sewing cancels horizontal displacement before summation.
It identifies the surviving possibilities as:

1. act at the singular Hilbert wall;
2. retain off-diagonal label incidence; or
3. introduce a divisor-coupled differential before diagonal pairing.

The map `C_n` realizes the unique coherent finite ramified version of option 3.  Multiplication by
`x^(n-1)` moves the source from raw residue class `0` to the dualizing top-conormal class before
the positive pairing.  Theorem 4.1 proves this correction is forced, not chosen from a family of
ad hoc shifts.

Hostile type audit adds necessary restriction. Existing finite rational-Witt stages are functions
on unit-group quotients `(ZMod m)^x / <p>` and have no ramified zero fibre. Therefore `C_n` cannot
be inserted into that source by identification. Minimal honest thickening retaining exact stage
labels and adjoining conormal grade is constructed and formalized separately in
`deninger-ramified-top-conormal-finite-stage-cocone.md`. It commutes with genuine gauge refinement
and lands injectively in actual algebraic packet, but remains added conormal grade rather than
proved intrinsic framed coefficient.

The paper also proves that the actual ordered `(2,3)` Gamma/co-Poisson boundary is a positive
multiple of the Deninger mate curvature `K_6(rho)`.  The present theorem does **not** prove that
the conormal maps `(5)` realize on the completed Xi Green primitive with character
`lambda_n(s)=n^(1/2-s)`. Exact remaining bridge is intrinsic-source-to-singular:

> Prove genuine framed rational-Witt coefficient supplies top-conormal grade, then construct a
> coefficient-faithful chain map carrying `C_n` and `R_(n,n-1)` to actual Gamma/co-Poisson Xi
> top-conormal transport before diagonal reflection sewing, nonannihilating on every Xi top jet.

If such a chain map preserves `(6)`, source inverse equals analytic dagger on the same Xi fibre;
the already-proved Deninger/Gamma mate identity then forces the horizontal curvature to vanish.
No claim of that bridge is made here.

## 6. Novelty and anti-theatre audit

### Parent mathematics

The following ingredients are classical and are not claimed new:

- monomial decomposition of a ramified power algebra;
- the Frobenius residue pairing on `C[x]/(x^N)`;
- trace equals different times residue;
- adjoint of a coordinate embedding is coordinate extraction;
- the chain rule for power-map differents.

### Candidate-new synthesis

The candidate-new result is the joint package:

1. residue transpose of raw power pullback is exactly the dagger of top-conormal pullback;
2. the normalized top-conormal pair realizes strict degree-`n` ambidexterity through ramification;
3. the full commutative power-semigroup coherence equation classifies all monomial corrections,
   leaving exactly raw and top-conormal sectors;
4. therefore the Deninger Route-L singular source transport is forced to use the top-conormal
   sector before Hilbertization.

The categorical literature on twisted Frobenius right adjoints requires a duality context and
projection-formula inverses; it does not supply this arithmetic ramified sector or its Xi landing.
No matching classification theorem was found in targeted internal or external searches.

### Hostile checks

- No Xi zero is enumerated or assumed simple.
- No RH-equivalent dagger identity is assumed on the Xi divisor.
- No positive diagonal detector is presented as an annihilator.
- The result changes the finite source map itself; it is not post-completion calibration.
- The theorem is nontrivial at every ramified degree `n>1`; raw and conormal reporters have
  disjoint residue support.
- Failure of cofinal Xi/Gamma landing remains explicit and blocks Route-L closure.

## 7. Lean obligations

Formalize without analytic computation:

1. shifted power pullback and residue extraction;
2. extraction/pullback left inverse and sector projection;
3. top-residue transpose identity;
4. exact composition law;
5. coherent-shift classification;
6. finite coordinate adjoint and rank-normalized push--pull law;
7. umbrella import and axiom audit.

## Log

- 2026-08-03 — extracted from updated Hellinger first-coalescence and off-diagonal-source audit;
  proved unique coherent top-conormal correction for ramified Deninger power transfer.
