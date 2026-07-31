# Suzuki global-local compound Bezoutian weld

## Status

`[PROVED ON PAPER: THEOREMS A--C] [FORMALIZED] [CONJECTURE: GRAM OPEN CORE] [SOURCE-PURE] [NO RH PREMISE]`

## Question

Can the local marked Volterra response and the global completed-zeta multiplier be coupled before division so that affine chart ambiguity disappears and the exact RH-bearing Pick kernel has one source-level numerator?

## Corpus frontier

The corpus already supplies:

- a local marked secant pair \((Q,P)\), with affine response \(I=Q/P\);
- the global pair \((S,T)=(\Xi_C',z^2\Xi_C)\), with multiplier \(M_0=S/T\);
- the jump response \(m=I-M_0\);
- projective Pluecker data for the local pair and a Volterra Cartesian phase defect;
- obstructions showing that local Pluecker data alone does not determine an affine response, scalar jump positivity is not source-visible, and the missing step is a prime--Gamma Green/Gram identity.

What is absent is an exact, division-free global-local carrier for the full jump Pick kernel. Existing cards name a desired "marked tensor plus Xi deficit" but do not identify its canonical algebraic form.

## External novelty audit

- Suzuki's [screw-function RH criterion](https://arxiv.org/abs/2206.03682) and [2026 operator construction](https://arxiv.org/abs/2606.09096) provide the explicit prime--Gamma source, compressed operators, and RH-equivalent positivity/spectral formulations. They do not supply the compound global-local determinant below.
- [Boundary-triple/Weyl-function theory](https://arxiv.org/abs/1706.07948) supplies abstract Green identities and Nevanlinna realizations. It cannot manufacture source positivity for this particular pair without assuming the missing positive realization.
- Bezoutian product identities are classical algebra. Their use below is therefore `[BRIDGE]`. The source-specific coupling of Suzuki's marked Volterra pair with \((\Xi_C',z^2\Xi_C)\) is `[NOVELTY UNVERIFIED]` pending broader literature review.

## Conjecture

For local pair \((Q,P)\) and global pair \((S,T)\), define

\[
  N:=QT-SP,\qquad D:=PT.
\]

Then:

1. off the zero sets of \(P,T\), \(N/D=Q/P-S/T=m\);
2. \(N\) is invariant under every common pointwise affine gauge
   \((Q,S)\mapsto(Q+\delta P,S+\delta T)\);
3. among bilinear global-local welds, common-gauge invariance plus vanishing when \(QT=SP\) characterizes \(N\) up to scale;
4. its Hermitian Bezoutian satisfies the exact product rule

\[
 \mathcal B(N,D)
 =T(z)\overline{T(w)}\,\mathcal B(Q,P)
 -P(z)\overline{P(w)}\,\mathcal B(S,T);
\]

5. after Suzuki source specialization, the right side admits a positive prime--Gamma Green/Gram factorization on one nontrivial aperture.

Items 1--4 are algebraic and should be provable unconditionally. Item 5 is the new RH-bearing open core:

`SUZUKI-COMPOUND-BEZOUTIAN-GRAM`.

## Scientific-method attack plan

### Predictions

- Common affine gauge must cancel before any quotient or nonvanishing assumption.
- Independent gauges must leave exactly one relative-gauge curvature term.
- Opposite shifts and diagonal/even sectors must survive because \(Q\), rather than only its alternating Pluecker chord, enters \(N\).
- A fake functional-equation orbit must not pass: changing \((S,T)\) changes \(N\).
- Rank one must not trivialize the construction.

### Falsifiers

- A second linearly independent bilinear weld satisfying the same invariance and coincidence laws.
- Failure of the Bezoutian product rule at cross-numerator level.
- Dependence on division or a zero-free premise.
- Collapse of \(N\) under opposite shifts or rank-one local data.
- Source positivity requiring an RH-equivalent premise.

### Next experiment

Prove the classification and cross-Bezoutian identity symbolically, audit all listed degeneracies, then formalize those exact unconditional statements. Only afterward attack source Gram factorization.

## Dependency ledger

- `[PROVED]` local marked Volterra pair and Cartesian phase-defect decomposition.
- `[PROVED]` global shifted-Xi multiplier pair.
- `[PROVED]` RH is equivalent to positivity of the full jump Pick kernel in the existing Suzuki route.
- `[CONJECTURE]` source Gram factorization of the compound Bezoutian.
- `[NO RH PREMISE]` in proposed algebraic reduction.

## Paper theorem

### Definitions

Let \(R\) be a commutative ring. For two local/global projective pairs
\((Q,P)\) and \((S,T)\), put

\[
 N(Q,P,S,T):=QT-SP,\qquad D(P,T):=PT.
\]

For complex-valued functions \(F,G\), define the division-free Hermitian
Bezout cross-numerator

\[
 [F,G]_{z,w}:=F(z)\overline{G(w)}-G(z)\overline{F(w)}.
\]

### Theorem A: canonical common-gauge weld

The following statements hold.

1. If \(P,T\) are invertible, then
   \[
   \frac{N}{D}=\frac QP-\frac ST.
   \]
2. For arbitrary \(\delta\in R\),
   \[
   N(Q+\delta P,P,S+\delta T,T)=N(Q,P,S,T).
   \]
3. For independent gauges \(\delta_L,\delta_G\),
   \[
   N(Q+\delta_LP,P,S+\delta_GT,T)
   =N+(\delta_L-\delta_G)D.
   \]
4. Let
   \[
   W=aQS+bQT+cPS+dPT
   \]
   be a bidegree-\((1,1)\) weld. If \(W\) is invariant under every common
   affine gauge and \(W=0\) whenever \(QT=SP\), then
   \[
   W=b(QT-SP).
   \]

Thus \(N\) is the unique such weld up to scalar.

### Proof

Statements 1--3 are direct ring identities. For 4, common-gauge invariance
gives

\[
0=a\delta(QT+PS)+a\delta^2PT+(b+c)\delta PT
\]

for all inputs. Take \((Q,P,S,T,\delta)=(0,1,1,0,1)\) to obtain \(a=0\).
Then take \((0,1,0,1,1)\) to obtain \(b+c=0\). Hence
\(W=b(QT-SP)+dPT\). The coincident input \((Q,P,S,T)=(0,1,0,1)\)
has \(QT=SP\), so \(d=0\). This proves the classification. \(\square\)

### Theorem B: compound Bezoutian product rule

For arbitrary complex-valued functions \(Q,P,S,T\), pointwise compound
functions \(N=QT-SP\), \(D=PT\), and arbitrary \(z,w\),

\[
 [N,D]_{z,w}
 =T(z)\overline{T(w)}[Q,P]_{z,w}
  -P(z)\overline{P(w)}[S,T]_{z,w}.
\]

No division, zero-free region, functional equation, or RH premise is used.

### Proof

Expanding the left side gives

\[
\begin{aligned}
 &(Q_zT_z-S_zP_z)\overline{P_wT_w}
 -P_zT_z\overline{(Q_wT_w-S_wP_w)}\\
={}&T_z\overline{T_w}
 (Q_z\overline{P_w}-P_z\overline{Q_w})
 -P_z\overline{P_w}
 (S_z\overline{T_w}-T_z\overline{S_w}),
\end{aligned}
\]

which is the claimed identity. \(\square\)

### Theorem C: exact relative-gauge curvature

If \(N_r=N+rD\) for a complex-valued function \(r\), then

\[
 [N_r,D]_{z,w}
 =[N,D]_{z,w}
 +D(z)\overline{D(w)}\bigl(r(z)-\overline{r(w)}\bigr).
\]

Consequently every common pointwise gauge is invisible, while every real
constant relative gauge is also invisible to the Hermitian Bezoutian. After
division by \(z-\overline w\), a nonconstant relative gauge contributes its
own Pick curvature multiplied by \(D(z)\overline{D(w)}\).

### Proof

Substitute \(N_r=N+rD\) into the cross-numerator and collect the two new
terms. \(\square\)

## Suzuki source specialization

Set

\[
 Q=Q_{\alpha,\beta}^{\mathrm{Volterra}},\qquad
 P=(Y-\beta y)(Y-\alpha y),\qquad
 S=\Xi_C',\qquad T=z^2\Xi_C.
\]

Then \((N,D)\) is the canonical bidegree-\((1,1)\), common-gauge-invariant
carrier of the full jump response

\[
 I_{\alpha,\beta}-M_0
 =\frac{Q_{\alpha,\beta}^{\mathrm{Volterra}}}{P}
  -\frac{\Xi_C'}{z^2\Xi_C}.
\]

Theorem B identifies the exact previously missing "marked tensor plus Xi
deficit": it is not the local Pluecker tensor alone but the compound
Bezoutian

\[
 T(z)\overline{T(w)}[Q,P]_{z,w}
 -P(z)\overline{P(w)}[\Xi_C',z^2\Xi_C]_{z,w}.
\]

This is an unconditional representation theorem, not a positivity theorem.
RH-bearing work is now concentrated in one source statement: factor this
specific difference as a positive prime--Gamma Gram form on a nontrivial
aperture.

## Hostile audit

### Affine gauge attack — survives with correction

The corpus's earlier affine-chart warning is too coarse for the RH kernel.
The response changes under independent gauges, but a common pointwise gauge
cancels exactly in \(N\). Moreover, a real constant relative gauge changes
the response but not its Pick kernel. The actual obstruction is relative
nonconstant/non-real gauge curvature, quantified exactly by Theorem C.

### Opposite-shift attack — survives

The weld retains \(Q\) itself, not only its alternating Pluecker chord.
Therefore symmetric and diagonal sectors exposed by opposite shifts are not
discarded by construction. No algebraic identity forces \(N\) to vanish in
that regime.

### Fake functional-equation orbit — survives

A change \((S,T)\mapsto(S+\Delta S,T+\Delta T)\) changes the carrier by
\(Q\Delta T-P\Delta S\), except for genuine projective/gauge degeneracies.
Thus functional-equation symmetry alone cannot freeze the compound source.

### Rank-one attack — survives

The construction uses a determinant between local and global projective
pairs, not a local exterior square. A one-dimensional local channel can have
\(QT-SP\ne0\); for example \((Q,P,S,T)=(1,1,0,1)\).

### Zero/division attack — survives

Theorems A.2--A.4, B, and C are polynomial identities. Only the optional
quotient interpretation A.1 requires invertible denominators.

### Circularity attack — survives at representation level

No positivity, Nevanlinna realization, zero location, or RH equivalent is
used. The remaining Gram conjecture is explicitly not claimed proved.

## Strongest positive survivor

`[PROVED ON PAPER] [SOURCE-PURE] [NO RH PREMISE]`

The unique common-gauge compound weld and its exact Hermitian Bezoutian
product rule give a canonical division-free full-jump kernel. This replaces
the vague frontier `SUZUKI-MARKED-SECANT-CD-WELD` by the precise open core

`SUZUKI-COMPOUND-BEZOUTIAN-GRAM`:

> Derive directly from Suzuki's prime--Gamma screw source a positive Gram
> factorization of the specialized compound Bezoutian on one nontrivial
> aperture, without assuming a Herglotz property or RH-equivalent positivity.

## Novelty verdict

- The determinant and Bezoutian product rule: `[BRIDGE]` (classical algebra).
- Their exact source specialization as the canonical cure for the corpus's
  local/global affine-gauge mismatch: `[NOVELTY UNVERIFIED]`.
- Scientific value: exact reduction of the RH-bearing frontier to one
  source-level signed Gram identity, with all chart ambiguity and denominator
  issues removed.

## Current verdict

`SURVIVES PRELIMINARY ATTACK`: paper proof and unconditional Lean
formalization are complete for Theorems A--C and the source specialization.
Gram positivity remains the single open core; no RH proof is claimed.
