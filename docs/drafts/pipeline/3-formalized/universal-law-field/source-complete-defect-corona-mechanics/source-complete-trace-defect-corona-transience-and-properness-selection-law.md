# Source-complete trace-defect corona transience and properness selection law

- **ID:** ULF-SCDCM-TRACE-CORONA
- **Stage:** 3-formalized
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [REDISCOVERED]`
  `[FUSION + CONSERVATION + PROPERNESS] [COMMON-RECOVERY NEUTRAL]`
  `[FUNCTIONAL-EQUATION NEUTRAL] [NOT NEW FIELD CORE] [LEAN-PROVED] [NOT RH]`
- **Failure audit:**
  `../../../5-failed/universal-law-field/source-complete-defect-corona-mechanics/source-complete-defect-corona-is-the-universal-field.md`
- **Date:** 2026-08-13

## 1. Purpose

This theorem does not introduce another obstruction variable.  It proves a bridge for what an
infinite, source-complete formation law does to every positive finite-energy defect:

1. source labels localize its normal cluster;
2. source fusion equalizes the remaining local values;
3. infinite dimensionality excludes a nonzero scalar normal defect;
4. conserved trace therefore moves to the observer corona;
5. a proper source cost makes that corona infinitely expensive.

The bridge simultaneously contains a fusion law, an exact normal/corona conservation identity,
a formation-properness selection theorem, and an information-neutral common-recovery action.

Hostile corpus audit found that stronger global formation/properness, essential-formation,
complete-test-closure, marked-variation, and operator-topology mechanisms were already Lean-certified.
Accordingly this theorem is retained as a correct operator-algebra chart, not promoted as the
missing universal field or as new scientific knowledge.

## 2. Explicit source-complete carrier

Let

\[
 H=\ell^2(\mathbb N_0)
 \tag{SC.1}
\]

with orthonormal basis `(e_j)_{j >= 0}`.  Define

\[
 Le_j=2^{-j}e_j,
 \qquad
 \Omega=\sum_{j\ge0}\sqrt3\,2^{-(j+1)}e_j,
 \qquad
 P=|\Omega\rangle\langle\Omega|.
 \tag{SC.2}
\]

The normalization is exact:

\[
 \|\Omega\|^2
 =3\sum_{j\ge0}4^{-(j+1)}=1.
 \tag{SC.3}
\]

Thus `L` is a compact positive label with simple nonzero eigenvalues and `P` is a rank-one
orthogonal projection whose fusion vector has nonzero coefficient in every source coordinate.

Write `S_1(H)` for trace-class operators and `K(H)` for compact operators.  For an operator pair
write `[A,B]=AB-BA`.

### Definition 2.1 -- source-complete reporter packet

Let `H_0` be an infinite-dimensional separable Hilbert space.  A finite bounded reporter packet

\[
 \mathfrak A=(A_1,\ldots,A_s)\subset\mathcal B(H_0)
 \tag{SC.3a}
\]

is **source-complete** when its common commutant is scalar:

\[
 \mathfrak A'
 =\{T:[T,A_a]=0\text{ for every }a\}
 =\mathbb C1.
 \tag{SC.3b}
\]

This is the intrinsic hypothesis.  The explicit pair `(L,P)` in `(SC.2)` is a concrete
source-complete packet by Theorem 3.1; its numerical coordinates are not part of the general law.

## 3. Source-complete normal-cluster theorem

### Theorem 3.1 -- scalar common commutant and trace-class exclusion

If `T in B(H)` satisfies

\[
 [T,L]=0,
 \qquad
 [T,P]=0,
 \tag{SC.4}
\]

then `T=c1_H` for a scalar `c`.  In particular, if `T in S_1(H)`, then `T=0`.

### Proof

Let `T_ij=<Te_j,e_i>`.  Since the eigenvalues `2^{-j}` of `L` are pairwise distinct,

\[
 0=\langle[T,L]e_j,e_i\rangle
 =(2^{-j}-2^{-i})T_{ij}
 \tag{SC.5}
\]

implies `T_ij=0` whenever `i != j`.  Hence `T` is diagonal, say `Te_j=t_j e_j`.

Put `omega_j=sqrt(3) 2^{-(j+1)}`.  Every `omega_j` is nonzero, and

\[
 \langle[T,P]e_j,e_i\rangle
 =(t_i-t_j)\omega_i\overline{\omega_j}.
 \tag{SC.6}
\]

Therefore all `t_j` are equal to one scalar `c`, so `T=c1_H`.  If `T` is additionally trace class,
then it is compact, whereas a nonzero scalar multiple of the identity is not compact on an
infinite-dimensional Hilbert space.  In that case `c=0`.  QED.

### Theorem 3.2 -- asymptotic source completeness forces compact-observer extinction

Let `(T_n)` be a sequence of positive trace-class operators such that

\[
 \sup_n\operatorname{tr}T_n<\infty,
 \qquad
 \|[T_n,L]\|_1+\|[T_n,P]\|_1\longrightarrow0.
 \tag{SC.7}
\]

Then for every compact operator `K`,

\[
 \boxed{\operatorname{tr}(KT_n)\longrightarrow0.}
 \tag{SC.8}
\]

### Proof

The standard duality

\[
 \mathcal K(H)^*=\mathcal S_1(H)
 \tag{SC.9}
\]

identifies bounded trace-class sets with weak-star bounded sets of functionals on `K(H)`.  Since
`H` is separable, `K(H)` is separable; hence every bounded sequence in `S_1(H)` has a weak-star
convergent subsequence on `K(H)`.  Let a subsequence converge to `T in S_1(H)`.

For every compact `A`, cyclicity of the trace gives

\[
 \operatorname{tr}(A[T_n,L])
 =\operatorname{tr}((LA-AL)T_n).
 \tag{SC.10}
\]

The left side tends to zero by `(SC.7)`, while `LA-AL` is compact.  Passing to the weak-star limit
shows `tr((LA-AL)T)=0` for every compact `A`, hence `[T,L]=0`.  The same argument with `P` gives
`[T,P]=0`.  Theorem 3.1 yields `T=0`.

Every weak-star cluster point is therefore zero.  If `(SC.8)` failed for some compact `K`, a
subsequence with pairing bounded away from zero would possess a further weak-star convergent
subsequence, whose limit would again be zero, a contradiction.  QED.

### Theorem 3.3 -- coordinate-free source-complete transience

Let `H_0` be an infinite-dimensional separable Hilbert space, let
`A=(A_1,...,A_s)` be any source-complete reporter packet, and let `(R_n)` be positive trace-class
operators satisfying

\[
 \sup_n\operatorname{tr}R_n<\infty,
 \qquad
 \|[R_n,A_a]\|_1\longrightarrow0
 \quad(1\le a\le s).
 \tag{SC.10a}
\]

Then

\[
 \boxed{\operatorname{tr}(KR_n)\longrightarrow0
 \quad\text{for every }K\in\mathcal K(H_0).}
 \tag{SC.10b}
\]

### Proof

Take a weak-star trace-class cluster point `R`.  For compact `B`, boundedness of `A_a` makes
`A_aB-BA_a` compact, and

\[
 \operatorname{tr}(B[R_n,A_a])
 =\operatorname{tr}((A_aB-BA_a)R_n)\longrightarrow0.
 \tag{SC.10c}
\]

Hence `[R,A_a]=0` for every `a`.  Source completeness gives `R=c1`.  Since `R` is trace class and
`H_0` is infinite dimensional, `c=0`.  Unique-cluster reasoning from Theorem 3.2 gives the full
convergence `(SC.10b)`.  QED.

All later corona, tightness, fusion, recovery, and compact-Gram conclusions use only compact
extinction.  They therefore hold verbatim for Theorem 3.3 after replacing `(L,P,T_n,H)` by
`(A,R_n,H_0)`.

## 4. Normal/corona conservation

Let

\[
 \widetilde{\mathcal K(H)}=\mathcal K(H)+\mathbb C1
 \tag{SC.11}
\]

be the minimal unitization.  Its quotient by `K(H)` is `C`, with quotient character

\[
 \omega_\infty(K+c1)=c.
 \tag{SC.12}
\]

### Theorem 4.1 -- trace becomes corona mass

Under the hypotheses of Theorem 3.2, assume additionally that

\[
 \operatorname{tr}T_n\longrightarrow m\ge0.
 \tag{SC.13}
\]

Define positive functionals on the unitization by

\[
 \varphi_n(K+c1)=\operatorname{tr}(KT_n)+c\operatorname{tr}T_n.
 \tag{SC.14}
\]

Then

\[
 \boxed{\varphi_n\overset{w^*}{\longrightarrow}m\omega_\infty.}
 \tag{SC.15}
\]

In particular, when `tr T_n=1`, every `varphi_n` is a state and it converges to the unique state of
the scalar quotient.

### Proof

For `K+c1` in the unitization, Theorem 3.2 and `(SC.13)` give

\[
 \varphi_n(K+c1)longrightarrow 0+cm=m\omega_\infty(K+c1).
 \tag{SC.16}
\]

This is exactly weak-star convergence on the unitization.  QED.

Let

\[
 Q_r=\sum_{j=0}^{r}|e_j\rangle\langle e_j|
 \tag{SC.17}
\]

be the finite source-head projection.

### Corollary 4.2 -- exact head/tail conservation

For every fixed `r`,

\[
 \operatorname{tr}(Q_rT_n)\longrightarrow0.
 \tag{SC.18}
\]

If `(SC.13)` holds, then

\[
 \boxed{
 \lim_{r\to\infty}\lim_{n\to\infty}
 \operatorname{tr}((1-Q_r)T_n)=m.}
 \tag{SC.19}
\]

Indeed, for every `n,r`,

\[
 \operatorname{tr}T_n
 =\operatorname{tr}(Q_rT_n)
 +\operatorname{tr}((1-Q_r)T_n).
 \tag{SC.20}
\]

Thus no mass is destroyed.  Source completeness moves all asymptotically invariant mass beyond
every finite compact chart.

## 5. Formation properness and selection

### Definition 5.1 -- tight formation

A positive trace-class sequence `(T_n)` is uniformly source-tight when

\[
 \lim_{r\to\infty}\sup_n
 \operatorname{tr}((1-Q_r)T_n)=0.
 \tag{SC.21}
\]

### Theorem 5.2 -- tight source-complete defects become extinct

If `(T_n)` satisfies Theorem 3.2 and `(SC.21)`, then

\[
 \boxed{\operatorname{tr}T_n=\|T_n\|_1\longrightarrow0.}
 \tag{SC.22}
\]

### Proof

Fix `epsilon>0`.  Choose `r` such that the tail in `(SC.21)` is at most `epsilon` for every `n`.
Since `Q_r` is compact, Theorem 3.2 gives `tr(Q_rT_n)->0`.  Hence

\[
 \limsup_n\operatorname{tr}T_n
 \le \epsilon.
 \tag{SC.23}
\]

Let `epsilon` tend to zero.  Positivity gives `||T_n||_1=tr T_n`.  QED.

Now let `(c_j)` be any increasing positive sequence with `c_j -> infinity`, and define the proper
diagonal source cost

\[
 Ce_j=c_je_j.
 \tag{SC.24}
\]

For `T>=0`, define its extended energy by

\[
 \mathcal E_C(T)
 =\operatorname{tr}(C^{1/2}TC^{1/2})
 =\sum_{j\ge0}c_j\langle Te_j,e_j\rangle
 \in[0,\infty].
 \tag{SC.25}
\]

### Theorem 5.3 -- properness selection law

Let `(T_n)` satisfy Theorem 3.2.

1. If `sup_n E_C(T_n)<infinity`, then `(T_n)` is uniformly source-tight and therefore
   `||T_n||_1->0`.
2. If `tr T_n -> m>0`, then

\[
 \boxed{\mathcal E_C(T_n)\longrightarrow\infty.}
 \tag{SC.26}
\]

Consequently no normalized positive defect can be simultaneously asymptotically source-complete
and of uniformly bounded proper formation cost.

### Proof

For every `r`, positivity and `(SC.25)` imply

\[
 \operatorname{tr}((1-Q_r)T_n)
 \le {\mathcal E_C(T_n)\over c_{r+1}}.
 \tag{SC.27}
\]

Uniformly bounded energy therefore gives `(SC.21)`, and Theorem 5.2 proves item 1.

For item 2, fix `M>0` and choose `r` so that `c_j>=M` for every `j>r`.  Then

\[
 \mathcal E_C(T_n)
 \ge M\operatorname{tr}((1-Q_r)T_n)
 =M\bigl(\operatorname{tr}T_n-\operatorname{tr}(Q_rT_n)\bigr).
 \tag{SC.28}
\]

Theorem 3.2 gives `tr(Q_rT_n)->0`, so

\[
 \liminf_n\mathcal E_C(T_n)\ge Mm.
 \tag{SC.29}
\]

Since `M` is arbitrary, the energy tends to infinity.  QED.

### Corollary 5.4 -- coordinate-free compact-resolvent properness

Let `(R_n)` satisfy Theorem 3.3 and let `C_0` be any nonnegative self-adjoint operator on `H_0`
with compact resolvent and eigenvalues tending to infinity, counted with finite multiplicity.  Then:

1. bounded `C_0`-energy forces `||R_n||_1->0`;
2. if `tr R_n->m>0`, then `E_(C_0)(R_n)->infinity`.

### Proof

The spectral projections of `C_0` below a finite threshold are finite rank.  Their complements
satisfy the Markov bound

\[
 \operatorname{tr}(1_{(M,\infty)}(C_0)R_n)
 \le M^{-1}\mathcal E_{C_0}(R_n).
 \tag{SC.29a}
\]

Thus bounded energy gives uniform tightness.  Conversely, compact extinction makes every fixed
low-energy spectral head tend to zero, while positive limiting trace remains in the complement,
where its cost is at least `M`.  Let `M->infinity`, exactly as in `(SC.28)`--`(SC.29)`.  QED.

## 6. Positive fusion law

### Theorem 6.1 -- source-complete defect capital fuses additively

Let `a=1,...,s` index finitely many positive trace-class sequences `T_n^(a)` satisfying `(SC.7)`,
and let `alpha_a>=0` be fixed.  Put

\[
 S_n=\sum_{a=1}^s\alpha_aT_n^{(a)}.
 \tag{SC.30}
\]

Then `S_n` again satisfies `(SC.7)`.  If `tr T_n^(a)->m_a`, then

\[
 \boxed{
 S_n\longrightarrow0\text{ on }\mathcal K(H),
 \qquad
 \widetilde S_n\longrightarrow
 \Bigl(\sum_a\alpha_am_a\Bigr)\omega_\infty.}
 \tag{SC.31}
\]

Moreover

\[
\mathcal E_C(S_n)=\sum_a\alpha_a\mathcal E_C(T_n^{(a)}).
\tag{SC.32}
\]

Thus formation, corona mass, and proper cost obey one exact additive fusion law.

### Proof

Positivity and trace-class boundedness are preserved by a finite positive sum.  The triangle
inequality gives

\[
 \|[S_n,L]\|_1+\|[S_n,P]\|_1
 \le\sum_a\alpha_a
 \bigl(\|[T_n^{(a)},L]\|_1+\|[T_n^{(a)},P]\|_1\bigr),
 \tag{SC.33}
\]

which tends to zero.  In `(SC.31)`, `\widetilde S_n` denotes the positive unitization functional
associated to `S_n` by formula `(SC.14)`.  Theorem 3.2 and Theorem 4.1 give `(SC.31)`.  Formula
`(SC.32)` follows from the nonnegative series `(SC.25)` and finite additivity.  QED.

### Corollary 6.2 -- positive fusion has no cancellation channel

Assume every `alpha_a>0`.

1. If `sup_n E_C(S_n)<infinity`, then

\[
 \|T_n^{(a)}\|_1\longrightarrow0
 \qquad\text{for every }a.
 \tag{SC.33a}
\]

2. If one component satisfies `tr T_n^(b)->m_b>0`, then

\[
 \mathcal E_C(S_n)\longrightarrow\infty.
 \tag{SC.33b}
\]

Thus positive formation of distinct organs cannot erase a persistent component by cross-organ
cancellation.

### Proof

By `(SC.32)`, bounded fused energy implies

\[
 \mathcal E_C(T_n^{(a)})
 \le \alpha_a^{-1}\mathcal E_C(S_n)
 \tag{SC.33c}
\]

for each `a`.  Theorem 5.3 gives item 1.  If component `b` has positive limiting trace, its energy
diverges by Theorem 5.3, and `(SC.32)` gives
`E_C(S_n)>=alpha_b E_C(T_n^(b))->infinity`.  QED.

## 7. Common recovery and functional-equation action

### Theorem 7.1 -- isometric common recovery is information-neutral

Let `V:H->H'` be an isometry into another Hilbert space.  Form

\[
 \widehat T_n=VT_nV^*,
 \qquad
 \widehat L=VLV^*,
 \qquad
 \widehat P=VPV^*.
 \tag{SC.34}
\]

Then

\[
 \operatorname{tr}\widehat T_n=\operatorname{tr}T_n,
 \tag{SC.35}
\]

\[
 \|[\widehat T_n,\widehat L]\|_1=\|[T_n,L]\|_1,
 \qquad
 \|[\widehat T_n,\widehat P]\|_1=\|[T_n,P]\|_1,
 \tag{SC.36}
\]

and, for every compact `K'` on `H'`,

\[
 \operatorname{tr}(K'\widehat T_n)
 =\operatorname{tr}((V^*K'V)T_n).
 \tag{SC.37}
\]

Hence common recovery preserves compact-observer extinction and corona mass exactly.  Decompose
`H'=VH direct-sum (VH)^perp`.  If `D` is any nonnegative self-adjoint operator on `(VH)^perp` and
the recovered cost is the nonnegative self-adjoint direct sum

\[
 C'=VCV^*\oplus D,
 \tag{SC.38a}
\]

then

\[
 \mathcal E_{C'}(\widehat T_n)=\mathcal E_C(T_n).
 \tag{SC.38}
\]

The lift creates no information, mass, or finite-cost advantage.

### Proof

Use `V^*V=1`.  Equations `(SC.35)`--`(SC.37)` are invariance/cyclicity of the trace and invariance
of singular values under the corner embedding `A |-> VAV*`.  The recovered defect is supported on
`VH`, so the complementary cost `D` contributes zero.  Equation `(SC.38)` follows first for finite
spectral truncations of `C` and then by monotone convergence.  QED.

### Corollary 7.2 -- functional-equation conjugation is information-neutral

Let `U:H->H` be unitary and transform the entire formed packet by

\[
 T_n^U=UT_nU^*,
 \qquad
 L^U=ULU^*,
 \qquad
 P^U=UPU^*,
 \qquad
 C^U=UCU^*.
 \tag{SC.39}
\]

Then trace, both commutator trace norms, compact-observer extinction, corona mass, and proper cost
are unchanged.  In particular a functional-equation involution can transport the mechanism but
cannot turn a corona-transient defect into a tight finite-cost defect.

This is a covariance theorem, not a claim that the functional equation supplies `(SC.7)`.

## 8. Fourth-organ prediction: compact Gram collapse

### Theorem 8.1 -- finite positive reporter packets collapse before the history cost

Let `A_1,...,A_d` be compact operators and define

\[
 G_n(i,j)=\operatorname{tr}(T_nA_i^*A_j).
 \tag{SC.40}
\]

Then each `G_n` is positive semidefinite and, under `(SC.7)`,

\[
 \boxed{G_n\longrightarrow0\text{ entrywise and in every matrix norm}.}
 \tag{SC.41}
\]

Consequently every positive-size principal determinant and every singular value of `G_n` tends to
zero.  If additionally `tr T_n->m>0`, then every proper source cost diverges by Theorem 5.3.

### Proof

For `z in C^d`,

\[
 z^*G_nz
 =\operatorname{tr}\left(
 T_n\Bigl(\sum_i z_iA_i\Bigr)^*
     \Bigl(\sum_j z_jA_j\Bigr)
 \right)\ge0.
 \tag{SC.42}
\]

Every `A_i^*A_j` is compact, so Theorem 3.2 gives entrywise convergence to zero.  In fixed finite
dimension this is convergence in every matrix norm; determinant and singular-value convergence
follow.  QED.

The prediction is sharp: compact positive determinants can collapse while conserved defect mass
and lifted history remain nonzero.  A determinant-only selection theorem must therefore add
tightness, properness, or a genuinely noncompact reporter.

## 9. Sharp countermodels and load-bearing hypotheses

### 9.1 Source completeness without properness does not select

Take

\[
 T_n=|e_n\rangle\langle e_n|.
 \tag{SC.43}
\]

Then `tr T_n=1` and `[T_n,L]=0`.  Also

\[
 \|[T_n,P]\|_1\le2|\langle e_n,\Omega\rangle|longrightarrow0.
 \tag{SC.44}
\]

Thus all source-completeness hypotheses hold, but `T_n` does not vanish in trace norm.  It moves to
the corona.  For `Ce_j=(j+1)e_j`, its energy is `n+1->infinity`.  Properness, not another compact
observer, is the missing selection law.

### 9.2 Finite dimension does not convert scalarity into extinction

On `C^N`, a simple diagonal label and a full-support fusion vector again have scalar common
commutant, but `N^{-1}1` is a nonzero invariant positive trace-one defect.  Infinite dimension is
load-bearing.

### 9.3 Full support is load-bearing

If one coefficient of `Omega` vanishes, the corresponding coordinate projection commutes with both
`L` and `P`, giving a nonzero tight trace-class defect.

### 9.4 Label simplicity is load-bearing

If `L` has a repeated eigenspace of dimension at least two, choose a nonzero vector in that
eigenspace orthogonal to the projection of `Omega`; its rank-one projection commutes with `L` and
`P`.

### 9.5 Normality is load-bearing

The corona character itself is a positive invariant state on the unitization but is not represented
by a trace-class density.  The theorem excludes finite-energy normal defects; it does not erase the
boundary by definition.

### 9.6 Reporter compactness is load-bearing

The identity is not compact and detects `tr T_n`.  Compact extinction is therefore not ordinary
weak convergence against all bounded operators.  This distinction is the conservation mechanism.

## 10. Corpus interpretation and exact open arithmetic premise

The theorem is route-independent and unconditional as functional analysis.  It does **not** yet
prove RH.  A route may use it only after constructing, before zero specialization:

1. a positive trace-class defect family `T_N(rho)` on one complete source carrier;
2. a source-native simple label and full-support fusion projector;
3. asymptotic trace-norm commutation `(SC.7)`;
4. off-neutral nonzero trace;
5. source tightness or bounded proper formation cost.

Items 3--5 are the exact formation/properness gate.  If all hold off the neutral locus, Theorem 5.3
gives a contradiction.  If one fails, that failure identifies a typed missing operation rather than
producing another scalar endpoint.

## 11. External and internal boundary

The proof uses classical trace-class/compact duality, irreducible common commutants, tightness, and
coercive moment bounds.  Quantum Markov irreducibility, microlocal defect measures, generalized
Young measures, H-measures, and concentration compactness contain neighboring ingredients.  No
external novelty claim is made for those ingredients.

The useful coupling in this chart is:

\[
 \boxed{
 \text{complete source invariance}
 \Longrightarrow
 \text{normal mass becomes corona mass}
 \Longrightarrow
 \text{proper cost diverges}.}
 \tag{SC.45}
\]

Unlike a generic defect measure, `(SC.45)` tells the defect where it must go and states the precise
additional law that excludes it.  This is still a source consumer: it assumes the source-complete
reporter packet, asymptotic commutation, and proper cost.  The corpus-wide missing mechanism is the
endogenous generation of those tests and costs from the source law itself.

## 12. Formalization status

`[LEAN-PROVED]`.  Every theorem, corollary and countermodel of §§2–9 is formalized, including the
coordinate-free Theorem 3.3 on every separable infinite-dimensional space; see the Lean certificate
below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.IsometricConjugationSchatten`, `GaloisForLFunctions.HTGeometry.SourceCompleteTransience`, `GaloisForLFunctions.HTGeometry.SourceCompleteCoronaProperness`, `GaloisForLFunctions.HTGeometry.SourceCompleteFusionRecovery`, `GaloisForLFunctions.HTGeometry.SourceCompleteCountermodels`, `GaloisForLFunctions.RHTower.TraceNorm`, `GaloisForLFunctions.RHTower.TraceClassCyclicity`, `GaloisForLFunctions.RHTower.TraceClassOperatorTrace`, `GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace`, `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitSelection`, `GaloisForLFunctions.HTGeometry.WeakSequentialCompactness`, `GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix`, `GaloisForLFunctions.HTGeometry.ObserverHorizonStability`, `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCountermodels`, `GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

New modules: `GaloisForLFunctions.HTGeometry.IsometricConjugationSchatten`, `GaloisForLFunctions.HTGeometry.SourceCompleteTransience`,
`GaloisForLFunctions.HTGeometry.SourceCompleteCoronaProperness`, `GaloisForLFunctions.HTGeometry.SourceCompleteFusionRecovery` and
`GaloisForLFunctions.HTGeometry.SourceCompleteCountermodels`. They build on the trace-class layer (`GaloisForLFunctions.RHTower.TraceNorm`,
`GaloisForLFunctions.RHTower.TraceClassCyclicity`, `GaloisForLFunctions.RHTower.TraceClassOperatorTrace`, `GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace`),
the matrix-vector selection machinery of `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitSelection` (with `GaloisForLFunctions.HTGeometry.WeakSequentialCompactness`
and `GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix`), the compact/weakly-null lemma of `GaloisForLFunctions.HTGeometry.ObserverHorizonStability`, the
coordinate projections of `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCountermodels`, and `GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp`.
Every module is clean under `lake env lean`, builds as a module, and the axiom audit shows only `[propext, Classical.choice, Quot.sound]`.
Theorems 3.2/3.3 are proved without the duality (SC.9): weak clusters are extracted in `ℓ²(ℕ×ℕ)` through operator matrices
transported by a Hilbert basis, and compact observers are handled by the tail estimate `‖K(1 - Q_r)‖ → 0`. The general theory
is stated on any Hilbert space with a Hilbert basis indexed by `ℕ` (and on every separable infinite-dimensional space via
`exists_hilbertBasis_nat`); the explicit pair `(L, P)` is an instance. The functional `φ_n` of (SC.14) is evaluated on unitization
elements `K + c1`, whose scalar part is unique (`unitization_scalar_unique`). A nonnegative cost with compact resolvent
(Corollary 5.4) is given by its spectral data, an orthonormal eigenbasis with eigenvalues `μ_k ≥ 0` of finite sublevel sets, and
`E_C(T) = Σ μ_k ⟨f_k, T f_k⟩` (SC.25); the recovered cost `VCV* ⊕ D` of (SC.38a) is diagonal in a basis `V f ∪ g`, `g ⊥ VE`.

| Claim | Lean declaration |
|-|-|
| (SC.1)–(SC.3) carrier, `L e_j = 2^{-j} e_j`, `Ω`, `‖Ω‖ = 1`, `P = ∣Ω⟩⟨Ω∣` a rank-one projection with full support | `sourceLabelWeight`, `sourceLabelWeight_injective`, `sourceLabel`, `fusionCoeff`, `hasSum_norm_fusionCoeff_sq`, `fusionVector`, `norm_fusionVector`, `fusionCoeff_ne_zero`, `fusionProjection`, `fusionProjection_isProjection` |
| (SC.3a)–(SC.3b) source-complete packets | `IsSourceComplete` |
| Theorem 3.1 (SC.4)–(SC.6) scalar common commutant; trace-class exclusion | `isSourceComplete_diag_rankOne`, `isSourceComplete_sourceLabel_fusion`, `eq_zero_of_memSchattenClass_commute`, `eq_zero_of_isHilbertSchmidt_smul_id` |
| Theorem 3.2 (SC.7)–(SC.10) asymptotic source completeness forces compact-observer extinction | `tendsto_opTrace_comp_sourceLabel_fusion`, `IsAsymptoticallySourceInvariant`, `IsAsymptoticallySourceInvariant.tendsto_opTrace_comp` |
| Theorem 3.3 (SC.10a)–(SC.10c) coordinate-free transience | `tendsto_inner_of_isSourceComplete`, `tendsto_opTrace_comp_of_isSourceComplete`, `tendsto_opTrace_comp_of_isSourceComplete'`, `exists_hilbertBasis_nat`, `exists_weakCluster_lp`, `tendsto_opTrace_comp_of_weaklyNull`, `tendsto_norm_comp_sub_headProjection`, `headProjection`, `basisIsometry`, `cornerConj`, `approxNumber_cornerConj`, `traceNorm_cornerConj`, `memSchattenClass_cornerConj_iff`, `opTrace_cornerConj` |
| (SC.11)–(SC.12) unitization, corona character well defined | `not_isCompactOperator_id`, `unitization_scalar_unique` |
| Theorem 4.1 (SC.13)–(SC.16) `φ_n → m ω_∞`; `φ_n` a state when `tr T_n = 1` | `opTrace_unitization`, `IsAsymptoticallySourceInvariant.tendsto_unitization`, `unitization_isState`, `re_opTrace_comp_nonneg` |
| Corollary 4.2 (SC.17)–(SC.20) head extinction, tail conservation, `lim_r lim_n tr((1-Q_r)T_n) = m` | `basisHead`, `basisHead_basis`, `isCompactOperator_basisHead`, `opTrace_basisHead_comp`, `opTrace_head_add_tail`, `IsAsymptoticallySourceInvariant.head_tail` |
| Definition 5.1, Theorem 5.2 (SC.21)–(SC.23) tight defects become extinct | `IsSourceTight`, `IsAsymptoticallySourceInvariant.tendsto_traceNorm_of_tight` |
| (SC.24)–(SC.29) Theorem 5.3 diagonal proper cost: tightness bound, extinction under bounded energy, divergence under persistent trace | `properCostEnergy`, `isProperSpectrum_of_monotone`, `ofReal_mul_tail_basisHead_le`, `IsAsymptoticallySourceInvariant.tendsto_traceNorm_of_bounded_energy`, `IsAsymptoticallySourceInvariant.tendsto_properCostEnergy_top` |
| Corollary 5.4 (SC.29a) compact-resolvent proper cost | `IsProperSpectrum`, `ofReal_mul_tail_le_properCostEnergy`, `notMem_sublevel`, `IsAsymptoticallySourceInvariant.tendsto_head`, `IsAsymptoticallySourceInvariant.tendsto_traceNorm_of_bounded_energy`, `IsAsymptoticallySourceInvariant.tendsto_properCostEnergy_top` |
| Theorem 6.1 (SC.30)–(SC.33) positive fusion: (SC.7) preserved, corona masses add, cost additive | `fusedDefect`, `fusedDefect_comm`, `memSchattenClass_one_finset_sum`, `opTrace_finset_sum`, `IsAsymptoticallySourceInvariant.fusion`, `IsAsymptoticallySourceInvariant.fusion_corona`, `properCostEnergy_fusedDefect` |
| Corollary 6.2 (SC.33a)–(SC.33c) no cancellation channel | `IsAsymptoticallySourceInvariant.fusion_no_cancellation` |
| Theorem 7.1 (SC.34)–(SC.38) isometric common recovery is information-neutral | `recovery_invariants`, `cornerConj_comp`, `cornerConj_commutator`, `cornerConj_isPositive`, `IsAsymptoticallySourceInvariant.recovery`, `IsAsymptoticallySourceInvariant.recovery_extinction`, `properCostEnergy_recovery` |
| Corollary 7.2 (SC.39) unitary (functional-equation) conjugation is neutral | `recovery_invariants`, `properCostEnergy_conj`, `exists_hilbertBasis_map`, `coronaCharacter_invariant` |
| Theorem 8.1 (SC.40)–(SC.42) compact Gram matrices are PSD and collapse: entries, every matrix norm, principal minors, eigenvalues | `reporterGramMatrix`, `dotProduct_reporterGramMatrix`, `reporterGramMatrix_posSemidef`, `IsAsymptoticallySourceInvariant.tendsto_reporterGramMatrix`, `IsAsymptoticallySourceInvariant.tendsto_norm_reporterGramMatrix`, `IsAsymptoticallySourceInvariant.tendsto_det_reporterGramMatrix`, `IsAsymptoticallySourceInvariant.tendsto_eigenvalues_reporterGramMatrix` |
| §9.1 (SC.43)–(SC.44) `T_n = ∣e_n⟩⟨e_n∣`: all hypotheses, `tr = ‖·‖₁ = 1`, energy `n + 1 → ∞` | `coordinate_countermodel`, `fusionHeatSource`, `tendsto_fusionCoeff`, `lpCoordProjection_comm_lpDiag`, `opTrace_lpCoordProjection` |
| §9.2 finite dimension is load-bearing | `finiteDimension_countermodel`, `memSchattenClass_one_of_finiteDimensional` |
| §9.3 full support is load-bearing | `fullSupport_countermodel` |
| §9.4 label simplicity is load-bearing | `simplicity_countermodel`, `rankOne_comp_rankOne_of_inner_eq_zero` |
| §9.5 normality is load-bearing: `ω_∞` positive, invariant, not normal | `coronaCharacter_nonneg`, `coronaCharacter_invariant`, `coronaCharacter_not_normal`, `tendsto_inner_hilbertBasis` |
| §9.6 reporter compactness is load-bearing | `coordinate_countermodel_compact_vs_identity`, `not_isCompactOperator_id` |

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
