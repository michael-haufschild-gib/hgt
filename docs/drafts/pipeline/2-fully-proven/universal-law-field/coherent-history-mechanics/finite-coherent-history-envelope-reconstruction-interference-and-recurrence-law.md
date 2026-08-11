# Finite coherent-history envelope, reconstruction, interference, and recurrence law

- **ID:** ULF-HIST-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT FUSION THEOREM
- **Status:** [DEPENDENCY-CLOSED PAPER PROOF] [THREE-ORGAN FUSION]
  [JOINT RECONSTRUCTION] [EXACT CONSERVATION] [FOURTH-ORGAN PREDICTION]
  [LEAN-PROVED CORE] [AXIOM-AUDITED] [NOT RH]

## 1. Setup

Let `X,Y` be finite sets.  A finite generated history presentation consists of finite sets
`H_(y,x)` and nonzero complex weights `a_h` for `h in H_(y,x)`.  Define

\[
A_{yx}=\sum_{h\in H_{yx}}a_h,
\qquad
E_{yx}=\sum_{h\in H_{yx}}|a_h|,
\qquad
\phi_h=\frac{a_h}{|a_h|}.
\tag{CH.1}
\]

`A` is coherent endpoint execution.  `E` is the source-marked positive history envelope.  Zero
histories may be deleted; they affect neither quantity.

For any complex matrix `T`, write `m(T)` for its entrywise modulus.  Matrix products use execution
order: `BA` means first `A`, then `B`.

## 2. Least-positive-majorant theorem

### Theorem 2.1

For every complex matrix `A:X->Y`, `m(A)` is the unique least nonnegative matrix `P` satisfying

\[
|(Au)_y|\le\sum_xP_{yx}|u_x|
\quad\text{for all }u\in\mathbb C^X, y\in Y.
\tag{CH.2}
\]

Every generated history envelope satisfies

\[
m(A)\le E
\tag{CH.3}
\]

entrywise.

### Proof

The triangle inequality gives `(CH.2)` for `P=m(A)`.  If another `P` satisfies `(CH.2)`, put
`u=e_x`.  Then `|A_(yx)|<=P_(yx)` for every pair, proving minimality and uniqueness.  Equation
`(CH.3)` is the triangle inequality applied to `(CH.1)`.  QED.

Thus `m(A)` is the positive envelope after all intermediate histories have been forgotten, while
`E` retains the source presentation.

## 3. Polar reconstruction and phase-dispersion conservation

For one nonempty history fibre `H`, put `p_h=|a_h|` and

\[
G_{hk}=\phi_h\overline{\phi_k}.
\tag{CH.4}
\]

### Theorem 3.1 — joint reconstruction

The pair `(p,G)` reconstructs the history weights `(a_h)` up to one common unit phase.  More
precisely, for any anchor `h_0`,

\[
\widetilde a_h=p_hG_{h h_0}=a_h\overline{\phi_{h_0}}.
\tag{CH.5}
\]

Hence one anchored phase reconstructs every `a_h` exactly.

### Proof

Substitute `(CH.4)`:

\[
p_hG_{h h_0}=|a_h|\phi_h\overline{\phi_{h_0}}
=a_h\overline{\phi_{h_0}}.
\]

The multiplier is independent of `h` and has modulus one.  QED.

### Theorem 3.2 — phase-dispersion identity

For `S=sum_h a_h` and `V=sum_h p_h`,

\[
\boxed{
V^2=|S|^2+rac12\sum_{h,k}p_hp_k|\phi_h-\phi_k|^2.}
\tag{CH.6}
\]

The second term is nonnegative and vanishes exactly when every history phase is equal.

### Proof

Since the phases are unit,

\[
|\phi_h-\phi_k|^2
=2-2\operatorname{Re}(\phi_h\overline{\phi_k}).
\]

Therefore the second term equals

\[
\sum_{h,k}p_hp_k-
\operatorname{Re}\sum_{h,k}p_hp_k\phi_h\overline{\phi_k}
=V^2-|S|^2.
\]

If it vanishes, every summand is nonnegative and every `p_hp_k` is positive, so all phase
differences vanish.  The converse is immediate.  QED.

This is the first fusion identity.  Positive mass equals visible coherent mass plus exact
orientation disagreement.

## 4. Interventional energy conservation

Let `w_x>0` be source weights and `r_x in C` an intervention score.  For each output `y`, set

\[
v_y=\sum_{x,h\in H_{yx}}w_x|a_h|,
\qquad
s_y=\begin{cases}
v_y^{-1}\sum_{x,h\in H_{yx}}w_xa_hr_x,&v_y>0,\\
0,&v_y=0.
\end{cases}
\tag{CH.7}
\]

### Theorem 4.1

\[
\boxed{
\sum_{x,y,h}w_x|a_h||r_x|^2
=\sum_yv_y|s_y|^2
+\sum_{x,y,h}w_x|a_h||\phi_hr_x-s_y|^2.}
\tag{CH.8}
\]

### Proof

Fix `y` with `v_y>0`.  Expand the last square.  Its cross term is

\[
-2\operatorname{Re}\left(
\overline{s_y}\sum_{x,h}w_x|a_h|\phi_hr_x
\right)
=-2v_y|s_y|^2
\]

by `(CH.7)`, while the constant term is `v_y|s_y|^2`.  Hence the residual equals the
input energy at `y` minus `v_y|s_y|^2`.  If `v_y=0`, the fibre is empty and both sides at `y` are
zero.  Sum over `y`.  QED.

The coherent phase-weighted response and unresolved history variance exactly exhaust positive
intervention energy.

## 5. Composition, interference defect, and associativity conservation

For composable complex matrices `A,B`, define

\[
\Delta(B,A)=m(B)m(A)-m(BA).
\tag{CH.9}
\]

### Theorem 5.1 — positive interference defect

`Delta(B,A)` is entrywise nonnegative.  It is exactly the excess of the positive two-stage history
envelope over the least positive majorant of the coherently collapsed composite.

### Proof

For every output/input pair,

\[
|(BA)_{zx}|=
\left|\sum_yB_{zy}A_{yx}\right|
\le\sum_y|B_{zy}||A_{yx}|.
\]

The right side is `(m(B)m(A))_(zx)`.  The interpretation follows from Theorem 2.1.  QED.

### Theorem 5.2 — exact associativity conservation

For three composable complex matrices,

\[
\boxed{
m(C)\Delta(B,A)+\Delta(C,BA)
=\Delta(C,B)m(A)+\Delta(CB,A).}
\tag{CH.10}
\]

### Proof

Expand the left side:

\[
m(C)m(B)m(A)-m(C)m(BA)+m(C)m(BA)-m(CBA)
=m(C)m(B)m(A)-m(CBA).
\]

Expanding the right side gives the same expression.  QED.

This is not curvature terminology.  It is an exact conservation law: changing the
parenthesization changes where interference memory is registered, not its total transported
positive budget.

## 6. Fourth-organ theorem: recurrent response with open positive history

### Theorem 6.1

Define

\[
A=\begin{pmatrix}3/5&2/5\\8/5&-3/5\end{pmatrix},
\qquad
M=m(A)=\begin{pmatrix}3/5&2/5\\8/5&3/5\end{pmatrix},
\qquad
q=\binom12.
\tag{CH.11}
\]

Then

\[
A^2=I,
\qquad
Mq=\frac75q,
\qquad
M^nq=\left(\frac75\right)^nq.
\tag{CH.12}
\]

Consequently the coherent evolution is exactly period two, while its source-marked positive path
envelope has an exponentially growing direction.  Moreover

\[
\|M^n-m(A^n)\|\longrightarrow\infty
\tag{CH.13}
\]

in every matrix norm.

### Proof

Direct multiplication gives

\[
A^2=
\begin{pmatrix}
9/25+16/25&6/25-6/25\\
24/25-24/25&16/25+9/25
\end{pmatrix}=I.
\]

Also

\[
Mq=\binom{3/5+4/5}{8/5+6/5}=\frac75\binom12.
\]

Induction gives the third identity.  Since `A^n` alternates between `I` and `A`, `m(A^n)` is
bounded.  But `M^nq=(7/5)^nq` is unbounded, so `M^n-m(A^n)` is unbounded as an operator and hence
in every norm on the finite-dimensional matrix space.  QED.

### Corollary 6.2 — positive-carrier obstruction

There is no nonzero positive vector `u` comparable with `q` and satisfying `Mu<=u`.  In particular,
the recurrent coherent process admits no finite invariant positive carrier dominating its marked
history envelope.

### Proof

If `c q<=u<=C q` with `c,C>0` and `Mu<=u`, then

\[
c(7/5)^nq=M^n(cq)\le M^nu\le u\le Cq
\]

for every `n`, impossible as `n` grows.  QED.

This theorem was predicted from `(CH.10)`: recurrent coherent collapse does not bound retained
variation history.  It is a theorem in the recurrence/open-history organ and simultaneously a
sharp positive-carrier no-go.

## 7. Three-organ fusion and fourth-organ prediction

The theorem fuses:

1. **oscillatory/cancellation organ:** coherent sums and products `A`;
2. **orientation organ:** phase Gram reconstruction and the exact dispersion term in `(CH.6)`;
3. **positive admission/coercivity organ:** least majorants, history envelopes, and intervention
   energy in `(CH.8)`.

Equations `(CH.6)`, `(CH.8)`, and `(CH.10)` are joint conservation laws.  Theorem 6.1 is the
withheld fourth-organ prediction: exact recurrence downstairs with forced exponential history
upstairs.

## 8. Sharp boundaries

1. **Source marking is load-bearing.** Splitting one amplitude into cancelling pieces changes `E`
   without changing `A`.  Arbitrary presentations are therefore not invariants.
2. **Legal concatenation is load-bearing.** `m(B)m(A)` represents all two-stage histories only
   when every matched intermediate state is legal.  Constraints require a restricted path
   incidence matrix.
3. **Finite theorem only.** Infinite systems require regularity, summability, strictness, and a
   chosen completion.  Those are precisely live frontier issues.
4. **Not every recurrent law has open envelope.** The extra condition is spectral growth of the
   marked variation execution.  Positive stochastic/permutation laws have no such growth.
5. **Not every phase defect is physical.** The phase packet is source data; physical clock, action,
   or complexity needs an independent sourced comparison.
6. **No RH consequence yet.** The actual Euler–Gamma–Stokes history factorization and its
   contractive positive envelope have not been constructed.

## 9. Parent mathematics

The algebra uses triangle inequalities, rank-one phase Gram matrices, conditional variance,
regular-operator majorants, path sums, and quasiprobability variation overhead.  These ingredients
are classical.  The exact synthesis is used here as a field mechanism and a source-realization
gate, not as a priority claim.

## 10. Lean certification

`GaloisForLFunctions.HTGeometry.CoherentHistoryMechanics` certifies:

1. the two-history phase-dispersion identity and nonnegativity;
2. the matrix interference-defect associativity identity;
3. the closed rational recurrent/open-envelope witness `(CH.11)`–`(CH.12)`;
4. no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.

The arbitrary finite-history conditional-variance identity `(CH.8)` remains paper-only.  The
phase-reconstruction core, least-majorant theorem, full matrix composition identity, and closed
fourth-organ recurrence witness are Lean-proved.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; no project axiom, premise, computation certificate, or RH
statement occurs.

## Log

- 2026-08-11 — dependency-closed paper proof written after full-frontier grammar extraction and
  hostile source-marking/composition audit.
