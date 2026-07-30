# Balanced actuality capacity classification

- **ID:** `balanced-actuality-capacity-classification`
- **Status:** `[FORMALIZED] [REDISCOVERED] [BRIDGE]`
- **Stage:** 3 — formalized in Lean 4
- **Scientific novelty:** none claimed
- **Physical use:** hostile discriminator for the actuality-triality conjecture
- **Lean target:** `GaloisForLFunctions.HTGeometry.BalancedActualityCapacity`

## Exact theorem

Let \(\mathbb F\) be one of the associative real normed division algebras
\(\mathbb R,\mathbb C,\mathbb H\), with standard conjugation, and write
\[
d=\dim_{\mathbb R}\mathbb F\in\{1,2,4\}.
\]
Let \(n,r\geq1\).  Consider the three real capacity spaces
\[
\operatorname{Herm}_n(\mathbb F)
=\{H\in M_n(\mathbb F):H^\dagger=H\},
\]
\[
\operatorname{Skew}_n(\mathbb F)
=\{S\in M_n(\mathbb F):S^\dagger=-S\},
\]
and
\[
\operatorname{Trans}_{r,n}(\mathbb F)=M_{r,n}(\mathbb F).
\]
Their real dimensions are
\[
h(d,n)=n+\frac d2n(n-1),
\tag{1}
\]
\[
k(d,n)=n(d-1)+\frac d2n(n-1),
\tag{2}
\]
and
\[
\tau(d,n,r)=dnr.
\tag{3}
\]

If
\[
h(d,n)=k(d,n)=\tau(d,n,r),
\tag{4}
\]
then
\[
\boxed{d=2,\qquad n=2r.}
\tag{5}
\]
Consequently, among \(\mathbb R,\mathbb C,\mathbb H\), balanced Hermitian record, skew
comparison, and transverse capacity force the complex scalar algebra.  At primitive transverse
multiplicity \(r=1\), they force
\[
\boxed{\mathbb F=\mathbb C,\qquad n=2,\qquad m=n+r=3.}
\tag{6}
\]
Thus the primitive balanced rectangular carrier is \(M_{3,2}(\mathbb C)\), and all three
capacities are four real dimensional.

## Paper proof

The diagonal entries of a Hermitian matrix lie in the conjugation-fixed real line, contributing
\(n\) dimensions.  For every unordered off-diagonal pair \(i<j\), one entry is arbitrary in
\(\mathbb F\) and the other is its conjugate, contributing \(d\) dimensions.  This proves `(1)`.

The diagonal entries of a skew-Hermitian matrix lie in the conjugation-odd subspace, whose real
dimension is \(d-1\).  Each unordered off-diagonal pair again contributes one arbitrary element
of \(\mathbb F\).  This proves `(2)`.  Formula `(3)` is the real dimension of \(r n\) independent
\(\mathbb F\)-entries.

Subtracting `(1)` from `(2)` gives
\[
k(d,n)-h(d,n)=n(d-2).
\tag{7}
\]
Since \(n>0\), the first equality in `(4)` forces \(d=2\).  Substituting \(d=2\) into `(1)` gives
\[
h(2,n)=n+n(n-1)=n^2.
\]
The equality \(h=\tau\) then gives
\[
n^2=2nr.
\]
Since \(n>0\), cancellation yields \(n=2r\), proving `(5)`.  If \(r=1\), then \(n=2\) and
\(m=n+r=3\), proving `(6)`.  Every dependency is closed.

## Relation to the event decomposition

For an isometric complex carrier \(D\in M_{m,n}(\mathbb C)\), the exact decomposition
\[
E=DH+DS+N,\qquad
H^\dagger=H,\quad S^\dagger=-S,\quad D^\dagger N=0
\]
has capacities
\[
n^2,\qquad n^2,\qquad 2n(m-n).
\]
Putting \(r=m-n\), the theorem explains the \(4/4/4\) split of the primitive
\(M_{3,2}(\mathbb C)\) carrier as the unique primitive balanced member of the real/complex/
quaternionic matrix family.

At \(n=2\), the positive Hermitian cone is \(H_2(\mathbb C)_+\), hence the four-dimensional
Lorentz future cone under Pauli coordinates.  At \(m=3,n=2\), the determinant-one left/right
unitary frame group is \(S(U(3)\times U(2))\).  These are exact neighbouring facts already proved
elsewhere in the corpus; they are not consequences of dimension counting alone.

## Hostile physical verdict

The mathematical theorem is routine dimension counting.  It does **not** prove:

1. physical events carry equal capacity in the three sectors;
2. the retained, created, and transverse sectors are operationally defined without a supplied
   matrix carrier;
3. the left \(SU(3)\) is physical colour while the right \(SU(2)\) is weak isospin;
4. the same right two-carrier also yields an independent Lorentz spin action;
5. the four sectors compose into spacetime or any force law; or
6. nature minimizes the transverse multiplicity at \(r=1\).

There is a particularly sharp fixed-carrier trap.  At an isometric \(3\times2\) carrier, the
eight-dimensional Gram kernel is the left skew-frame orbit.  Its \(4+4\) splitting into
right-skew and transverse pieces is the standard
\(\mathfrak{su}(3)=\mathfrak u(2)\oplus\mathbb C^2\) symmetric-pair decomposition.  Interpreting
that same local decomposition simultaneously as QCD colour and as electroweak-plus-Higgs data
would identify physically distinct roles.  Existing weak--Lorentz and nonconjugate-transport
no-go theorems rule out that shortcut.

The only surviving physical use is conditional:

> if a background-free source law independently forces a three-role capacity equivalence and
> primitive transverse multiplicity, then complex amplitudes and the \(3\times2\) carrier are
> selected rather than inserted.

Until that antecedent is derived, the selection is numerology-resistant bookkeeping, not physics.

## Lean target

Formalize the doubled integer-capacity classification, avoiding division:
\[
\begin{aligned}
2h&=2n+dn(n-1),\\
2k&=2n(d-1)+dn(n-1),\\
2\tau&=2dnr.
\end{aligned}
\]
Prove for positive integer \(d,n,r\):

1. \(2h=2k\Rightarrow d=2\);
2. together with \(2h=2\tau\), \(n=2r\);
3. \(r=1\Rightarrow(d,n,m)=(2,2,3)\).

This arithmetic theorem is the exact formalizable claim.  Identification of the scalar algebra
with \(\mathbb C\), Lorentz cone, Standard Model group, and physical capacity law remain separate
theorems or conjectures.

## Gates

- [x] exact statement frozen
- [x] dependency-closed paper proof
- [x] hostile fixed-carrier interpretation audit
- [x] novelty downgraded to `REDISCOVERED / BRIDGE`
- [x] exact Lean formalization
- [x] axiom audit; only `propext`, `Classical.choice`, and `Quot.sound`
- [x] targeted final build:
  `lake build GaloisForLFunctions.HTGeometry.BalancedActualityCapacity`
- [ ] repository-wide lint clean; blocked by pre-existing unreachable modules outside this card

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.BalancedActualityCapacity`
- **Direct check:** `lake env lean
  GaloisForLFunctions/HTGeometry/BalancedActualityCapacity.lean`
- **Target build:** passed, `3013/3013`
- **Formal scope:** doubled-capacity definitions, scalar-dimension classification, source/excess
  classification, primitive `3 × 2` profile, and exact `8/8/8` doubled capacities
- **Excluded:** identification of a two-real-dimensional scalar algebra with physical complex
  amplitudes, the equal-capacity physical antecedent, and every force/spacetime claim
