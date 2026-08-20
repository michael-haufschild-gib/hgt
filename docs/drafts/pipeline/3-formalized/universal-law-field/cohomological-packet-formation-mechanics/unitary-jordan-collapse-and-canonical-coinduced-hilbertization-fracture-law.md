# Unitary Jordan collapse and canonical coinduced Hilbertization fracture law

- **ID:** ULF-CPFM-3
- **Stage:** 3-formalized
- **Type:** GLOBAL ADMISSION THEOREM / THREE-ORGAN FUSION / EXACT NO-GO WITH POSITIVE SURVIVOR
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS]`
  `[FORMATION + PROLONGATION + POSITIVITY] [PROPERTY-T GATE CLOSED] [NOT RH]`
- **Date:** 2026-08-18

## 1. The mechanism question

ULF-CPFM-1 produces a nontrivial central formation packet. ULF-CPFM-2 lowers its degree through
the canonical coinduced quotient

\[
 \mathcal Q(G,A)=\operatorname{Map}(G,A)/A,
 \tag{UJ.1}
\]

where the copy of `A` consists of constant histories. Right translation acts exactly on
`mathcal Q`, and the quotient has the exact recovery kernel needed to reconstruct the original
two-cocycle.

The remaining proposed step was to make this action unitary on a Hilbert space and then use
fixed-point rigidity. The theorem below proves that this step is impossible for the canonical
exact reporter. The obstruction is not incompleteness, discontinuity, or a poor choice of norm.
It is an algebraic conflict between finite formation depth and positive unitary transport.

## 2. Unitary shear conservation

Let `H` be a real Hilbert space and let `U:H->H` be a surjective linear isometry. For `v in H`
put

\[
 w=Uv-v.
 \tag{UJ.2}
\]

### Theorem 2.1 -- a fixed unitary displacement vanishes

If

\[
 Uw=w,
 \tag{UJ.3}
\]

then

\[
 \boxed{Uv=v.}
 \tag{UJ.4}
\]

### Proof

By definition `Uv=v+w`. Inner-product conservation and `(UJ.3)` give

\[
 \langle v,w\rangle
 =\langle Uv,Uw\rangle
 =\langle v+w,w\rangle
 =\langle v,w\rangle+\|w\|^2.
 \tag{UJ.5}
\]

Thus `||w||^2=0`, so `w=0`. This is `(UJ.4)`. QED.

Equation `(UJ.5)` is the conservation identity: a positive invariant pairing cannot carry a
nonzero shear whose displacement is itself recurrent/fixed.

## 3. Collapse of every finite Jordan history

Define the displacement operator

\[
 \Delta_U=U-I.
 \tag{UJ.6}
\]

### Theorem 3.1 -- unitary finite-depth collapse

For every integer `N>=1`,

\[
 \boxed{\Delta_U^N v=0\quad\Longrightarrow\quad\Delta_Uv=0.}
 \tag{UJ.7}
\]

Equivalently, the generalized fixed space of every finite order equals the fixed space:

\[
 \boxed{\ker(U-I)^N=\ker(U-I).}
 \tag{UJ.8}
\]

### Proof

Induct on `N`. The case `N=1` is tautological. For the induction step put
`w=Delta_U v`. The hypothesis says `Delta_U^(N-1)w=0`; induction gives `Delta_Uw=0`, hence
`Uw=w`. Theorem 2.1 then gives `Delta_Uv=0`. QED.

This proof uses neither finite dimensionality nor the spectral theorem.

## 4. The canonical coinduced quotient contains a nontrivial Jordan chain

Specialize `(UJ.1)` to `G=A=R`, and let `tau` be translation by one:

\[
 (\tau f)(x)=f(x+1).
 \tag{UJ.9}
\]

Write brackets for classes modulo constants and define

\[
 \ell=[x],\qquad q=[x^2].
 \tag{UJ.10}
\]

### Lemma 4.1 -- exact quadratic-to-linear formation

In `mathcal Q(R,R)`,

\[
 \boxed{\tau\ell=\ell,\qquad \tau q=q+2\ell,\qquad 2\ell\ne0.}
 \tag{UJ.11}
\]

### Proof

The first two identities are

\[
 (x+1)-x=1,
 \qquad
 (x+1)^2-x^2=2x+1,
\]

with constants removed. If `2 ell=0`, the function `2x` is constant. Evaluation at `0` and `1`
gives the contradiction `0=2`. QED.

Thus `q` is a genuine length-two Jordan history for the exact recovery action:

\[
 (\tau-I)^2q=0,
 \qquad
 (\tau-I)q=2\ell\ne0.
 \tag{UJ.12}
\]

## 5. No faithful unitary Hilbertization

### Theorem 5.1 -- canonical exact reporter fracture

There do not exist

1. a real Hilbert space `H`;
2. an injective additive reporter `r:mathcal Q(R,R)->H`;
3. a surjective real-linear isometry `U` of `H`;

such that

\[
 \boxed{r(\tau z)=Ur(z)\qquad(z\in\mathcal Q(\mathbb R,\mathbb R)).}
 \tag{UJ.13}
\]

### Proof

Put `v=r(q)` and `w=r(2 ell)`. Equivariance and `(UJ.11)` give

\[
 Uv=v+w,
 \qquad
 Uw=w.
 \tag{UJ.14}
\]

Theorem 2.1 forces `w=0`. Injectivity forces `2 ell=0`, contradicting Lemma 4.1. QED.

No continuity of `r` is assumed. Therefore changing the Hilbert norm, completing a different
dense subspace, or allowing a discontinuous additive embedding cannot repair `(UJ.13)` while
retaining exact recovery.

### Corollary 5.2 -- the property-(T) route is closed in its canonical form

The canonical exact degree-lowering reporter from ULF-CPFM-2 cannot simultaneously be

1. faithful modulo exactly the constant histories;
2. equivariant for right translation; and
3. unitary on a Hilbert space.

Hence Delorme--Guichardet/property-(T) cannot be applied to that reporter. A different Hilbert
one-cocycle may still exist, but then it must lose exact recovery, exclude the polynomial history,
change fibres, or cease to be the canonical degree-lowering action.

## 6. Three-organ fusion and fourth-organ prediction

The theorem is one mechanism, not a comparison of similarly named quantities:

| Organ | Exact role |
|---|---|
| cohomological formation | quotient by constants lowers the packet from degree two to degree one without information loss |
| differential/prolongation history | polynomial translation gives finite nontrivial Jordan depth `(UJ.12)` |
| positive recurrent observation | inner-product invariance gives conservation `(UJ.5)` and collapses that depth |

The forced fourth-organ prediction concerns every normal spectral reporter:

> **Finite formation-depth prediction.** Any reporter implemented by a unitary/normal translation
> kills the displacement of every finitely nilpotent translation history. Therefore finite
> polynomial jet depth can survive algebraically or distributionally, but not as a faithful
> positive unitary state vector.

This predicts the fracture already visible in analytic HT and recurrence charts. Finite
unipotent translation orbits are differential-algebraic; genuine HT requires unbounded formation
depth. Compact/unitary recurrence may retain a phase orbit, but every finite polynomial lift is
semisimplified. Spectral-trace and quantum-clock observers can see the semisimple/phase quotient,
not the exact polynomial recovery history.

## 7. Rank raising does not evade the theorem

The corpus already proves that one added opposite root promotes a horizon parabolic to the full
`A_2` polynomial current algebra, and that Steinberg root commutators generate the missing root
directions. That is a valid rank-raising exactification, but it does not unitarize the finite
polynomial history.

Unitary representations of unipotent or semisimple groups do exist. Their root subgroups act by
unitaries with continuous spectral behaviour; polynomial coordinate functions occur as smooth or
distributional vectors, not as a finite nontrivial Jordan block of actual Hilbert vectors.
Thus the correct positive survivor is not "add rank and invoke property (T)." It is a two-level
formation doctrine:

\[
 \boxed{
 \text{exact algebraic/distributional recovery history}
 \quad\longrightarrow\quad
 \text{nonfaithful positive Hilbert semisimplification}.}
 \tag{UJ.15}
\]

The comparison defect between those levels is the **unitary formation radical**: displacements of
finite generalized fixed histories. A final selection theorem must control this radical or its
boundary current; a Hilbert norm cannot make it disappear while claiming exact recovery.

## 8. Sharp boundaries

1. The theorem concerns positive-definite Hilbert transport. Indefinite/Krein isometries can have
   nontrivial unipotent Jordan blocks.
2. Nonunitary bounded or unbounded representations are not excluded.
3. Cross-fibre unitary transport is not excluded; ULF-SMFM-1 proves it is the correct survivor for
   exact scale covariance.
4. Nonfaithful unitary reporters are allowed and necessarily erase the finite displacement.
5. Infinite-depth histories need not be generalized eigenvectors of any finite order.
6. The theorem supplies no arithmetic source map, Xi landing, critical-line orientation, or RH
   conclusion.

## 9. Literature boundary

The operator fact that normal operators have no nontrivial Jordan blocks is classical. Unitary
realisations of unipotent representations instead use `L^2` orbit models and infinite-dimensional
completions; see Dvorsky--Sahi, *Explicit Hilbert spaces for certain unipotent representations III*,
<https://arxiv.org/abs/math/0110339>. The field-level content here is the exact collision with the
canonical coinduced recovery quotient and its explicit quadratic-to-linear formation chain.

## 10. Lean certification

The dependency-closed core is formalized in

`formal/GaloisForLFunctions/HTGeometry/ConstitutiveUnitaryJordanFormationFracture.lean`.

It proves:

1. fixed-displacement unitary collapse `(UJ.4)`;
2. collapse of every finite iterated displacement `(UJ.7)`;
3. the exact linear and quadratic coinduced translation formulas `(UJ.11)`;
4. nonvanishing of `2 ell`;
5. nonexistence of every injective additive equivariant unitary realization `(UJ.13)`.

The Lean theorem uses no continuity, finite-dimensionality, project axioms, `sorry`, `admit`,
`opaque`, or `unsafe` declarations.

## Log

- 2026-08-18 -- canonical Hilbertization conjecture killed; unitary formation radical and
  algebraic/distributional-to-Hilbert fracture retained.
- 2026-08-18 -- paper proof closed and scratch Lean elaboration passed.
